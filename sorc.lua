task.wait("5")

--=============================================================
--  TD AUTO-FARM — LinoriaLib UI
--  Record/Replay + Auto Skip + Retry-on-failure + Auto Replay
--  Recordings stored in: TDAutoFarm/recordings
--=============================================================

local repo = 'https://raw.githubusercontent.com/violin-suzutsuki/LinoriaLib/main/'
local Library      = loadstring(game:HttpGet(repo .. 'Library.lua'))()
local ThemeManager = loadstring(game:HttpGet(repo .. 'addons/ThemeManager.lua'))()
local SaveManager  = loadstring(game:HttpGet(repo .. 'addons/SaveManager.lua'))()

local Players = game:GetService("Players")
local http    = game:GetService("HttpService")
local UIS     = game:GetService("UserInputService")

--=============================================================
--  STATE
--=============================================================
local Recording        = {}
local IsRecording      = false
local IsReplaying      = false
local RecordStart      = 0
local LastRecordT      = 0
local RecordMinGap     = 0.02

local RECORDINGS_FOLDER  = "TDAutoFarm/recordings"
local LAST_SELECTED_FILE = "TDAutoFarm/last_recording.txt"
local SelectedRecording  = nil

local RecordedSpawnedTowers = {}
local ReplaySpawnedTowers   = {}

local MAX_RETRIES           = 100
local MONEY_TOLERANCE       = 0.9
local MONEY_SETTLE_TIMEOUT  = 1.5
local MIN_ACTION_GAP        = 0.15

local PlaybackDelay         = 0
local AutoPlayEnabled       = false
local PendingPlaybackCancel = false

local CurrentReplayName     = "?"

local AutoReplayEnabled        = false
local WATCHDOG_TIMER_PATH      = "workspace.Info.Time.Timer"
local WATCHDOG_STALL_TIMEOUT   = 5
local WATCHDOG_REFIRE_COOLDOWN = 2
local WATCHDOG_POLL_RATE       = 0.25

local AutoSkipKeepEnabled      = false
local AutoSkipLastFireAt       = -math.huge
local AUTOSKIP_REFIRE_COOLDOWN = 0.5
local AUTOSKIP_POLL_RATE       = 0.25

--=============================================================
--  MONEY
--=============================================================
local MONEY_PATH_KEYS = { "Players", "LocalPlayer", "leaderstats", "Money" }
local MoneyObj     = nil
local cachedMoney  = nil
local moneyConn    = nil

local function setupMoney()
    if moneyConn then
        pcall(function() moneyConn:Disconnect() end)
        moneyConn = nil
    end
    MoneyObj = nil
    cachedMoney = nil

    local ok, obj = pcall(function()
        local cur = game
        for _, key in ipairs(MONEY_PATH_KEYS) do
            cur = cur[key]
            if cur == nil then return nil end
        end
        return cur
    end)
    if not ok or not obj then return false end
    local v = obj.Value
    if v == nil or type(v) ~= "number" then return false end

    MoneyObj = obj
    cachedMoney = v
    pcall(function()
        moneyConn = obj:GetPropertyChangedSignal("Value"):Connect(function()
            cachedMoney = obj.Value
        end)
    end)
    return true
end

local function getMoney()
    if not MoneyObj or not MoneyObj.Parent then
        setupMoney()
    end
    return cachedMoney
end

--=============================================================
--  TIMER PARSING
--=============================================================
local function parseTimerValue(v)
    if type(v) == "number" then return v end
    if type(v) ~= "string" then return 0 end
    local parts = {}
    for p in string.gmatch(v, "[^:]+") do
        table.insert(parts, p)
    end
    if #parts == 1 then
        return tonumber(parts[1]) or 0
    elseif #parts == 2 then
        return (tonumber(parts[1]) or 0) * 60 + (tonumber(parts[2]) or 0)
    elseif #parts == 3 then
        return (tonumber(parts[1]) or 0) * 3600
             + (tonumber(parts[2]) or 0) * 60
             + (tonumber(parts[3]) or 0)
    end
    return 0
end

--=============================================================
--  HELPERS
--=============================================================
local function packArgs(...) return { n = select("#", ...), ... } end
local function unpackArgs(t) return table.unpack(t, 1, t.n or #t) end

local function resolveRemote(path)
    local ok, obj = pcall(function()
        local cur = game
        for part in string.gmatch(path, "[^%.]+") do
            cur = cur[part]
        end
        return cur
    end)
    if ok and typeof(obj) == "Instance" then
        if obj:IsA("RemoteEvent") or obj:IsA("RemoteFunction") then
            return obj
        end
    end
    return nil
end

local function getTowerCFrameSafe(tower)
    local cf
    local ok = pcall(function() cf = tower:GetPivot() end)
    if ok and typeof(cf) == "CFrame" then return cf end
    ok = pcall(function() cf = tower.CFrame end)
    if ok and typeof(cf) == "CFrame" then return cf end
    local pos
    ok = pcall(function() pos = tower.Position end)
    if ok and typeof(pos) == "Vector3" then return CFrame.new(pos) end
    return nil
end

local function getRoundTimer()
    local obj
    pcall(function() obj = workspace.Info.Time.Timer end)
    return obj
end

local function getRoundTimerSeconds()
    local obj = getRoundTimer()
    if not obj then return nil end
    local ok, v = pcall(function() return obj.Value end)
    if not ok or v == nil then return nil end
    return parseTimerValue(v)
end

local function findTowerByNameAndPosition(name, cfComponents)
    if not name then return nil end

    local seen       = {}
    local candidates = {}

    local function add(obj)
        if obj and obj.Name == name and not seen[obj] then
            seen[obj] = true
            table.insert(candidates, obj)
        end
    end

    if type(getnilinstances) == "function" then
        local ok, list = pcall(getnilinstances)
        if ok and type(list) == "table" then
            for _, obj in ipairs(list) do add(obj) end
        end
    end

    local towersFolder = workspace:FindFirstChild("Towers")
    if towersFolder then
        for _, obj in ipairs(towersFolder:GetDescendants()) do add(obj) end
    end

    if #candidates == 0 then
        for _, obj in ipairs(workspace:GetDescendants()) do add(obj) end
    end

    if #candidates == 0 then return nil end

    if type(cfComponents) == "table" and #cfComponents >= 3 then
        local target
        pcall(function()
            target = CFrame.new(table.unpack(cfComponents, 1, math.min(#cfComponents, 12)))
        end)
        if target then
            local best, bestDist = nil, math.huge
            for _, obj in ipairs(candidates) do
                local cf = getTowerCFrameSafe(obj)
                if cf then
                    local d = (cf.Position - target.Position).Magnitude
                    if d < bestDist then best, bestDist = obj, d end
                end
            end
            if best then return best end
        end
    end

    return candidates[1]
end

local function getAutoSkipValue()
    local lp = game:GetService("Players").LocalPlayer
    if not lp then return nil end
    local child = lp:FindFirstChild("AutoSkip")
    if child then
        local ok, v = pcall(function() return child.Value end)
        if ok and typeof(v) == "boolean" then return v end
    end
    local attr = lp:GetAttribute("AutoSkip")
    if type(attr) == "boolean" then return attr end
    return nil
end

--=============================================================
--  ARG ENCODING
--=============================================================
local function encodeArg(a)
    if typeof(a) == "Instance" then
        local cf = getTowerCFrameSafe(a)
        local ref = { __t = "TowerRef", name = a.Name }
        if cf then ref.cf = { cf:GetComponents() } end
        local ok, path = pcall(function() return a:GetFullName() end)
        if ok and path and path:find("%.") then ref.path = path end
        return ref
    end
    if typeof(a) == "Vector3" then
        return { __t = "Vector3", v = {a.X, a.Y, a.Z} }
    end
    if typeof(a) == "CFrame" then
        return { __t = "CFrame", v = {a:GetComponents()} }
    end
    if type(a) == "table" then
        local entries = {}
        for k, v in pairs(a) do
            if k ~= "__t" then
                local key = (type(k) == "number") and k or tostring(k)
                table.insert(entries, { k = key, v = encodeArg(v) })
            end
        end
        return { __t = "Wrapped", entries = entries, n = a.n }
    end
    return a
end

local function decodeArg(a)
    if type(a) ~= "table" then return a end

    if a.__t == "SpawnedTower" then
        local t = ReplaySpawnedTowers[a.spawn_index]
        if not t then
            warn("[AutoFarm] SpawnedTower #" .. tostring(a.spawn_index) ..
                   " not in ReplaySpawnedTowers (have " .. tostring(#ReplaySpawnedTowers) .. ")")
        end
        return t
    end

    if a.__t == "TowerRef" then
        if a.__spawn_index and ReplaySpawnedTowers[a.__spawn_index] then
            return ReplaySpawnedTowers[a.__spawn_index]
        end
        if a.path then
            local inst = resolveRemote(a.path)
            if inst then return inst end
        end
        local inst = findTowerByNameAndPosition(a.name, a.cf)
        if inst then return inst end
        warn("[AutoFarm] could not resolve tower '" .. tostring(a.name) .. "'")
        return nil
    end

    if a.__t == "Instance" then
        return resolveRemote(a.p or a.path)
    end
    if a.__t == "Vector3" then
        local src = a.v or a
        return Vector3.new(src[1] or 0, src[2] or 0, src[3] or 0)
    end
    if a.__t == "CFrame" then
        local src = a.v or a
        if type(src) == "table" and #src >= 12 then
            return CFrame.new(table.unpack(src, 1, 12))
        end
        return CFrame.new()
    end
    if a.__t == "Wrapped" then
        local o = { n = a.n }
        for _, e in ipairs(a.entries or {}) do
            local k = tonumber(e.k) or e.k
            o[k] = decodeArg(e.v)
        end
        return o
    end
    return a
end

--=============================================================
--  FILE SERIALIZATION
--=============================================================
local function ser(v)
    local t = typeof(v)
    if t == "Vector3" then
        return { __t = "Vector3", v = {v.X, v.Y, v.Z} }
    end
    if t == "CFrame" then
        return { __t = "CFrame", v = {v:GetComponents()} }
    end
    if t == "Instance" then
        return { __t = "Instance", p = v:GetFullName() }
    end
    if type(v) == "table" then
        local tag = v.__t
        if tag == "TowerRef" then
            local ref = { __t = "TowerRef", name = v.name }
            if type(v.cf) == "table" then
                local out = {}
                for i = 1, 12 do out[i] = v.cf[i] end
                ref.cf = out
            end
            if v.path then ref.path = v.path end
            if v.__spawn_index then ref.__spawn_index = v.__spawn_index end
            return ref
        end
        if tag == "SpawnedTower" then
            return { __t = "SpawnedTower", spawn_index = v.spawn_index }
        end
        if tag == "Vector3" then
            local src = v.v or {}
            return { __t = "Vector3", v = {src[1] or 0, src[2] or 0, src[3] or 0} }
        end
        if tag == "CFrame" then
            local src = v.v or {}
            local out = {}
            for i = 1, 12 do out[i] = src[i] end
            return { __t = "CFrame", v = out }
        end
        if tag == "Instance" then
            return { __t = "Instance", p = v.p or v.path }
        end
        if tag == "Wrapped" then
            local entries = {}
            for _, e in ipairs(v.entries or {}) do
                table.insert(entries, { k = e.k, v = ser(e.v) })
            end
            return { __t = "Wrapped", entries = entries, n = v.n }
        end
        local entries = {}
        for k, val in pairs(v) do
            if k ~= "__t" then
                local key = (type(k) == "number") and k or tostring(k)
                table.insert(entries, { k = key, v = ser(val) })
            end
        end
        return { __t = "Wrapped", entries = entries, n = v.n }
    end
    return v
end

local function deser(v)
    if type(v) ~= "table" then return v end
    local tag = v.__t
    if tag == "Vector3" then
        local src = v.v or {}
        return { __t = "Vector3", v = {src[1] or 0, src[2] or 0, src[3] or 0} }
    end
    if tag == "CFrame" then
        local src = v.v or {}
        local out = {}
        for i = 1, 12 do out[i] = src[i] end
        return { __t = "CFrame", v = out }
    end
    if tag == "Instance" then
        return { __t = "Instance", p = v.p or v.path }
    end
    if tag == "SpawnedTower" then
        return { __t = "SpawnedTower", spawn_index = v.spawn_index }
    end
    if tag == "TowerRef" then
        local ref = { __t = "TowerRef", name = v.name }
        if type(v.cf) == "table" then
            local out = {}
            for i = 1, 12 do out[i] = v.cf[i] end
            ref.cf = out
        end
        if v.path then ref.path = v.path end
        if v.__spawn_index then ref.__spawn_index = v.__spawn_index end
        return ref
    end
    if tag == "Wrapped" then
        local o = { n = v.n }
        for _, e in ipairs(v.entries or {}) do
            local k = tonumber(e.k) or e.k
            o[k] = deser(e.v)
        end
        return o
    end
    return v
end

--=============================================================
--  RECORDINGS FOLDER
--=============================================================
local function ensureRecordingsFolder()
    if type(isfolder) ~= "function" or type(makefolder) ~= "function" then
        return false
    end
    local parts = {}
    for part in string.gmatch(RECORDINGS_FOLDER, "[^/\\]+") do
        table.insert(parts, part)
    end
    local path = ""
    for _, part in ipairs(parts) do
        path = (path == "") and part or (path .. "/" .. part)
        if not isfolder(path) then
            local ok = pcall(makefolder, path)
            if not ok then return false end
        end
    end
    return true
end

local function ensureParentFolder(filePath)
    if type(makefolder) ~= "function" or type(isfolder) ~= "function" then return end
    local parent = filePath:match("^(.*)/[^/]+$")
    if parent and not isfolder(parent) then
        pcall(makefolder, parent)
    end
end

local function listRecordings()
    local out = {}
    if not ensureRecordingsFolder() then return out end
    local ok, files = pcall(listfiles, RECORDINGS_FOLDER)
    if not ok or type(files) ~= "table" then return out end
    for _, file in ipairs(files) do
        local name = tostring(file):gsub("\\", "/"):match("[^/]+$") or ""
        if name:sub(-5) == ".json" then
            table.insert(out, name:sub(1, -6))
        end
    end
    table.sort(out)
    return out
end

local function recordingPath(name)
    return RECORDINGS_FOLDER .. "/" .. name .. ".json"
end

local function saveLastSelected(name)
    if type(writefile) ~= "function" then return end
    ensureParentFolder(LAST_SELECTED_FILE)
    pcall(writefile, LAST_SELECTED_FILE, tostring(name or ""))
end

local function loadLastSelected()
    if type(readfile) ~= "function" or type(isfile) ~= "function" then return nil end
    if not isfile(LAST_SELECTED_FILE) then return nil end
    local ok, v = pcall(readfile, LAST_SELECTED_FILE)
    if not ok or not v or v == "" then return nil end
    return v
end

--=============================================================
--  LINORIA UI
--=============================================================
local Window = Library:CreateWindow({
    Title = 'TD AutoFarm',
    Center = true,
    AutoShow = true,
    TabPadding = 8,
    MenuFadeTime = 0.2
})

local Tabs = {
    Main            = Window:AddTab('Main'),
    ['UI Settings'] = Window:AddTab('UI Settings'),
}

local LeftBox       = Tabs.Main:AddLeftGroupbox('Recordings')
local StatusBox     = Tabs.Main:AddLeftGroupbox('Status', 1000)
local RightBox      = Tabs.Main:AddRightGroupbox('Playback')
local DelayBox      = Tabs.Main:AddRightGroupbox('Playback Start Delay')
local SkipBox       = Tabs.Main:AddRightGroupbox('Auto Skip')
local AutoReplayBox = Tabs.Main:AddRightGroupbox('Auto Replay')

local StatusLabel = StatusBox:AddLabel('Idle')





local function setStatus(msg)
    pcall(function() StatusLabel:SetText(tostring(msg)) end)
    print("[AutoFarm] " .. tostring(msg))
end

-- Multi-line replay status. Only touches the label, not the console.
local function setReplayStatus(completed, total, secsLeft, nextDesc)
    local text = string.format(
        "Playing (%s)...\n(%d/%d actions)\n%.1fs until next action\n--> %s",
        tostring(CurrentReplayName or "?"),
        completed, total, math.max(0, secsLeft),
        tostring(nextDesc or "?")
    )
    pcall(function() StatusLabel:SetText(text) end)
end

-- Human-readable description for an action's status line.
local function describeAction(action, prevAction)
    if not action then return "?" end
    local name = tostring(action.name or "?")

    if name == "UpgradeTower" then
        local args = action.args
        local n = (args and args.n) or (args and #args) or 0
        for i = 1, n do
            local a = args[i]
            if type(a) == "table" and a.__t == "TowerRef" and a.name then
                return "UpgradeTower (" .. tostring(a.name) .. ")"
            end
            if type(a) == "table" and a.__t == "SpawnedTower" then
                local resolved = ReplaySpawnedTowers[a.spawn_index]
                if resolved and resolved.Name then
                    return "UpgradeTower (" .. tostring(resolved.Name) .. ")"
                end
                return "UpgradeTower (#" .. tostring(a.spawn_index) .. ")"
            end
        end
        return "UpgradeTower"
    end

    if name == "SpawnNewTower" then
        if prevAction and prevAction.name == "RequestTower" then
            local pa = prevAction.args
            if pa and type(pa[1]) == "string" then
                return "SpawnNewTower (" .. tostring(pa[1]) .. ")"
            end
        end
        return "SpawnNewTower"
    end

    if name == "RequestTower" then
        local a = action.args
        if a and type(a[1]) == "string" then
            return "RequestTower (" .. tostring(a[1]) .. ")"
        end
        return "RequestTower"
    end

    return name
end

--=============================================================
--  HOOK
--=============================================================
local originalNamecall = nil
local isHooked         = false

local function recordNamecall(self, ...)
    local methodNow = getnamecallmethod()
    if methodNow ~= "FireServer" and methodNow ~= "InvokeServer" then
        return originalNamecall(self, ...)
    end

    local timeNow = os.clock()
    if timeNow - LastRecordT < RecordMinGap then
        return originalNamecall(self, ...)
    end
    LastRecordT = timeNow

    local rawArgs     = packArgs(...)
    local moneyBefore = getMoney()

    local result = table.pack(originalNamecall(self, ...))

    local moneyAfter = getMoney()
    local selfName   = self.Name

    task.defer(function()
        pcall(function()
            if selfName == "SpawnNewTower" and methodNow == "InvokeServer" then
                if typeof(result[1]) == "Instance" then
                    table.insert(RecordedSpawnedTowers, result[1])
                end
            end

            local encodedArgs = { n = rawArgs.n }
            for i = 1, rawArgs.n do
                local arg = rawArgs[i]
                if selfName == "UpgradeTower" and typeof(arg) == "Instance" then
                    local ref = encodeArg(arg)
                    for j, t in ipairs(RecordedSpawnedTowers) do
                        if t == arg then ref.__spawn_index = j; break end
                    end
                    encodedArgs[i] = ref
                else
                    encodedArgs[i] = encodeArg(arg)
                end
            end

            local path = ""
            pcall(function() path = self:GetFullName() end)

            table.insert(Recording, {
                t            = timeNow - RecordStart,
                path         = path,
                name         = selfName,
                method       = methodNow,
                args         = encodedArgs,
                money_before = moneyBefore,
                money_after  = moneyAfter,
            })
        end)
    end)

    return table.unpack(result, 1, result.n)
end

local function installHook()
    if isHooked then return end
    originalNamecall = hookmetamethod(game, "__namecall", recordNamecall)
    isHooked = true
end

local function uninstallHook()
    if not isHooked then return end
    hookmetamethod(game, "__namecall", originalNamecall)
    isHooked = false
    originalNamecall = nil
end

--=============================================================
--  RECORDING STATUS POLLER
--=============================================================
task.spawn(function()
    local lastCount    = -1
    local wasRecording = false

    while true do
        task.wait(0.1)
        if IsRecording then
            wasRecording = true
            local count = #Recording
            if count ~= lastCount then
                lastCount = count
                pcall(function()
                    StatusLabel:SetText(("Recording... %d actions"):format(count))
                end)
            end
        else
            if wasRecording then
                wasRecording = false
                lastCount   = -1
            end
        end
    end
end)

--=============================================================
--  RETRY / WAIT HELPERS
--=============================================================
local function waitForMoneyDeduct(baseline, cost, timeout)
    if not baseline or not cost or cost <= 0 then return true end
    local target = baseline - cost * MONEY_TOLERANCE
    local t0 = os.clock()
    while os.clock() - t0 < timeout do
        local m = getMoney()
        if m and m <= target then return true end
        task.wait(0.05)
    end
    return false
end

local function waitForMoneyIndefinitely(required, actionIdx, actionDesc, total)
    if not required or required <= 0 then return true end
    local reported = false
    while IsReplaying do
        local m = getMoney()
        if m and m >= required then
            if reported then
                setReplayStatus(actionIdx - 1, total, 0, actionDesc)
            end
            return true
        end
        if not reported then
            pcall(function()
                StatusLabel:SetText(string.format(
                    "Waiting for money (#%d %s)\n%s / %s",
                    actionIdx, tostring(actionDesc),
                    tostring(m or "?"), tostring(math.floor(required))
                ))
            end)
            reported = true
        end
        task.wait(0.15)
    end
    return false
end

--=============================================================
--  REPLAY
--=============================================================
local function replayOnce()
    if IsReplaying or #Recording == 0 then return end
    IsReplaying = true
    ReplaySpawnedTowers = {}
    CurrentReplayName = SelectedRecording or "(in memory)"
    setStatus(("Replaying %d actions (%s)"):format(#Recording, CurrentReplayName))

    if not MoneyObj then
        setupMoney()
        if MoneyObj then
            print("[AutoFarm] money: " .. tostring(cachedMoney))
        else
            warn("[AutoFarm] money object unavailable")
        end
    end

    local start        = os.clock()
    local lastFireTime = -math.huge
    local failed       = {}
    local total        = #Recording

    for idx, action in ipairs(Recording) do
        if not IsReplaying then break end

        local actionName = tostring(action.name or "?")
        local actionPath = tostring(action.path or "?")

        local prevAction  = Recording[idx - 1]
        local description = describeAction(action, prevAction)

        local absoluteTarget = start + action.t
        local gapTarget      = lastFireTime + MIN_ACTION_GAP
        local targetTime     = math.max(absoluteTarget, gapTarget)

        -- Live countdown to this action's fire time
        local totalWait = targetTime - os.clock()
        if totalWait > 0 then
            local waitEnd = os.clock() + totalWait
            setReplayStatus(idx - 1, total, waitEnd - os.clock(), description)
            while IsReplaying do
                local remaining = waitEnd - os.clock()
                if remaining <= 0 then break end
                setReplayStatus(idx - 1, total, remaining, description)
                task.wait(0.1)
            end
        end

        if not IsReplaying then break end

        local remote = resolveRemote(actionPath)
        if not remote then
            warn("[AutoFarm] missing remote: " .. actionPath)
            table.insert(failed, { idx = idx, name = actionName, reason = "remote missing" })
            lastFireTime = os.clock()
        else
            local cost = 0
            if action.money_before and action.money_after then
                cost = action.money_before - action.money_after
                if cost < 0 then cost = 0 end
            end

            if cost > 0 then
                if not waitForMoneyIndefinitely(cost, idx, description, total) then
                    break
                end
            end

            local attempt = 0
            local success = false
            local skipped = false

            while attempt < MAX_RETRIES and IsReplaying do
                attempt = attempt + 1

                if cost > 0 then
                    local m = getMoney()
                    if not m or m < cost then
                        if not waitForMoneyIndefinitely(cost, idx, description, total) then
                            break
                        end
                    end
                end

                local packed = table.pack(unpackArgs(action.args))
                local unresolved = false
                for i = 1, packed.n do
                    local orig = packed[i]
                    packed[i] = decodeArg(orig)
                    if packed[i] == nil and type(orig) == "table" then
                        if orig.__t == "TowerRef" or orig.__t == "SpawnedTower" then
                            unresolved = true
                        end
                    end
                end

                if unresolved then
                    warn("[AF] action #" .. idx .. " (" .. description .. ") skipped — tower could not be resolved")
                    lastFireTime = os.clock()
                    skipped = true
                    break
                end

                local moneyBefore = getMoney()

                if action.method == "FireServer" then
                    pcall(function()
                        remote:FireServer(table.unpack(packed, 1, packed.n))
                    end)
                    success = true
                else
                    local ok, invokeResult = pcall(function()
                        return remote:InvokeServer(table.unpack(packed, 1, packed.n))
                    end)

                    if not ok then
                        warn("[AutoFarm] InvokeServer error on " .. actionPath .. ": "
                            .. tostring(invokeResult or "(nil)"))
                    else
                        if actionName == "SpawnNewTower" and typeof(invokeResult) == "Instance" then
                            table.insert(ReplaySpawnedTowers, invokeResult)
                            print(("[AF] SpawnNewTower #%d returned %s")
                                :format(#ReplaySpawnedTowers, tostring(invokeResult.Name)))
                        end
                        if cost > 0 then
                            success = waitForMoneyDeduct(moneyBefore, cost, MONEY_SETTLE_TIMEOUT)
                        else
                            success = true
                        end
                    end
                end

                if success then
                    if attempt > 1 then
                        print(("[AF] action #%d (%s) succeeded on attempt %d")
                            :format(idx, description, attempt))
                    end
                    break
                end

                print(("[AF] action #%d (%s) failed attempt %d/%d")
                    :format(idx, description, attempt, MAX_RETRIES))
                task.wait(0.3)
            end

            if not success and not skipped then
                warn(("[AF] action #%d (%s) FAILED after %d attempts")
                    :format(idx, description, MAX_RETRIES))
                table.insert(failed, { idx = idx, name = description, reason = "remote rejected" })
            elseif skipped then
                table.insert(failed, { idx = idx, name = description, reason = "unresolved tower" })
            end

            lastFireTime = os.clock()
        end
    end

    IsReplaying = false

    if #failed > 0 then
        setStatus(("Playback finished with %d failed action(s)"):format(#failed))
        for _, f in ipairs(failed) do
            print(("[AF] FAILED #%d %s — %s"):format(f.idx, f.name, f.reason))
        end
    else
        setStatus("Playback finished")
    end
end

local function stopPlayback()
    IsReplaying = false
    PendingPlaybackCancel = true
    setStatus("Playback stopped")
end

local loadRecording

local function startPlayback()
    if IsReplaying then
        setStatus("Already playing")
        return
    end

    if #Recording == 0 then
        if not SelectedRecording then
            setStatus("Pick a recording from the dropdown first")
            return
        end
        loadRecording(SelectedRecording)
        if #Recording == 0 then return end
    end

    task.spawn(function()
        PendingPlaybackCancel = false

        if PlaybackDelay > 0 then
            local t0 = os.clock()
            local current = getRoundTimerSeconds()

            if current and current >= PlaybackDelay then
                setStatus(("Auto Play: timer already at %ss, playing")
                    :format(tostring(current)))
            else
                setStatus(("Waiting for round timer >= %ss..."):format(tostring(PlaybackDelay)))
                while not PendingPlaybackCancel and (os.clock() - t0) < 120 do
                    local v = getRoundTimerSeconds()
                    if v and v >= PlaybackDelay then break end
                    task.wait(0.1)
                end
            end

            if PendingPlaybackCancel then
                PendingPlaybackCancel = false
                setStatus("Playback cancelled")
                return
            end
        end

        replayOnce()
    end)
end

local function autoPlayLoop()
    local lastTimerValue  = nil
    local playedThisRound = false

    while AutoPlayEnabled do
        task.wait(0.25)

        if #Recording == 0 and SelectedRecording then
            loadRecording(SelectedRecording)
        end

        if #Recording > 0 and not IsReplaying then
            local current = getRoundTimerSeconds()

            if current == nil then
                if not playedThisRound then
                    playedThisRound = true
                    replayOnce()
                end
            else
                if lastTimerValue and current < lastTimerValue - 1 then
                    playedThisRound = false
                end
                lastTimerValue = current

                if not playedThisRound and current >= PlaybackDelay then
                    playedThisRound = true
                    replayOnce()
                end
            end
        end
    end
    setStatus("Auto Play: disabled")
end

local function resolveWatchdogTimer()
    local ok, obj = pcall(function()
        local cur = game
        for part in string.gmatch(WATCHDOG_TIMER_PATH, "[^%.]+") do
            cur = cur[part]
        end
        return cur
    end)
    if ok and obj and obj.Value ~= nil then return obj end
    return nil
end

local function autoReplayLoop()
    local timerObj = resolveWatchdogTimer()
    if not timerObj then
        warn("[AutoReplay] timer not found at " .. WATCHDOG_TIMER_PATH)
        AutoReplayEnabled = false
        if Toggles and Toggles.AutoReplayToggle then
            Toggles.AutoReplayToggle:SetValue(false)
        end
        return
    end

    local replayRemote
    pcall(function()
        replayRemote = game:GetService("ReplicatedStorage").Events.Replay
    end)
    if not replayRemote then
        warn("[AutoReplay] Replay remote not found")
        AutoReplayEnabled = false
        if Toggles and Toggles.AutoReplayToggle then
            Toggles.AutoReplayToggle:SetValue(false)
        end
        return
    end

    print("[AutoReplay] running — will fire Replay if timer stalls for "
        .. tostring(WATCHDOG_STALL_TIMEOUT) .. "s")

    local lastValue    = timerObj.Value
    local lastChangeAt = os.clock()
    local lastFiredAt  = -math.huge

    while AutoReplayEnabled do
        task.wait(WATCHDOG_POLL_RATE)

        if not timerObj.Parent then
            local newTimer = resolveWatchdogTimer()
            if newTimer then
                timerObj     = newTimer
                lastValue    = timerObj.Value
                lastChangeAt = os.clock()
            end
        else
            local v = timerObj.Value
            if v ~= lastValue then
                lastValue    = v
                lastChangeAt = os.clock()
            end
        end

        local stalled     = (os.clock() - lastChangeAt) >= WATCHDOG_STALL_TIMEOUT
        local offCooldown = (os.clock() - lastFiredAt)  >= WATCHDOG_REFIRE_COOLDOWN

        if stalled and offCooldown then
            print(string.format("[AutoReplay] timer stalled %.1fs at %s — firing Replay",
                os.clock() - lastChangeAt, tostring(lastValue)))
            pcall(function() replayRemote:FireServer() end)
            lastFiredAt  = os.clock()
            lastChangeAt = os.clock()
            setStatus("Auto Replay: Replay fired")
        end
    end

    print("[AutoReplay] stopped")
end

local function autoSkipWatchLoop()
    print("[AutoSkip] watch loop started")
    while AutoSkipKeepEnabled do
        task.wait(AUTOSKIP_POLL_RATE)
        local v = getAutoSkipValue()
        if v == false then
            local now = os.clock()
            if now - AutoSkipLastFireAt >= AUTOSKIP_REFIRE_COOLDOWN then
                AutoSkipLastFireAt = now
                pcall(function()
                    game:GetService("ReplicatedStorage").Remotes.AutoSkip:FireServer()
                end)
                print("[AutoSkip] AutoSkip was off — fired remote")
            end
        end
    end
    print("[AutoSkip] watch loop stopped")
end

--=============================================================
--  SAVE / LOAD
--=============================================================
local function refreshRecordingDropdown(preserve)
    if not Options or not Options.RecordingDropdown then return end
    local names = listRecordings()
    if #names == 0 then names = { "(no recordings)" } end
    pcall(function() Options.RecordingDropdown:SetValues(names, true) end)
    if preserve then
        for i, n in ipairs(names) do
            if n == preserve then
                pcall(function() Options.RecordingDropdown:SetValue(i) end)
                break
            end
        end
    end
end

local function saveRecording(name)
    name = tostring(name or ""):gsub("%s+", " ")
    if name == "" then setStatus("Enter a recording name first"); return end
    name = name:gsub("[\\/:*?\"<>|]", "_")
    if not ensureRecordingsFolder() then
        setStatus("Could not create recordings folder"); return
    end
    if type(writefile) ~= "function" then setStatus("writefile unavailable"); return end

    local out = {}
    for _, a in ipairs(Recording) do
        table.insert(out, {
            t            = a.t,
            path         = a.path,
            name         = a.name,
            method       = a.method,
            args         = ser(a.args),
            money_before = a.money_before,
            money_after  = a.money_after,
        })
    end
    local ok, enc = pcall(function() return http:JSONEncode(out) end)
    if not ok then setStatus("encode failed"); return end

    local okWrite, err = pcall(writefile, recordingPath(name), enc)
    if not okWrite then
        setStatus("write failed: " .. tostring(err))
        return
    end
    setStatus(("Saved %d actions -> %s.json"):format(#Recording, name))
    SelectedRecording = name
    saveLastSelected(name)
    refreshRecordingDropdown(name)
end

function loadRecording(name)
    if not name or name == "" then setStatus("Pick a recording first"); return end
    if type(readfile) ~= "function" or type(isfile) ~= "function" then
        setStatus("file functions unavailable"); return
    end
    local path = recordingPath(name)
    if not isfile(path) then setStatus("file not found: " .. name .. ".json"); return end

    local ok, dec = pcall(function() return http:JSONDecode(readfile(path)) end)
    if not ok or type(dec) ~= "table" then setStatus("decode failed"); return end

    Recording = {}
    for _, a in ipairs(dec) do
        local entryName = a.name
        if not entryName and a.path then
            entryName = tostring(a.path):match("[^%.]+$")
        end

        table.insert(Recording, {
            t            = a.t,
            path         = a.path,
            name         = entryName,
            method       = a.method,
            args         = deser(a.args),
            money_before = a.money_before,
            money_after  = a.money_after,
        })
    end
    setStatus(("Loaded %d actions from %s.json"):format(#Recording, name))
end

--=============================================================
--  RECORDINGS UI
--=============================================================
LeftBox:AddButton({
    Text = 'Start Recording',
    Func = function()
        Recording             = {}
        RecordedSpawnedTowers = {}
        RecordStart           = os.clock()
        LastRecordT           = 0
        IsRecording           = true
        installHook()
        setStatus("Recording... 0 actions")
    end
})

LeftBox:AddButton({
    Text = 'Stop Recording',
    Func = function()
        if not IsRecording then return end
        IsRecording = false
        uninstallHook()
        setStatus(("Stopped — %d actions"):format(#Recording))
    end
})

LeftBox:AddButton({
    Text = 'Clear Recording (in memory)',
    Func = function()
        Recording = {}
        setStatus("Recording cleared from memory")
    end
})

LeftBox:AddDivider()

LeftBox:AddDropdown('RecordingDropdown', {
    Values  = (function()
        local names = listRecordings()
        if #names == 0 then names = { "(no recordings)" } end
        return names
    end)(),
    Default = 1,
    Multi   = false,
    Text    = 'Recording',
    Tooltip = 'Pick a recording from ' .. RECORDINGS_FOLDER,
    Callback = function(value)
        if value and value ~= "(no recordings)" then
            SelectedRecording = value
            saveLastSelected(value)
            setStatus("Selected: " .. value)
        end
    end
})

LeftBox:AddInput('RecordingNameInput', {
    Text = 'Save as',
    Default = "",
    Placeholder = 'my_run',
    Numeric = false,
    Finished = false,
    Callback = function() end
})

LeftBox:AddButton({
    Text = 'Save Recording',
    Func = function()
        local name = Options.RecordingNameInput and Options.RecordingNameInput.Value or ""
        saveRecording(name)
    end
})

LeftBox:AddButton({
    Text = 'Load Selected',
    Func = function() loadRecording(SelectedRecording) end
})

LeftBox:AddButton({
    Text = 'Refresh List',
    Func = function()
        refreshRecordingDropdown(SelectedRecording)
        setStatus("Recording list refreshed")
    end
})

LeftBox:AddButton({
    Text = 'Delete Selected',
    Func = function()
        if not SelectedRecording then setStatus("Pick a recording first"); return end
        if type(delfile) ~= "function" then setStatus("delfile unavailable"); return end
        local path = recordingPath(SelectedRecording)
        if isfile(path) then
            local ok = pcall(delfile, path)
            if ok then
                setStatus("Deleted " .. SelectedRecording .. ".json")
                SelectedRecording = nil
                saveLastSelected("")
                refreshRecordingDropdown()
            else
                setStatus("delete failed")
            end
        else
            setStatus("file not found")
        end
    end
})

--=============================================================
--  PLAYBACK UI
--=============================================================
RightBox:AddButton({
    Text = 'Play Recording',
    Func = function() startPlayback() end,
    Tooltip = 'Loads the selected recording (if needed) and replays it once.',
})

RightBox:AddButton({
    Text = 'Stop Playback',
    Func = function() stopPlayback() end,
    Tooltip = 'Cancels a running or pending replay.',
})

--=============================================================
--  PLAYBACK START DELAY UI
--=============================================================
DelayBox:AddSlider('PlaybackDelaySlider', {
    Text = 'Wait until round timer reaches',
    Default = 0,
    Min = 0,
    Max = 30,
    Rounding = 0,
    Suffix = 's',
    Compact = false,
    Tooltip = '0 = play immediately. Otherwise playback starts when workspace.Info.Time.Timer hits this value.',
    Callback = function(v)
        PlaybackDelay = v
    end,
})

DelayBox:AddToggle('AutoPlayToggle', {
    Text = 'Auto Play',
    Default = false,
    Tooltip = 'Automatically plays the selected recording each round once the timer reaches the delay above.',
    Callback = function(state)
        AutoPlayEnabled = state
        if state then
            if #Recording == 0 and SelectedRecording then
                loadRecording(SelectedRecording)
            end
            setStatus("Auto Play: enabled")
            task.spawn(autoPlayLoop)
        else
            setStatus("Auto Play: disabled")
        end
    end,
})

SkipBox:AddToggle('AutoSkipToggle', {
    Text = 'Skip Round',
    Default = false,
    Tooltip = 'Fires VoteSkip on toggle. While enabled, keeps LocalPlayer.AutoSkip on.',
    Callback = function(state)
        pcall(function()
            game:GetService("ReplicatedStorage").Remotes.VoteSkip:FireServer()
        end)

        if state then
            AutoSkipKeepEnabled = true
            setStatus("Skip: enabled (watching AutoSkip)")
            task.spawn(autoSkipWatchLoop)
        else
            AutoSkipKeepEnabled = false
            setStatus("Skip: disabled (AutoSkip left alone)")
        end
    end,
})

AutoReplayBox:AddToggle('AutoReplayToggle', {
    Text = 'Auto Replay',
    Default = false,
    Tooltip = 'Fires ReplicatedStorage.Events.Replay when the round timer stalls for 5s.',
    Callback = function(state)
        AutoReplayEnabled = state
        if state then
            setStatus("Auto Replay: enabled")
            task.spawn(autoReplayLoop)
        else
            setStatus("Auto Replay: disabled")
        end
    end,
})

--=============================================================
--  UI SETTINGS
--=============================================================
local MenuGroup = Tabs['UI Settings']:AddLeftGroupbox('Menu')

MenuGroup:AddButton({ Text = 'Unload', Func = function() Library:Unload() end })
MenuGroup:AddLabel('Menu bind'):AddKeyPicker('MenuKeybind', {
    Default = 'RightShift', NoUI = true, Text = 'Menu keybind'
})
Library.ToggleKeybind = Options.MenuKeybind

ThemeManager:SetLibrary(Library)
SaveManager:SetLibrary(Library)

SaveManager:IgnoreThemeSettings()
SaveManager:SetIgnoreIndexes({})

ThemeManager:SetFolder('TDAutoFarm')
SaveManager:SetFolder('TDAutoFarm')

SaveManager:BuildConfigSection(Tabs['UI Settings'])
ThemeManager:ApplyToTab(Tabs['UI Settings'])

task.spawn(function()
    task.wait(0.5)

    local last = loadLastSelected()
    if last and last ~= "" then
        SelectedRecording = last
        setStatus("Restored last recording: " .. last)
        local ok2 = pcall(loadRecording, last)
        if ok2 and #Recording > 0 then
            refreshRecordingDropdown(last)
            print("[AutoFarm] auto-loaded recording: " .. last)
        end
    end

    local ok, err = pcall(function()
        SaveManager:LoadAutoloadConfig()
    end)
    if not ok then
        warn("[AutoFarm] autofarm autoload failed: " .. tostring(err))
    else
        print("[AutoFarm] autoload attempted")
    end
end)

--=============================================================
--  KEYBINDS
--=============================================================
UIS.InputBegan:Connect(function(input, gp)
    if gp or UIS:GetFocusedTextBox() then return end
    if input.KeyCode == Enum.KeyCode.F1 then
        if IsRecording then
            IsRecording = false
            uninstallHook()
            setStatus(("Stopped — %d actions"):format(#Recording))
        else
            Recording             = {}
            RecordedSpawnedTowers = {}
            RecordStart           = os.clock()
            LastRecordT           = 0
            IsRecording           = true
            installHook()
            setStatus("Recording... 0 actions")
        end
    elseif input.KeyCode == Enum.KeyCode.F2 then
        local name = Options.RecordingNameInput and Options.RecordingNameInput.Value or ""
        saveRecording(name)
    elseif input.KeyCode == Enum.KeyCode.F3 then
        if IsReplaying then
            stopPlayback()
        else
            startPlayback()
        end
    end
end)

--=============================================================
--  STARTUP
--=============================================================
if setupMoney() then
    print("[AutoFarm] money resolved: " .. tostring(cachedMoney))
else
    warn("[AutoFarm] could not resolve money at startup")
end

print("[AutoFarm] Loaded. F1 record toggle, F2 save, F3 play once.")