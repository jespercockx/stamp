module InstallPlugin where

import GhcPlugins
import MAlonzo.Code.Plugin

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  reinitializeGlobals
  hello
  return todo
