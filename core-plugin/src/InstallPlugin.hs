module InstallPlugin where

import ShowCore
import GhcPlugins
import MAlonzo.Code.Plugin

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install options todo = do
  reinitializeGlobals
  let pass = agdaMetaPass options
  return (CoreDoPluginPass "Agda meta-programming" (bindsOnlyPass pass) :
          CoreDoPluginPass "Show Core" (bindsOnlyPass showCore) : todo)
