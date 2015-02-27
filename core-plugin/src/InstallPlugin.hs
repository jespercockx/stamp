module InstallPlugin where

import ShowCore
import GhcPlugins
import MAlonzo.Code.Plugin

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
}


bindsOnlyPassWithGuts :: (ModGuts -> CoreProgram -> CoreM CoreProgram) -> ModGuts -> CoreM ModGuts
bindsOnlyPassWithGuts pass guts
  = do { binds' <- pass guts (mg_binds guts)
       ; return (guts { mg_binds = binds' }) }


install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install options todo = do
  reinitializeGlobals
  let pass = agdaMetaPass options
  return (CoreDoPluginPass "Show Core" (bindsOnlyPass showCore) :
          CoreDoPluginPass "Agda meta-programming" (bindsOnlyPassWithGuts pass) :
          CoreDoPluginPass "Show Core" (bindsOnlyPass showCore) : todo)
