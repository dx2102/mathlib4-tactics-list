import Mathlib
import Lean

def x := 0

#eval Lean.Compiler.LCNF.builtinRuntimeTypes


#help cats

#help tactic
#help conv -- seems to be the same as `#help tactic`
#help cat tactic

#help command
#help option
#help term
#help attribute

open Lean Meta Elab Tactic Command Mathlib.Tactic



syntax withPosition("#myhelp " colGt &"cats" (colGt ppSpace Parser.rawIdent)) : command

private def elabHelpCat (catStx : Ident) : CommandElabM Unit := do
  let catName := catStx.getId.eraseMacroScopes
  let some cat := (Parser.parserExtension.getState (← getEnv)).categories.find? catName
    | throwErrorAt catStx "{catStx} is not a syntax category"
  liftTermElabM <| Term.addCategoryInfo catStx catName

  let mut msg := MessageData.nil
  let line := Format.line
  let env ← getEnv

  for (name, _) in cat.kinds do
    -- name : SyntaxNodeKind, where SyntaxNodeKind is a `Lean.Name`
    let headTk := do getHeadTk (← (← env.find? name).value?)
    let headTk := headTk |>.getD "..." |>.trim

    let mod ← findModuleOf? name
    let mod := mod |>.map Name.toString |>.getD "..."

    msg := (
      msg
      ++ m!"{headTk}"
      ++ line
      ++ m!"{mkConst name}"
      ++ line
      ++ m!"{mod}"
      ++ line
    )

    if let some doc ← findDocString? env name then
      msg := msg ++ doc.trim ++ line
    msg := msg ++ "----help----" ++ line

  logInfo msg

elab_rules : command | `(#myhelp cats $(id)) => elabHelpCat id

#myhelp cats tactic
#myhelp cats command
