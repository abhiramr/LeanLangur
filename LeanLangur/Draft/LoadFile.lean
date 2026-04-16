import Lean
-- import LeanAideCore.Kernel
-- import LeanAideCore.Syntax.Kernel

open IO FS System Lean

def readme : IO String := readFile "README.md"

#eval readme

def lakeManifest : IO String := readFile "lake-manifest.json"

#eval lakeManifest

def lakeManifestJson : IO Json := do
  let content ← lakeManifest
  match Json.parse content with
  | .ok json => return json
  | .error err => IO.throwServerError s!"Failed to parse JSON: {err}"

#eval lakeManifestJson

def jsonEg := json% {"name": "LeanLangur", "version": "0.1.0", "dependencies": {"lean": "4.0.0"}}

#eval jsonEg

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

declare_syntax_cat filepath
syntax str : filepath
syntax filepath " / " str : filepath

partial def filePath : TSyntax `filepath → System.FilePath
  | `(filepath| $s:str) => s.getString
  | `(filepath| $fs:filepath / $s) => (filePath fs / s.getString)
  | _ => System.FilePath.mk ""

syntax (name:= loadFileTerm) "load_file%" (ppSpace filepath)? " ; " : term
@[term_elab loadFileTerm] def loadFileTermImpl : TermElab := fun stx _ => do
  match stx with
  | `(load_file% $file:filepath ; ) =>
    let filePath : System.FilePath := filePath file
    let content ← IO.FS.readFile filePath
    let stx' := Syntax.mkStrLit content
    TryThis.addSuggestion stx stx'
    return mkStrLit content
  | _ => throwUnsupportedSyntax

-- def egFile := load_file% "README.md" ;

-- #eval egFile

syntax (name:= loadJsonTerm) "load_json%" (ppSpace filepath)? " ; " : term
@[term_elab loadJsonTerm] def loadJsonTermImpl : TermElab := fun stx _ => do
  match stx with
  | `(load_json% $file:filepath ; ) =>
    let filePath : System.FilePath := filePath file
    let content ← IO.FS.readFile filePath
    let .ok json := Json.parse content | throwError "Failed to parse JSON: {content}"
    let rhs := "json% " ++ json.pretty
    TryThis.addSuggestion stx rhs
    let .ok termStx := runParserCategory (← getEnv) `term rhs | throwError "Failed to parse JSON syntax: {rhs}"
    elabTerm termStx (mkConst ``Json)
  | _ => throwUnsupportedSyntax

-- def egJson := load_json% "lake-manifest.json" ;

-- #eval egJson

syntax (name:= loadFile) "#load_file" (ppSpace ident)? (ppSpace filepath)? : command
@[command_elab loadFile] def loadFileImpl : CommandElab := fun stx  =>
 Command.liftTermElabM  do
  match stx with
  | `(command| #load_file $id:ident $file) =>
    let filePath : System.FilePath := filePath file
    let content ← try
        IO.FS.readFile filePath
      catch _ =>
        if ← filePath.isDir then
          let files ← filePath.readDir
          let files := files.map (·.fileName)
          for f in files do
            let name := Syntax.mkStrLit f
            let newPath ← `(filepath| $file / $name)
            let newCommand ← `(command| #load_file $id $newPath)
            TryThis.addSuggestion stx newCommand
        else
          logWarning s!"Failed to read file: {filePath}"
        return
    let name := id.getId
    let contentLit := Syntax.mkStrLit content
    let nameIdent := mkIdent name
    let textCmd ← `(command| def $nameIdent := $contentLit:str)
    TryThis.addSuggestion (header := "Load source:\n") stx textCmd
  | `(command| #load_file $file:filepath) =>
    let filePath : System.FilePath := filePath file
    let content ← try
        IO.FS.readFile filePath

      catch _ =>
        if ← filePath.isDir then
          let files ← filePath.readDir
          let files := files.map (·.fileName)
          for f in files do
            let name := Syntax.mkStrLit f
            let newPath ← `(filepath| $file / $name)
            let newCommand ← `(command| #load_file $newPath:filepath)
            TryThis.addSuggestion stx newCommand
        else
          logWarning s!"Failed to read file: {filePath}"
        return
    let name := filePath.fileName.getD "source"
    let contentLit := Syntax.mkStrLit content
    let nameIdent := mkIdent name.toName
    let textCmd ← `(command| def $nameIdent := $contentLit:str)
    TryThis.addSuggestion (header := "Load source:\n") stx textCmd
  | `(command| #load_file $id:ident) =>
    let filePath : System.FilePath := "."
    let files ← filePath.readDir
    let files := files.map (·.fileName)
    for f in files do
      let name := Syntax.mkStrLit f
      let newPath ← `(filepath| $name:str)
      let newCommand ← `(command| #load_file $id $newPath:filepath)
      TryThis.addSuggestion stx newCommand
  | `(command| #load_file) =>
    let filePath : System.FilePath := "."
    let files ← filePath.readDir
    let files := files.map (·.fileName)
    for f in files do
      let name := Syntax.mkStrLit f
      let newPath ← `(filepath| $name:str)
      let newCommand ← `(command| #load_file $newPath:filepath)
      TryThis.addSuggestion stx newCommand
  | _ => throwUnsupportedSyntax

-- #consider "Hello there."

declare_syntax_cat json_wrap
syntax json : json_wrap

def getJsonSyntax (js : Json) : MetaM <| TSyntax `json := do
  let .ok stx :=
    runParserCategory (← getEnv) `json_wrap js.pretty | throwError "Failed to parse JSON: {js}"
  match stx with
  | `(json_wrap| $j:json) =>
    return j
  | _ => throwError "Unexpected syntax: {stx}"

-- Test code
syntax (name:= rt_json) "#rt_json" ppSpace json : command

@[command_elab rt_json] def elabRtJsonImpl : CommandElab
| stx_cmd@`(command| #rt_json $js:json) =>
  Command.liftTermElabM do
  let tExp ← elabTerm (← `(json% $js)) (mkConst ``Json)
  Term.synthesizeSyntheticMVarsNoPostponing
  let term ← unsafe evalExpr Json (mkConst ``Json) tExp
  let stx ← getJsonSyntax term -- extract syntax from JSON
  logInfo m!"JSON Syntax: {stx}"
  let n := mkIdent `json_example
  let cmd ← `(command| def $n := json% $stx:json)
  logInfo m!"Command: {cmd}"
  TryThis.addSuggestion stx_cmd cmd
  logInfo m!"Done"
| _ => throwUnsupportedSyntax

-- #rt_json {"c": {"d": -3.4}, "b": [true, false, null], "a": 1}
