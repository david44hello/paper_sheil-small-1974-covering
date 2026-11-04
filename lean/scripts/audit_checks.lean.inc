/- Audit commands (inserted into Sheil/Audit.lean by scripts/audit.py).
Inspect elaborated signatures, including project definition aliases and structure fields.
No proof bodies are searched and no check is assumed. -/
namespace SheilAudit
open Lean Elab Command

partial def checksIn (env : Environment) (e : Expr) (seen : NameSet := {}) : NameSet := Id.run do
  match e with
  | .const n _ =>
    if "Sheil.ComputerChecked.Check".isPrefixOf n.toString then
      return ({} : NameSet).insert n
    if seen.contains n || !("Sheil.".isPrefixOf n.toString) then return {}
    let seen := seen.insert n
    match env.find? n with
    | some (.defnInfo info) => return (checksIn env info.type seen).union (checksIn env info.value seen)
    | some (.opaqueInfo info) => return (checksIn env info.type seen).union (checksIn env info.value seen)
    | some (.inductInfo info) =>
      let mut found : NameSet := {}
      for ctor in info.ctors do
        if let some ci := env.find? ctor then
          found := found.union (checksIn env ci.type seen)
      return found
    | _ => return {}
  | .app f a => return (checksIn env f seen).union (checksIn env a seen)
  | .lam _ t b _ | .forallE _ t b _ => return (checksIn env t seen).union (checksIn env b seen)
  | .letE _ t v b _ => return ((checksIn env t seen).union (checksIn env v seen)).union (checksIn env b seen)
  | .mdata _ b | .proj _ _ b => return checksIn env b seen
  | _ => return {}

def namesCSV (names : NameSet) : String :=
  String.intercalate "," ((names.toList.map Name.toString).mergeSort (· ≤ ·))

partial def hypothesisChecks (env : Environment) (e : Expr) : NameSet :=
  match e with
  | .forallE _ t b _ => (checksIn env t).union (hypothesisChecks env b)
  | _ => {}

partial def bareInput (e : Expr) : String :=
  match e with
  | .lam _ _ b _ | .mdata _ b => bareInput b
  | _ => match e.getAppFn with
    | .const n _ => if "Sheil.Cited.".isPrefixOf n.toString then n.toString else ""
    | _ => ""

def inspect (name : Name) (label : String) : CommandElabM Unit := do
  let env ← getEnv
  let info ← getConstInfo name
  logInfo m!"GKCHECK|{label}|{namesCSV (checksIn env info.type)}|{namesCSV (hypothesisChecks env info.type)}|END"
  let direct := match info with
    | .thmInfo ti => bareInput ti.value
    | _ => ""
  logInfo m!"GKDIRECT|{label}|{direct}|END"
end SheilAudit
