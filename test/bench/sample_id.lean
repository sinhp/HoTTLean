import Lean.Elab.Command

open Lean Meta Elab Term Command


elab "#gen_ids" num:num : command => liftTermElabM do
  -- fun (x : Type 1) => x
  let idFn := Expr.lam `x (.sort 2) (.bvar 0) default
  let mut acc := .sort 1 -- Type 0
  for i in [0 : num.getNat] do
    let name : Name := Name.str .anonymous s!"BenchDef_id_{i}"
    if i != 0 then do
      acc := .app idFn acc
    let accPP ← ppExpr acc
    logInfo m!"acc[{i}] := {accPP}"
    addDecl <| .defnDecl
      { name,
        levelParams := [],
        type := ← inferType acc,
        value := acc,
        hints := default
        safety := .safe }

#gen_ids 40

-- open Char
-- def isSampleBenchDef (n : Name) : Bool :=
--   match n with
--   | .str (.str _ s1) s2 =>
--     -- components come as: ... → "sample<n>" (s1) ← "benchDef_<m>" (s2) ← _ (rest)
--     let ok1 := s1.startsWith "sample"
--       && isDigit ((s1.drop 6).get 0)
--     let ok2 := s2.startsWith "benchDef_"
--       && isDigit ((s2.drop 9).get 0)
--     ok1 && ok2
--   | _ => false

-- elab "#gen_id" num:num : command => liftTermElabM do
--   let env ← getEnv
--   for (n, ci) in env.constants do
--     if !isSampleBenchDef n then continue
--     let .defnInfo d := ci | continue
--     let mut acc := d.value
--     try
--       for i in [0 : num.getNat] do
--         let name : Name := n ++ Name.str .anonymous s!"id_{i}"
--         if i != 0 then do acc ← mkAppM ``id #[acc] --mkAppM' (mkConst ``id) #[acc]
--         addDecl <| .defnDecl
--           { name,
--             levelParams := d.levelParams,
--             type := d.type,
--             value := acc,
--             hints := d.hints
--             safety := d.safety }

--     catch ex =>
--       logInfo m!"gen_id error :\n{ex.toMessageData}"
--       continue
