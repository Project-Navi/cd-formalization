/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal
import Spec

/-!
# Comparator for the statement files

`#check_statements` takes every theorem `Spec.name` in the module `Spec` (`spec/Spec.lean`) and
checks it against the library declaration `name`:

1. the statement's proof is `sorry` itself (`isBareSorry`: exactly Lean's sorry under the
   statement's binders, not applied to anything), so the statement file states and does not
   prove;
2. the library declaration exists and is a theorem, not an axiom or an opaque constant;
3. the two types are equal up to binder names and annotations, after the statement's universe
   parameters are replaced by the library's;
4. the library proof uses no axiom outside `propext`, `Classical.choice` and `Quot.sound`
   (the walk is `Lean.collectAxioms`, transitive over the proof term).

It prints `SPEC OK name` for each match and fails with every mismatch listed. CI also requires
each headline result to have a `SPEC OK` line. Run with `lake env lean spec/Check.lean` after
`lake build Spec`.
-/

open Lean Elab Command

/-- The axioms a library proof may use. -/
def specAllowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `v`, the proof of a statement, is `sorry` itself: under the statement's binders,
    Lean's labelled sorry `sorryAx (∀ tag : Name, T) false tag`, with a closed label built from
    `Lean.Name` constructors and `Nat` literals only, or the unlabelled `sorryAx T false`. A sorry
    applied to further arguments, wrapped in `let` or `have`, or inside an otherwise real proof
    is not. The kernel has already checked that `T` is the statement's conclusion. -/
def isBareSorry (v : Expr) : Bool := Id.run do
  let mut v := v.consumeMData
  while v.isLambda do
    v := v.bindingBody!.consumeMData
  unless v.isAppOf ``sorryAx do return false
  match v.getAppArgs with
  | #[_, synthetic] => return synthetic.isConstOf ``Bool.false
  | #[t, synthetic, tag] =>
    -- The label is data: `Lean.Name` constructors and `Nat` literals (`OfNat.ofNat`).
    let nameOnly := tag.getUsedConstants.all (fun c => (`Lean.Name).isPrefixOf c ||
      [``OfNat.ofNat, ``Nat, ``instOfNatNat].contains c)
    match t.consumeMData with
    | .forallE _ (.const ``Lean.Name []) body _ =>
      return synthetic.isConstOf ``Bool.false && !tag.hasLooseBVars && !tag.hasFVar &&
        !tag.hasMVar && nameOnly && !body.hasLooseBVar 0
    | _ => return false
  | _ => return false

/-- Check every statement of the module `Spec`; see the module docstring. -/
elab "#check_statements" : command => do
  let env ← getEnv
  let mut statements : Array ConstantInfo := #[]
  for mod in env.header.moduleNames, data in env.header.moduleData do
    if mod == `Spec then
      statements := data.constants.filter (fun c => !c.name.isInternal)
  if statements.isEmpty then
    throwError "no statements found in the module Spec"
  let mut errors : Array MessageData := #[]
  for s in statements do
    let name := s.name.replacePrefix `Spec Name.anonymous
    let .thmInfo st := s
      | errors := errors.push m!"{s.name}: a statement file may declare theorems only"; continue
    -- The proof must be `sorry` itself (see `isBareSorry`): depending on `sorryAx` somewhere,
    -- or applying a sorry to further arguments, is not enough.
    unless isBareSorry st.value do
      errors := errors.push m!"{s.name}: the statement is proved; its proof must be sorry"
      continue
    let some d := env.find? name
      | errors := errors.push m!"{name}: no library declaration"; continue
    unless d matches .thmInfo _ do
      errors := errors.push m!"{name}: the library declaration is not a theorem"
      continue
    unless s.levelParams.length == d.levelParams.length do
      errors := errors.push m!"{name}: {s.levelParams.length} universe parameters in the \
        statement, {d.levelParams.length} in the library"
      continue
    let sType := s.type.instantiateLevelParams s.levelParams (d.levelParams.map Level.param)
    unless sType == d.type do
      errors := errors.push m!"{name}: the statement differs from the library\n  \
        statement: {sType}\n  library:   {d.type}"
      continue
    let axioms ← collectAxioms name
    let bad := axioms.filter (fun a => !specAllowedAxioms.contains a)
    unless bad.isEmpty do
      errors := errors.push m!"{name}: the library proof uses {bad}"
      continue
    logInfo m!"SPEC OK {name}"
  unless errors.isEmpty do
    throwError m!"statement check failed:\n{MessageData.joinSep errors.toList "\n"}"
  logInfo m!"{statements.size} statements match the library"

#check_statements
