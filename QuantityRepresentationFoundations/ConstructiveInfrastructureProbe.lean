import QuantityRepresentationFoundations.PrimitiveAxiomFreeCarryRigidity

namespace QuantityRepresentationFoundations.ConstructiveInfrastructureProbe

universe u

/-- Decidable equality used only through a nondependent `if`. -/
def eqIf {α : Type u} [DecidableEq α] (a b : α) : Bool :=
  if a = b then true else false

/-- The same test written as a dependent `if`, while ignoring the proof binder. -/
def eqDite {α : Type u} [DecidableEq α] (a b : α) : Bool :=
  if _h : a = b then true else false

/-- `Option` itself, without finite indexing. -/
def optionMap {α β : Type u} (f : α → β) : Option α → Option β
  | none => none
  | some a => some (f a)

/-- Successor embedding between adjacent `Fin` windows. -/
def finSucc {N : ℕ} (i : Fin N) : Fin (N + 1) := i.succ

/-- Explicit zero of a nonempty `Fin`, avoiding the generic numeral instance. -/
def finZero (N : ℕ) : Fin (N + 1) :=
  ⟨0, Nat.zero_lt_succ N⟩

/-- One finite search step using the generic `0 : Fin (N+1)` numeral. -/
def oneStep {Code : Type u} [DecidableEq Code]
    {N : ℕ} (encode : Fin (N + 1) → Code) (c : Code)
    (tail : Option (Fin N)) : Option (Fin (N + 1)) :=
  if encode 0 = c then
    some 0
  else
    match tail with
    | none => none
    | some i => some i.succ

/-- The same step with an explicitly constructed finite zero. -/
def oneStepExplicit {Code : Type u} [DecidableEq Code]
    {N : ℕ} (encode : Fin (N + 1) → Code) (c : Code)
    (tail : Option (Fin N)) : Option (Fin (N + 1)) :=
  let z : Fin (N + 1) := finZero N
  if encode z = c then
    some z
  else
    match tail with
    | none => none
    | some i => some i.succ

/-- One finite search step using a Boolean equality oracle and a generic Fin numeral. -/
def oneStepBool {Code : Type u}
    (eqb : Code → Code → Bool)
    {N : ℕ} (encode : Fin (N + 1) → Code) (c : Code)
    (tail : Option (Fin N)) : Option (Fin (N + 1)) :=
  if eqb (encode 0) c then
    some 0
  else
    match tail with
    | none => none
    | some i => some i.succ

/-- Boolean-oracle version with explicit finite zero. -/
def oneStepBoolExplicit {Code : Type u}
    (eqb : Code → Code → Bool)
    {N : ℕ} (encode : Fin (N + 1) → Code) (c : Code)
    (tail : Option (Fin N)) : Option (Fin (N + 1)) :=
  let z : Fin (N + 1) := finZero N
  if eqb (encode z) c then
    some z
  else
    match tail with
    | none => none
    | some i => some i.succ

end QuantityRepresentationFoundations.ConstructiveInfrastructureProbe

#print axioms QuantityRepresentationFoundations.ConstructiveInfrastructureProbe.eqIf
#print axioms QuantityRepresentationFoundations.ConstructiveInfrastructureProbe.eqDite
#print axioms QuantityRepresentationFoundations.ConstructiveInfrastructureProbe.optionMap
#print axioms QuantityRepresentationFoundations.ConstructiveInfrastructureProbe.finSucc
#print axioms QuantityRepresentationFoundations.ConstructiveInfrastructureProbe.finZero
#print axioms QuantityRepresentationFoundations.ConstructiveInfrastructureProbe.oneStep
#print axioms QuantityRepresentationFoundations.ConstructiveInfrastructureProbe.oneStepExplicit
#print axioms QuantityRepresentationFoundations.ConstructiveInfrastructureProbe.oneStepBool
#print axioms QuantityRepresentationFoundations.ConstructiveInfrastructureProbe.oneStepBoolExplicit
#print axioms Fin.succ
#print axioms dite
#print axioms ite
