import QuantityRepresentationFoundations.UnitDynamicsLocalRecurrence

/-!
# First local return and emergent local capacity

The previous layer proves that an infinite nonrepeating unit trajectory observed
through a finite local state must recur somewhere.  That alone does not imply
that the initial local state returns: a finite dynamical system may have a
transient tail before entering a cycle.

This module isolates a minimal additional operational hypothesis that removes
that ambiguity without introducing positional arithmetic:

* the local observation evolves autonomously through a local step map;
* the local step map is injective, so local information is not erased.

No numeral base, quotient, remainder, division, modulo, positional weight,
normalization, or carry is assumed.

Under these hypotheses a positive return to the initial local state exists.  Its
least positive return is canonical and unique.  We call that least return the
`EmergentLocalCapacity`; the name records the theorem's intended role, not an
assumed radix structure.
-/

namespace QuantityRepresentationFoundations

/--
An autonomous, information-preserving local observation of a unit trajectory.

`intertwines` says that observing one global unit step is the same as applying
one local step.  `step_injective` says the local step does not merge distinct
local states.
-/
structure AutonomousLocalDynamics
    {Q : Type*}
    (trajectory : UnitTrajectory Q)
    (LocalState : Type*) where
  observe : Q → LocalState
  step : LocalState → LocalState
  intertwines : ∀ q, observe (trajectory.transition q) = step (observe q)
  step_injective : Function.Injective step

/--
Autonomy identifies the observed trajectory with iteration of the local step
from the initial local observation.
-/
theorem autonomousLocalDynamics_orbit
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState) :
    ∀ n : ℕ,
      model.observe (trajectory.state n) =
        (model.step^[n]) (model.observe (trajectory.state 0)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        model.observe (trajectory.state (Nat.succ n)) =
            model.observe (trajectory.transition (trajectory.state n)) := by
              rw [show Nat.succ n = n + 1 by omega, trajectory.evolves]
        _ = model.step (model.observe (trajectory.state n)) :=
              model.intertwines _
        _ = model.step
              ((model.step^[n]) (model.observe (trajectory.state 0))) := by
              rw [ih]
        _ = (model.step^[Nat.succ n])
              (model.observe (trajectory.state 0)) := by
              symm
              exact Function.iterate_succ_apply' model.step n _

/-- A positive clock time at which the initial local observation returns. -/
def PositiveLocalReturn
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    (n : ℕ) : Prop :=
  0 < n ∧
    model.observe (trajectory.state n) =
      model.observe (trajectory.state 0)

/--
Finite local state plus autonomous injective local dynamics forces a positive
return to the initial local observation.

The proof starts from an arbitrary local recurrence supplied by finiteness and
uses injectivity of the local step to cancel the common prefix of the two
iterates.  Thus return-to-origin is derived rather than assumed.
-/
theorem autonomousLocalDynamics_has_positiveReturn
    {Q LocalState : Type*}
    [Finite LocalState]
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState) :
    ∃ b : ℕ, PositiveLocalReturn trajectory model b := by
  obtain ⟨m, n, hmn, hreadout⟩ :=
    unitTrajectory_forces_localRecurrence trajectory model.observe
  let x := model.observe (trajectory.state 0)
  have hm := autonomousLocalDynamics_orbit trajectory model m
  have hn := autonomousLocalDynamics_orbit trajectory model n
  have hiter : (model.step^[m]) x = (model.step^[n]) x := by
    rw [← hm, ← hn]
    exact hreadout
  have hreturnIter : (model.step^[n - m]) x = x :=
    Function.iterate_cancel model.step_injective hiter.symm
  refine ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  rw [autonomousLocalDynamics_orbit trajectory model (n - m)]
  exact hreturnIter

/--
Every positive return is a period of the entire local readout along the unit
trajectory.  This is a consequence of autonomous iteration, not an assumed
cyclic numeral convention.
-/
theorem positiveLocalReturn_implies_periodic_readout
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    {b : ℕ}
    (hb : PositiveLocalReturn trajectory model b) :
    ∀ n : ℕ,
      model.observe (trajectory.state (n + b)) =
        model.observe (trajectory.state n) := by
  let x := model.observe (trajectory.state 0)
  have hbOrbit := autonomousLocalDynamics_orbit trajectory model b
  have hbIter : (model.step^[b]) x = x := by
    rw [← hbOrbit]
    exact hb.2
  intro n
  rw [autonomousLocalDynamics_orbit trajectory model (n + b),
      autonomousLocalDynamics_orbit trajectory model n]
  calc
    (model.step^[n + b]) x =
        (model.step^[n]) ((model.step^[b]) x) :=
          Function.iterate_add_apply model.step n b x
    _ = (model.step^[n]) x := by rw [hbIter]

/--
`b` is an emergent local capacity when it is the least positive return time of
the autonomous local readout.

This definition contains no quotient, remainder, radix, digit, or carry.
-/
def EmergentLocalCapacity
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    (b : ℕ) : Prop :=
  PositiveLocalReturn trajectory model b ∧
    ∀ n : ℕ, PositiveLocalReturn trajectory model n → b ≤ n

/--
For finite autonomous injective local dynamics, the emergent local capacity
exists and is unique.
-/
theorem existsUnique_emergentLocalCapacity
    {Q LocalState : Type*}
    [Finite LocalState]
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState) :
    ∃! b : ℕ, EmergentLocalCapacity trajectory model b := by
  classical
  obtain ⟨b₀, hb₀⟩ := autonomousLocalDynamics_has_positiveReturn trajectory model
  let b := Nat.find ⟨b₀, hb₀⟩
  have hb : PositiveLocalReturn trajectory model b :=
    Nat.find_spec ⟨b₀, hb₀⟩
  have hmin : ∀ n : ℕ, PositiveLocalReturn trajectory model n → b ≤ n := by
    intro n hn
    exact Nat.find_min' ⟨b₀, hb₀⟩ hn
  refine ⟨b, ⟨hb, hmin⟩, ?_⟩
  intro c hc
  exact Nat.le_antisymm (hmin c hc.1) (hc.2 b hb)

/--
The canonical emergent capacity is automatically a period of every local
observation along the unit trajectory.
-/
theorem emergentLocalCapacity_periodic_readout
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    {b : ℕ}
    (hb : EmergentLocalCapacity trajectory model b) :
    ∀ n : ℕ,
      model.observe (trajectory.state (n + b)) =
        model.observe (trajectory.state n) :=
  positiveLocalReturn_implies_periodic_readout trajectory model hb.1

end QuantityRepresentationFoundations
