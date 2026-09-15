import QuantityRepresentationFoundations.EmergentQuotientRemainder

/-!
# Classical quotient-remainder crosswalk

The emergent quotient and remainder were constructed recursively from unit-step
cycle dynamics before any use of `Nat.div` or `Nat.mod`.

This module introduces the standard Euclidean quotient and remainder only as a
**downstream comparison**.  The proof strategy is deliberately one-way:

1. the classical pair `(n / b, n % b)` satisfies the same bounded cycle
   decomposition specification;
2. the emergent pair already satisfies that specification;
3. uniqueness of bounded cycle coordinates forces the two pairs to coincide.

Thus `Nat.div` and `Nat.mod` identify the independently constructed emergent
operations; they do not define or justify them retroactively.
-/

namespace QuantityRepresentationFoundations

/--
The standard natural-number quotient and remainder satisfy the cycle
specification for every positive capacity.
-/
theorem classicalQuotientRemainder_isCycleDecomposition
    (b n : ℕ) (hb : 0 < b) :
    IsCycleDecomposition b n (n / b) (n % b) := by
  constructor
  · calc
      n = n % b + b * (n / b) := (Nat.mod_add_div n b).symm
      _ = (n / b) * b + n % b := by ac_rfl
  · exact Nat.mod_lt n hb

/--
The recursively constructed emergent quotient is exactly the standard natural
number quotient, but only after both have independently been characterized by
the same unique bounded decomposition.
-/
theorem emergentQuotient_eq_div
    (b n : ℕ) (hb : 0 < b) :
    emergentQuotient b n = n / b := by
  have h := cycleDecomposition_eq_emergent hb
    (classicalQuotientRemainder_isCycleDecomposition b n hb)
  exact h.1.symm

/--
The recursively constructed emergent remainder is exactly the standard natural
number remainder, by uniqueness of the bounded cycle decomposition.
-/
theorem emergentRemainder_eq_mod
    (b n : ℕ) (hb : 0 < b) :
    emergentRemainder b n = n % b := by
  have h := cycleDecomposition_eq_emergent hb
    (classicalQuotientRemainder_isCycleDecomposition b n hb)
  exact h.2.symm

/-- The whole recursively generated coordinate pair is the classical QR pair. -/
theorem cycleCoordinatesRec_eq_classicalQuotientRemainder
    (b n : ℕ) (hb : 0 < b) :
    cycleCoordinatesRec b n = (n / b, n % b) := by
  apply Prod.ext
  · exact emergentQuotient_eq_div b n hb
  · exact emergentRemainder_eq_mod b n hb

/--
Canonical identification theorem: the independently constructed emergent
coordinates and the standard Euclidean quotient/remainder are the same data.
-/
theorem emergentQuotientRemainder_eq_classical
    (b n : ℕ) (hb : 0 < b) :
    emergentQuotient b n = n / b ∧
      emergentRemainder b n = n % b :=
  ⟨emergentQuotient_eq_div b n hb, emergentRemainder_eq_mod b n hb⟩

/--
For a dynamically emergent local capacity, its recursively generated cycle
coordinates coincide with the standard Euclidean quotient and remainder.
-/
theorem emergentLocalCapacity_eq_classicalQuotientRemainder
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    {b : ℕ}
    (hb : EmergentLocalCapacity trajectory model b)
    (n : ℕ) :
    emergentQuotient b n = n / b ∧
      emergentRemainder b n = n % b :=
  emergentQuotientRemainder_eq_classical b n hb.1.1

/--
Consequently the local readout at time `n` is the readout at the standard
Euclidean remainder, but this fact is obtained only after the emergent residual
has already been constructed and shown to control the local state.
-/
theorem classicalRemainder_controls_emergentLocalReadout
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    {b : ℕ}
    (hb : EmergentLocalCapacity trajectory model b)
    (n : ℕ) :
    model.observe (trajectory.state n) =
      model.observe (trajectory.state (n % b)) := by
  rw [← emergentRemainder_eq_mod b n hb.1.1]
  exact emergentRemainder_controls_localReadout trajectory model hb n

end QuantityRepresentationFoundations
