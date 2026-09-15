import QuantityRepresentationFoundations.EmergentCycleDecomposition

/-!
# Emergent quotient and remainder

The previous layer proves that every external step count `n` admits a unique
cycle decomposition

`n = q * b + r`, with `r < b`,

for every positive emergent local capacity `b`, without using `Nat.div` or
`Nat.mod`.

This module now defines the two coordinates themselves by the unit-step
recursion that was already implicit in that existence proof.  The definitions
remain independent of the standard quotient/remainder API.

At each successor step:

* if the residual coordinate can advance while staying below `b`, only the
  residual changes;
* otherwise one full cycle is completed, the cycle counter increases, and the
  residual resets to zero.

Only after these operations are constructed and characterized will a later
module compare them with the standard Euclidean quotient and remainder.
-/

namespace QuantityRepresentationFoundations

/-- One recursive update of cycle-count/residual coordinates. -/
def nextCycleCoordinates (b : ℕ) (coordinates : ℕ × ℕ) : ℕ × ℕ :=
  if coordinates.2 + 1 < b then
    (coordinates.1, coordinates.2 + 1)
  else
    (coordinates.1 + 1, 0)

/--
Recursive cycle coordinates generated from the unit-step clock.

No division or modulo operation occurs in this definition.
-/
def cycleCoordinatesRec (b : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 => nextCycleCoordinates b (cycleCoordinatesRec b n)

/-- The recursively generated completed-cycle count. -/
def emergentQuotient (b n : ℕ) : ℕ :=
  (cycleCoordinatesRec b n).1

/-- The recursively generated position inside the current cycle. -/
def emergentRemainder (b n : ℕ) : ℕ :=
  (cycleCoordinatesRec b n).2

@[simp] theorem emergentQuotient_zero (b : ℕ) :
    emergentQuotient b 0 = 0 := by
  rfl

@[simp] theorem emergentRemainder_zero (b : ℕ) :
    emergentRemainder b 0 = 0 := by
  rfl

/--
The recursive coordinates always satisfy the independently proved cycle
specification whenever the capacity is positive.
-/
theorem cycleCoordinatesRec_isCycleDecomposition
    (b : ℕ) (hb : 0 < b) :
    ∀ n : ℕ,
      IsCycleDecomposition b n
        (cycleCoordinatesRec b n).1
        (cycleCoordinatesRec b n).2 := by
  intro n
  induction n with
  | zero =>
      exact ⟨by simp [cycleCoordinatesRec], hb⟩
  | succ n ih =>
      rcases ih with ⟨hvalue, hresidual⟩
      by_cases hnext : (cycleCoordinatesRec b n).2 + 1 < b
      · change IsCycleDecomposition b (Nat.succ n)
          (nextCycleCoordinates b (cycleCoordinatesRec b n)).1
          (nextCycleCoordinates b (cycleCoordinatesRec b n)).2
        rw [show nextCycleCoordinates b (cycleCoordinatesRec b n) =
            ((cycleCoordinatesRec b n).1,
              (cycleCoordinatesRec b n).2 + 1) by
          simp [nextCycleCoordinates, hnext]]
        change Nat.succ n =
            (cycleCoordinatesRec b n).1 * b +
              ((cycleCoordinatesRec b n).2 + 1) ∧
          (cycleCoordinatesRec b n).2 + 1 < b
        constructor
        · omega
        · exact hnext
      · have hboundary : (cycleCoordinatesRec b n).2 + 1 = b := by
          omega
        change IsCycleDecomposition b (Nat.succ n)
          (nextCycleCoordinates b (cycleCoordinatesRec b n)).1
          (nextCycleCoordinates b (cycleCoordinatesRec b n)).2
        rw [show nextCycleCoordinates b (cycleCoordinatesRec b n) =
            ((cycleCoordinatesRec b n).1 + 1, 0) by
          simp [nextCycleCoordinates, hnext]]
        change Nat.succ n =
            ((cycleCoordinatesRec b n).1 + 1) * b + 0 ∧ 0 < b
        constructor
        · rw [Nat.add_mul, Nat.one_mul]
          omega
        · exact hb

/--
The emergent quotient and remainder satisfy the canonical decomposition law.
-/
theorem emergentQuotientRemainder_spec
    (b n : ℕ) (hb : 0 < b) :
    IsCycleDecomposition b n
      (emergentQuotient b n)
      (emergentRemainder b n) := by
  simpa [emergentQuotient, emergentRemainder] using
    cycleCoordinatesRec_isCycleDecomposition b hb n

/-- The defining value equation of the emergent coordinates. -/
theorem emergent_decomposition_value
    (b n : ℕ) (hb : 0 < b) :
    n = emergentQuotient b n * b + emergentRemainder b n :=
  (emergentQuotientRemainder_spec b n hb).1

/-- The emergent residual is always strictly inside the local cycle. -/
theorem emergentRemainder_lt
    (b n : ℕ) (hb : 0 < b) :
    emergentRemainder b n < b :=
  (emergentQuotientRemainder_spec b n hb).2

/--
Any bounded cycle decomposition must coincide with the recursively generated
coordinates.
-/
theorem cycleDecomposition_eq_emergent
    {b n q r : ℕ}
    (hb : 0 < b)
    (h : IsCycleDecomposition b n q r) :
    q = emergentQuotient b n ∧ r = emergentRemainder b n :=
  cycleDecomposition_unique h (emergentQuotientRemainder_spec b n hb)

/--
Away from the boundary, one unit step advances only the emergent residual.
-/
theorem emergent_step_inside_cycle
    {b n : ℕ}
    (hnext : emergentRemainder b n + 1 < b) :
    emergentQuotient b (n + 1) = emergentQuotient b n ∧
      emergentRemainder b (n + 1) = emergentRemainder b n + 1 := by
  have hnext' : (cycleCoordinatesRec b n).2 + 1 < b := by
    simpa [emergentRemainder] using hnext
  change
    (nextCycleCoordinates b (cycleCoordinatesRec b n)).1 =
        (cycleCoordinatesRec b n).1 ∧
      (nextCycleCoordinates b (cycleCoordinatesRec b n)).2 =
        (cycleCoordinatesRec b n).2 + 1
  simp [nextCycleCoordinates, hnext']

/--
At the local boundary, one unit step completes exactly one cycle and resets the
emergent residual to zero.
-/
theorem emergent_step_at_boundary
    {b n : ℕ}
    (hboundary : emergentRemainder b n + 1 = b) :
    emergentQuotient b (n + 1) = emergentQuotient b n + 1 ∧
      emergentRemainder b (n + 1) = 0 := by
  have hnot : ¬ emergentRemainder b n + 1 < b := by omega
  have hnot' : ¬ (cycleCoordinatesRec b n).2 + 1 < b := by
    simpa [emergentRemainder] using hnot
  change
    (nextCycleCoordinates b (cycleCoordinatesRec b n)).1 =
        (cycleCoordinatesRec b n).1 + 1 ∧
      (nextCycleCoordinates b (cycleCoordinatesRec b n)).2 = 0
  simp [nextCycleCoordinates, hnot']

/--
For a positive capacity, every successor step is forced into exactly one of the
two recursive regimes: advance inside the cycle or complete a cycle and reset.
-/
theorem emergent_step_dichotomy
    {b n : ℕ}
    (hb : 0 < b) :
    (emergentRemainder b n + 1 < b ∧
      emergentQuotient b (n + 1) = emergentQuotient b n ∧
      emergentRemainder b (n + 1) = emergentRemainder b n + 1) ∨
    (emergentRemainder b n + 1 = b ∧
      emergentQuotient b (n + 1) = emergentQuotient b n + 1 ∧
      emergentRemainder b (n + 1) = 0) := by
  have hr := emergentRemainder_lt b n hb
  by_cases hnext : emergentRemainder b n + 1 < b
  · exact Or.inl ⟨hnext, emergent_step_inside_cycle hnext⟩
  · have hboundary : emergentRemainder b n + 1 = b := by omega
    exact Or.inr ⟨hboundary, emergent_step_at_boundary hboundary⟩

/--
The dynamically extracted local capacity canonically determines the emergent
quotient/remainder coordinates of every external clock value.
-/
theorem emergentLocalCapacity_quotientRemainder_spec
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    {b : ℕ}
    (hb : EmergentLocalCapacity trajectory model b)
    (n : ℕ) :
    IsCycleDecomposition b n
      (emergentQuotient b n)
      (emergentRemainder b n) :=
  emergentQuotientRemainder_spec b n hb.1.1

/--
For an emergent local capacity, the local readout is controlled by the
recursively generated emergent remainder.
-/
theorem emergentRemainder_controls_localReadout
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    {b : ℕ}
    (hb : EmergentLocalCapacity trajectory model b)
    (n : ℕ) :
    model.observe (trajectory.state n) =
      model.observe (trajectory.state (emergentRemainder b n)) :=
  emergentCycleResidual_controls_localReadout trajectory model hb
    (emergentLocalCapacity_quotientRemainder_spec trajectory model hb n)

end QuantityRepresentationFoundations
