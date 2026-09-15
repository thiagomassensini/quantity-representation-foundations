import QuantityRepresentationFoundations.FirstLocalReturnCapacity

/-!
# Emergent cycle decomposition

The previous layer derives a canonical positive local period `b` from finite,
autonomous, information-preserving local dynamics.  This module asks what an
external step count `n` must look like relative to such a positive capacity.

The construction here deliberately does **not** use `Nat.div` or `Nat.mod`.
Existence is proved by induction on the external clock.  At each successor step,
the residual position either advances while remaining below `b`, or reaches the
boundary `b`, in which case one complete cycle is recorded and the residual
position resets to zero.

Thus the cycle-count/residual decomposition is constructed before it is
identified with any pre-existing quotient-remainder API.
-/

namespace QuantityRepresentationFoundations

/--
`q` and `r` are cycle coordinates for `n` at positive local capacity `b` when
`n` is the sum of `q` complete blocks of size `b` and a residual position `r`
strictly inside the block.

The definition contains no division or modulo operation.
-/
def IsCycleDecomposition (b n q r : ℕ) : Prop :=
  n = q * b + r ∧ r < b

/--
Every external step count has cycle coordinates relative to every positive
capacity.  The proof is constructive by induction and does not invoke division
or remainder.
-/
theorem exists_cycleDecomposition
    (b : ℕ) (hb : 0 < b) :
    ∀ n : ℕ, ∃ q r : ℕ, IsCycleDecomposition b n q r := by
  intro n
  induction n with
  | zero =>
      refine ⟨0, 0, ?_⟩
      exact ⟨by simp, hb⟩
  | succ n ih =>
      obtain ⟨q, r, hvalue, hresidual⟩ := ih
      by_cases hnext : r + 1 < b
      · refine ⟨q, r + 1, ?_⟩
        constructor
        · omega
        · exact hnext
      · have hboundary : r + 1 = b := by
          omega
        refine ⟨q + 1, 0, ?_⟩
        constructor
        · calc
            Nat.succ n = n + 1 := by omega
            _ = (q * b + r) + 1 := by rw [hvalue]
            _ = q * b + (r + 1) := by omega
            _ = q * b + b := by rw [hboundary]
            _ = (q + 1) * b + 0 := by simp [Nat.add_mul]
        · exact hb

/-- A bounded residual lies strictly before the next complete cycle boundary. -/
theorem cycleDecomposition_before_next_boundary
    {b q r : ℕ}
    (hr : r < b) :
    q * b + r < (q + 1) * b := by
  calc
    q * b + r < q * b + b := Nat.add_lt_add_left hr _
    _ = (q + 1) * b := by simp [Nat.add_mul]

/--
Cycle coordinates are unique.  The proof uses only order, addition,
multiplication as repeated addition, and the residual bound; it does not use
quotient or remainder operations.
-/
theorem cycleDecomposition_unique
    {b n q₁ r₁ q₂ r₂ : ℕ}
    (h₁ : IsCycleDecomposition b n q₁ r₁)
    (h₂ : IsCycleDecomposition b n q₂ r₂) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  rcases h₁ with ⟨hvalue₁, hresidual₁⟩
  rcases h₂ with ⟨hvalue₂, hresidual₂⟩
  have heq : q₁ * b + r₁ = q₂ * b + r₂ :=
    hvalue₁.symm.trans hvalue₂
  have hnot₁₂ : ¬ q₁ < q₂ := by
    intro hq
    have hsucc : q₁ + 1 ≤ q₂ := Nat.succ_le_of_lt hq
    have hblock : q₁ * b + r₁ < (q₁ + 1) * b :=
      cycleDecomposition_before_next_boundary hresidual₁
    have hmul : (q₁ + 1) * b ≤ q₂ * b :=
      Nat.mul_le_mul_right b hsucc
    have htail : q₂ * b ≤ q₂ * b + r₂ :=
      Nat.le_add_right _ _
    have hlt : q₁ * b + r₁ < q₂ * b + r₂ :=
      hblock.trans_le (hmul.trans htail)
    exact (Nat.ne_of_lt hlt) heq
  have hnot₂₁ : ¬ q₂ < q₁ := by
    intro hq
    have hsucc : q₂ + 1 ≤ q₁ := Nat.succ_le_of_lt hq
    have hblock : q₂ * b + r₂ < (q₂ + 1) * b :=
      cycleDecomposition_before_next_boundary hresidual₂
    have hmul : (q₂ + 1) * b ≤ q₁ * b :=
      Nat.mul_le_mul_right b hsucc
    have htail : q₁ * b ≤ q₁ * b + r₁ :=
      Nat.le_add_right _ _
    have hlt : q₂ * b + r₂ < q₁ * b + r₁ :=
      hblock.trans_le (hmul.trans htail)
    exact (Nat.ne_of_lt hlt) heq.symm
  have hq₁₂ : q₁ ≤ q₂ := Nat.le_of_not_gt hnot₂₁
  have hq₂₁ : q₂ ≤ q₁ := Nat.le_of_not_gt hnot₁₂
  have hq : q₁ = q₂ := Nat.le_antisymm hq₁₂ hq₂₁
  have hr : r₁ = r₂ := by
    rw [hq] at heq
    omega
  exact ⟨hq, hr⟩

/--
For every positive capacity and every external clock value there is a unique
pair `(q,r)` of cycle count and residual position.
-/
theorem existsUnique_cycleCoordinates
    (b n : ℕ) (hb : 0 < b) :
    ∃! coordinates : ℕ × ℕ,
      IsCycleDecomposition b n coordinates.1 coordinates.2 := by
  obtain ⟨q, r, hqr⟩ := exists_cycleDecomposition b hb n
  refine ⟨(q, r), hqr, ?_⟩
  intro coordinates hcoordinates
  rcases coordinates with ⟨q', r'⟩
  obtain ⟨hq, hr⟩ := cycleDecomposition_unique hcoordinates hqr
  simp only [Prod.fst, Prod.snd] at hq hr ⊢
  rw [hq, hr]

/--
An emergent local capacity supplies the positivity needed for the unique cycle
coordinate theorem.  No radix arithmetic is added here: the capacity was
already extracted dynamically in the previous layer.
-/
theorem emergentLocalCapacity_has_unique_cycleCoordinates
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    {b : ℕ}
    (hb : EmergentLocalCapacity trajectory model b)
    (n : ℕ) :
    ∃! coordinates : ℕ × ℕ,
      IsCycleDecomposition b n coordinates.1 coordinates.2 :=
  existsUnique_cycleCoordinates b n hb.1.1

/--
If `b` is a period of a readout and `n = q*b + r`, then the readout at `n`
is exactly the readout at the residual position `r`.

This makes `r` operationally meaningful: it is the position inside the local
cycle, not merely an algebraic leftover.
-/
theorem periodicReadout_depends_only_on_residual
    {α : Type*}
    (readout : ℕ → α)
    {b n q r : ℕ}
    (hperiod : ∀ k : ℕ, readout (k + b) = readout k)
    (hdecomp : IsCycleDecomposition b n q r) :
    readout n = readout r := by
  rcases hdecomp with ⟨hvalue, _⟩
  rw [hvalue]
  induction q with
  | zero => simp
  | succ q ih =>
      have hindex : (Nat.succ q) * b + r = (q * b + r) + b := by
        rw [Nat.succ_mul]
        omega
      rw [hindex, hperiod]
      exact ih

/--
For the dynamically emergent capacity, the local observation at any external
step count depends only on its uniquely bounded residual coordinate.
-/
theorem emergentCycleResidual_controls_localReadout
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    {b n q r : ℕ}
    (hb : EmergentLocalCapacity trajectory model b)
    (hdecomp : IsCycleDecomposition b n q r) :
    model.observe (trajectory.state n) =
      model.observe (trajectory.state r) := by
  apply periodicReadout_depends_only_on_residual
    (fun k => model.observe (trajectory.state k))
    (emergentLocalCapacity_periodic_readout trajectory model hb)
    hdecomp

end QuantityRepresentationFoundations
