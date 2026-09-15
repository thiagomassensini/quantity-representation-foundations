import QuantityRepresentationFoundations.EmergentWeightedPositionalTransport

/-!
# Iterated emergent positional expansion

The previous layer proved a one-level transport law

`a * b^j = R_b(a) * b^j + Q_b(a) * b^(j+1)`

for the recursively constructed emergent quotient/remainder coordinates.

This module iterates that transport.  At depth `k` we distinguish:

* the still-unresolved transported quantity after `k` quotient steps;
* the residual digit extracted at that depth.

For every finite depth, the original quantity is exactly the weighted sum of
all extracted residual digits below that depth plus one transported tail.
For genuine capacities `1 < b`, repeated transport eventually kills the tail,
so a finite positional expansion exists without taking `Nat.digits` as a
primitive construction.
-/

namespace QuantityRepresentationFoundations

/-- Quantity still transported after `k` successive emergent quotient steps. -/
def iteratedEmergentQuotient (b n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => emergentQuotient b (iteratedEmergentQuotient b n k)

/-- Residual digit extracted from the transported quantity at depth `k`. -/
def emergentPositionalDigit (b n k : ℕ) : ℕ :=
  emergentRemainder b (iteratedEmergentQuotient b n k)

@[simp] theorem iteratedEmergentQuotient_zero (b n : ℕ) :
    iteratedEmergentQuotient b n 0 = n := by
  rfl

@[simp] theorem iteratedEmergentQuotient_succ (b n k : ℕ) :
    iteratedEmergentQuotient b n (k + 1) =
      emergentQuotient b (iteratedEmergentQuotient b n k) := by
  rfl

/-- Iteration after one initial quotient is the same as shifting the depth. -/
theorem iteratedEmergentQuotient_succ_start
    (b n k : ℕ) :
    iteratedEmergentQuotient b n (k + 1) =
      iteratedEmergentQuotient b (emergentQuotient b n) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa only [iteratedEmergentQuotient_succ] using
        congrArg (emergentQuotient b) ih

/-- Every extracted emergent positional digit lies inside the local capacity. -/
theorem emergentPositionalDigit_lt
    (b n k : ℕ) (hb : 0 < b) :
    emergentPositionalDigit b n k < b := by
  exact emergentRemainder_lt b (iteratedEmergentQuotient b n k) hb

/--
At every depth, the still-transported quantity splits into its local residual
plus one further transported quantity.
-/
theorem iteratedEmergentQuotient_split
    (b n k : ℕ) (hb : 0 < b) :
    iteratedEmergentQuotient b n k =
      emergentPositionalDigit b n k +
        b * iteratedEmergentQuotient b n (k + 1) := by
  have h := emergent_decomposition_value b
    (iteratedEmergentQuotient b n k) hb
  calc
    iteratedEmergentQuotient b n k =
        emergentQuotient b (iteratedEmergentQuotient b n k) * b +
          emergentRemainder b (iteratedEmergentQuotient b n k) := h
    _ = emergentPositionalDigit b n k +
        b * iteratedEmergentQuotient b n (k + 1) := by
      simp [emergentPositionalDigit, iteratedEmergentQuotient]
      ac_rfl

/--
The one-step weighted transport law at the `k`-th iterated level.
-/
theorem iteratedEmergent_weighted_step
    (b n k : ℕ) (hb : 0 < b) :
    iteratedEmergentQuotient b n k * CarryGeometry.placeValue b k =
      emergentPositionalDigit b n k * CarryGeometry.placeValue b k +
        iteratedEmergentQuotient b n (k + 1) *
          CarryGeometry.placeValue b (k + 1) := by
  simpa [emergentPositionalDigit, iteratedEmergentQuotient] using
    emergent_weighted_positional_transport b
      (iteratedEmergentQuotient b n k) k hb

/--
Finite-depth positional expansion with an explicit transported tail.

Nothing is discarded: the digits extracted below depth `k` plus the unresolved
tail at level `k` reconstruct the original quantity exactly.
-/
theorem emergent_positional_expansion_with_tail
    (b n k : ℕ) (hb : 0 < b) :
    n =
      (∑ i ∈ Finset.range k,
        emergentPositionalDigit b n i * CarryGeometry.placeValue b i) +
      iteratedEmergentQuotient b n k * CarryGeometry.placeValue b k := by
  induction k with
  | zero =>
      simp [CarryGeometry.placeValue]
  | succ k ih =>
      calc
        n =
            (∑ i ∈ Finset.range k,
              emergentPositionalDigit b n i * CarryGeometry.placeValue b i) +
            iteratedEmergentQuotient b n k * CarryGeometry.placeValue b k := ih
        _ =
            (∑ i ∈ Finset.range k,
              emergentPositionalDigit b n i * CarryGeometry.placeValue b i) +
            (emergentPositionalDigit b n k * CarryGeometry.placeValue b k +
              iteratedEmergentQuotient b n (k + 1) *
                CarryGeometry.placeValue b (k + 1)) := by
          rw [iteratedEmergent_weighted_step b n k hb]
        _ =
            (∑ i ∈ Finset.range (k + 1),
              emergentPositionalDigit b n i * CarryGeometry.placeValue b i) +
            iteratedEmergentQuotient b n (k + 1) *
              CarryGeometry.placeValue b (k + 1) := by
          rw [Finset.sum_range_succ]
          ac_rfl

/--
For a genuine capacity `1 < b`, a positive transported quantity strictly
decreases after one emergent quotient step.
-/
theorem emergentQuotient_lt_self
    (b n : ℕ) (hb : 1 < b) (hn : 0 < n) :
    emergentQuotient b n < n := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  rw [emergentQuotient_eq_div b n hb0]
  exact Nat.div_lt_self hn hb

/--
For every genuine capacity, iterated emergent transport eventually reaches a
zero tail.
-/
theorem exists_iteratedEmergentQuotient_eq_zero
    (b n : ℕ) (hb : 1 < b) :
    ∃ k : ℕ, iteratedEmergentQuotient b n k = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        exact ⟨0, rfl⟩
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hq_lt : emergentQuotient b n < n :=
          emergentQuotient_lt_self b n hb hnpos
        obtain ⟨k, hk⟩ := ih (emergentQuotient b n) hq_lt
        refine ⟨k + 1, ?_⟩
        rw [iteratedEmergentQuotient_succ_start]
        exact hk

/--
Finite positional representation emerges: for `1 < b`, there is some depth at
which no transported tail remains, and the original quantity is exactly the
weighted sum of the extracted bounded digits.
-/
theorem exists_finite_emergent_positional_expansion
    (b n : ℕ) (hb : 1 < b) :
    ∃ k : ℕ,
      iteratedEmergentQuotient b n k = 0 ∧
      n = ∑ i ∈ Finset.range k,
        emergentPositionalDigit b n i * CarryGeometry.placeValue b i := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  obtain ⟨k, hk⟩ := exists_iteratedEmergentQuotient_eq_zero b n hb
  refine ⟨k, hk, ?_⟩
  have hfull := emergent_positional_expansion_with_tail b n k hb0
  simpa [hk] using hfull

/--
The finite expansion is composed entirely of admissible local digits.
-/
theorem finite_emergent_positional_expansion_digits_bounded
    (b n k : ℕ) (hb : 0 < b) :
    ∀ i < k, emergentPositionalDigit b n i < b := by
  intro i hi
  exact emergentPositionalDigit_lt b n i hb

/--
For a dynamically emergent local capacity `b > 1`, the same finite positional
expansion theorem applies to every external quantity.
-/
theorem emergentLocalCapacity_has_finite_positional_expansion
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    {b : ℕ}
    (_hb : EmergentLocalCapacity trajectory model b)
    (hb1 : 1 < b)
    (n : ℕ) :
    ∃ k : ℕ,
      iteratedEmergentQuotient b n k = 0 ∧
      n = ∑ i ∈ Finset.range k,
        emergentPositionalDigit b n i * CarryGeometry.placeValue b i :=
  exists_finite_emergent_positional_expansion b n hb1

end QuantityRepresentationFoundations
