import QuantityRepresentationFoundations.CanonicalEmergentDigits

/-!
# Intrinsic uniqueness of the emergent positional representation

This module removes canonical normalization from the uniqueness argument for
finite positional digit lists.

For a genuine capacity `1 < b`, a finite coefficient list is called canonical
here when:

* it reconstructs the target quantity exactly;
* every digit lies below `b`;
* if nonempty, its most significant digit is nonzero.

The main theorem proves directly that every such list is exactly
`emergentDigits b hb n`.  The proof only uses the recursively constructed
emergent quotient/remainder coordinates and uniqueness of their bounded cycle
decomposition.  Neither `CarryGeometry.normalizeCoefficients` nor `Nat.digits`
is used in the intrinsic uniqueness theorem.
-/

namespace QuantityRepresentationFoundations

/--
A canonical admissible positional list representing zero must be empty.

This is proved directly from the recursive evaluator, not by normalizing the
list or comparing it with `Nat.digits`.
-/
theorem canonicalExpansion_eq_nil_of_value_zero
    (b : ℕ) (hb : 1 < b) (coefficients : List ℕ)
    (hvalue : CarryGeometry.rawExpansionValue b coefficients = 0)
    (hdigits : ∀ digit ∈ coefficients,
      CarryGeometry.IsAdmissibleDigit b digit)
    (hleading : ∀ h : coefficients ≠ [], coefficients.getLast h ≠ 0) :
    coefficients = [] := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  revert hvalue hdigits hleading
  induction coefficients with
  | nil =>
      intro _ _ _
      rfl
  | cons d tail ih =>
      intro hvalue hdigits hleading
      have hsplit :
          d + b * CarryGeometry.rawExpansionValue b tail = 0 := by
        simpa [CarryGeometry.rawExpansionValue, Nat.ofDigits] using hvalue
      have hadd := Nat.add_eq_zero.mp hsplit
      have hd0 : d = 0 := hadd.1
      have hmul0 : b * CarryGeometry.rawExpansionValue b tail = 0 := hadd.2
      have htail0 : CarryGeometry.rawExpansionValue b tail = 0 := by
        rcases Nat.mul_eq_zero.mp hmul0 with hbzero | htailzero
        · exact (ne_of_gt hb0 hbzero).elim
        · exact htailzero
      have htaildigits : ∀ digit ∈ tail,
          CarryGeometry.IsAdmissibleDigit b digit := by
        intro digit hdigit
        exact hdigits digit (List.mem_cons_of_mem d hdigit)
      have htailleading : ∀ h : tail ≠ [], tail.getLast h ≠ 0 := by
        intro h
        have hcons : d :: tail ≠ [] := by simp
        have hlead := hleading hcons
        simpa [List.getLast_cons h] using hlead
      have htailnil := ih htail0 htaildigits htailleading
      subst tail
      subst d
      have hcontr := hleading (by simp)
      simp at hcontr

/--
Intrinsic uniqueness of the canonical finite positional representation.

Any finite list that has the correct value, uses only digits below the
capacity, and has no leading zero is forced to be the independently constructed
`emergentDigits` list.
-/
theorem intrinsicCanonicalExpansion_eq_emergentDigits
    (b n : ℕ) (hb : 1 < b) (coefficients : List ℕ)
    (hvalue : CarryGeometry.rawExpansionValue b coefficients = n)
    (hdigits : ∀ digit ∈ coefficients,
      CarryGeometry.IsAdmissibleDigit b digit)
    (hleading : ∀ h : coefficients ≠ [], coefficients.getLast h ≠ 0) :
    coefficients = emergentDigits b hb n := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  induction n using Nat.strong_induction_on generalizing coefficients with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        have hnil := canonicalExpansion_eq_nil_of_value_zero
          b hb coefficients hvalue hdigits hleading
        simpa [hnil]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        cases coefficients with
        | nil =>
            simp [CarryGeometry.rawExpansionValue] at hvalue
            exact (hn hvalue.symm).elim
        | cons d tail =>
            have hd : d < b := hdigits d (by simp)
            have htaildigits : ∀ digit ∈ tail,
                CarryGeometry.IsAdmissibleDigit b digit := by
              intro digit hdigit
              exact hdigits digit (List.mem_cons_of_mem d hdigit)
            have htailleading : ∀ htail : tail ≠ [], tail.getLast htail ≠ 0 := by
              intro htail
              have hcons : d :: tail ≠ [] := by simp
              have hlead := hleading hcons
              simpa [List.getLast_cons htail] using hlead
            have hsplit :
                n = CarryGeometry.rawExpansionValue b tail * b + d := by
              calc
                n = CarryGeometry.rawExpansionValue b (d :: tail) := hvalue.symm
                _ = d + b * CarryGeometry.rawExpansionValue b tail := by
                  rfl
                _ = CarryGeometry.rawExpansionValue b tail * b + d := by
                  ac_rfl
            have hdecomp : IsCycleDecomposition b n
                (CarryGeometry.rawExpansionValue b tail) d :=
              ⟨hsplit, hd⟩
            have hcoords := cycleDecomposition_eq_emergent hb0 hdecomp
            have htailvalue :
                CarryGeometry.rawExpansionValue b tail = emergentQuotient b n :=
              hcoords.1
            have hdigit : d = emergentRemainder b n := hcoords.2
            have hq_lt : emergentQuotient b n < n :=
              emergentQuotient_lt_self b n hb hnpos
            have htailcanonical :
                tail = emergentDigits b hb (emergentQuotient b n) :=
              ih (emergentQuotient b n) hq_lt tail
                htailvalue htaildigits htailleading
            calc
              d :: tail =
                  emergentRemainder b n ::
                    emergentDigits b hb (emergentQuotient b n) := by
                rw [hdigit, htailcanonical]
              _ = emergentDigits b hb n :=
                (emergentDigits_of_pos b n hb hnpos).symm

/--
The intrinsic conditions characterize the emergent list uniquely.
-/
theorem existsUnique_intrinsicCanonicalExpansion
    (b n : ℕ) (hb : 1 < b) :
    ∃! coefficients : List ℕ,
      CarryGeometry.rawExpansionValue b coefficients = n ∧
      (∀ digit ∈ coefficients,
        CarryGeometry.IsAdmissibleDigit b digit) ∧
      (∀ h : coefficients ≠ [], coefficients.getLast h ≠ 0) := by
  refine ⟨emergentDigits b hb n, ?_, ?_⟩
  · exact ⟨rawExpansionValue_emergentDigits b n hb,
      emergentDigits_digits_admissible b n hb,
      emergentDigits_no_leading_zero b n hb⟩
  · intro coefficients hcoefficients
    exact intrinsicCanonicalExpansion_eq_emergentDigits
      b n hb coefficients
      hcoefficients.1 hcoefficients.2.1 hcoefficients.2.2

/--
Downstream classical crosswalk obtained from intrinsic uniqueness.

`Nat.digits` enters only here, as a known finite list satisfying the intrinsic
canonical conditions; uniqueness then forces it to equal `emergentDigits`.
-/
theorem natDigits_eq_emergentDigits_by_intrinsic_uniqueness
    (b n : ℕ) (hb : 1 < b) :
    Nat.digits b n = emergentDigits b hb n := by
  apply intrinsicCanonicalExpansion_eq_emergentDigits b n hb (Nat.digits b n)
  · exact Nat.ofDigits_digits b n
  · intro digit hdigit
    exact Nat.digits_lt_base hb hdigit
  · intro h
    exact Nat.getLast_digit_ne_zero b
      ((Nat.digits_ne_nil_iff_ne_zero).mp h)

end QuantityRepresentationFoundations
