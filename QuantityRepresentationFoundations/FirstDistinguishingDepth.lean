import QuantityRepresentationFoundations.UnboundedPrefixDepth

/-!
# Canonical first distinguishing depth

The previous layer proved that faithful finite-state representations contain
new distinguishing information arbitrarily deep.  This module extracts a
canonical depth from that fact without introducing positional arithmetic.

For two source states in a layered representation, `FirstDifferenceAt encode
q₁ q₂ k` means:

* the two encoded states agree at every level strictly below `k`;
* they differ at level `k`.

Because the levels are indexed by `ℕ`, every pair of distinct faithfully
represented source states has a unique first distinguishing level.

No base, quotient, remainder, division, modulo, positional weight,
normalization, or carry is used.
-/

namespace QuantityRepresentationFoundations

/-- `k` is the first level at which two layered encodings differ. -/
def FirstDifferenceAt
    {Q : Type*} {Layer : ℕ → Type*}
    (encode : Q → ∀ n, Layer n)
    (q₁ q₂ : Q) (k : ℕ) : Prop :=
  AgreeBelow encode k q₁ q₂ ∧ encode q₁ k ≠ encode q₂ k

/--
Distinct source states under a faithful layered encoding differ at some level.
-/
theorem faithfulLayeredEncoding_has_difference
    {Q : Type*} {Layer : ℕ → Type*}
    (encode : Q → ∀ n, Layer n)
    (hfaithful : FaithfulRepresentation encode)
    {q₁ q₂ : Q} (hne : q₁ ≠ q₂) :
    ∃ n, encode q₁ n ≠ encode q₂ n := by
  by_contra hnone
  apply hne
  apply hfaithful
  funext n
  by_contra hdiff
  exact hnone ⟨n, hdiff⟩

/--
Every distinct pair in a faithful layered encoding has a first distinguishing
level.
-/
theorem exists_firstDistinguishingDepth
    {Q : Type*} {Layer : ℕ → Type*}
    (encode : Q → ∀ n, Layer n)
    (hfaithful : FaithfulRepresentation encode)
    {q₁ q₂ : Q} (hne : q₁ ≠ q₂) :
    ∃ k, FirstDifferenceAt encode q₁ q₂ k := by
  classical
  have hdiff : ∃ n, encode q₁ n ≠ encode q₂ n :=
    faithfulLayeredEncoding_has_difference encode hfaithful hne
  refine ⟨Nat.find hdiff, ?_, Nat.find_spec hdiff⟩
  intro n hn
  by_contra hneq
  exact (Nat.find_min hdiff hn) hneq

/--
The first distinguishing level is unique.
-/
theorem firstDifferenceAt_unique
    {Q : Type*} {Layer : ℕ → Type*}
    (encode : Q → ∀ n, Layer n)
    {q₁ q₂ : Q} {k₁ k₂ : ℕ}
    (h₁ : FirstDifferenceAt encode q₁ q₂ k₁)
    (h₂ : FirstDifferenceAt encode q₁ q₂ k₂) :
    k₁ = k₂ := by
  rcases h₁ with ⟨hbelow₁, hdiff₁⟩
  rcases h₂ with ⟨hbelow₂, hdiff₂⟩
  apply le_antisymm
  · by_contra hnot
    have hlt : k₂ < k₁ := Nat.lt_of_not_ge hnot
    exact hdiff₂ (hbelow₁ k₂ hlt)
  · by_contra hnot
    have hlt : k₁ < k₂ := Nat.lt_of_not_ge hnot
    exact hdiff₁ (hbelow₂ k₁ hlt)

/--
Canonical existence-and-uniqueness form of the first distinguishing depth.
-/
theorem existsUnique_firstDistinguishingDepth
    {Q : Type*} {Layer : ℕ → Type*}
    (encode : Q → ∀ n, Layer n)
    (hfaithful : FaithfulRepresentation encode)
    {q₁ q₂ : Q} (hne : q₁ ≠ q₂) :
    ∃! k, FirstDifferenceAt encode q₁ q₂ k := by
  obtain ⟨k, hk⟩ := exists_firstDistinguishingDepth encode hfaithful hne
  refine ⟨k, hk, ?_⟩
  intro k' hk'
  exact firstDifferenceAt_unique encode hk' hk

/--
In a faithful encoding by finite layers, canonical first distinguishing depths
are unbounded: beyond every finite cutoff there is a pair whose first
difference occurs at or after that cutoff.
-/
theorem faithfulFiniteLayerEncoding_has_unbounded_firstDistinguishingDepth
    {Q : Type*} [Infinite Q]
    (Layer : ℕ → Type*) [∀ n, Finite (Layer n)]
    (encode : Q → ∀ n, Layer n)
    (hfaithful : FaithfulRepresentation encode) :
    ∀ depth : ℕ,
      ∃ q₁ q₂ k,
        q₁ ≠ q₂ ∧
        FirstDifferenceAt encode q₁ q₂ k ∧
        depth ≤ k := by
  intro depth
  obtain ⟨q₁, q₂, hne, hagree⟩ :=
    finitePrefix_forces_collision Layer encode depth
  obtain ⟨k, hk⟩ :=
    exists_firstDistinguishingDepth encode hfaithful hne
  refine ⟨q₁, q₂, k, hne, hk, ?_⟩
  by_contra hnot
  have hlt : k < depth := Nat.lt_of_not_ge hnot
  exact hk.2 (hagree k hlt)

end QuantityRepresentationFoundations
