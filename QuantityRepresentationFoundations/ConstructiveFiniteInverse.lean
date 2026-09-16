import QuantityRepresentationFoundations.PrimitiveAxiomFreeCarryRigidity

/-!
# Constructive finite inverse search

This module isolates the remaining inverse-construction question from the carry
geometry. Given an encoder out of `Fin N`, decidable equality in the target,
and a propositional proof of surjectivity, we search the finite source directly.

A kernel-facing detail matters here: the generic numeral `0 : Fin N` is built
through `Fin.ofNat`, hence through natural remainder. Since that library path
carries logical dependencies in the current Lean environment, every finite zero
below is constructed directly as a `Fin.mk` value instead.

Likewise, the completeness proof avoids `Fin.cases`: its current library trace
contains `propext`.  Instead we inspect the underlying natural value and rebuild
the tail state explicitly.

The decoder itself does not eliminate the existential surjectivity proof into
`Type`: it is a closed recursive search with an explicit default. Surjectivity
is used only to prove that the search cannot miss.
-/

namespace QuantityRepresentationFoundations
namespace ConstructiveFiniteInverse

universe u

/-- Explicit zero in the successor-sized finite window. -/
def finZero (N : ℕ) : Fin (N + 1) :=
  ⟨0, Nat.zero_lt_succ N⟩

/--
Search `Fin N` structurally. At size `N+1`, test the explicitly constructed
zero and then recurse through `Fin.succ : Fin N → Fin (N+1)`.
-/
def findPreimage {Code : Type u} [DecidableEq Code] :
    {N : ℕ} → (Fin N → Code) → Code → Option (Fin N)
  | 0, _encode, _c => none
  | N + 1, encode, c =>
      let z : Fin (N + 1) := finZero N
      if h0 : encode z = c then
        some z
      else
        match findPreimage (fun i : Fin N => encode i.succ) c with
        | none => none
        | some i => some i.succ

/-- Anything returned by the structural search is a genuine preimage. -/
theorem findPreimage_sound {Code : Type u} [DecidableEq Code] :
    ∀ {N : ℕ} (encode : Fin N → Code) (c : Code) (n : Fin N),
      findPreimage encode c = some n → encode n = c := by
  intro N
  induction N with
  | zero =>
      intro encode c n _h
      exact Fin.elim0 n
  | succ N ih =>
      intro encode c n h
      let z : Fin (N + 1) := finZero N
      by_cases h0 : encode z = c
      · unfold findPreimage at h
        rw [dif_pos h0] at h
        cases h
        exact h0
      · unfold findPreimage at h
        rw [dif_neg h0] at h
        cases hrec : findPreimage (fun i : Fin N => encode i.succ) c with
        | none =>
            rw [hrec] at h
            cases h
        | some i =>
            rw [hrec] at h
            cases h
            exact ih (fun j : Fin N => encode j.succ) c i hrec

/-- If a preimage exists, the structural search returns one. -/
theorem findPreimage_complete {Code : Type u} [DecidableEq Code] :
    ∀ {N : ℕ} (encode : Fin N → Code) (c : Code),
      (∃ n : Fin N, encode n = c) →
      ∃ n : Fin N, findPreimage encode c = some n := by
  intro N
  induction N with
  | zero =>
      intro encode c hex
      obtain ⟨n, _hn⟩ := hex
      exact Fin.elim0 n
  | succ N ih =>
      intro encode c hex
      let z : Fin (N + 1) := finZero N
      by_cases h0 : encode z = c
      · refine ⟨z, ?_⟩
        unfold findPreimage
        rw [dif_pos h0]
      · have htail : ∃ i : Fin N, encode i.succ = c := by
          obtain ⟨n, hn⟩ := hex
          cases hval : n.val with
          | zero =>
              have hnz : n = z := by
                apply Fin.ext
                change n.val = 0
                exact hval
              rw [hnz] at hn
              exact False.elim (h0 hn)
          | succ a =>
              have hs : a + 1 < N + 1 := by
                have hlt := n.isLt
                rw [hval] at hlt
                exact hlt
              have ha : a < N := Nat.lt_of_succ_lt_succ hs
              let i : Fin N := ⟨a, ha⟩
              have hni : n = i.succ := by
                apply Fin.ext
                change n.val = a + 1
                exact hval
              rw [hni] at hn
              exact ⟨i, hn⟩
        obtain ⟨i, hi⟩ := htail
        obtain ⟨j, hj⟩ := ih (fun q : Fin N => encode q.succ) c ⟨i, hi⟩
        refine ⟨j.succ, ?_⟩
        unfold findPreimage
        rw [dif_neg h0, hj]

/--
Decoder obtained by finite search. The fallback is computationally explicit;
surjectivity will prove below that it is never used.
-/
def decode
    {Code : Type u} [DecidableEq Code]
    {N : ℕ} (hN : 0 < N)
    (encode : Fin N → Code) (c : Code) : Fin N :=
  match findPreimage encode c with
  | some n => n
  | none => ⟨0, hN⟩

/-- Surjectivity proves that finite search decodes every target exactly. -/
theorem encode_decode
    {Code : Type u} [DecidableEq Code]
    {N : ℕ} (hN : 0 < N)
    (encode : Fin N → Code)
    (hsurj : Function.Surjective encode)
    (c : Code) :
    encode (decode hN encode c) = c := by
  obtain ⟨w, hw⟩ := hsurj c
  obtain ⟨n, hn⟩ := findPreimage_complete encode c ⟨w, hw⟩
  unfold decode
  rw [hn]
  exact findPreimage_sound encode c n hn

/-- Injectivity plus the exact decode law gives the left inverse law. -/
theorem decode_encode
    {Code : Type u} [DecidableEq Code]
    {N : ℕ} (hN : 0 < N)
    (encode : Fin N → Code)
    (hinj : Function.Injective encode)
    (hsurj : Function.Surjective encode)
    (n : Fin N) :
    decode hN encode (encode n) = n := by
  apply hinj
  exact encode_decode hN encode hsurj (encode n)

/-- A bijective finite encoder with decidable target equality yields an explicit codec. -/
def primitiveCodeWindowOfBijective
    {b k : ℕ} (hb : 0 < b)
    {Code : Type u} [DecidableEq Code]
    (encode : PrimitiveCarry.WindowState b k → Code)
    (hinj : Function.Injective encode)
    (hsurj : Function.Surjective encode) :
    PrimitiveCarry.CodeWindow b k Code where
  encode := encode
  decode := decode (PrimitiveCarry.natPow_pos hb k) encode
  decode_encode := decode_encode (PrimitiveCarry.natPow_pos hb k) encode hinj hsurj
  encode_decode := encode_decode (PrimitiveCarry.natPow_pos hb k) encode hsurj

end ConstructiveFiniteInverse
end QuantityRepresentationFoundations
