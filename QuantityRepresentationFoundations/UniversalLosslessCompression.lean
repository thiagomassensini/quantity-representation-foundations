import QuantityRepresentationFoundations.CarryGeometryNormalizationBridge

/-!
# Universal lossless compression and carry conjugacy

This module isolates a representation-independent finite-window theorem.

Fix a genuine capacity `b > 1` and a depth `k`. There are exactly `b^k`
distinguishable quantity states in the canonical depth-`k` window. We do not
assume that an arbitrary compressed code for this window is positional, ordered,
or digit-like. Its code type may be completely opaque.

The only hypotheses are:

* losslessness: the encoding of the `b^k` quantity states is injective;
* compression budget: the code uses at most `b^k` states.

Finite cardinality then forces equality of state counts and hence bijectivity.
Therefore every optimal lossless code is merely a change of coordinates of the
canonical residual window. Transporting unit successor through this forced
equivalence gives the code's successor dynamics. The wrap event in *every*
such code is equivalent to the canonical depth-`k` carry event of
`carry-geometry`.

This theorem deliberately allows arbitrary recodings (permutations, Gray-like
coordinates, etc.). They are not counterexamples: they are conjugate coordinate
systems on the same finite quantity dynamics.
-/

namespace QuantityRepresentationFoundations

/--
An arbitrary lossless compressed representation of a depth-`k`, base-`b`
quantity window.

`Code` carries no positional structure. The budget says only that the code uses
no more states than the `b^k` quantities that must remain distinguishable.
-/
structure LosslessCompressedWindow
    (b k : ℕ) (Code : Type*) [Fintype Code] where
  encode : Fin (b ^ k) → Code
  faithful : Function.Injective encode
  state_budget : Fintype.card Code ≤ b ^ k

namespace LosslessCompressedWindow

variable {b k : ℕ} {Code Code₁ Code₂ : Type*}
variable [Fintype Code] [Fintype Code₁] [Fintype Code₂]

/--
A lossless code for `b^k` distinguishable states cannot use fewer than `b^k`
states. Together with the compression budget this forces exact cardinality.
-/
theorem card_eq_windowSize
    (rep : LosslessCompressedWindow b k Code) :
    Fintype.card Code = b ^ k := by
  have hlower : b ^ k ≤ Fintype.card Code := by
    simpa using Fintype.card_le_of_injective rep.encode rep.faithful
  exact Nat.le_antisymm rep.state_budget hlower

/-- The lossless optimal encoder is forced to be bijective. -/
theorem encode_bijective
    (rep : LosslessCompressedWindow b k Code) :
    Function.Bijective rep.encode := by
  apply (Fintype.bijective_iff_injective_and_card rep.encode).2
  refine ⟨rep.faithful, ?_⟩
  simpa [rep.card_eq_windowSize]

/--
The forced equivalence between the canonical quantity window and an arbitrary
optimal lossless code.
-/
noncomputable def windowEquiv
    (rep : LosslessCompressedWindow b k Code) :
    Fin (b ^ k) ≃ Code :=
  Equiv.ofBijective rep.encode rep.encode_bijective

@[simp] theorem windowEquiv_apply
    (rep : LosslessCompressedWindow b k Code)
    (n : Fin (b ^ k)) :
    rep.windowEquiv n = rep.encode n := rfl

@[simp] theorem windowEquiv_symm_encode
    (rep : LosslessCompressedWindow b k Code)
    (n : Fin (b ^ k)) :
    rep.windowEquiv.symm (rep.encode n) = n := by
  change rep.windowEquiv.symm (rep.windowEquiv n) = n
  exact rep.windowEquiv.symm_apply_apply n

/-- The explicit zero state of a nonempty canonical finite window. -/
def windowZero (b k : ℕ) (hb : 0 < b) : Fin (b ^ k) :=
  ⟨0, pow_pos hb k⟩

@[simp] theorem windowZero_val (b k : ℕ) (hb : 0 < b) :
    (windowZero b k hb).val = 0 := rfl

/--
Canonical cyclic unit successor on the finite depth-`k` quantity window.
The wrap at the top of the window is the finite shadow of carry through all
`k` lower places.
-/
def windowSuccessor
    (b k : ℕ) (hb : 0 < b) (n : Fin (b ^ k)) :
    Fin (b ^ k) :=
  ⟨(n.val + 1) % (b ^ k), Nat.mod_lt _ (pow_pos hb k)⟩

/--
The canonical window wraps to zero exactly when increment carries through the
lowest `k` positional places.
-/
theorem windowSuccessor_eq_zero_iff_carry
    (b k : ℕ) (hb : 0 < b) (n : Fin (b ^ k)) :
    windowSuccessor b k hb n = windowZero b k hb ↔
      CarryGeometry.carryAfterIncrementAtDepth b k n.val := by
  constructor
  · intro h
    have hmod : (n.val + 1) % (b ^ k) = 0 := by
      exact congrArg Fin.val h
    simpa [CarryGeometry.carryAfterIncrementAtDepth,
      CarryGeometry.placeValue, Nat.ModEq] using hmod
  · intro hcarry
    have hmod : (n.val + 1) % (b ^ k) = 0 := by
      simpa [CarryGeometry.carryAfterIncrementAtDepth,
        CarryGeometry.placeValue, Nat.ModEq] using hcarry
    apply Fin.ext
    exact hmod

/--
Successor dynamics transported into an arbitrary optimal lossless code.
No local syntax of the code is assumed.
-/
noncomputable def codeSuccessor
    (rep : LosslessCompressedWindow b k Code)
    (hb : 0 < b) : Code → Code :=
  fun c =>
    rep.windowEquiv
      (windowSuccessor b k hb (rep.windowEquiv.symm c))

/-- Encoding intertwines canonical unit successor with code successor. -/
@[simp] theorem codeSuccessor_encode
    (rep : LosslessCompressedWindow b k Code)
    (hb : 0 < b) (n : Fin (b ^ k)) :
    rep.codeSuccessor hb (rep.encode n) =
      rep.encode (windowSuccessor b k hb n) := by
  unfold codeSuccessor
  rw [rep.windowEquiv_symm_encode n]
  rfl

/--
Any exact code-level realization of unit successor is forced to equal the
transported successor.  There is no second exact successor dynamics hidden by
an arbitrary lossless recoding.
-/
theorem codeSuccessor_unique
    (rep : LosslessCompressedWindow b k Code)
    (hb : 0 < b)
    (step : Code → Code)
    (hstep : ∀ n : Fin (b ^ k),
      step (rep.encode n) = rep.encode (windowSuccessor b k hb n)) :
    step = rep.codeSuccessor hb := by
  funext c
  obtain ⟨n, rfl⟩ := rep.encode_bijective.2 c
  rw [hstep n, rep.codeSuccessor_encode hb n]

/--
Every optimal lossless code has a distinguished wrap event, namely the image of
the canonical zero state. That code-level event is equivalent to the canonical
arithmetic carry event, regardless of the code's coordinates.
-/
theorem code_wrap_iff_carry
    (rep : LosslessCompressedWindow b k Code)
    (hb : 0 < b) (n : Fin (b ^ k)) :
    rep.codeSuccessor hb (rep.encode n) =
        rep.encode (windowZero b k hb) ↔
      CarryGeometry.carryAfterIncrementAtDepth b k n.val := by
  rw [rep.codeSuccessor_encode hb n]
  constructor
  · intro h
    have hwindow :
        windowSuccessor b k hb n = windowZero b k hb := rep.faithful h
    exact (windowSuccessor_eq_zero_iff_carry b k hb n).1 hwindow
  · intro hcarry
    apply congrArg rep.encode
    exact (windowSuccessor_eq_zero_iff_carry b k hb n).2 hcarry

/--
Any exact unit-successor implementation on an optimal lossless code wraps
exactly on the canonical carry event.
-/
theorem exact_successor_wrap_iff_carry
    (rep : LosslessCompressedWindow b k Code)
    (hb : 0 < b)
    (step : Code → Code)
    (hstep : ∀ n : Fin (b ^ k),
      step (rep.encode n) = rep.encode (windowSuccessor b k hb n))
    (n : Fin (b ^ k)) :
    step (rep.encode n) = rep.encode (windowZero b k hb) ↔
      CarryGeometry.carryAfterIncrementAtDepth b k n.val := by
  rw [rep.codeSuccessor_unique hb step hstep]
  exact rep.code_wrap_iff_carry hb n

/--
Canonical change of representation between any two optimal lossless codes for
the same finite quantity window.
-/
noncomputable def changeOfRepresentation
    (left : LosslessCompressedWindow b k Code₁)
    (right : LosslessCompressedWindow b k Code₂) :
    Code₁ ≃ Code₂ :=
  left.windowEquiv.symm.trans right.windowEquiv

@[simp] theorem changeOfRepresentation_encode
    (left : LosslessCompressedWindow b k Code₁)
    (right : LosslessCompressedWindow b k Code₂)
    (n : Fin (b ^ k)) :
    left.changeOfRepresentation right (left.encode n) = right.encode n := by
  change right.windowEquiv (left.windowEquiv.symm (left.encode n)) = right.encode n
  rw [left.windowEquiv_symm_encode n]
  rfl

/--
Unit-successor dynamics is invariant under arbitrary optimal lossless changes
of representation: the two code dynamics are conjugate.
-/
theorem changeOfRepresentation_conjugates_successor
    (left : LosslessCompressedWindow b k Code₁)
    (right : LosslessCompressedWindow b k Code₂)
    (hb : 0 < b) (c : Code₁) :
    left.changeOfRepresentation right (left.codeSuccessor hb c) =
      right.codeSuccessor hb (left.changeOfRepresentation right c) := by
  unfold changeOfRepresentation codeSuccessor
  simp

/--
Finite-window universal compression theorem.

Every lossless representation of the `b^k` quantity states using at most
`b^k` code states is forced to be an exact re-coordination of the canonical
window; its unit-successor wrap event is therefore exactly carry through depth
`k` after transporting coordinates.
-/
theorem universal_lossless_compression_forces_carry_conjugacy
    (rep : LosslessCompressedWindow b k Code)
    (hb : 0 < b) :
    Fintype.card Code = b ^ k ∧
      Function.Bijective rep.encode ∧
      ∀ n : Fin (b ^ k),
        rep.codeSuccessor hb (rep.encode n) =
            rep.encode (windowZero b k hb) ↔
          CarryGeometry.carryAfterIncrementAtDepth b k n.val := by
  exact ⟨rep.card_eq_windowSize, rep.encode_bijective,
    fun n => rep.code_wrap_iff_carry hb n⟩

end LosslessCompressedWindow

end QuantityRepresentationFoundations
