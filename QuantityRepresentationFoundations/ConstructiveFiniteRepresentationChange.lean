import QuantityRepresentationFoundations.ConstructiveFiniteCapacityConservation
import QuantityRepresentationFoundations.ConstructiveFiniteInverse

/-!
# Constructive finite change of representation

This module turns finite-capacity conservation into an explicit change-of-
representation theorem.

A representation of quantitative states `Fin N` consists only of:

* a faithful encoder `Fin N → Code`;
* a faithful slot map `Code → Fin N`.

Finite-capacity conservation forces the encoder to be onto.  Equality on the
code type is decidable by comparing slots, so structural finite search recovers
an explicit inverse of the encoder without chosen inverses.

For two such representations `A` and `B`, the canonical change of
representation is

`B.encode ∘ A.decode`.

It preserves the underlying quantitative state exactly, is bijective, has the
reverse change as an explicit inverse, is identity on a representation, composes
coherently, and is pointwise unique among maps agreeing on represented states.
-/

namespace QuantityRepresentationFoundations
namespace ConstructiveFiniteRepresentationChange

universe u v w

/-- Decidable equality pulled back through a faithful finite slot map. -/
def decidableEqOfSlot
    {Code : Type u} {N : ℕ}
    (slot : Code → Fin N) (hslot : Function.Injective slot) : DecidableEq Code :=
  fun a b =>
    if h : slot a = slot b then
      isTrue (hslot h)
    else
      isFalse (fun hab => h (congrArg slot hab))

/--
A finite quantitative representation with explicit faithful placement into the
same finite capacity.  No decoder or surjectivity proof is supplied.
-/
structure Representation (N : ℕ) where
  Code : Type u
  encode : Fin N → Code
  encode_injective : Function.Injective encode
  slot : Code → Fin N
  slot_injective : Function.Injective slot

namespace Representation

variable {N : ℕ}

/-- Equality of code states is computationally decided through finite slots. -/
def decEq (R : Representation.{u} N) : DecidableEq R.Code :=
  decidableEqOfSlot R.slot R.slot_injective

/-- Finite-capacity conservation makes every faithful encoder onto. -/
theorem encode_surjective (R : Representation.{u} N) :
    Function.Surjective R.encode :=
  ConstructiveFiniteCapacityConservation.encode_surjective
    R.encode R.encode_injective R.slot R.slot_injective

/-- Both directions of a finite representation saturate capacity exactly. -/
theorem capacity_conservation (R : Representation.{u} N) :
    Function.Bijective R.encode ∧ Function.Bijective R.slot :=
  ConstructiveFiniteCapacityConservation.finite_capacity_conservation
    R.encode R.encode_injective R.slot R.slot_injective

/--
Explicit decoder recovered by structural search.  The slot value is an explicit
fallback, so this definition works uniformly even at `N = 0`; conservation
proves below that the fallback is never used.
-/
def decode (R : Representation.{u} N) (c : R.Code) : Fin N :=
  match @ConstructiveFiniteInverse.findPreimage R.Code R.decEq N R.encode c with
  | some n => n
  | none => R.slot c

/-- Encoding the recovered decoder returns the original code state. -/
theorem encode_decode (R : Representation.{u} N) (c : R.Code) :
    R.encode (R.decode c) = c := by
  obtain ⟨witness, hwitness⟩ := R.encode_surjective c
  obtain ⟨n, hn⟩ :=
    @ConstructiveFiniteInverse.findPreimage_complete
      R.Code R.decEq N R.encode c ⟨witness, hwitness⟩
  unfold decode
  rw [hn]
  exact @ConstructiveFiniteInverse.findPreimage_sound
    R.Code R.decEq N R.encode c n hn

/-- Decoding an encoded quantitative state returns that exact state. -/
theorem decode_encode (R : Representation.{u} N) (n : Fin N) :
    R.decode (R.encode n) = n := by
  apply R.encode_injective
  exact R.encode_decode (R.encode n)

/-- Canonical change of representation through the common quantitative state. -/
def change
    (A : Representation.{u} N) (B : Representation.{v} N)
    (c : A.Code) : B.Code :=
  B.encode (A.decode c)

/-- Changing the representation of an encoded state only changes its encoding. -/
theorem change_encode
    (A : Representation.{u} N) (B : Representation.{v} N)
    (n : Fin N) :
    change A B (A.encode n) = B.encode n := by
  unfold change
  rw [A.decode_encode n]

/-- The underlying quantitative state is invariant under change of representation. -/
theorem decode_change
    (A : Representation.{u} N) (B : Representation.{v} N)
    (c : A.Code) :
    B.decode (change A B c) = A.decode c := by
  unfold change
  exact B.decode_encode (A.decode c)

/-- Changing representation and immediately changing back is exactly identity. -/
theorem change_roundtrip
    (A : Representation.{u} N) (B : Representation.{v} N)
    (c : A.Code) :
    change B A (change A B c) = c := by
  unfold change
  rw [B.decode_encode (A.decode c)]
  exact A.encode_decode c

/-- The canonical change from a representation to itself is identity. -/
theorem change_identity
    (A : Representation.{u} N) (c : A.Code) :
    change A A c = c :=
  A.encode_decode c

/-- Canonical changes compose through any intermediate representation. -/
theorem change_comp
    (A : Representation.{u} N)
    (B : Representation.{v} N)
    (C : Representation.{w} N)
    (c : A.Code) :
    change B C (change A B c) = change A C c := by
  unfold change
  rw [B.decode_encode (A.decode c)]

/-- Every canonical change of finite representation is bijective. -/
theorem change_bijective
    (A : Representation.{u} N) (B : Representation.{v} N) :
    Function.Bijective (change A B) := by
  constructor
  · intro x y hxy
    calc
      x = change B A (change A B x) := (A.change_roundtrip B x).symm
      _ = change B A (change A B y) := congrArg (change B A) hxy
      _ = y := A.change_roundtrip B y
  · intro y
    exact ⟨change B A y, B.change_roundtrip A y⟩

/--
The canonical change is pointwise unique among maps that preserve every
quantitative state on encoded inputs.
-/
theorem change_unique_pointwise
    (A : Representation.{u} N) (B : Representation.{v} N)
    (T : A.Code → B.Code)
    (hT : ∀ n : Fin N, T (A.encode n) = B.encode n)
    (c : A.Code) :
    T c = change A B c := by
  calc
    T c = T (A.encode (A.decode c)) := congrArg T (A.encode_decode c).symm
    _ = B.encode (A.decode c) := hT (A.decode c)
    _ = change A B c := rfl

end Representation
end ConstructiveFiniteRepresentationChange
end QuantityRepresentationFoundations
