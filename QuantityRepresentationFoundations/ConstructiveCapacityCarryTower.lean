import QuantityRepresentationFoundations.PrimitiveFinitePigeonhole
import QuantityRepresentationFoundations.ConstructiveFiniteInverse

/-!
# Constructive capacity carry tower

This module replaces the legacy abstract cardinality budget
`Fintype.card Code ≤ N` by explicit finite data:

* a faithful encoder `Fin N → Code`;
* a faithful capacity embedding `Code → Fin N`.

The two injections give an injective self-map of `Fin N`.  The primitive finite
pigeonhole theorem makes that self-map surjective without `Fintype.card`.
Consequently both representation maps saturate the finite capacity: the encoder
and the capacity embedding are bijections.  Decidable equality on the code type
is recovered from the capacity embedding, and structural finite search constructs
the decoder.  The resulting exact codecs form the primitive carry tower.
-/

namespace QuantityRepresentationFoundations
namespace ConstructiveCapacityCarryTower

universe u

/-- Decidable equality pulled back along a faithful embedding into `Fin N`. -/
def decidableEqOfEmbedding
    {Code : Type u} {N : ℕ}
    (slot : Code → Fin N) (hslot : Function.Injective slot) : DecidableEq Code :=
  fun a b =>
    if h : slot a = slot b then
      isTrue (hslot h)
    else
      isFalse (fun hab => h (congrArg slot hab))

/--
A finite representation tower specified by a faithful encoder and an explicit
capacity embedding at every depth.  No decoder, surjectivity proof, cardinality
computation, or decidable equality on the code type is supplied.
-/
structure Tower (b : ℕ) where
  Code : ℕ → Type u
  encode : ∀ k : ℕ, PrimitiveCarry.WindowState b k → Code k
  encode_injective : ∀ k : ℕ, Function.Injective (encode k)
  capacityEmbed : ∀ k : ℕ, Code k → PrimitiveCarry.WindowState b k
  capacityEmbed_injective : ∀ k : ℕ, Function.Injective (capacityEmbed k)

namespace Tower

variable {b : ℕ}

/-- The explicit capacity embedding makes equality of code states decidable. -/
def decEq (tower : Tower.{u} b) (k : ℕ) : DecidableEq (tower.Code k) :=
  decidableEqOfEmbedding
    (tower.capacityEmbed k) (tower.capacityEmbed_injective k)

/-- Encoding followed by the capacity embedding is a faithful self-map. -/
theorem encodedSlots_injective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Injective
      (fun n : PrimitiveCarry.WindowState b k =>
        tower.capacityEmbed k (tower.encode k n)) := by
  intro a b' h
  apply tower.encode_injective k
  exact tower.capacityEmbed_injective k h

/-- The encoded-slot self-map fills every available finite slot. -/
theorem encodedSlots_surjective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Surjective
      (fun n : PrimitiveCarry.WindowState b k =>
        tower.capacityEmbed k (tower.encode k n)) :=
  PrimitiveFinitePigeonhole.injective_implies_surjective
    (fun n : PrimitiveCarry.WindowState b k =>
      tower.capacityEmbed k (tower.encode k n))
    (tower.encodedSlots_injective k)

/-- The encoded-slot self-map is a permutation of the finite window. -/
theorem encodedSlots_bijective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Bijective
      (fun n : PrimitiveCarry.WindowState b k =>
        tower.capacityEmbed k (tower.encode k n)) :=
  ⟨tower.encodedSlots_injective k, tower.encodedSlots_surjective k⟩

/--
The encoder is automatically onto: finite capacity leaves no room for a faithful
representation to omit a code state.
-/
theorem encode_surjective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Surjective (tower.encode k) := by
  intro c
  obtain ⟨n, hn⟩ :=
    tower.encodedSlots_surjective k (tower.capacityEmbed k c)
  refine ⟨n, ?_⟩
  exact tower.capacityEmbed_injective k hn

/-- Faithfulness plus explicit finite capacity forces the encoder to be exact. -/
theorem encode_bijective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Bijective (tower.encode k) :=
  ⟨tower.encode_injective k, tower.encode_surjective k⟩

/-- Every finite capacity slot is occupied by some code state. -/
theorem capacityEmbed_surjective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Surjective (tower.capacityEmbed k) := by
  intro n
  obtain ⟨m, hm⟩ := tower.encodedSlots_surjective k n
  exact ⟨tower.encode k m, hm⟩

/-- The capacity witness itself is therefore an exact finite reindexing. -/
theorem capacityEmbed_bijective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Bijective (tower.capacityEmbed k) :=
  ⟨tower.capacityEmbed_injective k, tower.capacityEmbed_surjective k⟩

/--
Constructive capacity saturation: neither side can contain unused states once
faithful maps exist in both directions at the same finite capacity.
-/
theorem capacity_saturated
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Bijective (tower.encode k) ∧
      Function.Bijective (tower.capacityEmbed k) :=
  ⟨tower.encode_bijective k, tower.capacityEmbed_bijective k⟩

/-- Recover the exact primitive codec at one depth from faithfulness plus capacity. -/
def level
    (tower : Tower.{u} b) (hb : 0 < b) (k : ℕ) :
    PrimitiveCarry.CodeWindow b k (tower.Code k) :=
  @ConstructiveFiniteInverse.primitiveCodeWindowOfBijective
    b k hb (tower.Code k) (tower.decEq k)
    (tower.encode k) (tower.encode_injective k) (tower.encode_surjective k)

/-- Promote the constructive-capacity tower to the exact primitive carry tower. -/
def toPrimitiveTower
    (tower : Tower.{u} b) (hb : 0 < b) : PrimitiveCarry.Tower.{u} b where
  Code := tower.Code
  level := tower.level hb

/--
Axiom-free carry rigidity from faithful encoding plus an explicit finite
capacity witness.  Neither a decoder nor encoder surjectivity nor an abstract
cardinality argument is assumed.
-/
theorem collapses_to_carry
    (tower : Tower.{u} b) (hb : 1 < b) :
    PrimitiveCarry.Tower.Certificate
      (tower.toPrimitiveTower (lt_trans Nat.zero_lt_one hb))
      (lt_trans Nat.zero_lt_one hb) := by
  exact PrimitiveCarry.Tower.collapses_to_carry
    (tower.toPrimitiveTower (lt_trans Nat.zero_lt_one hb)) hb

end Tower
end ConstructiveCapacityCarryTower
end QuantityRepresentationFoundations
