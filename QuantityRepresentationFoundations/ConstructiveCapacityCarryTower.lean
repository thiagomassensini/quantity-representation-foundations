import QuantityRepresentationFoundations.ConstructiveFiniteCapacityConservation
import QuantityRepresentationFoundations.ConstructiveFiniteInverse

/-!
# Constructive capacity carry tower

This module specializes the generic constructive finite-capacity conservation
principle to positional windows `Fin (Nat.pow b k)`.

At each depth it assumes only:

* a faithful encoder from the positional window into a code type;
* a faithful placement of code states back into the same finite window.

Generic finite-capacity conservation forces both maps to be bijections.  The
capacity embedding also gives decidable equality on the code type, structural
finite search reconstructs the decoder, and the exact codecs are promoted to
the primitive carry tower.
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
A positional representation tower specified only by faithful maps in both
directions at every finite depth.  No decoder, surjectivity proof, abstract
cardinality computation, or decidable equality on the code type is supplied.
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

/-- Encoding followed by the capacity embedding is faithful. -/
theorem encodedSlots_injective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Injective
      (fun n : PrimitiveCarry.WindowState b k =>
        tower.capacityEmbed k (tower.encode k n)) :=
  ConstructiveFiniteCapacityConservation.encodedSlots_injective
    (tower.encode k) (tower.encode_injective k)
    (tower.capacityEmbed k) (tower.capacityEmbed_injective k)

/-- Generic finite-capacity conservation fills every positional slot. -/
theorem encodedSlots_surjective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Surjective
      (fun n : PrimitiveCarry.WindowState b k =>
        tower.capacityEmbed k (tower.encode k n)) :=
  ConstructiveFiniteCapacityConservation.encodedSlots_surjective
    (tower.encode k) (tower.encode_injective k)
    (tower.capacityEmbed k) (tower.capacityEmbed_injective k)

/-- The encoded-slot self-map is a permutation of the positional window. -/
theorem encodedSlots_bijective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Bijective
      (fun n : PrimitiveCarry.WindowState b k =>
        tower.capacityEmbed k (tower.encode k n)) :=
  ConstructiveFiniteCapacityConservation.encodedSlots_bijective
    (tower.encode k) (tower.encode_injective k)
    (tower.capacityEmbed k) (tower.capacityEmbed_injective k)

/-- The positional encoder is automatically onto. -/
theorem encode_surjective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Surjective (tower.encode k) :=
  ConstructiveFiniteCapacityConservation.encode_surjective
    (tower.encode k) (tower.encode_injective k)
    (tower.capacityEmbed k) (tower.capacityEmbed_injective k)

/-- Faithfulness plus explicit finite capacity forces the encoder to be exact. -/
theorem encode_bijective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Bijective (tower.encode k) :=
  ConstructiveFiniteCapacityConservation.encode_bijective
    (tower.encode k) (tower.encode_injective k)
    (tower.capacityEmbed k) (tower.capacityEmbed_injective k)

/-- Every positional capacity slot is occupied by some code state. -/
theorem capacityEmbed_surjective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Surjective (tower.capacityEmbed k) :=
  ConstructiveFiniteCapacityConservation.slot_surjective
    (tower.encode k) (tower.encode_injective k)
    (tower.capacityEmbed k) (tower.capacityEmbed_injective k)

/-- The capacity witness itself is an exact finite reindexing. -/
theorem capacityEmbed_bijective
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Bijective (tower.capacityEmbed k) :=
  ConstructiveFiniteCapacityConservation.slot_bijective
    (tower.encode k) (tower.encode_injective k)
    (tower.capacityEmbed k) (tower.capacityEmbed_injective k)

/--
Positional specialization of constructive finite-capacity conservation: neither
side contains unused states.
-/
theorem capacity_saturated
    (tower : Tower.{u} b) (k : ℕ) :
    Function.Bijective (tower.encode k) ∧
      Function.Bijective (tower.capacityEmbed k) :=
  ConstructiveFiniteCapacityConservation.finite_capacity_conservation
    (tower.encode k) (tower.encode_injective k)
    (tower.capacityEmbed k) (tower.capacityEmbed_injective k)

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
