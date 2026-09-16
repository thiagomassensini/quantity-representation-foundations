import QuantityRepresentationFoundations.ConstructiveFiniteInverse

/-!
# Constructive bijective carry tower

This module removes the explicit-decoder hypothesis from the primitive carry
rigidity theorem.

At each depth we assume only:

* an arbitrary code type;
* decidable equality on that code type;
* an encoder from the canonical finite quantity window;
* propositional injectivity and surjectivity of that encoder.

`ConstructiveFiniteInverse` reconstructs a decoder by finite search with an
empty logical axiom trace.  The resulting exact codecs therefore form a
`PrimitiveCarry.Tower`, to which the primitive carry-collapse theorem applies.
-/

namespace QuantityRepresentationFoundations
namespace ConstructiveBijectiveCarryTower

universe u

/-- A tower specified only by bijective encoders, with no decoder supplied. -/
structure Tower (b : ℕ) where
  Code : ℕ → Type u
  decEq : ∀ k : ℕ, DecidableEq (Code k)
  encode : ∀ k : ℕ, PrimitiveCarry.WindowState b k → Code k
  injective : ∀ k : ℕ, Function.Injective (encode k)
  surjective : ∀ k : ℕ, Function.Surjective (encode k)

namespace Tower

variable {b : ℕ}

/-- Recover the exact primitive codec at one depth by structural finite search. -/
def level
    (tower : Tower.{u} b) (hb : 0 < b) (k : ℕ) :
    PrimitiveCarry.CodeWindow b k (tower.Code k) :=
  @ConstructiveFiniteInverse.primitiveCodeWindowOfBijective
    b k hb (tower.Code k) (tower.decEq k)
    (tower.encode k) (tower.injective k) (tower.surjective k)

/-- Promote a bijective-encoder tower to the exact primitive carry tower. -/
def toPrimitiveTower
    (tower : Tower.{u} b) (hb : 0 < b) : PrimitiveCarry.Tower.{u} b where
  Code := tower.Code
  level := tower.level hb

/--
Axiom-free carry rigidity without a supplied decoder.

Every tower of arbitrary code types whose level encoders are propositionally
bijective and decidably comparable collapses to the primitive projective carry
tower.  The decoder and both inverse laws are derived internally by finite
search rather than supplied as hypotheses or chosen noncomputably.
-/
theorem collapses_to_carry
    (tower : Tower.{u} b) (hb : 1 < b) :
    PrimitiveCarry.Tower.Certificate
      (tower.toPrimitiveTower (lt_trans Nat.zero_lt_one hb))
      (lt_trans Nat.zero_lt_one hb) := by
  exact PrimitiveCarry.Tower.collapses_to_carry
    (tower.toPrimitiveTower (lt_trans Nat.zero_lt_one hb)) hb

end Tower
end ConstructiveBijectiveCarryTower
end QuantityRepresentationFoundations
