import QuantityRepresentationFoundations.ConstructiveCarryRigidity
import QuantityRepresentationFoundations.AxiomFreeCarryRigidityCore

namespace QuantityRepresentationFoundations.ConstructiveAxiomProbe

theorem nat_rfl_probe (n : ℕ) : n = n := rfl

theorem pow_notation_rfl_probe (b k : ℕ) : b ^ k = b ^ k := rfl

theorem nat_pow_rfl_probe (b k : ℕ) : Nat.pow b k = Nat.pow b k := rfl

universe u

structure TinyFin (n : ℕ) (Code : Type u) where
  enc : Fin n → Code
  dec : Code → Fin n
  left : ∀ a : Fin n, dec (enc a) = a
  right : ∀ c : Code, enc (dec c) = c

structure TinyPow (b k : ℕ) (Code : Type u) where
  enc : Fin (b ^ k) → Code
  dec : Code → Fin (b ^ k)
  left : ∀ a : Fin (b ^ k), dec (enc a) = a
  right : ∀ c : Code, enc (dec c) = c

structure TinyNatPow (b k : ℕ) (Code : Type u) where
  enc : Fin (Nat.pow b k) → Code
  dec : Code → Fin (Nat.pow b k)
  left : ∀ a : Fin (Nat.pow b k), dec (enc a) = a
  right : ∀ c : Code, enc (dec c) = c

end QuantityRepresentationFoundations.ConstructiveAxiomProbe

#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.nat_rfl_probe
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.pow_notation_rfl_probe
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.nat_pow_rfl_probe
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.TinyFin.left
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.TinyPow.left
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.TinyNatPow.left

#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.windowSuccessor_eq_zero_iff_carry
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.natPow_dvd_of_le
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.depthProjection_commutes_successor
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.depthProjection_unique_pointwise
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Tower.collapses_to_carry

#print axioms Nat.mod_eq
#print axioms Nat.modCore_eq
#print axioms Nat.modCore_eq_mod
#print axioms Nat.mod_zero
#print axioms Nat.mod_eq_of_lt
#print axioms Nat.mod_mod_of_dvd
#print axioms Nat.mod_add_mod
#print axioms Nat.mod_eq_of_lt

#print axioms dvd_refl
#print axioms dvd_mul_of_dvd_left
#print axioms Nat.mul_assoc
#print axioms Nat.mul_one
#print axioms Nat.one_mul
#print axioms Nat.le_antisymm
#print axioms Nat.le_of_not_gt
#print axioms Nat.succ_le_of_lt
#print axioms Nat.not_le_of_gt
