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
#print axioms QuantityRepresentationFoundations.ExplicitLosslessTower.explicit_lossless_tower_collapses_to_carry

#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.natPow_pos
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.windowSuccessor_eq_zero_iff_carry
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.windowSuccessor_mk_of_succ_lt
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.natPow_dvd_of_le
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.depthProjection_zero
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.depthProjection_commutes_successor
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.depthProjection_refl_pointwise
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.depthProjection_comp
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.depthProjection_unique_pointwise
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Window.encode_injective
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Window.successor_encode
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Window.wrap_iff_carry
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Window.exact_successor_unique_pointwise
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Window.projection_zero
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Window.projection_commutes_successor
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Window.projection_unique_pointwise
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Window.projection_refl_pointwise
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Window.projection_comp_pointwise
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Tower.collapses_to_carry

#print axioms Nat.mod_mod_of_dvd
#print axioms Nat.mod_add_mod
#print axioms Nat.mod_eq_of_lt
#print axioms Nat.lt_of_succ_lt
