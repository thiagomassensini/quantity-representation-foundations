import QuantityRepresentationFoundations.ConstructiveCarryRigidity
import QuantityRepresentationFoundations.AxiomFreeCarryRigidityCore
import QuantityRepresentationFoundations.PrimitiveAxiomFreeCarryRigidity
import QuantityRepresentationFoundations.ConstructiveFiniteInverse
import QuantityRepresentationFoundations.ConstructiveBijectiveCarryTower
import QuantityRepresentationFoundations.PrimitiveFinitePigeonhole
import QuantityRepresentationFoundations.ConstructiveCapacityCarryTower

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

/-! Baseline probes explaining where the legacy `propext` trace comes from. -/

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

/-! Primitive carry route: every declaration below is intended to have an empty axiom trace. -/

#print axioms QuantityRepresentationFoundations.PrimitiveCarry.natPow_pos
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.natSucc_ne_zero
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.cycleSucc_of_lt
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.cycleSucc_of_not_lt
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.boundary_eq
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.cycleSucc_eq_zero_iff_carry
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.windowSuccessor_eq_zero_iff_carry
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.iterate_period
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.iterate_mul_period
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.lower_period_over_upper_capacity
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.depthProjection_zero
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.depthProjection_commutes_successor
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.depthProjection_refl_pointwise
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.depthProjection_unique_pointwise
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.depthProjection_comp_pointwise
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.CodeWindow.encode_injective
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.CodeWindow.successor_encode
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.CodeWindow.wrap_iff_carry
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.CodeWindow.projection_zero
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.CodeWindow.projection_commutes_successor
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.CodeWindow.projection_unique_pointwise
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.CodeWindow.projection_refl_pointwise
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.CodeWindow.projection_comp_pointwise
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.Tower.collapses_to_carry

/--
info: 'QuantityRepresentationFoundations.PrimitiveCarry.Tower.collapses_to_carry' does not depend on any axioms
-/
#guard_msgs in
#print axioms QuantityRepresentationFoundations.PrimitiveCarry.Tower.collapses_to_carry

/-! Constructive finite inverse: recover an explicit decoder from finite search. -/

#print axioms QuantityRepresentationFoundations.ConstructiveFiniteInverse.findPreimage
#print axioms QuantityRepresentationFoundations.ConstructiveFiniteInverse.findPreimage_sound
#print axioms QuantityRepresentationFoundations.ConstructiveFiniteInverse.findPreimage_complete
#print axioms QuantityRepresentationFoundations.ConstructiveFiniteInverse.decode
#print axioms QuantityRepresentationFoundations.ConstructiveFiniteInverse.encode_decode
#print axioms QuantityRepresentationFoundations.ConstructiveFiniteInverse.decode_encode
#print axioms QuantityRepresentationFoundations.ConstructiveFiniteInverse.primitiveCodeWindowOfBijective

/--
info: 'QuantityRepresentationFoundations.ConstructiveFiniteInverse.primitiveCodeWindowOfBijective' does not depend on any axioms
-/
#guard_msgs in
#print axioms QuantityRepresentationFoundations.ConstructiveFiniteInverse.primitiveCodeWindowOfBijective

/-! Decoder-free tower: only bijective encoders plus decidable equality are supplied. -/

#print axioms QuantityRepresentationFoundations.ConstructiveBijectiveCarryTower.Tower.level
#print axioms QuantityRepresentationFoundations.ConstructiveBijectiveCarryTower.Tower.toPrimitiveTower
#print axioms QuantityRepresentationFoundations.ConstructiveBijectiveCarryTower.Tower.collapses_to_carry

/-! Primitive finite pigeonhole route, avoiding abstract cardinality. -/

#print axioms QuantityRepresentationFoundations.PrimitiveFinitePigeonhole.complementDecode
#print axioms QuantityRepresentationFoundations.PrimitiveFinitePigeonhole.complementDecode_spec
#print axioms QuantityRepresentationFoundations.PrimitiveFinitePigeonhole.injective_implies_surjective

/--
info: 'QuantityRepresentationFoundations.PrimitiveFinitePigeonhole.injective_implies_surjective' does not depend on any axioms
-/
#guard_msgs in
#print axioms QuantityRepresentationFoundations.PrimitiveFinitePigeonhole.injective_implies_surjective

/-! Constructive finite-capacity route: faithful encoding plus explicit slots only. -/

#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.decidableEqOfEmbedding
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.encodedSlots_injective
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.encodedSlots_surjective
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.encodedSlots_bijective
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.encode_surjective
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.encode_bijective
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.capacityEmbed_surjective
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.capacityEmbed_bijective
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.capacity_saturated
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.level
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.toPrimitiveTower
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.collapses_to_carry

/--
info: 'QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.capacity_saturated' does not depend on any axioms
-/
#guard_msgs in
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.capacity_saturated

/--
info: 'QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.collapses_to_carry' does not depend on any axioms
-/
#guard_msgs in
#print axioms QuantityRepresentationFoundations.ConstructiveCapacityCarryTower.Tower.collapses_to_carry

/-! Finite-cardinality boundary in the legacy route. -/

#print axioms QuantityRepresentationFoundations.LosslessCompressedWindow.card_eq_windowSize
#print axioms QuantityRepresentationFoundations.LosslessCompressedWindow.encode_bijective
#print axioms Fintype.card_le_of_injective
#print axioms Fintype.bijective_iff_injective_and_card
#print axioms Equiv.ofBijective

/-! Library-source localization retained for reproducibility of the design choice. -/

#print axioms dif_pos
#print axioms dif_neg
#print axioms Nat.succ_ne_zero
#print axioms Nat.ne_of_lt
#print axioms Nat.lt_irrefl
#print axioms Nat.mul_pos

#print axioms Nat.mod_eq
#print axioms Nat.modCore_eq
#print axioms Nat.modCore_eq_mod
#print axioms Nat.mod_zero
#print axioms Nat.mod_eq_of_lt
#print axioms Nat.mod_mod_of_dvd
#print axioms Nat.mod_add_mod

#print axioms dvd_refl
#print axioms dvd_mul_of_dvd_left
#print axioms Nat.mul_assoc
#print axioms Nat.mul_one
#print axioms Nat.one_mul
#print axioms Nat.le_antisymm
#print axioms Nat.le_of_not_gt
#print axioms Nat.succ_le_of_lt
#print axioms Nat.not_le_of_gt
