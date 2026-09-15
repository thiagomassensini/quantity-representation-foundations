import QuantityRepresentationFoundations.ConstructiveCarryRigidity
import QuantityRepresentationFoundations.AxiomFreeCarryRigidityCore

namespace QuantityRepresentationFoundations.ConstructiveAxiomProbe

theorem nat_rfl_probe (n : ℕ) : n = n := rfl

theorem pow_notation_rfl_probe (b k : ℕ) : b ^ k = b ^ k := rfl

theorem nat_pow_rfl_probe (b k : ℕ) : Nat.pow b k = Nat.pow b k := rfl

universe u

structure Tiny (A : Type u) where
  f : A → A
  law : ∀ a : A, f a = a

structure TinyPair (A B : Type u) where
  enc : A → B
  dec : B → A
  left : ∀ a : A, dec (enc a) = a
  right : ∀ b : B, enc (dec b) = b

structure TinyFin (n : ℕ) (Code : Type u) where
  enc : Fin n → Code
  dec : Code → Fin n
  left : ∀ a : Fin n, dec (enc a) = a
  right : ∀ c : Code, enc (dec c) = c

structure TinyMul (b k : ℕ) (Code : Type u) where
  enc : Fin (b * k) → Code
  dec : Code → Fin (b * k)
  left : ∀ a : Fin (b * k), dec (enc a) = a
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

def rawPow (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => rawPow b k * b

structure TinyRawPow (b k : ℕ) (Code : Type u) where
  enc : Fin (rawPow b k) → Code
  dec : Code → Fin (rawPow b k)
  left : ∀ a : Fin (rawPow b k), dec (enc a) = a
  right : ∀ c : Code, enc (dec c) = c

variable {b k : ℕ} {Code : Type u}

theorem raw_decode_encode_field_probe
    (rep : ExplicitLosslessWindow b k Code)
    (n : Fin (b ^ k)) :
    rep.decode (rep.encode n) = n :=
  rep.decode_encode_law n

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
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.depthProjection_unique_pointwise
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Window.wrap_iff_carry
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Window.projection_unique_pointwise
#print axioms QuantityRepresentationFoundations.AxiomFreeCarry.Tower.collapses_to_carry
