import QuantityRepresentationFoundations.ConstructiveCarryRigidity

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

/-- Deliberately elementary power, to test whether the remaining dependency is
attached to the standard `Nat.pow` implementation rather than exponentiation as
mathematics. -/
def rawPow (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => rawPow b k * b

structure TinyRawPow (b k : ℕ) (Code : Type u) where
  enc : Fin (rawPow b k) → Code
  dec : Code → Fin (rawPow b k)
  left : ∀ a : Fin (rawPow b k), dec (enc a) = a
  right : ∀ c : Code, enc (dec c) = c

/-- Positivity of the explicit natural power, proved by recursion rather than
through the generic `^` notation. -/
theorem natPow_pos {b : ℕ} (hb : 0 < b) : ∀ k : ℕ, 0 < Nat.pow b k
  | 0 => Nat.zero_lt_succ 0
  | k + 1 => by
      change 0 < Nat.pow b k * b
      exact Nat.mul_pos (natPow_pos hb k) hb

/-- Canonical zero of the explicit-`Nat.pow` window. -/
def natPowWindowZero (b k : ℕ) (hb : 0 < b) : Fin (Nat.pow b k) :=
  ⟨0, natPow_pos hb k⟩

/-- Canonical cyclic successor without generic exponentiation notation. -/
def natPowWindowSuccessor
    (b k : ℕ) (hb : 0 < b) (n : Fin (Nat.pow b k)) :
    Fin (Nat.pow b k) :=
  ⟨(n.val + 1) % Nat.pow b k, Nat.mod_lt _ (natPow_pos hb k)⟩

/-- Carry-through-depth expressed directly as wrap modulo the explicit power. -/
def natPowCarryAtDepth (b k n : ℕ) : Prop :=
  (n + 1) % Nat.pow b k = 0

/-- The finite-window wrap event is exactly the explicit carry predicate. -/
theorem natPowWindowSuccessor_eq_zero_iff_carry
    (b k : ℕ) (hb : 0 < b) (n : Fin (Nat.pow b k)) :
    natPowWindowSuccessor b k hb n = natPowWindowZero b k hb ↔
      natPowCarryAtDepth b k n.val := by
  constructor
  · intro h
    exact congrArg Fin.val h
  · intro h
    apply Fin.ext
    exact h

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
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.Tiny.law
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.TinyPair.left
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.TinyFin.left
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.TinyMul.left
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.TinyPow.left
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.TinyNatPow.left
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.TinyRawPow.left
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.natPow_pos
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.natPowWindowSuccessor_eq_zero_iff_carry
#print axioms QuantityRepresentationFoundations.ExplicitLosslessWindow.decode_encode_law
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.raw_decode_encode_field_probe
#print axioms QuantityRepresentationFoundations.ExplicitLosslessTower.explicit_lossless_tower_collapses_to_carry
