import QuantityRepresentationFoundations.ConstructiveCarryRigidity

namespace QuantityRepresentationFoundations.ConstructiveAxiomProbe

theorem nat_rfl_probe (n : ℕ) : n = n := rfl

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

variable {b k : ℕ} {Code : Type u}

theorem raw_decode_encode_field_probe
    (rep : ExplicitLosslessWindow b k Code)
    (n : Fin (b ^ k)) :
    rep.decode (rep.encode n) = n :=
  rep.decode_encode_law n

end QuantityRepresentationFoundations.ConstructiveAxiomProbe

#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.nat_rfl_probe
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.Tiny.law
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.TinyPair.left
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.TinyFin.left
#print axioms QuantityRepresentationFoundations.ExplicitLosslessWindow.decode_encode_law
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.raw_decode_encode_field_probe
#print axioms QuantityRepresentationFoundations.ExplicitLosslessTower.explicit_lossless_tower_collapses_to_carry
