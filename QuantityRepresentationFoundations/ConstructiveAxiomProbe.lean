import QuantityRepresentationFoundations.ConstructiveCarryRigidity

namespace QuantityRepresentationFoundations.ConstructiveAxiomProbe

theorem nat_rfl_probe (n : ℕ) : n = n := rfl

universe u

variable {b k : ℕ} {Code : Type u}

theorem raw_decode_encode_field_probe
    (rep : ExplicitLosslessWindow b k Code)
    (n : Fin (b ^ k)) :
    rep.decode (rep.encode n) = n :=
  rep.decode_encode_law n

end QuantityRepresentationFoundations.ConstructiveAxiomProbe

#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.nat_rfl_probe
#print axioms QuantityRepresentationFoundations.ExplicitLosslessWindow.decode_encode_law
#print axioms QuantityRepresentationFoundations.ConstructiveAxiomProbe.raw_decode_encode_field_probe
#print axioms QuantityRepresentationFoundations.ExplicitLosslessWindow.decode_encode
#print axioms QuantityRepresentationFoundations.ExplicitLosslessWindow.encode_injective
#print axioms QuantityRepresentationFoundations.ExplicitLosslessWindow.wrap_iff_carry
#print axioms QuantityRepresentationFoundations.ExplicitLosslessWindow.exact_successor_unique_pointwise
#print axioms QuantityRepresentationFoundations.ExplicitLosslessWindow.projection_unique_pointwise
#print axioms QuantityRepresentationFoundations.ExplicitLosslessWindow.projection_refl_pointwise
#print axioms QuantityRepresentationFoundations.ExplicitLosslessWindow.projection_comp_pointwise
#print axioms QuantityRepresentationFoundations.ExplicitLosslessTower.explicit_lossless_tower_collapses_to_carry
