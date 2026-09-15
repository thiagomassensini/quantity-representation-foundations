import QuantityRepresentationFoundations

/-!
# Kernel audit surface

The first public results are intentionally free of quotient, remainder,
positional, and carry primitives.  These commands expose their logical axioms.
-/

#print axioms QuantityRepresentationFoundations.finiteState_obstructs_faithfulRepresentation
#print axioms QuantityRepresentationFoundations.finiteState_forces_collision
#print axioms QuantityRepresentationFoundations.noFaithfulEncoding_into_finite
#print axioms QuantityRepresentationFoundations.finiteLocal_and_finiteAuxiliary_still_obstruct_faithfulness
