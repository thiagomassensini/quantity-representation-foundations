import Mathlib.Data.Fintype.Pigeonhole

/-!
# Finite-state obstruction to faithful quantity representation

This module is intentionally pre-positional.

It does not assume a base, digits, quotient, remainder, division, modulo,
positional weights, or carry.  The only primitive representational notion used
here is faithfulness: distinguishable source states must remain distinguishable
under encoding.

The first obstruction is purely cardinal:

* an infinite family of distinguishable quantities cannot be faithfully encoded
  into a finite state space;
* equivalently, every map from an infinite quantity domain to a finite local
  state space must identify two distinct quantities.

This is the first formal step toward the later research question: what extra
structure is forced when a representation must remain faithful despite finite
local capacity?
-/

namespace QuantityRepresentationFoundations

/--
A representation is faithful when it never identifies two distinct source
states.  No arithmetic structure is assumed on either the source or target.
-/
def FaithfulRepresentation {Q S : Type*} (encode : Q → S) : Prop :=
  Function.Injective encode

/--
A finite state space cannot faithfully represent an infinite source type.

This theorem contains no quotient/remainder, positional, or carry hypothesis.
-/
theorem finiteState_obstructs_faithfulRepresentation
    {Q S : Type*} [Infinite Q] [Finite S] (encode : Q → S) :
    ¬ FaithfulRepresentation encode := by
  simpa [FaithfulRepresentation] using
    (not_injective_infinite_finite encode)

/--
Collision form of the finite-state obstruction: any encoding from an infinite
source into a finite state space identifies two distinct source states.
-/
theorem finiteState_forces_collision
    {Q S : Type*} [Infinite Q] [Finite S] (encode : Q → S) :
    ∃ q₁ q₂ : Q, q₁ ≠ q₂ ∧ encode q₁ = encode q₂ := by
  exact Finite.exists_ne_map_eq_of_infinite encode

/--
A packaged faithful representation consists only of an encoding and a proof of
injectivity.  This structure deliberately contains no arithmetic operations.
-/
structure FaithfulEncoding (Q S : Type*) where
  encode : Q → S
  faithful : FaithfulRepresentation encode

/--
There is no packaged faithful encoding of an infinite quantity domain into a
finite state space.
-/
theorem noFaithfulEncoding_into_finite
    (Q S : Type*) [Infinite Q] [Finite S] :
    IsEmpty (FaithfulEncoding Q S) := by
  refine ⟨fun representation => ?_⟩
  exact (finiteState_obstructs_faithfulRepresentation representation.encode)
    representation.faithful

/--
Adding only another finite component cannot repair the obstruction.  A finite
local state together with a finite auxiliary state is still globally finite.

This does *not* yet prove that the auxiliary component must be a positional
scale; it only proves that bounded extra state is insufficient.
-/
theorem finiteLocal_and_finiteAuxiliary_still_obstruct_faithfulness
    {Q Local Auxiliary : Type*}
    [Infinite Q] [Finite Local] [Finite Auxiliary]
    (encode : Q → Local × Auxiliary) :
    ¬ FaithfulRepresentation encode := by
  exact finiteState_obstructs_faithfulRepresentation encode

end QuantityRepresentationFoundations
