import QuantityRepresentationFoundations.InformationEscape

/-!
# Unbounded extension forced by faithful quantity representation

This module strengthens the finite-state obstruction without introducing any
positional arithmetic.

No base, digit, quotient, remainder, division, modulo, positional weight, or
carry appears in the hypotheses.

The two results are:

* if a faithful global encoding has a finite local component and an infinite
  source, then its extension component cannot itself be finite;
* more generally, no fixed finite tower of finite layers can faithfully encode
  an infinite source.

Thus finite local capacity does not merely force information to leave one local
state: if every layer remains finite, faithful representation requires
unbounded representational depth rather than any fixed finite number of layers.

This is still weaker than positionality.  The next problem is to identify the
minimal extra structure that turns unbounded depth into an ordered transport
between successive levels.
-/

namespace QuantityRepresentationFoundations

/--
If an infinite source is faithfully encoded into a finite local state paired
with an extension state, then the extension type must be infinite.

This is a cardinal consequence only; `Extension` is not assumed to be a scale,
position, counter, quotient, or carry channel.
-/
theorem faithfulFiniteLocal_forces_infiniteExtension
    {Q Local Extension : Type*}
    [Infinite Q] [Finite Local]
    (encode : Q → Local × Extension)
    (hfaithful : FaithfulRepresentation encode) :
    Infinite Extension := by
  by_contra hnotInfinite
  letI : Finite Extension := not_infinite_iff_finite.mp hnotInfinite
  exact
    (finiteLocal_and_finiteAuxiliary_still_obstruct_faithfulness encode)
      hfaithful

/--
A fixed finite family of finite representational layers is still a finite state
space.  Therefore it cannot faithfully encode an infinite source.

The layer types may vary with the level, so this theorem already covers mixed
finite local capacities.  What it rules out is *fixed finite depth*.
-/
theorem finiteFixedDepthTower_obstructs_faithfulness
    {Q : Type*} [Infinite Q]
    (depth : ℕ)
    (Layer : Fin depth → Type*)
    [∀ i, Finite (Layer i)]
    (encode : Q → ∀ i, Layer i) :
    ¬ FaithfulRepresentation encode := by
  exact finiteState_obstructs_faithfulRepresentation encode

/--
Packaged form: there is no faithful encoding of an infinite source into a
fixed-depth dependent tuple of finite layers.
-/
theorem noFaithfulEncoding_into_fixedFiniteDepthTower
    (Q : Type*) [Infinite Q]
    (depth : ℕ)
    (Layer : Fin depth → Type*)
    [∀ i, Finite (Layer i)] :
    IsEmpty (FaithfulEncoding Q (∀ i, Layer i)) := by
  exact noFaithfulEncoding_into_finite Q (∀ i, Layer i)

end QuantityRepresentationFoundations
