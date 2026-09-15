import QuantityRepresentationFoundations.FiniteStateObstruction

/-!
# Information escape from finite local state

This module isolates the next consequence of the finite-state obstruction.

We still do not assume quotient, remainder, digits, a base, positional weights,
or carry.  We only split a global representation into a `Local` component and
an arbitrary `Extension` component.

The result says that if two distinguishable quantities collide locally, then
faithfulness forces their extension states to differ.  When the local state
space is finite and the quantity domain is infinite, such a local collision is
unavoidable.  Therefore faithful representation requires information to escape
the finite local state.

No claim is made here that `Extension` is a positional scale.  Identifying the
weakest assumptions under which it must acquire a hierarchical/transport
structure is the next research problem.
-/

namespace QuantityRepresentationFoundations

/--
If two distinct source states have the same local image under a faithful global
encoding, their extension images must differ.
-/
theorem sameLocal_forces_extension_difference
    {Q Local Extension : Type*}
    (encode : Q → Local × Extension)
    (hfaithful : FaithfulRepresentation encode)
    {q₁ q₂ : Q}
    (hne : q₁ ≠ q₂)
    (hsameLocal : (encode q₁).1 = (encode q₂).1) :
    (encode q₁).2 ≠ (encode q₂).2 := by
  intro hsameExtension
  apply hne
  apply hfaithful
  exact Prod.ext hsameLocal hsameExtension

/--
For an infinite source and finite local state space, every faithful global
encoding into `Local × Extension` has two distinct source states that collide
locally and are necessarily distinguished by the extension component.

This is the first formal `information must leave the local state` theorem.
-/
theorem finiteLocal_forces_information_into_extension
    {Q Local Extension : Type*}
    [Infinite Q] [Finite Local]
    (encode : Q → Local × Extension)
    (hfaithful : FaithfulRepresentation encode) :
    ∃ q₁ q₂ : Q,
      q₁ ≠ q₂ ∧
      (encode q₁).1 = (encode q₂).1 ∧
      (encode q₁).2 ≠ (encode q₂).2 := by
  obtain ⟨q₁, q₂, hne, hlocal⟩ :=
    finiteState_forces_collision (fun q => (encode q).1)
  exact ⟨q₁, q₂, hne, hlocal,
    sameLocal_forces_extension_difference encode hfaithful hne hlocal⟩

end QuantityRepresentationFoundations
