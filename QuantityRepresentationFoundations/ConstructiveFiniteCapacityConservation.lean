import QuantityRepresentationFoundations.PrimitiveFinitePigeonhole

/-!
# Constructive finite-capacity conservation

This module isolates the finite information principle underneath the positional
carry application.  There is no base, digit depth, quotient/remainder law, or
carry hypothesis here.

Given a type `Code` and a finite reference window `Fin N`, assume only:

* a faithful representation `encode : Fin N → Code`;
* a faithful capacity placement `slot : Code → Fin N`.

The composite `slot ∘ encode` is an injective self-map of `Fin N`.  The
primitive finite pigeonhole theorem therefore makes it surjective.  This forces
both original maps to be surjective as well, hence bijective.

In this proof-relevant form, finite capacity plus losslessness leaves neither
missing represented states nor unused code states.
-/

namespace QuantityRepresentationFoundations
namespace ConstructiveFiniteCapacityConservation

universe u

/-- The representation followed by its capacity placement is faithful. -/
theorem encodedSlots_injective
    {Code : Type u} {N : ℕ}
    (encode : Fin N → Code) (hinj : Function.Injective encode)
    (slot : Code → Fin N) (hslot : Function.Injective slot) :
    Function.Injective (fun n : Fin N => slot (encode n)) := by
  intro a b h
  apply hinj
  exact hslot h

/-- An injective finite representation fills every reference slot. -/
theorem encodedSlots_surjective
    {Code : Type u} {N : ℕ}
    (encode : Fin N → Code) (hinj : Function.Injective encode)
    (slot : Code → Fin N) (hslot : Function.Injective slot) :
    Function.Surjective (fun n : Fin N => slot (encode n)) :=
  PrimitiveFinitePigeonhole.injective_implies_surjective
    (fun n : Fin N => slot (encode n))
    (encodedSlots_injective encode hinj slot hslot)

/-- The encoded-slot map is therefore a permutation of the finite reference window. -/
theorem encodedSlots_bijective
    {Code : Type u} {N : ℕ}
    (encode : Fin N → Code) (hinj : Function.Injective encode)
    (slot : Code → Fin N) (hslot : Function.Injective slot) :
    Function.Bijective (fun n : Fin N => slot (encode n)) :=
  ⟨encodedSlots_injective encode hinj slot hslot,
    encodedSlots_surjective encode hinj slot hslot⟩

/-- A faithful finite representation cannot omit a code state. -/
theorem encode_surjective
    {Code : Type u} {N : ℕ}
    (encode : Fin N → Code) (hinj : Function.Injective encode)
    (slot : Code → Fin N) (hslot : Function.Injective slot) :
    Function.Surjective encode := by
  intro c
  obtain ⟨n, hn⟩ :=
    encodedSlots_surjective encode hinj slot hslot (slot c)
  refine ⟨n, ?_⟩
  exact hslot hn

/-- Every finite reference slot is occupied by a code state. -/
theorem slot_surjective
    {Code : Type u} {N : ℕ}
    (encode : Fin N → Code) (hinj : Function.Injective encode)
    (slot : Code → Fin N) (hslot : Function.Injective slot) :
    Function.Surjective slot := by
  intro n
  obtain ⟨m, hm⟩ :=
    encodedSlots_surjective encode hinj slot hslot n
  exact ⟨encode m, hm⟩

/-- The representation map is exactly capacity-preserving. -/
theorem encode_bijective
    {Code : Type u} {N : ℕ}
    (encode : Fin N → Code) (hinj : Function.Injective encode)
    (slot : Code → Fin N) (hslot : Function.Injective slot) :
    Function.Bijective encode :=
  ⟨hinj, encode_surjective encode hinj slot hslot⟩

/-- The capacity placement is also exactly capacity-preserving. -/
theorem slot_bijective
    {Code : Type u} {N : ℕ}
    (encode : Fin N → Code) (hinj : Function.Injective encode)
    (slot : Code → Fin N) (hslot : Function.Injective slot) :
    Function.Bijective slot :=
  ⟨hslot, slot_surjective encode hinj slot hslot⟩

/--
Constructive conservation of finite quantitative capacity.

Faithful maps in both directions between `Fin N` and `Code` force exact
representation in both directions; no abstract cardinality computation is
needed.
-/
theorem finite_capacity_conservation
    {Code : Type u} {N : ℕ}
    (encode : Fin N → Code) (hinj : Function.Injective encode)
    (slot : Code → Fin N) (hslot : Function.Injective slot) :
    Function.Bijective encode ∧ Function.Bijective slot :=
  ⟨encode_bijective encode hinj slot hslot,
    slot_bijective encode hinj slot hslot⟩

end ConstructiveFiniteCapacityConservation
end QuantityRepresentationFoundations
