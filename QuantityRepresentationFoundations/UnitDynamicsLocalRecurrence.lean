import QuantityRepresentationFoundations.FirstDistinguishingDepth

/-!
# Unit dynamics and forced local recurrence

This module introduces the first dynamic object in the foundations project.

The quantity state type `Q` remains completely abstract.  We do not assume
addition, natural-number structure, a numeral base, quotient, remainder,
division, modulo, positional weights, normalization, or carry.

`ℕ` appears only as an external clock indexing repeated unit steps.

A `UnitTrajectory Q` consists of:

* a state observed after each external step;
* a transition map advancing one step;
* coherence between the clocked trajectory and the transition;
* injectivity of the trajectory, expressing that distinct step counts represent
  distinct quantity states.

The main consequence is purely finite-state: observing such an infinite,
nonrepeating trajectory through any finite local state forces local recurrence.
If the full representation is faithful, the repeated local state must be
accompanied by a difference outside the local component.
-/

namespace QuantityRepresentationFoundations

/--
An abstract unit-step trajectory.  The natural number is only an external step
counter; no arithmetic structure is imposed on `Q`.
-/
structure UnitTrajectory (Q : Type*) where
  state : ℕ → Q
  transition : Q → Q
  evolves : ∀ n, state (n + 1) = transition (state n)
  state_injective : Function.Injective state

/-- Two clock times form a local recurrence when the later state has the same
finite local observation as the earlier one. -/
def LocalRecurrence
    {Q Local : Type*}
    (trajectory : UnitTrajectory Q)
    (local : Q → Local)
    (m n : ℕ) : Prop :=
  m < n ∧ local (trajectory.state m) = local (trajectory.state n)

/--
Every observation of an injective unit trajectory in a finite local state space
must recur locally.

No global representation or faithfulness hypothesis is needed for this first
recurrence statement.
-/
theorem unitTrajectory_forces_localRecurrence
    {Q Local : Type*} [Finite Local]
    (trajectory : UnitTrajectory Q)
    (local : Q → Local) :
    ∃ m n, LocalRecurrence trajectory local m n := by
  obtain ⟨m, n, hne, heq⟩ :=
    finiteState_forces_collision (fun k : ℕ => local (trajectory.state k))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨m, n, hlt, heq⟩
  · exact ⟨n, m, hgt, heq.symm⟩

/--
A local recurrence along an injective trajectory always corresponds to two
distinct quantity states.
-/
theorem localRecurrence_states_ne
    {Q Local : Type*}
    (trajectory : UnitTrajectory Q)
    (local : Q → Local)
    {m n : ℕ}
    (hrec : LocalRecurrence trajectory local m n) :
    trajectory.state m ≠ trajectory.state n := by
  exact trajectory.state_injective.ne (Nat.ne_of_lt hrec.1)

/--
If a globally faithful representation splits into a finite local component and
an arbitrary extension component, then a forced local recurrence must be
resolved by a difference in the extension component.

This is the first dynamic `local recurrence forces nonlocal distinction`
theorem.  It does not yet identify the extension with a next positional level
or a carry channel.
-/
theorem unitTrajectory_localRecurrence_forces_extensionDifference
    {Q Local Extension : Type*}
    [Finite Local]
    (trajectory : UnitTrajectory Q)
    (encode : Q → Local × Extension)
    (hfaithful : FaithfulRepresentation encode) :
    ∃ m n,
      m < n ∧
      (encode (trajectory.state m)).1 = (encode (trajectory.state n)).1 ∧
      (encode (trajectory.state m)).2 ≠ (encode (trajectory.state n)).2 := by
  obtain ⟨m, n, hmn, hlocal⟩ :=
    unitTrajectory_forces_localRecurrence trajectory (fun q => (encode q).1)
  have hstate : trajectory.state m ≠ trajectory.state n :=
    trajectory.state_injective.ne (Nat.ne_of_lt hmn)
  exact ⟨m, n, hmn, hlocal,
    sameLocal_forces_extension_difference encode hfaithful hstate hlocal⟩

/--
Local recurrence occurs arbitrarily late along the unit trajectory: after every
external cutoff there are two later clock times with the same finite local
observation.
-/
theorem unitTrajectory_has_arbitrarily_late_localRecurrence
    {Q Local : Type*} [Finite Local]
    (trajectory : UnitTrajectory Q)
    (local : Q → Local) :
    ∀ cutoff : ℕ,
      ∃ m n,
        cutoff ≤ m ∧
        LocalRecurrence trajectory local m n := by
  intro cutoff
  obtain ⟨a, b, hne, heq⟩ :=
    finiteState_forces_collision
      (fun k : ℕ => local (trajectory.state (cutoff + k)))
  rcases lt_or_gt_of_ne hne with hab | hba
  · refine ⟨cutoff + a, cutoff + b, Nat.le_add_right cutoff a, ?_, heq⟩
    omega
  · refine ⟨cutoff + b, cutoff + a, Nat.le_add_right cutoff b, ?_, heq.symm⟩
    omega

/--
Arbitrarily late local recurrences in a faithful split representation force
arbitrarily late differences in the extension component.
-/
theorem unitTrajectory_has_arbitrarily_late_extensionDifference
    {Q Local Extension : Type*}
    [Finite Local]
    (trajectory : UnitTrajectory Q)
    (encode : Q → Local × Extension)
    (hfaithful : FaithfulRepresentation encode) :
    ∀ cutoff : ℕ,
      ∃ m n,
        cutoff ≤ m ∧
        m < n ∧
        (encode (trajectory.state m)).1 = (encode (trajectory.state n)).1 ∧
        (encode (trajectory.state m)).2 ≠ (encode (trajectory.state n)).2 := by
  intro cutoff
  obtain ⟨m, n, hcutoff, hmn, hlocal⟩ :=
    unitTrajectory_has_arbitrarily_late_localRecurrence trajectory
      (fun q => (encode q).1) cutoff
  have hstate : trajectory.state m ≠ trajectory.state n :=
    trajectory.state_injective.ne (Nat.ne_of_lt hmn)
  exact ⟨m, n, hcutoff, hmn, hlocal,
    sameLocal_forces_extension_difference encode hfaithful hstate hlocal⟩

end QuantityRepresentationFoundations
