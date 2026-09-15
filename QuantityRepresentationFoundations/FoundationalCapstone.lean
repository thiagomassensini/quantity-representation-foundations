import QuantityRepresentationFoundations.IntrinsicPositionalUniqueness

/-!
# Foundational capstone

This module packages the complete constructive chain proved in the foundations
project into one auditable theorem surface.

The capstone deliberately does **not** claim that finite faithfulness alone
forces positional notation.  The operational assumptions accumulated along the
chain are made explicit in `FoundationalOperationalRepresentation`:

* an infinite injective unit-step trajectory of quantity states;
* a globally faithful representation split into a finite local channel and an
  arbitrary extension channel;
* an autonomous local dynamics intertwined with the unit step;
* injectivity of the local step (already part of `AutonomousLocalDynamics`), so
  local information is not erased;
* agreement between the autonomous local observation and the local component of
  the faithful representation;
* nontriviality of the first local step.

From those hypotheses, finite local state first forces recurrent local
information and compensating nonlocal distinction.  Autonomous injective local
dynamics then yields a unique least positive return.  Nontriviality rules out
period one, so the emergent capacity is genuinely greater than one.  All of the
previously constructed downstream structure then applies canonically:

* periodic local observation;
* residual control of the local readout;
* unique cycle-count/residual coordinates;
* exact identification of those coordinates with Carry Geometry normalization;
* unique canonical finite positional representation.

The standard `Nat.digits` representation remains a downstream crosswalk, not a
primitive ingredient of the capstone.
-/

namespace QuantityRepresentationFoundations

/--
The explicit operational hypotheses under which the full foundational chain is
assembled.

The source quantity type `Q` remains abstract.  Natural numbers still appear
only as the external unit-step clock used by `UnitTrajectory` and by the
resulting positional coordinates.
-/
structure FoundationalOperationalRepresentation
    (Q LocalState Extension : Type*) where
  trajectory : UnitTrajectory Q
  encode : Q → LocalState × Extension
  faithful : FaithfulRepresentation encode
  localDynamics : AutonomousLocalDynamics trajectory LocalState
  local_agrees_with_encoding :
    ∀ q : Q, localDynamics.observe q = (encode q).1
  first_local_step_changes :
    localDynamics.observe (trajectory.state 1) ≠
      localDynamics.observe (trajectory.state 0)

/--
A complete capstone certificate at a candidate capacity `b`.

Every field is a theorem already derived in earlier layers.  This structure is
therefore a compact audit surface for the whole chain rather than a new set of
axioms.
-/
structure FoundationalCapstoneAt
    {Q LocalState Extension : Type*}
    (system : FoundationalOperationalRepresentation Q LocalState Extension)
    (b : ℕ) : Prop where
  capacity :
    EmergentLocalCapacity system.trajectory system.localDynamics b
  genuine_capacity : 1 < b
  arbitrarily_late_extension_escape :
    ∀ cutoff : ℕ,
      ∃ m n,
        cutoff ≤ m ∧
        m < n ∧
        (system.encode (system.trajectory.state m)).1 =
          (system.encode (system.trajectory.state n)).1 ∧
        (system.encode (system.trajectory.state m)).2 ≠
          (system.encode (system.trajectory.state n)).2
  periodic_local_readout :
    ∀ n : ℕ,
      system.localDynamics.observe (system.trajectory.state (n + b)) =
        system.localDynamics.observe (system.trajectory.state n)
  residual_controls_local_readout :
    ∀ n : ℕ,
      system.localDynamics.observe (system.trajectory.state n) =
        system.localDynamics.observe
          (system.trajectory.state (emergentRemainder b n))
  unique_cycle_coordinates :
    ∀ n : ℕ,
      ∃! coordinates : ℕ × ℕ,
        IsCycleDecomposition b n coordinates.1 coordinates.2
  carry_geometry_normalization :
    ∀ n : ℕ,
      emergentQuotient b n = CarryGeometry.carryUnits b n ∧
        emergentRemainder b n = CarryGeometry.normalizedDigit b n
  unique_canonical_positional_representation :
    ∀ n : ℕ,
      ∃! coefficients : List ℕ,
        CarryGeometry.rawExpansionValue b coefficients = n ∧
        (∀ digit ∈ coefficients,
          CarryGeometry.IsAdmissibleDigit b digit) ∧
        (∀ h : coefficients ≠ [], coefficients.getLast h ≠ 0)

/--
A nontrivial first local step rules out capacity one.

The least positive return is already known to be positive.  If it were exactly
one, its return equation would say that the first local step leaves the local
state unchanged, contradicting the explicit nontriviality hypothesis.
-/
theorem emergentLocalCapacity_gt_one_of_first_step_changes
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    {b : ℕ}
    (hb : EmergentLocalCapacity trajectory model b)
    (hchange :
      model.observe (trajectory.state 1) ≠
        model.observe (trajectory.state 0)) :
    1 < b := by
  have hbpos : 0 < b := hb.1.1
  have hbne : b ≠ 1 := by
    intro hbone
    subst b
    exact hchange hb.1.2
  omega

/--
Foundational capstone theorem.

For every finite local state space and every operational representation system
satisfying the explicit hypotheses above, there is a unique dynamically
emergent capacity `b` carrying the complete positional/carry certificate.

The uniqueness of the capstone capacity is inherited from uniqueness of the
least positive local return; all later structure is forced at that same `b`.
-/
theorem existsUnique_foundationalCapstone
    {Q LocalState Extension : Type*}
    [Finite LocalState]
    (system : FoundationalOperationalRepresentation Q LocalState Extension) :
    ∃! b : ℕ, FoundationalCapstoneAt system b := by
  obtain ⟨b, hb, hb_unique⟩ :=
    existsUnique_emergentLocalCapacity system.trajectory system.localDynamics
  have hb1 : 1 < b :=
    emergentLocalCapacity_gt_one_of_first_step_changes
      system.trajectory system.localDynamics hb system.first_local_step_changes
  refine ⟨b, ?_, ?_⟩
  · refine
      { capacity := hb
        genuine_capacity := hb1
        arbitrarily_late_extension_escape := ?_
        periodic_local_readout := ?_
        residual_controls_local_readout := ?_
        unique_cycle_coordinates := ?_
        carry_geometry_normalization := ?_
        unique_canonical_positional_representation := ?_ }
    · exact unitTrajectory_has_arbitrarily_late_extensionDifference
        system.trajectory system.encode system.faithful
    · exact emergentLocalCapacity_periodic_readout
        system.trajectory system.localDynamics hb
    · intro n
      exact emergentRemainder_controls_localReadout
        system.trajectory system.localDynamics hb n
    · intro n
      exact emergentLocalCapacity_has_unique_cycleCoordinates
        system.trajectory system.localDynamics hb n
    · intro n
      exact emergentLocalCapacity_eq_carryGeometryNormalization
        system.trajectory system.localDynamics hb n
    · intro n
      exact existsUnique_intrinsicCanonicalExpansion b n hb1
  · intro c hc
    exact hb_unique c hc.capacity

/--
The capstone's canonical representation is the independently constructed
`emergentDigits` list.
-/
theorem foundationalCapstone_emergentDigits_are_unique
    {Q LocalState Extension : Type*}
    {system : FoundationalOperationalRepresentation Q LocalState Extension}
    {b n : ℕ}
    (hcap : FoundationalCapstoneAt system b) :
    CarryGeometry.rawExpansionValue b
        (emergentDigits b hcap.genuine_capacity n) = n ∧
      (∀ digit ∈ emergentDigits b hcap.genuine_capacity n,
        CarryGeometry.IsAdmissibleDigit b digit) ∧
      (∀ h : emergentDigits b hcap.genuine_capacity n ≠ [],
        (emergentDigits b hcap.genuine_capacity n).getLast h ≠ 0) := by
  exact ⟨rawExpansionValue_emergentDigits b n hcap.genuine_capacity,
    emergentDigits_digits_admissible b n hcap.genuine_capacity,
    emergentDigits_no_leading_zero b n hcap.genuine_capacity⟩

/--
Final classical crosswalk attached to the capstone.

The standard digit list is identified only after intrinsic existence and
uniqueness have already been established.
-/
theorem foundationalCapstone_recovers_natDigits
    {Q LocalState Extension : Type*}
    {system : FoundationalOperationalRepresentation Q LocalState Extension}
    {b : ℕ}
    (hcap : FoundationalCapstoneAt system b)
    (n : ℕ) :
    emergentDigits b hcap.genuine_capacity n = Nat.digits b n :=
  emergentDigits_eq_natDigits b n hcap.genuine_capacity

end QuantityRepresentationFoundations
