import QuantityRepresentationFoundations.CarryGeometryNormalizationBridge

/-!
# Emergent weighted positional transport

The previous layers derived a local cycle capacity `b`, recursively constructed
its cycle-count/residual coordinates, identified them with Euclidean QR only
afterwards, and then bridged them to `CarryGeometry.normalizedDigit` and
`CarryGeometry.carryUnits`.

This module lifts that local split to an arbitrary positional level `j`.
The key identity is derived first from the emergent decomposition itself:

`a * b^j = R_b(a) * b^j + Q_b(a) * b^(j+1)`.

Thus the residual component remains at the current level while the completed-
cycle component is transported exactly one scale upward.  Only after proving
that identity do we compare it with Carry Geometry's existing weighted
normalization theorem.
-/

namespace QuantityRepresentationFoundations

/--
The emergent local decomposition lifts exactly to every positional level.
The residual value stays at level `j`; the completed-cycle value is represented
at level `j + 1`.
-/
theorem emergent_weighted_positional_transport
    (b a j : ℕ) (hb : 0 < b) :
    a * CarryGeometry.placeValue b j =
      emergentRemainder b a * CarryGeometry.placeValue b j +
        emergentQuotient b a * CarryGeometry.placeValue b (j + 1) := by
  have hvalue := emergent_decomposition_value b a hb
  have hsplit :
      emergentRemainder b a + b * emergentQuotient b a = a := by
    calc
      emergentRemainder b a + b * emergentQuotient b a =
          emergentQuotient b a * b + emergentRemainder b a := by ac_rfl
      _ = a := hvalue.symm
  calc
    a * CarryGeometry.placeValue b j =
        (emergentRemainder b a + b * emergentQuotient b a) *
          CarryGeometry.placeValue b j := by rw [hsplit]
    _ = emergentRemainder b a * CarryGeometry.placeValue b j +
        emergentQuotient b a * CarryGeometry.placeValue b (j + 1) := by
      rw [CarryGeometry.placeValue_succ]
      ring

/--
The weighted split produced by the emergent coordinates is literally the same
split as Carry Geometry's normalized digit/carry decomposition.
-/
theorem emergent_weighted_parts_eq_carryGeometry_parts
    (b a j : ℕ) (hb : 0 < b) :
    emergentRemainder b a * CarryGeometry.placeValue b j +
        emergentQuotient b a * CarryGeometry.placeValue b (j + 1) =
      CarryGeometry.normalizedDigit b a * CarryGeometry.placeValue b j +
        CarryGeometry.carryUnits b a * CarryGeometry.placeValue b (j + 1) := by
  rw [emergentRemainder_eq_normalizedDigit b a hb,
      emergentQuotient_eq_carryUnits b a hb]

/--
The independently derived weighted transport recovers exactly the theorem
`CarryGeometry.weighted_coefficient_normalization`.
-/
theorem emergent_weighted_transport_recovers_carryGeometry_normalization
    (b a j : ℕ) (hb : 0 < b) :
    a * CarryGeometry.placeValue b j =
      CarryGeometry.normalizedDigit b a * CarryGeometry.placeValue b j +
        CarryGeometry.carryUnits b a * CarryGeometry.placeValue b (j + 1) := by
  calc
    a * CarryGeometry.placeValue b j =
        emergentRemainder b a * CarryGeometry.placeValue b j +
          emergentQuotient b a * CarryGeometry.placeValue b (j + 1) :=
      emergent_weighted_positional_transport b a j hb
    _ = CarryGeometry.normalizedDigit b a * CarryGeometry.placeValue b j +
        CarryGeometry.carryUnits b a * CarryGeometry.placeValue b (j + 1) :=
      emergent_weighted_parts_eq_carryGeometry_parts b a j hb

/--
At the first saturation, the local residual vanishes and exactly one unit of
value appears at the next positional level.
-/
theorem firstSaturation_transports_exactly_one_nextLevel
    (b j : ℕ) (hb : 0 < b) :
    emergentRemainder b b * CarryGeometry.placeValue b j +
        emergentQuotient b b * CarryGeometry.placeValue b (j + 1) =
      CarryGeometry.placeValue b (j + 1) := by
  have hone : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr (ne_of_gt hb)
  have hsat :
      emergentRemainder b b = 0 ∧ emergentQuotient b b = 1 := by
    simpa [Nat.sub_add_cancel hone] using
      firstSaturation_is_maxDigit_add_one_normalization b hb
  simp [hsat.1, hsat.2]

/--
Consequently, the value of one complete local cycle at level `j` is exactly one
unit at level `j + 1`.
-/
theorem firstSaturation_value_moves_to_nextLevel
    (b j : ℕ) (hb : 0 < b) :
    b * CarryGeometry.placeValue b j =
      CarryGeometry.placeValue b (j + 1) := by
  calc
    b * CarryGeometry.placeValue b j =
        emergentRemainder b b * CarryGeometry.placeValue b j +
          emergentQuotient b b * CarryGeometry.placeValue b (j + 1) :=
      emergent_weighted_positional_transport b b j hb
    _ = CarryGeometry.placeValue b (j + 1) :=
      firstSaturation_transports_exactly_one_nextLevel b j hb

/--
For a dynamically emergent local capacity, every external coefficient admits
the same exact one-level positional transport law.
-/
theorem emergentLocalCapacity_weighted_positional_transport
    {Q LocalState : Type*}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory LocalState)
    {b : ℕ}
    (hb : EmergentLocalCapacity trajectory model b)
    (a j : ℕ) :
    a * CarryGeometry.placeValue b j =
      emergentRemainder b a * CarryGeometry.placeValue b j +
        emergentQuotient b a * CarryGeometry.placeValue b (j + 1) :=
  emergent_weighted_positional_transport b a j hb.1.1

end QuantityRepresentationFoundations
