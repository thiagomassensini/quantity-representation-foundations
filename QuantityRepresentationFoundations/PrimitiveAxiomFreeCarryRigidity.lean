import QuantityRepresentationFoundations.UniversalCarryCollapseCapstone

/-!
# Primitive axiom-free projective carry rigidity

This module reconstructs the projective carry dynamics without the standard
modulo/divisibility lemma layer.  The canonical finite cycle is defined directly:
increment while the next value remains inside the window, otherwise wrap to zero.
Cross-depth projection is repeated lower-level successor from zero.

All finite code levels carry explicit encoders and decoders.  Uniqueness is
pointwise.  The intended audit target is zero logical axioms.
-/

namespace QuantityRepresentationFoundations
namespace PrimitiveCarry

universe u v

/-- Positivity of explicit natural powers. -/
theorem natPow_pos {b : ℕ} (hb : 0 < b) : ∀ k : ℕ, 0 < Nat.pow b k
  | 0 => Nat.zero_lt_succ 0
  | k + 1 => by
      change 0 < Nat.pow b k * b
      exact Nat.mul_pos (natPow_pos hb k) hb

/-- Zero of a nonempty finite cycle. -/
def zero (N : ℕ) (hN : 0 < N) : Fin N := ⟨0, hN⟩

/-- Primitive cyclic successor: increment, or wrap at the boundary. -/
def cycleSucc (N : ℕ) (hN : 0 < N) (n : Fin N) : Fin N :=
  if h : n.val + 1 < N then ⟨n.val + 1, h⟩ else zero N hN

/-- Inside the boundary, primitive successor is ordinary increment. -/
theorem cycleSucc_of_lt
    (N : ℕ) (hN : 0 < N) (n : Fin N)
    (h : n.val + 1 < N) :
    cycleSucc N hN n = ⟨n.val + 1, h⟩ := by
  unfold cycleSucc
  exact dif_pos h

/-- At the boundary, primitive successor wraps to zero. -/
theorem cycleSucc_of_not_lt
    (N : ℕ) (hN : 0 < N) (n : Fin N)
    (h : ¬ n.val + 1 < N) :
    cycleSucc N hN n = zero N hN := by
  unfold cycleSucc
  exact dif_neg h

/-- For an in-window state, failure of another in-window increment means exact boundary. -/
theorem boundary_eq
    {N : ℕ} (n : Fin N) (h : ¬ n.val + 1 < N) :
    n.val + 1 = N := by
  apply Nat.le_antisymm
  · exact Nat.succ_le_of_lt n.isLt
  · exact Nat.le_of_not_gt h

/-- Primitive successor numerals cannot equal zero, proved directly by constructor disjointness. -/
theorem natSucc_ne_zero (n : ℕ) : n + 1 ≠ 0 := by
  change Nat.succ n ≠ 0
  intro h
  exact Nat.noConfusion h

/-- Carry at a finite window is the exact boundary event. -/
def carry (N : ℕ) (n : Fin N) : Prop := n.val + 1 = N

/-- Primitive successor wraps exactly on carry. -/
theorem cycleSucc_eq_zero_iff_carry
    (N : ℕ) (hN : 0 < N) (n : Fin N) :
    cycleSucc N hN n = zero N hN ↔ carry N n := by
  by_cases h : n.val + 1 < N
  · rw [cycleSucc_of_lt N hN n h]
    constructor
    · intro hz
      have hv : n.val + 1 = 0 := congrArg Fin.val hz
      exact False.elim ((natSucc_ne_zero n.val) hv)
    · intro hc
      exact False.elim ((Nat.ne_of_lt h) hc)
  · rw [cycleSucc_of_not_lt N hN n h]
    constructor
    · intro _
      exact boundary_eq n h
    · intro _
      rfl

/-- Iteration of an endomap. -/
def iterate {α : Sort u} (step : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => step (iterate step n x)

@[simp] theorem iterate_zero {α : Sort u} (step : α → α) (x : α) :
    iterate step 0 x = x := rfl

@[simp] theorem iterate_succ {α : Sort u} (step : α → α) (n : ℕ) (x : α) :
    iterate step (n + 1) x = step (iterate step n x) := rfl

/-- Iteration over a sum factors into successive iterations. -/
theorem iterate_add {α : Sort u} (step : α → α) :
    ∀ a b : ℕ, ∀ x : α,
      iterate step (a + b) x = iterate step b (iterate step a x)
  | a, 0, x => rfl
  | a, b + 1, x => by
      change step (iterate step (a + b) x) =
        step (iterate step b (iterate step a x))
      exact congrArg step (iterate_add step a b x)

/-- Before the boundary, iterating primitive successor from zero reaches the numeral itself. -/
theorem iterate_zero_eq_mk
    (N : ℕ) (hN : 0 < N) :
    ∀ a : ℕ, ∀ ha : a < N,
      iterate (cycleSucc N hN) a (zero N hN) = ⟨a, ha⟩
  | 0, ha => rfl
  | a + 1, ha => by
      have ha0 : a < N := Nat.lt_trans (Nat.lt_succ_self a) ha
      change cycleSucc N hN
          (iterate (cycleSucc N hN) a (zero N hN)) = ⟨a + 1, ha⟩
      rw [iterate_zero_eq_mk N hN a ha0]
      exact cycleSucc_of_lt N hN ⟨a, ha0⟩ ha

/-- One full primitive cycle returns zero. -/
theorem iterate_period
    (N : ℕ) (hN : 0 < N) :
    iterate (cycleSucc N hN) N (zero N hN) = zero N hN := by
  cases N with
  | zero => exact False.elim (Nat.lt_asymm hN hN)
  | succ t =>
      have ht : t < t + 1 := Nat.lt_succ_self t
      change cycleSucc (t + 1) hN
          (iterate (cycleSucc (t + 1) hN) t (zero (t + 1) hN)) =
        zero (t + 1) hN
      rw [iterate_zero_eq_mk (t + 1) hN t ht]
      exact cycleSucc_of_not_lt (t + 1) hN ⟨t, ht⟩ (Nat.lt_irrefl (t + 1))

/-- If `N` is a period at zero, every natural multiple of `N` is also a period. -/
theorem iterate_mul_period
    {α : Sort u} (step : α → α) (z : α) (N : ℕ)
    (hperiod : iterate step N z = z) :
    ∀ q : ℕ, iterate step (N * q) z = z
  | 0 => rfl
  | q + 1 => by
      change iterate step (N * q + N) z = z
      rw [iterate_add step (N * q) N z]
      rw [iterate_mul_period step z N hperiod q]
      exact hperiod

/-- Explicit power factorization along ordered depths. -/
theorem natPow_factor_of_le
    (b k m : ℕ) (hkm : k ≤ m) :
    ∃ q : ℕ, Nat.pow b m = Nat.pow b k * q := by
  induction hkm with
  | refl =>
      exact ⟨1, (Nat.mul_one (Nat.pow b k)).symm⟩
  | @step m hkm ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨q * b, ?_⟩
      change Nat.pow b m * b = Nat.pow b k * (q * b)
      rw [hq, Nat.mul_assoc]

/-- Canonical window at base `b`, depth `k`. -/
def WindowState (b k : ℕ) := Fin (Nat.pow b k)

/-- Canonical zero at a base/depth. -/
def windowZero (b k : ℕ) (hb : 0 < b) : WindowState b k :=
  zero (Nat.pow b k) (natPow_pos hb k)

/-- Canonical primitive successor at a base/depth. -/
def windowSuccessor
    (b k : ℕ) (hb : 0 < b) : WindowState b k → WindowState b k :=
  cycleSucc (Nat.pow b k) (natPow_pos hb k)

/-- Carry-through-depth is exact saturation of the finite capacity. -/
def carryAtDepth (b k : ℕ) (n : WindowState b k) : Prop :=
  carry (Nat.pow b k) n

/-- Window wrap is exactly carry. -/
theorem windowSuccessor_eq_zero_iff_carry
    (b k : ℕ) (hb : 0 < b) (n : WindowState b k) :
    windowSuccessor b k hb n = windowZero b k hb ↔
      carryAtDepth b k n :=
  cycleSucc_eq_zero_iff_carry (Nat.pow b k) (natPow_pos hb k) n

/-- Dynamic projection: run the lower cycle as many unit steps as the upper representative. -/
def depthProjection
    (b k m : ℕ) (hb : 0 < b) (n : WindowState b m) : WindowState b k :=
  iterate (windowSuccessor b k hb) n.val (windowZero b k hb)

/-- Dynamic projection preserves zero by computation. -/
theorem depthProjection_zero
    (b k m : ℕ) (hb : 0 < b) :
    depthProjection b k m hb (windowZero b m hb) = windowZero b k hb := rfl

/-- The lower cycle repeats across the full upper capacity whenever `k ≤ m`. -/
theorem lower_period_over_upper_capacity
    (b k m : ℕ) (hb : 0 < b) (hkm : k ≤ m) :
    iterate (windowSuccessor b k hb) (Nat.pow b m) (windowZero b k hb) =
      windowZero b k hb := by
  induction hkm with
  | refl =>
      exact iterate_period (Nat.pow b k) (natPow_pos hb k)
  | @step m hkm ih =>
      change iterate (windowSuccessor b k hb)
          (Nat.pow b m * b) (windowZero b k hb) = windowZero b k hb
      exact iterate_mul_period
        (windowSuccessor b k hb) (windowZero b k hb) (Nat.pow b m) ih b

/-- Dynamic projection commutes with unit successor. -/
theorem depthProjection_commutes_successor
    (b k m : ℕ) (hb : 0 < b) (hkm : k ≤ m)
    (n : WindowState b m) :
    depthProjection b k m hb (windowSuccessor b m hb n) =
      windowSuccessor b k hb (depthProjection b k m hb n) := by
  by_cases hnext : n.val + 1 < Nat.pow b m
  · have hs : windowSuccessor b m hb n = ⟨n.val + 1, hnext⟩ := by
      exact cycleSucc_of_lt (Nat.pow b m) (natPow_pos hb m) n hnext
    unfold depthProjection
    rw [hs]
    rfl
  · have hs : windowSuccessor b m hb n = windowZero b m hb := by
      exact cycleSucc_of_not_lt (Nat.pow b m) (natPow_pos hb m) n hnext
    have hboundary : n.val + 1 = Nat.pow b m := boundary_eq n hnext
    unfold depthProjection
    rw [hs]
    change windowZero b k hb =
      iterate (windowSuccessor b k hb) (n.val + 1) (windowZero b k hb)
    rw [hboundary, lower_period_over_upper_capacity b k m hb hkm]

/-- At equal depth, dynamic projection is pointwise identity. -/
theorem depthProjection_refl_pointwise
    (b k : ℕ) (hb : 0 < b) (n : WindowState b k) :
    depthProjection b k k hb n = n := by
  exact iterate_zero_eq_mk (Nat.pow b k) (natPow_pos hb k) n.val n.isLt

/-- Every zero-preserving successor-equivariant cross-depth map is forced pointwise. -/
theorem depthProjection_unique_pointwise
    (b k m : ℕ) (hb : 0 < b) (hkm : k ≤ m)
    (f : WindowState b m → WindowState b k)
    (hzero : f (windowZero b m hb) = windowZero b k hb)
    (hsucc : ∀ n : WindowState b m,
      f (windowSuccessor b m hb n) =
        windowSuccessor b k hb (f n)) :
    ∀ n : WindowState b m,
      f n = depthProjection b k m hb n := by
  have hmain : ∀ a : ℕ, ∀ ha : a < Nat.pow b m,
      f ⟨a, ha⟩ = depthProjection b k m hb ⟨a, ha⟩ := by
    intro a
    induction a with
    | zero =>
        intro ha
        exact hzero
    | succ a ih =>
        intro has
        have ha : a < Nat.pow b m := Nat.lt_trans (Nat.lt_succ_self a) has
        let x : WindowState b m := ⟨a, ha⟩
        have hxsucc : windowSuccessor b m hb x = ⟨a + 1, has⟩ := by
          exact cycleSucc_of_lt (Nat.pow b m) (natPow_pos hb m) x has
        calc
          f ⟨a + 1, has⟩ = f (windowSuccessor b m hb x) := by rw [hxsucc]
          _ = windowSuccessor b k hb (f x) := hsucc x
          _ = windowSuccessor b k hb (depthProjection b k m hb x) := by rw [ih ha]
          _ = depthProjection b k m hb (windowSuccessor b m hb x) :=
            (depthProjection_commutes_successor b k m hb hkm x).symm
          _ = depthProjection b k m hb ⟨a + 1, has⟩ := by rw [hxsucc]
  intro n
  exact hmain n.val n.isLt

/-- Projective composition follows from dynamical uniqueness, not modulo algebra. -/
theorem depthProjection_comp_pointwise
    (b j k m : ℕ) (hb : 0 < b)
    (hjk : j ≤ k) (hkm : k ≤ m)
    (n : WindowState b m) :
    depthProjection b j k hb (depthProjection b k m hb n) =
      depthProjection b j m hb n := by
  let f : WindowState b m → WindowState b j :=
    fun x => depthProjection b j k hb (depthProjection b k m hb x)
  have fzero : f (windowZero b m hb) = windowZero b j hb := by
    change depthProjection b j k hb
        (depthProjection b k m hb (windowZero b m hb)) = windowZero b j hb
    rw [depthProjection_zero, depthProjection_zero]
  have fsucc : ∀ x : WindowState b m,
      f (windowSuccessor b m hb x) = windowSuccessor b j hb (f x) := by
    intro x
    change depthProjection b j k hb
        (depthProjection b k m hb (windowSuccessor b m hb x)) = _
    rw [depthProjection_commutes_successor b k m hb hkm]
    exact depthProjection_commutes_successor b j k hb hjk (depthProjection b k m hb x)
  exact depthProjection_unique_pointwise b j m hb (Nat.le_trans hjk hkm) f fzero fsucc n

/-- Explicit exact finite code for one primitive window. -/
structure CodeWindow (b k : ℕ) (Code : Type u) where
  encode : WindowState b k → Code
  decode : Code → WindowState b k
  decode_encode : ∀ n : WindowState b k, decode (encode n) = n
  encode_decode : ∀ c : Code, encode (decode c) = c

namespace CodeWindow

variable {b k m : ℕ}
variable {Code : Type u} {Upper : Type u} {Lower : Type v}

/-- Encoder injectivity follows directly from the supplied decoder. -/
theorem encode_injective (rep : CodeWindow b k Code) : Function.Injective rep.encode := by
  intro x y h
  calc
    x = rep.decode (rep.encode x) := (rep.decode_encode x).symm
    _ = rep.decode (rep.encode y) := congrArg rep.decode h
    _ = y := rep.decode_encode y

/-- Code successor transported through the supplied exact codec. -/
def successor (rep : CodeWindow b k Code) (hb : 0 < b) : Code → Code :=
  fun c => rep.encode (windowSuccessor b k hb (rep.decode c))

/-- Encoded unit successor law. -/
theorem successor_encode
    (rep : CodeWindow b k Code) (hb : 0 < b) (n : WindowState b k) :
    rep.successor hb (rep.encode n) = rep.encode (windowSuccessor b k hb n) := by
  unfold successor
  rw [rep.decode_encode]

/-- Code wrap is exactly primitive carry. -/
theorem wrap_iff_carry
    (rep : CodeWindow b k Code) (hb : 0 < b) (n : WindowState b k) :
    rep.successor hb (rep.encode n) = rep.encode (windowZero b k hb) ↔
      carryAtDepth b k n := by
  rw [rep.successor_encode hb n]
  constructor
  · intro h
    exact (windowSuccessor_eq_zero_iff_carry b k hb n).1 (rep.encode_injective h)
  · intro h
    exact congrArg rep.encode ((windowSuccessor_eq_zero_iff_carry b k hb n).2 h)

/-- Residual dynamical projection transported through explicit codecs. -/
def projection
    (upper : CodeWindow b m Upper)
    (lower : CodeWindow b k Lower)
    (hb : 0 < b) : Upper → Lower :=
  fun c => lower.encode (depthProjection b k m hb (upper.decode c))

/-- Projection preserves encoded zero. -/
theorem projection_zero
    (upper : CodeWindow b m Upper)
    (lower : CodeWindow b k Lower)
    (hb : 0 < b) :
    projection upper lower hb (upper.encode (windowZero b m hb)) =
      lower.encode (windowZero b k hb) := by
  unfold projection
  rw [upper.decode_encode, depthProjection_zero]

/-- Projection commutes with code successor. -/
theorem projection_commutes_successor
    (upper : CodeWindow b m Upper)
    (lower : CodeWindow b k Lower)
    (hb : 0 < b) (hkm : k ≤ m) (c : Upper) :
    projection upper lower hb (upper.successor hb c) =
      lower.successor hb (projection upper lower hb c) := by
  unfold projection successor
  rw [upper.decode_encode, lower.decode_encode]
  exact congrArg lower.encode
    (depthProjection_commutes_successor b k m hb hkm (upper.decode c))

/-- Every coherent code map is forced pointwise. -/
theorem projection_unique_pointwise
    (upper : CodeWindow b m Upper)
    (lower : CodeWindow b k Lower)
    (hb : 0 < b) (hkm : k ≤ m)
    (f : Upper → Lower)
    (hzero : f (upper.encode (windowZero b m hb)) =
      lower.encode (windowZero b k hb))
    (hsucc : ∀ c : Upper,
      f (upper.successor hb c) = lower.successor hb (f c)) :
    ∀ c : Upper, f c = projection upper lower hb c := by
  let g : WindowState b m → WindowState b k :=
    fun n => lower.decode (f (upper.encode n))
  have gzero : g (windowZero b m hb) = windowZero b k hb := by
    change lower.decode (f (upper.encode (windowZero b m hb))) = windowZero b k hb
    rw [hzero, lower.decode_encode]
  have gsucc : ∀ n : WindowState b m,
      g (windowSuccessor b m hb n) = windowSuccessor b k hb (g n) := by
    intro n
    change lower.decode (f (upper.encode (windowSuccessor b m hb n))) = _
    rw [← upper.successor_encode hb n, hsucc]
    unfold successor
    rw [lower.decode_encode]
  have hg := depthProjection_unique_pointwise b k m hb hkm g gzero gsucc
  intro c
  have hp := hg (upper.decode c)
  have he := congrArg lower.encode hp
  calc
    f c = lower.encode (lower.decode (f c)) := (lower.encode_decode (f c)).symm
    _ = lower.encode (lower.decode (f (upper.encode (upper.decode c)))) := by
      rw [upper.encode_decode]
    _ = lower.encode (depthProjection b k m hb (upper.decode c)) := he
    _ = projection upper lower hb c := rfl

/-- Equal-depth code projection is pointwise identity. -/
theorem projection_refl_pointwise
    (rep : CodeWindow b k Code) (hb : 0 < b) (c : Code) :
    projection rep rep hb c = c := by
  unfold projection
  rw [depthProjection_refl_pointwise, rep.encode_decode]

/-- Code projections compose pointwise. -/
theorem projection_comp_pointwise
    {j : ℕ} {Low : Type v}
    (upper : CodeWindow b m Upper)
    (middle : CodeWindow b k Lower)
    (lower : CodeWindow b j Low)
    (hb : 0 < b) (hjk : j ≤ k) (hkm : k ≤ m) (c : Upper) :
    projection middle lower hb (projection upper middle hb c) =
      projection upper lower hb c := by
  unfold projection
  rw [middle.decode_encode]
  exact congrArg lower.encode
    (depthProjection_comp_pointwise b j k m hb hjk hkm (upper.decode c))

end CodeWindow

/-- Tower of explicit exact primitive-cycle codecs. -/
structure Tower (b : ℕ) where
  Code : ℕ → Type u
  level : ∀ k : ℕ, CodeWindow b k (Code k)

namespace Tower

variable {b : ℕ}

/-- Complete primitive projective carry-rigidity certificate. -/
structure Certificate (tower : Tower.{u} b) (hb : 0 < b) : Prop where
  successor_wrap : ∀ (k : ℕ) (n : WindowState b k),
    (tower.level k).successor hb ((tower.level k).encode n) =
        (tower.level k).encode (windowZero b k hb) ↔ carryAtDepth b k n
  projection_zero : ∀ (k m : ℕ) (hkm : k ≤ m),
    CodeWindow.projection (tower.level m) (tower.level k) hb
        ((tower.level m).encode (windowZero b m hb)) =
      (tower.level k).encode (windowZero b k hb)
  projection_successor : ∀ (k m : ℕ) (hkm : k ≤ m) (c : tower.Code m),
    CodeWindow.projection (tower.level m) (tower.level k) hb
        ((tower.level m).successor hb c) =
      (tower.level k).successor hb
        (CodeWindow.projection (tower.level m) (tower.level k) hb c)
  projection_unique : ∀ (k m : ℕ) (hkm : k ≤ m) (f : tower.Code m → tower.Code k),
    f ((tower.level m).encode (windowZero b m hb)) =
        (tower.level k).encode (windowZero b k hb) →
    (∀ c : tower.Code m,
      f ((tower.level m).successor hb c) = (tower.level k).successor hb (f c)) →
    ∀ c : tower.Code m,
      f c = CodeWindow.projection (tower.level m) (tower.level k) hb c
  projection_refl : ∀ (k : ℕ) (c : tower.Code k),
    CodeWindow.projection (tower.level k) (tower.level k) hb c = c
  projection_comp : ∀ (j k m : ℕ) (hjk : j ≤ k) (hkm : k ≤ m) (c : tower.Code m),
    CodeWindow.projection (tower.level k) (tower.level j) hb
        (CodeWindow.projection (tower.level m) (tower.level k) hb c) =
      CodeWindow.projection (tower.level m) (tower.level j) hb c

/-- Primitive constructive carry-collapse theorem. -/
theorem collapses_to_carry
    (tower : Tower.{u} b) (hb : 1 < b) :
    Certificate tower (lt_trans Nat.zero_lt_one hb) := by
  let hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  refine
    { successor_wrap := ?_
      projection_zero := ?_
      projection_successor := ?_
      projection_unique := ?_
      projection_refl := ?_
      projection_comp := ?_ }
  · intro k n
    exact (tower.level k).wrap_iff_carry hb0 n
  · intro k m hkm
    exact CodeWindow.projection_zero (tower.level m) (tower.level k) hb0
  · intro k m hkm c
    exact CodeWindow.projection_commutes_successor
      (tower.level m) (tower.level k) hb0 hkm c
  · intro k m hkm f hzero hsucc c
    exact CodeWindow.projection_unique_pointwise
      (tower.level m) (tower.level k) hb0 hkm f hzero hsucc c
  · intro k c
    exact CodeWindow.projection_refl_pointwise (tower.level k) hb0 c
  · intro j k m hjk hkm c
    exact CodeWindow.projection_comp_pointwise
      (tower.level m) (tower.level k) (tower.level j) hb0 hjk hkm c

end Tower
end PrimitiveCarry
end QuantityRepresentationFoundations