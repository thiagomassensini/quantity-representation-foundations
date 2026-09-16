import QuantityRepresentationFoundations.UniversalProjectiveCarryTower

/-!
# Axiom-free constructive carry rigidity

This module gives a kernel-facing constructive version of universal carry
rigidity for explicitly decodable finite quantity codes.

Two proof-engineering choices are essential:

* finite window sizes are written with the concrete natural operation
  `Nat.pow b k`, avoiding the generic `HPow` elaboration of `b ^ k`;
* every code level supplies explicit `encode` and `decode` maps with pointwise
  inverse laws, and all uniqueness statements are pointwise.

Thus no inverse is selected by `Classical.choice`, and no function equality is
needed through `funext`/quotient machinery.
-/

namespace QuantityRepresentationFoundations
namespace AxiomFreeCarry

universe u v

/-- Positivity of the explicit natural power. -/
theorem natPow_pos {b : ℕ} (hb : 0 < b) : ∀ k : ℕ, 0 < Nat.pow b k
  | 0 => Nat.zero_lt_succ 0
  | k + 1 => by
      change 0 < Nat.pow b k * b
      exact Nat.mul_pos (natPow_pos hb k) hb

/-- Zero state of the canonical depth-`k` window. -/
def windowZero (b k : ℕ) (hb : 0 < b) : Fin (Nat.pow b k) :=
  ⟨0, natPow_pos hb k⟩

/-- Cyclic unit successor on the canonical depth-`k` window. -/
def windowSuccessor
    (b k : ℕ) (hb : 0 < b) (n : Fin (Nat.pow b k)) :
    Fin (Nat.pow b k) :=
  ⟨(n.val + 1) % Nat.pow b k, Nat.mod_lt _ (natPow_pos hb k)⟩

/-- Carry through depth `k`, expressed as wrap modulo the full capacity. -/
def carryAtDepth (b k n : ℕ) : Prop :=
  (n + 1) % Nat.pow b k = 0

/-- Canonical wrap is exactly carry. -/
theorem windowSuccessor_eq_zero_iff_carry
    (b k : ℕ) (hb : 0 < b) (n : Fin (Nat.pow b k)) :
    windowSuccessor b k hb n = windowZero b k hb ↔
      carryAtDepth b k n.val := by
  constructor
  · intro h
    exact congrArg Fin.val h
  · intro h
    apply Fin.ext
    exact h

/-- A nonterminal representative increments without wrap. -/
theorem windowSuccessor_mk_of_succ_lt
    (b k a : ℕ) (hb : 0 < b)
    (ha : a < Nat.pow b k) (has : a + 1 < Nat.pow b k) :
    windowSuccessor b k hb ⟨a, ha⟩ = ⟨a + 1, has⟩ := by
  apply Fin.ext
  change (a + 1) % Nat.pow b k = a + 1
  exact Nat.mod_eq_of_lt has

/-- Lower explicit powers divide higher explicit powers. -/
theorem natPow_dvd_of_le
    (b k m : ℕ) (hkm : k ≤ m) :
    Nat.pow b k ∣ Nat.pow b m := by
  induction hkm with
  | refl => exact dvd_refl _
  | @step m hkm ih =>
      change Nat.pow b k ∣ Nat.pow b m * b
      exact dvd_mul_of_dvd_left ih b

/-- Canonical residual projection from depth `m` to depth `k`. -/
def depthProjection
    (b k m : ℕ) (hb : 0 < b) :
    Fin (Nat.pow b m) → Fin (Nat.pow b k) :=
  fun n => ⟨n.val % Nat.pow b k, Nat.mod_lt _ (natPow_pos hb k)⟩

/-- Residual projection preserves zero. -/
theorem depthProjection_zero
    (b k m : ℕ) (hb : 0 < b) :
    depthProjection b k m hb (windowZero b m hb) = windowZero b k hb := by
  apply Fin.ext
  exact Nat.zero_mod (Nat.pow b k)

/-- Residual projection commutes with successor whenever `k ≤ m`. -/
theorem depthProjection_commutes_successor
    (b k m : ℕ) (hb : 0 < b) (hkm : k ≤ m)
    (n : Fin (Nat.pow b m)) :
    depthProjection b k m hb (windowSuccessor b m hb n) =
      windowSuccessor b k hb (depthProjection b k m hb n) := by
  apply Fin.ext
  change
    (((n.val + 1) % Nat.pow b m) % Nat.pow b k) =
      (((n.val % Nat.pow b k) + 1) % Nat.pow b k)
  rw [Nat.mod_mod_of_dvd _ (natPow_dvd_of_le b k m hkm)]
  exact (Nat.mod_add_mod n.val (Nat.pow b k) 1).symm

/-- Equal-depth projection is pointwise identity. -/
theorem depthProjection_refl_pointwise
    (b k : ℕ) (hb : 0 < b) (n : Fin (Nat.pow b k)) :
    depthProjection b k k hb n = n := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt n.isLt

/-- Residual projections compose transitively. -/
theorem depthProjection_comp
    (b j k m : ℕ) (hb : 0 < b)
    (hjk : j ≤ k) (hkm : k ≤ m)
    (n : Fin (Nat.pow b m)) :
    depthProjection b j k hb (depthProjection b k m hb n) =
      depthProjection b j m hb n := by
  apply Fin.ext
  change (n.val % Nat.pow b k) % Nat.pow b j = n.val % Nat.pow b j
  exact Nat.mod_mod_of_dvd _ (natPow_dvd_of_le b j k hjk)

/-- Every zero-preserving successor-equivariant map is residual reduction, pointwise. -/
theorem depthProjection_unique_pointwise
    (b k m : ℕ) (hb : 0 < b) (hkm : k ≤ m)
    (f : Fin (Nat.pow b m) → Fin (Nat.pow b k))
    (hzero : f (windowZero b m hb) = windowZero b k hb)
    (hsucc : ∀ n : Fin (Nat.pow b m),
      f (windowSuccessor b m hb n) =
        windowSuccessor b k hb (f n)) :
    ∀ n : Fin (Nat.pow b m), f n = depthProjection b k m hb n := by
  have hmain : ∀ a : ℕ, ∀ ha : a < Nat.pow b m,
      f ⟨a, ha⟩ = depthProjection b k m hb ⟨a, ha⟩ := by
    intro a
    induction a with
    | zero =>
        intro ha
        exact hzero
    | succ a ih =>
        intro has
        have ha : a < Nat.pow b m := Nat.lt_of_succ_lt has
        let x : Fin (Nat.pow b m) := ⟨a, ha⟩
        have hxsucc : windowSuccessor b m hb x = ⟨a + 1, has⟩ := by
          exact windowSuccessor_mk_of_succ_lt b m a hb ha has
        calc
          f ⟨a + 1, has⟩ = f (windowSuccessor b m hb x) := by rw [hxsucc]
          _ = windowSuccessor b k hb (f x) := hsucc x
          _ = windowSuccessor b k hb (depthProjection b k m hb x) := by rw [ih ha]
          _ = depthProjection b k m hb (windowSuccessor b m hb x) :=
            (depthProjection_commutes_successor b k m hb hkm x).symm
          _ = depthProjection b k m hb ⟨a + 1, has⟩ := by rw [hxsucc]
  intro n
  exact hmain n.val n.isLt

/-- Exact finite quantity codec with an explicit two-sided inverse. -/
structure Window (b k : ℕ) (Code : Type u) where
  encode : Fin (Nat.pow b k) → Code
  decode : Code → Fin (Nat.pow b k)
  decode_encode_law : ∀ n : Fin (Nat.pow b k), decode (encode n) = n
  encode_decode_law : ∀ c : Code, encode (decode c) = c

namespace Window

variable {b k m : ℕ}
variable {Code : Type u} {CodeUpper : Type u} {CodeLower : Type v}

@[simp] theorem decode_encode
    (rep : Window b k Code) (n : Fin (Nat.pow b k)) :
    rep.decode (rep.encode n) = n := rep.decode_encode_law n

@[simp] theorem encode_decode
    (rep : Window b k Code) (c : Code) :
    rep.encode (rep.decode c) = c := rep.encode_decode_law c

/-- Encoder injectivity is constructive from the explicit decoder. -/
theorem encode_injective (rep : Window b k Code) : Function.Injective rep.encode := by
  intro x y h
  calc
    x = rep.decode (rep.encode x) := (rep.decode_encode x).symm
    _ = rep.decode (rep.encode y) := congrArg rep.decode h
    _ = y := rep.decode_encode y

/-- Successor transported through the explicit codec. -/
def successor (rep : Window b k Code) (hb : 0 < b) : Code → Code :=
  fun c => rep.encode (windowSuccessor b k hb (rep.decode c))

@[simp] theorem successor_encode
    (rep : Window b k Code) (hb : 0 < b) (n : Fin (Nat.pow b k)) :
    rep.successor hb (rep.encode n) = rep.encode (windowSuccessor b k hb n) := by
  unfold successor
  rw [rep.decode_encode]

/-- Every code wraps exactly on the carry event. -/
theorem wrap_iff_carry
    (rep : Window b k Code) (hb : 0 < b) (n : Fin (Nat.pow b k)) :
    rep.successor hb (rep.encode n) = rep.encode (windowZero b k hb) ↔
      carryAtDepth b k n.val := by
  rw [rep.successor_encode hb n]
  constructor
  · intro h
    exact (windowSuccessor_eq_zero_iff_carry b k hb n).1 (rep.encode_injective h)
  · intro h
    exact congrArg rep.encode ((windowSuccessor_eq_zero_iff_carry b k hb n).2 h)

/-- Any exact successor implementation is forced pointwise. -/
theorem exact_successor_unique_pointwise
    (rep : Window b k Code)
    (hb : 0 < b)
    (step : Code → Code)
    (hstep : ∀ n : Fin (Nat.pow b k),
      step (rep.encode n) = rep.encode (windowSuccessor b k hb n)) :
    ∀ c : Code, step c = rep.successor hb c := by
  intro c
  calc
    step c = step (rep.encode (rep.decode c)) := congrArg step (rep.encode_decode c).symm
    _ = rep.encode (windowSuccessor b k hb (rep.decode c)) := hstep (rep.decode c)
    _ = rep.successor hb c := rfl

/-- Residual projection transported through explicit codecs. -/
def projection
    (upper : Window b m CodeUpper)
    (lower : Window b k CodeLower)
    (hb : 0 < b) : CodeUpper → CodeLower :=
  fun c => lower.encode (depthProjection b k m hb (upper.decode c))

@[simp] theorem projection_encode
    (upper : Window b m CodeUpper)
    (lower : Window b k CodeLower)
    (hb : 0 < b) (n : Fin (Nat.pow b m)) :
    projection upper lower hb (upper.encode n) =
      lower.encode (depthProjection b k m hb n) := by
  unfold projection
  rw [upper.decode_encode]

/-- Explicit projection preserves represented zero. -/
theorem projection_zero
    (upper : Window b m CodeUpper)
    (lower : Window b k CodeLower)
    (hb : 0 < b) :
    projection upper lower hb (upper.encode (windowZero b m hb)) =
      lower.encode (windowZero b k hb) := by
  rw [projection_encode]
  exact congrArg lower.encode (depthProjection_zero b k m hb)

/-- Explicit projection commutes with exact successor. -/
theorem projection_commutes_successor
    (upper : Window b m CodeUpper)
    (lower : Window b k CodeLower)
    (hb : 0 < b) (hkm : k ≤ m)
    (c : CodeUpper) :
    projection upper lower hb (upper.successor hb c) =
      lower.successor hb (projection upper lower hb c) := by
  unfold projection successor
  rw [upper.decode_encode, lower.decode_encode]
  exact congrArg lower.encode
    (depthProjection_commutes_successor b k m hb hkm (upper.decode c))

/-- Every coherent cross-depth code map is forced pointwise. -/
theorem projection_unique_pointwise
    (upper : Window b m CodeUpper)
    (lower : Window b k CodeLower)
    (hb : 0 < b) (hkm : k ≤ m)
    (f : CodeUpper → CodeLower)
    (hzero : f (upper.encode (windowZero b m hb)) =
      lower.encode (windowZero b k hb))
    (hsucc : ∀ c : CodeUpper,
      f (upper.successor hb c) = lower.successor hb (f c)) :
    ∀ c : CodeUpper, f c = projection upper lower hb c := by
  let g : Fin (Nat.pow b m) → Fin (Nat.pow b k) :=
    fun n => lower.decode (f (upper.encode n))
  have gzero : g (windowZero b m hb) = windowZero b k hb := by
    change lower.decode (f (upper.encode (windowZero b m hb))) = windowZero b k hb
    rw [hzero, lower.decode_encode]
  have gsucc : ∀ n : Fin (Nat.pow b m),
      g (windowSuccessor b m hb n) = windowSuccessor b k hb (g n) := by
    intro n
    change lower.decode (f (upper.encode (windowSuccessor b m hb n))) = _
    rw [← upper.successor_encode hb n, hsucc]
    unfold successor
    rw [lower.decode_encode]
  have hg := depthProjection_unique_pointwise b k m hb hkm g gzero gsucc
  intro c
  have hpoint := hg (upper.decode c)
  have hencoded := congrArg lower.encode hpoint
  calc
    f c = lower.encode (lower.decode (f c)) := (lower.encode_decode (f c)).symm
    _ = lower.encode (lower.decode (f (upper.encode (upper.decode c)))) := by
      rw [upper.encode_decode]
    _ = lower.encode (depthProjection b k m hb (upper.decode c)) := hencoded
    _ = projection upper lower hb c := rfl

/-- Equal-depth projection is pointwise identity. -/
theorem projection_refl_pointwise
    (rep : Window b k Code) (hb : 0 < b) (c : Code) :
    projection rep rep hb c = c := by
  calc
    projection rep rep hb c =
        rep.encode (depthProjection b k k hb (rep.decode c)) := rfl
    _ = rep.encode (rep.decode c) :=
      congrArg rep.encode (depthProjection_refl_pointwise b k hb (rep.decode c))
    _ = c := rep.encode_decode c

/-- Projective composition law, pointwise. -/
theorem projection_comp_pointwise
    {j : ℕ} {CodeJ : Type v}
    (upper : Window b m CodeUpper)
    (middle : Window b k CodeLower)
    (lower : Window b j CodeJ)
    (hb : 0 < b) (hjk : j ≤ k) (hkm : k ≤ m)
    (c : CodeUpper) :
    projection middle lower hb (projection upper middle hb c) =
      projection upper lower hb c := by
  unfold projection
  rw [middle.decode_encode]
  exact congrArg lower.encode
    (depthProjection_comp b j k m hb hjk hkm (upper.decode c))

end Window

/-- Tower of explicit exact finite codecs. -/
structure Tower (b : ℕ) where
  Code : ℕ → Type u
  level : ∀ k : ℕ, Window b k (Code k)

namespace Tower

variable {b : ℕ}

/-- Complete constructive, pointwise carry-rigidity certificate. -/
structure Certificate (tower : Tower.{u} b) (hb : 0 < b) : Prop where
  successor_wrap : ∀ (k : ℕ) (n : Fin (Nat.pow b k)),
    (tower.level k).successor hb ((tower.level k).encode n) =
        (tower.level k).encode (windowZero b k hb) ↔
      carryAtDepth b k n.val
  projection_zero : ∀ (k m : ℕ) (hkm : k ≤ m),
    Window.projection (tower.level m) (tower.level k) hb
        ((tower.level m).encode (windowZero b m hb)) =
      (tower.level k).encode (windowZero b k hb)
  projection_successor : ∀ (k m : ℕ) (hkm : k ≤ m) (c : tower.Code m),
    Window.projection (tower.level m) (tower.level k) hb
        ((tower.level m).successor hb c) =
      (tower.level k).successor hb
        (Window.projection (tower.level m) (tower.level k) hb c)
  projection_unique_pointwise : ∀ (k m : ℕ) (hkm : k ≤ m)
      (f : tower.Code m → tower.Code k),
    f ((tower.level m).encode (windowZero b m hb)) =
        (tower.level k).encode (windowZero b k hb) →
    (∀ c : tower.Code m,
      f ((tower.level m).successor hb c) =
        (tower.level k).successor hb (f c)) →
    ∀ c : tower.Code m,
      f c = Window.projection (tower.level m) (tower.level k) hb c
  projection_refl_pointwise : ∀ (k : ℕ) (c : tower.Code k),
    Window.projection (tower.level k) (tower.level k) hb c = c
  projection_comp_pointwise : ∀ (j k m : ℕ)
      (hjk : j ≤ k) (hkm : k ≤ m) (c : tower.Code m),
    Window.projection (tower.level k) (tower.level j) hb
        (Window.projection (tower.level m) (tower.level k) hb c) =
      Window.projection (tower.level m) (tower.level j) hb c

/-- Axiom-free constructive carry-rigidity capstone. -/
theorem collapses_to_carry
    (tower : Tower.{u} b) (hb : 1 < b) :
    Certificate tower (lt_trans Nat.zero_lt_one hb) := by
  let hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  refine
    { successor_wrap := ?_
      projection_zero := ?_
      projection_successor := ?_
      projection_unique_pointwise := ?_
      projection_refl_pointwise := ?_
      projection_comp_pointwise := ?_ }
  · intro k n
    exact (tower.level k).wrap_iff_carry hb0 n
  · intro k m hkm
    exact Window.projection_zero (tower.level m) (tower.level k) hb0
  · intro k m hkm c
    exact Window.projection_commutes_successor
      (tower.level m) (tower.level k) hb0 hkm c
  · intro k m hkm f hzero hsucc c
    exact Window.projection_unique_pointwise
      (tower.level m) (tower.level k) hb0 hkm f hzero hsucc c
  · intro k c
    exact Window.projection_refl_pointwise (tower.level k) hb0 c
  · intro j k m hjk hkm c
    exact Window.projection_comp_pointwise
      (tower.level m) (tower.level k) (tower.level j) hb0 hjk hkm c

end Tower
end AxiomFreeCarry
end QuantityRepresentationFoundations
