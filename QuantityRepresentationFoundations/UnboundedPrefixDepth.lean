import QuantityRepresentationFoundations.UnboundedExtension

/-!
# Information beyond every finite prefix

This module introduces an explicitly layered representation architecture while
remaining pre-positional.

Each level may have its own finite state type.  A global state is an infinite
sequence of such finite layers.  We do not assume a base, digits, arithmetic
weights, quotient, remainder, division, modulo, normalization, or carry.

The result is stronger than fixed-depth impossibility: for every finite cutoff,
there are distinct source states that agree on every layer below the cutoff.
If the full layered encoding is faithful, those source states must differ at
some layer at or beyond the cutoff.

Thus, within any countably layered finite-state architecture, quantitative
distinguishability is forced to persist to arbitrarily large depth.

This still does not prove transport between successive levels.  That requires
an additional operational/locality principle and is intentionally deferred.
-/

namespace QuantityRepresentationFoundations

/-- The finite prefix of a layered state, keeping exactly the layers below `depth`. -/
def prefixState
    {Layer : ℕ → Type*}
    (depth : ℕ)
    (state : ∀ n, Layer n) :
    (i : Fin depth) → Layer i.1 :=
  fun i => state i.1

/-- Two source states agree through every layer strictly below `depth`. -/
def AgreeBelow
    {Q : Type*} {Layer : ℕ → Type*}
    (encode : Q → ∀ n, Layer n)
    (depth : ℕ) (q₁ q₂ : Q) : Prop :=
  ∀ n, n < depth → encode q₁ n = encode q₂ n

/--
No finite prefix of finite layers can be faithful on an infinite source.
-/
theorem finitePrefix_obstructs_faithfulness
    {Q : Type*} [Infinite Q]
    (Layer : ℕ → Type*) [∀ n, Finite (Layer n)]
    (encode : Q → ∀ n, Layer n)
    (depth : ℕ) :
    ¬ FaithfulRepresentation (fun q => prefixState depth (encode q)) := by
  exact finiteState_obstructs_faithfulRepresentation
    (fun q => prefixState depth (encode q))

/--
For every finite cutoff, two distinct source states are indistinguishable on
all layers below that cutoff.
-/
theorem finitePrefix_forces_collision
    {Q : Type*} [Infinite Q]
    (Layer : ℕ → Type*) [∀ n, Finite (Layer n)]
    (encode : Q → ∀ n, Layer n)
    (depth : ℕ) :
    ∃ q₁ q₂ : Q,
      q₁ ≠ q₂ ∧ AgreeBelow encode depth q₁ q₂ := by
  obtain ⟨q₁, q₂, hne, hprefix⟩ :=
    finiteState_forces_collision (fun q => prefixState depth (encode q))
  refine ⟨q₁, q₂, hne, ?_⟩
  intro n hn
  exact congrFun hprefix ⟨n, hn⟩

/--
If the complete layered representation is faithful, then after every finite
cutoff there are distinct source states that agree below the cutoff but differ
at some layer at or beyond it.

This is the formal `new information must occur arbitrarily deep` theorem.
-/
theorem faithfulLayeredEncoding_forces_late_difference
    {Q : Type*} [Infinite Q]
    (Layer : ℕ → Type*) [∀ n, Finite (Layer n)]
    (encode : Q → ∀ n, Layer n)
    (hfaithful : FaithfulRepresentation encode)
    (depth : ℕ) :
    ∃ q₁ q₂ : Q,
      q₁ ≠ q₂ ∧
      AgreeBelow encode depth q₁ q₂ ∧
      ∃ n, depth ≤ n ∧ encode q₁ n ≠ encode q₂ n := by
  obtain ⟨q₁, q₂, hne, hagree⟩ :=
    finitePrefix_forces_collision Layer encode depth
  refine ⟨q₁, q₂, hne, hagree, ?_⟩
  by_contra hlate
  apply hne
  apply hfaithful
  funext n
  by_cases hn : n < depth
  · exact hagree n hn
  · have hge : depth ≤ n := Nat.le_of_not_gt hn
    by_contra hdiff
    exact hlate ⟨n, hge, hdiff⟩

/--
Universal form: a faithful infinite layered encoding contains distinguishing
information beyond every finite depth.
-/
theorem faithfulLayeredEncoding_has_arbitrarily_late_information
    {Q : Type*} [Infinite Q]
    (Layer : ℕ → Type*) [∀ n, Finite (Layer n)]
    (encode : Q → ∀ n, Layer n)
    (hfaithful : FaithfulRepresentation encode) :
    ∀ depth : ℕ,
      ∃ q₁ q₂ : Q,
        q₁ ≠ q₂ ∧
        AgreeBelow encode depth q₁ q₂ ∧
        ∃ n, depth ≤ n ∧ encode q₁ n ≠ encode q₂ n := by
  intro depth
  exact faithfulLayeredEncoding_forces_late_difference
    Layer encode hfaithful depth

end QuantityRepresentationFoundations
