import GaloisForLFunctions.HTGeometry.OrbitBalance
import GaloisForLFunctions.HTGeometry.ArchimedeanCorank

/-!
# The two-face `F₁` criterion: flow-imbalance ⊕ multiplier-corank

The obstruction to a single base / single Frobenius splits into two invariants of the scaling
structure, which this file packages over the two algebraic layers the corpus already owns:

* the **flow-imbalance** face — the global orbit degree of the shift-multiplier divisor
  (`OrbitBalance`);
* the **multiplier-corank** face — the rational rank of the multiplier value group
  (`ArchimedeanCorank`).

A single Frobenius is an automorphism, so its multiplier divisor is a shift coboundary — no
one-sided imbalance — and it generates a rank-one value group.  Both faces are therefore trivial
whenever one exists.  Over a function field both are trivial: divisor zero and value group `⟨log q⟩`.
Over `ℚ` **both** fail: the archimedean `Γ` multiplier carries a single point mass, so its orbit
degree is `1`, and the prime-log value group has rank the cardinality of the primes.

The two faces are logically independent: all four combinations of (imbalance zero or not) and
(rank one or infinite) are realized.

Only the **necessity** direction of the criterion is formalized, which is exactly the proven content
of the card; sufficiency (the construction of the absolute object) is the open frontier and is not
claimed here.

## Main results

* `SingleFrobenius.flowImbalance_eq_zero`, `SingleFrobenius.rank_le_one` — necessity;
* `functionFieldDatum_singleFrobenius` — over `F_q` both faces are trivial;
* `not_singleFrobenius_of_flowImbalance_ne_zero`,
  `not_singleFrobenius_of_one_lt_rank` — the two independent obstructions;
* `not_singleFrobenius_rationalDatum` — over `ℚ` no single Frobenius, on either face;
* `flowImbalance_corank_independent` — the four-way orthogonality realization.
-/

noncomputable section

namespace GaloisForLFunctions

namespace F1TwoFace

open scoped Cardinal

private theorem rank_span_singleton_le_one (x : ℝ) :
    Module.rank ℚ (Submodule.span ℚ ({x} : Set ℝ)) ≤ 1 := by
  have h := rank_span_le (R := ℚ) (M := ℝ) ({x} : Set ℝ)
  simpa using h

private theorem rank_span_singleton_eq_one {x : ℝ} (hx : x ≠ 0) :
    Module.rank ℚ (Submodule.span ℚ ({x} : Set ℝ)) = 1 := by
  refine le_antisymm (rank_span_singleton_le_one x) ?_
  have hmem : x ∈ Submodule.span ℚ ({x} : Set ℝ) := Submodule.mem_span_singleton_self x
  have hnt : Nontrivial (Submodule.span ℚ ({x} : Set ℝ)) := by
    refine ⟨⟨⟨x, hmem⟩, 0, ?_⟩⟩
    intro h
    exact hx (congrArg Subtype.val h)
  have hpos : 0 < Module.rank ℚ (Submodule.span ℚ ({x} : Set ℝ)) := rank_pos
  exact Cardinal.one_le_iff_pos.mpr hpos

private theorem infinite_natPrimes : Infinite Nat.Primes :=
  Nat.infinite_setOf_prime.to_subtype


/-- The two-face datum of a scaling structure: the divisor of its shift multiplier on one orbit,
and the `ℚ`-span of the logarithms of its multiplier value group. -/
structure PlaceDatum where
  /-- Divisor of the scaling multiplier on one shift orbit. -/
  multiplierDivisor : ℤ →₀ ℤ
  /-- Rational span of the logarithmic multiplier value group. -/
  valueGroup : Submodule ℚ ℝ

/-- **The flow face.**  The global orbit degree of the multiplier divisor. -/
def PlaceDatum.flowImbalance (P : PlaceDatum) : ℤ :=
  orbitDegree P.multiplierDivisor

/-- **The corank face.**  The rational rank of the multiplier value group. -/
def PlaceDatum.corank (P : PlaceDatum) : Cardinal :=
  Module.rank ℚ P.valueGroup

/-- **A single Frobenius.**  It is an automorphism, so its multiplier divisor is a shift
coboundary; and it generates the value group, so the value group is monogenic. -/
structure SingleFrobenius (P : PlaceDatum) : Prop where
  /-- No one-sided imbalance: the multiplier divisor telescopes. -/
  coboundary : ∃ E : ℤ →₀ ℤ, P.multiplierDivisor = intShiftCoboundary E
  /-- One generator: the value group is spanned by a single element. -/
  monogenic : ∃ x : ℝ, P.valueGroup = Submodule.span ℚ {x}

/-! ### Necessity -/

/-- **Necessity, flow face.**  A single Frobenius has zero flow imbalance. -/
theorem SingleFrobenius.flowImbalance_eq_zero {P : PlaceDatum} (h : SingleFrobenius P) :
    P.flowImbalance = 0 := by
  obtain ⟨E, hE⟩ := h.coboundary
  rw [PlaceDatum.flowImbalance, hE, orbitDegree_intShiftCoboundary]

/-- **Necessity, corank face.**  A single Frobenius has value-group rank at most one. -/
theorem SingleFrobenius.rank_le_one {P : PlaceDatum} (h : SingleFrobenius P) :
    P.corank ≤ 1 := by
  obtain ⟨x, hx⟩ := h.monogenic
  rw [PlaceDatum.corank, hx]
  exact rank_span_singleton_le_one x

/-! ### The two obstructions -/

/-- **The flow obstruction.**  A nonzero flow imbalance forbids a single Frobenius. -/
theorem not_singleFrobenius_of_flowImbalance_ne_zero {P : PlaceDatum}
    (h : P.flowImbalance ≠ 0) : ¬ SingleFrobenius P :=
  fun hF => h hF.flowImbalance_eq_zero

/-- **The corank obstruction.**  A value group of rank above one forbids a single Frobenius. -/
theorem not_singleFrobenius_of_one_lt_rank {P : PlaceDatum}
    (h : 1 < P.corank) : ¬ SingleFrobenius P :=
  fun hF => absurd hF.rank_le_one (not_le.mpr h)

/-! ### The function-field place: both faces trivial -/

/-- The function-field datum: the scaling multiplier is a unit, so its divisor vanishes, and the
value group is generated by the single Frobenius weight `log q`. -/
def functionFieldDatum (q : ℕ) : PlaceDatum where
  multiplierDivisor := 0
  valueGroup := Submodule.span ℚ {Real.log (q : ℝ)}

@[simp]
theorem functionFieldDatum_flowImbalance (q : ℕ) :
    (functionFieldDatum q).flowImbalance = 0 := by
  rw [PlaceDatum.flowImbalance, functionFieldDatum, orbitDegree_zero]

/-- **Over `F_q` a single Frobenius exists on both faces.** -/
theorem functionFieldDatum_singleFrobenius (q : ℕ) :
    SingleFrobenius (functionFieldDatum q) where
  coboundary := ⟨0, by simp [functionFieldDatum, intShiftCoboundary]⟩
  monogenic := ⟨Real.log (q : ℝ), rfl⟩

/-- The function-field corank is exactly one whenever the Frobenius weight is nontrivial. -/
theorem functionFieldDatum_corank (q : ℕ) (hq : 1 < q) :
    (functionFieldDatum q).corank = 1 := by
  have hlog : Real.log (q : ℝ) ≠ 0 := by
    have h1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact ne_of_gt (Real.log_pos h1)
  rw [PlaceDatum.corank, functionFieldDatum]
  exact rank_span_singleton_eq_one hlog

/-! ### The rational place: both faces fail -/

/-- The rational datum: the archimedean `Γ` multiplier carries a single point mass on its orbit,
and the multiplier value group is the full prime-log span. -/
def rationalDatum : PlaceDatum where
  multiplierDivisor := Finsupp.single 0 1
  valueGroup := primeLogFullSpan

/-- **The flow face over `ℚ` is `+1`.**  The archimedean `Γ` orbit is one-sided. -/
@[simp]
theorem rationalDatum_flowImbalance : rationalDatum.flowImbalance = 1 := by
  rw [PlaceDatum.flowImbalance, rationalDatum, orbitDegree_single]

/-- **The corank face over `ℚ` is the cardinality of the primes.** -/
theorem rationalDatum_corank : rationalDatum.corank = Cardinal.mk Nat.Primes := by
  rw [PlaceDatum.corank, rationalDatum]
  exact primeLogFullSpan_rank

/-- The rational corank is strictly above one: the prime-log value group is not monogenic. -/
theorem one_lt_rationalDatum_corank : 1 < rationalDatum.corank := by
  rw [rationalDatum_corank]
  haveI : Infinite Nat.Primes := infinite_natPrimes
  exact lt_of_lt_of_le Cardinal.one_lt_aleph0 (Cardinal.aleph0_le_mk Nat.Primes)

/-- **No single Frobenius over `ℚ`, from the flow face alone.** -/
theorem not_singleFrobenius_rationalDatum_flow : ¬ SingleFrobenius rationalDatum :=
  not_singleFrobenius_of_flowImbalance_ne_zero (by simp)

/-- **No single Frobenius over `ℚ`, from the corank face alone.**  The two obstructions are
independent, so either one suffices. -/
theorem not_singleFrobenius_rationalDatum_corank : ¬ SingleFrobenius rationalDatum :=
  not_singleFrobenius_of_one_lt_rank one_lt_rationalDatum_corank

/-! ### Orthogonality of the two faces -/

/-- Datum with trivial flow face and infinite corank. -/
def flowZeroCorankInfinite : PlaceDatum where
  multiplierDivisor := 0
  valueGroup := primeLogFullSpan

/-- Datum with nontrivial flow face and rank-one corank. -/
def flowOneCorankOne : PlaceDatum where
  multiplierDivisor := Finsupp.single 0 1
  valueGroup := Submodule.span ℚ {Real.log 2}

/-- **The two faces are logically independent.**  All four combinations of a vanishing or
nonvanishing flow imbalance with a rank-one or infinite corank occur. -/
theorem flowImbalance_corank_independent :
    (functionFieldDatum 2).flowImbalance = 0 ∧ (functionFieldDatum 2).corank = 1 ∧
    flowZeroCorankInfinite.flowImbalance = 0 ∧
      flowZeroCorankInfinite.corank = Cardinal.mk Nat.Primes ∧
    flowOneCorankOne.flowImbalance = 1 ∧ flowOneCorankOne.corank = 1 ∧
    rationalDatum.flowImbalance = 1 ∧ rationalDatum.corank = Cardinal.mk Nat.Primes := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := by
    have : (1 : ℝ) < 2 := by norm_num
    exact ne_of_gt (Real.log_pos this)
  refine ⟨functionFieldDatum_flowImbalance 2, functionFieldDatum_corank 2 (by norm_num), ?_, ?_,
    ?_, ?_, rationalDatum_flowImbalance, rationalDatum_corank⟩
  · rw [PlaceDatum.flowImbalance, flowZeroCorankInfinite, orbitDegree_zero]
  · rw [PlaceDatum.corank, flowZeroCorankInfinite]
    exact primeLogFullSpan_rank
  · rw [PlaceDatum.flowImbalance, flowOneCorankOne, orbitDegree_single]
  · rw [PlaceDatum.corank, flowOneCorankOne]
    exact rank_span_singleton_eq_one hlog2

end F1TwoFace

end GaloisForLFunctions
