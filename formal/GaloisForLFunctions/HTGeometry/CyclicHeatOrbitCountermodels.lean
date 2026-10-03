import GaloisForLFunctions.HTGeometry.CyclicHeatOrbitAtomicWall

/-!
# Sharp countermodels for the cyclic heat-orbit selection law

* **Properness cannot be omitted (OG.36)–(OG.37).**  The coordinate projections
  `R_n = |e_{j_n}⟩⟨e_{j_n}|` have `tr R_n = 1`, `[R_n, D] = 0` and `‖[R_n, P]‖₁ ≤ 2|v_{j_n}| ‖v‖ → 0`;
  selection therefore forces `E_G(R_n) → ∞`.
* **Full support is load-bearing.**  If `v_j = 0`, then `G e_j = 0` and the non-scalar
  projection `|e_j⟩⟨e_j|` commutes with `D` and `P`.
* **Simple spectrum is load-bearing.**  If `λ_i = λ_j` for `i ≠ j` and `v_i ≠ 0`, the vector
  `w = v̄_j e_i - v̄_i e_j` is invisible to the heat orbit, `G w = 0`, and the non-scalar
  `|w⟩⟨w|` commutes with `D` and `P`.
* **The spectral gap is load-bearing.**  If some `λ_{j₀} = 0` with `v_{j₀} ≠ 0`, then
  `‖S_t v‖² ≥ |v_{j₀}|²` and the orbit integrand is not integrable.
* **Infinite dimension is load-bearing.**  On a finite index set `G` is invertible and the scalar
  density `|ι|^{-1}·1` is a positive, normalized, source-invariant defect of finite cost.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {ι : Type*}

local notation "ℓ²ι" => lp (fun _ : ι => ℂ) 2

/-- The coordinate projection `|e_j⟩⟨e_j|`. -/
def lpCoordProjection [DecidableEq ι] (j : ι) : ℓ²ι →L[ℂ] ℓ²ι :=
  InnerProductSpace.rankOne ℂ (lp.single 2 j (1 : ℂ)) (lp.single 2 j (1 : ℂ))

theorem norm_lpSingle_one [DecidableEq ι] (j : ι) : ‖(lp.single 2 j (1 : ℂ) : ℓ²ι)‖ = 1 := by
  rw [lp.norm_single (by norm_num), norm_one]

theorem lpCoordProjection_apply [DecidableEq ι] (j : ι) (x : ℓ²ι) :
    lpCoordProjection j x = x j • (lp.single 2 j (1 : ℂ) : ℓ²ι) := by
  rw [lpCoordProjection, InnerProductSpace.rankOne_apply, inner_single_one_left]

theorem isPositive_lpCoordProjection [DecidableEq ι] (j : ι) : (lpCoordProjection (ι := ι) j).IsPositive :=
  InnerProductSpace.isPositive_rankOne_self _

theorem memSchattenClass_lpCoordProjection [DecidableEq ι] (j : ι) :
    MemSchattenClass 1 (lpCoordProjection (ι := ι) j) :=
  (rankOneSchattenOne (lp.single 2 j (1 : ℂ) : ℓ²ι) (lp.single 2 j (1 : ℂ))).property

/-- **(OG.36)** `tr R_j = ‖R_j‖₁ = 1`. -/
theorem traceNorm_lpCoordProjection [DecidableEq ι] (j : ι) : traceNorm ℓ²ι (lpCoordProjection j) = 1 := by
  have h := norm_rankOneSchattenOne (lp.single 2 j (1 : ℂ) : ℓ²ι) (lp.single 2 j (1 : ℂ))
  rw [SchattenOneOperator.norm_def, rankOneSchattenOne_coe, norm_lpSingle_one, one_mul] at h
  exact h

namespace HeatSource

variable (s : HeatSource ι) [DecidableEq ι]

/-- **(OG.36)** `[R_j, D] = 0`. -/
theorem lpCoordProjection_commutator_heatReporter (j : ι) :
    lpCoordProjection j ∘L s.heatReporter - s.heatReporter ∘L lpCoordProjection j = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, lpCoordProjection_apply,
    lpCoordProjection_apply, map_smul, s.heatReporter_single, s.heatReporter_apply, smul_smul, mul_comm,
    sub_self, zero_apply]

/-- `[R_j, P] = ⟨e_j, v⟩ |e_j⟩⟨v| - ⟨v, e_j⟩ |v⟩⟨e_j|`. -/
theorem lpCoordProjection_commutator_heatProjection (j : ι) :
    lpCoordProjection j ∘L s.heatProjection - s.heatProjection ∘L lpCoordProjection j =
      ⟪(lp.single 2 j (1 : ℂ) : ℓ²ι), s.v⟫_ℂ • InnerProductSpace.rankOne ℂ (lp.single 2 j (1 : ℂ)) s.v -
        ⟪s.v, (lp.single 2 j (1 : ℂ) : ℓ²ι)⟫_ℂ • InnerProductSpace.rankOne ℂ s.v (lp.single 2 j (1 : ℂ)) := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [sub_apply, ContinuousLinearMap.comp_apply, smul_apply, InnerProductSpace.rankOne_apply,
    lpCoordProjection, heatProjection, inner_smul_right, smul_smul]
  rw [mul_comm ⟪(lp.single 2 j (1 : ℂ) : ℓ²ι), s.v⟫_ℂ, mul_comm ⟪s.v, (lp.single 2 j (1 : ℂ) : ℓ²ι)⟫_ℂ]

/-- **(OG.36)** `‖[R_j, P]‖₁ ≤ 2 |v_j| ‖v‖`. -/
theorem traceNorm_lpCoordProjection_commutator_le (j : ι) :
    traceNorm ℓ²ι (lpCoordProjection j ∘L s.heatProjection - s.heatProjection ∘L lpCoordProjection j) ≤
      2 * ‖s.v j‖ * ‖s.v‖ := by
  set X : SchattenOneOperator ℓ²ι :=
    ⟪(lp.single 2 j (1 : ℂ) : ℓ²ι), s.v⟫_ℂ • rankOneSchattenOne (lp.single 2 j (1 : ℂ) : ℓ²ι) s.v -
      ⟪s.v, (lp.single 2 j (1 : ℂ) : ℓ²ι)⟫_ℂ • rankOneSchattenOne s.v (lp.single 2 j (1 : ℂ) : ℓ²ι)
  have hX : (X : ℓ²ι →L[ℂ] ℓ²ι) =
      lpCoordProjection j ∘L s.heatProjection - s.heatProjection ∘L lpCoordProjection j := by
    rw [s.lpCoordProjection_commutator_heatProjection]
    simp only [X, SchattenOneOperator.coe_sub, SchattenOneOperator.coe_smul, rankOneSchattenOne_coe]
  rw [← hX, ← SchattenOneOperator.norm_def]
  calc ‖X‖ ≤ ‖⟪(lp.single 2 j (1 : ℂ) : ℓ²ι), s.v⟫_ℂ‖ * (‖(lp.single 2 j (1 : ℂ) : ℓ²ι)‖ * ‖s.v‖) +
        ‖⟪s.v, (lp.single 2 j (1 : ℂ) : ℓ²ι)⟫_ℂ‖ * (‖s.v‖ * ‖(lp.single 2 j (1 : ℂ) : ℓ²ι)‖) := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;>
          rw [norm_smul, norm_rankOneSchattenOne]
    _ = 2 * ‖s.v j‖ * ‖s.v‖ := by
        rw [inner_single_one_left, inner_single_one_right, Complex.norm_conj, norm_lpSingle_one]
        ring

end HeatSource

namespace CyclicHeatSource

variable (c : CyclicHeatSource ι) [DecidableEq ι]

/-- **(OG.37) Properness cannot be omitted.**  Along any injective sequence of coordinates the
normalized, approximately source-invariant projections `|e_{j_n}⟩⟨e_{j_n}|` have divergent orbit
cost. -/
theorem tendsto_orbitDefectCost_lpCoordProjection [Infinite ι] [Countable ι] {j : ℕ → ι}
    (hj : Function.Injective j) :
    Tendsto (fun n => c.orbitDefectCost (lpCoordProjection (j n))) atTop (𝓝 ⊤) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => absurd ha not_top_lt⟩
  by_contra hne
  rw [Filter.not_eventually] at hne
  obtain ⟨ψ, hψ, hψa⟩ := extraction_of_frequently_atTop hne
  have hv : Tendsto (fun n => ‖c.v (j (ψ n))‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun i => ‖c.v i‖ ^ 2) cofinite (𝓝 0) := c.summable_norm_sq.tendsto_cofinite_zero
    have h2 : Tendsto (fun i => ‖c.v i‖) cofinite (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at this
      refine this.congr fun i => ?_
      simp only [Function.comp_apply]
      rw [Real.sqrt_sq (norm_nonneg _)]
    have h3 : Tendsto (j ∘ ψ) atTop cofinite := by
      rw [← Nat.cofinite_eq_atTop]
      exact (hj.comp hψ.injective).tendsto_cofinite
    exact h2.comp h3
  have hcomm : Tendsto (fun n => traceNorm ℓ²ι (lpCoordProjection (j (ψ n)) ∘L c.heatReporter -
      c.heatReporter ∘L lpCoordProjection (j (ψ n))) + traceNorm ℓ²ι (lpCoordProjection (j (ψ n)) ∘L
        c.heatProjection - c.heatProjection ∘L lpCoordProjection (j (ψ n)))) atTop (𝓝 0) := by
    simp_rw [c.lpCoordProjection_commutator_heatReporter]
    simp_rw [traceNorm_zero, zero_add]
    refine squeeze_zero (fun n => traceNorm_nonneg _)
      (fun n => c.traceNorm_lpCoordProjection_commutator_le (j (ψ n))) ?_
    have := (hv.const_mul 2).mul_const ‖c.v‖
    simpa using this
  have hlim := c.tendsto_traceNorm_of_selection (fun n => lpCoordProjection (j (ψ n)))
    (fun n => isPositive_lpCoordProjection _) (fun n => memSchattenClass_lpCoordProjection _) hcomm
    (M := a.toReal) fun n => by
      rw [ENNReal.ofReal_toReal ha.ne]
      exact not_lt.1 (hψa n)
  simp_rw [traceNorm_lpCoordProjection] at hlim
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)

end CyclicHeatSource

/-! ## Full support is load-bearing -/

namespace HeatSource

variable (s : HeatSource ι) [DecidableEq ι]

/-- A coordinate missing from `v` lies in `ker G`. -/
theorem orbitGramian_single_of_v_eq_zero {j : ι} (hv : s.v j = 0) :
    s.orbitGramian (lp.single 2 j (1 : ℂ)) = 0 := by
  refine lp.ext (funext fun i => ?_)
  rw [← inner_single_one_left, inner_single_orbitGramian, hv, map_zero, mul_zero, zero_div,
    lp.coeFn_zero, Pi.zero_apply]

/-- A coordinate missing from `v` gives a projection commuting with `P`. -/
theorem lpCoordProjection_commutator_heatProjection_of_v_eq_zero {j : ι} (hv : s.v j = 0) :
    lpCoordProjection j ∘L s.heatProjection - s.heatProjection ∘L lpCoordProjection j = 0 := by
  rw [s.lpCoordProjection_commutator_heatProjection, inner_single_one_left, inner_single_one_right, hv,
    map_zero, zero_smul, zero_smul, sub_zero]

theorem lpCoordProjection_ne_smul_one [Nontrivial ι] (j : ι) (a : ℂ) :
    lpCoordProjection (ι := ι) j ≠ a • 1 := by
  intro h
  obtain ⟨i, hij⟩ := exists_ne j
  have h1 := congrArg (fun A : ℓ²ι →L[ℂ] ℓ²ι => A (lp.single 2 j (1 : ℂ))) h
  have h2 := congrArg (fun A : ℓ²ι →L[ℂ] ℓ²ι => A (lp.single 2 i (1 : ℂ))) h
  simp only [lpCoordProjection_apply, smul_apply, one_apply_eq_self, lp.single_apply_self] at h1 h2
  rw [lp.single_apply_ne _ _ _ hij.symm, zero_smul] at h2
  have h3 := congrArg (fun x : ℓ²ι => x i) h2
  simp only [lp.coeFn_zero, Pi.zero_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply_self,
    smul_eq_mul, mul_one] at h3
  have h4 := congrArg (fun x : ℓ²ι => x j) h1
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply_self, smul_eq_mul, mul_one, one_smul] at h4
  rw [← h3] at h4
  exact one_ne_zero h4

/-- **Full support is load-bearing.**  If `v_j = 0`, the non-scalar projection `|e_j⟩⟨e_j|`
commutes with `D` and `P`, and `e_j ∈ ker G`. -/
theorem fullSupport_load_bearing [Nontrivial ι] {j : ι} (hv : s.v j = 0) :
    s.orbitGramian (lp.single 2 j (1 : ℂ)) = 0 ∧
      Commute (lpCoordProjection j) s.heatReporter ∧ Commute (lpCoordProjection j) s.heatProjection ∧
      ∀ a : ℂ, lpCoordProjection (ι := ι) j ≠ a • 1 :=
  ⟨s.orbitGramian_single_of_v_eq_zero hv,
    sub_eq_zero.1 (s.lpCoordProjection_commutator_heatReporter j),
    sub_eq_zero.1 (s.lpCoordProjection_commutator_heatProjection_of_v_eq_zero hv),
    lpCoordProjection_ne_smul_one j⟩

/-! ## Simple spectrum is load-bearing -/

/-- The invisible direction `w = v̄_j e_i - v̄_i e_j` in a degenerate eigenspace. -/
def degenerateDirection (i j : ι) : ℓ²ι :=
  starRingEnd ℂ (s.v j) • lp.single 2 i (1 : ℂ) - starRingEnd ℂ (s.v i) • lp.single 2 j (1 : ℂ)

theorem degenerateDirection_apply (i j k : ι) :
    s.degenerateDirection i j k = starRingEnd ℂ (s.v j) * (lp.single 2 i (1 : ℂ) : ℓ²ι) k -
      starRingEnd ℂ (s.v i) * (lp.single 2 j (1 : ℂ) : ℓ²ι) k := by
  simp [degenerateDirection]

/-- **Simple spectrum is load-bearing.**  For `λ_i = λ_j`, `i ≠ j`, `v_i ≠ 0`: the direction
`w = v̄_j e_i - v̄_i e_j` is nonzero, `G w = 0`, and the non-scalar `|w⟩⟨w|` commutes with `D` and
`P`. -/
theorem simple_load_bearing {i j : ι} (hij : i ≠ j) (hlam : s.lam i = s.lam j) (hv : s.v i ≠ 0) :
    s.degenerateDirection i j ≠ 0 ∧ s.orbitGramian (s.degenerateDirection i j) = 0 ∧
      Commute (InnerProductSpace.rankOne ℂ (s.degenerateDirection i j) (s.degenerateDirection i j))
        s.heatReporter ∧
      Commute (InnerProductSpace.rankOne ℂ (s.degenerateDirection i j) (s.degenerateDirection i j))
        s.heatProjection ∧
      ∀ a : ℂ, InnerProductSpace.rankOne ℂ (s.degenerateDirection i j) (s.degenerateDirection i j) ≠
        a • (1 : ℓ²ι →L[ℂ] ℓ²ι) := by
  set w := s.degenerateDirection i j with hw
  have wi : w i = starRingEnd ℂ (s.v j) := by
    rw [hw, degenerateDirection_apply, lp.single_apply_self, lp.single_apply_ne _ _ _ hij]
    ring
  have wj : w j = -starRingEnd ℂ (s.v i) := by
    rw [hw, degenerateDirection_apply, lp.single_apply_self, lp.single_apply_ne _ _ _ hij.symm]
    ring
  have wk : ∀ k, k ≠ i → k ≠ j → w k = 0 := fun k hki hkj => by
    rw [hw, degenerateDirection_apply, lp.single_apply_ne _ _ _ hki, lp.single_apply_ne _ _ _ hkj]
    ring
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg (fun x : ℓ²ι => x j) h
    simp only [wj, lp.coeFn_zero, Pi.zero_apply, neg_eq_zero, map_eq_zero] at this
    exact hv this
  have hG : s.orbitGramian w = 0 := by
    rw [hw, degenerateDirection, map_sub, map_smul, map_smul]
    have hc : ∀ (y : ℓ²ι) (k : ι), s.orbitGramian y k =
        ⟪(lp.single 2 k (1 : ℂ) : ℓ²ι), s.orbitGramian y⟫_ℂ := fun y k => (inner_single_one_left _ _).symm
    refine lp.ext (funext fun k => ?_)
    rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply,
      hc (lp.single 2 i 1) k, hc (lp.single 2 j 1) k, inner_single_orbitGramian,
      inner_single_orbitGramian, hlam, lp.coeFn_zero, Pi.zero_apply, smul_eq_mul, smul_eq_mul]
    ring
  have hDw : s.heatReporter w = (((1 + s.lam i)⁻¹ : ℝ) : ℂ) • w := by
    rw [hw, degenerateDirection, map_sub, map_smul, map_smul, s.heatReporter_single, s.heatReporter_single,
      hlam, smul_comm _ (((1 + s.lam j)⁻¹ : ℝ) : ℂ), smul_comm _ (((1 + s.lam j)⁻¹ : ℝ) : ℂ), smul_sub]
  have hDsa : ∀ x y : ℓ²ι, ⟪x, s.heatReporter y⟫_ℂ = ⟪s.heatReporter x, y⟫_ℂ := fun x y => by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun k => ?_
    rw [s.heatReporter_apply, s.heatReporter_apply, RCLike.inner_apply, RCLike.inner_apply, map_mul,
      Complex.conj_ofReal]
    ring
  have hvw : ⟪s.v, w⟫_ℂ = 0 := by
    rw [hw, degenerateDirection, inner_sub_right, inner_smul_right, inner_smul_right,
      inner_single_one_right, inner_single_one_right]
    ring
  have hwv : ⟪w, s.v⟫_ℂ = 0 := by rw [← inner_conj_symm, hvw, map_zero]
  refine ⟨hw0, hG, ?_, ?_, fun a ha => ?_⟩
  · refine ContinuousLinearMap.ext fun x => ?_
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      InnerProductSpace.rankOne_apply, map_smul, hDw]
    rw [hDsa, hDw, inner_smul_left, Complex.conj_ofReal, smul_smul, mul_comm]
  · refine ContinuousLinearMap.ext fun x => ?_
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      InnerProductSpace.rankOne_apply, heatProjection, map_smul, hwv, hvw, zero_smul, smul_zero]
  · set u : ℓ²ι := s.v i • lp.single 2 i (1 : ℂ) + s.v j • lp.single 2 j (1 : ℂ) with hu
    have hwu : ⟪w, u⟫_ℂ = 0 := by
      rw [hu, inner_add_right, inner_smul_right, inner_smul_right, inner_single_one_right,
        inner_single_one_right, wi, wj, Complex.conj_conj, map_neg, Complex.conj_conj]
      ring
    have hu0 : u ≠ 0 := by
      intro h
      have := congrArg (fun x : ℓ²ι => x i) h
      simp only [hu, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, lp.single_apply_self,
        lp.single_apply_ne _ _ _ hij, smul_eq_mul, mul_one, mul_zero, add_zero, lp.coeFn_zero,
        Pi.zero_apply] at this
      exact hv this
    have h1 := congrArg (fun A : ℓ²ι →L[ℂ] ℓ²ι => A w) ha
    have h2 := congrArg (fun A : ℓ²ι →L[ℂ] ℓ²ι => A u) ha
    simp only [InnerProductSpace.rankOne_apply, smul_apply, one_apply_eq_self, hwu, zero_smul] at h1 h2
    rw [inner_self_eq_norm_sq_to_K] at h1
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at h1
      exact hw0 (by
        have := (smul_eq_zero.1 h1).resolve_left (by
          have : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw0
          exact pow_ne_zero 2 this)
        exact this)
    exact hu0 ((smul_eq_zero.1 h2.symm).resolve_left ha0)

end HeatSource

/-! ## The spectral gap is load-bearing -/

/-- **The spectral gap is load-bearing.**  A zero eigenvalue `λ_{j₀} = 0` with `v_{j₀} ≠ 0` makes
`‖S_t v‖² ≥ |v_{j₀}|²`, so neither `‖S_t v‖²` nor the rank-one orbit integrand is integrable on
`(0, ∞)`: the infinite-time Gramian does not exist as a trace-class Bochner integral. -/
theorem gap_load_bearing {lam : ι → ℝ} (hlam : ∀ j, 0 ≤ lam j) {v : ℓ²ι} {j₀ : ι}
    (h0 : lam j₀ = 0) (hv : v j₀ ≠ 0) :
    ¬ IntegrableOn (fun t => ‖heatSemigroup hlam t v‖ ^ 2) (Ioi 0) ∧
      ¬ IntegrableOn (fun t => positiveRankOneSchattenOne (heatSemigroup hlam t v)) (Ioi 0) := by
  have hlow : ∀ t, ‖v j₀‖ ^ 2 ≤ ‖heatSemigroup hlam t v‖ ^ 2 := fun t => by
    have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (heatSemigroup hlam t v) j₀
    rw [heatSemigroup_apply, heatFactor, h0, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one,
      one_mul] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hnot : ¬ IntegrableOn (fun t => ‖heatSemigroup hlam t v‖ ^ 2) (Ioi 0) := by
    intro hint
    have hc : IntegrableOn (fun _ : ℝ => ‖v j₀‖ ^ 2) (Ioi 0) :=
      Integrable.mono' hint aestronglyMeasurable_const (Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hlow t)
    rw [integrableOn_const_iff, Real.volume_Ioi] at hc
    rcases hc with hc | hc
    · have : ‖v j₀‖ ^ 2 = 0 := by simpa using hc
      exact hv (by simpa using this)
    · exact absurd hc (lt_irrefl _)
  refine ⟨hnot, fun hint => hnot ?_⟩
  refine Integrable.congr hint.norm (Eventually.of_forall fun t => ?_)
  simp only [norm_positiveRankOneSchattenOne]

/-! ## Infinite dimension is load-bearing -/

namespace CyclicHeatSource

variable (c : CyclicHeatSource ι) [DecidableEq ι]

instance finiteDimensional_lp [Fintype ι] : FiniteDimensional ℂ ℓ²ι :=
  Module.Finite.of_basis (HilbertSchmidt.lpBasis ι).toOrthonormalBasis.toBasis

/-- **Infinite dimension is load-bearing.**  On a finite index set `G` is invertible with bounded
inverse, and the scalar density `|ι|^{-1}·1` is positive, of trace one, commutes with `D` and `P`,
and has finite orbit cost: no extinction occurs. -/
theorem finiteDimension_load_bearing [Fintype ι] [Nonempty ι] :
    (∃ Ginv : ℓ²ι →L[ℂ] ℓ²ι, c.orbitGramian ∘L Ginv = 1 ∧ Ginv ∘L c.orbitGramian = 1) ∧
      let T : ℓ²ι →L[ℂ] ℓ²ι := ((Fintype.card ι : ℂ)⁻¹) • 1
      T.IsPositive ∧ MemSchattenClass 1 T ∧ traceNorm ℓ²ι T = 1 ∧ Commute T c.heatReporter ∧
        Commute T c.heatProjection ∧ c.orbitDefectCost T < ⊤ := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsurj : Function.Surjective c.orbitGramian :=
    (LinearMap.injective_iff_surjective (f := (c.orbitGramian : ℓ²ι →ₗ[ℂ] ℓ²ι))).1 c.orbitGramian_injective
  refine ⟨?_, ?_⟩
  · let e := ContinuousLinearEquiv.ofBijective c.orbitGramian
      (LinearMap.ker_eq_bot.2 c.orbitGramian_injective) (LinearMap.range_eq_top.2 hsurj)
    refine ⟨e.symm.toContinuousLinearMap, ?_, ?_⟩
    · exact ContinuousLinearMap.ext fun x => e.apply_symm_apply x
    · exact ContinuousLinearMap.ext fun x => e.symm_apply_apply x
  · intro T
    have hT : T = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) • 1 := by
      simp [T]
    have hpos : T.IsPositive := by
      rw [hT]
      exact ContinuousLinearMap.IsPositive.smul_of_nonneg ContinuousLinearMap.isPositive_one
        (by exact_mod_cast (inv_nonneg.2 hN.le))
    have hdiag : ∀ i, ⟪HilbertSchmidt.lpBasis ι i, T (HilbertSchmidt.lpBasis ι i)⟫_ℂ =
        (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) := fun i => by
      rw [hT, smul_apply, one_apply_eq_self, inner_smul_right, inner_self_eq_norm_sq_to_K,
        HilbertSchmidt.lpBasis_apply, norm_lpSingle_one]
      simp
    have hS : MemSchattenClass 1 T :=
      memSchattenClass_one_of_isPositive_of_summable_diagonal (HilbertSchmidt.lpBasis ι) hpos
        (Summable.of_finite)
    refine ⟨hpos, hS, ?_, ?_, ?_, ?_⟩
    · rw [traceNorm_eq_re_opTrace_of_isPositive hS hpos,
        opTrace_eq_tsum_basis_of_memSchattenClass_one hS (HilbertSchmidt.lpBasis ι), tsum_fintype]
      simp_rw [hdiag]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Complex.ofReal_natCast,
        ← Complex.ofReal_mul, Complex.ofReal_re, mul_inv_cancel₀ hN.ne']
    · exact (Commute.one_left _).smul_left _
    · exact (Commute.one_left _).smul_left _
    · haveI : Finite (EigenIndex c.orbitGramian) :=
        c.orbitEigenbasis.orthonormal.linearIndependent.finite
      haveI := Fintype.ofFinite (EigenIndex c.orbitGramian)
      rw [orbitDefectCost, tsum_fintype]
      exact ENNReal.sum_lt_top.2 fun k _ => ENNReal.ofReal_lt_top

end CyclicHeatSource

end GaloisForLFunctions.HTGeometry
