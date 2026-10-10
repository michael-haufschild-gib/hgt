import GaloisForLFunctions.RHTower.GaussianWeightedGapExtremalBohrSpectrum

/-!
# Relatively dense sign changes of the central Gaussian gap forced by an extremal zero

Let `G(y) = Σ Λ(n) n^{-1/2} e^{-yn²} − ∫₁^∞ u^{-1/2} e^{-yu²} du` and `Θ = sup Re ρ`.  Under RH the
gap is eventually negative (complete archimedean bias).  This file proves the opposite regime in
quantitative form.

**Theorem** (`exists_dense_sign_changes_of_extremal_zero`).  If `ξ` has a zero on the line
`Re ρ = Θ` and `Θ > ½`, there are `L, ε > 0` and `U₀` such that every window `[u₀, u₀ + L]` with
`u₀ ≥ U₀` contains points `u, u'` with
`G(e^{-u}) > ε e^{(Θ−½)u/2}` and `G(e^{-u'}) < −ε e^{(Θ−½)u'/2}`.
So the sign changes have bounded gaps and growing amplitude.

The proof uses three facts.
* The extremal decomposition: `e^{-(Θ−½)u/2} G(e^{-u}) = −Σ_{Re ρ = Θ} ½ Γ((ρ−½)/2) e^{i(Im ρ/2)u} + o(1)`.
* Window averages of an absolutely convergent exponential series over `[u₀, u₀ + L]` extract
  their coefficients uniformly in `u₀` (`exists_uniform_shiftedWindowAverage_tsum_cexp`).
* Positivity: a real function bounded below by `−ε` on a window satisfies
  `|avg(g e^{-iτu})| ≤ avg(g) + 2ε`.
The coefficient at `τ₀ = Im ρ₀/2` is nonzero (visibility of the extremal line) while the mean
coefficient vanishes, which contradicts positivity on long windows.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- The average of `f` over the window `[u₀, u₀ + L]`. -/
def gaussianShiftedWindowAverage (f : ℝ → ℂ) (u₀ L : ℝ) : ℂ :=
  (L : ℂ)⁻¹ * ∫ u in u₀..(u₀ + L), f u

theorem shiftedWindowAverage_cexp_zero (u₀ : ℝ) {L : ℝ} (hL : 0 < L) :
    gaussianShiftedWindowAverage (fun u => Complex.exp (((0 : ℝ) : ℂ) * I * (u : ℂ))) u₀ L = 1 := by
  rw [gaussianShiftedWindowAverage]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
    add_sub_cancel_left, Complex.real_smul, mul_one]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 hL.ne')

theorem norm_shiftedWindowAverage_cexp_le_one (μ u₀ : ℝ) {L : ℝ} (hL : 0 < L) :
    ‖gaussianShiftedWindowAverage (fun u => Complex.exp ((μ : ℂ) * I * (u : ℂ))) u₀ L‖ ≤ 1 := by
  rw [gaussianShiftedWindowAverage, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hL]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := u₀) (b := u₀ + L) (C := 1)
    (f := fun u : ℝ => Complex.exp ((μ : ℂ) * I * (u : ℂ)))
    (fun u _ => (norm_cexp_ofReal_mul_I_mul μ u).le)
  rw [add_sub_cancel_left, abs_of_pos hL, one_mul] at h
  calc L⁻¹ * ‖∫ u in u₀..(u₀ + L), Complex.exp ((μ : ℂ) * I * (u : ℂ))‖ ≤ L⁻¹ * L := by gcongr
    _ = 1 := inv_mul_cancel₀ hL.ne'

theorem norm_shiftedWindowAverage_cexp_le {μ : ℝ} (hμ : μ ≠ 0) (u₀ : ℝ) {L : ℝ} (hL : 0 < L) :
    ‖gaussianShiftedWindowAverage (fun u => Complex.exp ((μ : ℂ) * I * (u : ℂ))) u₀ L‖ ≤
      2 / (L * |μ|) := by
  have hc : (μ : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hμ) I_ne_zero
  rw [gaussianShiftedWindowAverage, integral_exp_mul_complex hc, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, norm_div]
  have hnum : ‖Complex.exp ((μ : ℂ) * I * ((u₀ + L : ℝ) : ℂ)) -
      Complex.exp ((μ : ℂ) * I * (u₀ : ℂ))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_cexp_ofReal_mul_I_mul, norm_cexp_ofReal_mul_I_mul]
    norm_num
  have hden : ‖(μ : ℂ) * I‖ = |μ| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  rw [hden]
  have hμ0 : 0 < |μ| := abs_pos.2 hμ
  calc L⁻¹ * (‖Complex.exp ((μ : ℂ) * I * ((u₀ + L : ℝ) : ℂ)) -
        Complex.exp ((μ : ℂ) * I * (u₀ : ℂ))‖ / |μ|) ≤ L⁻¹ * (2 / |μ|) := by gcongr
    _ = 2 / (L * |μ|) := by field_simp

/-- **Uniform coefficient extraction.**  For an absolutely convergent exponential series, the
window averages over `[u₀, u₀ + L]` approach the `τ`-coefficient uniformly in `u₀` as `L → ∞`. -/
theorem exists_uniform_shiftedWindowAverage_tsum_cexp {ι : Type*} [Countable ι] (c : ι → ℂ)
    (hc : Summable fun q => ‖c q‖) (μ : ι → ℝ) (τ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ u₀ : ℝ,
      ‖gaussianShiftedWindowAverage (fun u =>
          (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) *
            Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) u₀ L -
        ∑' q, (if μ q = τ then c q else 0)‖ ≤ ε := by
  -- the error weights
  set b : ℝ → ι → ℝ := fun L q => if μ q = τ then 0 else min 1 (2 / (|L| * |μ q - τ|)) with hb
  have hb0 : ∀ L q, 0 ≤ b L q := fun L q => by
    simp only [hb]; split_ifs
    · exact le_rfl
    · exact le_min zero_le_one (by positivity)
  have hb1 : ∀ L q, b L q ≤ 1 := fun L q => by
    simp only [hb]; split_ifs
    · exact zero_le_one
    · exact min_le_left _ _
  have hbt : Tendsto (fun L : ℝ => ∑' q, ‖c q‖ * b L q) atTop (𝓝 0) := by
    have hz : (0 : ℝ) = ∑' q : ι, ‖c q‖ * 0 := by simp
    rw [hz]
    refine tendsto_tsum_of_dominated_convergence hc (fun q => ?_) ?_
    · refine Tendsto.const_mul _ ?_
      simp only [hb]
      split_ifs with h
      · exact tendsto_const_nhds
      · have hμ : 0 < |μ q - τ| := abs_pos.2 (sub_ne_zero.2 h)
        have h2 : Tendsto (fun L : ℝ => 2 / (|L| * |μ q - τ|)) atTop (𝓝 0) := by
          have := (tendsto_inv_atTop_zero.const_mul (2 / |μ q - τ|))
          rw [mul_zero] at this
          refine this.congr' ?_
          filter_upwards [eventually_gt_atTop 0] with L hL
          rw [abs_of_pos hL]
          field_simp
        have h3 := (tendsto_const_nhds (x := (1 : ℝ))).min h2
        rwa [min_eq_right zero_le_one] at h3
    · exact Eventually.of_forall fun L q => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hb0 L q))]
        exact mul_le_of_le_one_right (norm_nonneg _) (hb1 L q)
  obtain ⟨L₁, hL₁⟩ := (hbt.eventually (ge_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨max L₁ 1, by positivity, fun L hL u₀ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  -- interchange the window integral with the series
  let F : ι → C(ℝ, ℂ) := fun q =>
    ⟨fun u => c q * Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ)), by fun_prop⟩
  have hnormF : ∀ q (K : TopologicalSpace.Compacts ℝ), ‖(F q).restrict K‖ ≤ ‖c q‖ := by
    intro q K
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
    show ‖c q * Complex.exp (((μ q - τ : ℝ) : ℂ) * I * ((x : ℝ) : ℂ))‖ ≤ ‖c q‖
    rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one]
  have hpt : ∀ u : ℝ, (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) *
      Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ)) = ∑' q, F q u := by
    intro u
    rw [← tsum_mul_right]
    refine tsum_congr fun q => ?_
    show c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ)) * Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ)) =
      c q * Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ))
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have havg : gaussianShiftedWindowAverage (fun u =>
      (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) *
        Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) u₀ L =
      ∑' q, c q * gaussianShiftedWindowAverage
        (fun u => Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ))) u₀ L := by
    rw [gaussianShiftedWindowAverage]
    simp_rw [hpt]
    rw [← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hnormF q _) hc),
      ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [gaussianShiftedWindowAverage]
    have : ∫ x in u₀..(u₀ + L), F q x = c q * ∫ x in u₀..(u₀ + L),
        Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (x : ℂ)) :=
      intervalIntegral.integral_const_mul (c q)
        (fun u : ℝ => Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ)))
    rw [this]
    ring
  have hsumc : Summable fun q => c q * gaussianShiftedWindowAverage
      (fun u => Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ))) u₀ L :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (norm_shiftedWindowAverage_cexp_le_one _ _ hLpos)) hc)
  have hsumi : Summable fun q => (if μ q = τ then c q else 0) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => by
      split_ifs <;> simp) hc)
  rw [havg, ← hsumc.tsum_sub hsumi]
  have hterm : ∀ q, ‖c q * gaussianShiftedWindowAverage
      (fun u => Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ))) u₀ L -
      (if μ q = τ then c q else 0)‖ ≤ ‖c q‖ * b L q := by
    intro q
    simp only [hb]
    split_ifs with h
    · have h0 : μ q - τ = 0 := sub_eq_zero.2 h
      rw [h0, shiftedWindowAverage_cexp_zero u₀ hLpos]
      simp
    · rw [sub_zero, norm_mul]
      rw [abs_of_pos hLpos]
      refine mul_le_mul_of_nonneg_left (le_min (norm_shiftedWindowAverage_cexp_le_one _ _ hLpos)
        (norm_shiftedWindowAverage_cexp_le (sub_ne_zero.2 h) u₀ hLpos)) (norm_nonneg _)
  have hsumb : Summable fun q => ‖c q‖ * b L q :=
    Summable.of_nonneg_of_le (fun q => mul_nonneg (norm_nonneg _) (hb0 L q))
      (fun q => mul_le_of_le_one_right (norm_nonneg _) (hb1 L q)) hc
  calc _ ≤ ∑' q, ‖c q * gaussianShiftedWindowAverage
        (fun u => Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ))) u₀ L -
        (if μ q = τ then c q else 0)‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumb)
    _ ≤ ∑' q, ‖c q‖ * b L q :=
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumb).tsum_le_tsum hterm hsumb
    _ ≤ ε := hL₁ L ((le_max_left _ _).trans hL)

/-- A function tending to `0` has small window averages on late windows, uniformly in `L > 0`. -/
theorem exists_late_shiftedWindowAverage_small {r : ℝ → ℂ} (h0 : Tendsto r atTop (𝓝 0)) (τ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ u₀ : ℝ, U₀ ≤ u₀ → ∀ L : ℝ, 0 < L →
      ‖gaussianShiftedWindowAverage (fun u => r u *
        Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) u₀ L‖ ≤ ε := by
  obtain ⟨U₀, hU₀⟩ := (Metric.tendsto_atTop.1 h0) ε hε
  refine ⟨U₀, fun u₀ hu₀ L hL => ?_⟩
  rw [gaussianShiftedWindowAverage, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hL]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := u₀) (b := u₀ + L) (C := ε)
    (f := fun u : ℝ => r u * Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) (fun u hu => by
      rw [Set.uIoc_of_le (by linarith)] at hu
      rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one]
      have := hU₀ u (by linarith [hu.1])
      rw [dist_zero_right] at this
      exact this.le)
  rw [add_sub_cancel_left, abs_of_pos hL] at h
  calc L⁻¹ * ‖∫ u in u₀..(u₀ + L), r u * Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))‖
      ≤ L⁻¹ * (ε * L) := by gcongr
    _ = ε := by field_simp

/-- **Positivity on a window.**  If a real continuous `g` satisfies `g ≥ −ε` on `[u₀, u₀ + L]`, then
`‖avg(g e^{-iτu})‖ ≤ Re avg(g) + 2ε`. -/
theorem norm_shiftedWindowAverage_le_of_ge {g : ℝ → ℝ} (hg : Continuous g) {u₀ L ε : ℝ}
    (hL : 0 < L) (hε : 0 ≤ ε) (hge : ∀ u ∈ Icc u₀ (u₀ + L), -ε ≤ g u) (τ : ℝ) :
    ‖gaussianShiftedWindowAverage (fun u => (g u : ℂ) *
        Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) u₀ L‖ ≤
      (gaussianShiftedWindowAverage (fun u => (g u : ℂ)) u₀ L).re + 2 * ε := by
  have hle : u₀ ≤ u₀ + L := by linarith
  have hint : ∫ u in u₀..(u₀ + L), (g u : ℂ) = ((∫ u in u₀..(u₀ + L), g u : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  have hre : (gaussianShiftedWindowAverage (fun u => (g u : ℂ)) u₀ L).re =
      L⁻¹ * ∫ u in u₀..(u₀ + L), g u := by
    rw [gaussianShiftedWindowAverage, hint, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [hre, gaussianShiftedWindowAverage, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hL]
  have h1 : ‖∫ u in u₀..(u₀ + L), (g u : ℂ) * Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))‖ ≤
      ∫ u in u₀..(u₀ + L), |g u| := by
    refine (intervalIntegral.norm_integral_le_integral_norm hle).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ∫ u in u₀..(u₀ + L), |g u| ≤ ∫ u in u₀..(u₀ + L), (g u + 2 * ε) := by
    refine intervalIntegral.integral_mono_on hle (hg.abs.intervalIntegrable _ _)
      ((hg.add continuous_const).intervalIntegrable _ _) fun u hu => ?_
    have := hge u hu
    rcases abs_cases (g u) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have h3 : ∫ u in u₀..(u₀ + L), (g u + 2 * ε) = (∫ u in u₀..(u₀ + L), g u) + L * (2 * ε) := by
    rw [intervalIntegral.integral_add (hg.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [add_sub_cancel_left, smul_eq_mul]
  calc L⁻¹ * ‖∫ u in u₀..(u₀ + L), (g u : ℂ) * Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))‖
      ≤ L⁻¹ * ((∫ u in u₀..(u₀ + L), g u) + L * (2 * ε)) := by
        gcongr
        exact h1.trans (h2.trans h3.le)
    _ = L⁻¹ * (∫ u in u₀..(u₀ + L), g u) + 2 * ε := by field_simp

theorem gaussianShiftedWindowAverage_sub {f₁ f₂ : ℝ → ℂ} (h₁ : Continuous f₁)
    (h₂ : Continuous f₂) (u₀ L : ℝ) :
    gaussianShiftedWindowAverage (fun u => f₁ u - f₂ u) u₀ L =
      gaussianShiftedWindowAverage f₁ u₀ L - gaussianShiftedWindowAverage f₂ u₀ L := by
  rw [gaussianShiftedWindowAverage, gaussianShiftedWindowAverage, gaussianShiftedWindowAverage,
    intervalIntegral.integral_sub (h₁.intervalIntegrable _ _) (h₂.intervalIntegrable _ _)]
  ring

theorem gaussianShiftedWindowAverage_neg (f : ℝ → ℂ) (u₀ L : ℝ) :
    gaussianShiftedWindowAverage (fun u => -f u) u₀ L = -gaussianShiftedWindowAverage f u₀ L := by
  rw [gaussianShiftedWindowAverage, gaussianShiftedWindowAverage, intervalIntegral.integral_neg]
  ring

/-- No zero is real, so the extremal Bohr coefficient at frequency `0` vanishes. -/
theorem weightedBohrCoefficient_zero (θ : ℝ) : weightedBohrCoefficient θ 0 = 0 := by
  by_contra h
  have hz := exists_xi_zero_of_weightedBohrCoefficient_ne_zero h
  exact xi_ne_zero_of_abs_im_le_one (by simp) hz

/-- **Abstract sign lemma.**  Let `g` be real and continuous with
`g(u) + Σ_q c_q e^{iμ_q u} → 0`, where `Σ ‖c_q‖ < ∞`, the `0`-coefficient `Σ_{μ_q = 0} c_q` vanishes
and some `τ₀`-coefficient is nonzero.  Then `g` takes values `> ε` and `< −ε` in every late window
of a fixed length. -/
theorem exists_dense_sign_changes_of_tendsto_add_tsum {ι : Type*} [Countable ι] {g : ℝ → ℝ}
    (hg : Continuous g) (c : ι → ℂ) (hc : Summable fun q => ‖c q‖) (μ : ι → ℝ)
    (hlim : Tendsto (fun u : ℝ => (g u : ℂ) + ∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ)))
      atTop (𝓝 0))
    (h0 : (∑' q, if μ q = 0 then c q else 0) = 0) {τ₀ : ℝ}
    (hτ₀ : (∑' q, if μ q = τ₀ then c q else 0) ≠ 0) :
    ∃ L ε U₀ : ℝ, 0 < L ∧ 0 < ε ∧ ∀ u₀ : ℝ, U₀ ≤ u₀ →
      (∃ u ∈ Icc u₀ (u₀ + L), ε < g u) ∧ (∃ u ∈ Icc u₀ (u₀ + L), g u < -ε) := by
  set S : ℝ → ℂ := fun u => ∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ)) with hSdef
  have hScont : Continuous S := by
    refine continuous_tsum (fun q => by fun_prop) hc (fun q u => ?_)
    rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one]
  set r : ℝ → ℂ := fun u => (g u : ℂ) + S u with hrdef
  have hrcont : Continuous r := (Complex.continuous_ofReal.comp hg).add hScont
  set C₀ : ℂ := ∑' q, if μ q = τ₀ then c q else 0 with hC₀
  set δ : ℝ := ‖C₀‖ with hδ
  have hδ0 : 0 < δ := norm_pos_iff.2 hτ₀
  obtain ⟨L₁, hL₁0, hL₁⟩ := exists_uniform_shiftedWindowAverage_tsum_cexp c hc μ τ₀
    (ε := δ / 8) (by positivity)
  obtain ⟨L₂, hL₂0, hL₂⟩ := exists_uniform_shiftedWindowAverage_tsum_cexp c hc μ 0
    (ε := δ / 8) (by positivity)
  obtain ⟨U₁, hU₁⟩ := exists_late_shiftedWindowAverage_small hlim τ₀ (ε := δ / 8) (by positivity)
  obtain ⟨U₂, hU₂⟩ := exists_late_shiftedWindowAverage_small hlim 0 (ε := δ / 8) (by positivity)
  set L : ℝ := max L₁ L₂ with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le hL₁0 (le_max_left _ _)
  refine ⟨L, δ / 16, max U₁ U₂, hL0, by positivity, fun u₀ hu₀ => ?_⟩
  have hu₁ : U₁ ≤ u₀ := (le_max_left _ _).trans hu₀
  have hu₂ : U₂ ≤ u₀ := (le_max_right _ _).trans hu₀
  set e : ℝ → ℝ → ℂ := fun τ u => Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ)) with he
  have hecont : ∀ τ, Continuous (e τ) := fun τ => by fun_prop
  have hsplit : ∀ τ : ℝ, gaussianShiftedWindowAverage (fun u => (g u : ℂ) * e τ u) u₀ L =
      gaussianShiftedWindowAverage (fun u => r u * e τ u) u₀ L -
        gaussianShiftedWindowAverage (fun u => S u * e τ u) u₀ L := by
    intro τ
    have hs := gaussianShiftedWindowAverage_sub (f₁ := fun u => r u * e τ u)
      (f₂ := fun u => S u * e τ u) (hrcont.mul (hecont τ)) (hScont.mul (hecont τ)) u₀ L
    rw [← hs]
    congr 1
    funext u
    simp only [hrdef]
    ring
  have hfreq : ‖gaussianShiftedWindowAverage (fun u => (g u : ℂ) * e τ₀ u) u₀ L‖ ≥ 3 * δ / 4 := by
    rw [hsplit]
    have h1 := hL₁ L (le_max_left _ _) u₀
    have h2 := hU₁ u₀ hu₁ L hL0
    have h3 : ‖gaussianShiftedWindowAverage (fun u => S u * e τ₀ u) u₀ L‖ ≥ δ - δ / 8 := by
      have := norm_sub_norm_le C₀ (C₀ - gaussianShiftedWindowAverage (fun u => S u * e τ₀ u) u₀ L)
      rw [sub_sub_cancel, norm_sub_rev] at this
      have h1' : ‖gaussianShiftedWindowAverage (fun u => S u * e τ₀ u) u₀ L - C₀‖ ≤ δ / 8 := h1
      linarith
    have := norm_sub_norm_le (gaussianShiftedWindowAverage (fun u => S u * e τ₀ u) u₀ L)
      (gaussianShiftedWindowAverage (fun u => r u * e τ₀ u) u₀ L)
    rw [norm_sub_rev] at this
    have h2' : ‖gaussianShiftedWindowAverage (fun u => r u * e τ₀ u) u₀ L‖ ≤ δ / 8 := h2
    linarith
  have hmean : ‖gaussianShiftedWindowAverage (fun u => (g u : ℂ)) u₀ L‖ ≤ δ / 4 := by
    have he0 : (fun u => (g u : ℂ)) = fun u => (g u : ℂ) * e 0 u := by
      funext u; simp [he]
    rw [he0, hsplit]
    have h1 := hL₂ L (le_max_right _ _) u₀
    rw [h0, sub_zero] at h1
    have h2 := hU₂ u₀ hu₂ L hL0
    have h1' : ‖gaussianShiftedWindowAverage (fun u => S u * e 0 u) u₀ L‖ ≤ δ / 8 := h1
    have h2' : ‖gaussianShiftedWindowAverage (fun u => r u * e 0 u) u₀ L‖ ≤ δ / 8 := h2
    calc _ ≤ ‖gaussianShiftedWindowAverage (fun u => r u * e 0 u) u₀ L‖ +
          ‖gaussianShiftedWindowAverage (fun u => S u * e 0 u) u₀ L‖ := norm_sub_le _ _
      _ ≤ δ / 4 := by linarith
  have hre := Complex.abs_re_le_norm (gaussianShiftedWindowAverage (fun u => (g u : ℂ)) u₀ L)
  have hmre := abs_le.1 (hre.trans hmean)
  constructor
  · by_contra hno
    push Not at hno
    have hge : ∀ u ∈ Icc u₀ (u₀ + L), -(δ / 16) ≤ -g u := fun u hu => by
      have := hno u hu; linarith
    have hpos := norm_shiftedWindowAverage_le_of_ge (g := fun u => -g u) hg.neg hL0
      (by positivity) hge τ₀
    beta_reduce at hpos
    have hneg1 : gaussianShiftedWindowAverage (fun u => ((-g u : ℝ) : ℂ) *
        Complex.exp (((-τ₀ : ℝ) : ℂ) * I * (u : ℂ))) u₀ L =
        -gaussianShiftedWindowAverage (fun u => (g u : ℂ) * e τ₀ u) u₀ L := by
      rw [← gaussianShiftedWindowAverage_neg]
      congr 1; funext u; simp [he]
    have hneg2 : gaussianShiftedWindowAverage (fun u => ((-g u : ℝ) : ℂ)) u₀ L =
        -gaussianShiftedWindowAverage (fun u => (g u : ℂ)) u₀ L := by
      rw [← gaussianShiftedWindowAverage_neg]
      congr 1; funext u; simp
    rw [hneg1, hneg2, norm_neg, Complex.neg_re] at hpos
    linarith
  · by_contra hno
    push Not at hno
    have hpos := norm_shiftedWindowAverage_le_of_ge hg hL0 (by positivity) hno τ₀
    have hfreq' : ‖gaussianShiftedWindowAverage (fun u => (g u : ℂ) *
        Complex.exp (((-τ₀ : ℝ) : ℂ) * I * (u : ℂ))) u₀ L‖ ≥ 3 * δ / 4 := hfreq
    linarith

/-- **Dense sign changes forced by an extremal zero.**  If `ξ` has a zero on `Re ρ = Θ` and
`Θ > ½`, then there are `L, ε > 0` and `U₀` such that every window `[u₀, u₀ + L]`, `u₀ ≥ U₀`,
contains points where `G(e^{-u}) > ε e^{(Θ−½)u/2}` and points where `G(e^{-u}) < −ε e^{(Θ−½)u/2}`. -/
theorem exists_dense_sign_changes_of_extremal_zero {ρ₀ : ℂ} (hρ₀ : xi ρ₀ = 0)
    (hre : ρ₀.re = xiZeroAbscissa) (hΘ : 1 / 2 < xiZeroAbscissa) :
    ∃ L ε U₀ : ℝ, 0 < L ∧ 0 < ε ∧ ∀ u₀ : ℝ, U₀ ≤ u₀ →
      (∃ u ∈ Icc u₀ (u₀ + L), ε * Real.exp ((xiZeroAbscissa - 1 / 2) * u / 2) <
        gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) ∧
      (∃ u ∈ Icc u₀ (u₀ + L), gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)) <
        -(ε * Real.exp ((xiZeroAbscissa - 1 / 2) * u / 2))) := by
  set Θ : ℝ := xiZeroAbscissa with hΘdef
  have hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ Θ := fun _ hρ => re_le_xiZeroAbscissa hρ
  set G : ℝ → ℝ := fun u => gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
    gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)) with hGdef
  have hGcont : Continuous G := by
    have h := continuous_gaussianBudgetProfile (σ := 1 / 2) (by norm_num) (-1) 0 0
    have heq : G = gaussianBudgetProfile (-1) (1 / 2) 0 0 := by
      funext u; simp [hGdef, gaussianBudgetProfile]
    rw [heq]; exact h
  set g : ℝ → ℝ := fun u => Real.exp (-((Θ - 1 / 2) * u / 2)) * G u with hgdef
  have hgcont : Continuous g := (by fun_prop : Continuous fun u : ℝ =>
    Real.exp (-((Θ - 1 / 2) * u / 2))).mul hGcont
  set c : XiZeroCopy → ℂ := fun q => if (xiZero q).re = Θ then zeroBohrAmplitude q else 0 with hc
  have hcsum : Summable fun q => ‖c q‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => by simp only [hc]; split_ifs <;> simp) summable_norm_zeroBohrAmplitude
  have hlim : Tendsto (fun u : ℝ => (g u : ℂ) + ∑' q, c q *
      Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ))) atTop (𝓝 0) := by
    have h := tendsto_weightedGap_add_extremalSeries hθ
    have hne : Θ ≠ 1 / 2 := ne_of_gt hΘ
    refine h.congr fun u => ?_
    simp only [hgdef, hGdef, hc, if_neg hne, Complex.ofReal_zero, zero_mul, sub_zero]
  have hcoef : ∀ τ : ℝ, (∑' q : XiZeroCopy, if xiZeroHalfOrdinate q = τ then c q else 0) =
      weightedBohrCoefficient Θ τ := by
    intro τ
    rw [weightedBohrCoefficient]
    refine tsum_congr fun q => ?_
    simp only [hc]
    by_cases h1 : (xiZero q).re = Θ <;> by_cases h2 : xiZeroHalfOrdinate q = τ <;> simp [h1, h2]
  have h0 : (∑' q : XiZeroCopy, if xiZeroHalfOrdinate q = 0 then c q else 0) = 0 := by
    rw [hcoef 0, weightedBohrCoefficient_zero]
  have hτ₀ : (∑' q : XiZeroCopy, if xiZeroHalfOrdinate q = ρ₀.im / 2 then c q else 0) ≠ 0 := by
    rw [hcoef]; exact weightedBohrCoefficient_ne_zero_of_xi_eq_zero hρ₀ hre
  obtain ⟨L, ε, U₀, hL, hε, hwin⟩ :=
    exists_dense_sign_changes_of_tendsto_add_tsum hgcont c hcsum xiZeroHalfOrdinate hlim h0 hτ₀
  have hGg : ∀ u, G u = Real.exp ((Θ - 1 / 2) * u / 2) * g u := by
    intro u
    simp only [hgdef]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  refine ⟨L, ε, U₀, hL, hε, fun u₀ hu₀ => ?_⟩
  obtain ⟨⟨u, hu, hgu⟩, ⟨u', hu', hgu'⟩⟩ := hwin u₀ hu₀
  refine ⟨⟨u, hu, ?_⟩, ⟨u', hu', ?_⟩⟩
  · have h : G u = Real.exp ((Θ - 1 / 2) * u / 2) * g u := hGg u
    have hpos := Real.exp_pos ((Θ - 1 / 2) * u / 2)
    show ε * Real.exp ((Θ - 1 / 2) * u / 2) < G u
    rw [h]; nlinarith
  · have h : G u' = Real.exp ((Θ - 1 / 2) * u' / 2) * g u' := hGg u'
    have hpos := Real.exp_pos ((Θ - 1 / 2) * u' / 2)
    show G u' < -(ε * Real.exp ((Θ - 1 / 2) * u' / 2))
    rw [h]; nlinarith

end

end RHTower
