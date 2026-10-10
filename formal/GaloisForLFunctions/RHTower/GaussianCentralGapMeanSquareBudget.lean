import GaloisForLFunctions.RHTower.GaussianWeightedGapExtremalParseval

/-!
# The mean-square form of the central Gaussian budget

Let `G(u) = Σ Λ(n) n^{-1/2} e^{-e^{-u} n²} − ∫₁^∞ v^{-1/2} e^{-e^{-u} v²} dv` be the central Gaussian
prime gap read in the logarithmic damping variable.

**Theorem** (`riemannHypothesis_iff_gaussianCentralGap_meanSquare_le`).  RH holds iff
`∫₀^U G(u)² du ≤ K U` for all `U ≥ 1`.  It also holds iff for every `ε > 0` there is `K` with
`∫₀^U G(u)² du ≤ K e^{εU}` for all `U ≥ 0`.

* `⇒`: under RH the Cesàro means of `G²` converge (Gaussian Cramér identity).
* `⇐`: unit-block Cauchy–Schwarz turns the `L²` growth bound into absolute convergence of
  `∫₀^∞ |G(u)| e^{-τu} du` for every `τ > 0`, and the integrated one-sided Landau law excludes
  zeros with `Re ρ > ½`.

The budget thus has an `L²` form: a second-moment statement about a bilinear form in `Λ`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- The central Gaussian gap in the logarithmic damping variable. -/
def gaussianCentralGapLog (u : ℝ) : ℝ :=
  gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
    gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))

theorem continuous_gaussianCentralGapLog : Continuous gaussianCentralGapLog := by
  have h := continuous_gaussianBudgetProfile (σ := 1 / 2) (by norm_num) (-1) 0 0
  have heq : gaussianCentralGapLog = gaussianBudgetProfile (-1) (1 / 2) 0 0 := by
    funext u; simp [gaussianCentralGapLog, gaussianBudgetProfile]
  rw [heq]; exact h

/-- Cauchy–Schwarz on a unit interval: `(∫_a^{a+1} |f|)² ≤ ∫_a^{a+1} f²`. -/
theorem integral_abs_sq_le_integral_sq_unit {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    (∫ u in a..(a + 1), |f u|) ^ 2 ≤ ∫ u in a..(a + 1), f u ^ 2 := by
  set m : ℝ := ∫ u in a..(a + 1), |f u| with hm
  have hle : a ≤ a + 1 := by linarith
  have hsq : 0 ≤ ∫ u in a..(a + 1), (|f u| - m) ^ 2 :=
    intervalIntegral.integral_nonneg hle fun u _ => sq_nonneg _
  have i1 : IntervalIntegrable (fun u => f u ^ 2 - 2 * m * |f u|) volume a (a + 1) :=
    ((hf.pow 2).sub (continuous_const.mul hf.abs)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun u => f u ^ 2) volume a (a + 1) :=
    (hf.pow 2).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun u => 2 * m * |f u|) volume a (a + 1) :=
    (continuous_const.mul hf.abs).intervalIntegrable _ _
  have hexp : ∫ u in a..(a + 1), (|f u| - m) ^ 2 =
      (∫ u in a..(a + 1), f u ^ 2) - 2 * m * m + m ^ 2 := by
    have e1 : (fun u => (|f u| - m) ^ 2) = fun u => (f u ^ 2 - 2 * m * |f u|) + m ^ 2 := by
      funext u; rw [sub_sq, sq_abs]; ring
    rw [e1, intervalIntegral.integral_add i1 intervalIntegrable_const,
      intervalIntegral.integral_sub i2 i3, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, add_sub_cancel_left, one_smul]
  rw [hexp] at hsq
  nlinarith

/-- An `L²` growth bound `∫₀^U f² ≤ K e^{εU}` gives absolute convergence of the Laplace integral
`∫₀^∞ |f| e^{-τu}` for every `τ > ε/2`. -/
theorem integrableOn_abs_mul_exp_of_integral_sq_le {f : ℝ → ℝ} (hf : Continuous f) {K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hbound : ∀ U : ℝ, 0 ≤ U → ∫ u in (0 : ℝ)..U, f u ^ 2 ≤ K * Real.exp (ε * U))
    {τ : ℝ} (hτ : ε / 2 < τ) :
    IntegrableOn (fun u => |f u| * Real.exp (-τ * u)) (Ioi 0) := by
  set r : ℝ := Real.exp (-(τ - ε / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  set I : ℝ := Real.sqrt K * Real.exp (ε / 2) * (1 - r)⁻¹ with hI
  have hcont : Continuous fun u => |f u| * Real.exp (-τ * u) := by fun_prop
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (l := atTop) (b := fun n : ℕ => (n : ℝ))
    I 0 (fun n => (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self) tendsto_natCast_atTop_atTop
    (Eventually.of_forall fun n => ?_)
  -- unit blocks
  have hblock : ∀ k : ℕ, ∫ u in (k : ℝ)..((k : ℝ) + 1), ‖|f u| * Real.exp (-τ * u)‖ ≤
      Real.sqrt K * Real.exp (ε / 2) * r ^ k := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hle : (k : ℝ) ≤ k + 1 := by linarith
    have h1 : ∫ u in (k : ℝ)..((k : ℝ) + 1), ‖|f u| * Real.exp (-τ * u)‖ ≤
        Real.exp (-τ * k) * ∫ u in (k : ℝ)..((k : ℝ) + 1), |f u| := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hle (hcont.norm.intervalIntegrable _ _)
        ((continuous_const.mul hf.abs).intervalIntegrable _ _) fun u hu => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _), mul_comm]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (abs_nonneg _)
      have := hu.1
      have hτ0 : 0 < τ := by linarith
      nlinarith
    have h2 : (∫ u in (k : ℝ)..((k : ℝ) + 1), |f u|) ^ 2 ≤ K * Real.exp (ε * (k + 1)) := by
      refine (integral_abs_sq_le_integral_sq_unit hf k).trans ?_
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        ((hf.pow 2).intervalIntegrable (μ := volume) 0 (k : ℝ))
        ((hf.pow 2).intervalIntegrable (μ := volume) (k : ℝ) (k + 1))
      have hnn : 0 ≤ ∫ u in (0 : ℝ)..(k : ℝ), f u ^ 2 :=
        intervalIntegral.integral_nonneg hk0 fun u _ => sq_nonneg _
      have := hbound (k + 1) (by linarith)
      simp only [Pi.pow_apply] at hsplit
      linarith
    have h3 : ∫ u in (k : ℝ)..((k : ℝ) + 1), |f u| ≤ Real.sqrt K * Real.exp (ε * (k + 1) / 2) := by
      have hnn : 0 ≤ ∫ u in (k : ℝ)..((k : ℝ) + 1), |f u| :=
        intervalIntegral.integral_nonneg hle fun u _ => abs_nonneg _
      have hrhs : Real.sqrt K * Real.exp (ε * (k + 1) / 2) =
          Real.sqrt (K * Real.exp (ε * (k + 1))) := by
        have he : Real.exp (ε * (k + 1)) = Real.exp (ε * (k + 1) / 2) ^ 2 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        rw [Real.sqrt_mul hK, he, Real.sqrt_sq (Real.exp_pos _).le]
      rw [hrhs]
      exact Real.le_sqrt_of_sq_le h2
    calc _ ≤ Real.exp (-τ * k) * ∫ u in (k : ℝ)..((k : ℝ) + 1), |f u| := h1
      _ ≤ Real.exp (-τ * k) * (Real.sqrt K * Real.exp (ε * (k + 1) / 2)) := by gcongr
      _ = Real.sqrt K * Real.exp (ε / 2) * r ^ k := by
          rw [hr, ← Real.exp_nat_mul,
            show Real.exp (-τ * k) * (Real.sqrt K * Real.exp (ε * (k + 1) / 2)) =
              Real.sqrt K * Real.exp (-τ * k + ε * (k + 1) / 2) by rw [Real.exp_add]; ring,
            show Real.sqrt K * Real.exp (ε / 2) * Real.exp (k * -(τ - ε / 2)) =
              Real.sqrt K * Real.exp (ε / 2 + k * -(τ - ε / 2)) by rw [Real.exp_add]; ring]
          congr 2
          ring
  have hsum : ∫ u in (0 : ℝ)..(n : ℝ), ‖|f u| * Real.exp (-τ * u)‖ =
      ∑ k ∈ Finset.range n, ∫ u in (k : ℝ)..((k : ℝ) + 1), ‖|f u| * Real.exp (-τ * u)‖ := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
      (n := n) (f := fun u => ‖|f u| * Real.exp (-τ * u)‖) (μ := volume)
      (fun k _ => hcont.norm.intervalIntegrable _ _)
    simp only [Nat.cast_zero, Nat.cast_succ] at h
    exact h.symm
  rw [hsum]
  calc ∑ k ∈ Finset.range n, ∫ u in (k : ℝ)..((k : ℝ) + 1), ‖|f u| * Real.exp (-τ * u)‖
      ≤ ∑ k ∈ Finset.range n, Real.sqrt K * Real.exp (ε / 2) * r ^ k :=
        Finset.sum_le_sum fun k _ => hblock k
    _ = Real.sqrt K * Real.exp (ε / 2) * ∑ k ∈ Finset.range n, r ^ k := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt K * Real.exp (ε / 2) * (1 - r)⁻¹ := by
        gcongr
        exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun k _ => pow_nonneg hr0 k)
          |>.trans (le_of_eq (tsum_geometric_of_lt_one hr0 hr1))

/-- Convergent Cesàro means of a nonnegative continuous function give linear growth of its
integral on all of `[0, ∞)`. -/
theorem exists_integral_le_mul_add_one_of_tendsto {h : ℝ → ℝ} (hh : Continuous h)
    (hnn : ∀ u, 0 ≤ h u) {L : ℝ}
    (hlim : Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0 : ℝ)..T, h u) atTop (𝓝 L)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : ℝ, 0 ≤ U → ∫ u in (0 : ℝ)..U, h u ≤ K * (U + 1) := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1
    ((hlim.eventually (gt_mem_nhds (lt_add_one L))).and (eventually_gt_atTop 0))
  set T₁ : ℝ := max T₀ 1 with hT₁
  have hT₁pos : 0 < T₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set M : ℝ := ∫ u in (0 : ℝ)..T₁, h u with hM
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg hT₁pos.le fun u _ => hnn u
  refine ⟨max (|L| + 1) M, le_trans hM0 (le_max_right _ _), fun U hU => ?_⟩
  rcases le_total T₁ U with hle | hle
  · obtain ⟨h1, h2⟩ := hT₀ U (le_trans (le_max_left _ _) hle)
    have hUpos : 0 < U := h2
    have hbound : ∫ u in (0 : ℝ)..U, h u ≤ (L + 1) * U := by
      have := (inv_mul_lt_iff₀ hUpos).1 h1
      linarith
    have hLL : L + 1 ≤ max (|L| + 1) M := le_trans (by linarith [le_abs_self L]) (le_max_left _ _)
    calc ∫ u in (0 : ℝ)..U, h u ≤ (L + 1) * U := hbound
      _ ≤ max (|L| + 1) M * U := by gcongr
      _ ≤ max (|L| + 1) M * (U + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_trans hM0 (le_max_right _ _))
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hh.intervalIntegrable (μ := volume) 0 U) (hh.intervalIntegrable (μ := volume) U T₁)
    have hrest : 0 ≤ ∫ u in U..T₁, h u := intervalIntegral.integral_nonneg hle fun u _ => hnn u
    have hKM : M ≤ max (|L| + 1) M := le_max_right _ _
    have hK0 : 0 ≤ max (|L| + 1) M := le_trans hM0 hKM
    nlinarith

/-- One-sided Landau criterion in `L¹` form: if `∫₀^∞ |G(u)| e^{-τu} du < ∞` for every `τ > 0`,
then RH holds. -/
theorem riemannHypothesis_of_integrableOn_abs_gaussianCentralGapLog
    (hint : ∀ τ : ℝ, 0 < τ →
      IntegrableOn (fun u => |gaussianCentralGapLog u| * Real.exp (-τ * u)) (Ioi 0)) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro z hz
  have hre : 1 / 2 < z.re := mem_rightHalf.mp hz
  refine xi_ne_zero_of_gaussianPrimeExcess (σ := 1 / 2) (by norm_num) (η := 1) (Or.inl rfl)
    (a := 0) le_rfl zero_le_one 0 (fun τ hτ => ?_) (by simpa using hre)
  refine (hint τ hτ).mono' ?_ (Eventually.of_forall fun u => ?_)
  · exact (((continuous_gaussianBudgetProfile (σ := 1 / 2) (by norm_num) 1 0 0).neg.max
      continuous_const).mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (abs_nonneg _)
    simp only [gaussianBudgetProfile, gaussianCentralGapLog, zero_mul, Real.exp_zero, mul_one,
      one_mul, zero_sub, neg_neg]
    exact le_abs_self _

/-- **Mean-square form of the central Gaussian budget.**  The following are equivalent:
RH; linear growth `∫₀^U G² ≤ K (U + 1)`; subexponential growth `∫₀^U G² ≤ K_ε e^{εU}` for each
`ε > 0`.  Under RH the growth is exactly linear, with Cesàro constant given by the Gaussian Cramér
identity. -/
theorem riemannHypothesis_tfae_gaussianCentralGapMeanSquare :
    List.TFAE [
      RiemannHypothesis,
      ∃ K : ℝ, ∀ U : ℝ, 0 ≤ U → ∫ u in (0 : ℝ)..U, gaussianCentralGapLog u ^ 2 ≤ K * (U + 1),
      ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ U : ℝ, 0 ≤ U →
        ∫ u in (0 : ℝ)..U, gaussianCentralGapLog u ^ 2 ≤ K * Real.exp (ε * U)] := by
  tfae_have 1 → 2 := by
    intro hRH
    obtain ⟨K, -, hK⟩ := exists_integral_le_mul_add_one_of_tendsto
      (continuous_gaussianCentralGapLog.pow 2) (fun u => sq_nonneg _)
      (tendsto_centralGap_meanSquare_of_riemannHypothesis hRH)
    exact ⟨K, hK⟩
  tfae_have 2 → 3 := by
    rintro ⟨K, hK⟩ ε hε
    refine ⟨|K| * (1 + ε⁻¹), fun U hU => ?_⟩
    have h1 := hK U hU
    have h2 : U + 1 ≤ (1 + ε⁻¹) * Real.exp (ε * U) := by
      have he := Real.add_one_le_exp (ε * U)
      have hεi : 0 < ε⁻¹ := inv_pos.2 hε
      have hexp1 : 1 ≤ Real.exp (ε * U) := Real.one_le_exp (by positivity)
      have : U ≤ ε⁻¹ * Real.exp (ε * U) := by
        rw [← div_eq_inv_mul, le_div_iff₀ hε]
        nlinarith
      nlinarith
    calc _ ≤ K * (U + 1) := h1
      _ ≤ |K| * (U + 1) := mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
      _ ≤ |K| * ((1 + ε⁻¹) * Real.exp (ε * U)) := by gcongr
      _ = _ := by ring
  tfae_have 3 → 1 := by
    intro h
    refine riemannHypothesis_of_integrableOn_abs_gaussianCentralGapLog fun τ hτ => ?_
    obtain ⟨K, hK⟩ := h τ hτ
    have hK0 : 0 ≤ |K| := abs_nonneg K
    refine integrableOn_abs_mul_exp_of_integral_sq_le continuous_gaussianCentralGapLog hK0 hτ.le
      (fun U hU => (hK U hU).trans (by gcongr; exact le_abs_self K)) (by linarith)
  tfae_finish

end

end RHTower
