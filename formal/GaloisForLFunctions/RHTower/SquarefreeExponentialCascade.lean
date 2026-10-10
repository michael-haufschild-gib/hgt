import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyZeroCascade
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.HTGeometry.BoundedCoefficientLaplaceMellin

/-!
# The exponentially weighted squarefree count and the halving cascade

Let `A(t) = Σ_{n ≥ 1} μ(n)² e^{-nt}` and `c = 6/π²`. Its Mellin transform is
`∫_0^∞ A(t) t^{s-1} dt = Γ(s) ζ(s)/ζ(2s)` for `Re s > 1`. Unlike the sharp count, the weight has a
nonvanishing Mellin transform `Γ(s)`, so no lattice-point term enters.

* **Halving law** (`riemannZeta_half_eq_zero_of_expBound`). If `‖A(t) - c/t‖ ≤ C t^{-α}` on
  `0 < t ≤ 1` with `0 ≤ α < 1`, then every zero `ρ` with `2α < Re ρ < 1` has `ζ(ρ/2) = 0`.
* **Zero-free band** (`riemannZeta_ne_zero_of_expBound`). Hence `ζ` has no zero with `2α < Re s` and
  `2α < 1 - Re s/2` (the cascade `z ↦ 1 - z/2`).
* **Receiver** (`riemannHypothesis_of_expBound_quarter`). `A(t) = c/t + O(t^{-1/4-ε})` for every
  `ε > 0` implies RH.
* **Ω-result** (`not_expBound_of_lt_quarter`). Unconditionally `A(t) - c/t ≠ O(t^{-α})` for every
  `α < 1/4`.

**Proof.** Split `(0, ∞)` at `1`: with `K = 1_{(0,1]}(A - c/t)` and `P = 1_{(1,∞)} A`,
`Γ(s)ζ(s)/ζ(2s) = 𝓜K(s) + 𝓜P(s) + c/(s - 1)` on `Re s > 1`. The bound makes `𝓜K` holomorphic on
`Re s > α`, and `𝓜P` is entire. Clearing poles with `Z(w) = (w - 1)ζ(w)`:
`(s - 1) Z(2s) (𝓜K + 𝓜P)(s) + c Z(2s) = (2s - 1) Γ(s) Z(s)` on `Re s > α`. At `s = ρ/2` the left
side is `0`, and `Γ(ρ/2) ≠ 0`, so `ζ(ρ/2) = 0`.
-/

open Filter Topology MeasureTheory Set Asymptotics Complex
open GaloisForLFunctions.HTGeometry
open scoped LSeries.notation

namespace RHTower.SquarefreeExponential

noncomputable section

/-- The squarefree indicator `μ(n)²` as a complex coefficient sequence. -/
def sqfCoeff (n : ℕ) : ℂ :=
  ((ArithmeticFunction.pmul (ArithmeticFunction.moebius : ArithmeticFunction ℤ)
    ArithmeticFunction.moebius n : ℤ) : ℂ)

/-- `A(t) = Σ_n μ(n)² e^{-nt}`. -/
def profile (t : ℝ) : ℂ := coeffLaplaceProfile sqfCoeff t

/-- The squarefree density `c = 6/π²`. -/
def density : ℂ := (Sieve.squarefreeDensity : ℂ)

theorem norm_sqfCoeff_le (n : ℕ) : ‖sqfCoeff n‖ ≤ 1 := by
  unfold sqfCoeff
  rw [ArithmeticFunction.pmul_apply, Complex.norm_intCast]
  have h : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  push_cast
  rw [abs_mul]
  exact mul_le_one₀ h (abs_nonneg _) h

theorem sqfCoeff_zero : sqfCoeff 0 = 0 := by
  simp [sqfCoeff]

/-- `𝓜A(s) = Γ(s) ζ(s)/ζ(2s)` on `Re s > 1`. -/
theorem mellin_profile {s : ℂ} (hs : 1 < s.re) :
    mellin profile s = Complex.Gamma s * (riemannZeta s / riemannZeta (2 * s)) := by
  show mellin (coeffLaplaceProfile sqfCoeff) s = _
  rw [mellin_coeffLaplaceProfile_eq_gamma_mul_LSeries norm_sqfCoeff_le sqfCoeff_zero hs]
  congr 1
  exact LSeries_squarefree_eq_riemannZeta_div hs

/-! ## The three pieces -/

/-- The error piece `K = 1_{(0,1]} (A - c/t)`. -/
def errorPiece : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator fun t => profile t - density / t

/-- The tail piece `P = 1_{(1,∞)} A`. -/
def tailPiece : ℝ → ℂ := (Ioi (1 : ℝ)).indicator profile

/-- The pole piece `Q = 1_{(0,1]} c/t`. -/
def polePiece : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator fun t => density / t

theorem continuousOn_profile : ContinuousOn profile (Ioi 0) :=
  continuousOn_coeffLaplaceProfile norm_sqfCoeff_le

theorem locallyIntegrableOn_errorPiece : LocallyIntegrableOn errorPiece (Ioi 0) := by
  have hg : ContinuousOn (fun t : ℝ => profile t - density / t) (Ioi 0) :=
    continuousOn_profile.sub (continuousOn_const.div Complex.continuous_ofReal.continuousOn
      fun t ht => by exact_mod_cast (ne_of_gt (mem_Ioi.mp ht)))
  intro x hx
  obtain ⟨u, hu, hint⟩ := hg.locallyIntegrableOn (μ := volume) measurableSet_Ioi x hx
  exact ⟨u, hu, hint.indicator measurableSet_Ioc⟩

theorem locallyIntegrableOn_tailPiece : LocallyIntegrableOn tailPiece (Ioi 0) := by
  intro x hx
  obtain ⟨u, hu, hint⟩ :=
    continuousOn_profile.locallyIntegrableOn (μ := volume) measurableSet_Ioi x hx
  exact ⟨u, hu, hint.indicator measurableSet_Ioi⟩

theorem errorPiece_isBigO_atTop (a : ℝ) : errorPiece =O[atTop] fun t : ℝ => t ^ (-a) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [errorPiece, indicator_of_notMem (fun h => absurd h.2 (not_le.mpr ht)), norm_zero]
  simp

theorem errorPiece_isBigO_zero {α C : ℝ}
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ C * t ^ (-α)) :
    errorPiece =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-α) := by
  refine IsBigO.of_bound |C| ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  have htI : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  rw [errorPiece, indicator_of_mem htI, Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  exact (hB t htI).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
    (Real.rpow_nonneg ht.1.le _))

theorem tailPiece_isBigO_atTop (a : ℝ) : tailPiece =O[atTop] fun t : ℝ => t ^ (-a) := by
  have h1 : tailPiece =O[atTop] fun t : ℝ => Real.exp (-1 * t) := by
    refine (coeffLaplaceProfile_isBigO_exp_neg norm_sqfCoeff_le sqfCoeff_zero).congr' ?_
      EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [tailPiece, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht), profile]
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop one_pos (-a)).isBigO

theorem tailPiece_isBigO_zero (b : ℝ) : tailPiece =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-b) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  rw [tailPiece, indicator_of_notMem (fun h => absurd (mem_Ioi.mp h) (not_lt.mpr ht.2.le)),
    norm_zero]
  simp

/-- `𝓜K` is holomorphic on `Re s > α`. -/
theorem differentiableAt_mellin_errorPiece {α C : ℝ}
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ C * t ^ (-α)) {s : ℂ}
    (hs : α < s.re) : DifferentiableAt ℂ (mellin errorPiece) s :=
  mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_errorPiece
    (errorPiece_isBigO_atTop (s.re + 1)) (by linarith) (errorPiece_isBigO_zero hB) hs

theorem mellinConvergent_errorPiece {α C : ℝ}
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ C * t ^ (-α)) {s : ℂ}
    (hs : α < s.re) : MellinConvergent errorPiece s :=
  mellinConvergent_of_isBigO_rpow locallyIntegrableOn_errorPiece
    (errorPiece_isBigO_atTop (s.re + 1)) (by linarith) (errorPiece_isBigO_zero hB) hs

/-- `𝓜P` is entire. -/
theorem differentiableAt_mellin_tailPiece (s : ℂ) : DifferentiableAt ℂ (mellin tailPiece) s :=
  mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_tailPiece
    (tailPiece_isBigO_atTop (s.re + 1)) (by linarith) (tailPiece_isBigO_zero (s.re - 1))
    (by linarith)

theorem mellinConvergent_tailPiece (s : ℂ) : MellinConvergent tailPiece s :=
  mellinConvergent_of_isBigO_rpow locallyIntegrableOn_tailPiece
    (tailPiece_isBigO_atTop (s.re + 1)) (by linarith) (tailPiece_isBigO_zero (s.re - 1))
    (by linarith)

theorem mellinConvergent_polePiece {s : ℂ} (hs : 1 < s.re) : MellinConvergent polePiece s := by
  have hint : IntegrableOn (fun t : ℝ => density * (t : ℂ) ^ (s - 2)) (Ioc 0 1) := by
    have h := (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) (r := s - 2)
      (by simp; linarith)).const_mul density
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h
  unfold MellinConvergent
  have hcongr : (fun t : ℝ => (t : ℂ) ^ (s - 1) • polePiece t) =
      (Ioc (0 : ℝ) 1).indicator (fun t : ℝ => density * (t : ℂ) ^ (s - 2)) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [polePiece, indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul]
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
      rw [show s - 1 = (s - 2) + 1 by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]
      field_simp
    · rw [polePiece, indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  rw [hcongr, IntegrableOn, integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (Ioc_subset_Ioi_self)]
  exact hint

theorem mellin_polePiece {s : ℂ} (hs : 1 < s.re) : mellin polePiece s = density / (s - 1) := by
  unfold mellin
  have hcongr : (fun t : ℝ => (t : ℂ) ^ (s - 1) • polePiece t) =
      (Ioc (0 : ℝ) 1).indicator (fun t : ℝ => density * (t : ℂ) ^ (s - 2)) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [polePiece, indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul]
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
      rw [show s - 1 = (s - 2) + 1 by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]
      field_simp
    · rw [polePiece, indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  rw [hcongr, integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (Ioc_subset_Ioi_self), integral_const_mul,
    ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (by simp; linarith))]
  have hs1 : s - 2 + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero,
    Complex.zero_cpow hs1, sub_zero, show s - 2 + 1 = s - 1 by ring]
  ring

/-- **Decomposition on `Re s > 1`.** `Γ(s)ζ(s)/ζ(2s) = 𝓜K(s) + 𝓜P(s) + c/(s - 1)`. -/
theorem gamma_zeta_div_eq_of_expBound {α C : ℝ} (hα1 : α ≤ 1)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ C * t ^ (-α)) {s : ℂ}
    (hs : 1 < s.re) :
    Complex.Gamma s * (riemannZeta s / riemannZeta (2 * s)) =
      mellin errorPiece s + mellin tailPiece s + density / (s - 1) := by
  rw [← mellin_profile hs, ← mellin_polePiece hs]
  have hK := mellinConvergent_errorPiece hB (show α < s.re by linarith)
  have hP := mellinConvergent_tailPiece s
  have hQ := mellinConvergent_polePiece hs
  have e : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • profile t =
      ((t : ℂ) ^ (s - 1) • errorPiece t + (t : ℂ) ^ (s - 1) • tailPiece t) +
        (t : ℂ) ^ (s - 1) • polePiece t := by
    intro t ht
    rw [← smul_add, ← smul_add]
    congr 1
    by_cases ht1 : t ≤ 1
    · have htI : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
      rw [errorPiece, polePiece, tailPiece, indicator_of_mem htI, indicator_of_mem htI,
        indicator_of_notMem (fun h => absurd (mem_Ioi.mp h) (not_lt.mpr ht1))]
      ring
    · have htI : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
      rw [errorPiece, polePiece, tailPiece, indicator_of_notMem htI, indicator_of_notMem htI,
        indicator_of_mem (show t ∈ Ioi (1 : ℝ) from not_le.mp ht1)]
      ring
  calc mellin profile s
      = ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ (s - 1) • errorPiece t + (t : ℂ) ^ (s - 1) • tailPiece t) +
          (t : ℂ) ^ (s - 1) • polePiece t := setIntegral_congr_fun measurableSet_Ioi e
    _ = (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • errorPiece t + (t : ℂ) ^ (s - 1) • tailPiece t) +
          ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • polePiece t := integral_add (hK.add hP) hQ
    _ = mellin errorPiece s + mellin tailPiece s + mellin polePiece s := by
          rw [integral_add hK hP]; rfl

/-! ## The pole-cleared identity and the halving law -/

/-- **Pole-cleared identity on `Re s > α`.** -/
theorem pole_cleared_identity {α C : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ C * t ^ (-α)) {s : ℂ}
    (hs : α < s.re) :
    (s - 1) * zetaResidueUnit (2 * s) * (mellin errorPiece s + mellin tailPiece s) +
        density * zetaResidueUnit (2 * s) =
      (2 * s - 1) * Complex.Gamma s * zetaResidueUnit s := by
  set U : Set ℂ := {z : ℂ | α < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hz2 : ∀ z : ℂ, AnalyticAt ℂ (fun w : ℂ => zetaResidueUnit (2 * w)) z := fun z =>
    (analyticAt_zetaResidueUnit (2 * z)).comp (by fun_prop)
  have hK : AnalyticOnNhd ℂ (mellin errorPiece) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    exact (differentiableAt_mellin_errorPiece hB hw).differentiableWithinAt
  have hP : AnalyticOnNhd ℂ (mellin tailPiece) U :=
    DifferentiableOn.analyticOnNhd
      (fun w _ => (differentiableAt_mellin_tailPiece w).differentiableWithinAt) hUo
  have hΓ : AnalyticOnNhd ℂ Complex.Gamma U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    refine (Complex.differentiableAt_Gamma w fun m hm => ?_).differentiableWithinAt
    have hre := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have : α < w.re := hw
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hl : AnalyticOnNhd ℂ (fun z => (z - 1) * zetaResidueUnit (2 * z) *
      (mellin errorPiece z + mellin tailPiece z) + density * zetaResidueUnit (2 * z)) U :=
    fun z hz => (((analyticAt_id.sub analyticAt_const).mul (hz2 z)).mul
      ((hK z hz).add (hP z hz))).add (analyticAt_const.mul (hz2 z))
  have hr : AnalyticOnNhd ℂ (fun z => (2 * z - 1) * Complex.Gamma z * zetaResidueUnit z) U :=
    fun z hz => (((analyticAt_const.mul analyticAt_id).sub analyticAt_const).mul
      (hΓ z hz)).mul (analyticAt_zetaResidueUnit z)
  have hev : (fun z => (z - 1) * zetaResidueUnit (2 * z) *
      (mellin errorPiece z + mellin tailPiece z) + density * zetaResidueUnit (2 * z)) =ᶠ[𝓝 2]
      (fun z => (2 * z - 1) * Complex.Gamma z * zetaResidueUnit z) := by
    have hgt : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with z hz1
    have hz1ne : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hz1; linarith
    have hz2ne : 2 * z ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.mul_re, Complex.one_re] at this
      norm_num at this
      linarith
    have hζ2 : riemannZeta (2 * z) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simp only [Complex.mul_re]; norm_num; linarith)
    have hd : z - 1 ≠ 0 := sub_ne_zero.mpr hz1ne
    have h := gamma_zeta_div_eq_of_expBound hα1 hB hz1
    rw [zetaResidueUnit, Function.update_of_ne hz2ne, Function.update_of_ne hz1ne]
    have hsum : mellin errorPiece z + mellin tailPiece z =
        Complex.Gamma z * (riemannZeta z / riemannZeta (2 * z)) - density / (z - 1) := by
      rw [h]; ring
    rw [hsum]
    have hζ2' : riemannZeta (z * 2) ≠ 0 := by rwa [mul_comm]
    field_simp [hζ2', hd]
    ring
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr (convex_halfSpace_re_gt α).isPreconnected
    (show (2 : ℂ) ∈ U by simp [hU]; linarith) hev hs

/-- **Halving law for the exponential count.** -/
theorem riemannZeta_half_eq_zero_of_expBound {α C : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ C * t ^ (-α)) {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (h2α : 2 * α < ρ.re) (h1 : ρ.re < 1) :
    riemannZeta (ρ / 2) = 0 := by
  have hs : α < (ρ / 2).re := by
    rw [Complex.div_re]; simp; nlinarith [Complex.normSq_nonneg ρ]
  have hid := pole_cleared_identity hα hα1.le hB hs
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at h1; linarith
  have hZρ : zetaResidueUnit ρ = 0 := by
    rw [zetaResidueUnit, Function.update_of_ne hρ1, hz, mul_zero]
  rw [show 2 * (ρ / 2) = ρ by ring, hZρ, mul_zero, zero_mul, mul_zero, add_zero] at hid
  have hΓ : Complex.Gamma (ρ / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hne : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hZ : zetaResidueUnit (ρ / 2) = 0 := by
    rcases mul_eq_zero.mp hid.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hne
      · exact absurd h' hΓ
    · exact h
  have hhalf1 : ρ / 2 ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.div_re] at this
    simp at this
    nlinarith [Complex.normSq_nonneg ρ]
  rw [zetaResidueUnit, Function.update_of_ne hhalf1] at hZ
  rcases mul_eq_zero.mp hZ with h | h
  · exact absurd (sub_eq_zero.mp h) hhalf1
  · exact h

/-! ## Consequences -/

/-- **Zero-free band.** If `‖A(t) - c/t‖ ≤ C t^{-α}` on `(0, 1]` with `0 ≤ α < 1`, then `ζ(s) ≠ 0`
whenever `2α < Re s` and `2α < 1 - Re s/2`. -/
theorem riemannZeta_ne_zero_of_expBound {α C : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ C * t ^ (-α)) {s : ℂ}
    (h1 : 2 * α < s.re) (h2 : 2 * α < 1 - s.re / 2) :
    riemannZeta s ≠ 0 :=
  SquarefreeDiscrepancy.riemannZeta_ne_zero_of_halving hα
    (fun _ hz hre1 hre2 => riemannZeta_half_eq_zero_of_expBound hα hα1 hB hz hre1 hre2) h1 h2

/-- **Receiver.** `A(t) = c/t + O(t^{-1/4-ε})` for every `ε > 0` implies RH. -/
theorem riemannHypothesis_of_expBound_quarter
    (hB : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖profile t - density / t‖ ≤ C * t ^ (-(1 / 4 + ε))) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro s hs hz
  have hs1 : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  set ε : ℝ := min ((s.re - 1 / 2) / 4) ((1 - s.re) / 8) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := hB ε hε0
  have hε1 : ε ≤ (s.re - 1 / 2) / 4 := min_le_left _ _
  have hε2 : ε ≤ (1 - s.re) / 8 := min_le_right _ _
  exact riemannZeta_ne_zero_of_expBound (by linarith) (by linarith) hC (by linarith)
    (by linarith) hz

/-- **Ω-result.** Unconditionally `A(t) - c/t ≠ O(t^{-α})` as `t ↓ 0` for every `α < 1/4`. -/
theorem not_expBound_of_lt_quarter {α : ℝ} (hα : α < 1 / 4) :
    ¬ ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ C * t ^ (-α) := by
  rintro ⟨C, hC⟩
  obtain ⟨s, hs, hz⟩ := ZetaMultiple.exists_riemannZeta_zero_re_half
  have hC' : ∀ t ∈ Ioc (0 : ℝ) 1, ‖profile t - density / t‖ ≤ |C| * t ^ (-(max α 0)) := by
    intro t ht
    calc ‖profile t - density / t‖ ≤ C * t ^ (-α) := hC t ht
      _ ≤ |C| * t ^ (-α) := mul_le_mul_of_nonneg_right (le_abs_self C)
          (Real.rpow_nonneg ht.1.le _)
      _ ≤ |C| * t ^ (-(max α 0)) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith [le_max_left α 0]))
          (abs_nonneg C)
  have hmax : max α 0 < 1 / 4 := max_lt hα (by norm_num)
  exact riemannZeta_ne_zero_of_expBound (le_max_right _ _) (by linarith) hC'
    (by rw [hs]; linarith) (by rw [hs]; linarith) hz

end

end RHTower.SquarefreeExponential
