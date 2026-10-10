import GaloisForLFunctions.RHTower.GaussianTopologicalGateEquivalences

/-!
# Bessel inequality and attainment of the zero abscissa

Let `G(y) = Σ Λ(n) n^{-1/2} e^{-yn²} − ∫₁^∞ u^{-1/2} e^{-yu²} du`, `Θ = sup Re ρ`, and
`g(u) = e^{-(Θ−½)u/2} G(e^{-u})`.

* **Window Bessel inequality** (`norm_gaussianWindowAverage_mul_cexp_sq_le`).
  `|T⁻¹ ∫₀^T f e^{-iτu}|² ≤ T⁻¹ ∫₀^T |f|²`.
* **Extremal Bessel inequality** (`eventually_extremalBohr_sq_le_meanSquare`).  For every `τ` and
  `ε > 0`, eventually `|A(½)·[Θ = ½, τ = 0] − Σ_{Re ρ = Θ, Im ρ = 2τ} ½Γ((ρ−½)/2)|² − ε ≤ T⁻¹∫₀^T g²`.
  The squared extremal zero amplitudes are dominated by the prime-side mean square.
* **Attainment criterion** (`extremal_zero_exists_iff_not_tendsto_meanSquare`).  If `Θ > ½`, then `ξ`
  has a zero on `Re ρ = Θ` iff the window means `T⁻¹ ∫₀^T g²` do not tend to `0`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- **Window Bessel inequality.**  For continuous `f` and `T > 0`,
`‖T⁻¹ ∫₀^T f e^{-iτu}‖² ≤ T⁻¹ ∫₀^T ‖f‖²`. -/
theorem norm_gaussianWindowAverage_mul_cexp_sq_le {f : ℝ → ℂ} (hf : Continuous f) (τ : ℝ)
    {T : ℝ} (hT : 0 < T) :
    ‖gaussianWindowAverage (fun u => f u * Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) T‖ ^ 2 ≤
      T⁻¹ * ∫ u in (0 : ℝ)..T, ‖f u‖ ^ 2 := by
  set m : ℝ := T⁻¹ * ∫ u in (0 : ℝ)..T, ‖f u‖ with hm
  have hnf : Continuous fun u => ‖f u‖ := hf.norm
  have h1 : ‖gaussianWindowAverage (fun u => f u * Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) T‖
      ≤ m := by
    rw [gaussianWindowAverage, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hT, hm]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hT.le)
    refine (intervalIntegral.norm_integral_le_integral_norm hT.le).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one]
  have hm0 : 0 ≤ m := (norm_nonneg _).trans h1
  -- `∫ (‖f‖ - m)² ≥ 0` gives `m² T ≤ ∫ ‖f‖²`
  have hsq : 0 ≤ ∫ u in (0 : ℝ)..T, (‖f u‖ - m) ^ 2 :=
    intervalIntegral.integral_nonneg hT.le fun u _ => sq_nonneg _
  have hexp : ∫ u in (0 : ℝ)..T, (‖f u‖ - m) ^ 2 =
      (∫ u in (0 : ℝ)..T, ‖f u‖ ^ 2) - 2 * m * (∫ u in (0 : ℝ)..T, ‖f u‖) + m ^ 2 * T := by
    have e1 : (fun u => (‖f u‖ - m) ^ 2) =
        fun u => (‖f u‖ ^ 2 - 2 * m * ‖f u‖) + m ^ 2 := by funext u; ring
    have i1 : IntervalIntegrable (fun u => ‖f u‖ ^ 2 - 2 * m * ‖f u‖) volume 0 T :=
      ((hnf.pow 2).sub (continuous_const.mul hnf)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun u => ‖f u‖ ^ 2) volume 0 T :=
      (hnf.pow 2).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun u => 2 * m * ‖f u‖) volume 0 T :=
      (continuous_const.mul hnf).intervalIntegrable _ _
    rw [e1, intervalIntegral.integral_add i1 intervalIntegrable_const,
      intervalIntegral.integral_sub i2 i3, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  have hint : ∫ u in (0 : ℝ)..T, ‖f u‖ = m * T := by
    rw [hm]; field_simp
  rw [hexp, hint] at hsq
  have hfinal : m ^ 2 ≤ T⁻¹ * ∫ u in (0 : ℝ)..T, ‖f u‖ ^ 2 := by
    rw [le_inv_mul_iff₀ hT]
    nlinarith
  calc _ ≤ m ^ 2 := by gcongr
    _ ≤ _ := hfinal

/-- The extremal decomposition at `θ = Θ`, stated for the weighted gap. -/
theorem tendsto_extremalGap_add_series :
    Tendsto (fun u : ℝ =>
        ((Real.exp (-((xiZeroAbscissa - 1 / 2) * u / 2)) *
          (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
            gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) : ℝ) : ℂ) +
        (∑' q : XiZeroCopy, (if (xiZero q).re = xiZeroAbscissa then zeroBohrAmplitude q else 0) *
          Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ))) -
        (((if xiZeroAbscissa = 1 / 2 then 1 else 0 : ℝ)) : ℂ) *
          gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ))
      atTop (𝓝 0) :=
  tendsto_weightedGap_add_extremalSeries fun _ hρ => re_le_xiZeroAbscissa hρ

/-- **Extremal Bessel inequality.**  For every `τ` and `ε > 0`, eventually in `T`,
`‖A(½)·[Θ = ½ ∧ τ = 0] − weightedBohrCoefficient Θ τ‖² − ε ≤ T⁻¹ ∫₀^T g(u)² du`. -/
theorem eventually_extremalBohr_sq_le_meanSquare (τ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop,
      ‖(if xiZeroAbscissa = 1 / 2 ∧ τ = 0 then gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ)
        else 0) - weightedBohrCoefficient xiZeroAbscissa τ‖ ^ 2 - ε ≤
      T⁻¹ * ∫ u in (0 : ℝ)..T, (Real.exp (-((xiZeroAbscissa - 1 / 2) * u / 2)) *
        (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)))) ^ 2 := by
  set g : ℝ → ℝ := fun u => Real.exp (-((xiZeroAbscissa - 1 / 2) * u / 2)) *
    (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
      gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) with hgdef
  have hGcont : Continuous fun u : ℝ => gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
      gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)) := by
    have h := continuous_gaussianBudgetProfile (σ := 1 / 2) (by norm_num) (-1) 0 0
    have heq : (fun u : ℝ => gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
        gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) =
        gaussianBudgetProfile (-1) (1 / 2) 0 0 := by
      funext u; simp [gaussianBudgetProfile]
    rw [heq]; exact h
  have hgcont : Continuous g := (by fun_prop : Continuous fun u : ℝ =>
    Real.exp (-((xiZeroAbscissa - 1 / 2) * u / 2))).mul hGcont
  set C : ℂ := (if xiZeroAbscissa = 1 / 2 ∧ τ = 0 then gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ)
    else 0) - weightedBohrCoefficient xiZeroAbscissa τ with hC
  have hlim : Tendsto (gaussianWindowAverage fun u => ((g u : ℝ) : ℂ) *
      Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) atTop (𝓝 C) :=
    tendsto_gaussianWindowAverage_extremalGap τ
  have hnorm := (continuous_norm.tendsto C).comp hlim
  have hsq := (hnorm.pow 2)
  have hev := hsq.eventually (lt_mem_nhds (show ‖C‖ ^ 2 - ε < ‖C‖ ^ 2 by linarith))
  filter_upwards [hev, eventually_gt_atTop 0] with T hT hT0
  simp only [Function.comp] at hT
  have hb := norm_gaussianWindowAverage_mul_cexp_sq_le
    (Complex.continuous_ofReal.comp hgcont) τ hT0
  have heq : (fun u => ‖((g u : ℝ) : ℂ)‖ ^ 2) = fun u => g u ^ 2 := by
    funext u; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [Function.comp] at hb
  rw [heq] at hb
  linarith

/-- **Attainment criterion.**  If `Θ > ½`, then `ξ` has a zero on the line `Re ρ = Θ` iff the
window means of `g(u)² = e^{-(Θ−½)u} G(e^{-u})²` do not tend to `0`. -/
theorem extremal_zero_exists_iff_not_tendsto_meanSquare (hΘ : 1 / 2 < xiZeroAbscissa) :
    (∃ ρ : ℂ, xi ρ = 0 ∧ ρ.re = xiZeroAbscissa) ↔
      ¬ Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0 : ℝ)..T,
        (Real.exp (-((xiZeroAbscissa - 1 / 2) * u / 2)) *
          (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
            gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)))) ^ 2) atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun u => Real.exp (-((xiZeroAbscissa - 1 / 2) * u / 2)) *
    (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
      gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) with hgdef
  have hne : xiZeroAbscissa ≠ 1 / 2 := ne_of_gt hΘ
  constructor
  · rintro ⟨ρ₀, hρ₀, hre⟩ htend
    set C : ℂ := (if xiZeroAbscissa = 1 / 2 ∧ ρ₀.im / 2 = 0 then
      gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ) else 0) -
        weightedBohrCoefficient xiZeroAbscissa (ρ₀.im / 2) with hC
    have hC0 : C ≠ 0 := by
      rw [hC, if_neg (fun h => hne h.1), zero_sub, neg_ne_zero]
      exact weightedBohrCoefficient_ne_zero_of_xi_eq_zero hρ₀ hre
    have hpos : 0 < ‖C‖ ^ 2 := by positivity
    have hev := eventually_extremalBohr_sq_le_meanSquare (ρ₀.im / 2)
      (ε := ‖C‖ ^ 2 / 2) (by positivity)
    have hsmall := htend.eventually (gt_mem_nhds (show (0 : ℝ) < ‖C‖ ^ 2 / 2 by positivity))
    obtain ⟨T, hT1, hT2⟩ := (hev.and hsmall).exists
    rw [← hC] at hT1
    linarith
  · intro hnot
    by_contra hno
    push Not at hno
    apply hnot
    -- with no zero on the extremal line, the weighted gap tends to `0`
    have hlim := tendsto_extremalGap_add_series
    have hzero : ∀ u : ℝ, (∑' q : XiZeroCopy,
        (if (xiZero q).re = xiZeroAbscissa then zeroBohrAmplitude q else 0) *
          Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ))) = 0 := by
      intro u
      have hall : ∀ q : XiZeroCopy, (xiZero q).re ≠ xiZeroAbscissa := fun q h =>
        hno (xiZero q) (xi_xiZero q) h
      simp [hall]
    have hg0 : Tendsto (fun u => ((g u : ℝ) : ℂ)) atTop (𝓝 0) := by
      refine hlim.congr fun u => ?_
      rw [hzero u, if_neg hne]
      simp [hgdef]
    have hg2 : Tendsto (fun u => (((g u) ^ 2 : ℝ) : ℂ)) atTop (𝓝 0) := by
      have := hg0.pow 2
      rw [zero_pow two_ne_zero] at this
      exact this.congr fun u => by push_cast; ring
    have hcont : Continuous fun u => (((g u) ^ 2 : ℝ) : ℂ) := by
      have hGcont : Continuous fun u : ℝ => gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)) := by
        have h := continuous_gaussianBudgetProfile (σ := 1 / 2) (by norm_num) (-1) 0 0
        have heq : (fun u : ℝ => gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
            gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) =
            gaussianBudgetProfile (-1) (1 / 2) 0 0 := by
          funext u; simp [gaussianBudgetProfile]
        rw [heq]; exact h
      have hgcont : Continuous g := (by fun_prop : Continuous fun u : ℝ =>
        Real.exp (-((xiZeroAbscissa - 1 / 2) * u / 2))).mul hGcont
      exact Complex.continuous_ofReal.comp (hgcont.pow 2)
    have havg := tendsto_gaussianWindowAverage_of_tendsto_zero hcont hg2
    have hre := (Complex.continuous_re.tendsto 0).comp havg
    rw [Complex.zero_re] at hre
    refine hre.congr fun T => ?_
    simp only [Function.comp, gaussianWindowAverage]
    rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re]

end

end RHTower
