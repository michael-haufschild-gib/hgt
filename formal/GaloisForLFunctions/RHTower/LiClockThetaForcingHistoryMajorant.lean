import GaloisForLFunctions.RHTower.LiClockThetaForcingRatioShape

/-!
# The literal forcing history majorants: cofinal failure and exact origin law

The first-crossing laws `g(T) = (y ⋆ K)(T)`, `y'(T) = g'(T) - (y ⋆ K')(T)` suggest the source-level
majorants `g ⋆ K < g` and `g ⋆ K' < g'`.  Both fail cofinally for the literal `g`, even with any
finite factor: `g`, `g'`, `K`, `K'` have every positive exponential type, so their Laplace transforms
exist for every `p > 0`, with `K̂' = pK̂`, `ĝ' = pĝ` and `(g ⋆ K)^ = ĝK̂`, `(g ⋆ K')^ = ĝ p K̂`.  An
eventual bound by `A g` (resp. `A g'`) would bound `K̂(p)` by `O(1)` (resp. `O(1/p)`) as `p ↓ 0`,
contradicting `K̂(p) ≥ c₁/p²`.

At the origin the comparisons do hold: with `a = g'(0) = ω²M₀ + M₁` and `b = K'(0) = ν₁/2`,
`(g ⋆ K)(t) = ab t³/6 + O(t⁵)`, `(g ⋆ K')(t) = ab t²/2 + O(t⁴)`, hence
`(g ⋆ K)/g = ν₁t²/12 + O(t⁴)` and `(g ⋆ K')/g' = ν₁t²/4 + O(t⁴)`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ContDiff

noncomputable section

namespace RHTower

/-! ## Laplace transforms of factorial series -/

theorem hasSum_integral_Ioi_oddFactorialSeries_mul_exp_neg {a : ℕ → ℝ} {M₀ R₀ M R p : ℝ}
    (hR₀ : 0 ≤ R₀) (ha₀ : GeometricCoeffBound a M₀ R₀) (hb : GeometricCoeffBound (oddSpread a) M R)
    (hR : 0 ≤ R) (hRp : R < p) :
    HasSum (fun k : ℕ => a k * (p ^ (2 * k + 2))⁻¹)
      (∫ t in Ioi (0 : ℝ), oddFactorialSeries a t * Real.exp (-(p * t))) := by
  have h := hasSum_integral_Ioi_borelSeries_mul_exp_neg hb hR hRp
  rw [← oddFactorialSeries_eq_borelSeries hR₀ ha₀] at h
  set f : ℕ → ℝ := fun N => oddSpread a N * (p ^ (N + 1))⁻¹ with hfdef
  have hodd : Summable fun k : ℕ => f (2 * k + 1) :=
    h.summable.comp_injective (i := fun k : ℕ => 2 * k + 1) fun x y hxy => by simpa using hxy
  have heven : HasSum (fun k : ℕ => f (2 * k)) 0 := by
    simp only [hfdef, oddSpread_two_mul, zero_mul]; exact hasSum_zero
  have hall := heven.even_add_odd hodd.hasSum
  rw [zero_add] at hall
  rw [h.unique hall]
  exact hodd.hasSum.congr_fun fun k => by simp [hfdef]

theorem hasSum_integral_Ioi_evenFactorialSeries_mul_exp_neg {a : ℕ → ℝ} {M₀ R₀ M R p : ℝ}
    (hR₀ : 0 ≤ R₀) (ha₀ : GeometricCoeffBound a M₀ R₀) (hb : GeometricCoeffBound (evenSpread a) M R)
    (hR : 0 ≤ R) (hRp : R < p) :
    HasSum (fun k : ℕ => a k * (p ^ (2 * k + 1))⁻¹)
      (∫ t in Ioi (0 : ℝ), evenFactorialSeries a t * Real.exp (-(p * t))) := by
  have h := hasSum_integral_Ioi_borelSeries_mul_exp_neg hb hR hRp
  rw [← evenFactorialSeries_eq_borelSeries hR₀ ha₀] at h
  set f : ℕ → ℝ := fun N => evenSpread a N * (p ^ (N + 1))⁻¹ with hfdef
  have heven : Summable fun k : ℕ => f (2 * k) :=
    h.summable.comp_injective (i := fun k : ℕ => 2 * k) fun x y hxy => by simpa using hxy
  have hodd : HasSum (fun k : ℕ => f (2 * k + 1)) 0 := by
    simp only [hfdef, evenSpread_two_mul_add_one, zero_mul]; exact hasSum_zero
  have hall := heven.hasSum.even_add_odd hodd
  rw [add_zero] at hall
  rw [h.unique hall]
  exact heven.hasSum.congr_fun fun k => by simp [hfdef]

private theorem hγ : GeometricCoeffBound (fun m => -liClockThetaForcingTaylorCoeff (m + 1))
    ((2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1) 1 :=
  fun m => by rw [abs_neg]; exact geometricCoeffBound_liClockThetaForcingTaylorCoeff.shift m

private theorem hκ : GeometricCoeffBound (fun m => liClockThetaGeneratorCoeff (m + 1))
    (1 * (32 / 303)) (32 / 303) := geometricCoeffBound_liClockThetaGeneratorCoeff.shift

private theorem hγ_small {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    |-liClockThetaForcingTaylorCoeff (k + 1)| ≤
      (Real.exp (32 / (303 * (ρ / 2) ^ 2)) * (2 * (ρ / 2) ^ 2 +
        2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * ρ ^ 2) *
          ρ ^ (2 * k) := by
  rw [abs_neg]
  have := abs_liClockThetaForcingTaylorCoeff_le_pow (ρ := ρ / 2) (by positivity) (k + 1)
  rw [show 2 * (ρ / 2) = ρ by ring, show 2 * (k + 1) = 2 + 2 * k by ring, pow_add] at this
  calc _ ≤ _ := this
    _ = _ := by ring

private theorem hκ_small {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    |liClockThetaGeneratorCoeff (k + 1)| ≤
      (Real.exp (32 / (303 * ρ ^ 2)) * ρ ^ 2) * ρ ^ (2 * k) := by
  rw [abs_of_pos (liClockThetaGeneratorCoeff_pos _)]
  have := liClockThetaGeneratorCoeff_le_pow hρ (k + 1)
  rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add] at this
  calc _ ≤ _ := this
    _ = _ := by ring

/-- `ĝ(p) = Σ_k (-e_{k+1}) p^{-2k-2}` for every `p > 0`. -/
theorem hasSum_integral_Ioi_liClockThetaForcingInput {p : ℝ} (hp : 0 < p) :
    HasSum (fun k : ℕ => -liClockThetaForcingTaylorCoeff (k + 1) * (p ^ (2 * k + 2))⁻¹)
      (∫ t in Ioi (0 : ℝ), liClockThetaForcingInput t * Real.exp (-(p * t))) :=
  hasSum_integral_Ioi_oddFactorialSeries_mul_exp_neg (by norm_num) hγ
    (geometricCoeffBound_oddSpread_of_le (half_pos hp) (hγ_small (half_pos hp))) (by positivity)
    (by linarith)

theorem hasSum_integral_Ioi_liClockThetaForcingInputDeriv {p : ℝ} (hp : 0 < p) :
    HasSum (fun k : ℕ => -liClockThetaForcingTaylorCoeff (k + 1) * (p ^ (2 * k + 1))⁻¹)
      (∫ t in Ioi (0 : ℝ), liClockThetaForcingInputDeriv t * Real.exp (-(p * t))) :=
  hasSum_integral_Ioi_evenFactorialSeries_mul_exp_neg (by norm_num) hγ
    (geometricCoeffBound_evenSpread_of_le (half_pos hp) (hγ_small (half_pos hp))) (by positivity)
    (by linarith)

theorem hasSum_integral_Ioi_liClockThetaKernelDeriv {p : ℝ} (hp : 0 < p) :
    HasSum (fun k : ℕ => liClockThetaGeneratorCoeff (k + 1) * (p ^ (2 * k + 1))⁻¹)
      (∫ t in Ioi (0 : ℝ), liClockThetaKernelDeriv t * Real.exp (-(p * t))) :=
  hasSum_integral_Ioi_evenFactorialSeries_mul_exp_neg (by norm_num) hκ
    (geometricCoeffBound_evenSpread_of_le (half_pos hp) (hκ_small (half_pos hp))) (by positivity)
    (by linarith)

/-- `ĝ'(p) = p ĝ(p)`. -/
theorem integral_liClockThetaForcingInputDeriv_eq {p : ℝ} (hp : 0 < p) :
    ∫ t in Ioi (0 : ℝ), liClockThetaForcingInputDeriv t * Real.exp (-(p * t)) =
      p * ∫ t in Ioi (0 : ℝ), liClockThetaForcingInput t * Real.exp (-(p * t)) := by
  refine (hasSum_integral_Ioi_liClockThetaForcingInputDeriv hp).unique ?_
  refine ((hasSum_integral_Ioi_liClockThetaForcingInput hp).mul_left p).congr_fun fun k => ?_
  have hp0 : p ≠ 0 := hp.ne'
  rw [pow_succ p (2 * k + 1)]
  field_simp

/-- `K̂'(p) = p K̂(p)`. -/
theorem integral_liClockThetaKernelDeriv_eq {p : ℝ} (hp : 0 < p) :
    ∫ t in Ioi (0 : ℝ), liClockThetaKernelDeriv t * Real.exp (-(p * t)) =
      p * ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t)) := by
  refine (hasSum_integral_Ioi_liClockThetaKernelDeriv hp).unique ?_
  refine ((hasSum_integral_Ioi_liClockThetaKernel_mul_exp_neg hp).mul_left p).congr_fun fun k => ?_
  have hp0 : p ≠ 0 := hp.ne'
  rw [pow_succ p (2 * k + 1)]
  field_simp

/-! ## Laplace transform of a nonnegative convolution -/

private theorem complex_integral_eq_ofReal'' (p : ℝ) (f : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-((p : ℂ) * t)) * (f t : ℂ) =
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * f t : ℝ) : ℂ) := by
  have h1 : ∫ t in Ioi (0 : ℝ), Complex.exp (-((p : ℂ) * t)) * (f t : ℂ) =
      ∫ t in Ioi (0 : ℝ), ((Real.exp (-(p * t)) * f t : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by push_cast; ring_nf
  rw [h1]
  exact integral_ofReal

/-- For continuous `f, k ≥ 0` on `[0,∞)` with integrable `e^{-pt}f`, `e^{-pt}k`:
`∫ e^{-pt}(f ⋆ k) = (∫ e^{-pt} f)(∫ e^{-pt} k)`. -/
theorem integral_exp_mul_volterraConv_of_nonneg {f k : ℝ → ℝ} (hf : Continuous f)
    (hk : Continuous k) (hf0 : ∀ t, 0 ≤ t → 0 ≤ f t) (hk0 : ∀ t, 0 ≤ t → 0 ≤ k t) {p : ℝ}
    (hfi : IntegrableOn (fun t => Real.exp (-(p * t)) * f t) (Ioi 0))
    (hki : IntegrableOn (fun t => Real.exp (-(p * t)) * k t) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * volterraConv f k t =
      (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * f t) *
        ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * k t := by
  have hfi' : IntegrableOn (fun t => Real.exp (-((p : ℂ).re * t)) * |f t|) (Ioi 0) :=
    hfi.congr_fun (fun t ht => by
      simp only [Complex.ofReal_re]; rw [abs_of_nonneg (hf0 t (le_of_lt ht))]) measurableSet_Ioi
  have hki' : IntegrableOn (fun t => Real.exp (-((p : ℂ).re * t)) * |k t|) (Ioi 0) :=
    hki.congr_fun (fun t ht => by
      simp only [Complex.ofReal_re]; rw [abs_of_nonneg (hk0 t (le_of_lt ht))]) measurableSet_Ioi
  have h := integral_Ioi_cexp_mul_volterraConv hf hk hfi' hki'
  rw [complex_integral_eq_ofReal'', complex_integral_eq_ofReal'', complex_integral_eq_ofReal'',
    ← Complex.ofReal_mul] at h
  exact_mod_cast h

private theorem volterraConv_nonneg' {f k : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hk0 : ∀ t, 0 ≤ t → 0 ≤ k t) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ volterraConv f k t := by
  unfold volterraConv
  exact intervalIntegral.integral_nonneg ht fun s hs =>
    mul_nonneg (hf0 _ (by linarith [hs.2])) (hk0 _ hs.1)

/-! ## Cofinal failure of the history majorants -/

private theorem forcingInput_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ liClockThetaForcingInput t := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, liClockThetaForcingInput_zero]
  · exact (liClockThetaForcingInput_pos h).le

private theorem integrableOn_exp_mul_of_hasSum {f : ℝ → ℝ} {p : ℝ}
    (h : IntegrableOn (fun t => f t * Real.exp (-(p * t))) (Ioi 0)) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * f t) (Ioi 0) :=
  h.congr_fun (fun _ _ => mul_comm _ _) measurableSet_Ioi

private theorem integrableOn_forcingInput {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaForcingInput t) (Ioi 0) := by
  have hb := geometricCoeffBound_oddSpread_of_le (half_pos hp) (hγ_small (half_pos hp))
  refine integrableOn_exp_mul_of_hasSum ?_
  unfold liClockThetaForcingInput
  rw [oddFactorialSeries_eq_borelSeries (by norm_num) hγ]
  exact integrableOn_borelSeries_mul_exp_neg hb (by linarith)

private theorem integrableOn_forcingInputDeriv {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaForcingInputDeriv t) (Ioi 0) := by
  have hb := geometricCoeffBound_evenSpread_of_le (half_pos hp) (hγ_small (half_pos hp))
  refine integrableOn_exp_mul_of_hasSum ?_
  unfold liClockThetaForcingInputDeriv
  rw [evenFactorialSeries_eq_borelSeries (by norm_num) hγ]
  exact integrableOn_borelSeries_mul_exp_neg hb (by linarith)

private theorem integrableOn_kernelDeriv {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaKernelDeriv t) (Ioi 0) := by
  have hb := geometricCoeffBound_evenSpread_of_le (half_pos hp) (hκ_small (half_pos hp))
  refine integrableOn_exp_mul_of_hasSum ?_
  unfold liClockThetaKernelDeriv
  rw [evenFactorialSeries_eq_borelSeries (by norm_num) hκ]
  exact integrableOn_borelSeries_mul_exp_neg hb (by linarith)

private theorem integral_comm' (p : ℝ) (f : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), f t * Real.exp (-(p * t)) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * f t :=
  setIntegral_congr_fun measurableSet_Ioi fun _ _ => mul_comm _ _

/-- A uniform lower bound for the forcing transform on `0 < p ≤ 1`. -/
private theorem exists_forcingInput_laplace_lower :
    ∃ G₁ > 0, ∀ p, 0 < p → p ≤ 1 →
      G₁ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaForcingInput t := by
  have hcont : Continuous fun t => Real.exp (-t) * liClockThetaForcingInput t :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-t)).mul
      (contDiff_liClockThetaForcingInput.continuous)
  refine ⟨∫ t in (0 : ℝ)..1, Real.exp (-t) * liClockThetaForcingInput t, ?_, fun p hp hp1 => ?_⟩
  · exact intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _)
      (fun x hx => mul_pos (Real.exp_pos _) (liClockThetaForcingInput_pos hx.1)) one_pos
  · have hi := integrableOn_forcingInput hp
    rw [intervalIntegral.integral_of_le zero_le_one]
    calc ∫ t in Ioc (0 : ℝ) 1, Real.exp (-t) * liClockThetaForcingInput t ≤
        ∫ t in Ioc (0 : ℝ) 1, Real.exp (-(p * t)) * liClockThetaForcingInput t :=
          setIntegral_mono_on hcont.integrableOn_Ioc (hi.mono_set Ioc_subset_Ioi_self)
            measurableSet_Ioc fun t ht => mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.2 (by nlinarith [ht.1, ht.2])) (forcingInput_nonneg ht.1.le)
      _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaForcingInput t :=
          setIntegral_mono_set hi (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
            mul_nonneg (Real.exp_pos _).le (forcingInput_nonneg (le_of_lt ht)))
            (Eventually.of_forall fun x hx => Ioc_subset_Ioi_self hx)

/-- Splitting a weighted half-line integral at `T ≥ 0`, with a pointwise tail bound. -/
private theorem integral_split_le {u v : ℝ → ℝ} (hu : Continuous u)
    (hu0 : ∀ t, 0 ≤ t → 0 ≤ u t) {p T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hui : IntegrableOn (fun t => Real.exp (-(p * t)) * u t) (Ioi 0))
    (hvi : IntegrableOn (fun t => Real.exp (-(p * t)) * v t) (Ioi 0))
    (hv0 : ∀ t, 0 ≤ t → 0 ≤ v t) (hp : 0 < p) (htail : ∀ t, T < t → u t ≤ A * v t) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * u t ≤
      (∫ t in Ioc (0 : ℝ) T, u t) + A * ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * v t := by
  have hsplit : ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * u t =
      (∫ t in Ioc (0 : ℝ) T, Real.exp (-(p * t)) * u t) +
        ∫ t in Ioi T, Real.exp (-(p * t)) * u t := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hui.mono_set Ioc_subset_Ioi_self) (hui.mono_set (Ioi_subset_Ioi hT)),
      Ioc_union_Ioi_eq_Ioi hT]
  have h1 : ∫ t in Ioc (0 : ℝ) T, Real.exp (-(p * t)) * u t ≤ ∫ t in Ioc (0 : ℝ) T, u t :=
    setIntegral_mono_on (hui.mono_set Ioc_subset_Ioi_self) hu.integrableOn_Ioc measurableSet_Ioc
      fun t ht => by
        have := hu0 t ht.1.le
        have he : Real.exp (-(p * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
        nlinarith
  have h2 : ∫ t in Ioi T, Real.exp (-(p * t)) * u t ≤
      ∫ t in Ioi T, A * (Real.exp (-(p * t)) * v t) :=
    setIntegral_mono_on (hui.mono_set (Ioi_subset_Ioi hT)) ((hvi.mono_set (Ioi_subset_Ioi hT)).const_mul A)
      measurableSet_Ioi fun t ht => by
        have := htail t ht
        have he := (Real.exp_pos (-(p * t))).le
        nlinarith
  have h3 : ∫ t in Ioi T, A * (Real.exp (-(p * t)) * v t) ≤
      A * ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * v t := by
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hA
    exact setIntegral_mono_set hvi (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      mul_nonneg (Real.exp_pos _).le (hv0 t (le_of_lt ht)))
      (Eventually.of_forall fun x hx => Ioi_subset_Ioi hT hx)
  linarith

/-- **Cofinal failure of `g ⋆ K ≤ A g`.**  For every `A` and `T` some clock `t > T` has
`(g ⋆ K)(t) > A g(t)`. -/
theorem exists_liClockThetaForcingInput_conv_kernel_gt (A T : ℝ) :
    ∃ t, T < t ∧ A * liClockThetaForcingInput t <
      volterraConv liClockThetaForcingInput liClockThetaKernel t := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  set T' := max T 0
  set A' := max A 0
  have htail : ∀ t, T' < t → volterraConv liClockThetaForcingInput liClockThetaKernel t ≤
      A' * liClockThetaForcingInput t := fun t ht => by
    have h := hcon t (lt_of_le_of_lt (le_max_left _ _) ht)
    have hg := forcingInput_nonneg (show 0 ≤ t by linarith [le_max_right T 0])
    nlinarith [le_max_left A 0]
  obtain ⟨G₁, hG₁, hG⟩ := exists_forcingInput_laplace_lower
  set CT := ∫ t in Ioc (0 : ℝ) T', volterraConv liClockThetaForcingInput liClockThetaKernel t
  have hCT : 0 ≤ CT := setIntegral_nonneg measurableSet_Ioc fun t ht =>
    volterraConv_nonneg' (fun s hs => forcingInput_nonneg hs)
      (fun s hs => liClockThetaKernel_nonneg hs) ht.1.le
  have hc1 := liClockThetaGeneratorCoeff_one_pos
  have hbound : ∀ p, 0 < p → p ≤ 1 → liClockThetaGeneratorCoeff 1 * (p ^ 2)⁻¹ ≤ CT / G₁ + A' := by
    intro p hp hp1
    have hgi := integrableOn_forcingInput hp
    have hKi : IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaKernel t) (Ioi 0) :=
      integrableOn_exp_mul_of_hasSum (integrableOn_liClockThetaKernel_mul_exp_neg hp)
    have hconv := integral_exp_mul_volterraConv_of_nonneg
      (contDiff_liClockThetaForcingInput.continuous) continuous_liClockThetaKernel
      (fun t ht => forcingInput_nonneg ht) (fun t ht => liClockThetaKernel_nonneg ht) hgi hKi
    have hci : IntegrableOn (fun t => Real.exp (-(p * t)) *
        volterraConv liClockThetaForcingInput liClockThetaKernel t) (Ioi 0) := by
      have := integrableOn_volterraConv_of_nonneg
        ((by fun_prop : Continuous fun t : ℝ => Real.exp (-p * t)).mul
          contDiff_liClockThetaForcingInput.continuous)
        ((by fun_prop : Continuous fun t : ℝ => Real.exp (-p * t)).mul continuous_liClockThetaKernel)
        (fun t ht => mul_nonneg (Real.exp_pos _).le (forcingInput_nonneg ht))
        (fun t ht => mul_nonneg (Real.exp_pos _).le (liClockThetaKernel_nonneg ht))
        (hgi.congr_fun (fun t _ => by simp only [Pi.mul_apply]; ring_nf) measurableSet_Ioi)
        (hKi.congr_fun (fun t _ => by simp only [Pi.mul_apply]; ring_nf) measurableSet_Ioi)
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      show volterraConv (fun s => Real.exp (-p * s) * liClockThetaForcingInput s)
        (fun s => Real.exp (-p * s) * liClockThetaKernel s) t = _
      rw [← exp_mul_volterraConv]; ring_nf
    have hsplit := integral_split_le (u := volterraConv liClockThetaForcingInput liClockThetaKernel)
      (v := liClockThetaForcingInput)
      (continuous_volterraConv contDiff_liClockThetaForcingInput.continuous
        continuous_liClockThetaKernel)
      (fun t ht => volterraConv_nonneg' (fun s hs => forcingInput_nonneg hs)
        (fun s hs => liClockThetaKernel_nonneg hs) ht)
      (le_max_right T 0) (le_max_right A 0) hci hgi (fun t ht => forcingInput_nonneg ht) hp htail
    rw [hconv] at hsplit
    have hGp := hG p hp hp1
    have hKlow := liClockThetaGeneratorCoeff_one_div_sq_le_integral hp
    rw [integral_comm'] at hKlow
    set Gp := ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaForcingInput t
    set Kp := ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaKernel t
    have hGp0 : 0 < Gp := hG₁.trans_le hGp
    have hK : Kp ≤ CT / Gp + A' := by
      rw [div_add' _ _ _ hGp0.ne', le_div_iff₀ hGp0]; linarith
    have hCT' : CT / Gp ≤ CT / G₁ := div_le_div_of_nonneg_left hCT hG₁ hGp
    linarith
  set B := CT / G₁ + A' + 1
  have hB : 0 < B := by have : 0 ≤ CT / G₁ := div_nonneg hCT hG₁.le
                        have : 0 ≤ A' := le_max_right A 0
                        positivity
  set p := min 1 (liClockThetaGeneratorCoeff 1 / (2 * B))
  have hp : 0 < p := lt_min one_pos (by positivity)
  have hp1 : p ≤ 1 := min_le_left _ _
  have hp2 : p ≤ liClockThetaGeneratorCoeff 1 / (2 * B) := min_le_right _ _
  have h := hbound p hp hp1
  have hpp : p ^ 2 ≤ p := by nlinarith
  have : liClockThetaGeneratorCoeff 1 * (p ^ 2)⁻¹ ≥ 2 * B := by
    rw [ge_iff_le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have : p * (2 * B) ≤ liClockThetaGeneratorCoeff 1 := by
      rw [le_div_iff₀ (by positivity)] at hp2; linarith
    nlinarith
  linarith

/-- **Cofinal failure of `g ⋆ K' ≤ A g'`.**  For every `A` and `T` some clock `t > T` has
`(g ⋆ K')(t) > A g'(t)`. -/
theorem exists_liClockThetaForcingInput_conv_kernelDeriv_gt (A T : ℝ) :
    ∃ t, T < t ∧ A * liClockThetaForcingInputDeriv t <
      volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  set T' := max T 0
  set A' := max A 0
  have hK'0 : ∀ t, 0 ≤ liClockThetaKernelDeriv t := liClockThetaKernelDeriv_nonneg
  have htail : ∀ t, T' < t → volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t ≤
      A' * liClockThetaForcingInputDeriv t := fun t ht => by
    have h := hcon t (lt_of_le_of_lt (le_max_left _ _) ht)
    have hg := (liClockThetaForcingInputDeriv_pos t).le
    nlinarith [le_max_left A 0]
  obtain ⟨G₁, hG₁, hG⟩ := exists_forcingInput_laplace_lower
  have hcK' : Continuous liClockThetaKernelDeriv :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_liClockThetaKernelDeriv t).continuousAt
  set CT := ∫ t in Ioc (0 : ℝ) T', volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t
  have hCT : 0 ≤ CT := setIntegral_nonneg measurableSet_Ioc fun t ht =>
    volterraConv_nonneg' (fun s hs => forcingInput_nonneg hs) (fun s _ => hK'0 s) ht.1.le
  have hc1 := liClockThetaGeneratorCoeff_one_pos
  have hbound : ∀ p, 0 < p → p ≤ 1 →
      liClockThetaGeneratorCoeff 1 * (p ^ 2)⁻¹ ≤ CT / (p * G₁) + A' := by
    intro p hp hp1
    have hgi := integrableOn_forcingInput hp
    have hK'i := integrableOn_kernelDeriv hp
    have hconv := integral_exp_mul_volterraConv_of_nonneg
      (contDiff_liClockThetaForcingInput.continuous) hcK'
      (fun t ht => forcingInput_nonneg ht) (fun t _ => hK'0 t) hgi hK'i
    have hci : IntegrableOn (fun t => Real.exp (-(p * t)) *
        volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t) (Ioi 0) := by
      have := integrableOn_volterraConv_of_nonneg
        ((by fun_prop : Continuous fun t : ℝ => Real.exp (-p * t)).mul
          contDiff_liClockThetaForcingInput.continuous)
        ((by fun_prop : Continuous fun t : ℝ => Real.exp (-p * t)).mul hcK')
        (fun t ht => mul_nonneg (Real.exp_pos _).le (forcingInput_nonneg ht))
        (fun t _ => mul_nonneg (Real.exp_pos _).le (hK'0 t))
        (hgi.congr_fun (fun t _ => by simp only [Pi.mul_apply]; ring_nf) measurableSet_Ioi)
        (hK'i.congr_fun (fun t _ => by simp only [Pi.mul_apply]; ring_nf) measurableSet_Ioi)
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      show volterraConv (fun s => Real.exp (-p * s) * liClockThetaForcingInput s)
        (fun s => Real.exp (-p * s) * liClockThetaKernelDeriv s) t = _
      rw [← exp_mul_volterraConv]; ring_nf
    have hsplit := integral_split_le
      (u := volterraConv liClockThetaForcingInput liClockThetaKernelDeriv)
      (v := liClockThetaForcingInputDeriv)
      (continuous_volterraConv contDiff_liClockThetaForcingInput.continuous hcK')
      (fun t ht => volterraConv_nonneg' (fun s hs => forcingInput_nonneg hs) (fun s _ => hK'0 s) ht)
      (le_max_right T 0) (le_max_right A 0) hci (integrableOn_forcingInputDeriv hp)
      (fun t _ => (liClockThetaForcingInputDeriv_pos t).le) hp htail
    have e1 : ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaKernelDeriv t =
        p * ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaKernel t := by
      have := integral_liClockThetaKernelDeriv_eq hp
      rw [integral_comm', integral_comm'] at this
      exact this
    have e2 : ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaForcingInputDeriv t =
        p * ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaForcingInput t := by
      have := integral_liClockThetaForcingInputDeriv_eq hp
      rw [integral_comm', integral_comm'] at this
      exact this
    rw [hconv, e1, e2] at hsplit
    have hGp := hG p hp hp1
    have hKlow := liClockThetaGeneratorCoeff_one_div_sq_le_integral hp
    rw [integral_comm'] at hKlow
    set Gp := ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaForcingInput t
    set Kp := ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaKernel t
    have hGp0 : 0 < Gp := hG₁.trans_le hGp
    have hpG : 0 < p * Gp := mul_pos hp hGp0
    have hK : Kp ≤ CT / (p * Gp) + A' := by
      rw [div_add' _ _ _ hpG.ne', le_div_iff₀ hpG]; nlinarith
    have hCT' : CT / (p * Gp) ≤ CT / (p * G₁) :=
      div_le_div_of_nonneg_left hCT (mul_pos hp hG₁) (mul_le_mul_of_nonneg_left hGp hp.le)
    linarith
  set B := CT / G₁ + A' + 1
  have hB : 0 < B := by have : 0 ≤ CT / G₁ := div_nonneg hCT hG₁.le
                        have : 0 ≤ A' := le_max_right A 0
                        positivity
  set p := min 1 (liClockThetaGeneratorCoeff 1 / (2 * B))
  have hp : 0 < p := lt_min one_pos (by positivity)
  have hp1 : p ≤ 1 := min_le_left _ _
  have hp2 : p ≤ liClockThetaGeneratorCoeff 1 / (2 * B) := min_le_right _ _
  have h := hbound p hp hp1
  have hA' : 0 ≤ A' := le_max_right A 0
  have key : liClockThetaGeneratorCoeff 1 ≤ p * (CT / G₁) + A' * p ^ 2 := by
    have hp2 : 0 < p ^ 2 := by positivity
    have h' := mul_le_mul_of_nonneg_left h hp2.le
    have e1 : p ^ 2 * (liClockThetaGeneratorCoeff 1 * (p ^ 2)⁻¹) = liClockThetaGeneratorCoeff 1 := by
      field_simp
    have e2 : p ^ 2 * (CT / (p * G₁) + A') = p * (CT / G₁) + A' * p ^ 2 := by
      have hp0 : p ≠ 0 := hp.ne'
      have hG0 : G₁ ≠ 0 := hG₁.ne'
      rw [mul_add, show p ^ 2 * (CT / (p * G₁)) = p * (CT / G₁) by field_simp]
      ring
    rw [e1, e2] at h'
    exact h'
  have hpp : p ^ 2 ≤ p := by nlinarith
  have hpB : p * (2 * B) ≤ liClockThetaGeneratorCoeff 1 := by
    rw [le_div_iff₀ (by positivity)] at hp2; linarith
  have : 0 ≤ CT / G₁ := div_nonneg hCT hG₁.le
  nlinarith

/-! ## The exact origin law -/

private theorem hκ1 : GeometricCoeffBound (fun m => liClockThetaGeneratorCoeff (m + 1))
    (1 * (32 / 303)) 1 := fun m => (hκ m).trans (by
      rw [one_pow, mul_one]
      exact mul_le_of_le_one_right (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num)))

/-- The convolution coefficients of `g ⋆ K`. -/
def liClockThetaHistoryCoeff : ℕ → ℝ :=
  oddConvCoeff (fun m => -liClockThetaForcingTaylorCoeff (m + 1))
    (fun m => liClockThetaGeneratorCoeff (m + 1))

private theorem hC : GeometricCoeffBound liClockThetaHistoryCoeff
    ((2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1 *
      (1 * (32 / 303)) / (2 * 1)) (2 * 1) := fun m => by
  unfold liClockThetaHistoryCoeff
  rw [oddConvCoeff_eq_borelConvCoeff]
  exact geometricCoeffBound_borelConvCoeff hγ hκ1 one_pos m

theorem volterraConv_liClockThetaForcingInput_kernel (t : ℝ) :
    volterraConv liClockThetaForcingInput liClockThetaKernel t =
      oddFactorialSeries liClockThetaHistoryCoeff t :=
  volterraConv_oddFactorialSeries hγ hκ1 one_pos t

theorem volterraConv_liClockThetaForcingInput_kernelDeriv (t : ℝ) :
    volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t =
      evenFactorialSeries liClockThetaHistoryCoeff t := by
  have h1 := hasDerivAt_volterraConv (f := liClockThetaKernel) (f' := liClockThetaKernelDeriv)
    (g := liClockThetaForcingInput) hasDerivAt_liClockThetaKernel
    (continuous_iff_continuousAt.2 fun t => (hasDerivAt_liClockThetaKernelDeriv t).continuousAt)
    contDiff_liClockThetaForcingInput.continuous t
  have hK0 : liClockThetaKernel 0 = 0 := by simp [liClockThetaKernel, oddFactorialSeries_zero]
  rw [hK0, zero_mul, zero_add] at h1
  have hV : volterraConv liClockThetaKernel liClockThetaForcingInput =
      oddFactorialSeries liClockThetaHistoryCoeff := by
    funext s; rw [volterraConv_comm]; exact volterraConv_liClockThetaForcingInput_kernel s
  rw [hV] at h1
  rw [volterraConv_comm]
  exact h1.unique (hasDerivAt_oddFactorialSeries (by norm_num) hC t)

theorem liClockThetaHistoryCoeff_zero : liClockThetaHistoryCoeff 0 = 0 := rfl

theorem liClockThetaHistoryCoeff_one :
    liClockThetaHistoryCoeff 1 = liClockThetaForcingInputDeriv 0 * liClockThetaKernelDeriv 0 := by
  unfold liClockThetaHistoryCoeff oddConvCoeff liClockThetaForcingInputDeriv liClockThetaKernelDeriv
  rw [evenFactorialSeries_zero, evenFactorialSeries_zero]
  simp

private theorem abs_sub_le_odd_one {t : ℝ} (ht : |t| ≤ 1) :
    |liClockThetaForcingInput t - liClockThetaForcingInputDeriv 0 * t| ≤
      (2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1 *
        Real.exp 1 * |t| ^ 3 := by
  have h := abs_oddFactorialSeries_sub_sum_le (by norm_num) hγ ht 1
  have e : liClockThetaForcingInputDeriv 0 = -liClockThetaForcingTaylorCoeff (0 + 1) := by
    unfold liClockThetaForcingInputDeriv; rw [evenFactorialSeries_zero]
  simp only [Finset.range_one, Finset.sum_singleton, mul_zero, zero_add, pow_one,
    Nat.factorial_one, Nat.cast_one, div_one, show 2 * 1 + 1 = 3 from rfl] at h e
  rw [e]
  unfold liClockThetaForcingInput
  exact h

private theorem abs_sub_le_even_one {t : ℝ} (ht : |t| ≤ 1) :
    |liClockThetaForcingInputDeriv t - liClockThetaForcingInputDeriv 0| ≤
      (2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1 *
        Real.exp 1 * |t| ^ 2 := by
  have h := abs_evenFactorialSeries_sub_sum_le (by norm_num) hγ ht 1
  have e : liClockThetaForcingInputDeriv 0 = -liClockThetaForcingTaylorCoeff (0 + 1) := by
    unfold liClockThetaForcingInputDeriv; rw [evenFactorialSeries_zero]
  simp only [Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, mul_one, zero_add, show 2 * 1 = 2 from rfl] at h e
  rw [e, mul_one]
  unfold liClockThetaForcingInputDeriv
  exact h

private theorem abs_history_sub_le {t : ℝ} (ht : |t| ≤ 1) :
    |volterraConv liClockThetaForcingInput liClockThetaKernel t -
        liClockThetaForcingInputDeriv 0 * liClockThetaKernelDeriv 0 * t ^ 3 / 6| ≤
      (2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1 *
        (1 * (32 / 303)) / (2 * 1) * Real.exp (2 * 1) * |t| ^ 5 := by
  have h := abs_oddFactorialSeries_sub_sum_le (by norm_num) hC ht 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, liClockThetaHistoryCoeff_zero,
    zero_mul, zero_div, liClockThetaHistoryCoeff_one] at h
  rw [volterraConv_liClockThetaForcingInput_kernel]
  have e : liClockThetaForcingInputDeriv 0 * liClockThetaKernelDeriv 0 * t ^ (2 * 1 + 1) /
      ((2 * 1 + 1).factorial : ℝ) = liClockThetaForcingInputDeriv 0 * liClockThetaKernelDeriv 0 *
        t ^ 3 / 6 := by norm_num [Nat.factorial]
  rw [e] at h
  norm_num at h ⊢
  linarith [h]

private theorem abs_historyDeriv_sub_le {t : ℝ} (ht : |t| ≤ 1) :
    |volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t -
        liClockThetaForcingInputDeriv 0 * liClockThetaKernelDeriv 0 * t ^ 2 / 2| ≤
      (2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1 *
        (1 * (32 / 303)) / (2 * 1) * Real.exp (2 * 1) * |t| ^ 4 := by
  have h := abs_evenFactorialSeries_sub_sum_le (by norm_num) hC ht 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, liClockThetaHistoryCoeff_zero,
    zero_mul, zero_div, liClockThetaHistoryCoeff_one] at h
  rw [volterraConv_liClockThetaForcingInput_kernelDeriv]
  have e : liClockThetaForcingInputDeriv 0 * liClockThetaKernelDeriv 0 * t ^ (2 * 1) /
      ((2 * 1).factorial : ℝ) = liClockThetaForcingInputDeriv 0 * liClockThetaKernelDeriv 0 *
        t ^ 2 / 2 := by norm_num [Nat.factorial]
  rw [e] at h
  norm_num at h ⊢
  linarith [h]

/-- **Origin law for `g ⋆ K`.**  `(g ⋆ K)(t)/g(t) = ν₁t²/12 + O(t⁴)` on a positive origin
interval. -/
theorem exists_abs_history_div_forcingInput_sub_le :
    ∃ C ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t < ε →
      |volterraConv liClockThetaForcingInput liClockThetaKernel t / liClockThetaForcingInput t -
        thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 12| ≤ C * t ^ 4 := by
  set a := liClockThetaForcingInputDeriv 0
  set b := liClockThetaKernelDeriv 0
  have ha : 0 < a := liClockThetaForcingInputDeriv_pos 0
  have hb : b = thetaCuspNormalizedEvenMoment 1 / 2 := liClockThetaKernelDeriv_zero
  have hb0 : 0 < b := by rw [hb]; have := thetaCuspNormalizedEvenMoment_pos 1; positivity
  set M1 := (2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1 *
    Real.exp 1
  set M2 := (2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1 *
    (1 * (32 / 303)) / (2 * 1) * Real.exp (2 * 1)
  have hM1 : 0 ≤ M1 := by
    have : 0 ≤ normalizedPrimeArchMoment 0 := by
      rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
      exact (thetaCuspNormalizedEvenMoment_pos 1).le
    positivity
  have hM2 : 0 ≤ M2 := by
    have : 0 ≤ normalizedPrimeArchMoment 0 := by
      rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
      exact (thetaCuspNormalizedEvenMoment_pos 1).le
    positivity
  refine ⟨2 * (M2 + b * M1 / 6) / a, min 1 (a / (2 * M1 + 1)), lt_min one_pos (by positivity),
    fun t ht htε => ?_⟩
  have ht1 : t < 1 := htε.trans_le (min_le_left _ _)
  have htabs : |t| ≤ 1 := by rw [abs_of_pos ht]; exact ht1.le
  have htM : t < a / (2 * M1 + 1) := htε.trans_le (min_le_right _ _)
  have hg1 := abs_sub_le_odd_one htabs
  have hh := abs_history_sub_le htabs
  rw [abs_of_pos ht] at hg1 hh
  have hMt : M1 * t ^ 2 ≤ a / 2 := by
    have h1 : M1 * t ^ 2 ≤ M1 * t := mul_le_mul_of_nonneg_left (by nlinarith) hM1
    have h2 : M1 * t < a / 2 := by
      rw [lt_div_iff₀ (by positivity)] at htM
      nlinarith
    linarith
  have hglow : a * t / 2 ≤ liClockThetaForcingInput t := by
    have := (abs_le.1 hg1).1
    nlinarith
  have hgpos : 0 < liClockThetaForcingInput t := by nlinarith
  rw [div_sub' hgpos.ne', abs_div, abs_of_pos hgpos, div_le_iff₀ hgpos]
  have hnum : |volterraConv liClockThetaForcingInput liClockThetaKernel t -
      liClockThetaForcingInput t * (thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 12)| ≤
      (M2 + b * M1 / 6) * t ^ 5 := by
    have e : liClockThetaForcingInput t * (thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 12) =
        a * b * t ^ 3 / 6 + b * t ^ 2 / 6 * (liClockThetaForcingInput t - a * t) := by
      rw [hb]; ring
    rw [e]
    calc |volterraConv liClockThetaForcingInput liClockThetaKernel t -
          (a * b * t ^ 3 / 6 + b * t ^ 2 / 6 * (liClockThetaForcingInput t - a * t))| ≤
        |volterraConv liClockThetaForcingInput liClockThetaKernel t - a * b * t ^ 3 / 6| +
          |b * t ^ 2 / 6 * (liClockThetaForcingInput t - a * t)| := by
          rw [show volterraConv liClockThetaForcingInput liClockThetaKernel t -
            (a * b * t ^ 3 / 6 + b * t ^ 2 / 6 * (liClockThetaForcingInput t - a * t)) =
            (volterraConv liClockThetaForcingInput liClockThetaKernel t - a * b * t ^ 3 / 6) -
              b * t ^ 2 / 6 * (liClockThetaForcingInput t - a * t) by ring]
          exact abs_sub _ _
      _ ≤ M2 * t ^ 5 + b * t ^ 2 / 6 * (M1 * t ^ 3) := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ b * t ^ 2 / 6)]
          exact add_le_add hh (mul_le_mul_of_nonneg_left hg1 (by positivity))
      _ = (M2 + b * M1 / 6) * t ^ 5 := by ring
  refine hnum.trans ?_
  have hC0 : 0 ≤ M2 + b * M1 / 6 := by positivity
  calc (M2 + b * M1 / 6) * t ^ 5 = (2 * (M2 + b * M1 / 6) / a * t ^ 4) * (a * t / 2) := by
        field_simp
    _ ≤ 2 * (M2 + b * M1 / 6) / a * t ^ 4 * liClockThetaForcingInput t :=
        mul_le_mul_of_nonneg_left hglow (by positivity)

/-- **Origin law for `g ⋆ K'`.**  `(g ⋆ K')(t)/g'(t) = ν₁t²/4 + O(t⁴)` on a positive origin
interval. -/
theorem exists_abs_historyDeriv_div_forcingInputDeriv_sub_le :
    ∃ C ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t < ε →
      |volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t /
          liClockThetaForcingInputDeriv t - thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 4| ≤
        C * t ^ 4 := by
  set a := liClockThetaForcingInputDeriv 0
  set b := liClockThetaKernelDeriv 0
  have ha : 0 < a := liClockThetaForcingInputDeriv_pos 0
  have hb : b = thetaCuspNormalizedEvenMoment 1 / 2 := liClockThetaKernelDeriv_zero
  have hb0 : 0 < b := by rw [hb]; have := thetaCuspNormalizedEvenMoment_pos 1; positivity
  set M1 := (2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1 *
    Real.exp 1
  set M2 := (2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1 *
    (1 * (32 / 303)) / (2 * 1) * Real.exp (2 * 1)
  have hM0 : 0 ≤ normalizedPrimeArchMoment 0 := by
    rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    exact (thetaCuspNormalizedEvenMoment_pos 1).le
  have hM1 : 0 ≤ M1 := by positivity
  have hM2 : 0 ≤ M2 := by positivity
  refine ⟨2 * (M2 + b * M1 / 2) / a, min 1 (a / (2 * M1 + 1)), lt_min one_pos (by positivity),
    fun t ht htε => ?_⟩
  have ht1 : t < 1 := htε.trans_le (min_le_left _ _)
  have htabs : |t| ≤ 1 := by rw [abs_of_pos ht]; exact ht1.le
  have htM : t < a / (2 * M1 + 1) := htε.trans_le (min_le_right _ _)
  have hg1 := abs_sub_le_even_one htabs
  have hh := abs_historyDeriv_sub_le htabs
  rw [abs_of_pos ht] at hg1 hh
  have hMt : M1 * t ^ 2 ≤ a / 2 := by
    have h1 : M1 * t ^ 2 ≤ M1 * t := mul_le_mul_of_nonneg_left (by nlinarith) hM1
    have h2 : M1 * t < a / 2 := by
      rw [lt_div_iff₀ (by positivity)] at htM
      nlinarith
    linarith
  have hglow : a / 2 ≤ liClockThetaForcingInputDeriv t := by
    have := (abs_le.1 hg1).1
    linarith
  have hgpos : 0 < liClockThetaForcingInputDeriv t := liClockThetaForcingInputDeriv_pos t
  rw [div_sub' hgpos.ne', abs_div, abs_of_pos hgpos, div_le_iff₀ hgpos]
  have hnum : |volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t -
      liClockThetaForcingInputDeriv t * (thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 4)| ≤
      (M2 + b * M1 / 2) * t ^ 4 := by
    have e : liClockThetaForcingInputDeriv t * (thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 4) =
        a * b * t ^ 2 / 2 + b * t ^ 2 / 2 * (liClockThetaForcingInputDeriv t - a) := by
      rw [hb]; ring
    rw [e]
    calc |volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t -
          (a * b * t ^ 2 / 2 + b * t ^ 2 / 2 * (liClockThetaForcingInputDeriv t - a))| ≤
        |volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t - a * b * t ^ 2 / 2| +
          |b * t ^ 2 / 2 * (liClockThetaForcingInputDeriv t - a)| := by
          rw [show volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t -
            (a * b * t ^ 2 / 2 + b * t ^ 2 / 2 * (liClockThetaForcingInputDeriv t - a)) =
            (volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t - a * b * t ^ 2 / 2) -
              b * t ^ 2 / 2 * (liClockThetaForcingInputDeriv t - a) by ring]
          exact abs_sub _ _
      _ ≤ M2 * t ^ 4 + b * t ^ 2 / 2 * (M1 * t ^ 2) := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ b * t ^ 2 / 2)]
          exact add_le_add hh (mul_le_mul_of_nonneg_left hg1 (by positivity))
      _ = (M2 + b * M1 / 2) * t ^ 4 := by ring
  refine hnum.trans ?_
  calc (M2 + b * M1 / 2) * t ^ 4 = (2 * (M2 + b * M1 / 2) / a * t ^ 4) * (a / 2) := by
        field_simp
    _ ≤ 2 * (M2 + b * M1 / 2) / a * t ^ 4 * liClockThetaForcingInputDeriv t :=
        mul_le_mul_of_nonneg_left hglow (by positivity)

/-- **Both strict comparisons hold on a positive origin interval**, and both ratios tend to `0`. -/
theorem exists_history_lt_forcingInput_near_zero :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t < ε →
      volterraConv liClockThetaForcingInput liClockThetaKernel t < liClockThetaForcingInput t ∧
      volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t <
        liClockThetaForcingInputDeriv t := by
  obtain ⟨C₁, ε₁, hε₁, h₁⟩ := exists_abs_history_div_forcingInput_sub_le
  obtain ⟨C₂, ε₂, hε₂, h₂⟩ := exists_abs_historyDeriv_div_forcingInputDeriv_sub_le
  set ν := thetaCuspNormalizedEvenMoment 1
  have hν := thetaCuspNormalizedEvenMoment_pos 1
  set B := ν + |C₁| + |C₂| + 1
  have hB : 0 < B := by positivity
  refine ⟨min (min ε₁ ε₂) (min 1 (1 / (2 * B))), by positivity, fun t ht htε => ?_⟩
  have ht1 : t < ε₁ := htε.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have ht2 : t < ε₂ := htε.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have ht3 : t < 1 := htε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ht4 : t < 1 / (2 * B) := htε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htB : t * B < 1 / 2 := by rw [lt_div_iff₀ (by positivity)] at ht4; linarith
  have ht2le : t ^ 2 ≤ t := by nlinarith
  have ht4le : t ^ 4 ≤ t := by nlinarith [pow_le_pow_of_le_one ht.le ht3.le (by norm_num : 1 ≤ 4)]
  have hsmall : ν * t ^ 2 + |C₁| * t ^ 4 + |C₂| * t ^ 4 < 1 / 2 := by
    have : ν * t ^ 2 + |C₁| * t ^ 4 + |C₂| * t ^ 4 ≤ t * B := by
      nlinarith [abs_nonneg C₁, abs_nonneg C₂]
    linarith
  have hg := liClockThetaForcingInput_pos ht
  have hg' := liClockThetaForcingInputDeriv_pos t
  constructor
  · have h := h₁ t ht ht1
    have hr : volterraConv liClockThetaForcingInput liClockThetaKernel t /
        liClockThetaForcingInput t < 1 := by
      have := (abs_le.1 (h.trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) (by positivity)))).2
      nlinarith [abs_nonneg C₁, abs_nonneg C₂]
    rwa [div_lt_one hg] at hr
  · have h := h₂ t ht ht2
    have hr : volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t /
        liClockThetaForcingInputDeriv t < 1 := by
      have := (abs_le.1 (h.trans (mul_le_mul_of_nonneg_right (le_abs_self C₂) (by positivity)))).2
      nlinarith [abs_nonneg C₁, abs_nonneg C₂]
    rwa [div_lt_one hg'] at hr

theorem tendsto_history_div_forcingInput :
    Tendsto (fun t => volterraConv liClockThetaForcingInput liClockThetaKernel t /
      liClockThetaForcingInput t) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, ε, hε, h⟩ := exists_abs_history_div_forcingInput_sub_le
  have hlim : Tendsto (fun t : ℝ => thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 12 + C * t ^ 4)
      (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 12 + C * t ^ 4)
        (𝓝 0) (𝓝 0) := by
      have := ((by fun_prop : Continuous fun t : ℝ => thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 12 +
        C * t ^ 4).tendsto 0)
      simpa using this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim' : Tendsto (fun t : ℝ => thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 12 - C * t ^ 4)
      (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 12 - C * t ^ 4)
        (𝓝 0) (𝓝 0) := by
      have := ((by fun_prop : Continuous fun t : ℝ => thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 12 -
        C * t ^ 4).tendsto 0)
      simpa using this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < ε :=
    (eventually_nhdsWithin_of_forall fun t ht => ht).and
      ((eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim' hlim ?_ ?_
  · filter_upwards [hev] with t ht
    have := (abs_le.1 (h t ht.1 ht.2)).1
    linarith
  · filter_upwards [hev] with t ht
    have := (abs_le.1 (h t ht.1 ht.2)).2
    linarith

theorem tendsto_historyDeriv_div_forcingInputDeriv :
    Tendsto (fun t => volterraConv liClockThetaForcingInput liClockThetaKernelDeriv t /
      liClockThetaForcingInputDeriv t) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, ε, hε, h⟩ := exists_abs_historyDeriv_div_forcingInputDeriv_sub_le
  have hlim : Tendsto (fun t : ℝ => thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 4 + C * t ^ 4)
      (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 4 + C * t ^ 4)
        (𝓝 0) (𝓝 0) := by
      have := ((by fun_prop : Continuous fun t : ℝ => thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 4 +
        C * t ^ 4).tendsto 0)
      simpa using this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim' : Tendsto (fun t : ℝ => thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 4 - C * t ^ 4)
      (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 4 - C * t ^ 4)
        (𝓝 0) (𝓝 0) := by
      have := ((by fun_prop : Continuous fun t : ℝ => thetaCuspNormalizedEvenMoment 1 * t ^ 2 / 4 -
        C * t ^ 4).tendsto 0)
      simpa using this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < ε :=
    (eventually_nhdsWithin_of_forall fun t ht => ht).and
      ((eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim' hlim ?_ ?_
  · filter_upwards [hev] with t ht
    have := (abs_le.1 (h t ht.1 ht.2)).1
    linarith
  · filter_upwards [hev] with t ht
    have := (abs_le.1 (h t ht.1 ht.2)).2
    linarith

end RHTower
