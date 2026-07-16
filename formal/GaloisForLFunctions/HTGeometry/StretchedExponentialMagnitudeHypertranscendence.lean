import GaloisForLFunctions.HTGeometry.StretchedExponentialIntegerDominance
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryMagnitudeHypertranscendence
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryDoubleExponentialFamily

open Filter Finset PowerSeries MvPolynomial
open scoped Topology ENNReal

namespace GaloisForLFunctions

noncomputable section

/-- Exact stretched-exponential Taylor magnitudes force hypertranscendence after Mahler integer
normalization. -/
theorem hypertranscendental_of_mahler_stretchedExponential {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) {α B : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hB : 0 < B)
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ =
      Real.exp (-(B * stretchedExp α i)))
    (hmahler : ∀ (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ), Q ≠ 0 →
        aeval (formalJets n (taylorPS f)) Q = 0 →
        ∃ (n' : ℕ) (Q' : MvPolynomial (Fin (n' + 2)) ℂ), Q' ≠ 0 ∧
          (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q' = (z : ℂ)) ∧
          aeval (formalJets n' (taylorPS f)) Q' = 0) :
    Hypertranscendental f := by
  refine hypertranscendental_of_aeval_survives hf (fun n Q hQ => ?_)
  intro hrel
  obtain ⟨n', Q', hQ', hint, hrel'⟩ := hmahler n Q hQ hrel
  obtain ⟨N, ν₀, G, hν₀, hw₀, hgap, hmass⟩ :=
    exists_stretchedExponential_intDominance hα0 hα1 hB Q' hQ'
  have hne := aeval_coeff_ne_zero_of_int_dominant_on_support
    n' N (taylorPS f) Q' hb hint ν₀ hν₀ hw₀ hgap hmass
  rw [hrel', map_zero] at hne
  exact hne rfl

def finiteTaylorCorrectionToMagnitude (F : PowerSeries ℂ) (T : ℕ)
    (b : ℕ → ℝ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range T,
    Polynomial.monomial i ((Real.exp (-b i) : ℂ) - PowerSeries.coeff i F)

@[simp]
theorem coeff_finiteTaylorCorrectionToMagnitude (F : PowerSeries ℂ) (T : ℕ)
    (b : ℕ → ℝ) (i : ℕ) :
    Polynomial.coeff (finiteTaylorCorrectionToMagnitude F T b) i =
      if i < T then (Real.exp (-b i) : ℂ) - PowerSeries.coeff i F else 0 := by
  classical
  by_cases hi : i < T
  · simp [finiteTaylorCorrectionToMagnitude, Polynomial.coeff_monomial, eq_comm, hi]
  · simp [finiteTaylorCorrectionToMagnitude, Polynomial.coeff_monomial, eq_comm, hi]

/-- An arbitrary finite Taylor prefix does not affect stretched-exponential magnitude
hypertranscendence. -/
theorem hypertranscendental_of_eventually_stretchedExponentialMagnitude {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) {α B : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hB : 0 < B)
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ =
        Real.exp (-(B * stretchedExp α i))) :
    Hypertranscendental f := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hb
  let F := taylorPS f
  let b : ℕ → ℝ := fun i => B * stretchedExp α i
  let p := finiteTaylorCorrectionToMagnitude F T b
  let g : ℂ → ℂ := fun z => f z + p.eval z
  have hp : ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => p.eval z) :=
    contDiff_polynomial_eval p
  have hgsm : ContDiff ℂ (⊤ : ℕ∞) g := hf.add hp
  have htaylor : taylorPS g = F + (p : PowerSeries ℂ) := by
    change taylorPS (fun z => f z + p.eval z) = _
    rw [show (fun z => f z + p.eval z) = f + (fun z => p.eval z) from rfl,
      taylorPS_add hf hp, taylorPS_polynomial_eval]
  have hb' : ∀ i, ‖PowerSeries.coeff i (taylorPS g)‖ =
      Real.exp (-(B * stretchedExp α i)) := by
    intro i
    rw [htaylor, map_add, Polynomial.coeff_coe,
      coeff_finiteTaylorCorrectionToMagnitude]
    by_cases hi : i < T
    · simp [b, hi]
      rw [Complex.norm_exp]
      simp
    · have hiT : T ≤ i := Nat.le_of_not_gt hi
      simp only [if_neg hi, add_zero]
      change ‖PowerSeries.coeff i F‖ = Real.exp (-(B * stretchedExp α i))
      simpa only [F] using hT i hiT
  have hg : Hypertranscendental g :=
    hypertranscendental_of_mahler_stretchedExponential hgsm hα0 hα1 hB hb'
      (fun _n _Q hQ hrel => formal_mahler_integer_normalization hQ hrel)
  exact (hypertranscendental_add_polynomial_iff hf p).mp hg

/-- Paper-form logarithmic-magnitude criterion, including eventual nonvanishing. -/
theorem hypertranscendental_of_eventually_stretchedExponential_logMagnitude {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) {α B : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hB : 0 < B)
    (hne : ∀ᶠ i in atTop, PowerSeries.coeff i (taylorPS f) ≠ 0)
    (hlog : ∀ᶠ i in atTop,
      -Real.log ‖PowerSeries.coeff i (taylorPS f)‖ = B * stretchedExp α i) :
    Hypertranscendental f := by
  apply hypertranscendental_of_eventually_stretchedExponentialMagnitude
    hf hα0 hα1 hB
  filter_upwards [hne, hlog] with i hi hlogi
  have hnorm : 0 < ‖PowerSeries.coeff i (taylorPS f)‖ := norm_pos_iff.mpr hi
  rw [← Real.exp_log hnorm]
  congr 1
  linarith

/-! ## Explicit arbitrary-phase entire family -/

def stretchedExponentialPhaseCoeff (B α : ℝ) (θ : ℕ → ℝ) (n : ℕ) : ℂ :=
  (Real.exp (-(B * stretchedExp α n)) : ℂ) *
    Complex.exp (Complex.I * (θ n : ℂ))

theorem norm_stretchedExponentialPhaseCoeff (B α : ℝ) (θ : ℕ → ℝ) (n : ℕ) :
    ‖stretchedExponentialPhaseCoeff B α θ n‖ =
      Real.exp (-(B * stretchedExp α n)) := by
  simp [stretchedExponentialPhaseCoeff, Complex.norm_exp]

theorem stretchedExponentialPhaseCoeff_ne_zero (B α : ℝ) (θ : ℕ → ℝ) (n : ℕ) :
    stretchedExponentialPhaseCoeff B α θ n ≠ 0 := by
  simp [stretchedExponentialPhaseCoeff, Complex.exp_ne_zero]

theorem stretchedExponentialPhaseCoeff_ratio_tendsto {B α : ℝ}
    (hB : 0 < B) (hα0 : 0 < α) (hα1 : α < 1) (θ : ℕ → ℝ) :
    Tendsto (fun n => ‖stretchedExponentialPhaseCoeff B α θ n.succ‖ /
      ‖stretchedExponentialPhaseCoeff B α θ n‖) atTop (𝓝 0) := by
  have hinc := tendsto_stretchedIncrement_atTop hα0 hα1
  have hmul : Tendsto (fun n => B * stretchedIncrement α n) atTop atTop :=
    hinc.const_mul_atTop hB
  have harg : Tendsto (fun n => -(B * stretchedIncrement α n)) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hmul
  have hexp := Real.tendsto_exp_atBot.comp harg
  convert hexp using 1
  funext n
  rw [norm_stretchedExponentialPhaseCoeff, norm_stretchedExponentialPhaseCoeff,
    ← Real.exp_sub]
  congr 1
  change -(B * stretchedExp α n.succ) - -(B * stretchedExp α n) =
    -(B * stretchedIncrement α n)
  rw [show n.succ = n + 1 by omega, stretchedIncrement]
  push_cast
  ring

def stretchedExponentialPhaseFunction (B α : ℝ) (θ : ℕ → ℝ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (stretchedExponentialPhaseCoeff B α θ)

theorem stretchedExponentialPhaseFunction_eq_tsum (B α : ℝ) (θ : ℕ → ℝ) (z : ℂ) :
    stretchedExponentialPhaseFunction B α θ z =
      ∑' n, stretchedExponentialPhaseCoeff B α θ n * z ^ n := by
  simpa [stretchedExponentialPhaseFunction, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (stretchedExponentialPhaseCoeff B α θ) z)

theorem stretchedExponentialPhaseSeries_radius_eq_top {B α : ℝ}
    (hB : 0 < B) (hα0 : 0 < α) (hα1 : α < 1) (θ : ℕ → ℝ) :
    (FormalMultilinearSeries.ofScalars ℂ
      (stretchedExponentialPhaseCoeff B α θ)).radius = ⊤ := by
  exact FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℂ
    (stretchedExponentialPhaseCoeff B α θ)
    (Eventually.of_forall (stretchedExponentialPhaseCoeff_ne_zero B α θ))
    (stretchedExponentialPhaseCoeff_ratio_tendsto hB hα0 hα1 θ)

theorem contDiff_stretchedExponentialPhaseFunction {B α : ℝ}
    (hB : 0 < B) (hα0 : 0 < α) (hα1 : α < 1) (θ : ℕ → ℝ) :
    ContDiff ℂ (⊤ : ℕ∞) (stretchedExponentialPhaseFunction B α θ) := by
  let p := FormalMultilinearSeries.ofScalars ℂ (stretchedExponentialPhaseCoeff B α θ)
  have hr : p.radius = ⊤ := stretchedExponentialPhaseSeries_radius_eq_top hB hα0 hα1 θ
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have ha : AnalyticOnNhd ℂ p.sum Set.univ := by
    simpa [hr] using hp.analyticOnNhd
  exact ha.contDiff

theorem taylorPS_stretchedExponentialPhaseFunction {B α : ℝ}
    (hB : 0 < B) (hα0 : 0 < α) (hα1 : α < 1)
    (θ : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (stretchedExponentialPhaseFunction B α θ)) =
      stretchedExponentialPhaseCoeff B α θ n := by
  exact taylorPS_ofScalarsSum_of_radius_eq_top (stretchedExponentialPhaseCoeff B α θ)
    (stretchedExponentialPhaseSeries_radius_eq_top hB hα0 hα1 θ) n

/-- Every arbitrary-phase member of the stretched-exponential family is
hypertranscendental. -/
theorem hypertranscendental_stretchedExponentialPhaseFunction {B α : ℝ}
    (hB : 0 < B) (hα0 : 0 < α) (hα1 : α < 1) (θ : ℕ → ℝ) :
    Hypertranscendental (stretchedExponentialPhaseFunction B α θ) := by
  apply hypertranscendental_of_eventually_stretchedExponentialMagnitude
    (contDiff_stretchedExponentialPhaseFunction hB hα0 hα1 θ) hα0 hα1 hB
  exact Eventually.of_forall fun n => by
    rw [taylorPS_stretchedExponentialPhaseFunction hB hα0 hα1,
      norm_stretchedExponentialPhaseCoeff]

theorem stretchedExp_oneHalf_eq_exp_sqrt (n : ℕ) :
    stretchedExp (1 / 2 : ℝ) n = Real.exp (Real.sqrt n) := by
  rw [stretchedExp, Real.sqrt_eq_rpow]

def sqrtStretchedPhaseFunction (θ : ℕ → ℝ) : ℂ → ℂ :=
  stretchedExponentialPhaseFunction 1 (1 / 2) θ

theorem sqrtStretchedPhaseFunction_eq_tsum (θ : ℕ → ℝ) (z : ℂ) :
    sqrtStretchedPhaseFunction θ z =
      ∑' (n : ℕ), (Real.exp (-Real.exp (Real.sqrt n)) : ℂ) *
        Complex.exp (Complex.I * (θ n : ℂ)) * z ^ n := by
  rw [sqrtStretchedPhaseFunction, stretchedExponentialPhaseFunction_eq_tsum]
  apply tsum_congr
  intro n
  rw [stretchedExponentialPhaseCoeff, stretchedExp_oneHalf_eq_exp_sqrt]
  norm_num

/-- The explicit arbitrary-phase square-root stretched-exponential family from the card is
hypertranscendental. -/
theorem hypertranscendental_sqrtStretchedPhaseFunction (θ : ℕ → ℝ) :
    Hypertranscendental (sqrtStretchedPhaseFunction θ) := by
  exact hypertranscendental_stretchedExponentialPhaseFunction
    (by norm_num) (by norm_num) (by norm_num) θ

end

end GaloisForLFunctions
