import GaloisForLFunctions.HTGeometry.AnalyticNullPreimage
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation
import GaloisForLFunctions.HTGeometry.LinearPMapBoundedUnitaryTransport
import GaloisForLFunctions.HTGeometry.OrbitExceptionalTimes
import GaloisForLFunctions.RHTower.PrimeLogPhaseBudget
import GaloisForLFunctions.RHTower.VectorL2WeakDerivativeFourier
import GaloisForLFunctions.RHTower.WeightOneCliffordLogClosure

/-!
# Finite commuting prime couplings preserve continuous dilation spectrum

For every finite set of prime subtypes and every complex coefficient family, this module builds
the literal paired translation coupling

`V_P = ∑ p ∈ P, c_p T_(log p) + conj(c_p) T_(-log p)`

on scalar `L²(ℝ)`, with `T_a f(u) = f(u-a)`. It identifies the exact Fourier multiplier, proves
the sharp uniform coupling bound, constructs the maximal self-adjoint Hamiltonian on the standard
weak-derivative domain, and proves `H_P = -2i d/du + V_P` there.

The multiplier is nonconstant real analytic and proper. Its level sets and critical set are
countable; its direct-integral spectral measure is absolutely continuous with respect to Lebesgue
measure; and every point-eigenvalue equation has only the zero vector. No smallness, genericity,
or rational-independence premise is used. Prime-log independence is recorded separately as the
exact finite phase-rank law.
-/

noncomputable section

open Complex MeasureTheory Set Filter FourierTransform
open scoped ENNReal LinearPMap LineDeriv

namespace GaloisForLFunctions.RHTower

def finitePrimeLogFrequency (p : Nat.Primes) : ℝ := Real.log ((p : ℕ) : ℝ)

def finitePrimeNegativePhase (p : Nat.Primes) (t : ℝ) : ℂ :=
  (Real.cos (finitePrimeLogFrequency p * t) : ℂ) -
    (Real.sin (finitePrimeLogFrequency p * t) : ℂ) * Complex.I

def finitePrimePositivePhase (p : Nat.Primes) (t : ℝ) : ℂ :=
  (Real.cos (finitePrimeLogFrequency p * t) : ℂ) +
    (Real.sin (finitePrimeLogFrequency p * t) : ℂ) * Complex.I

theorem finitePrimeNegativePhase_eq_trig (p : Nat.Primes) (t : ℝ) :
    finitePrimeNegativePhase p t =
      (Real.cos (finitePrimeLogFrequency p * t) : ℂ) -
        (Real.sin (finitePrimeLogFrequency p * t) : ℂ) * Complex.I := by
  rfl

theorem finitePrimePositivePhase_eq_trig (p : Nat.Primes) (t : ℝ) :
    finitePrimePositivePhase p t =
      (Real.cos (finitePrimeLogFrequency p * t) : ℂ) +
        (Real.sin (finitePrimeLogFrequency p * t) : ℂ) * Complex.I := by
  rfl

@[simp] theorem finitePrimeNegativePhase_re (p : Nat.Primes) (t : ℝ) :
    (finitePrimeNegativePhase p t).re = Real.cos (finitePrimeLogFrequency p * t) := by
  change (((Real.cos (finitePrimeLogFrequency p * t) : ℂ) -
    (Real.sin (finitePrimeLogFrequency p * t) : ℂ) * Complex.I)).re = _
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

@[simp] theorem finitePrimeNegativePhase_im (p : Nat.Primes) (t : ℝ) :
    (finitePrimeNegativePhase p t).im = -Real.sin (finitePrimeLogFrequency p * t) := by
  change (((Real.cos (finitePrimeLogFrequency p * t) : ℂ) -
    (Real.sin (finitePrimeLogFrequency p * t) : ℂ) * Complex.I)).im = _
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

@[simp] theorem finitePrimePositivePhase_re (p : Nat.Primes) (t : ℝ) :
    (finitePrimePositivePhase p t).re = Real.cos (finitePrimeLogFrequency p * t) := by
  change (((Real.cos (finitePrimeLogFrequency p * t) : ℂ) +
    (Real.sin (finitePrimeLogFrequency p * t) : ℂ) * Complex.I)).re = _
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

@[simp] theorem finitePrimePositivePhase_im (p : Nat.Primes) (t : ℝ) :
    (finitePrimePositivePhase p t).im = Real.sin (finitePrimeLogFrequency p * t) := by
  change (((Real.cos (finitePrimeLogFrequency p * t) : ℂ) +
    (Real.sin (finitePrimeLogFrequency p * t) : ℂ) * Complex.I)).im = _
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem finitePrimeNegativePhase_eq_exp (p : Nat.Primes) (t : ℝ) :
    finitePrimeNegativePhase p t =
      Complex.exp (-Complex.I * ((t * finitePrimeLogFrequency p : ℝ) : ℂ)) := by
  have h := Complex.exp_ofReal_mul_I (-(t * finitePrimeLogFrequency p))
  calc
    finitePrimeNegativePhase p t =
        (Real.cos (-(t * finitePrimeLogFrequency p)) : ℂ) +
          (Real.sin (-(t * finitePrimeLogFrequency p)) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [finitePrimeNegativePhase, Real.cos_neg, Real.sin_neg, mul_comm]
      · simp [finitePrimeNegativePhase, Real.cos_neg, Real.sin_neg, mul_comm]
        abel
    _ = Complex.exp (((-(t * finitePrimeLogFrequency p) : ℝ) : ℂ) * Complex.I) := h.symm
    _ = Complex.exp (-Complex.I * ((t * finitePrimeLogFrequency p : ℝ) : ℂ)) := by
      apply congrArg Complex.exp
      push_cast
      ring

theorem finitePrimePositivePhase_eq_exp (p : Nat.Primes) (t : ℝ) :
    finitePrimePositivePhase p t =
      Complex.exp (Complex.I * ((t * finitePrimeLogFrequency p : ℝ) : ℂ)) := by
  calc
    finitePrimePositivePhase p t =
        (Real.cos (t * finitePrimeLogFrequency p) : ℂ) +
          (Real.sin (t * finitePrimeLogFrequency p) : ℂ) * Complex.I := by
      rw [finitePrimePositivePhase, mul_comm (finitePrimeLogFrequency p) t]
    _ = Complex.exp (((t * finitePrimeLogFrequency p : ℝ) : ℂ) * Complex.I) :=
      (Complex.exp_ofReal_mul_I (t * finitePrimeLogFrequency p)).symm
    _ = Complex.exp (Complex.I * ((t * finitePrimeLogFrequency p : ℝ) : ℂ)) := by
      apply congrArg Complex.exp
      ring

theorem norm_finitePrimeNegativePhase (p : Nat.Primes) (t : ℝ) :
    ‖finitePrimeNegativePhase p t‖ = 1 := by
  rw [finitePrimeNegativePhase_eq_exp, Complex.norm_exp]
  simp

def finitePrimePairedTerm (c : Nat.Primes → ℂ) (p : Nat.Primes) (t : ℝ) : ℝ :=
  2 * ((c p).re * Real.cos (finitePrimeLogFrequency p * t) +
    (c p).im * Real.sin (finitePrimeLogFrequency p * t))

theorem finitePrimePairedTerm_eq_two_re (c : Nat.Primes → ℂ) (p : Nat.Primes) (t : ℝ) :
    finitePrimePairedTerm c p t = 2 * (c p * finitePrimeNegativePhase p t).re := by
  rw [finitePrimePairedTerm, Complex.mul_re, finitePrimeNegativePhase_re, finitePrimeNegativePhase_im]
  ring

theorem ofReal_finitePrimePairedTerm_eq_pair (c : Nat.Primes → ℂ) (p : Nat.Primes) (t : ℝ) :
    (finitePrimePairedTerm c p t : ℂ) =
      c p * finitePrimeNegativePhase p t +
        (starRingEnd ℂ) (c p) * finitePrimePositivePhase p t := by
  rw [finitePrimePairedTerm_eq_two_re]
  apply Complex.ext
  · simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, finitePrimeNegativePhase_re,
      finitePrimeNegativePhase_im, finitePrimePositivePhase_re, finitePrimePositivePhase_im]
    ring
  · simp only [Complex.ofReal_im, Complex.add_im, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, finitePrimeNegativePhase_re,
      finitePrimeNegativePhase_im, finitePrimePositivePhase_re, finitePrimePositivePhase_im]
    ring

theorem abs_finitePrimePairedTerm_le (c : Nat.Primes → ℂ) (p : Nat.Primes) (t : ℝ) :
    |finitePrimePairedTerm c p t| ≤ 2 * ‖c p‖ := by
  calc
    |finitePrimePairedTerm c p t| = 2 * |(c p * finitePrimeNegativePhase p t).re| := by
      rw [finitePrimePairedTerm_eq_two_re, abs_mul]
      norm_num
    2 * |(c p * finitePrimeNegativePhase p t).re| ≤
        2 * ‖c p * finitePrimeNegativePhase p t‖ := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ = 2 * ‖c p‖ := by
      rw [norm_mul, norm_finitePrimeNegativePhase, mul_one]

def finitePrimeTranslationSymbol (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) (t : ℝ) : ℝ :=
  ∑ p ∈ P, finitePrimePairedTerm c p t

def finitePrimeCouplingBudget (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) : ℝ :=
  2 * ∑ p ∈ P, ‖c p‖

theorem abs_finitePrimeTranslationSymbol_le (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) (t : ℝ) :
    |finitePrimeTranslationSymbol P c t| ≤ finitePrimeCouplingBudget P c := by
  calc
    |finitePrimeTranslationSymbol P c t| ≤ ∑ p ∈ P, |finitePrimePairedTerm c p t| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, 2 * ‖c p‖ := by
      exact Finset.sum_le_sum fun p hp => abs_finitePrimePairedTerm_le c p t
    _ = finitePrimeCouplingBudget P c := by
      simp [finitePrimeCouplingBudget, Finset.mul_sum]

def finitePrimeDilationSymbol (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) (t : ℝ) : ℝ :=
  2 * t + finitePrimeTranslationSymbol P c t

theorem ofReal_finitePrimeDilationSymbol_eq (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) (t : ℝ) :
    (finitePrimeDilationSymbol P c t : ℂ) = (2 * t : ℝ) +
      ∑ p ∈ P, (c p * finitePrimeNegativePhase p t +
        (starRingEnd ℂ) (c p) * finitePrimePositivePhase p t) := by
  rw [finitePrimeDilationSymbol]
  push_cast
  congr 1
  rw [finitePrimeTranslationSymbol]
  push_cast
  exact Finset.sum_congr rfl fun p hp => ofReal_finitePrimePairedTerm_eq_pair c p t

theorem analyticOnNhd_finitePrimePairedTerm (c : Nat.Primes → ℂ) (p : Nat.Primes) :
    AnalyticOnNhd ℝ (finitePrimePairedTerm c p) Set.univ := by
  unfold finitePrimePairedTerm
  refine analyticOnNhd_const.mul ((analyticOnNhd_const.mul ?_).add
    (analyticOnNhd_const.mul ?_))
  · simpa [mul_comm] using
      GaloisForLFunctions.HTGeometry.analyticOnNhd_cos_mul (finitePrimeLogFrequency p)
  · simpa [mul_comm] using
      GaloisForLFunctions.HTGeometry.analyticOnNhd_sin_mul (finitePrimeLogFrequency p)

theorem analyticOnNhd_finitePrimeTranslationSymbol (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    AnalyticOnNhd ℝ (finitePrimeTranslationSymbol P c) Set.univ := by
  classical
  unfold finitePrimeTranslationSymbol
  have heq : (fun t => ∑ p ∈ P, finitePrimePairedTerm c p t) =
      ∑ p ∈ P, finitePrimePairedTerm c p := by
    funext t
    simp
  rw [heq]
  exact Finset.analyticOnNhd_sum P (fun p _ => analyticOnNhd_finitePrimePairedTerm c p)

theorem analyticOnNhd_finitePrimeDilationSymbol (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    AnalyticOnNhd ℝ (finitePrimeDilationSymbol P c) Set.univ := by
  exact (analyticOnNhd_const.mul analyticOnNhd_id).add
    (analyticOnNhd_finitePrimeTranslationSymbol P c)

theorem continuous_finitePrimeDilationSymbol (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    Continuous (finitePrimeDilationSymbol P c) :=
  continuousOn_univ.mp (analyticOnNhd_finitePrimeDilationSymbol P c).continuousOn

theorem measurable_finitePrimeDilationSymbol (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    Measurable (finitePrimeDilationSymbol P c) :=
  (continuous_finitePrimeDilationSymbol P c).measurable

theorem finitePrimeCouplingBudget_nonneg (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    0 ≤ finitePrimeCouplingBudget P c := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem finitePrimeDilationSymbol_nonconstant (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    ∃ x y : ℝ, finitePrimeDilationSymbol P c x ≠ finitePrimeDilationSymbol P c y := by
  let B := finitePrimeCouplingBudget P c
  have hB : 0 ≤ B := finitePrimeCouplingBudget_nonneg P c
  have hzero := abs_finitePrimeTranslationSymbol_le P c 0
  have hfar := abs_finitePrimeTranslationSymbol_le P c (B + 1)
  refine ⟨0, B + 1, ne_of_lt ?_⟩
  dsimp [finitePrimeDilationSymbol]
  have hzeroUpper : finitePrimeTranslationSymbol P c 0 ≤ B :=
    le_trans (le_abs_self _) hzero
  have hfarLower : -B ≤ finitePrimeTranslationSymbol P c (B + 1) :=
    (neg_le_of_abs_le hfar)
  linarith

theorem tendsto_finitePrimeDilationSymbol_atTop (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    Tendsto (finitePrimeDilationSymbol P c) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop ((b + finitePrimeCouplingBudget P c) / 2)] with t ht
  have hpart := abs_finitePrimeTranslationSymbol_le P c t
  have hlower : -finitePrimeCouplingBudget P c ≤ finitePrimeTranslationSymbol P c t := neg_le_of_abs_le hpart
  dsimp [finitePrimeDilationSymbol]
  linarith

theorem tendsto_finitePrimeDilationSymbol_atBot (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    Tendsto (finitePrimeDilationSymbol P c) atBot atBot := by
  rw [tendsto_atBot]
  intro b
  filter_upwards [eventually_le_atBot ((b - finitePrimeCouplingBudget P c) / 2)] with t ht
  have hpart := abs_finitePrimeTranslationSymbol_le P c t
  have hupper : finitePrimeTranslationSymbol P c t ≤ finitePrimeCouplingBudget P c := le_of_abs_le hpart
  dsimp [finitePrimeDilationSymbol]
  linarith

theorem finitePrimeDilationSymbol_compactPreimageProper (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) {K : Set ℝ} (hK : IsCompact K) :
    IsCompact (finitePrimeDilationSymbol P c ⁻¹' K) := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  refine (isCompact_closedBall (0 : ℝ)
    ((r + finitePrimeCouplingBudget P c) / 2)).of_isClosed_subset
      (hK.isClosed.preimage (continuous_finitePrimeDilationSymbol P c)) ?_
  intro t ht
  have henergyBall := hr ht
  have henergy : |finitePrimeDilationSymbol P c t| ≤ r := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using henergyBall
  have hprime := abs_finitePrimeTranslationSymbol_le P c t
  have hlinear : |2 * t| ≤ |finitePrimeDilationSymbol P c t| + |finitePrimeTranslationSymbol P c t| := by
    calc
      |2 * t| = |finitePrimeDilationSymbol P c t - finitePrimeTranslationSymbol P c t| := by
        simp only [finitePrimeDilationSymbol]
        congr 1
        ring
      _ ≤ |finitePrimeDilationSymbol P c t| + |finitePrimeTranslationSymbol P c t| := abs_sub _ _
  have htbound : |t| ≤ (r + finitePrimeCouplingBudget P c) / 2 := by
    rw [abs_mul] at hlinear
    norm_num at hlinear
    linarith
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using htbound

theorem finitePrimeDilationSymbol_criticalSet_countable (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) :
    {t : ℝ | deriv (finitePrimeDilationSymbol P c) t = 0}.Countable := by
  obtain ⟨x, y, hxy⟩ := finitePrimeDilationSymbol_nonconstant P c
  have hderiv : ∃ t : ℝ, deriv (finitePrimeDilationSymbol P c) t ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hxy (is_const_of_deriv_eq_zero
      (differentiableOn_univ.mp
        (analyticOnNhd_finitePrimeDilationSymbol P c).differentiableOn) h x y)
  exact GaloisForLFunctions.HTGeometry.analytic_zero_set_countable
    (analyticOnNhd_finitePrimeDilationSymbol P c).deriv hderiv

theorem finitePrimeDilationSymbol_levelSet_countable (P : Finset Nat.Primes) (c : Nat.Primes → ℂ)
    (lambda : ℝ) : {t : ℝ | finitePrimeDilationSymbol P c t = lambda}.Countable := by
  have hne : ∃ t : ℝ, finitePrimeDilationSymbol P c t - lambda ≠ 0 := by
    obtain ⟨x, y, hxy⟩ := finitePrimeDilationSymbol_nonconstant P c
    by_cases hx : finitePrimeDilationSymbol P c x = lambda
    · exact ⟨y, sub_ne_zero.mpr (by intro hy; exact hxy (hx.trans hy.symm))⟩
    · exact ⟨x, sub_ne_zero.mpr hx⟩
  have han : AnalyticOnNhd ℝ (fun t => finitePrimeDilationSymbol P c t - lambda) Set.univ :=
    (analyticOnNhd_finitePrimeDilationSymbol P c).sub analyticOnNhd_const
  simpa only [sub_eq_zero] using
    GaloisForLFunctions.HTGeometry.analytic_zero_set_countable han hne

theorem volume_finitePrimeDilationSymbol_levelSet_eq_zero (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (lambda : ℝ) :
    volume {t : ℝ | finitePrimeDilationSymbol P c t = lambda} = 0 :=
  (finitePrimeDilationSymbol_levelSet_countable P c lambda).measure_zero volume

theorem finitePrimeDilationSymbol_spectralMeasure_absolutelyContinuous (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) :
    Measure.map (finitePrimeDilationSymbol P c) (volume : Measure ℝ) ≪ volume := by
  intro E hE
  obtain ⟨E', hEE', hE'meas, hE'null⟩ := exists_measurable_superset_of_null hE
  refine measure_mono_null hEE' ?_
  rw [Measure.map_apply (measurable_finitePrimeDilationSymbol P c) hE'meas]
  exact GaloisForLFunctions.HTGeometry.analytic_preimage_volume_eq_zero
    (analyticOnNhd_finitePrimeDilationSymbol P c) (finitePrimeDilationSymbol_nonconstant P c) hE'null

def finitePrimeFourierSymbol (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) (xi : ℝ) : ℝ :=
  finitePrimeDilationSymbol P c (2 * Real.pi * xi)

theorem finitePrimeFourierSymbol_eq_rescaled (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (xi : ℝ) :
    finitePrimeFourierSymbol P c xi = finitePrimeDilationSymbol P c (2 * Real.pi * xi) := rfl

theorem analyticOnNhd_finitePrimeFourierSymbol (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) :
    AnalyticOnNhd ℝ (finitePrimeFourierSymbol P c) Set.univ := by
  have hscale : AnalyticOnNhd ℝ (fun xi : ℝ => 2 * Real.pi * xi) Set.univ :=
    analyticOnNhd_const.mul analyticOnNhd_id
  exact (analyticOnNhd_finitePrimeDilationSymbol P c).comp hscale fun _ _ => Set.mem_univ _

theorem measurable_finitePrimeFourierSymbol (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    Measurable (finitePrimeFourierSymbol P c) :=
  (continuousOn_univ.mp (analyticOnNhd_finitePrimeFourierSymbol P c).continuousOn).measurable

theorem finitePrimeFourierSymbol_nonconstant (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    ∃ x y : ℝ, finitePrimeFourierSymbol P c x ≠ finitePrimeFourierSymbol P c y := by
  obtain ⟨x, y, hxy⟩ := finitePrimeDilationSymbol_nonconstant P c
  have hscale : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  refine ⟨x / (2 * Real.pi), y / (2 * Real.pi), ?_⟩
  have hrescale (z : ℝ) : 2 * Real.pi * (z / (2 * Real.pi)) = z := by
    field_simp
  rw [finitePrimeFourierSymbol, finitePrimeFourierSymbol, hrescale, hrescale]
  exact hxy

theorem finitePrimeFourierSymbol_levelSet_countable (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (lambda : ℝ) :
    {xi : ℝ | finitePrimeFourierSymbol P c xi = lambda}.Countable := by
  have hne : ∃ xi : ℝ, finitePrimeFourierSymbol P c xi - lambda ≠ 0 := by
    obtain ⟨x, y, hxy⟩ := finitePrimeFourierSymbol_nonconstant P c
    by_cases hx : finitePrimeFourierSymbol P c x = lambda
    · exact ⟨y, sub_ne_zero.mpr (by intro hy; exact hxy (hx.trans hy.symm))⟩
    · exact ⟨x, sub_ne_zero.mpr hx⟩
  have han : AnalyticOnNhd ℝ (fun xi => finitePrimeFourierSymbol P c xi - lambda) Set.univ :=
    (analyticOnNhd_finitePrimeFourierSymbol P c).sub analyticOnNhd_const
  simpa only [sub_eq_zero] using
    GaloisForLFunctions.HTGeometry.analytic_zero_set_countable han hne

theorem volume_finitePrimeFourierSymbol_levelSet_eq_zero (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (lambda : ℝ) :
    volume {xi : ℝ | finitePrimeFourierSymbol P c xi = lambda} = 0 :=
  (finitePrimeFourierSymbol_levelSet_countable P c lambda).measure_zero volume

theorem finitePrimeFourierSymbol_spectralMeasure_absolutelyContinuous
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    Measure.map (finitePrimeFourierSymbol P c) (volume : Measure ℝ) ≪ volume := by
  intro E hE
  obtain ⟨E', hEE', hE'meas, hE'null⟩ := exists_measurable_superset_of_null hE
  refine measure_mono_null hEE' ?_
  rw [Measure.map_apply (measurable_finitePrimeFourierSymbol P c) hE'meas]
  exact GaloisForLFunctions.HTGeometry.analytic_preimage_volume_eq_zero
    (analyticOnNhd_finitePrimeFourierSymbol P c) (finitePrimeFourierSymbol_nonconstant P c) hE'null

theorem ae_eq_zero_of_finitePrimeFourierSymbol_mul_eq (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (lambda : ℂ) {f : ℝ → ℂ}
    (h : ∀ᵐ xi : ℝ ∂volume,
      (finitePrimeFourierSymbol P c xi : ℂ) * f xi = lambda * f xi) :
    f =ᵐ[volume] (0 : ℝ → ℂ) := by
  have hne : ∀ᵐ xi : ℝ ∂volume, finitePrimeFourierSymbol P c xi ≠ lambda.re := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not] using
      volume_finitePrimeFourierSymbol_levelSet_eq_zero P c lambda.re
  filter_upwards [h, hne] with xi hxi hxi_ne
  have hcoef : (finitePrimeFourierSymbol P c xi : ℂ) - lambda ≠ 0 := by
    intro hz
    have heq : (finitePrimeFourierSymbol P c xi : ℂ) = lambda := sub_eq_zero.mp hz
    apply hxi_ne
    have hre := congrArg Complex.re heq
    simpa using hre
  have hzero : ((finitePrimeFourierSymbol P c xi : ℂ) - lambda) * f xi = 0 := by
    rw [sub_mul, hxi, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left hcoef

theorem l2_finitePrimeFourierSymbolMultiplier_has_no_eigenvector
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) (lambda : ℂ)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (h : ∀ᵐ xi : ℝ ∂volume,
      (finitePrimeFourierSymbol P c xi : ℂ) * (f : ℝ → ℂ) xi =
        lambda * (f : ℝ → ℂ) xi) :
    f = 0 := by
  have hz := ae_eq_zero_of_finitePrimeFourierSymbol_mul_eq P c lambda h
  apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with xi hxi hzero
  rw [hxi, hzero]

abbrev FinitePrimeDilationL2 := Lp ℂ 2 (volume : Measure ℝ)

def finitePrimeSpectralMultiplier (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    FinitePrimeDilationL2 →ₗ.[ℂ] FinitePrimeDilationL2 :=
  GaloisForLFunctions.HTGeometry.maximalRealL2Mul
    (volume : Measure ℝ) (finitePrimeFourierSymbol P c)

theorem finitePrimeSpectralMultiplier_isSelfAdjoint (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) :
    IsSelfAdjoint (finitePrimeSpectralMultiplier P c) :=
  GaloisForLFunctions.HTGeometry.maximalRealL2Mul_isSelfAdjoint
    (volume : Measure ℝ) (measurable_finitePrimeFourierSymbol P c)

theorem finitePrimeSpectralMultiplier_apply_ae (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (f : (finitePrimeSpectralMultiplier P c).domain) :
    (finitePrimeSpectralMultiplier P c f : ℝ → ℂ) =ᵐ[volume]
      fun xi => (finitePrimeFourierSymbol P c xi : ℂ) *
        (f : FinitePrimeDilationL2) xi :=
  GaloisForLFunctions.HTGeometry.maximalRealL2Mul_apply_ae
    (volume : Measure ℝ) (finitePrimeFourierSymbol P c) f

theorem finitePrimeSpectralMultiplier_has_no_eigenvector
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) (lambda : ℂ)
    (f : (finitePrimeSpectralMultiplier P c).domain)
    (h : finitePrimeSpectralMultiplier P c f = lambda • (f : FinitePrimeDilationL2)) :
    (f : FinitePrimeDilationL2) = 0 := by
  have heig : (finitePrimeSpectralMultiplier P c f : ℝ → ℂ) =ᵐ[volume]
      fun xi => lambda * (f : FinitePrimeDilationL2) xi := by
    rw [h]
    filter_upwards [Lp.coeFn_smul lambda (f : FinitePrimeDilationL2)] with xi hxi
    simpa only [Pi.smul_apply, smul_eq_mul] using hxi
  have hpoint := (finitePrimeSpectralMultiplier_apply_ae P c f).symm.trans heig
  exact l2_finitePrimeFourierSymbolMultiplier_has_no_eigenvector P c lambda
    (f : FinitePrimeDilationL2) hpoint

theorem finitePrimeSpectralMultiplier_eigenvalue_iff_levelSet_volume_ne_zero
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) (lambda : ℝ) :
    (∃ f : (finitePrimeSpectralMultiplier P c).domain,
      (f : FinitePrimeDilationL2) ≠ 0 ∧
        finitePrimeSpectralMultiplier P c f =
          (lambda : ℂ) • (f : FinitePrimeDilationL2)) ↔
      volume {xi : ℝ | finitePrimeFourierSymbol P c xi = lambda} ≠ 0 := by
  constructor
  · rintro ⟨f, hf, heig⟩
    exact False.elim (hf
      (finitePrimeSpectralMultiplier_has_no_eigenvector P c (lambda : ℂ) f heig))
  · intro hlevel
    exact False.elim (hlevel
      (volume_finitePrimeFourierSymbol_levelSet_eq_zero P c lambda))

def finitePrimeCommutingDilationHamiltonian (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) :
    FinitePrimeDilationL2 →ₗ.[ℂ] FinitePrimeDilationL2 :=
  GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) (finitePrimeSpectralMultiplier P c)

theorem finitePrimeCommutingDilationHamiltonian_isSelfAdjoint
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    IsSelfAdjoint (finitePrimeCommutingDilationHamiltonian P c) :=
  GaloisForLFunctions.HTGeometry.IsSelfAdjoint.unitaryConjugate
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
    (finitePrimeSpectralMultiplier_isSelfAdjoint P c)

theorem fourier_finitePrimeCommutingDilationHamiltonian
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ)
    (f : (finitePrimeCommutingDilationHamiltonian P c).domain) :
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
        (finitePrimeCommutingDilationHamiltonian P c f) =
      finitePrimeSpectralMultiplier P c
        (GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap
          (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
          (finitePrimeSpectralMultiplier P c) f) := by
  simp [finitePrimeCommutingDilationHamiltonian,
    GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap_apply]

theorem finitePrimeCommutingDilationHamiltonian_has_no_eigenvector
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) (lambda : ℂ)
    (f : (finitePrimeCommutingDilationHamiltonian P c).domain)
    (h : finitePrimeCommutingDilationHamiltonian P c f =
      lambda • (f : FinitePrimeDilationL2)) :
    (f : FinitePrimeDilationL2) = 0 := by
  let U := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
  let Fdom : (finitePrimeSpectralMultiplier P c).domain :=
    GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap U
      (finitePrimeSpectralMultiplier P c) f
  have hFdom : (Fdom : FinitePrimeDilationL2) = U (f : FinitePrimeDilationL2) := rfl
  have heig : finitePrimeSpectralMultiplier P c Fdom =
      lambda • (Fdom : FinitePrimeDilationL2) := by
    have hU := congrArg U h
    rw [hFdom]
    simpa [U, Fdom, finitePrimeCommutingDilationHamiltonian,
      GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap_apply] using hU
  have hzero := finitePrimeSpectralMultiplier_has_no_eigenvector P c lambda Fdom heig
  apply U.injective
  rw [← hFdom]
  simpa only [map_zero] using hzero

def finitePrimeTranslationCoupling (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) :
    FinitePrimeDilationL2 →L[ℂ] FinitePrimeDilationL2 :=
  ∑ p ∈ P,
    (c p • (GaloisForLFunctions.HTGeometry.translateL2
      (-finitePrimeLogFrequency p)).toContinuousLinearMap +
    (starRingEnd ℂ) (c p) •
      (GaloisForLFunctions.HTGeometry.translateL2
        (finitePrimeLogFrequency p)).toContinuousLinearMap)

def finitePrimeModulationCoupling (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) :
    FinitePrimeDilationL2 →L[ℂ] FinitePrimeDilationL2 :=
  ∑ p ∈ P,
    (c p • GaloisForLFunctions.HTGeometry.modulationMul (-finitePrimeLogFrequency p) +
    (starRingEnd ℂ) (c p) •
      GaloisForLFunctions.HTGeometry.modulationMul (finitePrimeLogFrequency p))

theorem fourier_finitePrimeTranslationCoupling (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (f : FinitePrimeDilationL2) :
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
        (finitePrimeTranslationCoupling P c f) =
      finitePrimeModulationCoupling P c
        ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) f) := by
  classical
  simp only [finitePrimeTranslationCoupling, finitePrimeModulationCoupling,
    sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [add_apply, smul_apply,
    map_add, map_smul]
  have hneg : (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
      ((GaloisForLFunctions.HTGeometry.translateL2
        (-finitePrimeLogFrequency p)).toContinuousLinearMap f) =
      GaloisForLFunctions.HTGeometry.modulationMul (-finitePrimeLogFrequency p)
        ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) f) := by
    change (𝓕 (GaloisForLFunctions.HTGeometry.translateL2
      (-finitePrimeLogFrequency p) f) : FinitePrimeDilationL2) =
        GaloisForLFunctions.HTGeometry.modulationMul (-finitePrimeLogFrequency p) (𝓕 f)
    exact GaloisForLFunctions.HTGeometry.fourierTransform_translateL2
      (-finitePrimeLogFrequency p) f
  have hpos : (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
      ((GaloisForLFunctions.HTGeometry.translateL2
        (finitePrimeLogFrequency p)).toContinuousLinearMap f) =
      GaloisForLFunctions.HTGeometry.modulationMul (finitePrimeLogFrequency p)
        ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) f) := by
    change (𝓕 (GaloisForLFunctions.HTGeometry.translateL2
      (finitePrimeLogFrequency p) f) : FinitePrimeDilationL2) =
        GaloisForLFunctions.HTGeometry.modulationMul (finitePrimeLogFrequency p) (𝓕 f)
    exact GaloisForLFunctions.HTGeometry.fourierTransform_translateL2
      (finitePrimeLogFrequency p) f
  rw [hneg, hpos]

theorem modulationSymbol_neg_finitePrimeLogFrequency (p : Nat.Primes) (xi : ℝ) :
    GaloisForLFunctions.HTGeometry.modulationSymbol (-finitePrimeLogFrequency p) xi =
      finitePrimeNegativePhase p (2 * Real.pi * xi) := by
  rw [GaloisForLFunctions.HTGeometry.modulationSymbol,
    finitePrimeNegativePhase_eq_exp]
  congr 1
  push_cast
  ring

theorem modulationSymbol_finitePrimeLogFrequency (p : Nat.Primes) (xi : ℝ) :
    GaloisForLFunctions.HTGeometry.modulationSymbol (finitePrimeLogFrequency p) xi =
      finitePrimePositivePhase p (2 * Real.pi * xi) := by
  rw [GaloisForLFunctions.HTGeometry.modulationSymbol,
    finitePrimePositivePhase_eq_exp]
  congr 1
  push_cast
  ring

theorem coeFn_finitePrimeModulationPair (c : Nat.Primes → ℂ)
    (p : Nat.Primes) (f : FinitePrimeDilationL2) :
    ((c p • GaloisForLFunctions.HTGeometry.modulationMul (-finitePrimeLogFrequency p) f +
      (starRingEnd ℂ) (c p) •
        GaloisForLFunctions.HTGeometry.modulationMul (finitePrimeLogFrequency p) f :
        FinitePrimeDilationL2) : ℝ → ℂ) =ᵐ[volume]
      fun xi => (finitePrimePairedTerm c p (2 * Real.pi * xi) : ℂ) *
        (f : ℝ → ℂ) xi := by
  filter_upwards [Lp.coeFn_add
      (c p • GaloisForLFunctions.HTGeometry.modulationMul (-finitePrimeLogFrequency p) f)
      ((starRingEnd ℂ) (c p) •
        GaloisForLFunctions.HTGeometry.modulationMul (finitePrimeLogFrequency p) f),
    Lp.coeFn_smul (c p)
      (GaloisForLFunctions.HTGeometry.modulationMul (-finitePrimeLogFrequency p) f),
    Lp.coeFn_smul ((starRingEnd ℂ) (c p))
      (GaloisForLFunctions.HTGeometry.modulationMul (finitePrimeLogFrequency p) f),
    GaloisForLFunctions.HTGeometry.coeFn_modulationMul (-finitePrimeLogFrequency p) f,
    GaloisForLFunctions.HTGeometry.coeFn_modulationMul (finitePrimeLogFrequency p) f]
      with xi hadd hnegsmul hpossmul hneg hpos
  rw [hadd, Pi.add_apply]
  rw [hnegsmul, hpossmul]
  change c p * (GaloisForLFunctions.HTGeometry.modulationMul
      (-finitePrimeLogFrequency p) f : ℝ → ℂ) xi +
      (starRingEnd ℂ) (c p) *
        (GaloisForLFunctions.HTGeometry.modulationMul
          (finitePrimeLogFrequency p) f : ℝ → ℂ) xi = _
  rw [hneg, hpos, modulationSymbol_neg_finitePrimeLogFrequency,
    modulationSymbol_finitePrimeLogFrequency]
  calc
    c p * (finitePrimeNegativePhase p (2 * Real.pi * xi) * (f : ℝ → ℂ) xi) +
        (starRingEnd ℂ) (c p) *
          (finitePrimePositivePhase p (2 * Real.pi * xi) * (f : ℝ → ℂ) xi) =
      (c p * finitePrimeNegativePhase p (2 * Real.pi * xi) +
        (starRingEnd ℂ) (c p) * finitePrimePositivePhase p (2 * Real.pi * xi)) *
          (f : ℝ → ℂ) xi := by ring
    _ = (finitePrimePairedTerm c p (2 * Real.pi * xi) : ℂ) * (f : ℝ → ℂ) xi := by
      rw [← ofReal_finitePrimePairedTerm_eq_pair]

theorem coeFn_finitePrimeModulationCoupling (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (f : FinitePrimeDilationL2) :
    (finitePrimeModulationCoupling P c f : ℝ → ℂ) =ᵐ[volume]
      fun xi => (finitePrimeTranslationSymbol P c (2 * Real.pi * xi) : ℂ) *
        (f : ℝ → ℂ) xi := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with xi hzero
      change ((0 : FinitePrimeDilationL2) : ℝ → ℂ) xi = _
      rw [hzero]
      simp [finitePrimeTranslationSymbol]
  | @insert p P hp ih =>
      let A : FinitePrimeDilationL2 :=
        c p • GaloisForLFunctions.HTGeometry.modulationMul (-finitePrimeLogFrequency p) f +
          (starRingEnd ℂ) (c p) •
            GaloisForLFunctions.HTGeometry.modulationMul (finitePrimeLogFrequency p) f
      have hpair := coeFn_finitePrimeModulationPair c p f
      have hadd := Lp.coeFn_add A (finitePrimeModulationCoupling P c f)
      filter_upwards [hadd, hpair, ih] with xi haddxi hpairxi ihxi
      rw [show finitePrimeModulationCoupling (insert p P) c f =
          A + finitePrimeModulationCoupling P c f by
        simp [finitePrimeModulationCoupling, hp, A]]
      rw [haddxi, Pi.add_apply]
      have hpairA : (A : ℝ → ℂ) xi =
          (finitePrimePairedTerm c p (2 * Real.pi * xi) : ℂ) * (f : ℝ → ℂ) xi := by
        simpa only [A] using hpairxi
      rw [hpairA, ihxi]
      simp only [finitePrimeTranslationSymbol, Finset.sum_insert hp]
      push_cast
      ring

theorem finitePrimeModulationCoupling_inner (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (f g : FinitePrimeDilationL2) :
    inner ℂ (finitePrimeModulationCoupling P c f) g =
      inner ℂ f (finitePrimeModulationCoupling P c g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [coeFn_finitePrimeModulationCoupling P c f,
    coeFn_finitePrimeModulationCoupling P c g] with xi hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem finitePrimeTranslationCoupling_inner (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (f g : FinitePrimeDilationL2) :
    inner ℂ (finitePrimeTranslationCoupling P c f) g =
      inner ℂ f (finitePrimeTranslationCoupling P c g) := by
  let U := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
  calc
    inner ℂ (finitePrimeTranslationCoupling P c f) g =
        inner ℂ (U (finitePrimeTranslationCoupling P c f)) (U g) :=
      (U.inner_map_map _ _).symm
    _ = inner ℂ (finitePrimeModulationCoupling P c (U f)) (U g) := by
      rw [fourier_finitePrimeTranslationCoupling]
    _ = inner ℂ (U f) (finitePrimeModulationCoupling P c (U g)) :=
      finitePrimeModulationCoupling_inner P c _ _
    _ = inner ℂ (U f) (U (finitePrimeTranslationCoupling P c g)) := by
      rw [fourier_finitePrimeTranslationCoupling]
    _ = inner ℂ f (finitePrimeTranslationCoupling P c g) :=
      U.inner_map_map _ _

theorem finitePrimeTranslationCoupling_isSelfAdjoint (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) :
    IsSelfAdjoint (finitePrimeTranslationCoupling P c) := by
  change (finitePrimeTranslationCoupling P c).adjoint = finitePrimeTranslationCoupling P c
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact finitePrimeTranslationCoupling_inner P c x y

def finitePrimeFourierCouplingSymbol (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (xi : ℝ) : ℂ :=
  (finitePrimeTranslationSymbol P c (2 * Real.pi * xi) : ℂ)

theorem measurable_finitePrimeFourierCouplingSymbol (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) :
    Measurable (finitePrimeFourierCouplingSymbol P c) := by
  apply Complex.measurable_ofReal.comp
  have hscale : Continuous fun xi : ℝ => 2 * Real.pi * xi :=
    continuous_const.mul continuous_id
  exact ((continuousOn_univ.mp
    (analyticOnNhd_finitePrimeTranslationSymbol P c).continuousOn).comp hscale).measurable

theorem norm_finitePrimeFourierCouplingSymbol_le (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (xi : ℝ) :
    ‖finitePrimeFourierCouplingSymbol P c xi‖ ≤ finitePrimeCouplingBudget P c := by
  rw [finitePrimeFourierCouplingSymbol, Complex.norm_real, Real.norm_eq_abs]
  exact abs_finitePrimeTranslationSymbol_le P c (2 * Real.pi * xi)

theorem memLp_finitePrimeFourierCouplingSymbol_mul (P : Finset Nat.Primes)
    (c : Nat.Primes → ℂ) (f : FinitePrimeDilationL2) :
    MemLp (fun xi => finitePrimeFourierCouplingSymbol P c xi * (f : ℝ → ℂ) xi)
      2 volume :=
  MeasureTheory.memLp_mul_of_bound (measurable_finitePrimeFourierCouplingSymbol P c)
    (finitePrimeCouplingBudget_nonneg P c) (norm_finitePrimeFourierCouplingSymbol_le P c) f

theorem ofReal_finitePrimeFourierSymbol_eq_linear_add_prime
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) (xi : ℝ) :
    (finitePrimeFourierSymbol P c xi : ℂ) =
      ((4 * Real.pi * xi : ℝ) : ℂ) + finitePrimeFourierCouplingSymbol P c xi := by
  simp only [finitePrimeFourierSymbol, finitePrimeDilationSymbol, finitePrimeFourierCouplingSymbol]
  push_cast
  ring

theorem mem_finitePrimeCommutingDilationHamiltonian_domain_iff
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ)
    (f : FinitePrimeDilationL2) :
    f ∈ (finitePrimeCommutingDilationHamiltonian P c).domain ↔
      MemLp (fun xi : ℝ => (xi : ℂ) *
        ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) f : ℝ → ℂ) xi)
        2 volume := by
  let U := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
  let F : FinitePrimeDilationL2 := U f
  change MemLp (fun xi : ℝ => (finitePrimeFourierSymbol P c xi : ℂ) * (F : ℝ → ℂ) xi)
      2 volume ↔ MemLp (fun xi : ℝ => (xi : ℂ) * (F : ℝ → ℂ) xi) 2 volume
  have hpot : MemLp (fun xi : ℝ =>
      finitePrimeFourierCouplingSymbol P c xi * (F : ℝ → ℂ) xi) 2 volume :=
    memLp_finitePrimeFourierCouplingSymbol_mul P c F
  have hscale : (4 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  constructor
  · intro htotal
    have hlinear : MemLp (fun xi : ℝ =>
        (((4 * Real.pi * xi : ℝ) : ℂ) * (F : ℝ → ℂ) xi)) 2 volume := by
      refine (memLp_congr_ae ?_).mpr (htotal.sub hpot)
      filter_upwards with xi
      rw [Pi.sub_apply, ofReal_finitePrimeFourierSymbol_eq_linear_add_prime]
      ring
    have hscaled := hlinear.const_mul (((4 : ℂ) * (Real.pi : ℂ))⁻¹)
    refine (memLp_congr_ae ?_).mpr hscaled
    filter_upwards with xi
    change (xi : ℂ) * (F : ℝ → ℂ) xi =
      ((4 : ℂ) * (Real.pi : ℂ))⁻¹ *
        (((4 * Real.pi * xi : ℝ) : ℂ) * (F : ℝ → ℂ) xi)
    push_cast
    field_simp
  · intro hcoordinate
    have hscaled := hcoordinate.const_mul ((4 : ℂ) * (Real.pi : ℂ))
    have hlinear : MemLp (fun xi : ℝ =>
        (((4 * Real.pi * xi : ℝ) : ℂ) * (F : ℝ → ℂ) xi)) 2 volume := by
      refine (memLp_congr_ae ?_).mpr hscaled
      filter_upwards with xi
      change (((4 * Real.pi * xi : ℝ) : ℂ) * (F : ℝ → ℂ) xi) =
        ((4 : ℂ) * (Real.pi : ℂ)) * ((xi : ℂ) * (F : ℝ → ℂ) xi)
      push_cast
      ring
    refine (memLp_congr_ae ?_).mpr (hlinear.add hpot)
    filter_upwards with xi
    rw [Pi.add_apply, ofReal_finitePrimeFourierSymbol_eq_linear_add_prime]
    ring

theorem finitePrimeCommutingDilationHamiltonian_domain_eq_weakDerivativeDomain
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    (finitePrimeCommutingDilationHamiltonian P c).domain =
      RHTower.weightOneLogDerivative.domain := by
  ext f
  rw [mem_finitePrimeCommutingDilationHamiltonian_domain_iff]
  change MemLp (fun xi : ℝ => (xi : ℂ) *
      ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) f : ℝ → ℂ) xi) 2 volume ↔
    MemLp (fun xi : ℝ => (xi : ℂ) *
      (RHTower.fourierUnitary f : ℝ → ℂ) xi) 2 volume
  rfl

def dilationGenerator :
    FinitePrimeDilationL2 →ₗ.[ℂ] FinitePrimeDilationL2 :=
  finitePrimeCommutingDilationHamiltonian ∅ (fun _ => 0)

theorem dilationGenerator_isSelfAdjoint :
    IsSelfAdjoint dilationGenerator :=
  finitePrimeCommutingDilationHamiltonian_isSelfAdjoint ∅ (fun _ => 0)

theorem dilationGenerator_domain_eq_weakDerivativeDomain :
    dilationGenerator.domain = RHTower.weightOneLogDerivative.domain :=
  finitePrimeCommutingDilationHamiltonian_domain_eq_weakDerivativeDomain ∅ (fun _ => 0)

theorem finitePrimeCommutingDilationHamiltonian_domain_eq_dilationGeneratorDomain
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    (finitePrimeCommutingDilationHamiltonian P c).domain = dilationGenerator.domain := by
  rw [finitePrimeCommutingDilationHamiltonian_domain_eq_weakDerivativeDomain,
    dilationGenerator_domain_eq_weakDerivativeDomain]

theorem fourier_finitePrimeCommutingDilationHamiltonian_apply_ae
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ)
    (f : (finitePrimeCommutingDilationHamiltonian P c).domain) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
      (finitePrimeCommutingDilationHamiltonian P c f) : ℝ → ℂ) =ᵐ[volume]
      fun xi => (finitePrimeFourierSymbol P c xi : ℂ) *
        ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
          (f : FinitePrimeDilationL2) : ℝ → ℂ) xi := by
  let Fdom : (finitePrimeSpectralMultiplier P c).domain :=
    GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap
      (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
      (finitePrimeSpectralMultiplier P c) f
  have heq := fourier_finitePrimeCommutingDilationHamiltonian P c f
  rw [heq]
  have happ := finitePrimeSpectralMultiplier_apply_ae P c Fdom
  have hFdom : (Fdom : FinitePrimeDilationL2) =
      (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
        (f : FinitePrimeDilationL2) := rfl
  filter_upwards [happ] with xi hxi
  rw [hxi, hFdom]

theorem finitePrimeCommutingDilationHamiltonian_eq_dilation_add_primeTranslation
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ)
    (f : (finitePrimeCommutingDilationHamiltonian P c).domain) :
    let fD : dilationGenerator.domain :=
      ⟨(f : FinitePrimeDilationL2), by
        rw [← finitePrimeCommutingDilationHamiltonian_domain_eq_dilationGeneratorDomain P c]
        exact f.property⟩
    finitePrimeCommutingDilationHamiltonian P c f =
      dilationGenerator fD +
        finitePrimeTranslationCoupling P c (f : FinitePrimeDilationL2) := by
  dsimp only
  let fD : dilationGenerator.domain :=
    ⟨(f : FinitePrimeDilationL2), by
      rw [← finitePrimeCommutingDilationHamiltonian_domain_eq_dilationGeneratorDomain P c]
      exact f.property⟩
  let U := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
  apply U.injective
  rw [map_add]
  apply Lp.ext
  have hH := fourier_finitePrimeCommutingDilationHamiltonian_apply_ae P c f
  have hD := fourier_finitePrimeCommutingDilationHamiltonian_apply_ae
    (∅ : Finset Nat.Primes) (fun _ => 0) fD
  change (U (dilationGenerator fD) : ℝ → ℂ) =ᵐ[volume]
    fun xi => (finitePrimeFourierSymbol ∅ (fun _ => 0) xi : ℂ) *
      (U (fD : FinitePrimeDilationL2) : ℝ → ℂ) xi at hD
  have hVeq := fourier_finitePrimeTranslationCoupling P c (f : FinitePrimeDilationL2)
  have hV : (U (finitePrimeTranslationCoupling P c (f : FinitePrimeDilationL2)) :
      ℝ → ℂ) =ᵐ[volume]
      fun xi => finitePrimeFourierCouplingSymbol P c xi *
        (U (f : FinitePrimeDilationL2) : ℝ → ℂ) xi := by
    rw [hVeq]
    exact coeFn_finitePrimeModulationCoupling P c (U (f : FinitePrimeDilationL2))
  have hadd := Lp.coeFn_add (U (dilationGenerator fD))
    (U (finitePrimeTranslationCoupling P c (f : FinitePrimeDilationL2)))
  filter_upwards [hH, hD, hV, hadd] with xi hHxi hDxi hVxi haddxi
  rw [hHxi, haddxi, Pi.add_apply, hDxi, hVxi]
  rw [ofReal_finitePrimeFourierSymbol_eq_linear_add_prime,
    ofReal_finitePrimeFourierSymbol_eq_linear_add_prime]
  simp only [finitePrimeFourierCouplingSymbol, finitePrimeTranslationSymbol, Finset.sum_empty,
    Complex.ofReal_zero, add_zero]
  ring

theorem dilationGenerator_eq_neg_two_I_weakDerivative
    (f : dilationGenerator.domain) :
    let fW : RHTower.weightOneLogDerivative.domain :=
      ⟨(f : FinitePrimeDilationL2), by
        rw [← dilationGenerator_domain_eq_weakDerivativeDomain]
        exact f.property⟩
    dilationGenerator f =
      (-2 * Complex.I) • RHTower.weightOneLogDerivative fW := by
  dsimp only
  let fW : RHTower.weightOneLogDerivative.domain :=
    ⟨(f : FinitePrimeDilationL2), by
      rw [← dilationGenerator_domain_eq_weakDerivativeDomain]
      exact f.property⟩
  let U := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
  apply U.injective
  rw [map_smul]
  apply Lp.ext
  have hD := fourier_finitePrimeCommutingDilationHamiltonian_apply_ae
    (∅ : Finset Nat.Primes) (fun _ => 0) f
  change (U (dilationGenerator f) : ℝ → ℂ) =ᵐ[volume]
    fun xi => (finitePrimeFourierSymbol ∅ (fun _ => 0) xi : ℂ) *
      (U (f : FinitePrimeDilationL2) : ℝ → ℂ) xi at hD
  have hweak := RHTower.weightOneLogDerivative_isWeakDerivative fW
  have hFourier := RHTower.l2_fourier_weakDerivative_ae
    (f : FinitePrimeDilationL2)
    (RHTower.weightOneLogDerivative fW) hweak
  change (U (RHTower.weightOneLogDerivative fW) : ℝ → ℂ) =ᵐ[volume]
    fun xi => (2 * Real.pi * Complex.I * xi) •
      (U (f : FinitePrimeDilationL2) : ℝ → ℂ) xi at hFourier
  have hsmul := Lp.coeFn_smul (-2 * Complex.I)
    (U (RHTower.weightOneLogDerivative fW))
  filter_upwards [hD, hFourier, hsmul] with xi hDxi hFourierxi hsmulxi
  rw [hDxi, hsmulxi]
  change (finitePrimeFourierSymbol ∅ (fun _ => 0) xi : ℂ) *
      (U (f : FinitePrimeDilationL2) : ℝ → ℂ) xi =
    (-2 * Complex.I) *
      (U (RHTower.weightOneLogDerivative fW) : ℝ → ℂ) xi
  rw [hFourierxi]
  change (finitePrimeFourierSymbol ∅ (fun _ => 0) xi : ℂ) *
      (U (f : FinitePrimeDilationL2) : ℝ → ℂ) xi =
    (-2 * Complex.I) *
      ((2 * (Real.pi : ℂ) * Complex.I * (xi : ℂ)) *
        (U (f : FinitePrimeDilationL2) : ℝ → ℂ) xi)
  rw [ofReal_finitePrimeFourierSymbol_eq_linear_add_prime]
  simp only [finitePrimeFourierCouplingSymbol, finitePrimeTranslationSymbol, Finset.sum_empty,
    Complex.ofReal_zero, add_zero]
  push_cast
  calc
    4 * (Real.pi : ℂ) * (xi : ℂ) *
        (U (f : FinitePrimeDilationL2) : ℝ → ℂ) xi =
      (-4 * (Real.pi : ℂ) * (xi : ℂ) *
        (U (f : FinitePrimeDilationL2) : ℝ → ℂ) xi) * (-1) := by ring
    _ = (-4 * (Real.pi : ℂ) * (xi : ℂ) *
        (U (f : FinitePrimeDilationL2) : ℝ → ℂ) xi) *
          (Complex.I * Complex.I) := by rw [Complex.I_mul_I]
    _ = (-2 * Complex.I) *
        (2 * (Real.pi : ℂ) * Complex.I * (xi : ℂ) *
          (U (f : FinitePrimeDilationL2) : ℝ → ℂ) xi) := by ring

theorem primePhaseRank_exact (N : ℕ) :
    LinearIndependent ℤ
      (fun p : (N.primesBelow : Finset ℕ) => Real.log (p : ℕ)) :=
  GaloisForLFunctions.primeLog_primesBelow_linearIndependent N

theorem primePhaseRank_eq_primeCounting (N : ℕ) :
    LinearIndependent ℤ
        (fun p : (N.primesBelow : Finset ℕ) => Real.log (p : ℕ)) ∧
      (N.primesBelow).card = Nat.primeCounting' N :=
  ⟨primePhaseRank_exact N,
    GaloisForLFunctions.primesBelow_card_eq_primeCounting' N⟩

/-- Exact finite-prime commuting-dilation classification. Every finite prime packet and every
self-adjoint coefficient pairing gives a bounded self-adjoint translation coupling on the common
maximal dilation domain. The full Hamiltonian is self-adjoint, its scalar direct-integral spectral
measure is Lebesgue-absolutely-continuous, and every point-eigenvalue equation has only the zero
vector. No coefficient smallness, genericity, or prime-log independence premise is used. -/
theorem finitePrimeCommutingDilation_spectralClassification
    (P : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    IsSelfAdjoint (finitePrimeCommutingDilationHamiltonian P c) ∧
      IsSelfAdjoint (finitePrimeTranslationCoupling P c) ∧
      Measure.map (finitePrimeFourierSymbol P c) (volume : Measure ℝ) ≪ volume ∧
      (∀ (lambda : ℂ) (f : (finitePrimeCommutingDilationHamiltonian P c).domain),
        finitePrimeCommutingDilationHamiltonian P c f =
          lambda • (f : FinitePrimeDilationL2) →
        (f : FinitePrimeDilationL2) = 0) ∧
      (∀ ⦃K : Set ℝ⦄, IsCompact K → IsCompact (finitePrimeDilationSymbol P c ⁻¹' K)) ∧
      Tendsto (finitePrimeDilationSymbol P c) atTop atTop ∧
      Tendsto (finitePrimeDilationSymbol P c) atBot atBot ∧
      (∀ f : (finitePrimeCommutingDilationHamiltonian P c).domain,
        let fD : dilationGenerator.domain :=
          ⟨(f : FinitePrimeDilationL2), by
            rw [← finitePrimeCommutingDilationHamiltonian_domain_eq_dilationGeneratorDomain P c]
            exact f.property⟩
        finitePrimeCommutingDilationHamiltonian P c f =
          dilationGenerator fD +
            finitePrimeTranslationCoupling P c (f : FinitePrimeDilationL2)) := by
  exact ⟨finitePrimeCommutingDilationHamiltonian_isSelfAdjoint P c,
    finitePrimeTranslationCoupling_isSelfAdjoint P c,
    finitePrimeFourierSymbol_spectralMeasure_absolutelyContinuous P c,
    fun lambda f h =>
      finitePrimeCommutingDilationHamiltonian_has_no_eigenvector P c lambda f h,
    fun _ hK => finitePrimeDilationSymbol_compactPreimageProper P c hK,
    tendsto_finitePrimeDilationSymbol_atTop P c,
    tendsto_finitePrimeDilationSymbol_atBot P c,
    fun f => finitePrimeCommutingDilationHamiltonian_eq_dilation_add_primeTranslation P c f⟩

end GaloisForLFunctions.RHTower
