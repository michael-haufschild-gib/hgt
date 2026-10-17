import GaloisForLFunctions.BiScaleUncertainty.SpectralLaplaceEnergyCriticalLine
import GaloisForLFunctions.RHTower.Sieve.DirichletMeanValueSharp
import GaloisForLFunctions.RHTower.Sieve.DirichletMVTWindow

/-!
# The high-frequency part of the Laplace energy is small: the mean value theorem on the critical line

The spectral density of the Laplace energy is `S_N(ξ) = ‖ν̂_N(ξ)‖² / (¼ + 4π²ξ²)`, with
`ν̂_N = A_N − P_N` the atomic Dirichlet polynomial `A_N(ξ) = Σ_{n ≤ N+2} Λ(n) n^{−½−2πiξ}` minus the
two pole terms `P_N`.  The Montgomery–Vaughan mean value theorem of the corpus bounds the two-sided
mean square of `A_N` on `[−u, u]` by `2u D₁ + 208 D₂`, where `D₁ = Σ Λ(n)²/n` and `D₂ = Σ Λ(n)²`
are the diagonal sums; the pole terms are `O(e^{L/2}/|ξ|)`.  One integration by parts against the
weight `1/u²` then gives, for every `0 < ξ₀ ≤ ξ₁`,

`∫_{ξ₀}^{ξ₁} (S_N(ξ) + S_N(−ξ)) dξ ≤ 2D₁/(π²ξ₀) + 52 D₂/(π³ξ₀²) + 4(e^{L/2}+3)²/(3(2π)⁴ξ₀³)`,

uniformly in `ξ₁`, hence the same bound for the whole two-sided tail `|ξ| ≥ ξ₀`.  Since `D₁ ≤ L·Σ Λ(n)/n`
and `D₂ ≤ L·ψ(N+2)`, the Laplace energy carried by frequencies `|ξ| ≥ e^{L/2} = √(N+2)` is
unconditionally `O(L)`: the square-root barrier lives entirely in the band `|ξ| < √x`, the frequency
side of the bi-scale uncertainty `(position √x) × (frequency √x)`.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported Real FourierTransform

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar RHTower.Sieve
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## The atomic and polar parts of the spectral density -/

/-- The atomic part `A_N(ξ) = Σ_{n ≤ N+2} Λ(n) n^{−1/2} e^{−2πiξ log n}` of `ν̂_N`. -/
def atomicFourier (N : ℕ) (ξ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (N + 2), (primeWeight n : ℂ) * frequencyCharacter ξ (Real.log n)

/-- The polar part `P_N(ξ) = ∫_0^L 2cosh(x/2) e^{−2πiξx} dx` of `ν̂_N`. -/
def polarFourier (N : ℕ) (ξ : ℝ) : ℂ :=
  ∫ x in Icc 0 (cutoff N), (polarDensity x : ℂ) * frequencyCharacter ξ x

theorem fourierPairing_eq_atomic_sub_polar (N : ℕ) (ξ : ℝ) :
    fourierPairing N ξ = atomicFourier N ξ - polarFourier N ξ := rfl

/-- The atomic coefficients `a_m = Λ(m+1)/√(m+1)`, `m < N+2`. -/
def atomicCoefficient (N : ℕ) : Fin (N + 2) → ℂ := fun m => (primeWeight ((m : ℕ) + 1) : ℂ)

/-- **The atomic part is the corpus Dirichlet polynomial at `t = −2πξ`.** -/
theorem atomicFourier_eq_dirPoly (N : ℕ) (ξ : ℝ) :
    atomicFourier N ξ = dirPoly (N + 2) (atomicCoefficient N) (-(2 * π * ξ)) := by
  unfold atomicFourier dirPoly atomicCoefficient
  have h1 := Fin.sum_univ_eq_sum_range (fun k : ℕ => (primeWeight (k + 1) : ℂ) *
    Complex.exp (((-(2 * π * ξ) * Real.log ((k : ℝ) + 1) : ℝ) : ℂ) * Complex.I)) (N + 2)
  rw [h1]
  have hIco : Finset.Icc 1 (N + 2) = Finset.Ico 1 (N + 3) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIco, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun k _ => ?_
  rw [show 1 + k = k + 1 by ring]
  congr 1
  unfold frequencyCharacter
  congr 1
  push_cast
  ring

theorem continuous_dirPoly (M : ℕ) (a : Fin M → ℂ) : Continuous (dirPoly M a) := by
  unfold dirPoly
  refine continuous_finsetSum _ fun m _ => continuous_const.mul ?_
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul continuous_const)

theorem continuous_atomicFourier (N : ℕ) : Continuous (atomicFourier N) := by
  have : atomicFourier N = fun ξ => dirPoly (N + 2) (atomicCoefficient N) (-(2 * π * ξ)) :=
    funext (atomicFourier_eq_dirPoly N)
  rw [this]
  exact (continuous_dirPoly _ _).comp (continuous_const.mul continuous_id).neg

theorem criticalPoint_eq (ξ : ℝ) :
    criticalPoint ξ = ((1 / 2 : ℝ) : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [criticalPoint]

theorem continuous_criticalPoint : Continuous criticalPoint := by
  have : criticalPoint = fun ξ => ((1 / 2 : ℝ) : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * Complex.I :=
    funext criticalPoint_eq
  rw [this]
  fun_prop

theorem polarFourier_eq (N : ℕ) (ξ : ℝ) :
    polarFourier N ξ =
      (Complex.exp ((1 - criticalPoint ξ) * cutoff N) - 1) / (1 - criticalPoint ξ) +
        (1 - Complex.exp (-criticalPoint ξ * cutoff N)) / criticalPoint ξ :=
  integral_polarDensity_mul_frequencyCharacter N ξ

theorem continuous_polarFourier (N : ℕ) : Continuous (polarFourier N) := by
  have : polarFourier N = fun ξ =>
      (Complex.exp ((1 - criticalPoint ξ) * cutoff N) - 1) / (1 - criticalPoint ξ) +
        (1 - Complex.exp (-criticalPoint ξ * cutoff N)) / criticalPoint ξ :=
    funext (polarFourier_eq N)
  rw [this]
  refine Continuous.add (Continuous.div ?_ (continuous_const.sub continuous_criticalPoint)
    one_sub_criticalPoint_ne_zero) (Continuous.div ?_ continuous_criticalPoint criticalPoint_ne_zero)
  · exact (Complex.continuous_exp.comp ((continuous_const.sub continuous_criticalPoint).mul
      continuous_const)).sub continuous_const
  · exact continuous_const.sub (Complex.continuous_exp.comp
      (continuous_criticalPoint.neg.mul continuous_const))

theorem continuous_fourierPairing (N : ℕ) : Continuous (fourierPairing N) := by
  have : fourierPairing N = fun ξ => atomicFourier N ξ - polarFourier N ξ := rfl
  rw [this]
  exact (continuous_atomicFourier N).sub (continuous_polarFourier N)

/-- The spectral density of the Laplace energy. -/
def spectralDensity (N : ℕ) (ξ : ℝ) : ℝ := ‖fourierPairing N ξ‖ ^ 2 / (1 / 4 + (2 * π * ξ) ^ 2)

theorem laplaceEnergy_eq_integral_spectralDensity (N : ℕ) :
    laplaceEnergy N = ∫ ξ, spectralDensity N ξ :=
  laplaceEnergy_eq_integral_fourierPairing_sq N

theorem spectralDensity_nonneg (N : ℕ) (ξ : ℝ) : 0 ≤ spectralDensity N ξ := by
  unfold spectralDensity; positivity

theorem continuous_spectralDensity (N : ℕ) : Continuous (spectralDensity N) := by
  unfold spectralDensity
  refine Continuous.div (((continuous_fourierPairing N).norm).pow 2) (by fun_prop) fun ξ => ?_
  positivity

theorem spectralDensity_le_mass_sq_div (N : ℕ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    spectralDensity N ξ ≤ mass N ^ 2 / (2 * π * ξ) ^ 2 := by
  unfold spectralDensity
  have hpos : 0 < (2 * π * ξ) ^ 2 := by positivity
  calc ‖fourierPairing N ξ‖ ^ 2 / (1 / 4 + (2 * π * ξ) ^ 2)
      ≤ ‖fourierPairing N ξ‖ ^ 2 / (2 * π * ξ) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) hpos (by linarith)
    _ ≤ mass N ^ 2 / (2 * π * ξ) ^ 2 :=
        div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (norm_fourierPairing_le N ξ) 2) hpos.le

/-! ## The polar part is `O(e^{L/2}/|s|)` -/

theorem norm_one_sub_criticalPoint (ξ : ℝ) : ‖1 - criticalPoint ξ‖ = ‖criticalPoint ξ‖ := by
  rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, Complex.sq_norm,
    Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp [criticalPoint]
  ring

theorem norm_polarFourier_le (N : ℕ) (ξ : ℝ) :
    ‖polarFourier N ξ‖ ≤ (Real.exp (cutoff N / 2) + 3) / ‖criticalPoint ξ‖ := by
  have hs0 : 0 ≤ ‖criticalPoint ξ‖ := norm_nonneg _
  have he1 : ‖Complex.exp ((1 - criticalPoint ξ) * cutoff N)‖ = Real.exp (cutoff N / 2) := by
    rw [Complex.norm_exp]; congr 1; simp [criticalPoint]; ring
  have he2 : ‖Complex.exp (-criticalPoint ξ * cutoff N)‖ ≤ 1 := by
    rw [Complex.norm_exp, re_neg_criticalPoint_mul]
    exact Real.exp_le_one_iff.2 (by linarith [cutoff_nonneg N])
  rw [polarFourier_eq]
  calc ‖(Complex.exp ((1 - criticalPoint ξ) * cutoff N) - 1) / (1 - criticalPoint ξ) +
        (1 - Complex.exp (-criticalPoint ξ * cutoff N)) / criticalPoint ξ‖
      ≤ ‖Complex.exp ((1 - criticalPoint ξ) * cutoff N) - 1‖ / ‖1 - criticalPoint ξ‖ +
          ‖1 - Complex.exp (-criticalPoint ξ * cutoff N)‖ / ‖criticalPoint ξ‖ := by
        rw [← norm_div, ← norm_div]; exact norm_add_le _ _
    _ ≤ (Real.exp (cutoff N / 2) + 1) / ‖criticalPoint ξ‖ + 2 / ‖criticalPoint ξ‖ := by
        rw [norm_one_sub_criticalPoint]
        refine add_le_add (div_le_div_of_nonneg_right ?_ hs0) (div_le_div_of_nonneg_right ?_ hs0)
        · exact (norm_sub_le _ _).trans (by rw [he1, norm_one])
        · exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    _ = (Real.exp (cutoff N / 2) + 3) / ‖criticalPoint ξ‖ := by ring

theorem norm_polarFourier_sq_le (N : ℕ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖polarFourier N ξ‖ ^ 2 ≤ (Real.exp (cutoff N / 2) + 3) ^ 2 / (2 * π * ξ) ^ 2 := by
  have hpos : 0 < (2 * π * ξ) ^ 2 := by positivity
  have hs : ‖criticalPoint ξ‖ ^ 2 = 1 / 4 + (2 * π * ξ) ^ 2 := by
    rw [Complex.sq_norm, normSq_criticalPoint]
  calc ‖polarFourier N ξ‖ ^ 2
      ≤ ((Real.exp (cutoff N / 2) + 3) / ‖criticalPoint ξ‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_polarFourier_le N ξ) 2
    _ = (Real.exp (cutoff N / 2) + 3) ^ 2 / (1 / 4 + (2 * π * ξ) ^ 2) := by rw [div_pow, hs]
    _ ≤ (Real.exp (cutoff N / 2) + 3) ^ 2 / (2 * π * ξ) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) hpos (by linarith)

/-! ## The Montgomery–Vaughan bound for the two-sided atomic mean square -/

/-- `D₁ = Σ_{n ≤ N+2} Λ(n)²/n`, the diagonal of the atomic coefficients. -/
def atomicDiagonal (N : ℕ) : ℝ := ∑ m : Fin (N + 2), ‖atomicCoefficient N m‖ ^ 2

/-- `D₂ = Σ_{n ≤ N+2} Λ(n)²`, the weighted diagonal entering the sharp mean value theorem. -/
def atomicSecondMoment (N : ℕ) : ℝ :=
  ∑ m : Fin (N + 2), (((m : ℕ) : ℝ) + 1) * ‖atomicCoefficient N m‖ ^ 2

theorem atomicDiagonal_nonneg (N : ℕ) : 0 ≤ atomicDiagonal N :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem atomicSecondMoment_nonneg (N : ℕ) : 0 ≤ atomicSecondMoment N :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The two-sided mean square `∫_{−u}^{u} ‖A_N‖²` of the atomic Dirichlet polynomial. -/
def twoSidedAtomicMean (N : ℕ) (u : ℝ) : ℝ :=
  ∫ t in (-u)..u, ‖dirPoly (N + 2) (atomicCoefficient N) t‖ ^ 2

theorem twoSidedAtomicMean_eq_sub (N : ℕ) (u : ℝ) :
    twoSidedAtomicMean N u =
      (∫ t in (0 : ℝ)..u, ‖dirPoly (N + 2) (atomicCoefficient N) t‖ ^ 2) -
        ∫ t in (0 : ℝ)..(-u), ‖dirPoly (N + 2) (atomicCoefficient N) t‖ ^ 2 := by
  unfold twoSidedAtomicMean
  rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_normSq_dirPoly _ _ _ _)
    (intervalIntegrable_normSq_dirPoly _ _ _ _)]

/-- **Montgomery–Vaughan, two-sided:** `∫_{−u}^{u} ‖A_N‖² ≤ 2u D₁ + 208 D₂`. -/
theorem twoSidedAtomicMean_le (N : ℕ) (u : ℝ) :
    twoSidedAtomicMean N u ≤ 2 * u * atomicDiagonal N + 208 * atomicSecondMoment N := by
  have h1 := abs_le.1 (dirichlet_meanValue_sharp (N + 2) (atomicCoefficient N) u)
  have h2 := abs_le.1 (dirichlet_meanValue_sharp (N + 2) (atomicCoefficient N) (-u))
  rw [twoSidedAtomicMean_eq_sub]
  unfold atomicDiagonal atomicSecondMoment
  nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem twoSidedAtomicMean_nonneg (N : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ twoSidedAtomicMean N u :=
  intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity

theorem hasDerivAt_twoSidedAtomicMean (N : ℕ) (u : ℝ) :
    HasDerivAt (twoSidedAtomicMean N)
      (‖dirPoly (N + 2) (atomicCoefficient N) u‖ ^ 2 +
        ‖dirPoly (N + 2) (atomicCoefficient N) (-u)‖ ^ 2) u := by
  have hFc : Continuous fun t => ‖dirPoly (N + 2) (atomicCoefficient N) t‖ ^ 2 :=
    continuous_normSq_dirPoly _ _
  have hfun : twoSidedAtomicMean N = fun u =>
      (∫ t in (0 : ℝ)..u, ‖dirPoly (N + 2) (atomicCoefficient N) t‖ ^ 2) -
        ∫ t in (0 : ℝ)..(-u), ‖dirPoly (N + 2) (atomicCoefficient N) t‖ ^ 2 :=
    funext (twoSidedAtomicMean_eq_sub N)
  rw [hfun]
  have h1 : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, ‖dirPoly (N + 2) (atomicCoefficient N) t‖ ^ 2)
      (‖dirPoly (N + 2) (atomicCoefficient N) u‖ ^ 2) u :=
    intervalIntegral.integral_hasDerivAt_right (hFc.intervalIntegrable _ _)
      (hFc.stronglyMeasurableAtFilter _ _) hFc.continuousAt
  have h2 : HasDerivAt (fun u => ∫ t in (0 : ℝ)..(-u), ‖dirPoly (N + 2) (atomicCoefficient N) t‖ ^ 2)
      (‖dirPoly (N + 2) (atomicCoefficient N) (-u)‖ ^ 2 * (-1)) u := by
    have h0 : HasDerivAt (fun v => ∫ t in (0 : ℝ)..v, ‖dirPoly (N + 2) (atomicCoefficient N) t‖ ^ 2)
        (‖dirPoly (N + 2) (atomicCoefficient N) (-u)‖ ^ 2) (-u) :=
      intervalIntegral.integral_hasDerivAt_right (hFc.intervalIntegrable _ _)
        (hFc.stronglyMeasurableAtFilter _ _) hFc.continuousAt
    exact h0.comp u (hasDerivAt_neg u)
  exact (h1.sub h2).congr_deriv (by ring)

/-! ## Integration by parts against `1/u²` -/

/-- The two-sided atomic mean square weighted by `1/u²` over a high-frequency window. -/
theorem integral_twoSided_atomic_div_sq_le (N : ℕ) {T₀ T₁ : ℝ} (h0 : 0 < T₀) (h01 : T₀ ≤ T₁) :
    (∫ u in T₀..T₁, (‖dirPoly (N + 2) (atomicCoefficient N) u‖ ^ 2 +
        ‖dirPoly (N + 2) (atomicCoefficient N) (-u)‖ ^ 2) / u ^ 2) ≤
      4 * atomicDiagonal N / T₀ + 208 * atomicSecondMoment N / T₀ ^ 2 := by
  set D₁ := atomicDiagonal N with hD₁
  set D₂ := atomicSecondMoment N with hD₂
  have hD₁0 : 0 ≤ D₁ := atomicDiagonal_nonneg N
  have hD₂0 : 0 ≤ D₂ := atomicSecondMoment_nonneg N
  set Hs : ℝ → ℝ := fun u => ‖dirPoly (N + 2) (atomicCoefficient N) u‖ ^ 2 +
    ‖dirPoly (N + 2) (atomicCoefficient N) (-u)‖ ^ 2 with hHs
  have hHsc : Continuous Hs :=
    (continuous_normSq_dirPoly _ _).add ((continuous_normSq_dirPoly _ _).comp continuous_neg)
  have hHs0 : ∀ u, 0 ≤ Hs u := fun u => by positivity
  have hT1 : 0 < T₁ := lt_of_lt_of_le h0 h01
  have hne : ∀ x ∈ uIcc T₀ T₁, x ≠ 0 := fun x hx => by
    rw [uIcc_of_le h01] at hx; exact (lt_of_lt_of_le h0 hx.1).ne'
  -- the weight and its derivative
  have hv : ∀ x ∈ uIcc T₀ T₁, HasDerivAt (fun x : ℝ => (x ^ 2)⁻¹) (-(2 * x) / (x ^ 2) ^ 2) x := by
    intro x hx
    have := (hasDerivAt_pow 2 x).inv (pow_ne_zero 2 (hne x hx))
    refine this.congr_deriv ?_
    norm_num
  have hG : ∀ x ∈ uIcc T₀ T₁, HasDerivAt (twoSidedAtomicMean N) (Hs x) x :=
    fun x _ => hasDerivAt_twoSidedAtomicMean N x
  have hv'c : ContinuousOn (fun x : ℝ => -(2 * x) / (x ^ 2) ^ 2) (uIcc T₀ T₁) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    exact pow_ne_zero 2 (pow_ne_zero 2 (hne x hx))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hv hG
    (hv'c.intervalIntegrable) (hHsc.intervalIntegrable _ _)
  -- hibp : ∫ (x²)⁻¹ * Hs x = (T₁²)⁻¹ * G T₁ − (T₀²)⁻¹ * G T₀ − ∫ (−2x/(x²)²) * G x
  have hint : (∫ u in T₀..T₁, Hs u / u ^ 2) = ∫ u in T₀..T₁, (u ^ 2)⁻¹ * Hs u :=
    intervalIntegral.integral_congr fun u _ => by rw [div_eq_inv_mul]
  -- the derivative integral is bounded through Montgomery–Vaughan
  have hGle : ∀ x ∈ Icc T₀ T₁, (-(2 * x) / (x ^ 2) ^ 2) * twoSidedAtomicMean N x ≥
      -((2 * x / (x ^ 2) ^ 2) * (2 * x * D₁ + 208 * D₂)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le h0 hx.1
    have hw : 0 ≤ 2 * x / (x ^ 2) ^ 2 := by positivity
    have := twoSidedAtomicMean_le N x
    have : (2 * x / (x ^ 2) ^ 2) * twoSidedAtomicMean N x ≤
        (2 * x / (x ^ 2) ^ 2) * (2 * x * D₁ + 208 * D₂) := mul_le_mul_of_nonneg_left this hw
    have e : (-(2 * x) / (x ^ 2) ^ 2) * twoSidedAtomicMean N x =
        -((2 * x / (x ^ 2) ^ 2) * twoSidedAtomicMean N x) := by ring
    rw [e]; linarith
  have hGc : Continuous (twoSidedAtomicMean N) :=
    continuous_iff_continuousAt.2 fun u => (hasDerivAt_twoSidedAtomicMean N u).continuousAt
  have hwc : ContinuousOn (fun x : ℝ => 2 * x / (x ^ 2) ^ 2 * (2 * x * D₁ + 208 * D₂)) (uIcc T₀ T₁) := by
    refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_) (by fun_prop)
    exact pow_ne_zero 2 (pow_ne_zero 2 (hne x hx))
  -- the comparison integral has an explicit antiderivative
  have hA : ∀ x ∈ uIcc T₀ T₁, HasDerivAt (fun x : ℝ => -4 * D₁ * x⁻¹ - 208 * D₂ * (x ^ 2)⁻¹)
      (2 * x / (x ^ 2) ^ 2 * (2 * x * D₁ + 208 * D₂)) x := by
    intro x hx
    have hx0 : x ≠ 0 := hne x hx
    have h1 := ((hasDerivAt_inv hx0).const_mul (-4 * D₁)).sub
      (((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx0)).const_mul (208 * D₂))
    refine h1.congr_deriv ?_
    field_simp
    ring
  have hcomp : (∫ x in T₀..T₁, 2 * x / (x ^ 2) ^ 2 * (2 * x * D₁ + 208 * D₂)) =
      (-4 * D₁ * T₁⁻¹ - 208 * D₂ * (T₁ ^ 2)⁻¹) - (-4 * D₁ * T₀⁻¹ - 208 * D₂ * (T₀ ^ 2)⁻¹) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hA hwc.intervalIntegrable
  -- monotonicity of the derivative integral
  have hmono : (∫ x in T₀..T₁, -((2 * x / (x ^ 2) ^ 2) * (2 * x * D₁ + 208 * D₂))) ≤
      ∫ x in T₀..T₁, (-(2 * x) / (x ^ 2) ^ 2) * twoSidedAtomicMean N x := by
    refine intervalIntegral.integral_mono_on h01 hwc.neg.intervalIntegrable
      ((hv'c.mul hGc.continuousOn).intervalIntegrable) fun x hx => ?_
    exact le_of_eq_of_le (by ring) (hGle x hx)
  rw [intervalIntegral.integral_neg, hcomp] at hmono
  -- the boundary terms
  have hb1 : (T₁ ^ 2)⁻¹ * twoSidedAtomicMean N T₁ ≤ 2 * D₁ * T₁⁻¹ + 208 * D₂ * (T₁ ^ 2)⁻¹ := by
    have := mul_le_mul_of_nonneg_left (twoSidedAtomicMean_le N T₁)
      (inv_nonneg.2 (sq_nonneg T₁) : (0 : ℝ) ≤ (T₁ ^ 2)⁻¹)
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  have hb0 : 0 ≤ (T₀ ^ 2)⁻¹ * twoSidedAtomicMean N T₀ :=
    mul_nonneg (inv_nonneg.2 (sq_nonneg T₀)) (twoSidedAtomicMean_nonneg N h0.le)
  have hD₁T : 0 ≤ D₁ * T₁⁻¹ := mul_nonneg hD₁0 (inv_nonneg.2 hT1.le)
  rw [hint, hibp]
  have hfinal : 4 * D₁ / T₀ + 208 * D₂ / T₀ ^ 2 = 4 * D₁ * T₀⁻¹ + 208 * D₂ * (T₀ ^ 2)⁻¹ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [hfinal]
  linarith

/-! ## The high-frequency window of the spectral density -/

theorem norm_atomicFourier_neg (N : ℕ) (ξ : ℝ) :
    atomicFourier N (-ξ) = dirPoly (N + 2) (atomicCoefficient N) (2 * π * ξ) := by
  rw [atomicFourier_eq_dirPoly]; congr 1; ring

/-- Pointwise domination of the two-sided spectral density by the atomic mean square and the
polar tail. -/
theorem spectralDensity_add_neg_le (N : ℕ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    spectralDensity N ξ + spectralDensity N (-ξ) ≤
      2 * ((‖dirPoly (N + 2) (atomicCoefficient N) (2 * π * ξ)‖ ^ 2 +
        ‖dirPoly (N + 2) (atomicCoefficient N) (-(2 * π * ξ))‖ ^ 2) / (2 * π * ξ) ^ 2) +
        4 * (Real.exp (cutoff N / 2) + 3) ^ 2 / (2 * π * ξ) ^ 4 := by
  have hpos : 0 < (2 * π * ξ) ^ 2 := by positivity
  have hpos4 : 0 < (2 * π * ξ) ^ 4 := by positivity
  set C := Real.exp (cutoff N / 2) + 3 with hC
  -- one side
  have key : ∀ η : ℝ, η ≠ 0 → spectralDensity N η ≤
      (2 * ‖atomicFourier N η‖ ^ 2 + 2 * (C ^ 2 / (2 * π * η) ^ 2)) / (2 * π * η) ^ 2 := by
    intro η hη
    have hposη : 0 < (2 * π * η) ^ 2 := by positivity
    have h1 : ‖fourierPairing N η‖ ^ 2 ≤ 2 * ‖atomicFourier N η‖ ^ 2 + 2 * ‖polarFourier N η‖ ^ 2 := by
      rw [fourierPairing_eq_atomic_sub_polar]
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (atomicFourier N η) (polarFourier N η)) 2
      nlinarith [h, sq_nonneg (‖atomicFourier N η‖ - ‖polarFourier N η‖)]
    have h2 := norm_polarFourier_sq_le N hη
    unfold spectralDensity
    calc ‖fourierPairing N η‖ ^ 2 / (1 / 4 + (2 * π * η) ^ 2)
        ≤ ‖fourierPairing N η‖ ^ 2 / (2 * π * η) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) hposη (by linarith)
      _ ≤ (2 * ‖atomicFourier N η‖ ^ 2 + 2 * (C ^ 2 / (2 * π * η) ^ 2)) / (2 * π * η) ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) hposη.le
  have hk1 := key ξ hξ
  have hk2 := key (-ξ) (neg_ne_zero.2 hξ)
  have hsq : (2 * π * -ξ) ^ 2 = (2 * π * ξ) ^ 2 := by ring
  rw [hsq] at hk2
  rw [atomicFourier_eq_dirPoly] at hk1
  rw [norm_atomicFourier_neg] at hk2
  have hsum := add_le_add hk1 hk2
  refine hsum.trans (le_of_eq ?_)
  rw [show (2 * π * ξ) ^ 4 = (2 * π * ξ) ^ 2 * (2 * π * ξ) ^ 2 by ring]
  field_simp
  ring

/-- **The high-frequency window law.**  For `0 < ξ₀ ≤ ξ₁`,
`∫_{ξ₀}^{ξ₁} (S_N(ξ) + S_N(−ξ)) dξ ≤ 2D₁/(π²ξ₀) + 52D₂/(π³ξ₀²) + 4(e^{L/2}+3)²/(3(2π)⁴ξ₀³)`. -/
theorem integral_spectralDensity_window_le (N : ℕ) {ξ₀ ξ₁ : ℝ} (h0 : 0 < ξ₀) (h01 : ξ₀ ≤ ξ₁) :
    (∫ ξ in ξ₀..ξ₁, spectralDensity N ξ + spectralDensity N (-ξ)) ≤
      2 * atomicDiagonal N / (π ^ 2 * ξ₀) + 52 * atomicSecondMoment N / (π ^ 3 * ξ₀ ^ 2) +
        4 * (Real.exp (cutoff N / 2) + 3) ^ 2 / (3 * (2 * π) ^ 4 * ξ₀ ^ 3) := by
  set D₁ := atomicDiagonal N with hD₁
  set D₂ := atomicSecondMoment N with hD₂
  set C := Real.exp (cutoff N / 2) + 3 with hC
  have hD₁0 : 0 ≤ D₁ := atomicDiagonal_nonneg N
  have hD₂0 : 0 ≤ D₂ := atomicSecondMoment_nonneg N
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hne : ∀ x ∈ uIcc ξ₀ ξ₁, x ≠ 0 := fun x hx => by
    rw [uIcc_of_le h01] at hx; exact (lt_of_lt_of_le h0 hx.1).ne'
  set Hs : ℝ → ℝ := fun u => ‖dirPoly (N + 2) (atomicCoefficient N) u‖ ^ 2 +
    ‖dirPoly (N + 2) (atomicCoefficient N) (-u)‖ ^ 2 with hHs
  have hHsc : Continuous Hs :=
    (continuous_normSq_dirPoly _ _).add ((continuous_normSq_dirPoly _ _).comp continuous_neg)
  -- the dominating function
  set U : ℝ → ℝ := fun ξ => 2 * (Hs (2 * π * ξ) / (2 * π * ξ) ^ 2) + 4 * C ^ 2 / (2 * π * ξ) ^ 4
    with hU
  have hUc : ContinuousOn U (uIcc ξ₀ ξ₁) := by
    refine ContinuousOn.add (ContinuousOn.mul continuousOn_const (ContinuousOn.div
      (hHsc.comp_continuousOn (by fun_prop)) (by fun_prop) fun x hx => ?_))
      (ContinuousOn.div continuousOn_const (by fun_prop) fun x hx => ?_)
    · exact pow_ne_zero 2 (mul_ne_zero h2π (hne x hx))
    · exact pow_ne_zero 4 (mul_ne_zero h2π (hne x hx))
  have hSc : Continuous fun ξ => spectralDensity N ξ + spectralDensity N (-ξ) :=
    (continuous_spectralDensity N).add ((continuous_spectralDensity N).comp continuous_neg)
  have hmono : (∫ ξ in ξ₀..ξ₁, spectralDensity N ξ + spectralDensity N (-ξ)) ≤ ∫ ξ in ξ₀..ξ₁, U ξ := by
    refine intervalIntegral.integral_mono_on h01 (hSc.intervalIntegrable _ _) hUc.intervalIntegrable
      fun ξ hξ => ?_
    exact spectralDensity_add_neg_le N (lt_of_lt_of_le h0 hξ.1).ne'
  -- split `U`
  have hU1c : ContinuousOn (fun ξ : ℝ => 2 * (Hs (2 * π * ξ) / (2 * π * ξ) ^ 2)) (uIcc ξ₀ ξ₁) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div
      (hHsc.comp_continuousOn (by fun_prop)) (by fun_prop) fun x hx => ?_)
    exact pow_ne_zero 2 (mul_ne_zero h2π (hne x hx))
  have hU2c : ContinuousOn (fun ξ : ℝ => 4 * C ^ 2 / (2 * π * ξ) ^ 4) (uIcc ξ₀ ξ₁) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun x hx => ?_
    exact pow_ne_zero 4 (mul_ne_zero h2π (hne x hx))
  have hsplit : (∫ ξ in ξ₀..ξ₁, U ξ) =
      (∫ ξ in ξ₀..ξ₁, 2 * (Hs (2 * π * ξ) / (2 * π * ξ) ^ 2)) +
        ∫ ξ in ξ₀..ξ₁, 4 * C ^ 2 / (2 * π * ξ) ^ 4 :=
    intervalIntegral.integral_add hU1c.intervalIntegrable hU2c.intervalIntegrable
  -- the atomic part by substitution and the integration-by-parts bound
  have hatom : (∫ ξ in ξ₀..ξ₁, 2 * (Hs (2 * π * ξ) / (2 * π * ξ) ^ 2)) ≤
      2 * ((2 * π)⁻¹ * (4 * D₁ / (2 * π * ξ₀) + 208 * D₂ / (2 * π * ξ₀) ^ 2)) := by
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hsub := intervalIntegral.integral_comp_mul_left (fun u => Hs u / u ^ 2) h2π
      (a := ξ₀) (b := ξ₁)
    rw [smul_eq_mul] at hsub
    rw [hsub]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact integral_twoSided_atomic_div_sq_le N (by positivity)
      (mul_le_mul_of_nonneg_left h01 (by positivity))
  -- the polar part by an explicit antiderivative
  have hpolar : (∫ ξ in ξ₀..ξ₁, 4 * C ^ 2 / (2 * π * ξ) ^ 4) ≤
      4 * C ^ 2 / (2 * π) ^ 4 * ((1 / 3) * (ξ₀ ^ 3)⁻¹) := by
    have hA : ∀ x ∈ uIcc ξ₀ ξ₁, HasDerivAt
        (fun x : ℝ => 4 * C ^ 2 / (2 * π) ^ 4 * (-(1 / 3) * (x ^ 3)⁻¹)) (4 * C ^ 2 / (2 * π * x) ^ 4) x := by
      intro x hx
      have hx0 : x ≠ 0 := hne x hx
      have h1 := (((hasDerivAt_pow 3 x).inv (pow_ne_zero 3 hx0)).const_mul (-(1 / 3 : ℝ))).const_mul
        (4 * C ^ 2 / (2 * π) ^ 4)
      refine h1.congr_deriv ?_
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hA hU2c.intervalIntegrable]
    have hξ1 : 0 < ξ₁ := lt_of_lt_of_le h0 h01
    have : 0 ≤ 4 * C ^ 2 / (2 * π) ^ 4 * ((1 / 3) * (ξ₁ ^ 3)⁻¹) := by positivity
    nlinarith
  -- assemble
  have hfin : 2 * ((2 * π)⁻¹ * (4 * D₁ / (2 * π * ξ₀) + 208 * D₂ / (2 * π * ξ₀) ^ 2)) +
      4 * C ^ 2 / (2 * π) ^ 4 * ((1 / 3) * (ξ₀ ^ 3)⁻¹) =
      2 * D₁ / (π ^ 2 * ξ₀) + 52 * D₂ / (π ^ 3 * ξ₀ ^ 2) + 4 * C ^ 2 / (3 * (2 * π) ^ 4 * ξ₀ ^ 3) := by
    field_simp
    ring
  rw [← hfin]
  linarith [hmono, hsplit, hatom, hpolar]

/-! ## The two-sided tail -/

theorem integrableOn_spectralDensity_add_neg_Ioi (N : ℕ) {ξ₀ : ℝ} (h0 : 0 < ξ₀) :
    IntegrableOn (fun ξ => spectralDensity N ξ + spectralDensity N (-ξ)) (Ioi ξ₀) := by
  have hSc : Continuous fun ξ => spectralDensity N ξ + spectralDensity N (-ξ) :=
    (continuous_spectralDensity N).add ((continuous_spectralDensity N).comp continuous_neg)
  have hmaj : IntegrableOn (fun ξ : ℝ => 2 * mass N ^ 2 / (2 * π) ^ 2 * ξ ^ (-2 : ℝ)) (Ioi ξ₀) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) h0).const_mul _
  refine hmaj.mono' hSc.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun ξ hξ => ?_
  have hξ0 : 0 < ξ := lt_trans h0 hξ
  have h1 := spectralDensity_le_mass_sq_div N hξ0.ne'
  have h2 := spectralDensity_le_mass_sq_div N (neg_ne_zero.2 hξ0.ne')
  rw [show (2 * π * -ξ) ^ 2 = (2 * π * ξ) ^ 2 by ring] at h2
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (spectralDensity_nonneg N ξ)
    (spectralDensity_nonneg N (-ξ))), Real.rpow_neg hξ0.le, Real.rpow_two]
  have he : 2 * mass N ^ 2 / (2 * π) ^ 2 * (ξ ^ 2)⁻¹ = 2 * (mass N ^ 2 / (2 * π * ξ) ^ 2) := by
    field_simp
  rw [he]
  linarith

/-- **The two-sided high-frequency tail of the Laplace energy** is bounded by the window law. -/
theorem integral_spectralDensity_tail_le (N : ℕ) {ξ₀ : ℝ} (h0 : 0 < ξ₀) :
    (∫ ξ in Ioi ξ₀, spectralDensity N ξ + spectralDensity N (-ξ)) ≤
      2 * atomicDiagonal N / (π ^ 2 * ξ₀) + 52 * atomicSecondMoment N / (π ^ 3 * ξ₀ ^ 2) +
        4 * (Real.exp (cutoff N / 2) + 3) ^ 2 / (3 * (2 * π) ^ 4 * ξ₀ ^ 3) := by
  have ht := intervalIntegral_tendsto_integral_Ioi ξ₀
    (integrableOn_spectralDensity_add_neg_Ioi N h0) (tendsto_id (x := atTop))
  refine le_of_tendsto ht ((eventually_ge_atTop ξ₀).mono fun ξ₁ hξ₁ => ?_)
  exact integral_spectralDensity_window_le N h0 hξ₁

/-! ## The band-plus-tail decomposition of the Laplace energy -/

theorem integrable_spectralDensity (N : ℕ) : Integrable (spectralDensity N) := by
  have hmaj : Integrable fun ξ : ℝ => 4 * mass N ^ 2 * (1 + (4 * π * ξ) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_mul_left' (show (4 * π : ℝ) ≠ 0 by positivity)).const_mul
      (4 * mass N ^ 2)
  refine hmaj.mono' (continuous_spectralDensity N).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (spectralDensity_nonneg N ξ)]
  unfold spectralDensity
  have hpos : 0 < 1 / 4 + (2 * π * ξ) ^ 2 := by positivity
  have he : 4 * mass N ^ 2 * (1 + (4 * π * ξ) ^ 2)⁻¹ = mass N ^ 2 / (1 / 4 + (2 * π * ξ) ^ 2) := by
    field_simp
    ring
  rw [he]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (norm_fourierPairing_le N ξ) 2) hpos.le

/-- `laplaceEnergy N = ∫_{−ξ₀}^{ξ₀} S_N + ∫_{ξ₀}^∞ (S_N(ξ) + S_N(−ξ))`. -/
theorem laplaceEnergy_eq_band_add_tail (N : ℕ) {ξ₀ : ℝ} (h0 : 0 < ξ₀) :
    laplaceEnergy N = (∫ ξ in Icc (-ξ₀) ξ₀, spectralDensity N ξ) +
      ∫ ξ in Ioi ξ₀, spectralDensity N ξ + spectralDensity N (-ξ) := by
  have hint := integrable_spectralDensity N
  have h1 := integral_add_compl (μ := volume) measurableSet_Ioi hint (s := Ioi ξ₀)
  rw [compl_Ioi] at h1
  have hunion : Iic (-ξ₀) ∪ Ioc (-ξ₀) ξ₀ = Iic ξ₀ := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ioc]
    constructor
    · rintro (h | h)
      · linarith
      · exact h.2
    · intro h
      by_cases hx : x ≤ -ξ₀
      · exact Or.inl hx
      · exact Or.inr ⟨not_le.1 hx, h⟩
  have hdisj : Disjoint (Iic (-ξ₀)) (Ioc (-ξ₀) ξ₀) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx'.1 (not_lt.2 hx)
  have h2 : (∫ ξ in Iic ξ₀, spectralDensity N ξ) =
      (∫ ξ in Iic (-ξ₀), spectralDensity N ξ) + ∫ ξ in Ioc (-ξ₀) ξ₀, spectralDensity N ξ := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioc hint.integrableOn hint.integrableOn]
  have h3 : (∫ ξ in Iic (-ξ₀), spectralDensity N ξ) = ∫ ξ in Ioi ξ₀, spectralDensity N (-ξ) :=
    (integral_comp_neg_Ioi ξ₀ (fun ξ => spectralDensity N ξ)).symm
  have h4 : (∫ ξ in Ioi ξ₀, spectralDensity N ξ + spectralDensity N (-ξ)) =
      (∫ ξ in Ioi ξ₀, spectralDensity N ξ) + ∫ ξ in Ioi ξ₀, spectralDensity N (-ξ) :=
    integral_add hint.integrableOn ((hint.comp_neg).integrableOn)
  rw [laplaceEnergy_eq_integral_spectralDensity, ← h1, h2, h3, h4, integral_Icc_eq_integral_Ioc]
  ring

/-- **The Laplace energy is its band energy plus an explicit high-frequency remainder.** -/
theorem laplaceEnergy_le_band_add_remainder (N : ℕ) {ξ₀ : ℝ} (h0 : 0 < ξ₀) :
    laplaceEnergy N ≤ (∫ ξ in Icc (-ξ₀) ξ₀, spectralDensity N ξ) +
      (2 * atomicDiagonal N / (π ^ 2 * ξ₀) + 52 * atomicSecondMoment N / (π ^ 3 * ξ₀ ^ 2) +
        4 * (Real.exp (cutoff N / 2) + 3) ^ 2 / (3 * (2 * π) ^ 4 * ξ₀ ^ 3)) := by
  rw [laplaceEnergy_eq_band_add_tail N h0]
  exact add_le_add le_rfl (integral_spectralDensity_tail_le N h0)

/-! ## The diagonal sums in Chebyshev terms -/

theorem norm_atomicCoefficient_sq (N : ℕ) (m : Fin (N + 2)) :
    ‖atomicCoefficient N m‖ ^ 2 =
      ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) ^ 2 / (((m : ℕ) : ℝ) + 1) := by
  unfold atomicCoefficient primeWeight
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by positivity)]
  push_cast
  ring

/-- `D₂ = Σ_{n ≤ N+2} Λ(n)²`. -/
theorem atomicSecondMoment_eq (N : ℕ) :
    atomicSecondMoment N = ∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n ^ 2 := by
  unfold atomicSecondMoment
  have h1 : ∀ m : Fin (N + 2), (((m : ℕ) : ℝ) + 1) * ‖atomicCoefficient N m‖ ^ 2 =
      ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) ^ 2 := by
    intro m
    have hm : ((m : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    rw [norm_atomicCoefficient_sq]
    field_simp
  rw [Finset.sum_congr rfl fun m _ => h1 m]
  have h2 := Fin.sum_univ_eq_sum_range
    (fun k : ℕ => ArithmeticFunction.vonMangoldt (k + 1) ^ 2) (N + 2)
  rw [h2]
  have hIco : Finset.Icc 1 (N + 2) = Finset.Ico 1 (N + 3) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIco, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun k _ => ?_
  rw [show 1 + k = k + 1 by ring]

/-- **`D₂ ≤ L · ψ(N+2)`:** the weighted diagonal is at most `log(N+2)` times the Chebyshev
function, since `Λ(n) ≤ log n ≤ L` on the window. -/
theorem atomicSecondMoment_le (N : ℕ) :
    atomicSecondMoment N ≤ cutoff N * Chebyshev.psi ((N + 2 : ℕ) : ℝ) := by
  have hexp : Real.exp (cutoff N) = ((N + 2 : ℕ) : ℝ) := by
    unfold cutoff; exact Real.exp_log (by positivity)
  have hpsi : Chebyshev.psi ((N + 2 : ℕ) : ℝ) =
      ∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n := by
    rw [← hexp, ← step_eq N le_rfl]
    unfold step
    exact Finset.sum_congr rfl fun n hn => by rw [if_pos (node_bounds N n hn).2]
  rw [hpsi, Finset.mul_sum, atomicSecondMoment_eq]
  refine Finset.sum_le_sum fun n hn => ?_
  have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ cutoff N :=
    ArithmeticFunction.vonMangoldt_le_log.trans (node_bounds N n hn).2
  rw [sq]
  exact mul_le_mul_of_nonneg_right hΛ hΛ0

/-- `D₁ = Σ_{n ≤ N+2} Λ(n)²/n`. -/
theorem atomicDiagonal_eq (N : ℕ) :
    atomicDiagonal N = ∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n ^ 2 / n := by
  unfold atomicDiagonal
  rw [Finset.sum_congr rfl fun m _ => norm_atomicCoefficient_sq N m]
  have h2 := Fin.sum_univ_eq_sum_range
    (fun k : ℕ => ArithmeticFunction.vonMangoldt (k + 1) ^ 2 / ((k : ℝ) + 1)) (N + 2)
  rw [h2]
  have hIco : Finset.Icc 1 (N + 2) = Finset.Ico 1 (N + 3) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIco, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun k _ => ?_
  rw [show 1 + k = k + 1 by ring]
  push_cast
  ring

/-- `D₁ ≤ L · Σ_{n ≤ N+2} Λ(n)/n`. -/
theorem atomicDiagonal_le (N : ℕ) :
    atomicDiagonal N ≤ cutoff N * ∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n / n := by
  rw [atomicDiagonal_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ cutoff N :=
    ArithmeticFunction.vonMangoldt_le_log.trans (node_bounds N n hn).2
  rw [sq, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hΛ (div_nonneg hΛ0 hn0.le)

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
