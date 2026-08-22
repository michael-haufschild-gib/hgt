import GaloisForLFunctions.RHTower.GammaEulerPhysicalConnector
import GaloisForLFunctions.RHTower.PrimeSeamDampingAperture
import GaloisForLFunctions.HTGeometry.PSDKernelOperations
import GaloisForLFunctions.RHTower.HeatAperturePrimeSeamReflection
import GaloisForLFunctions.RHTower.PrimeLaplaceGammaJetIncidence

/-!
# The Gamma--Meixner convolution-root scale of the prime seam

The archimedean cyclic Gamma measure is the time-one member of an exact convolution semigroup with
characteristic function `φ_θ(t) = (cosh t)^{-θ/2}`, realised by the normalised Gamma height density.
Its pointed diagonal at a prime logarithm is comparable with `p^{-θ}` on both sides, so membership
of the reflected Xi seam in the time-`θ` Hilbert domain is decided by the same threshold as the
plain prime damping: the critical line, or a convolution time above the horizontal reflection
charge.  Taking `θ = 1/m` gives a countable criterion for the Riemann hypothesis.
-/

namespace RHTower

open MeasureTheory Complex
open scoped ComplexOrder ComplexConjugate

noncomputable section

/-! ### The Gamma--Meixner convolution semigroup -/

/-- The Gamma--Meixner characteristic function at convolution time `θ`. -/
def meixnerChar (theta t : ℝ) : ℝ := Real.cosh t ^ (-(theta / 2))

theorem meixnerChar_pos (theta t : ℝ) : 0 < meixnerChar theta t :=
  Real.rpow_pos_of_pos (Real.cosh_pos t) _

theorem meixnerChar_zero (theta : ℝ) : meixnerChar theta 0 = 1 := by
  simp [meixnerChar]

/-- **Equation (5).**  The characteristic functions form a one-parameter semigroup. -/
theorem meixnerChar_add (theta eta t : ℝ) :
    meixnerChar (theta + eta) t = meixnerChar theta t * meixnerChar eta t := by
  rw [meixnerChar, meixnerChar, meixnerChar, ← Real.rpow_add (Real.cosh_pos t)]
  ring_nf

/-- **Equation (6).**  The time-one characteristic is the `m`-th power of the time-`1/m`
characteristic. -/
theorem meixnerChar_pow (m : ℕ) (hm : 0 < m) (t : ℝ) :
    meixnerChar 1 t = meixnerChar (1 / m) t ^ m := by
  rw [meixnerChar, meixnerChar, ← Real.rpow_natCast (Real.cosh t ^ (-(1 / (m : ℝ) / 2))) m,
    ← Real.rpow_mul (Real.cosh_pos t).le]
  congr 1
  field_simp

/-- **Equation (1).**  The Gamma--Meixner density at convolution time `θ`. -/
def meixnerDensity (theta s : ℝ) : ℝ := gammaHeightDensity (theta / 2) (s / 2) / 2

theorem meixnerDensity_eq (theta s : ℝ) :
    meixnerDensity theta s =
      (4 : ℝ) ^ (theta / 4) / (4 * Real.pi * Real.Gamma (theta / 2)) *
        Complex.normSq (Complex.Gamma (((theta / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * Complex.I)) := by
  rw [meixnerDensity, gammaHeightDensity]
  have harg : (((theta / 2 : ℝ) : ℂ) + ((2 * (s / 2) : ℝ) : ℂ) * Complex.I) / 2
      = ((theta / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  have hfour : (4 : ℝ) ^ (theta / 4) = (2 : ℝ) ^ (theta / 2) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num [Real.rpow_two], ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [hfour, Real.rpow_sub (by norm_num)]
  field_simp
  ring

theorem meixnerDensity_nonneg {theta : ℝ} (htheta : 0 < theta) (s : ℝ) :
    0 ≤ meixnerDensity theta s := by
  refine div_nonneg (gammaHeightDensity_nonneg (by linarith) _) (by norm_num)

theorem integrable_meixnerDensity {theta : ℝ} (htheta : 0 < theta) :
    Integrable (meixnerDensity theta) := by
  have h : Integrable (fun s : ℝ => gammaHeightDensity (theta / 2) (2⁻¹ * s)) :=
    (integrable_gammaHeightDensity (r := theta / 2) (by linarith)).comp_mul_left'
      (by norm_num : (2⁻¹ : ℝ) ≠ 0)
  have heq : meixnerDensity theta = fun s => (gammaHeightDensity (theta / 2) (2⁻¹ * s)) / 2 := by
    funext s
    rw [meixnerDensity]
    ring_nf
  rw [heq]
  exact h.div_const 2

/-- **Equation (3).**  The Gamma--Meixner density at time `θ` has characteristic function
`φ_θ(t) = (cosh t)^{-θ/2}`. -/
theorem integral_cexp_mul_meixnerDensity {theta : ℝ} (htheta : 0 < theta) (t : ℝ) :
    (∫ s : ℝ, Complex.exp (((t * s : ℝ) : ℂ) * Complex.I) * (meixnerDensity theta s : ℂ))
      = ((meixnerChar theta t : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun s => Complex.exp (((t * s : ℝ) : ℂ) * Complex.I) *
    (meixnerDensity theta s : ℂ) with hF
  have hscale := MeasureTheory.Measure.integral_comp_mul_left F 2
  have hhalf : |(2 : ℝ)⁻¹| = 2⁻¹ := by norm_num
  rw [hhalf, real_smul] at hscale
  have hpoint : ∀ u : ℝ, F (2 * u)
      = Complex.exp (((u * (2 * t) : ℝ) : ℂ) * Complex.I) *
          ((gammaHeightDensity (theta / 2) u : ℝ) : ℂ) / 2 := by
    intro u
    rw [hF]
    simp only [meixnerDensity]
    have harg : (2 * u / 2 : ℝ) = u := by ring
    rw [harg]
    have hexp : ((t * (2 * u) : ℝ) : ℂ) = ((u * (2 * t) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  rw [show (fun u : ℝ => F (2 * u)) = fun u : ℝ =>
      Complex.exp (((u * (2 * t) : ℝ) : ℂ) * Complex.I) *
        ((gammaHeightDensity (theta / 2) u : ℝ) : ℂ) / 2 from funext hpoint] at hscale
  rw [MeasureTheory.integral_div, integral_cexp_mul_gammaHeightDensity (by linarith) (2 * t)]
    at hscale
  have harg2 : (2 * t / 2 : ℝ) = t := by ring
  rw [harg2] at hscale
  have h2 : ((2 : ℝ) : ℂ) ≠ 0 := by norm_num
  field_simp at hscale
  rw [meixnerChar]
  push_cast at hscale
  norm_num at hscale
  exact hscale.symm

/-- The Gamma--Meixner density is a probability density. -/
theorem integral_meixnerDensity_eq_one {theta : ℝ} (htheta : 0 < theta) :
    (∫ s : ℝ, meixnerDensity theta s) = 1 := by
  have h := congrArg Complex.re (integral_cexp_mul_meixnerDensity htheta 0)
  simpa [integral_complex_ofReal, meixnerChar_zero] using h

theorem integrable_cexp_mul_meixnerDensity {theta : ℝ} (htheta : 0 < theta) (a : ℝ) :
    Integrable (fun s : ℝ => Complex.exp (((a * s : ℝ) : ℂ) * Complex.I) *
      (meixnerDensity theta s : ℂ)) := by
  have hρ : Integrable (fun s : ℝ => ((meixnerDensity theta s : ℝ) : ℂ)) :=
    (integrable_meixnerDensity htheta).ofReal
  refine Integrable.mono' hρ.norm ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ hρ.aestronglyMeasurable
    exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with s
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-! ### The pointed covariance kernel -/

open GaloisForLFunctions.HTGeometry in
/-- The stationary characteristic kernel `φ_θ(t - u)` is positive semidefinite: it is the Fourier
transform of the positive Gamma--Meixner density. -/
theorem isPSDKernel_meixnerChar_sub {theta : ℝ} (htheta : 0 < theta) :
    IsPSDKernel (fun t u : ℝ => ((meixnerChar theta (t - u) : ℝ) : ℂ)) := by
  refine isPSDKernel_of_forall_posSemidef ?_ ?_
  · intro t u
    rw [Complex.conj_ofReal]
    congr 1
    rw [meixnerChar, meixnerChar, show u - t = -(t - u) by ring, Real.cosh_neg]
  · intro n w
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext j k
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def, Complex.conj_ofReal]
      congr 1
      rw [meixnerChar, meixnerChar, show w j - w k = -(w k - w j) by ring, Real.cosh_neg]
    · intro x
      have hrep : ∀ a : ℝ, ((meixnerChar theta a : ℝ) : ℂ)
          = ∫ s : ℝ, Complex.exp (((a * s : ℝ) : ℂ) * Complex.I) *
              (meixnerDensity theta s : ℂ) :=
        fun a => (integral_cexp_mul_meixnerDensity htheta a).symm
      have hint : ∀ j k : Fin n, Integrable (fun s : ℝ =>
          (starRingEnd ℂ) (x j) * x k *
            (Complex.exp ((((w j - w k) * s : ℝ) : ℂ) * Complex.I) *
              (meixnerDensity theta s : ℂ))) :=
        fun j k => (integrable_cexp_mul_meixnerDensity htheta (w j - w k)).const_mul _
      set v : ℝ → ℂ := fun s => ∑ k, x k * Complex.exp (-(((w k * s : ℝ) : ℂ) * Complex.I))
        with hv
      have hpoint : ∀ s : ℝ, (∑ j, ∑ k, (starRingEnd ℂ) (x j) * x k *
          (Complex.exp ((((w j - w k) * s : ℝ) : ℂ) * Complex.I) *
            (meixnerDensity theta s : ℂ)))
          = ((Complex.normSq (v s) * meixnerDensity theta s : ℝ) : ℂ) := by
        intro s
        have hfac : ∑ j, ∑ k, (starRingEnd ℂ) (x j) * x k *
            Complex.exp ((((w j - w k) * s : ℝ) : ℂ) * Complex.I)
            = (starRingEnd ℂ) (v s) * v s := by
          rw [hv]
          simp only [map_sum]
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul, ← Complex.exp_conj]
          rw [show (starRingEnd ℂ) (-(((w j * s : ℝ) : ℂ) * Complex.I))
              = ((w j * s : ℝ) : ℂ) * Complex.I by
            simp [Complex.conj_ofReal]]
          rw [mul_mul_mul_comm, ← Complex.exp_add]
          congr 2
          push_cast
          ring
        calc (∑ j, ∑ k, (starRingEnd ℂ) (x j) * x k *
              (Complex.exp ((((w j - w k) * s : ℝ) : ℂ) * Complex.I) *
                (meixnerDensity theta s : ℂ)))
            = (∑ j, ∑ k, (starRingEnd ℂ) (x j) * x k *
                Complex.exp ((((w j - w k) * s : ℝ) : ℂ) * Complex.I)) *
                (meixnerDensity theta s : ℂ) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun k _ => ?_
              ring
          _ = ((Complex.normSq (v s) * meixnerDensity theta s : ℝ) : ℂ) := by
              rw [hfac]
              push_cast
              rw [← Complex.normSq_eq_conj_mul_self]
      have hstep : star x ⬝ᵥ (Matrix.of fun j k =>
          ((meixnerChar theta (w j - w k) : ℝ) : ℂ)).mulVec x
          = ((∫ s : ℝ, Complex.normSq (v s) * meixnerDensity theta s : ℝ) : ℂ) := by
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
          Finset.mul_sum]
        have hinner : ∀ j : Fin n, (∑ k, (starRingEnd ℂ) (x j) *
            (((meixnerChar theta (w j - w k) : ℝ) : ℂ) * x k))
            = ∫ s : ℝ, ∑ k, (starRingEnd ℂ) (x j) * x k *
              (Complex.exp ((((w j - w k) * s : ℝ) : ℂ) * Complex.I) *
                (meixnerDensity theta s : ℂ)) := by
          intro j
          rw [MeasureTheory.integral_finsetSum _ (fun k _ => hint j k)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [MeasureTheory.integral_const_mul, ← hrep]
          ring
        rw [show (∑ j, ∑ k, (starRingEnd ℂ) (x j) *
            (((meixnerChar theta (w j - w k) : ℝ) : ℂ) * x k))
            = ∑ j, ∫ s : ℝ, ∑ k, (starRingEnd ℂ) (x j) * x k *
              (Complex.exp ((((w j - w k) * s : ℝ) : ℂ) * Complex.I) *
                (meixnerDensity theta s : ℂ)) from Finset.sum_congr rfl fun j _ => hinner j]
        rw [← MeasureTheory.integral_finsetSum _ (fun j _ =>
          MeasureTheory.integrable_finsetSum _ (fun k _ => hint j k))]
        rw [← integral_complex_ofReal]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        exact hpoint s
      rw [hstep]
      refine Complex.zero_le_real.mpr (MeasureTheory.integral_nonneg fun s => ?_)
      exact mul_nonneg (Complex.normSq_nonneg _) (meixnerDensity_nonneg htheta s)

/-- **Equation (7).**  The pointed covariance kernel of the Gamma--Meixner time-`θ` state. -/
def meixnerPointedKernel (theta t u : ℝ) : ℝ :=
  Real.sqrt (meixnerChar theta (2 * t)) * Real.sqrt (meixnerChar theta (2 * u)) *
    meixnerChar theta (t - u)

open GaloisForLFunctions.HTGeometry in
/-- **Equation (8).**  The pointed kernel is positive semidefinite: it is the Schur product of the
rank-one kernel of the square-root weights with the stationary characteristic kernel, that is, the
Gram kernel of the scaled characters. -/
theorem isPSDKernel_meixnerPointedKernel {theta : ℝ} (htheta : 0 < theta) :
    IsPSDKernel (fun t u : ℝ => ((meixnerPointedKernel theta t u : ℝ) : ℂ)) := by
  have h1 : IsPSDKernel (fun t u : ℝ =>
      (fun r : ℝ => ((Real.sqrt (meixnerChar theta (2 * r)) : ℝ) : ℂ)) t *
        (starRingEnd ℂ) ((fun r : ℝ => ((Real.sqrt (meixnerChar theta (2 * r)) : ℝ) : ℂ)) u)) :=
    isPSDKernel_rankOne _
  have h3 := h1.mul (isPSDKernel_meixnerChar_sub htheta)
  have heq : (fun t u : ℝ => ((meixnerPointedKernel theta t u : ℝ) : ℂ))
      = fun t u : ℝ =>
          ((fun r : ℝ => ((Real.sqrt (meixnerChar theta (2 * r)) : ℝ) : ℂ)) t *
            (starRingEnd ℂ) ((fun r : ℝ => ((Real.sqrt (meixnerChar theta (2 * r)) : ℝ) : ℂ)) u)) *
            ((meixnerChar theta (t - u) : ℝ) : ℂ) := by
    funext t u
    rw [meixnerPointedKernel]
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  rw [heq]
  exact h3

/-! ### The exact prime weight -/

/-- The corpus prime weight is the pointed diagonal of the time-`θ` characteristic. -/
theorem meixnerPrimeWeight_eq_meixnerChar (theta : ℝ) (n : ℕ) :
    meixnerPrimeWeight theta n = meixnerChar theta (2 * Real.log n) := by
  rw [meixnerPrimeWeight, meixnerChar, neg_div]

theorem cosh_two_log_factored {p : ℝ} (hp : 0 < p) :
    Real.cosh (2 * Real.log p) = p ^ 2 * (1 + p ^ (-4 : ℝ)) / 2 := by
  rw [Real.cosh_eq]
  have h1 : Real.exp (2 * Real.log p) = p ^ 2 := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hp, Real.rpow_two]
  have h2 : Real.exp (-(2 * Real.log p)) = (p ^ 2)⁻¹ := by
    rw [Real.exp_neg, h1]
  have hp4 : p ^ (-4 : ℝ) = (p ^ (4 : ℕ))⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hp.le, Real.rpow_natCast]
  rw [h1, h2, hp4]
  have hpne : p ≠ 0 := ne_of_gt hp
  field_simp

/-- **Equation (9).**  The exact value of the pointed prime diagonal. -/
theorem meixnerPrimeWeight_eq {theta : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    meixnerPrimeWeight theta n =
      (2 : ℝ) ^ (theta / 2) * (n : ℝ) ^ (-theta) *
        (1 + (n : ℝ) ^ (-4 : ℝ)) ^ (-(theta / 2)) := by
  have hp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 1 + (n : ℝ) ^ (-4 : ℝ) := by positivity
  have hp2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [meixnerPrimeWeight_eq_meixnerChar, meixnerChar, cosh_two_log_factored hp]
  rw [show (n : ℝ) ^ 2 * (1 + (n : ℝ) ^ (-4 : ℝ)) / 2
      = (n : ℝ) ^ 2 * (1 + (n : ℝ) ^ (-4 : ℝ)) * 2⁻¹ by ring]
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hp2.le hpos.le,
    ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul hp.le, ← Real.rpow_neg_one (2 : ℝ),
    ← Real.rpow_mul (by norm_num)]
  ring_nf

/-- **Equation (19).**  The complementary half-density is two-sidedly comparable with
`n^{-θ/2}`; its inverse is therefore unbounded on the prime basis. -/
theorem sqrt_meixnerPrimeWeight_bounds {theta : ℝ} (htheta : 0 ≤ theta) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (-theta / 2) ≤ Real.sqrt (meixnerPrimeWeight theta n) ∧
      Real.sqrt (meixnerPrimeWeight theta n) ≤ (2 : ℝ) ^ (theta / 4) * (n : ℝ) ^ (-theta / 2) := by
  rw [sqrt_meixnerPrimeWeight]
  constructor
  · have h := meixnerPrimeWeight_ge (theta / 2) (by linarith) hn
    rw [show -(theta / 2) = -theta / 2 by ring] at h
    exact h
  · have h := meixnerPrimeWeight_le (theta / 2) (by linarith) hn
    rw [show -(theta / 2) = -theta / 2 by ring, show theta / 2 / 2 = theta / 4 by ring] at h
    exact h

/-! ### The exact seam-domain threshold -/

/-- **Equation (11).**  The Gamma--Meixner root-domain energy of a fibre at convolution time `θ`. -/
def meixnerSeamEnergy (theta : ℝ) (rho : ℂ) (p : Nat.Primes) : ℝ :=
  meixnerPrimeWeight theta (p : ℕ) * ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2

theorem meixnerSeamEnergy_nonneg (theta : ℝ) (rho : ℂ) (p : Nat.Primes) :
    0 ≤ meixnerSeamEnergy theta rho p :=
  mul_nonneg (meixnerPrimeWeight_pos theta _).le (sq_nonneg _)

/-- **Equation (12).**  The exact root-domain threshold: a fibre lies in the time-`θ` Gamma--Meixner
domain exactly on the critical line or above the horizontal reflection charge. -/
theorem summable_meixnerSeamEnergy_iff {theta : ℝ} (htheta : 0 < theta) (rho : ℂ) :
    Summable (meixnerSeamEnergy theta rho) ↔ rho.re = 1 / 2 ∨ |2 * rho.re - 1| < theta := by
  have hp1 : ∀ p : Nat.Primes, 1 ≤ (p : ℕ) := fun p => p.prop.one_lt.le
  rw [← summable_weightedNatPrimeSeamCharge_norm_sq_iff theta rho]
  constructor
  · intro h
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) h
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
    · rw [weightedNatPrimeSeamChargeNormSq, meixnerSeamEnergy]
      exact mul_le_mul_of_nonneg_right
        (meixnerPrimeWeight_ge theta htheta.le (hp1 p)) (sq_nonneg _)
  · intro h
    refine Summable.of_nonneg_of_le (fun p => meixnerSeamEnergy_nonneg theta rho p)
      (fun p => ?_) (h.mul_left ((2 : ℝ) ^ (theta / 2)))
    rw [meixnerSeamEnergy, weightedNatPrimeSeamChargeNormSq]
    calc meixnerPrimeWeight theta (p : ℕ) * ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2
        ≤ ((2 : ℝ) ^ (theta / 2) * ((p : ℕ) : ℝ) ^ (-theta)) *
            ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (meixnerPrimeWeight_le theta htheta.le (hp1 p)) (sq_nonneg _)
      _ = (2 : ℝ) ^ (theta / 2) *
            (((p : ℕ) : ℝ) ^ (-theta) * ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2) := by ring

/-! ### The Hilbert--Schmidt reading -/

/-- **Equations (13) and (14).**  The squared `L²(μ_θ)` norm of the `p`-th channel of the
seam synthesis is exactly the `p`-th term of the root-domain energy. -/
theorem integral_normSq_meixnerSynthesis {theta : ℝ} (htheta : 0 < theta) (rho : ℂ)
    (p : Nat.Primes) :
    (∫ s : ℝ, ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho *
        ((Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℝ) : ℂ) *
        Complex.exp (((Real.log (p : ℝ) * s : ℝ) : ℂ) * Complex.I)‖ ^ 2 *
        meixnerDensity theta s)
      = meixnerSeamEnergy theta rho p := by
  have hconst : ∀ s : ℝ, ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho *
      ((Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℝ) : ℂ) *
      Complex.exp (((Real.log (p : ℝ) * s : ℝ) : ℂ) * Complex.I)‖ ^ 2
      = meixnerSeamEnergy theta rho p := by
    intro s
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (meixnerPrimeWeight_pos theta (p : ℕ)).le, meixnerSeamEnergy]
    ring
  simp_rw [hconst]
  rw [MeasureTheory.integral_const_mul, integral_meixnerDensity_eq_one htheta, mul_one]

/-- **Equation (15).**  The seam synthesis at convolution time `θ` is Hilbert--Schmidt exactly on
the critical line or above the horizontal reflection charge. -/
theorem summable_integral_normSq_meixnerSynthesis_iff {theta : ℝ} (htheta : 0 < theta) (rho : ℂ) :
    Summable (fun p : Nat.Primes => ∫ s : ℝ,
        ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho *
          ((Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℝ) : ℂ) *
          Complex.exp (((Real.log (p : ℝ) * s : ℝ) : ℂ) * Complex.I)‖ ^ 2 *
          meixnerDensity theta s)
      ↔ rho.re = 1 / 2 ∨ |2 * rho.re - 1| < theta := by
  rw [show (fun p : Nat.Primes => ∫ s : ℝ,
      ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho *
        ((Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℝ) : ℂ) *
        Complex.exp (((Real.log (p : ℝ) * s : ℝ) : ℂ) * Complex.I)‖ ^ 2 *
        meixnerDensity theta s) = meixnerSeamEnergy theta rho from
    funext fun p => integral_normSq_meixnerSynthesis htheta rho p]
  exact summable_meixnerSeamEnergy_iff htheta rho

/-! ### The countable RH criterion -/

theorem re_eq_half_of_forall_meixnerRootDomain {rho : ℂ}
    (h : ∀ m : ℕ, 0 < m → Summable (meixnerSeamEnergy (1 / m) rho)) : rho.re = 1 / 2 := by
  by_contra hne
  have hpos : 0 < |2 * rho.re - 1| := by
    refine abs_pos.mpr fun hzero => hne ?_
    linarith
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  have hm : 0 < n + 1 := Nat.succ_pos n
  have hthetapos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hsum := h (n + 1) hm
  have hcast : ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) = 1 / ((n : ℝ) + 1) := by push_cast; ring
  rw [hcast] at hsum
  rcases (summable_meixnerSeamEnergy_iff hthetapos rho).1 hsum with hline | hlt
  · exact hne hline
  · linarith

/-- **Equation (16).**  RH is exactly membership of every Xi seam fibre in every Gamma--Meixner
convolution-root domain along the countable sequence `θ = 1/m`. -/
theorem riemannHypothesis_iff_meixnerRootDomain :
    RiemannHypothesis ↔
      ∀ m : ℕ, 0 < m → ∀ rho : ℂ, xi rho = 0 →
        Summable (meixnerSeamEnergy (1 / (m : ℝ)) rho) := by
  constructor
  · intro hRH m hm rho hzero
    have hline : rho.re = 1 / 2 :=
      (summable_primeClockReflectionEnergy_iff rho.re).mp
        ((riemannHypothesis_iff_xiZero_primeClockShale.mp hRH) rho hzero)
    have hthetapos : (0 : ℝ) < 1 / (m : ℝ) := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      positivity
    exact (summable_meixnerSeamEnergy_iff hthetapos rho).2 (Or.inl hline)
  · intro hall
    refine riemannHypothesis_iff_xiZero_primeClockShale.mpr fun rho hzero => ?_
    have hline : rho.re = 1 / 2 :=
      re_eq_half_of_forall_meixnerRootDomain fun m hm => hall m hm rho hzero
    exact (summable_primeClockReflectionEnergy_iff rho.re).mpr hline

/-- The same criterion along an arbitrary positive null sequence of convolution times. -/
theorem riemannHypothesis_of_meixnerRootDomain_seq {th : ℕ → ℝ} (hpos : ∀ n, 0 < th n)
    (hlim : Filter.Tendsto th Filter.atTop (nhds 0))
    (h : ∀ n : ℕ, ∀ rho : ℂ, xi rho = 0 → Summable (meixnerSeamEnergy (th n) rho)) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZero_primeClockShale.mpr fun rho hzero => ?_
  have hline : rho.re = 1 / 2 := by
    by_contra hne
    have hcpos : 0 < |2 * rho.re - 1| := by
      refine abs_pos.mpr fun hzero' => hne ?_
      linarith
    obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hcpos)).exists
    rcases (summable_meixnerSeamEnergy_iff (hpos n) rho).1 (h n rho hzero) with hline' | hlt
    · exact hne hline'
    · linarith
  exact (summable_primeClockReflectionEnergy_iff rho.re).mpr hline

/-- **Equation (17), first arrow.**  Membership of a Xi fibre in every Gamma--Meixner root domain
forces every prime seam charge of that fibre to vanish. -/
theorem orbitwiseNatPrimeSeamCharge_eq_zero_of_meixnerRootDomain {rho : ℂ}
    (h : ∀ m : ℕ, 0 < m → Summable (meixnerSeamEnergy (1 / (m : ℝ)) rho)) (p : ℕ) (hp : p.Prime) :
    orbitwiseNatPrimeSeamCharge p rho = 0 :=
  (GaloisForLFunctions.orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half rho p hp).2
    (re_eq_half_of_forall_meixnerRootDomain h)

/-! ### The complementary deconvolution -/

/-- **Equation (18).**  The time-one prime weight factors through every complementary pair of
convolution times. -/
theorem meixnerPrimeWeight_split (theta : ℝ) (n : ℕ) :
    meixnerPrimeWeight 1 n = meixnerPrimeWeight theta n * meixnerPrimeWeight (1 - theta) n := by
  rw [meixnerPrimeWeight_eq_meixnerChar, meixnerPrimeWeight_eq_meixnerChar,
    meixnerPrimeWeight_eq_meixnerChar, ← meixnerChar_add theta (1 - theta)]
  ring_nf


end

end RHTower
