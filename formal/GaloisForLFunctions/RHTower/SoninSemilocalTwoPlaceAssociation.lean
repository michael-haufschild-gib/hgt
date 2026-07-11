import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section

namespace RHTower

open Set

/-- The inverse-square-root function is strictly convex on the positive real axis. -/
theorem strictConvexOn_rpow_neg_half :
    StrictConvexOn ℝ (Ioi 0) (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  · intro x hx
    exact (Real.continuousAt_rpow_const x (-(1 : ℝ) / 2) (Or.inl hx.ne')).continuousWithinAt
  · intro x hx
    rw [Real.iter_deriv_rpow_const]
    norm_num [descPochhammer]
    exact Real.rpow_pos_of_pos hx (-(5 / 2 : ℝ))

/-- The normalized Fourier transform of the archimedean cyclic measure. -/
def semilocalArchimedeanCharacteristic (t : ℝ) : ℝ :=
  (Real.cosh t) ^ (-(1 : ℝ) / 2)

/-- The covariance kernel of the second spectral moment against a Fourier mode.
For the archimedean cyclic measure this is
`E[s² exp(i t s)] - E[s²] E[exp(i t s)]`. -/
def semilocalArchimedeanSecondMomentCovarianceKernel (t : ℝ) : ℝ :=
  -(3 / 4 : ℝ) * semilocalArchimedeanCharacteristic t * Real.tanh t ^ 2

/-- Every nonconstant Fourier mode has strictly negative covariance with the
second spectral moment of the archimedean cyclic measure. -/
theorem semilocalArchimedeanSecondMomentCovarianceKernel_neg
    {t : ℝ} (ht : t ≠ 0) :
    semilocalArchimedeanSecondMomentCovarianceKernel t < 0 := by
  have hchar : 0 < semilocalArchimedeanCharacteristic t := by
    exact Real.rpow_pos_of_pos (Real.cosh_pos t) (-(1 : ℝ) / 2)
  have htanh : Real.tanh t ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    have hsinh : Real.sinh t ≠ 0 := by
      simpa using Real.sinh_strictMono.injective.ne ht
    exact div_ne_zero hsinh (Real.cosh_pos t).ne'
  have htanh_sq : 0 < Real.tanh t ^ 2 := sq_pos_of_ne_zero htanh
  dsimp [semilocalArchimedeanSecondMomentCovarianceKernel]
  nlinarith

/-- Distinct positive frequencies have a strictly positive cosine covariance for the
archimedean cyclic characteristic function. -/
theorem semilocalArchimedean_twoFrequencyAssociation_pos
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    semilocalArchimedeanCharacteristic u * semilocalArchimedeanCharacteristic v <
      (semilocalArchimedeanCharacteristic (u + v) +
        semilocalArchimedeanCharacteristic (u - v)) / 2 := by
  have hxy : Real.cosh (u + v) ≠ Real.cosh (u - v) := by
    rw [Real.cosh_add, Real.cosh_sub]
    have hsu : 0 < Real.sinh u := (Real.sinh_pos_iff).2 hu
    have hsv : 0 < Real.sinh v := (Real.sinh_pos_iff).2 hv
    nlinarith
  have hmid := strictConvexOn_rpow_neg_half.2
    (Real.cosh_pos (u + v)) (Real.cosh_pos (u - v)) hxy
    (show 0 < (1 / 2 : ℝ) by norm_num) (show 0 < (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  rw [Real.cosh_add, Real.cosh_sub] at hmid
  dsimp [semilocalArchimedeanCharacteristic]
  convert hmid using 1 <;> ring_nf
  · rw [← Real.mul_rpow (Real.cosh_pos u).le (Real.cosh_pos v).le]
  · rw [Real.cosh_add, Real.cosh_sub]

/-- The archimedean characteristic does not define a positive Hankel kernel by the tempting
sum-frequency prescription `K(u,v) = phi(u+v)`.  Already the two nodes `0,t` have a negative
Gram determinant.  Thus the exponential Gamma decay cannot be inserted as a diagonal damping
factor for the prime-log Herglotz carrier; a genuine relative prime--Gamma covariance is needed. -/
theorem semilocalArchimedeanCharacteristic_two_mul_lt_sq
    {t : ℝ} (ht : t ≠ 0) :
    semilocalArchimedeanCharacteristic (2 * t) <
      semilocalArchimedeanCharacteristic t ^ 2 := by
  have hsinh : Real.sinh t ≠ 0 := by
    simpa using Real.sinh_strictMono.injective.ne ht
  have hbase : Real.cosh t ^ 2 < Real.cosh (2 * t) := by
    rw [show 2 * t = t + t by ring, Real.cosh_add]
    nlinarith [sq_pos_of_ne_zero hsinh]
  have hpow := Real.rpow_lt_rpow_of_neg
    (sq_pos_of_pos (Real.cosh_pos t)) hbase (by norm_num : (-(1 : ℝ) / 2) < 0)
  dsimp [semilocalArchimedeanCharacteristic] at hpow ⊢
  rw [← Real.rpow_pow_comm (Real.cosh_pos t).le (-(1 : ℝ) / 2) 2] at hpow
  exact hpow

/-- The explicit negative `2 x 2` determinant for the sum-frequency Gamma Hankel kernel. -/
theorem semilocalArchimedeanCharacteristic_hankelDet_neg
    {t : ℝ} (ht : t ≠ 0) :
    semilocalArchimedeanCharacteristic 0 *
          semilocalArchimedeanCharacteristic (2 * t) -
        semilocalArchimedeanCharacteristic t ^ 2 < 0 := by
  simpa [semilocalArchimedeanCharacteristic] using
    sub_neg.mpr (semilocalArchimedeanCharacteristic_two_mul_lt_sq ht)

/-- The diagonally damped stationary Gamma covariance candidate.  On the paper-level Gamma
spectral model this is the Gram kernel of
`sqrt(phi(2t)) * exp(i t s)` in the archimedean cyclic `L²` space. -/
def semilocalArchimedeanDampedCovarianceKernel (t u : ℝ) : ℝ :=
  Real.sqrt (semilocalArchimedeanCharacteristic (2 * t)) *
    Real.sqrt (semilocalArchimedeanCharacteristic (2 * u)) *
      semilocalArchimedeanCharacteristic (t - u)

/-- Every scalar entry of the damped stationary Gamma covariance is strictly positive. -/
theorem semilocalArchimedeanDampedCovarianceKernel_pos (t u : ℝ) :
    0 < semilocalArchimedeanDampedCovarianceKernel t u := by
  unfold semilocalArchimedeanDampedCovarianceKernel
  have hchar (x : ℝ) : 0 < semilocalArchimedeanCharacteristic x := by
    exact Real.rpow_pos_of_pos (Real.cosh_pos x) (-(1 : ℝ) / 2)
  exact mul_pos (mul_pos (Real.sqrt_pos.2 (hchar (2 * t)))
    (Real.sqrt_pos.2 (hchar (2 * u)))) (hchar (t - u))

/-- The covariance diagonal is exactly the doubled-frequency Gamma characteristic. -/
theorem semilocalArchimedeanDampedCovarianceKernel_self (t : ℝ) :
    semilocalArchimedeanDampedCovarianceKernel t t =
      semilocalArchimedeanCharacteristic (2 * t) := by
  unfold semilocalArchimedeanDampedCovarianceKernel
  have hchar : 0 ≤ semilocalArchimedeanCharacteristic (2 * t) :=
    (Real.rpow_pos_of_pos (Real.cosh_pos (2 * t)) (-(1 : ℝ) / 2)).le
  rw [sub_self]
  simp only [semilocalArchimedeanCharacteristic, Real.cosh_zero, Real.one_rpow, mul_one]
  simpa [pow_two] using Real.sq_sqrt hchar

/-- Exact exponential upper bound for the Gamma covariance diagonal. -/
theorem semilocalArchimedeanCharacteristic_two_mul_le_sqrtTwo_mul_exp_neg (t : ℝ) :
    semilocalArchimedeanCharacteristic (2 * t) ≤
      Real.sqrt 2 * Real.exp (-t) := by
  have hexp : Real.exp (2 * t) / 2 ≤ Real.cosh (2 * t) := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-(2 * t))
    linarith
  have hpow := Real.rpow_le_rpow_of_nonpos
    (by positivity : 0 < Real.exp (2 * t) / 2) hexp
      (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
  dsimp [semilocalArchimedeanCharacteristic]
  refine hpow.trans_eq ?_
  rw [Real.div_rpow (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.exp_mul]
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.sqrt_eq_rpow]
  rw [div_inv_eq_mul]
  rw [show 2 * t * -(1 / 2 : ℝ) = -t by ring]
  ring

end RHTower
