import GaloisForLFunctions.HTGeometry.GaussBonnetThermodynamicPrescriptions
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSchwarzschildRecoilCompletionEndpoint

/-!
# Logarithmic entropy in the existing Schwarzschild recoil construction

Applies the logarithmic entropy in arXiv:2609.00025v1, equation (7), to the
normalized two-emission construction already formalized in
`ThetaCuspHawkingSchwarzschildRecoilCompletionEndpoint`.

The corrected candidate factors exactly into the old Gaussian and an explicit
nonnegative logarithmic correction. We prove a sharp two-point correlation
boundary, an explicit negative determinant beyond it, and strict residual-mass
dependence at fixed emission gap for every positive correction. Thus this
substitution cannot universally retain the original covariance interpretation.
These conclusions concern the substituted mathematical kernel; they make no
claim that the paper postulates or derives this recoil kernel.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry

def gaussBonnetRecoilLogRatio (x y : ℝ) : ℝ :=
  Real.log ((Real.exp x + Real.exp y) ^ (2 : ℕ) / (4 * Real.exp x * Real.exp y))

def gaussBonnetRecoilAction (a l x y : ℝ) : ℝ :=
  egbEntropyA a l (Real.exp x + Real.exp y) -
    (egbEntropyA a l (2 * Real.exp x) + egbEntropyA a l (2 * Real.exp y)) / 2

def gaussBonnetRecoilCoherence (a l x y : ℝ) : ℝ := Real.exp (gaussBonnetRecoilAction a l x y)

theorem gaussBonnetRecoilLogRatio_expansion (x y : ℝ) :
    gaussBonnetRecoilLogRatio x y =
      2 * Real.log (Real.exp x + Real.exp y) - 2 * Real.log 2 - x - y := by
  have hs : Real.exp x + Real.exp y ≠ 0 := by positivity
  have hx : 2 * Real.exp x ≠ 0 := by positivity
  have hy : 2 * Real.exp y ≠ 0 := by positivity
  unfold gaussBonnetRecoilLogRatio
  rw [show 4 * Real.exp x * Real.exp y = (2 * Real.exp x) * (2 * Real.exp y) by ring,
    Real.log_div (pow_ne_zero _ hs) (mul_ne_zero hx hy), Real.log_pow, Real.log_mul hx hy]
  rw [Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (Real.exp_ne_zero x),
    Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (Real.exp_ne_zero y), Real.log_exp, Real.log_exp]
  push_cast
  ring

theorem gaussBonnetRecoilAction_decomposition (a l x y : ℝ) :
    gaussBonnetRecoilAction a l x y = -Real.pi * (Real.exp x - Real.exp y) ^ (2 : ℕ) +
      2 * Real.pi * a ^ (2 : ℕ) * gaussBonnetRecoilLogRatio x y := by
  have hs : Real.exp x + Real.exp y ≠ 0 := by positivity
  have hx : 2 * Real.exp x ≠ 0 := by positivity
  have hy : 2 * Real.exp y ≠ 0 := by positivity
  rw [gaussBonnetRecoilAction, egbEntropyA, egbEntropyA, egbEntropyA,
    Real.log_div hs (Real.exp_ne_zero l), Real.log_div hx (Real.exp_ne_zero l),
    Real.log_div hy (Real.exp_ne_zero l)]
  rw [Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (Real.exp_ne_zero x),
    Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (Real.exp_ne_zero y),
    Real.log_exp, Real.log_exp, gaussBonnetRecoilLogRatio_expansion]
  simp only [Real.log_exp]
  ring

theorem gaussBonnetRecoilCoherence_factorization (a l x y : ℝ) :
    gaussBonnetRecoilCoherence a l x y =
      schwarzschildNormalizedTwoEmissionRecoilCoherence (Real.exp x + Real.exp y)
        (Real.exp x / 2) (Real.exp y / 2) *
      Real.exp (2 * Real.pi * a ^ (2 : ℕ) * gaussBonnetRecoilLogRatio x y) := by
  rw [gaussBonnetRecoilCoherence, gaussBonnetRecoilAction_decomposition, Real.exp_add,
    schwarzschildNormalizedTwoEmissionRecoilCoherence_eq]
  congr 2
  ring

theorem gaussBonnetRecoilLogRatio_lower_bound (x y : ℝ) :
    (Real.exp x - Real.exp y) ^ (2 : ℕ) / (Real.exp x + Real.exp y) ^ (2 : ℕ) ≤
      gaussBonnetRecoilLogRatio x y := by
  have hs : Real.exp x + Real.exp y ≠ 0 := by positivity
  have hp : 0 < (Real.exp x + Real.exp y) ^ (2 : ℕ) / (4 * Real.exp x * Real.exp y) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hp
  change _ ≤ Real.log _
  convert h using 1
  field_simp
  ring

theorem gaussBonnetRecoilLogRatio_nonneg (x y : ℝ) : 0 ≤ gaussBonnetRecoilLogRatio x y := by
  exact le_trans (by positivity) (gaussBonnetRecoilLogRatio_lower_bound x y)

theorem gaussBonnetRecoilCoherence_ge_schwarzschild (a l x y : ℝ) :
    schwarzschildNormalizedTwoEmissionRecoilCoherence (Real.exp x + Real.exp y)
      (Real.exp x / 2) (Real.exp y / 2) ≤ gaussBonnetRecoilCoherence a l x y := by
  rw [gaussBonnetRecoilCoherence_factorization]
  have h : 1 ≤ Real.exp (2 * Real.pi * a ^ (2 : ℕ) * gaussBonnetRecoilLogRatio x y) :=
    Real.one_le_exp_iff.mpr (by positivity [gaussBonnetRecoilLogRatio_nonneg x y])
  simpa only [schwarzschildNormalizedTwoEmissionRecoilCoherence_eq, mul_one] using mul_le_mul_of_nonneg_left h
    (Real.exp_pos (-4 * Real.pi * (Real.exp x / 2 - Real.exp y / 2) ^ (2 : ℕ))).le

theorem gaussBonnetRecoilCoherence_reference_independent (a l k x y : ℝ) :
    gaussBonnetRecoilCoherence a l x y = gaussBonnetRecoilCoherence a k x y := by
  simp only [gaussBonnetRecoilCoherence, gaussBonnetRecoilAction_decomposition]

theorem gaussBonnetRecoilCoherence_symmetric (a l x y : ℝ) :
    gaussBonnetRecoilCoherence a l x y = gaussBonnetRecoilCoherence a l y x := by
  unfold gaussBonnetRecoilCoherence gaussBonnetRecoilAction
  rw [add_comm (Real.exp x), add_comm (egbEntropyA a l (2 * Real.exp x))]

theorem gaussBonnetRecoilCoherence_diagonal (a l x : ℝ) : gaussBonnetRecoilCoherence a l x x = 1 := by
  unfold gaussBonnetRecoilCoherence gaussBonnetRecoilAction
  rw [show Real.exp x + Real.exp x = 2 * Real.exp x by ring]
  convert Real.exp_zero using 1
  congr 1
  ring

theorem gaussBonnetRecoil_highCoupling_lower_bound (l x y : ℝ) :
    Real.exp (Real.pi * (Real.exp x - Real.exp y) ^ (2 : ℕ)) ≤
      gaussBonnetRecoilCoherence (Real.exp x + Real.exp y) l x y := by
  rw [gaussBonnetRecoilCoherence, gaussBonnetRecoilAction_decomposition]
  apply Real.exp_le_exp.mpr
  have hs : 0 < (Real.exp x + Real.exp y) ^ (2 : ℕ) := by positivity
  have h := (div_le_iff₀ hs).mp (gaussBonnetRecoilLogRatio_lower_bound x y)
  have hp := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * Real.pi)
  nlinarith

theorem gaussBonnetRecoil_highCoupling_amplification_iff (l x y : ℝ) :
    1 < gaussBonnetRecoilCoherence (Real.exp x + Real.exp y) l x y ↔ x ≠ y := by
  constructor
  · intro h heq
    subst y
    rw [gaussBonnetRecoilCoherence_diagonal] at h
    exact lt_irrefl _ h
  · intro h
    have he : Real.exp x - Real.exp y ≠ 0 := fun he => h (Real.exp_injective (sub_eq_zero.mp he))
    have hp : 0 < Real.pi * (Real.exp x - Real.exp y) ^ (2 : ℕ) :=
      mul_pos Real.pi_pos (sq_pos_of_ne_zero he)
    exact lt_of_lt_of_le (Real.one_lt_exp_iff.mpr hp) (gaussBonnetRecoil_highCoupling_lower_bound l x y)

/-- An explicit positive-coupling covariance candidate has negative two-point determinant. -/
theorem gaussBonnetRecoil_highCoupling_negative_determinant (l x u : ℝ) :
    1 - gaussBonnetRecoilCoherence (Real.exp x + Real.exp (x + Real.exp u))
      l x (x + Real.exp u) ^ (2 : ℕ) < 0 := by
  have h := (gaussBonnetRecoil_highCoupling_amplification_iff l x (x + Real.exp u)).mpr
    (by linarith [Real.exp_pos u])
  nlinarith

/-- The exact coupling boundary for a normalized two-point correlation bound. -/
theorem gaussBonnetRecoilCoherence_le_one_iff (a l x y : ℝ) :
    gaussBonnetRecoilCoherence a l x y ≤ 1 ↔
      2 * a ^ (2 : ℕ) * gaussBonnetRecoilLogRatio x y ≤ (Real.exp x - Real.exp y) ^ (2 : ℕ) := by
  rw [gaussBonnetRecoilCoherence, Real.exp_le_one_iff, gaussBonnetRecoilAction_decomposition]
  have hp := Real.pi_pos
  constructor <;> intro h
  · nlinarith
  · nlinarith

/-- Fixed emission separation with a freely varying positive residual mass. -/
def gaussBonnetFixedGapCoherence (a l u t : ℝ) : ℝ :=
  gaussBonnetRecoilCoherence a l t (Real.log (Real.exp t + 2 * Real.exp u))

theorem gaussBonnetRecoilLogRatio_fixedGap (u t : ℝ) :
    gaussBonnetRecoilLogRatio t (Real.log (Real.exp t + 2 * Real.exp u)) =
      2 * Real.log (Real.exp t + Real.exp u) - t - Real.log (Real.exp t + 2 * Real.exp u) := by
  rw [gaussBonnetRecoilLogRatio_expansion, Real.exp_log (by positivity),
    show Real.exp t + (Real.exp t + 2 * Real.exp u) = 2 * (Real.exp t + Real.exp u) by ring,
    Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (by positivity : Real.exp t + Real.exp u ≠ 0)]
  ring

theorem gaussBonnetFixedGapCoherence_eq (a l u t : ℝ) :
    gaussBonnetFixedGapCoherence a l u t =
      Real.exp (-4 * Real.pi * Real.exp u ^ (2 : ℕ) + 2 * Real.pi * a ^ (2 : ℕ) *
        (2 * Real.log (Real.exp t + Real.exp u) - t - Real.log (Real.exp t + 2 * Real.exp u))) := by
  rw [gaussBonnetFixedGapCoherence, gaussBonnetRecoilCoherence,
    gaussBonnetRecoilAction_decomposition, gaussBonnetRecoilLogRatio_fixedGap,
    Real.exp_log (by positivity)]
  congr 1
  ring

theorem gaussBonnetFixedGapCoherence_schwarzschild_factor (a l u t : ℝ) :
    gaussBonnetFixedGapCoherence a l u t =
      schwarzschildNormalizedTwoEmissionRecoilCoherence (Real.exp t + 2 * Real.exp u) 0 (Real.exp u) *
      Real.exp (2 * Real.pi * a ^ (2 : ℕ) * gaussBonnetRecoilLogRatio t
        (Real.log (Real.exp t + 2 * Real.exp u))) := by
  rw [gaussBonnetFixedGapCoherence_eq, schwarzschildNormalizedTwoEmissionRecoilCoherence_eq,
    gaussBonnetRecoilLogRatio_fixedGap, Real.exp_add]
  simp

theorem gaussBonnetFixedGapCoherence_derivative (a l u t : ℝ) :
    HasDerivAt (gaussBonnetFixedGapCoherence a l u)
      (-4 * Real.pi * a ^ (2 : ℕ) * Real.exp u ^ (2 : ℕ) /
        ((Real.exp t + Real.exp u) * (Real.exp t + 2 * Real.exp u)) *
        gaussBonnetFixedGapCoherence a l u t) t := by
  have hx : Real.exp t + Real.exp u ≠ 0 := by positivity
  have hy : Real.exp t + 2 * Real.exp u ≠ 0 := by positivity
  have hlog := (((((Real.hasDerivAt_exp t).add_const (Real.exp u)).log hx).const_mul 2).sub
    (hasDerivAt_id t)).sub (((Real.hasDerivAt_exp t).add_const (2 * Real.exp u)).log hy)
  have h := (((hlog.const_mul (2 * Real.pi * a ^ (2 : ℕ))).const_add
    (-4 * Real.pi * Real.exp u ^ (2 : ℕ))).exp)
  rw [show gaussBonnetFixedGapCoherence a l u = _ from funext (gaussBonnetFixedGapCoherence_eq a l u)]
  apply h.congr_deriv
  dsimp
  field_simp
  ring

/-- Every strictly positive correction destroys residual-mass independence at fixed gap. -/
theorem gaussBonnetFixedGapCoherence_strictAnti (k l u : ℝ) :
    StrictAnti (gaussBonnetFixedGapCoherence (Real.exp k) l u) := by
  apply strictAnti_of_deriv_neg
  intro t
  rw [(gaussBonnetFixedGapCoherence_derivative (Real.exp k) l u t).deriv]
  have hc : 0 < gaussBonnetFixedGapCoherence (Real.exp k) l u t := by
    rw [gaussBonnetFixedGapCoherence_eq]
    positivity
  have hp : 0 < 4 * Real.pi * Real.exp k ^ (2 : ℕ) * Real.exp u ^ (2 : ℕ) := by positivity
  exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by nlinarith) (by positivity)) hc

end RHTower
