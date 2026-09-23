import GaloisForLFunctions.RHTower.ProlateActionLinear
import GaloisForLFunctions.RHTower.HermiteGaussianEnvelope
import GaloisForLFunctions.RHTower.ProlateSecondMoment

/-!
# The rescaled Hermite trial family

The trial space for the prolate spectrum is spanned by the rescaled Hermite functions
`Φ_n^c(x) = φ_n(√c·x)` on the aperture.  This module fixes the family together with its first two
derivatives as explicit functions, and computes the prolate action on it exactly:

`(1−x²)Φ_n″ − 2xΦ_n′ − c²x²Φ_n
  = −c(2n+1)(1−x²)·φ_n(√c x) − c²x⁴·φ_n(√c x) − 2√c·x·φ_n′(√c x)` .

The first term is the `c`-sized main term carrying the oscillator rung; the other two are the
`O(1)` corrections whose integrals stay bounded as the bandwidth grows.
-/

open Filter Topology Set

noncomputable section

namespace RHTower

/-- The rescaled Hermite trial function on the aperture. -/
def prolateHermiteTrial (c : ℝ) (n : ℕ) (x : ℝ) : ℝ := hermiteFun n (Real.sqrt c * x)

/-- Its first derivative. -/
def prolateHermiteTrialDeriv (c : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt c * deriv (hermiteFun n) (Real.sqrt c * x)

/-- Its second derivative. -/
def prolateHermiteTrialDeriv2 (c : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  c * (hermiteRungP n (Real.sqrt c * x) * hermiteFun n (Real.sqrt c * x))

theorem prolateHermiteTrial_eq (c : ℝ) (n : ℕ) :
    prolateHermiteTrial c n = fun x => hermiteFun n (Real.sqrt c * x) := rfl

theorem prolateHermiteTrialDeriv_eq (c : ℝ) (n : ℕ) :
    prolateHermiteTrialDeriv c n
      = fun x => Real.sqrt c * deriv (hermiteFun n) (Real.sqrt c * x) := rfl

theorem prolateHermiteTrialDeriv2_eq (c : ℝ) (n : ℕ) :
    prolateHermiteTrialDeriv2 c n
      = fun x => c * (hermiteRungP n (Real.sqrt c * x) * hermiteFun n (Real.sqrt c * x)) := rfl

theorem hermiteRungP_eq (n : ℕ) :
    hermiteRungP n = fun xi : ℝ => xi ^ (2 : ℕ) - (2 * (n : ℝ) + 1) := rfl

theorem hasDerivAt_sqrt_mul (c x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sqrt c * y) (Real.sqrt c) x := by
  simpa using (hasDerivAt_id x).const_mul (Real.sqrt c)

theorem hasDerivAt_prolateHermiteTrial (c : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (prolateHermiteTrial c n) (prolateHermiteTrialDeriv c n x) x := by
  have h := (hasDerivAt_hermiteFun n (Real.sqrt c * x)).comp x (hasDerivAt_sqrt_mul c x)
  refine h.congr_deriv ?_
  rw [prolateHermiteTrialDeriv]
  ring

theorem hasDerivAt_prolateHermiteTrialDeriv {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : ℝ) :
    HasDerivAt (prolateHermiteTrialDeriv c n) (prolateHermiteTrialDeriv2 c n x) x := by
  have h := ((hasDerivAt_deriv_hermiteFun n (Real.sqrt c * x)).comp x
    (hasDerivAt_sqrt_mul c x)).const_mul (Real.sqrt c)
  refine h.congr_deriv ?_
  rw [prolateHermiteTrialDeriv2]
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc
  linear_combination (hermiteRungP n (Real.sqrt c * x)
    * hermiteFun n (Real.sqrt c * x)) * hsq

theorem continuous_prolateHermiteTrial (c : ℝ) (n : ℕ) :
    Continuous (prolateHermiteTrial c n) := by
  rw [prolateHermiteTrial_eq]
  exact (continuous_hermiteFun n).comp (continuous_const.mul continuous_id)

theorem continuous_prolateHermiteTrialDeriv (c : ℝ) (n : ℕ) :
    Continuous (prolateHermiteTrialDeriv c n) := by
  rw [prolateHermiteTrialDeriv_eq]
  exact continuous_const.mul
    ((continuous_deriv_hermiteFun n).comp (continuous_const.mul continuous_id))

theorem continuous_prolateHermiteTrialDeriv2 (c : ℝ) (n : ℕ) :
    Continuous (prolateHermiteTrialDeriv2 c n) := by
  rw [prolateHermiteTrialDeriv2_eq, hermiteRungP_eq]
  have hlin : Continuous fun x : ℝ => Real.sqrt c * x := continuous_const.mul continuous_id
  exact continuous_const.mul
    ((((hlin.pow 2).sub continuous_const)).mul ((continuous_hermiteFun n).comp hlin))

/-- **The prolate action on the rescaled Hermite trial function.**  The rung term carries the full
factor `c`; the two remaining terms are the bounded corrections. -/
theorem prolateHermiteTrial_action {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : ℝ) :
    (1 - x ^ (2 : ℕ)) * prolateHermiteTrialDeriv2 c n x
        - 2 * x * prolateHermiteTrialDeriv c n x
        - c ^ (2 : ℕ) * x ^ (2 : ℕ) * prolateHermiteTrial c n x
      = -(c * (2 * (n : ℝ) + 1)) * ((1 - x ^ (2 : ℕ)) * hermiteFun n (Real.sqrt c * x))
        - c ^ (2 : ℕ) * x ^ (4 : ℕ) * hermiteFun n (Real.sqrt c * x)
        - 2 * Real.sqrt c * (x * deriv (hermiteFun n) (Real.sqrt c * x)) := by
  rw [prolateHermiteTrialDeriv2, prolateHermiteTrialDeriv, prolateHermiteTrial, hermiteRungP]
  have hsq : (Real.sqrt c * x) ^ (2 : ℕ) = c * x ^ (2 : ℕ) := by
    rw [mul_pow, Real.sq_sqrt hc]
  rw [hsq]
  ring

/-- Change of variables to the Hermite scale: an aperture integral of a rescaled integrand is the
window integral divided by `√c`. -/
theorem integral_comp_sqrt_mul {c : ℝ} (hc : 0 < c) (F : ℝ → ℝ) :
    (∫ x in (-1 : ℝ)..1, F (Real.sqrt c * x))
      = (1 / Real.sqrt c) * ∫ xi in (-Real.sqrt c)..(Real.sqrt c), F xi := by
  have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hbase := integral_comp_div_sqrt hc (fun y : ℝ => F (Real.sqrt c * y))
  have hcong : (∫ xi in (-Real.sqrt c)..(Real.sqrt c), F (Real.sqrt c * (xi / Real.sqrt c)))
      = ∫ xi in (-Real.sqrt c)..(Real.sqrt c), F xi :=
    intervalIntegral.integral_congr fun xi _ => by rw [mul_div_cancel₀ xi hs]
  rw [hcong] at hbase
  rw [hbase]
  field_simp

/-- **The pairwise Rayleigh numerator at the Hermite scale.**  All the bandwidth dependence is the
single explicit factor `c` on the rung term. -/
theorem integral_trialPair_numerator {c : ℝ} (hc : 0 < c) (m n : ℕ) :
    (∫ x in (-1 : ℝ)..1,
        ((1 - x ^ (2 : ℕ)) * prolateHermiteTrialDeriv2 c m x
          - 2 * x * prolateHermiteTrialDeriv c m x
          - c ^ (2 : ℕ) * x ^ (2 : ℕ) * prolateHermiteTrial c m x) * prolateHermiteTrial c n x)
      = (1 / Real.sqrt c) * ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
          ((-(c * (2 * (m : ℝ) + 1)) + (2 * (m : ℝ) + 1) * xi ^ (2 : ℕ) - xi ^ (4 : ℕ))
              * (hermiteFun m xi * hermiteFun n xi)
            - 2 * xi * (deriv (hermiteFun m) xi * hermiteFun n xi)) := by
  rw [← integral_comp_sqrt_mul hc]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [prolateHermiteTrial_action hc.le m x, prolateHermiteTrial]
  have hsq : (Real.sqrt c * x) ^ (2 : ℕ) = c * x ^ (2 : ℕ) := by
    rw [mul_pow, Real.sq_sqrt hc.le]
  have hquart : (Real.sqrt c * x) ^ (4 : ℕ) = c ^ (2 : ℕ) * x ^ (4 : ℕ) := by
    have : (Real.sqrt c * x) ^ (4 : ℕ) = ((Real.sqrt c * x) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    rw [this, hsq]
    ring
  rw [hsq, hquart]
  ring

/-- The pairwise aperture norm at the Hermite scale. -/
theorem integral_trialPair_norm {c : ℝ} (hc : 0 < c) (m n : ℕ) :
    (∫ x in (-1 : ℝ)..1, prolateHermiteTrial c m x * prolateHermiteTrial c n x)
      = (1 / Real.sqrt c)
        * ∫ xi in (-Real.sqrt c)..(Real.sqrt c), hermiteFun m xi * hermiteFun n xi := by
  rw [← integral_comp_sqrt_mul hc]
  rfl

end RHTower
