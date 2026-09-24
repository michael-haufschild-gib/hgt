import GaloisForLFunctions.RHTower.CoshPowerSpectrumOrderDerivative
import GaloisForLFunctions.RHTower.ThetaCuspWignerPairCenterWeight

/-!
# The spectrum of the log-scale theta Wigner pair kernel

The log-scale pair kernel is a combination of two hyperbolic-secant powers and the same two powers
weighted by `log (cosh y)`.  Both families have explicit cosine transforms — the second is minus
the order derivative of the first — so the log-scale spectrum is explicit in `Γ`, `Γ'` and the
order derivative of `2^(b-1) |Γ((b+iξ)/2)|² / Γ(b)`.

Together with the RH-blindness of the exponential weight this makes the archimedean profile of the
centre-weighted current completely explicit.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- Universal log-scale pair kernel in the hyperbolic separation. -/
def thetaCuspWignerPairLogKernel (σ y : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-σ) / 2 *
    ((1 / Real.cosh y) ^ (σ + 2) * thetaCuspWignerRadialLogWeight σ (Real.cosh y))

/-- Spectral density of the log-scale pair kernel. -/
def thetaCuspWignerPairLogSpectrum (σ ξ : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-σ) / 2 *
    (deriv Real.Gamma (σ + 4) * coshPowerSpectrum (σ + 4) ξ +
      (9 * deriv Real.Gamma (σ + 2) - 6 * deriv Real.Gamma (σ + 3)) *
        coshPowerSpectrum (σ + 2) ξ +
      (Real.Gamma (σ + 4) * deriv (fun b : ℝ => coshPowerSpectrum b ξ) (σ + 4) +
        (9 * Real.Gamma (σ + 2) - 6 * Real.Gamma (σ + 3)) *
          deriv (fun b : ℝ => coshPowerSpectrum b ξ) (σ + 2)))

theorem thetaCuspWignerPairLogKernel_eq_cosh_combination (σ y : ℝ) :
    thetaCuspWignerPairLogKernel σ y =
      (2 * Real.pi) ^ (-σ) / 2 *
        (deriv Real.Gamma (σ + 4) * (Real.cosh y) ^ (-(σ + 4)) +
          (9 * deriv Real.Gamma (σ + 2) - 6 * deriv Real.Gamma (σ + 3)) * (Real.cosh y) ^ (-(σ + 2)) +
          (-Real.Gamma (σ + 4)) * (Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 4))) +
          (-(9 * Real.Gamma (σ + 2) - 6 * Real.Gamma (σ + 3))) * (Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 2)))) := by
  have hc : (0 : ℝ) < Real.cosh y := Real.cosh_pos y
  have hinv : (1 / Real.cosh y) ^ (σ + 2) = Real.cosh y ^ (-(σ + 2)) := by
    rw [one_div, Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
  have hC2 : Real.cosh y ^ (-(σ + 4)) =
      Real.cosh y ^ (-(σ + 2)) / Real.cosh y ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (Real.cosh y) 2, ← Real.rpow_sub hc]
    congr 1
    push_cast
    ring
  rw [thetaCuspWignerPairLogKernel, thetaCuspWignerRadialLogWeight, hinv, hC2]
  field_simp
  ring

/-- **The log-scale pair kernel has an explicit spectrum.** -/
theorem integral_thetaCuspWignerPairLogKernel_mul_cos {σ : ℝ} (hσ : 0 < σ) (ξ : ℝ) :
    (∫ y : ℝ, thetaCuspWignerPairLogKernel σ y * Real.cos (ξ * y)) =
      thetaCuspWignerPairLogSpectrum σ ξ := by
  have j4 : Integrable (fun y : ℝ => ((Real.cosh y) ^ (-(σ + 4)) * Real.cos (ξ * y))) :=
    integrable_cosh_rpow_neg_mul_cos (by linarith) ξ
  have j2 : Integrable (fun y : ℝ => ((Real.cosh y) ^ (-(σ + 2)) * Real.cos (ξ * y))) :=
    integrable_cosh_rpow_neg_mul_cos (by linarith) ξ
  have k4 : Integrable (fun y : ℝ => (Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 4)) * Real.cos (ξ * y))) := by
    have h := (integrable_log_cosh_mul_cosh_rpow_neg_mul_cos
      (b := σ + 4) (by linarith) ξ).neg
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    show -(-(Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 4))) * Real.cos (ξ * y)) =
      Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 4)) * Real.cos (ξ * y)
    ring
  have k2 : Integrable (fun y : ℝ => (Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 2)) * Real.cos (ξ * y))) := by
    have h := (integrable_log_cosh_mul_cosh_rpow_neg_mul_cos
      (b := σ + 2) (by linarith) ξ).neg
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    show -(-(Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 2))) * Real.cos (ξ * y)) =
      Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 2)) * Real.cos (ξ * y)
    ring
  have i1 : Integrable (fun y : ℝ => deriv Real.Gamma (σ + 4) * ((Real.cosh y) ^ (-(σ + 4)) * Real.cos (ξ * y))) := j4.const_mul _
  have i2 : Integrable (fun y : ℝ => (9 * deriv Real.Gamma (σ + 2) - 6 * deriv Real.Gamma (σ + 3)) * ((Real.cosh y) ^ (-(σ + 2)) * Real.cos (ξ * y))) := j2.const_mul _
  have i3 : Integrable (fun y : ℝ => (-Real.Gamma (σ + 4)) * (Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 4)) * Real.cos (ξ * y))) := k4.const_mul _
  have i4 : Integrable (fun y : ℝ => (-(9 * Real.Gamma (σ + 2) - 6 * Real.Gamma (σ + 3))) * (Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 2)) * Real.cos (ξ * y))) := k2.const_mul _
  have s12 : Integrable (fun y : ℝ => deriv Real.Gamma (σ + 4) * ((Real.cosh y) ^ (-(σ + 4)) * Real.cos (ξ * y)) + (9 * deriv Real.Gamma (σ + 2) - 6 * deriv Real.Gamma (σ + 3)) * ((Real.cosh y) ^ (-(σ + 2)) * Real.cos (ξ * y))) := i1.add i2
  have s123 : Integrable (fun y : ℝ =>
      deriv Real.Gamma (σ + 4) * ((Real.cosh y) ^ (-(σ + 4)) * Real.cos (ξ * y)) + (9 * deriv Real.Gamma (σ + 2) - 6 * deriv Real.Gamma (σ + 3)) * ((Real.cosh y) ^ (-(σ + 2)) * Real.cos (ξ * y)) + (-Real.Gamma (σ + 4)) * (Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 4)) * Real.cos (ξ * y))) := s12.add i3
  have hpt : ∀ y : ℝ, thetaCuspWignerPairLogKernel σ y * Real.cos (ξ * y) =
      (2 * Real.pi) ^ (-σ) / 2 *
        (deriv Real.Gamma (σ + 4) * ((Real.cosh y) ^ (-(σ + 4)) * Real.cos (ξ * y)) + (9 * deriv Real.Gamma (σ + 2) - 6 * deriv Real.Gamma (σ + 3)) * ((Real.cosh y) ^ (-(σ + 2)) * Real.cos (ξ * y)) + (-Real.Gamma (σ + 4)) * (Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 4)) * Real.cos (ξ * y)) + (-(9 * Real.Gamma (σ + 2) - 6 * Real.Gamma (σ + 3))) * (Real.log (Real.cosh y) * (Real.cosh y) ^ (-(σ + 2)) * Real.cos (ξ * y))) := by
    intro y
    rw [thetaCuspWignerPairLogKernel_eq_cosh_combination]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_add s123 i4, integral_add s12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_cosh_rpow_neg_mul_cos (by linarith : (0:ℝ) < σ + 4) ξ,
    integral_cosh_rpow_neg_mul_cos (by linarith : (0:ℝ) < σ + 2) ξ,
    integral_log_cosh_mul_cosh_rpow_neg_mul_cos (by linarith : (0:ℝ) < σ + 4) ξ,
    integral_log_cosh_mul_cosh_rpow_neg_mul_cos (by linarith : (0:ℝ) < σ + 2) ξ,
    thetaCuspWignerPairLogSpectrum]
  ring

/-! ## The two kernels of the centre-weighted current -/

theorem integral_log_scale_mul_exp_mul_thetaCuspSourceTerm_pair_factor {σ : ℝ} (hσ : 0 < σ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    (∫ u : ℝ, Real.log (thetaCuspWignerAtomScale n m u) * Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) =
      (n : ℝ) ^ (-σ) * (m : ℝ) ^ (-σ) *
        thetaCuspWignerPairLogKernel σ (2 * t + Real.log n - Real.log m) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [integral_log_scale_mul_exp_mul_thetaCuspSourceTerm_pair hσ hn hm t,
    thetaCuspWignerPairLogKernel]
  have hsplit : (2 * Real.pi * n * m) ^ σ =
      (2 * Real.pi) ^ σ * (n : ℝ) ^ σ * (m : ℝ) ^ σ := by
    rw [show 2 * Real.pi * (n : ℝ) * m = (2 * Real.pi * n) * m by ring,
      Real.mul_rpow (by positivity) hmR.le, Real.mul_rpow (by positivity) hnR.le]
  have h2pi : (0 : ℝ) < (2 * Real.pi) ^ σ := Real.rpow_pos_of_pos (by positivity) _
  have hnp : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnR _
  have hmp : (0 : ℝ) < (m : ℝ) ^ σ := Real.rpow_pos_of_pos hmR _
  rw [hsplit]
  simp only [Real.rpow_neg hnR.le, Real.rpow_neg hmR.le,
    Real.rpow_neg (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
  field_simp

/-- **The centre-weighted pair current in terms of its two universal kernels.**  The log-scale
kernel enters with weight one, the exponential kernel with weight `log (2π n m)`. -/
theorem integral_center_mul_exp_mul_thetaCuspSourceTerm_pair_factor {σ : ℝ} (hσ : 0 < σ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    (∫ u : ℝ, u * Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) =
      (1 / 2) * ((n : ℝ) ^ (-σ) * (m : ℝ) ^ (-σ)) *
        (thetaCuspWignerPairLogKernel σ (2 * t + Real.log n - Real.log m) -
          Real.log (2 * Real.pi * n * m) *
            thetaCuspWignerPairKernel σ (2 * t + Real.log n - Real.log m)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hI1 := integrable_log_scale_mul_exp_mul_thetaCuspSourceTerm_pair hσ hn hm t
  have hI2 := integrable_exp_mul_thetaCuspSourceTerm_pair hσ hn hm t
  have hpt : ∀ u : ℝ, u * Real.exp ((2 * σ - 1) * u) *
      (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m) =
      (1 / 2) * (Real.log (thetaCuspWignerAtomScale n m u) * Real.exp ((2 * σ - 1) * u) *
          (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) -
        (Real.log (2 * Real.pi * n * m) / 2) * (Real.exp ((2 * σ - 1) * u) *
          (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) := by
    intro u
    rw [log_thetaCuspWignerAtomScale hn hm u]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul,
    integral_log_scale_mul_exp_mul_thetaCuspSourceTerm_pair_factor hσ hn hm t,
    integral_exp_mul_thetaCuspSourceTerm_pair_factor hσ hn hm t]
  ring

end

end RHTower
