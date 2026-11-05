import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomRadialProfile
import GaloisForLFunctions.CompletedArithmeticForms.FourierPositiveHankel
import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomRankBoundary
import GaloisForLFunctions.RHTower.MellinHardyBridge
import GaloisForLFunctions.RHTower.WeightedLaplaceShift

/-!
# Strict first-atom center tails at every finite rank

The literal integrated reflection jets equal the signed Schwartz jets of
an explicitly normalized radial source. Its Fourier density is strictly
positive at every real frequency, so every finite moment matrix is positive
definite.
-/

open Complex Filter Set MeasureTheory Matrix
open scoped SchwartzMap FourierTransform BigOperators Topology
namespace GaloisForLFunctions.CompletedArithmeticForms
open HTGeometry _root_.RHTower
noncomputable section

/-- The positive normalization between radial and literal center tails. -/
def firstAtomCenterTailFactor : ℝ := 4 * Real.pi ^ (-(1 / 2 : ℝ))

theorem firstAtomCenterTailFactor_pos : 0 < firstAtomCenterTailFactor := by
  unfold firstAtomCenterTailFactor
  positivity

private theorem radial_half_power (s : ℝ) :
    Real.pi ^ (-(1 / 2 : ℝ)) * (Real.pi * Real.exp s) ^ (1 / 2 : ℝ) = Real.exp (s / 2) := by
  rw [Real.rpow_def_of_pos Real.pi_pos,
    Real.rpow_def_of_pos (mul_pos Real.pi_pos (Real.exp_pos s)),
    ← Real.exp_add, Real.log_mul Real.pi_pos.ne' (Real.exp_pos s).ne', Real.log_exp]
  congr 1
  ring

/-- Exact complex normalization of the literal reflected first atom. -/
theorem firstAtomComplexPair_eq_radialKernel (s : ℝ) (z : ℂ) :
    firstAtomComplexPair (s / 2) z =
      ((firstAtomCenterTailFactor * (Real.pi * Real.exp s) : ℝ) : ℂ) *
        firstAtomRadialKernel (Real.pi * Real.exp s) z := by
  let u := Real.pi * Real.exp s
  have hu : 0 < u := mul_pos Real.pi_pos (Real.exp_pos s)
  have hscale : thetaCuspSingleAtomReflectionScale 1 (s / 2) = u := by
    simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one,
      show 2 * (s / 2) = s by ring, u]
  have hp : u ^ (3 / 2 : ℝ) = u * u ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hu, Real.rpow_one]
  have hhalf : Real.pi ^ (-(1 / 2 : ℝ)) * u ^ (1 / 2 : ℝ) = Real.exp (s / 2) :=
    radial_half_power s
  have hcoeff : firstAtomCenterTailFactor * u * u ^ (3 / 2 : ℝ) =
      4 * u ^ 2 * Real.exp (s / 2) := by
    rw [hp, firstAtomCenterTailFactor]
    calc
      _ = 4 * u ^ 2 * (Real.pi ^ (-(1 / 2 : ℝ)) * u ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [hhalf]
  have he : (Real.exp (s / 2 - 2 * u) : ℂ) *
      Complex.exp (-2 * (u : ℂ) * (Complex.cosh (2 * z) - 1)) =
      (Real.exp (s / 2) : ℂ) * Complex.exp (-2 * (u : ℂ) * Complex.cosh (2 * z)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold firstAtomComplexPair
  rw [hscale]
  change ((4 * u ^ 2 * Real.exp (s / 2 - 2 * u) : ℝ) : ℂ) *
      Complex.exp (-2 * (u : ℂ) * (Complex.cosh (2 * z) - 1)) *
        (((2 * u - 3) ^ 2 : ℝ) - 12 * (u : ℂ) * (Complex.cosh (2 * z) - 1)) = _
  have hc : ((firstAtomCenterTailFactor * u : ℝ) : ℂ) * (u ^ (3 / 2 : ℝ) : ℝ) =
      (4 * u ^ 2 * Real.exp (s / 2) : ℝ) := by exact_mod_cast hcoeff
  unfold firstAtomRadialKernel
  change _ = ((firstAtomCenterTailFactor * u : ℝ) : ℂ) *
    ((u ^ (3 / 2 : ℝ) : ℝ) * (4 * (u : ℂ) ^ 2 + 9 - 12 * (u : ℂ) * Complex.cosh (2 * z)) *
      Complex.exp (-2 * (u : ℂ) * Complex.cosh (2 * z)))
  calc
    _ = ((4 * u ^ 2 : ℝ) : ℂ) *
        ((Real.exp (s / 2 - 2 * u) : ℂ) *
          Complex.exp (-2 * (u : ℂ) * (Complex.cosh (2 * z) - 1))) *
        (4 * (u : ℂ) ^ 2 + 9 - 12 * (u : ℂ) * Complex.cosh (2 * z)) := by
      push_cast
      ring
    _ = _ := by
      rw [he]
      calc
        _ = ((4 * u ^ 2 * Real.exp (s / 2) : ℝ) : ℂ) *
            (4 * (u : ℂ) ^ 2 + 9 - 12 * (u : ℂ) * Complex.cosh (2 * z)) *
              Complex.exp (-2 * (u : ℂ) * Complex.cosh (2 * z)) := by push_cast; ring
        _ = _ := by rw [← hc]; ring

/-- The normalization preserves every literal source jet, with no rank restriction. -/
theorem firstAtomReflectionJet_eq_radialKernel_jet (s : ℝ) (n : ℕ) :
    thetaCuspFirstAtomReflectionJet n (s / 2) =
      firstAtomCenterTailFactor * (Real.pi * Real.exp s) *
        (iteratedDeriv n (firstAtomRadialKernel (Real.pi * Real.exp s)) 0).re := by
  have he := congrArg (fun f : ℂ → ℂ => iteratedDeriv n f 0)
    (funext (firstAtomComplexPair_eq_radialKernel s))
  rw [firstAtomComplexPair_jet, iteratedDeriv_const_mul_field] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hr

/-- Exponential radial coordinates identify each literal center tail. -/
theorem integral_center_to_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (r : ℝ) :
    (∫ s in Ioi r, (Real.pi * Real.exp s) • g (Real.pi * Real.exp s)) =
      ∫ u in Ioi (Real.pi * Real.exp r), g u := by
  rw [integral_Ioi_expScale (mul_pos Real.pi_pos (Real.exp_pos r))]
  have ht := GaloisForLFunctions.RHTower.setIntegral_Ioi_comp_add_right
    (fun s : ℝ => (Real.pi * Real.exp s) • g (Real.pi * Real.exp s)) r r
  rw [sub_self] at ht
  rw [← ht]
  apply integral_congr_ae
  filter_upwards with s
  rw [Real.exp_add]
  simp only [mul_assoc, mul_comm (Real.exp s) (Real.exp r)]

/-- The actual signed source-jet tail, at every derivative order. -/
def firstAtomCenterTailSignedJet (r : ℝ) (n : ℕ) : ℝ :=
  ∫ s in Ioi r, ((-I) ^ n).re * thetaCuspFirstAtomReflectionJet n (s / 2)

private theorem firstAtomRadialKernel_jet_im {u : ℝ} (hu : 0 < u) (n : ℕ) :
    (iteratedDeriv n (firstAtomRadialKernel u) 0).im = 0 := by
  let s := Real.log (u / Real.pi)
  have hs : Real.pi * Real.exp s = u := by
    dsimp only [s]
    rw [Real.exp_log (div_pos hu Real.pi_pos)]
    field_simp [Real.pi_ne_zero]
  have he := congrArg (fun f : ℂ → ℂ => iteratedDeriv n f 0)
    (funext (firstAtomComplexPair_eq_radialKernel s))
  rw [firstAtomComplexPair_jet, iteratedDeriv_const_mul_field, hs] at he
  have hi := congrArg Complex.im he
  simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero] at hi
  have hc : firstAtomCenterTailFactor * u ≠ 0 :=
    (mul_pos firstAtomCenterTailFactor_pos hu).ne'
  exact (mul_eq_zero.mp hi.symm).resolve_left hc

private theorem firstAtomRadialTail_jet_im {q : ℝ} (hq : 2 ≤ q) (n : ℕ) :
    (iteratedDeriv n (firstAtomRadialTail q) 0).im = 0 := by
  have hz : |(0 : ℂ).im| < Real.pi / 6 := by simp; positivity
  have hi := integrableOn_iteratedDeriv_firstAtomRadialKernel hq n hz
  have he := Complex.imCLM.integral_comp_comm hi
  simp only [Complex.imCLM_apply] at he
  rw [iteratedDeriv_firstAtomRadialTail hq n hz, ← he]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact firstAtomRadialKernel_jet_im (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    (hq.trans hu.le)) n

/-- Exact all-order bridge from literal center integrals to the Schwartz signed jets. -/
theorem firstAtomCenterTailSignedJet_eq {r : ℝ}
    (hq : 2 ≤ Real.pi * Real.exp r) (n : ℕ) :
    firstAtomCenterTailSignedJet r n = firstAtomCenterTailFactor *
      ((-I) ^ n * iteratedDeriv n
        (firstAtomRadialTailSchwartz (Real.pi * Real.exp r) hq) 0).re := by
  let q := Real.pi * Real.exp r
  let g : ℝ → ℝ := fun u => (iteratedDeriv n (firstAtomRadialKernel u) 0).re
  have hz : |(0 : ℂ).im| < Real.pi / 6 := by simp; positivity
  have hi := integrableOn_iteratedDeriv_firstAtomRadialKernel hq n hz
  have hr := Complex.reCLM.integral_comp_comm hi
  simp only [Complex.reCLM_apply] at hr
  have hj : (∫ u in Ioi q, g u) = (iteratedDeriv n (firstAtomRadialTail q) 0).re := by
    rw [iteratedDeriv_firstAtomRadialTail hq n hz]
    exact hr
  have hsch : iteratedDeriv n (firstAtomRadialTailSchwartz q hq) 0 =
      iteratedDeriv n (firstAtomRadialTail q) 0 := by
    change iteratedDeriv n (fun t : ℝ => firstAtomRadialTail q (t : ℂ)) 0 = _
    exact HTGeometry.iteratedDeriv_ofReal_on_strip (by positivity : 0 < Real.pi / 6)
      (fun z hz => differentiableAt_firstAtomRadialTail hq hz) n 0
  have he : firstAtomCenterTailSignedJet r n =
      firstAtomCenterTailFactor * ((-I) ^ n).re *
        ∫ s in Ioi r, (Real.pi * Real.exp s) * g (Real.pi * Real.exp s) := by
    unfold firstAtomCenterTailSignedJet
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    rw [firstAtomReflectionJet_eq_radialKernel_jet]
    dsimp only [g]
    ring
  rw [he]
  have ht := integral_center_to_radial g r
  simp only [smul_eq_mul] at ht
  rw [ht, hj, hsch]
  rw [Complex.mul_re, firstAtomRadialTail_jet_im (q := q) hq n, mul_zero, sub_zero]
  ring

/-- The matrix of all literal integrated Fourier-signed first-atom reflection jets. -/
def firstAtomCenterTailMatrix (r : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => firstAtomCenterTailSignedJet r ((i : ℕ) + (j : ℕ))

/-- Every finite rank of the literal first-atom center-tail matrix is strictly positive. -/
theorem firstAtomCenterTailMatrix_posDef {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    (firstAtomCenterTailMatrix r N).PosDef := by
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have he : 1 ≤ Real.exp r := Real.one_le_exp hr
  have hq3 : 3 < Real.pi * Real.exp r :=
    hpi.trans_le (le_mul_of_one_le_right Real.pi_pos.le he)
  have hq2 : 2 ≤ Real.pi * Real.exp r := by linarith only [hq3]
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hq : 1 + Real.sqrt 2 < Real.pi * Real.exp r := by linarith only [hq3, hsqrt]
  have hs := signedSchwartzJet_hankel_posDef
    (firstAtomRadialTailSchwartz (Real.pi * Real.exp r) hq2)
    (fourier_firstAtomRadialTail_re_pos hq2 hq) N
  have hp := momentHankelMatrix_posDef_geometric firstAtomCenterTailFactor_pos
    (show (1 : ℝ) ≠ 0 by norm_num) hs
  have hm : firstAtomCenterTailMatrix r N =
      _root_.HTGeometry.momentHankelMatrix
        (fun n => firstAtomCenterTailFactor * (1 : ℝ) ^ n *
          ((-I) ^ n * iteratedDeriv n
            (firstAtomRadialTailSchwartz (Real.pi * Real.exp r) hq2) 0).re) N := by
    ext i j
    simp only [firstAtomCenterTailMatrix, _root_.HTGeometry.momentHankelMatrix,
      firstAtomCenterTailSignedJet_eq hq2, one_pow, mul_one]
  rw [hm]
  exact hp

/-- In particular, every determinant in the literal first-atom tail hierarchy is positive. -/
theorem firstAtomCenterTailMatrix_det_pos {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    0 < (firstAtomCenterTailMatrix r N).det :=
  (firstAtomCenterTailMatrix_posDef hr N).det_pos

/-- The literal derivative-integral matrix is positive definite for every finite size. -/
theorem firstAtomLiteralCenterTailMatrix_posDef {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    Matrix.PosDef (fun i j : Fin N => ∫ s in Ioi r, ((-I) ^ ((i : ℕ) + (j : ℕ))).re *
      iteratedDeriv ((i : ℕ) + (j : ℕ))
        (fun t : ℝ => thetaCuspSourceTerm (s / 2 + t) 1 *
          thetaCuspSourceTerm (s / 2 - t) 1) 0) := by
  exact firstAtomCenterTailMatrix_posDef hr N

end
end GaloisForLFunctions.CompletedArithmeticForms
