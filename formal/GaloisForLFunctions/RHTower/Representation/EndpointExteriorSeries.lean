import GaloisForLFunctions.RHTower.XiReciprocalCentreTotalPositivity
import GaloisForLFunctions.RHTower.XiHorizontalSliceTaylorPositivityConverse
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import GaloisForLFunctions.RHTower.Representation.EndpointCharacterDefect
import Mathlib.Analysis.Complex.Positivity

/-!
# Positive coefficients of the normalized endpoint exterior series

The entire center lift has derivatives `n! · θₙ / (2n)!`, where `θₙ` is a positive theta
moment. Taylor expansion of each derivative propagates nonnegativity along the positive axis.
Consequently the squared translate `G(1/4+z/M)²/G(1/4)²` has nonnegative coefficients at every
order. Its value and first derivative at zero are both one, with `M` the exact endpoint mass.
-/

noncomputable section
open scoped ComplexOrder
namespace RHTower
open GaloisForLFunctions.HTGeometry

/-- Taylor expansion of each derivative propagates positivity along the positive real axis. -/
theorem NonnegTaylorAtZero.iteratedDeriv_nonneg {f : ℂ → ℂ}
    (hf : NonnegTaylorAtZero f) {a : ℂ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ iteratedDeriv n f a := by
  have hd : Differentiable ℂ (iteratedDeriv n f) :=
    (hf.1.contDiff (n := ⊤)).differentiable_iteratedDeriv n (WithTop.coe_lt_top _)
  apply hd.nonneg_of_iteratedDeriv_nonneg (c := 0) _ ha
  intro k
  have he : iteratedDeriv k (iteratedDeriv n f) = iteratedDeriv (n + k) f := by
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
      ← Function.iterate_add_apply, add_comm]
  rw [he]
  exact hf.2 (n + k)

/-- Nonnegative translation and dilation preserve every nonnegative Taylor coefficient. -/
theorem NonnegTaylorAtZero.affine {f : ℂ → ℂ} (hf : NonnegTaylorAtZero f)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    NonnegTaylorAtZero (fun z => f ((a : ℂ) + (b : ℂ) * z)) := by
  have hs : Differentiable ℂ (fun z : ℂ => f ((a : ℂ) + z)) :=
    hf.1.comp (differentiable_const _ |>.add differentiable_id)
  refine ⟨hf.1.comp (by fun_prop), fun n => ?_⟩
  change 0 ≤ iteratedDeriv n ((fun z : ℂ => f ((a : ℂ) + z)) ∘
    (fun z : ℂ => (b : ℂ) * z)) 0
  simp only [Function.comp_def, iteratedDeriv_comp_const_mul hs.contDiff,
    mul_zero, iteratedDeriv_comp_const_add, add_zero]
  exact mul_nonneg (pow_nonneg (Complex.zero_le_real.mpr hb) _)
    (hf.iteratedDeriv_nonneg (Complex.zero_le_real.mpr ha) n)

/-- The center lift removes the alternating signs of the even Fourier-theta derivatives. -/
theorem iteratedDeriv_xiCentreLift_zero (n : ℕ) :
    iteratedDeriv n xiCentreLift 0 =
      ((n.factorial : ℝ) * thetaCuspRawEvenMoment n / ((2 * n).factorial : ℝ) : ℝ) := by
  have he : iteratedDeriv n (evenSquareLift XiC) 0 =
      (n.factorial : ℂ) * evenSquareCoeff XiC n := by
    have h := (hasFPowerSeriesOnBall_evenSquareLift XiC_differentiable).factorial_smul
      (1 : ℂ) n
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      Finset.prod_const_one, one_smul, FormalMultilinearSeries.ofScalars_apply_eq,
      one_pow, smul_eq_mul, mul_one, nsmul_eq_mul] at h
    exact h.symm
  unfold xiCentreLift
  rw [iteratedDeriv_comp_neg, neg_zero, smul_eq_mul, he,
    evenSquareCoeff, iteratedDeriv_XiC_zero_eq_rawEvenMoment]
  push_cast
  have hs : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_pow]; simp
  calc
    _ = (n.factorial : ℂ) * ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
      thetaCuspRawEvenMoment n / ((2 * n).factorial : ℂ) := by ring
    _ = _ := by rw [hs, mul_one]

theorem nonnegTaylorAtZero_xiCentreLift : NonnegTaylorAtZero xiCentreLift := by
  refine ⟨differentiable_xiCentreLift, fun n => ?_⟩
  rw [iteratedDeriv_xiCentreLift_zero]
  exact Complex.zero_le_real.mpr
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (thetaCuspRawEvenMoment_nonneg n))
      (Nat.cast_nonneg _))

/-- The normalized squared endpoint translate of the entire center lift. -/
def xiEndpointExteriorSeries (z : ℂ) : ℂ :=
  xiCentreLift (1 / 4 + z / xiEndpointColorMass) ^ 2 / xiCentreLift (1 / 4) ^ 2

/-- All endpoint exterior-series coefficients are nonnegative, without a zero-location premise. -/
theorem nonnegTaylorAtZero_xiEndpointExteriorSeries :
    NonnegTaylorAtZero xiEndpointExteriorSeries := by
  have ha : NonnegTaylorAtZero (fun z : ℂ =>
      xiCentreLift (1 / 4 + z / xiEndpointColorMass)) := by
    have h := nonnegTaylorAtZero_xiCentreLift.affine (a := 1 / 4)
      (b := xiEndpointColorMass⁻¹) (by positivity) (inv_nonneg.mpr xiEndpointColorMass_pos.le)
    simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using h
  have hc : (0 : ℂ) ≤ xiCentreLift (1 / 4) := by
    have h := nonnegTaylorAtZero_xiCentreLift.iteratedDeriv_nonneg
      (a := (1 / 4 : ℝ)) (Complex.zero_le_real.mpr (by positivity)) 0
    simpa using h
  have hi : (0 : ℂ) ≤ (xiCentreLift (1 / 4) ^ 2)⁻¹ := inv_nonneg.mpr (pow_nonneg hc 2)
  have h := (ha.mul ha).mul (nonnegTaylorAtZero_const hi)
  change NonnegTaylorAtZero (fun z : ℂ =>
    (xiCentreLift (1 / 4 + z / xiEndpointColorMass) *
      xiCentreLift (1 / 4 + z / xiEndpointColorMass)) * (xiCentreLift (1 / 4) ^ 2)⁻¹) at h
  change NonnegTaylorAtZero (fun z : ℂ =>
    xiCentreLift (1 / 4 + z / xiEndpointColorMass) ^ 2 / xiCentreLift (1 / 4) ^ 2)
  simpa only [pow_two, div_eq_mul_inv] using h


/-- The unrotated square variable of the completed xi function. -/
lemma xiCentreLift_sq (z : ℂ) : xiCentreLift (z ^ 2) = xi (1 / 2 + z) := by
  calc
    xiCentreLift (z ^ 2) = xiCentreLift (-((-Complex.I * z) ^ 2)) := by
      congr 1
      rw [mul_pow]
      simp [Complex.I_sq]
    _ = XiC (-Complex.I * z) := xiCentreLift_neg_sq _
    _ = xi (1 / 2 + z) := by
      unfold XiC
      congr 1
      linear_combination (-z) * Complex.I_sq

lemma xiCentreLift_quarter : xiCentreLift (1 / 4) = (1 / 2 : ℂ) := by
  have h := xiCentreLift_sq (1 / 2)
  norm_num only [one_div, inv_pow, Nat.cast_ofNat, show (2 : ℂ) ^ 2 = 4 by ring,
    show (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 1 by ring, xi_one] at h
  exact h

lemma xiEndpointColorMass_complex_eq :
    (xiEndpointColorMass : ℂ) = 2 * completedRiemannZeta₀ 1 := by
  calc
    (xiEndpointColorMass : ℂ) = ∑' q, xiStripEdgeWeight q := by
      rw [xiEndpointColorMass_eq]
      simpa only [xiStripEdgeWeight, one_div] using tsum_inv_zero_mul_one_sub_zero.symm
    _ = _ := hasSum_xiStripEdgeWeight.tsum_eq

lemma deriv_xiCentreLift_quarter :
    deriv xiCentreLift (1 / 4) = (xiEndpointColorMass : ℂ) / 4 := by
  have hinner : HasDerivAt (fun z : ℂ => z ^ 2) 1 (1 / 2) := by
    have h := (hasDerivAt_id (1 / 2 : ℂ)).pow 2
    norm_num at h
    exact h
  have houter : HasDerivAt xiCentreLift (deriv xiCentreLift (1 / 4))
      ((1 / 2 : ℂ) ^ 2) := by
    rw [show (1 / 2 : ℂ) ^ 2 = 1 / 4 by ring]
    exact (differentiable_xiCentreLift (1 / 4)).hasDerivAt
  have h1 : HasDerivAt (fun z : ℂ => xiCentreLift (z ^ 2))
      (deriv xiCentreLift (1 / 4)) (1 / 2) := by
    simpa only [mul_one, Function.comp_def] using houter.comp (1 / 2) hinner
  have h2 : HasDerivAt (fun z : ℂ => xi (1 / 2 + z))
      (completedRiemannZeta₀ 1 / 2) (1 / 2) := by
    have hxi : HasDerivAt xi (completedRiemannZeta₀ 1 / 2)
        (1 / 2 + (1 / 2 : ℂ)) := by
      norm_num
      exact hasDerivAt_xi_one_archimedeanGenusZeroSum
    simpa only [mul_one, Function.comp_def, id_eq] using hxi.comp (1 / 2)
      ((hasDerivAt_id (1 / 2 : ℂ)).const_add (1 / 2))
  have he : (fun z : ℂ => xiCentreLift (z ^ 2)) = (fun z : ℂ => xi (1 / 2 + z)) :=
    funext xiCentreLift_sq
  rw [he] at h1
  rw [h1.unique h2, xiEndpointColorMass_complex_eq]
  ring

lemma xiEndpointExteriorSeries_zero : xiEndpointExteriorSeries 0 = 1 := by
  simp only [xiEndpointExteriorSeries, zero_div, add_zero, xiCentreLift_quarter]
  norm_num

lemma hasDerivAt_xiEndpointExteriorSeries_zero : HasDerivAt xiEndpointExteriorSeries 1 0 := by
  have hM : (xiEndpointColorMass : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr xiEndpointColorMass_pos.ne'
  have hi : HasDerivAt (fun z : ℂ => 1 / 4 + z / xiEndpointColorMass)
      (1 / (xiEndpointColorMass : ℂ)) 0 :=
    ((hasDerivAt_id (0 : ℂ)).div_const (xiEndpointColorMass : ℂ)).const_add (1 / 4)
  have hg : HasDerivAt xiCentreLift ((xiEndpointColorMass : ℂ) / 4)
      (1 / 4 + (0 : ℂ) / xiEndpointColorMass) := by
    simpa only [zero_div, add_zero, deriv_xiCentreLift_quarter] using
      (differentiable_xiCentreLift (1 / 4)).hasDerivAt
  have h := (((hg.comp 0 hi).pow 2).div_const (xiCentreLift (1 / 4) ^ 2))
  change HasDerivAt xiEndpointExteriorSeries
    (2 * xiCentreLift (1 / 4 + 0 / xiEndpointColorMass) ^ (2 - 1) *
      ((xiEndpointColorMass : ℂ) / 4 * (1 / xiEndpointColorMass)) /
        xiCentreLift (1 / 4) ^ 2) 0 at h
  apply h.congr_deriv
  simp only [zero_div, add_zero, xiCentreLift_quarter]
  field_simp [hM]
  ring

end RHTower
