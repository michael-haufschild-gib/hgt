import GaloisForLFunctions.HTGeometry.GaussianThetaCharacteristics

/-!
# Quadratic instanton duality and its convergence disk

The Gaussian Fourier inversion `γ ↦ π²/γ` induces the action transformation
`A ↦ iπA/γ`. Its square reverses `A`, and the stationary action changes sign.
The reciprocal quadratic convergence inequality is exactly an open disk, empty when the action
vanishes and tangent to the origin otherwise.
These statements concern the Gaussian algebra and convergence geometry alone.
-/

open Complex Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Linear action after Fourier exchange of the quadratic saddle. -/
def quadraticDualAction (A γ : ℂ) : ℂ := Complex.I * Real.pi * A / γ

/-- Reciprocal Fourier bandwidth of the quadratic Gaussian. -/
def quadraticDualAnnulus (γ : ℂ) : ℂ := (Real.pi : ℂ) ^ 2 / γ

/-- The quadratic stationary-action formula, with division totalized at zero. -/
def quadraticStationaryAction (A γ : ℂ) : ℂ := -(A ^ 2) / (4 * γ)

/-- The annulus duality is involutive, including the totalized value at zero. -/
theorem quadraticDualAnnulus_involutive (γ : ℂ) :
    quadraticDualAnnulus (quadraticDualAnnulus γ) = γ := by
  unfold quadraticDualAnnulus
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hp]

/-- Twice exchanging the Gaussian variables reverses the linear action. -/
theorem quadraticDualAction_twice (A z : ℂ) :
    quadraticDualAction (quadraticDualAction A (Complex.exp z))
      (quadraticDualAnnulus (Complex.exp z)) = -A := by
  unfold quadraticDualAction quadraticDualAnnulus
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [Complex.exp_ne_zero, hp]; ring_nf; simp only [Complex.I_sq]; ring

/-- The two stationary actions are exact opposites. -/
theorem quadraticStationaryAction_dual (A γ : ℂ) :
    quadraticStationaryAction (quadraticDualAction A γ) (quadraticDualAnnulus γ) =
      -quadraticStationaryAction A γ := by
  by_cases hγ : γ = 0
  · simp [hγ, quadraticStationaryAction, quadraticDualAction, quadraticDualAnnulus]
  · unfold quadraticStationaryAction quadraticDualAction quadraticDualAnnulus
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hγ, hp]; ring_nf; simp only [Complex.I_sq]; ring

/-- Theta duality preserves the open right half-plane exactly. -/
theorem quadraticDualAnnulus_re_pos_iff (γ : ℂ) :
    0 < (quadraticDualAnnulus γ).re ↔ 0 < γ.re := by
  by_cases hγ : γ = 0
  · simp [hγ, quadraticDualAnnulus]
  · have hn : 0 < Complex.normSq γ := Complex.normSq_pos.mpr hγ
    have he : (quadraticDualAnnulus γ).re =
        Real.pi ^ 2 * γ.re / Complex.normSq γ := by
      simp [quadraticDualAnnulus, Complex.div_re, pow_two, Complex.mul_re, Complex.mul_im]
    rw [he, lt_div_iff₀ hn, zero_mul,
      mul_pos_iff_of_pos_left (sq_pos_of_pos Real.pi_pos)]

/-- The original and Fourier-dual theta nomes have precisely the same convergence chamber. -/
theorem quadraticDualAnnulus_nome_norm_lt_one_iff (γ : ℂ) :
    ‖Complex.exp (-quadraticDualAnnulus γ)‖ < 1 ↔ ‖Complex.exp (-γ)‖ < 1 := by
  simp only [Complex.norm_exp, Complex.neg_re, Real.exp_lt_one_iff, neg_lt_zero]
  exact quadraticDualAnnulus_re_pos_iff γ

/-- The complex dual annulus restricts to the existing real lattice Fourier bandwidth. -/
theorem quadraticDualAnnulus_real_bandwidth (s : ℝ) :
    quadraticDualAnnulus (Real.exp s) = ((Real.pi ^ 2 / Real.exp s : ℝ) : ℂ) := by
  simp only [quadraticDualAnnulus, Complex.ofReal_div, Complex.ofReal_pow]

private theorem reciprocal_convergence_disk (A t : ℂ) (b : ℝ) (hb : 0 < b) :
    0 < (-(b : ℂ) + A ^ 2 / (4 * t)).re ↔
      t ∈ ball (A ^ 2 / (8 * (b : ℂ)))
        ‖A ^ 2 / (8 * (b : ℂ))‖ := by
  by_cases ht : t = 0
  · have hneg : ¬ 0 < -b := by linarith only [hb]
    simp [ht, dist_eq_norm, norm_neg, hneg]
  · have hn : 0 < Complex.normSq t := Complex.normSq_pos.mpr ht
    have he : (A ^ 2 / (4 * t)).re =
        ((A ^ 2).re * t.re + (A ^ 2).im * t.im) / (4 * Complex.normSq t) := by
      norm_num [Complex.div_re, Complex.normSq_mul, Complex.mul_re, Complex.mul_im]
      field_simp [hn.ne']; ring
    have hr : (A ^ 2 / (8 * (b : ℂ))).re =
        (A ^ 2).re / (8 * b) := by
      norm_num [Complex.div_re]
      field_simp [hb.ne']; ring
    have hi : (A ^ 2 / (8 * (b : ℂ))).im =
        (A ^ 2).im / (8 * b) := by
      norm_num [Complex.div_im]
      field_simp [hb.ne']; ring
    have hdiff : Complex.normSq (t - A ^ 2 / (8 * (b : ℂ))) -
        Complex.normSq (A ^ 2 / (8 * (b : ℂ))) =
        Complex.normSq t - ((A ^ 2).re * t.re + (A ^ 2).im * t.im) /
          (4 * b) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      simp only [hr, hi]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    have hball : t ∈ ball (A ^ 2 / (8 * (b : ℂ)))
        ‖A ^ 2 / (8 * (b : ℂ))‖ ↔
        Complex.normSq t * (4 * b) <
          (A ^ 2).re * t.re + (A ^ 2).im * t.im := by
      rw [mem_ball, dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
        ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        ← sub_neg, hdiff, sub_neg, lt_div_iff₀ (by positivity)]
    rw [hball, Complex.add_re, Complex.neg_re, Complex.ofReal_re, he]
    rw [show (0 < -b +
        ((A ^ 2).re * t.re + (A ^ 2).im * t.im) / (4 * Complex.normSq t)) ↔
        b < ((A ^ 2).re * t.re + (A ^ 2).im * t.im) /
          (4 * Complex.normSq t) by
      constructor <;> intro h <;> linarith only [h]]
    rw [lt_div_iff₀ (by positivity)]
    ring_nf

/-- A reciprocal Gaussian convergence region is exactly an open disk, possibly empty. -/
theorem quadratic_reciprocal_convergence_disk (A t : ℂ) (s : ℝ) :
    0 < (-(Real.exp s : ℂ) + A ^ 2 / (4 * t)).re ↔
      t ∈ ball (A ^ 2 / (8 * (Real.exp s : ℂ)))
        ‖A ^ 2 / (8 * (Real.exp s : ℂ))‖ :=
  reciprocal_convergence_disk A t (Real.exp s) (Real.exp_pos s)

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.quadraticDualAnnulus_involutive
#print axioms GaloisForLFunctions.HTGeometry.quadraticDualAction_twice
#print axioms GaloisForLFunctions.HTGeometry.quadraticStationaryAction_dual
#print axioms GaloisForLFunctions.HTGeometry.quadraticDualAnnulus_re_pos_iff
#print axioms GaloisForLFunctions.HTGeometry.quadraticDualAnnulus_nome_norm_lt_one_iff
#print axioms GaloisForLFunctions.HTGeometry.quadraticDualAnnulus_real_bandwidth
#print axioms GaloisForLFunctions.HTGeometry.quadratic_reciprocal_convergence_disk
