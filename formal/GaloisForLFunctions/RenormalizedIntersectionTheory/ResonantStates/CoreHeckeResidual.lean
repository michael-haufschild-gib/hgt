import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CoreReturnMass
import GaloisForLFunctions.RHTower.EisensteinHeckeSecondMoment

/-!
# The automorphic Hecke residual persists in the compact core

On the single-return rectangle, the coordinate residual dominates the returning
Weyl term in modulus. This prevents cancellation at every frequency.
-/

open Complex MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- The genuine dyadic eigen-equation defect of the truncated automorphic state. -/
def dyadicEigenResidual (u : ℂ) (z : ℍ) : ℂ :=
  dyadicHecke (automorphicTruncation u 1) z -
    ((2 : ℂ) ^ u + (2 : ℂ) ^ (-u)) * automorphicTruncation u 1 z

theorem dyadicEigenResidual_on_core {u : ℂ} (hAu : msA u = 0)
    {z : ℍ} (hz : z ∈ coreRectangle) :
    dyadicEigenResidual u z =
      msB u * (z.im : ℂ) ^ (1 / 2 - u) * (2 : ℂ) ^ u - dyadicReturnDefect u z := by
  have hy1 : 1 < z.im := by linarith [hz.2.1]
  have hy2 : z.im ≤ (1 : ℝ) * 2 := by linarith [hz.2.2]
  have he := heckeTruncated_eq Nat.prime_two u 1 z
  rw [heckeRemainder_eq_upperBand (by norm_num : 0 < (2 : ℕ)) u (by norm_num)
    hy1 hy2, upperBandRemainder_resonant (by norm_num : 0 < (2 : ℕ)) hAu] at he
  rw [dyadicEigenResidual, automorphicTruncation_eq_of_mem_fd u (by norm_num)
    (coreRectangle_subset_fd hz), dyadicReturnDefect]
  linear_combination he

private theorem core_radius_bounds {z : ℍ} (hz : z ∈ coreRectangle) :
    3 ≤ z.re ^ 2 + z.im ^ 2 ∧ z.re ^ 2 + z.im ^ 2 ≤ 4 := by
  have hx := abs_le.mp hz.1
  have hylo := hz.2.1
  have hyhi := hz.2.2
  have hx2 : z.re ^ 2 ≤ 1 / 16 := by nlinarith
  constructor <;> nlinarith [sq_nonneg z.re]

/-- Ratio of the two positive height scales entering the central return. -/
def returnRatio (z : ℍ) : ℝ := 4 / (z.re ^ 2 + z.im ^ 2)

private theorem returnRatio_pos (z : ℍ) : 0 < returnRatio z :=
  div_pos (by norm_num)
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos z.im_pos))

private theorem returnRatio_bounds {z : ℍ} (hz : z ∈ coreRectangle) :
    1 ≤ returnRatio z ∧ returnRatio z ≤ 4 / 3 := by
  have hr := core_radius_bounds hz
  have hd : 0 < z.re ^ 2 + z.im ^ 2 := by linarith [hr.1]
  constructor
  · rw [returnRatio, le_div_iff₀ hd]
    linarith [hr.2]
  · rw [returnRatio, div_le_iff₀ hd]
    linarith [hr.1]

private theorem returnRatio_height (z : ℍ) :
    (z.im / 2) * returnRatio z = returnHeight 0 z := by
  simp only [returnRatio, returnHeight, Int.cast_zero, add_zero]
  ring

/-- On the core rectangle the residual is the return term times an explicit scalar gap. -/
theorem dyadicEigenResidual_factor {u : ℂ} (hAu : msA u = 0)
    {z : ℍ} (hz : z ∈ coreRectangle) :
    dyadicEigenResidual u z = dyadicReturnDefect u z *
      (2 * (returnRatio z : ℂ) ^ (u - 1 / 2) - 1) := by
  let s : ℂ := 1 / 2 - u
  have hg : 0 < returnRatio z := returnRatio_pos z
  have hgC : (returnRatio z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg.ne'
  have hgp : (returnRatio z : ℂ) ^ s ≠ 0 := by
    intro h
    exact hgC ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hprod : (returnHeight 0 z : ℂ) ^ s =
      ((z.im / 2 : ℝ) : ℂ) ^ s * (returnRatio z : ℂ) ^ s := by
    have hm := Complex.mul_cpow_ofReal_nonneg (half_pos z.im_pos).le hg.le s
    simpa only [← Complex.ofReal_mul, returnRatio_height] using hm
  have hupp := weyl_scalar_identity (p := 2) (by norm_num) u false
  rw [weylExponent_false, sqrt_inv_mul_cpow_half_sub (by norm_num)] at hupp
  have hupp' : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2 * ((2 : ℂ) ^ s)⁻¹ = (2 : ℂ) ^ u := by
    change _ = _ at hupp
    linear_combination hupp
  rw [dyadicEigenResidual_on_core hAu hz, dyadicReturnDefect_on_core hAu hz]
  change msB u * (z.im : ℂ) ^ s * (2 : ℂ) ^ u -
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * msB u * (returnHeight 0 z : ℂ) ^ s = _
  rw [show u - 1 / 2 = -s by dsimp [s]; ring, Complex.cpow_neg,
    hprod, ofReal_div_natCast_cpow_eisensteinHeckeMaassSelberg 2 z.im_pos.le s]
  push_cast
  rw [← hupp']
  field_simp [hgp]
  <;> ring

private theorem return_scalar_norm_lower {u : ℂ} (hu : -1 / 2 < u.re)
    {z : ℍ} (hz : z ∈ coreRectangle) :
    3 / 2 ≤ ‖2 * (returnRatio z : ℂ) ^ (u - 1 / 2)‖ := by
  have hg := returnRatio_pos z
  have hgb := returnRatio_bounds hz
  have he : (u - 1 / 2 : ℂ).re = u.re - 1 / 2 := by simp
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hg, he]
  norm_num only [norm_ofNat]
  have hp : 1 ≤ returnRatio z ^ (u.re + 1 / 2) :=
    Real.one_le_rpow hgb.1 (by linarith)
  have hm : returnRatio z ^ (u.re - 1 / 2) * returnRatio z =
      returnRatio z ^ (u.re + 1 / 2) := by
    rw [← Real.rpow_one (returnRatio z), ← Real.rpow_add hg]
    congr 1
    ring
  have hn : 0 ≤ returnRatio z ^ (u.re - 1 / 2) := Real.rpow_nonneg hg.le _
  nlinarith only [hp, hm, mul_nonneg hn (sub_nonneg.mpr hgb.2)]

/-- The full automorphic Hecke residual has positive pointwise core mass at every frequency. -/
theorem dyadicEigenResidual_norm_sq_lower {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) {z : ℍ} (hz : z ∈ coreRectangle) :
    ‖msB u‖ ^ 2 / 8 ≤ ‖dyadicEigenResidual u z‖ ^ 2 := by
  have hg := return_scalar_norm_lower hu.1 hz
  have ht := norm_sub_norm_le (2 * (returnRatio z : ℂ) ^ (u - 1 / 2)) 1
  have hgap : 1 / 2 ≤ ‖2 * (returnRatio z : ℂ) ^ (u - 1 / 2) - 1‖ := by
    norm_num only [norm_one] at ht
    linarith
  have hnorm : ‖dyadicReturnDefect u z‖ / 2 ≤ ‖dyadicEigenResidual u z‖ := by
    rw [dyadicEigenResidual_factor hAu hz, norm_mul]
    nlinarith only [mul_nonneg (norm_nonneg (dyadicReturnDefect u z))
      (sub_nonneg.mpr hgap)]
  have hlow := dyadicReturnDefect_norm_sq_lower hur hAu hz
  nlinarith only [hlow, hnorm, norm_nonneg (dyadicReturnDefect u z),
    norm_nonneg (dyadicEigenResidual u z)]

private def residualRect : Set (ℝ × ℝ) :=
  Icc (-(1 / 4)) (1 / 4) ×ˢ Icc (7 / 4) (15 / 8)

private theorem residualRect_pos {p : ℝ × ℝ} (hp : p ∈ residualRect) : 0 < p.2 := by
  have := hp.2.1
  linarith

private def residualDensity (u : ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖msB u * (p.2 : ℂ) ^ (1 / 2 - u) * (2 : ℂ) ^ u -
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * msB u *
      ((2 * p.2 / (p.1 ^ 2 + p.2 ^ 2) : ℝ) : ℂ) ^ (1 / 2 - u)‖ ^ 2 / p.2 ^ 2

private theorem residualDensity_eq {u : ℂ} (hAu : msA u = 0) {p : ℝ × ℝ}
    (hp : p ∈ residualRect) :
    residualDensity u p = ‖dyadicEigenResidual u (ofComplex ⟨p.1, p.2⟩)‖ ^ 2 / p.2 ^ 2 := by
  let z : ℍ := ⟨⟨p.1, p.2⟩, residualRect_pos hp⟩
  have he : ofComplex (⟨p.1, p.2⟩ : ℂ) = z := by
    rw [ofComplex_apply_of_im_pos (residualRect_pos hp)]
  have hz : z ∈ coreRectangle := ⟨abs_le.mpr hp.1, hp.2⟩
  rw [he, dyadicEigenResidual_on_core hAu hz, dyadicReturnDefect_on_core hAu hz]
  simp [residualDensity, returnHeight, z]

private theorem residualDensity_continuousOn (u : ℂ) :
    ContinuousOn (residualDensity u) residualRect := by
  have hd (p : ℝ × ℝ) (hp : p ∈ residualRect) : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (residualRect_pos hp))
  have hb : ContinuousOn (fun p : ℝ × ℝ => 2 * p.2 / (p.1 ^ 2 + p.2 ^ 2)) residualRect :=
    (continuous_const.mul continuous_snd).continuousOn.div
      ((continuous_fst.pow 2).add (continuous_snd.pow 2)).continuousOn
      (fun p hp => (hd p hp).ne')
  have hy : ContinuousOn (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (1 / 2 - u)) residualRect :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn.cpow_const
      (fun p hp => Complex.ofReal_mem_slitPlane.mpr (residualRect_pos hp))
  have hh : ContinuousOn (fun p : ℝ × ℝ =>
      ((2 * p.2 / (p.1 ^ 2 + p.2 ^ 2) : ℝ) : ℂ) ^ (1 / 2 - u)) residualRect :=
    (Complex.continuous_ofReal.comp_continuousOn hb).cpow_const
      (fun p hp => Complex.ofReal_mem_slitPlane.mpr
        (div_pos (mul_pos (by norm_num) (residualRect_pos hp)) (hd p hp)))
  exact ((((continuousOn_const.mul hy).mul continuousOn_const).sub
    (continuousOn_const.mul hh)).norm.pow 2).div (continuous_snd.pow 2).continuousOn
      (fun p hp => (sq_pos_of_pos (residualRect_pos hp)).ne')

private theorem residualDensity_lower {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) {p : ℝ × ℝ} (hp : p ∈ residualRect) :
    ‖msB u‖ ^ 2 / 32 ≤ residualDensity u p := by
  let z : ℍ := ⟨⟨p.1, p.2⟩, residualRect_pos hp⟩
  have he : ofComplex (⟨p.1, p.2⟩ : ℂ) = z := by
    rw [ofComplex_apply_of_im_pos (residualRect_pos hp)]
  have hz : z ∈ coreRectangle := ⟨abs_le.mpr hp.1, hp.2⟩
  rw [residualDensity_eq hAu hp, he, le_div_iff₀ (sq_pos_of_pos (residualRect_pos hp))]
  have hy2 : p.2 ^ 2 ≤ 4 := by
    have hlo := hp.2.1
    have hhi := hp.2.2
    nlinarith only [hlo, hhi]
  have hlow := dyadicEigenResidual_norm_sq_lower hu hur hAu hz
  nlinarith only [hlow, mul_nonneg (sq_nonneg ‖msB u‖) (sub_nonneg.mpr hy2)]

/-- The full Hecke eigen-equation defect has uniformly positive compact-core mass. -/
theorem dyadicEigenResidual_core_mass_lower {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) :
    ‖msB u‖ ^ 2 / 512 ≤ ∫ z in coreRectangle, ‖dyadicEigenResidual u z‖ ^ 2 := by
  have hA : MeasurableSet residualRect := measurableSet_Icc.prod measurableSet_Icc
  have hK : IsCompact residualRect := isCompact_Icc.prod isCompact_Icc
  have hset : coreRectangle = {z : ℍ | (z.re, z.im) ∈ residualRect} := by
    ext z
    simp only [coreRectangle, residualRect, mem_setOf_eq, mem_prod, mem_Icc, abs_le, and_assoc]
  let F : ℝ × ℝ → ℝ := fun p => ‖dyadicEigenResidual u (ofComplex ⟨p.1, p.2⟩)‖ ^ 2
  have hF : (fun z : ℍ => F (z.re, z.im)) = fun z => ‖dyadicEigenResidual u z‖ ^ 2 := by
    funext z
    have he : (⟨z.re, z.im⟩ : ℂ) = (z : ℂ) := Complex.ext rfl rfl
    simp only [F, he, ofComplex_apply]
  rw [← hF, hset, setIntegral_coord_eq_real hA (fun p hp => residualRect_pos hp)]
  have heq : (∫ p in residualRect, F p / p.2 ^ 2) = ∫ p in residualRect, residualDensity u p :=
    setIntegral_congr_fun hA (fun p hp => (residualDensity_eq hAu hp).symm)
  rw [heq]
  have hm := setIntegral_mono_on
    (ContinuousOn.integrableOn_compact (μ := volume) hK
      (f := fun _ => ‖msB u‖ ^ 2 / 32) continuousOn_const)
    (ContinuousOn.integrableOn_compact (μ := volume) hK (residualDensity_continuousOn u)) hA
    (fun p hp => residualDensity_lower hu hur hAu hp)
  have hv : (volume : Measure (ℝ × ℝ)).real residualRect = 1 / 16 := by
    change ((volume : Measure (ℝ × ℝ))
      (Icc (-(1 / 4 : ℝ)) (1 / 4) ×ˢ Icc (7 / 4 : ℝ) (15 / 8))).toReal = 1 / 16
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    norm_num
  simpa only [setIntegral_const, hv, smul_eq_mul, show (1 / 16 : ℝ) *
    (‖msB u‖ ^ 2 / 32) = ‖msB u‖ ^ 2 / 512 by ring] using hm

/-- Fixed-height truncations remain a definite distance from Hecke eigenstates,
uniformly in frequency whenever the real parameter stays below zero. -/
theorem dyadicEigenResidual_relative_mass_lower {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hur : u.re < 0) (hAu : msA u = 0) :
    (-2 * u.re) / 512 * (∫ z in fd, ‖truncatedLineModel u 1 z‖ ^ 2) ≤
      ∫ z in coreRectangle, ‖dyadicEigenResidual u z‖ ^ 2 := by
  have he : (-2 * u.re) / 512 * (∫ z in fd, ‖truncatedLineModel u 1 z‖ ^ 2) =
      ‖msB u‖ ^ 2 / 512 := by
    rw [integral_norm_sq_of_msA_eq_zero hu hur hAu (by norm_num)]
    simp only [Real.one_rpow, mul_one]
    have hne : u.re ≠ 0 := hur.ne
    field_simp
  rw [he]
  exact dyadicEigenResidual_core_mass_lower hu hur hAu

#print axioms dyadicEigenResidual_factor
#print axioms dyadicEigenResidual_norm_sq_lower
#print axioms dyadicEigenResidual_core_mass_lower
#print axioms dyadicEigenResidual_relative_mass_lower

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
