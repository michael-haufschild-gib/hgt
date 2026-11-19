import GaloisForLFunctions.TransThresholdPairCorrelation.TotientGridFormFactor
import Mathlib.Analysis.Fourier.ZMod

/-!
# One positive sampler for every short period

The sinc-square law of width K on the integers has exactly uniform image
modulo every positive k at most K. Its Fourier transform on each such
quotient vanishes on all nontrivial characters, including at the edge
k = K. Translating the sampler leaves these uniform images unchanged.
-/

open Finset Filter Real GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.TransThresholdPairCorrelation
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

noncomputable section

private theorem distance_from_integers {k : ℕ} [NeZero k] {j : ZMod k} (hj : j ≠ 0) (n : ℤ) :
    1/(k : ℝ) ≤ |(j.val : ℝ)/k + n| := by
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hne : (j.val : ℤ) + n*k ≠ 0 := by
    intro he
    have hm := congrArg (fun t : ℤ => (t : ZMod k)) he
    exact hj (by simpa using hm)
  have hab : (1 : ℤ) ≤ |(j.val : ℤ)+n*k| := by
    have hp := abs_pos.mpr hne
    omega
  rw [show (j.val : ℝ)/k+n = ((j.val : ℝ)+n*k)/k by field_simp, abs_div, abs_of_pos hk,
    div_le_div_iff_of_pos_right hk]
  exact_mod_cast hab

private theorem char_sum {K k : ℕ} [NeZero k] (hk : k ≤ K) (j : ZMod k) :
    HasSum (fun z : ℤ => (gridSincWeight K z : ℂ) * ZMod.stdAddChar (j*(z : ZMod k)))
      (if j = 0 then 1 else 0) := by
  have hk0 := Nat.pos_of_ne_zero (NeZero.ne k)
  have hK := hk0.trans_le hk
  have hW := summable_gridSincWeight hK
  by_cases hj : j = 0
  · subst j
    simpa only [zero_mul,AddChar.map_zero_eq_one,mul_one,if_true,Complex.ofReal_one] using
      (Complex.hasSum_ofReal.mpr (hW.hasSum_iff.mpr (tsum_gridSincWeight hK)))
  rw [if_neg hj]
  have ha : 0 < 1/(K:ℝ) := by positivity
  have hz := tsum_sinc_sq_mul_fourier_eq_zero ha
    (fun n => (one_div_le_one_div_of_le (by exact_mod_cast hk0) (by exact_mod_cast hk)).trans
      (distance_from_integers hj n))
  have he (z : ℤ) : ZMod.stdAddChar (j*(z : ZMod k)) =
      (fourier z (((j.val : ℝ)/k : ℝ) : UnitAddCircle) : ℂ) := by
    have hc : j*(z : ZMod k) = (((j.val : ℤ)*z : ℤ) : ZMod k) := by push_cast; simp
    rw [hc,ZMod.stdAddChar_coe,fourier_coe_apply]
    push_cast
    congr 1
    ring
  have hnorm (z : ℤ) : ‖ZMod.stdAddChar (j*(z : ZMod k))‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  apply (hW.of_norm_bounded (fun z => by
    rw [norm_mul,hnorm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (gridSincWeight_nonneg K z)])).hasSum_iff.mpr
  simp only [mul_assoc] at hz
  simp only [he,gridSincWeight,Complex.ofReal_mul,mul_assoc,tsum_mul_left,hz,mul_zero]

private theorem uniform_complex {K k : ℕ} [NeZero k] (hk : k ≤ K) (f : ZMod k → ℂ) :
    HasSum (fun z : ℤ => (gridSincWeight K z : ℂ)*f (z : ZMod k))
      ((k : ℂ)⁻¹ * ∑ j, f j) := by
  let F := ZMod.dft f
  have hf (x : ZMod k) : f x = (k : ℂ)⁻¹ * ∑ j : ZMod k, ZMod.stdAddChar (j*x)*F j := by
    have h := ZMod.invDFT_apply F x
    simpa only [F,LinearEquiv.symm_apply_apply,smul_eq_mul] using h
  have h := (hasSum_sum (s := (univ : Finset (ZMod k))) fun j _ => (char_sum hk j).mul_right (F j)).mul_left
    ((k : ℂ)⁻¹)
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',mem_univ,if_true,F,ZMod.dft_apply_zero] at h
  apply h.congr_fun
  intro z
  rw [hf (z : ZMod k)]
  change _ = (k : ℂ)⁻¹ * _
  rw [mul_left_comm,Finset.mul_sum]
  apply congrArg ((k : ℂ)⁻¹ * ·)
  exact sum_congr rfl fun _ _ => by ring

/-- All short residue classes are sampled with Haar probability by a single sinc-square law. -/
theorem hasSum_gridSinc_periodic_mean {K k : ℕ} [NeZero k] (hk : k ≤ K)
    (f : ZMod k → ℝ) (s : ℤ) :
    HasSum (fun z : ℤ => gridSincWeight K (z-s)*f (z : ZMod k)) ((∑ j, f j)/(k : ℝ)) := by
  let g (j : ZMod k) := f (j+(s : ZMod k))
  have h := uniform_complex hk (fun j => (g j : ℂ))
  have he : ∑ j, g j = ∑ j, f j := Equiv.sum_comp (Equiv.addRight (s : ZMod k)) f
  have hr : HasSum (fun z : ℤ => gridSincWeight K z * g (z : ZMod k)) ((∑ j, g j)/(k : ℝ)) := by
    apply Complex.hasSum_ofReal.mp
    simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_natCast,
      div_eq_inv_mul,Complex.ofReal_inv,Complex.ofReal_natCast] using h
  rw [he] at hr
  apply (Equiv.addRight s).hasSum_iff.mp
  change HasSum (fun z : ℤ => gridSincWeight K ((z+s)-s) * f ((z+s : ℤ) : ZMod k)) _
  simpa only [add_sub_cancel_right,Int.cast_add,g] using hr

/-- The sampler cannot exceed its peak 1/K. -/
theorem gridSincWeight_le_peak {K : ℕ} (hK : 0 < K) (z : ℤ) : gridSincWeight K z ≤ 1/(K:ℝ) := by
  apply mul_le_of_le_one_right (by positivity)
  rw [← sq_abs]
  exact pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _)

/-- Its inverse-square tail has the same power as the pronic excess of an integer floor row. -/
theorem gridSincWeight_mul_sq_le {K : ℕ} (hK : 0 < K) (z : ℤ) :
    gridSincWeight K z * (z : ℝ)^2 ≤ K := by
  by_cases hz : z = 0
  · simp [hz]
  have hx : Real.pi*(1/(K:ℝ))*(z:ℝ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero Real.pi_ne_zero (by positivity)) (Int.cast_ne_zero.mpr hz)
  rw [gridSincWeight, Real.sinc_of_ne_zero hx]
  have he : 1/(K:ℝ)*(Real.sin (Real.pi*(1/(K:ℝ))*z)/(Real.pi*(1/K)*z))^2*(z:ℝ)^2 =
      (K:ℝ)*(Real.sin (Real.pi*(1/(K:ℝ))*z))^2/Real.pi^2 := by
    field_simp [Real.pi_ne_zero,show (z:ℝ) ≠ 0 from Int.cast_ne_zero.mpr hz]
  rw [he,div_le_iff₀ (sq_pos_of_pos Real.pi_pos)]
  exact mul_le_mul_of_nonneg_left ((Real.sin_sq_le_one _).trans (by nlinarith only [Real.pi_gt_three])) (Nat.cast_nonneg _)

#print axioms hasSum_gridSinc_periodic_mean
#print axioms gridSincWeight_mul_sq_le

end

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
