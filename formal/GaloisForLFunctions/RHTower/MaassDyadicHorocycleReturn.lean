import GaloisForLFunctions.RHTower.MaassCuspAutomorphicCorrespondence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic horocycle returns of Maass forms

For `q = 4 * 2^n`, the points `z/q^2 + (q/2+1)/q` approach the real boundary.
An explicit integral modular transformation sends them to points converging to
`z/4-1/2`. Consequently a nonzero level-one Maass form need not decay along
these points: for a suitable fixed `z`, its values converge to a nonzero value.

The samples occur among the residues at denominator `q^2`. This prevents a
uniform termwise inverse-`q` bound, not cancellation in their arithmetic sum.
No bound or counterexample for a normalized Hecke eigenvalue follows.
-/

open Complex UpperHalfPlane Filter Topology Matrix
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.MaassDyadicHorocycleReturn

/-- An integral return matrix for the residue `2*k+1` at denominator `4*k`. -/
def returnMatrix (k : ℕ) : SL2Z :=
  ⟨!![1 - 2 * (k : ℤ), (k : ℤ); -2, 1], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring⟩

/-- A rational horocycle sample with height proportional to `1/(4*k)^2`. -/
noncomputable def point (k : ℕ) (hk : 0 < k) (z : ℍ) : ℍ :=
  ⟨(z : ℂ) / (((4 * (k : ℝ)) ^ 2 : ℝ) : ℂ) +
      (((2 * (k : ℝ) + 1) / (4 * k) : ℝ) : ℂ), by
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.div_ofReal_im]
    exact div_pos z.im_pos (sq_pos_of_pos (by positivity))⟩

/-- The interior point approached after modular return. -/
noncomputable def interior (z : ℍ) : ℍ :=
  ⟨(z : ℂ) / 4 - 1 / 2, by simpa using div_pos z.im_pos (by norm_num : (0 : ℝ) < 4)⟩

theorem return_formula (k : ℕ) (hk : 0 < k) (z : ℍ) :
    ((integralSL2ToReal (returnMatrix k) • point k hk z : ℍ) : ℂ) =
      (z : ℂ) / 4 / (1 + (z : ℂ) / (4 * (k : ℂ))) - 1 / 2 := by
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hz : 4 * (k : ℂ) + z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    have hpos := z.im_pos
    simp at hi
    linarith
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [integralSL2ToReal, Matrix.SpecialLinearGroup.map_apply_coe,
    returnMatrix, RingHom.mapMatrix_apply, Matrix.map_apply]
  dsimp [point]
  push_cast
  field_simp
  rw [show -(2 * ((z : ℂ) + (k : ℂ) * 4 * (2 * k + 1))) + (k : ℂ) ^ 2 * 4 ^ 2 =
    -2 * ((k : ℂ) * 4 + z) by ring]
  have hz' : (k : ℂ) * 4 + z ≠ 0 := by simpa [mul_comm] using hz
  field_simp [hz']
  ring

theorem dyadic_return_tendsto (z : ℍ) :
    Tendsto (fun n : ℕ => integralSL2ToReal (returnMatrix (2 ^ n)) •
      point (2 ^ n) (pow_pos (by norm_num) n) z) atTop (𝓝 (interior z)) := by
  apply UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff.mpr
  have hi : Tendsto (fun n : ℕ => ((4 * (2 : ℝ) ^ n)⁻¹ : ℝ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 4))
  have hiC := Filter.tendsto_ofReal_iff.mpr hi
  have hden : Tendsto (fun n : ℕ => (1 : ℂ) + (z : ℂ) *
      (((4 * (2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hiC)
  have h := ((tendsto_const_nhds (x := (z : ℂ) / 4)).div hden
    (by norm_num : (1 : ℂ) ≠ 0)).sub
    (tendsto_const_nhds (x := (1 / 2 : ℂ)))
  simpa only [Pi.div_apply, Pi.sub_apply, Function.comp_def, return_formula, interior, div_eq_mul_inv,
    Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Nat.cast_pow, Nat.cast_ofNat, inv_one, mul_one] using h

/-- Maass values converge to the value at the interior return point. -/
theorem maass_values_tendsto {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma 1)) lam) (z : ℍ) :
    Tendsto (fun n : ℕ => f.1.1 (point (2 ^ n) (pow_pos (by norm_num) n) z))
      atTop (𝓝 (f.1.1 (interior z))) := by
  have hf : Continuous f.1.1 := by
    apply continuous_iff_continuousAt.mpr
    intro w
    have h := (f.2.2.1.1.continuousOn.continuousAt
      (isOpen_upperHalfPlaneSet.mem_nhds w.im_pos)).comp
      UpperHalfPlane.continuous_coe.continuousAt
    simpa only [Function.comp_def, ofComplex_apply] using h
  have hinv (n : ℕ) : f.1.1 (integralSL2ToReal (returnMatrix (2 ^ n)) •
      point (2 ^ n) (pow_pos (by norm_num) n) z) =
      f.1.1 (point (2 ^ n) (pow_pos (by norm_num) n) z) := by
    exact f.1.2 ⟨_, ⟨returnMatrix (2 ^ n), CongruenceSubgroup.mem_Gamma_one _, rfl⟩⟩ _
  exact (hf.continuousAt.tendsto.comp (dyadic_return_tendsto z)).congr hinv

/-- No uniform inverse-scale bound holds on this dyadic residue sequence. -/
theorem exists_maass_scaled_values_unbounded {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma 1)) lam) :
    ∃ z : ℍ, ¬ ∃ C : ℝ, ∀ n : ℕ, 4 * (2 : ℝ) ^ n *
      ‖f.1.1 (point (2 ^ n) (pow_pos (by norm_num) n) z)‖ ≤ C := by
  classical
  have hw : ∃ w : ℍ, f.1.1 w ≠ 0 := by
    by_contra h
    apply f.2.1
    apply Subtype.ext
    funext w
    simpa using not_exists.mp h w
  obtain ⟨w, hw⟩ := hw
  let z : ℍ := ⟨4 * (w : ℂ) + 2, by simpa using mul_pos (by norm_num : (0 : ℝ) < 4) w.im_pos⟩
  have hz : interior z = w := by
    apply UpperHalfPlane.ext
    dsimp [interior, z]
    ring
  refine ⟨z, ?_⟩
  rintro ⟨C, hC⟩
  have hpos : 0 < ‖f.1.1 w‖ := norm_pos_iff.mpr hw
  have hlim := (maass_values_tendsto f z).norm
  rw [hz] at hlim
  have hlow : ∀ᶠ n : ℕ in atTop, ‖f.1.1 w‖ / 2 <
      ‖f.1.1 (point (2 ^ n) (pow_pos (by norm_num) n) z)‖ :=
    hlim.eventually (lt_mem_nhds (half_lt_self hpos))
  have hpow : Tendsto (fun n : ℕ => 4 * (2 : ℝ) ^ n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop
      (by norm_num)
  have hlarge := hpow.eventually (eventually_gt_atTop (C / (‖f.1.1 w‖ / 2)))
  obtain ⟨n, hn, hlarge⟩ := (hlow.and hlarge).exists
  have hsmall := mul_lt_mul_of_pos_left hn (by positivity : (0 : ℝ) < 4 * 2 ^ n)
  have hlarge' := (div_lt_iff₀ (half_pos hpos)).mp hlarge
  have := hC n
  linarith

/-- The return point is literally a residue sample in the denominator-square Hecke branch. -/
theorem point_eq_hecke_sample (k : ℕ) (hk : 0 < k) (z : ℍ) :
    (point k hk z : ℂ) =
      ((z : ℂ) + ((2 * k + 1) * (4 * k) : ℕ)) / ((4 * k) ^ 2 : ℕ) := by
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  dsimp [point]
  push_cast
  field_simp

theorem sample_residue_lt (k : ℕ) (hk : 0 < k) :
    (2 * k + 1) * (4 * k) < (4 * k) ^ 2 := by
  have : 2 * k + 1 < 4 * k := by omega
  simpa only [pow_two] using Nat.mul_lt_mul_of_pos_right this (by omega : 0 < 4 * k)

theorem dyadic_sample_denominator (n : ℕ) : (4 * 2 ^ n) ^ 2 = 2 ^ (2 * n + 4) := by
  rw [pow_add, Nat.mul_comm 2 n, pow_mul, mul_pow]
  ring

end GaloisForLFunctions.RHTower.MaassDyadicHorocycleReturn
