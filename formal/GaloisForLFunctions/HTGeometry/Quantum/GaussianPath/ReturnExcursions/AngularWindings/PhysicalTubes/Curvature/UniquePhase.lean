import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.UnitaryMidpoint
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! # Rotation away from a single active spectral chord -/

open Complex Filter Set Matrix
open scoped Topology ComplexConjugate Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
noncomputable section

private theorem chord_sq (a b : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) :
    ‖a-b‖^2=2-2*(a*conj b).re := by
  rw [Complex.sq_norm,Complex.normSq_sub]
  simp only [Complex.normSq_eq_norm_sq,ha,hb,one_pow]
  ring

/-- A positive worst chord below the semicircle threshold can be reduced by
rotating the common phase whenever just one spectral point attains it. -/
theorem rotate_unique_phase (S : Set ℂ) (hS : S.Finite) {z : ℂ} {ε : ℝ}
    (hz : ‖z‖=1) (he : 0<ε) (hcut : ε^2<2) (hd : ‖1-z‖=ε)
    (hgap : ∀ w∈S, w≠z → ‖1-w‖<ε) : ∃ c : ℂ, ‖c‖=1 ∧ ∀ w∈S, ‖c-w‖<ε := by
  let a (t : ℝ) : ℂ := ((1-t:ℝ):ℂ)+(t:ℂ)*z
  let U (t : ℝ) : ℂ := ((‖a t‖⁻¹:ℝ):ℂ)*a t
  have ha₀ : a 0=1 := by simp [a]
  have hU₀ : U 0=1 := by simp [U,ha₀]
  have ha : Continuous a := by unfold a; fun_prop
  have hU : ContinuousAt U 0 := by
    exact (Complex.continuous_ofReal.continuousAt.comp
      (ha.norm.continuousAt.inv₀ (by simp [ha₀]))).mul ha.continuousAt
  have hh : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ w∈S \ {z}, ‖U t-w‖<ε := by
    apply (Filter.eventually_all_finite (hS.diff _)).mpr
    intro w hw
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    apply (hU.sub continuousAt_const).norm.eventually_lt continuousAt_const
    rw [hU₀]
    exact hgap w hw.1 hw.2
  have hpos : ∀ᶠ t in 𝓝[>] (0:ℝ), 0<t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t<1 :=
    (gt_mem_nhds (by norm_num : (1:ℝ)>0)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,ht,ht',hrest⟩ := (hpos.and (hsmall.and hh)).exists
  have hsq := chord_sq 1 z norm_one hz
  rw [hd,one_mul,Complex.conj_re] at hsq
  have hreal : 0<z.re := by linarith only [hcut,hsq]
  have hless : z.re<1 := by linarith only [hsq,sq_pos_of_pos he]
  have hconv : ‖a t‖≤1 := by
    apply (norm_add_le ..).trans
    rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg ht.le,
      Real.norm_of_nonneg (sub_nonneg.mpr ht'.le),hz,mul_one]
    ring_nf
  have hprod : (a t*conj z).re=(1-t)*z.re+t := by
    simp only [a,add_mul,mul_assoc,Complex.mul_conj,Complex.normSq_eq_norm_sq,hz,one_pow,
      Complex.ofReal_one,mul_one,Complex.add_re,Complex.mul_re,Complex.conj_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
  have himprove : z.re<(a t*conj z).re := by
    rw [hprod]
    linarith only [mul_pos ht (sub_pos.mpr hless)]
  have hn : 0<‖a t‖ := by
    apply norm_pos_iff.mpr
    intro h
    rw [h,zero_mul,Complex.zero_re] at himprove
    exact (hreal.trans himprove).false
  have hnorm : ‖U t‖=1 := by
    rw [show U t=((‖a t‖⁻¹:ℝ):ℂ)*a t from rfl,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
  refine ⟨U t,hnorm,fun w hw => ?_⟩
  by_cases hwz : w=z
  · subst w
    apply (sq_lt_sq₀ (norm_nonneg _) he.le).mp
    rw [chord_sq _ _ hnorm hz,hsq]
    have hmul : z.re*‖a t‖<(a t*conj z).re :=
      (mul_le_of_le_one_right hreal.le hconv).trans_lt himprove
    have hh := (lt_div_iff₀ hn).mpr hmul
    rw [show (U t*conj z).re=(a t*conj z).re/‖a t‖ by
      dsimp only [U]
      rw [mul_assoc,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,div_eq_inv_mul]]
    linarith only [hh]
  · exact hrest w ⟨hw,hwz⟩

#print axioms rotate_unique_phase
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
