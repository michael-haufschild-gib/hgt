import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.DensityWitnesses.Polar.UnitaryBasis
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.Rounding.ColumnTests
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.MarkedMass
import GaloisForLFunctions.HTGeometry.CalibrationSpectrumMechanics

/-! # Convex feasibility for approximation by a spectral phase below √2 -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.DensityWitnesses.Polar
open StaticLocalLaboratoryComplexityGrowthLaw MarkedReflections.Rounding
open private diagonal_sum from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.MarkedMass
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
local instance : CStarAlgebra (Mat I) where

private theorem compressed_modulus (V : unitaryGroup I ℂ) (i : I) (d : I → ℂ) (hd : ∀ j, ‖d j‖≤1) :
    ∃ r∈Set.Icc (0:ℝ) 1, (star V.val*diagonal (fun j => (‖d j‖:ℂ))*V.val) i i=(r:ℂ) := by
  let w (j : I) := ‖(V⁻¹).val i j‖^2
  have h := diagonal_sum V⁻¹ (fun _ => 1) i
  simp only [diagonal_one,mul_one,(Unitary.mem_iff.mp (V⁻¹).property).2,one_apply_eq] at h
  have hw : ∑ j, w j=1 := by
    simpa only [Complex.re_sum,Complex.ofReal_re,Complex.one_re] using congrArg Complex.re h.symm
  let r := ∑ j, w j*‖d j‖
  have hr : r≤1 := by
    rw [←hw]
    exact sum_le_sum fun j _ => mul_le_of_le_one_right (sq_nonneg _) (hd j)
  refine ⟨r,⟨sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (norm_nonneg _)),hr⟩,?_⟩
  have he := diagonal_sum V⁻¹ (fun j => (‖d j‖:ℂ)) i
  change (star V.val*_*star (star V.val)) i i=_ at he
  rw [star_star] at he
  simpa only [r,w,Complex.ofReal_sum,Complex.ofReal_mul] using he

/-- If a diagonal contraction gives a positive overlap in every unit
direction, its coordinatewise polar phases attain at least that overlap
in the least favorable direction. -/
theorem polar_error (W : unitaryGroup I ℂ) (d : I → ℂ) (hd : ∀ i, ‖d i‖≤1)
    {e : ℝ} (he : 0≤e) (he' : e^2<2)
    (ht : ∀ V : unitaryGroup I ℂ, ∀ i, 1-e^2/2≤reading V i (star W.val*diagonal d)) :
    ‖diagonal (fun i => coherentUnitPhase (d i))-W.val‖≤e := by
  let S : unitaryGroup I ℂ := ⟨diagonal (fun i => coherentUnitPhase (d i)),
    mem_unitaryGroup_diagonal_general _ (fun i => norm_coherentUnitPhase _)⟩
  let P := diagonal (fun j => (‖d j‖:ℂ))
  let U := W⁻¹*S
  obtain ⟨V,p,hp,hV⟩ := unitary_phase_basis U
  have hsplit : U.val*P=star W.val*diagonal d := by
    change (star W.val*diagonal _)*diagonal _=_
    rw [mul_assoc,diagonal_mul_diagonal]
    congr 2
    funext i
    exact (mul_comm ..).trans (norm_mul_coherentUnitPhase _)
  have hrow : star V.val*U.val=diagonal p*star V.val := by
    rw [←hV,mul_assoc,(Unitary.mem_iff.mp V.property).2,mul_one]
  have hbound (i : I) : ‖p i-1‖≤e := by
    obtain ⟨r,hr,hread⟩ := compressed_modulus V i d hd
    have hx := ht V i
    rw [←hsplit] at hx
    change 1-e^2/2≤((star V.val*(U.val*P)*V.val) i i).re at hx
    rw [←mul_assoc (star V.val) U.val,hrow,mul_assoc (diagonal p),mul_assoc (diagonal p),
      diagonal_mul,show (star V.val*P*V.val) i i=(r:ℂ) from hread,Complex.mul_re] at hx
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at hx
    have hpos : 0≤(p i).re := by
      by_contra! hn
      have hneg := mul_nonpos_of_nonpos_of_nonneg hn.le hr.1
      linarith only [hx,hneg,he']
    have hle := mul_le_of_le_one_right hpos hr.2
    apply (sq_le_sq₀ (norm_nonneg _) he).mp
    rw [Complex.sq_norm,Complex.normSq_sub,←Complex.sq_norm,hp,Complex.normSq_one]
    simp only [Complex.conj_one,mul_one,one_pow]
    linarith only [hx,hle]
  have hnorm : ‖S.val-W.val‖=‖diagonal (fun i => p i-1)‖ := by
    calc _ = ‖star W.val*(S.val-W.val)‖ := (CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem W.property)).symm
         _ = ‖U.val-1‖ := by rw [mul_sub,(Unitary.mem_iff.mp W.property).1]; rfl
         _ = ‖star V.val*(U.val-1)*V.val‖ :=
           (by simpa only [star_star] using l2_opNorm_unitary_conj_eq (Unitary.star_mem V.property) (U.val-1)).symm
         _ = _ := by rw [mul_sub,mul_one,sub_mul,hV,(Unitary.mem_iff.mp V.property).1,←diagonal_one,diagonal_sub]; rfl
  change ‖S.val-W.val‖≤e
  rw [hnorm,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg he).mpr hbound

/-- At positive overlap, unit-modulus phase feasibility is exactly the
intersection of the closed unit polydisk with real linear inequalities. -/
theorem phase_fit_iff_contraction (W : unitaryGroup I ℂ) {e : ℝ} (he : 0≤e) (hs : e^2<2) :
    (∃ f : I → ℂ, (∀ i, ‖f i‖=1) ∧ ‖diagonal f-W.val‖≤e) ↔
      ∃ d : I → ℂ, (∀ i, ‖d i‖≤1) ∧
        ∀ V : unitaryGroup I ℂ, ∀ i, 1-e^2/2≤reading V i (star W.val*diagonal d) := by
  constructor
  · rintro ⟨f,hf,hh⟩
    refine ⟨f,fun i => (hf i).le,fun V i => ?_⟩
    have hm := column_error V i W.val (diagonal f) W.property (mem_unitaryGroup_diagonal_general f hf)
    have hb := (sq_le_sq₀ (norm_nonneg _) he).mpr hh
    linarith only [hm,hb]
  · rintro ⟨d,hd,h⟩
    exact ⟨_,fun _ => norm_coherentUnitPhase _,polar_error W d hd he hs h⟩

#print axioms phase_fit_iff_contraction
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.DensityWitnesses.Polar
