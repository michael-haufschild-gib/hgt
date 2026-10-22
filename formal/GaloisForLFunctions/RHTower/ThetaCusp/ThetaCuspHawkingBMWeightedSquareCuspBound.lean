import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalAngularForcing

/-! The complete square remainder can be paired with any literal scalar cusp leg. -/
namespace RHTower.D4BMGlobalAngularResponse
open Complex Set
noncomputable section
set_option autoImplicit false

private theorem weighted_principal_mul_bound (u w : ℂ) (l : ℝ) (hl : 0 < l)
    (f : (Fin 2 → ℝ) → ℂ)
    (h : ∀ v : ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 → ‖(z 1:ℂ)^v*f z‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 → ‖(z 1:ℂ)^w*principal u z*f z‖ ≤ C := by
  obtain ⟨Cm,hCm,hm⟩ := h (w+d4BMCompletedEisensteinCuspWeylExponent u false)
  obtain ⟨Cp,hCp,hp⟩ := h (w+d4BMCompletedEisensteinCuspWeylExponent u true)
  let A := d4BMCompletedEisensteinCuspConstantCoefficient u false
  let D := d4BMCompletedEisensteinCuspConstantCoefficient u true
  refine ⟨‖A‖*Cm+‖D‖*Cp,by positivity,?_⟩
  intro z hz
  have hn : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hl.trans_le hz).ne'
  have he : (z 1:ℂ)^w*principal u z*f z =
      A*((z 1:ℂ)^(w+d4BMCompletedEisensteinCuspWeylExponent u false)*f z)+
      D*((z 1:ℂ)^(w+d4BMCompletedEisensteinCuspWeylExponent u true)*f z) := by
    rw [Complex.cpow_add _ _ hn,Complex.cpow_add _ _ hn]
    dsimp [principal,d4BMCompletedEisensteinCuspConstantPart,
      d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantMaassFactor,A,D]
    ring
  rw [he]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by rw [norm_mul A,norm_mul D]; gcongr; exacts [hm z hz,hp z hz]

/-- Every complex height weight preserves boundedness of the full square remainder. -/
theorem weighted_squareRemainder_bounded (u w : ℂ) (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 → ‖(z 1:ℂ)^w*squareRemainder u z‖ ≤ C := by
  obtain ⟨Cm,hCm,hm⟩ := weighted_principal_mul_bound u w l hl (tail u)
    (fun v => weighted_tail_bounded u v l hl)
  obtain ⟨Ct,hCt,ht⟩ := weighted_tail_bounded u w l hl
  obtain ⟨C0,hC0,h0⟩ := weighted_tail_bounded u 0 l hl
  refine ⟨2*Cm+Ct*C0,by positivity,?_⟩
  intro z hz
  have htail : ‖tail u z‖ ≤ C0 := by simpa only [Complex.cpow_zero,one_mul] using h0 z hz
  have he : (z 1:ℂ)^w*squareRemainder u z =
      2*((z 1:ℂ)^w*principal u z*tail u z)+((z 1:ℂ)^w*tail u z)*tail u z := by
    rw [squareRemainder_eq]
    ring
  rw [he]
  calc
    _ ≤ ‖2*((z 1:ℂ)^w*principal u z*tail u z)‖+‖((z 1:ℂ)^w*tail u z)*tail u z‖ := norm_add_le _ _
    _ = 2*‖(z 1:ℂ)^w*principal u z*tail u z‖+‖(z 1:ℂ)^w*tail u z‖*‖tail u z‖ := by
      simp only [norm_mul,Complex.norm_ofNat]
    _ ≤ _ := by gcongr; exacts [hm z hz,ht z hz]

/-- The actual full scalar field times the full square remainder is uniformly cusp bounded. -/
theorem scalar_squareRemainder_bounded (v u : ℂ) (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 → ‖scalar v z*squareRemainder u z‖ ≤ C := by
  obtain ⟨Cp,hCp,hp⟩ := weighted_principal_mul_bound v 0 l hl (squareRemainder u)
    (fun w => weighted_squareRemainder_bounded u w l hl)
  obtain ⟨Ct,hCt,ht⟩ := weighted_tail_bounded v 0 l hl
  obtain ⟨Cr,hCr,hr⟩ := squareRemainder_bounded u l hl
  refine ⟨Cp+Ct*Cr,by positivity,?_⟩
  intro z hz
  have hprincipal : ‖principal v z*squareRemainder u z‖ ≤ Cp := by
    simpa only [Complex.cpow_zero,one_mul] using hp z hz
  have htail : ‖tail v z‖ ≤ Ct := by simpa only [Complex.cpow_zero,one_mul] using ht z hz
  have he : scalar v z=principal v z+tail v z := rfl
  rw [he,add_mul]
  calc
    _ ≤ ‖principal v z*squareRemainder u z‖+‖tail v z*squareRemainder u z‖ := norm_add_le _ _
    _ = ‖principal v z*squareRemainder u z‖+‖tail v z‖*‖squareRemainder u z‖ := by
      rw [norm_mul (tail v z)]
    _ ≤ Cp+Ct*Cr := add_le_add hprincipal
      (mul_le_mul htail (hr z hz) (norm_nonneg _) hCt)

end
end RHTower.D4BMGlobalAngularResponse
