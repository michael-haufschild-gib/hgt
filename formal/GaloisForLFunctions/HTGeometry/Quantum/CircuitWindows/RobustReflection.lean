import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw
import GaloisForLFunctions.HTGeometry.UniformProjectiveFixedErrorCircuitHardIntervalLaw

/-! # Spectral reflections remain hard at coarse operator accuracy -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Conjugation by a unitary preserves the diagonal norm, so every sign
coordinate witnesses the distance between the rephased reflections. -/
private theorem sign_coordinate_le {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) (x y : Fin d → Bool) (z : ℂ) (j : Fin (d+1)) :
    ‖anchoredBooleanPacket x j-z*anchoredBooleanPacket y j‖ ≤
      ‖anchoredSpectralBooleanReflection e V x-z • anchoredSpectralBooleanReflection e V y‖ := by
  let f (i : Fin n → Bool) := anchoredBooleanPacket x (e i)-z*anchoredBooleanPacket y (e i)
  have he : anchoredSpectralBooleanReflection e V x-z • anchoredSpectralBooleanReflection e V y =
      (V : Reg n)*Matrix.diagonal f*star (V : Reg n) := by
    have hdiag : Matrix.diagonal f =
        Matrix.diagonal (anchoredBooleanPacket x ∘ e)-z • Matrix.diagonal (anchoredBooleanPacket y ∘ e) := by
      ext i l
      by_cases h : i=l
      · subst l; simp [f]
      · simp [h]
    rw [hdiag,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul]
    rfl
  rw [he,l2_opNorm_unitary_conj_eq V.2,Matrix.l2_opNorm_diagonal]
  simpa only [f,Equiv.apply_symm_apply] using norm_le_pi_norm f (e.symm j)

/-- Two distinct anchored sign patterns contain both a matched sign and an
opposite sign. The parallelogram identity gives distance at least √2 after
arbitrary rephasing. -/
theorem spectral_reflection_sqrt_two_separation {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) {x y : Fin d → Bool} (hxy : x ≠ y)
    (z : ℂ) (hz : ‖z‖ = 1) :
    Real.sqrt 2 ≤ ‖anchoredSpectralBooleanReflection e V x-z • anchoredSpectralBooleanReflection e V y‖ := by
  let M := ‖anchoredSpectralBooleanReflection e V x-z • anchoredSpectralBooleanReflection e V y‖
  have ha : ‖(1:ℂ)-z‖ ≤ M := by
    simpa [anchoredBooleanPacket] using sign_coordinate_le e V x y z 0
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
  have hb : ‖(1:ℂ)+z‖ ≤ M := by
    have h := sign_coordinate_le e V x y z i.succ
    cases hx : x i <;> cases hy : y i <;> simp [hx,hy] at hi
    · simpa [anchoredBooleanPacket,hx,hy] using h
    · have h' : ‖(-1:ℂ)-z‖ ≤ M := by simpa [anchoredBooleanPacket,hx,hy] using h
      simpa only [show (-1:ℂ)-z = -(1+z) by ring,norm_neg] using h'
  have hpar := parallelogram_law_with_norm ℂ (1:ℂ) z
  rw [hz,norm_one] at hpar
  apply Real.sqrt_le_iff.mpr
  refine ⟨norm_nonneg _,?_⟩
  linarith only [hpar,pow_le_pow_left₀ (norm_nonneg _) ha 2,pow_le_pow_left₀ (norm_nonneg _) hb 2]

/-- A net of radius one quarter with fewer points than anchored sign patterns
leaves some reflection farther than 11/25 from the entire circuit budget. -/
theorem exists_coarsely_separated_spectral_reflection {n d s : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hent : atMostQuarterCircuitEntropyBound n s < ((2^d:ℕ):ℝ)) :
    ∃ x : Fin d → Bool, ProjectiveCircuitSeparated n (11/25:ℝ) s
      (anchoredSpectralBooleanReflection e V x) := by
  classical
  let net := atMostQuarterCircuitNet n s
  let F : Finset (Reg n) := net.image Subtype.val
  have hcard : F.card < Fintype.card (Fin d → Bool) := by
    have hreal := (atMostQuarterCircuitNet_card_real_le n s).trans_lt hent
    have hnat : net.card < 2^d := by exact_mod_cast hreal
    simpa [F,Finset.card_image_of_injective _ Subtype.val_injective] using hnat
  obtain ⟨x,hx⟩ := exists_projectively_far_from_small_net (anchoredSpectralBooleanReflection e V)
    (Real.sqrt 2) (69/100) (fun h z hz => spectral_reflection_sqrt_two_separation e V h z hz)
    (by rw [Real.lt_sqrt (by norm_num)]; norm_num) F hcard
  refine ⟨x,?_⟩
  intro z hz C hC
  obtain ⟨W,hW,he⟩ := atMostQuarterCircuitNet_cover C hC
  have hfar := hx W (Finset.mem_image.mpr ⟨W,hW,rfl⟩) z hz
  have hclose : ‖z • (C.eval : Reg n)-z • (W : Reg n)‖ ≤ 1/4 := by
    rw [← smul_sub,norm_smul,hz,one_mul]
    simpa only [dist_eq_norm] using he
  linarith only [hfar,hclose,norm_sub_le_norm_sub_add_norm_sub (anchoredSpectralBooleanReflection e V x)
    (z • (C.eval : Reg n)) (z • (W : Reg n))]

#print axioms exists_coarsely_separated_spectral_reflection
end
end GaloisForLFunctions.HTGeometry
