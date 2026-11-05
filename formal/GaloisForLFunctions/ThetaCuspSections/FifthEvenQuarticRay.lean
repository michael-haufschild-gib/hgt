import GaloisForLFunctions.ThetaCuspSections.FifthEvenQuarticRayModel

/-!
# The complete native fifth section pays a quartic cross-load

The retained-pair reserve dominates the complete normalized theta source.
The inverse Gaussian congruence transfers this strict inequality to the
native fifth even matrix for reflection scale at least seven.
-/

noncomputable section
open Matrix
namespace GaloisForLFunctions.ThetaCuspSections.QuarticRayCertificate
open FifthLeadingPair EightCrossData EvenFiveEndpoint

open _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit
open FifthNativeRay FifthRemainder

/-- The quartic reserve includes every theta atom and the complete remainder. -/
private theorem normalized_reserve_posDef {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (sourceGram x-(3/20*(thetaCuspSingleAtomReflectionScale 1 x)^4) •
      loadGram (thetaCuspSingleAtomReflectionScale 1 x)).PosDef := by
  have hq5 : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  have hp := model_quartic_reserve_from_seven_posDef hq
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_,?_⟩
  · exact (sourceGram_posDef hq5).isHermitian.sub
      ((loadGram_posSemidef _).isHermitian.smul (by rfl))
  · intro v hv
    have hpos := hp.dotProduct_mulVec_pos hv
    have hl := sourceGram_retained_lower hq5 v
    have he : v ⬝ᵥ v = ∑ i, v i^2 := by simp only [dotProduct,pow_two]
    simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
      dotProduct_sub,dotProduct_smul,smul_eq_mul,star_trivial,he] at hpos ⊢
    linarith only [hpos,hl]

private theorem posDef_of_gram {M B : Matrix (Fin 5) (Fin 5) ℝ}
    (hB : B.det ≠ 0) (hgram : (Bᴴ*M*B).PosDef) : M.PosDef := by
  have hbinv : B*B⁻¹=1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB)
  have hinj : Function.Injective (B⁻¹).mulVec := by
    intro v w h
    have hh := congrArg (fun u => B*ᵥu) h
    simpa only [Matrix.mulVec_mulVec,hbinv,Matrix.one_mulVec] using hh
  have hback := hgram.conjTranspose_mul_mul_same hinj
  have he : (B⁻¹)ᴴ*(Bᴴ*M*B)*B⁻¹=M := by
    calc
      _ = (B*B⁻¹)ᴴ*M*(B*B⁻¹) := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = _ := by rw [hbinv]; simp
  rwa [he] at hback

/-- A quartic cross-load is paid by the complete native source from scale seven. -/
theorem native_quartic_reserve_from_seven_posDef {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (nativeShiftedMatrix 5 0 x-
      ((3/20)*sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^4) •
        crossLoad paidSevenSchur).PosDef := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq5 : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  have hK := sourceUnit_pos hq5
  have hq0 : 0 < q := by dsimp only [q]; linarith only [hq]
  have hload : (nativeBasis q)ᴴ*crossLoad paidSevenSchur*nativeBasis q = loadGram q := by
    simp only [crossLoad,loadGram,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  have hn : normalizedGram x (nativeShiftedMatrix 5 0 x-
      ((3/20)*sourceUnit x*q^4) • crossLoad paidSevenSchur) =
      sourceGram x-(3/20*q^4) • loadGram q := by
    unfold sourceGram
    rw [normalizedGram_eq_congruence,normalizedGram_eq_congruence]
    change (1/sourceUnit x) • ((nativeBasis q)ᴴ*
        (nativeShiftedMatrix 5 0 x-((3/20)*sourceUnit x*q^4) • crossLoad paidSevenSchur)*
        nativeBasis q) = _
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
      smul_sub,smul_smul,hload]
    rw [show (1/sourceUnit x)*((3/20)*sourceUnit x*q^4)=3/20*q^4 by
      field_simp [hK.ne']]
  have hp : (normalizedGram x (nativeShiftedMatrix 5 0 x-
      ((3/20)*sourceUnit x*q^4) • crossLoad paidSevenSchur)).PosDef := by
    rw [hn]
    exact normalized_reserve_posDef hq
  have hg := hp.smul hK
  rw [normalizedGram_eq_congruence,smul_smul,
    show sourceUnit x*(1/sourceUnit x)=1 by field_simp [hK.ne'],one_smul] at hg
  exact posDef_of_gram (nativeBasis_det_pos hq0).ne' hg

/-- The complete native quartic reserve on the scale-eight ray. -/
theorem native_quartic_reserve_posDef {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (nativeShiftedMatrix 5 0 x-
      ((3/20)*sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^4) •
        crossLoad paidSevenSchur).PosDef :=
  native_quartic_reserve_from_seven_posDef (by linarith only [hq])

end GaloisForLFunctions.ThetaCuspSections.QuarticRayCertificate
