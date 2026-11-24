import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AngularError.UnitaryChord

/-! # The unitary distance deficit as a least singular value -/

open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.AntipodalError
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
private abbrev op := toEuclideanCLM (n:=I) (𝕜:=ℂ)

/-- Complementary chord to the operator distance between two unitaries. -/
def deficit (U C : Mat I) := sqrt (4-‖U-C‖^2)

private theorem norm_image (U : Mat I) (hU : U∈unitary (Mat I)) (v : EuclideanSpace ℂ I) :
    ‖op U v‖=‖v‖ := by
  apply RHTower.deningerUnitary_norm_apply
  simpa only [map_mul,map_one,map_star,ContinuousLinearMap.star_eq_adjoint] using
    congrArg op (Unitary.mem_iff.mp hU).1

private theorem deficit_sq (U C : Mat I) (hU : U∈unitary (Mat I)) (hC : C∈unitary (Mat I)) :
    (deficit U C)^2+‖U-C‖^2=4 := by
  have hdist : ‖U-C‖ ≤ 2 := (norm_sub_le ..).trans (by
    rw [CStarRing.norm_coe_unitary (⟨U,hU⟩ : unitary (Mat I)),
      CStarRing.norm_coe_unitary (⟨C,hC⟩ : unitary (Mat I))]; norm_num)
  have h := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  rw [deficit,sq_sqrt (by linarith only [h])]
  ring

private theorem images_sq (U C : Mat I) (hU : U∈unitary (Mat I)) (hC : C∈unitary (Mat I))
    (v : EuclideanSpace ℂ I) : ‖op (U+C) v‖^2+‖op (U-C) v‖^2=4*‖v‖^2 := by
  have h := parallelogram_law_with_norm_mul (𝕜:=ℂ) (op U v) (op C v)
  rw [norm_image U hU,norm_image C hC] at h
  rw [map_add,map_sub,_root_.add_apply,_root_.sub_apply]
  linarith only [h]

/-- The complementary chord is the exact lower bound of U+C on unit
vectors. This characterization also works at the antipodal endpoint. -/
theorem deficit_floor_iff (U C : Mat I) (hU : U∈unitary (Mat I)) (hC : C∈unitary (Mat I))
    {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 2) :
    a ≤ deficit U C ↔ ∀ v : EuclideanSpace ℂ I, a*‖v‖ ≤ ‖op (U+C) v‖ := by
  have hquad := deficit_sq U C hU hC
  constructor
  · intro h v
    have h₁ := pow_le_pow_left₀ ha h 2
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) ((op (U-C)).le_opNorm v) 2
    change ‖op (U-C) v‖^2 ≤ (‖U-C‖*‖v‖)^2 at h₂
    apply (sq_le_sq₀ (mul_nonneg ha (norm_nonneg _)) (norm_nonneg _)).mp
    have hh := mul_le_mul_of_nonneg_right h₁ (sq_nonneg ‖v‖)
    have he := congrArg (fun x : ℝ => x*‖v‖^2) hquad
    nlinarith only [images_sq U C hU hC v,h₂,hh,he]
  · intro h
    let b := sqrt (4-a^2)
    have hb : 0 ≤ b := sqrt_nonneg _
    have hbsq : b^2=4-a^2 := sq_sqrt (by linarith only [pow_le_pow_left₀ ha ha' 2])
    have hh : ‖U-C‖ ≤ b := by
      change ‖op (U-C)‖ ≤ b
      apply ContinuousLinearMap.opNorm_le_bound _ hb
      intro v
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (norm_nonneg _))).mp
      have h₁ := pow_le_pow_left₀ (mul_nonneg ha (norm_nonneg _)) (h v) 2
      rw [mul_pow,hbsq]
      nlinarith only [images_sq U C hU hC v,h₁]
    apply (sq_le_sq₀ ha (sqrt_nonneg _)).mp
    linarith only [pow_le_pow_left₀ (norm_nonneg _) hh 2,hbsq,hquad]

/-- Operator perturbations of a unitary change its complementary chord
by at most their norm, including when ordinary distance is near two. -/
theorem deficit_perturb (U V C : Mat I) (hU : U∈unitary (Mat I))
    (hV : V∈unitary (Mat I)) (hC : C∈unitary (Mat I)) :
    deficit U C ≤ deficit V C+‖U-V‖ := by
  let a := deficit U C
  have ha : 0 ≤ a := sqrt_nonneg _
  have ha' : a ≤ 2 := by
    apply (sq_le_sq₀ ha zero_le_two).mp
    linarith only [deficit_sq U C hU hC,sq_nonneg ‖U-C‖]
  by_cases h : a ≤ ‖U-V‖
  · exact h.trans (le_add_of_nonneg_left (sqrt_nonneg _))
  have hlow := (deficit_floor_iff U C hU hC ha ha').mp le_rfl
  have hh := (deficit_floor_iff V C hV hC (sub_nonneg.mpr (le_of_not_ge h))
    ((sub_le_self a (norm_nonneg ‖U-V‖)).trans ha')).mpr (by
    intro v
    have he : op (U+C) v=op (U-V) v+op (V+C) v := by
      rw [←_root_.add_apply,←map_add]; congr 2; abel
    have h₁ := hlow v
    rw [he] at h₁
    have h₂ := norm_add_le (op (U-V) v) (op (V+C) v)
    have h₃ : ‖op (U-V) v‖ ≤ ‖U-V‖*‖v‖ := (op (U-V)).le_opNorm v
    linarith only [h₁,h₂,h₃])
  change a ≤ _
  linarith only [hh]

#print axioms deficit_floor_iff
#print axioms deficit_perturb
end
end GaloisForLFunctions.HTGeometry.FirstAscent.AntipodalError
