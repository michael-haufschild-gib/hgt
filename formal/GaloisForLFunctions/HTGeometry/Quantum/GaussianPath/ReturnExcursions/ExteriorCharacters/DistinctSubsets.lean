import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.UnitaryCoefficients

/-! # Distinct energy subsets in exterior characters -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Fourier coefficient at each subset is the corresponding principal minor
of the fixed matrix. Each selected coordinate occurs exactly once. -/
def subsetCharacter (A : Mat I) (p : I → ℂ) (q : ℕ) : ℂ :=
  ∑ S ∈ univ.powersetCard q, (A.submatrix (Subtype.val : S → I) Subtype.val).det*∏ i ∈ S, p i

private theorem twisted_minor (A : Mat I) (p : I → ℂ) (S : Finset I) :
    ((A*diagonal p).submatrix (Subtype.val : S → I) Subtype.val).det=
      (A.submatrix (Subtype.val : S → I) Subtype.val).det*∏ i ∈ S, p i := by
  have h : (A*diagonal p).submatrix (Subtype.val : S → I) Subtype.val=
      A.submatrix (Subtype.val : S → I) Subtype.val * diagonal (fun i : S => p i) := by
    ext i j
    simp only [submatrix_apply,Matrix.mul_diagonal]
  rw [h,det_mul,det_diagonal,←prod_attach S p]
  rfl

/-- The characteristic coefficient is the signed sum at one exterior degree. -/
theorem charpoly_diagonal_twist (A : Mat I) (p : I → ℂ) (q : ℕ) (hq : q≤Fintype.card I) :
    (A*diagonal p).charpoly.coeff (Fintype.card I-q)=(-1)^q*subsetCharacter A p q := by
  simp only [Matrix.charpoly_coeff_eq_sum_minors _ q hq,twisted_minor,subsetCharacter]

/-- A common phase contributes only its degree-th power. -/
theorem subsetCharacter_smul (A : Mat I) (p : I → ℂ) (a : ℂ) (q : ℕ) :
    subsetCharacter A (fun i => a*p i) q=a^q*subsetCharacter A p q := by
  rw [subsetCharacter,subsetCharacter,mul_sum]
  apply sum_congr rfl
  intro S hS
  rw [prod_mul_distrib,prod_const,(mem_powersetCard.mp hS).2]
  ring

/-- One implementing unitary must pass all the distinct-subset tests. -/
theorem diagonal_fit [Nonempty I] (W D : unitary (Mat I)) (p : I → ℂ) (hD : D.val=diagonal p)
    {e : ℝ} (hc : 0≤1-e^2/2) (hfit : ‖D.val-W.val‖≤e) (q : ℕ) (hq : q≤Fintype.card I) :
    ((Fintype.card I).choose q:ℝ)*(1-e^2/2)^min q (Fintype.card I-q)
      ≤ ‖subsetCharacter (star W.val) p q‖ := by
  let Y := W⁻¹*D
  have hh : ‖1-Y.val‖≤e := by
    change ‖1-star W.val*D.val‖≤e
    rw [←(Unitary.mem_iff.mp W.2).1,←mul_sub]
    change ‖(W⁻¹).val*(W.val-D.val)‖≤e
    rw [CStarRing.norm_mem_unitary_mul _ (W⁻¹).2,norm_sub_rev]
    exact hfit
  have h := unitary_character_floor Y hh hc q hq
  change _≤‖(star W.val*D.val).charpoly.coeff _‖ at h
  simpa only [hD,charpoly_diagonal_twist _ _ q hq,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul] using h

#print axioms diagonal_fit
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
