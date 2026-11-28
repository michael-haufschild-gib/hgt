import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Transversals.Compression
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Transversals.Weights

/-! # Energy transversals at a fit to a diagonal phase packet -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.Transversals
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {q : ℕ}
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- The weight depends on the fitted circuit and on the chosen pairing;
it is independent of the observed phases. -/
def pairWeight (W : unitary (Mat I)) (f : Fin q × Bool ↪ I) (x : Fin q → Bool) : ℂ :=
  transversalMinor ((pairColumns f).conjTranspose*star W.val) f x

/-- Each Fourier frequency uses exactly one physical level from each
pair. In particular, frequency differences involve only the paired gaps. -/
def pairCharacter (W : unitary (Mat I)) (f : Fin q × Bool ↪ I) (p : I → ℂ) : ℂ :=
  ∑ x : Fin q → Bool, pairWeight W f x*∏ j, p (f (j,x j))

omit [Nonempty I] in
theorem common_phase (W : unitary (Mat I)) (f : Fin q × Bool ↪ I) (p : I → ℂ) (z : ℂ) :
    pairCharacter W f (fun i => z*p i)=z^q*pairCharacter W f p := by
  simp only [pairCharacter,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,mul_sum]
  exact sum_congr rfl fun _ _ => by ring

/-- Compressing to the equal superpositions within the pairs produces
the transversal character. Cauchy–Binet bounds its total squared weights. -/
theorem diagonal_transversals (W D : unitary (Mat I)) (p : I → ℂ) (hD : D.val=diagonal p)
    {e : ℝ} (hf : ‖D.val-W.val‖≤e) (hc : 0≤1-e^2/2) (f : Fin q × Bool ↪ I) :
    (1-e^2/2)^q≤halfAmplitude^q*‖pairCharacter W f p‖ ∧
      (∑ x : Fin q → Bool, ‖pairWeight W f x‖^2)≤1 := by
  let B := pairColumns f
  let A := B.conjTranspose*star W.val
  have hB : B.conjTranspose*B=1 := columns_isometry f
  have hA : A*A.conjTranspose=1 := by
    dsimp only [A]
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose]
    change B.conjTranspose*star W.val*(W.val*B)=1
    rw [Matrix.mul_assoc,←Matrix.mul_assoc (star W.val),(Unitary.mem_iff.mp W.2).1,Matrix.one_mul,hB]
  refine ⟨?_,transversal_mass A hA f⟩
  let Y := W⁻¹*D
  have hY : ‖1-Y.val‖≤e := by
    change ‖1-star W.val*D.val‖≤e
    rw [←(Unitary.mem_iff.mp W.2).1,←mul_sub]
    change ‖(W⁻¹).val*(W.val-D.val)‖≤e
    rwa [CStarRing.norm_mem_unitary_mul _ (W⁻¹).2,norm_sub_rev]
  have h := compression_det Y B hB hY hc
  change _≤‖(B.conjTranspose*(star W.val*D.val)*B).det‖ at h
  rw [←Matrix.mul_assoc B.conjTranspose,hD,paired_expansion, norm_mul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0≤halfAmplitude from Real.sqrt_nonneg _)] at h
  simpa only [Fintype.card_fin,pairCharacter,pairWeight,B] using h

#print axioms diagonal_transversals
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.Transversals
