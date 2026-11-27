import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.Rounding.ColumnTests

/-! # Sign rounding and a weighted Gram inequality for a reflection -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections.Rounding
open StaticLocalLaboratoryComplexityGrowthLaw
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Choose the real sign in the half-plane of the phase. -/
def side (z : ℂ) : ℂ := if 0≤z.re then 1 else -1

private theorem side_norm (z : ℂ) : ‖side z‖=1 := by by_cases h : 0≤z.re <;> simp [side,h]

def signs (f : I → ℂ) : unitaryGroup I ℂ :=
  ⟨diagonal (fun i => side (f i)),mem_unitaryGroup_diagonal_general _ (fun _ => side_norm _)⟩

def magnitude (f : I → ℂ) : Mat I := diagonal (fun i => ((|(f i).re|:ℝ):ℂ))

theorem star_signs (f : I → ℂ) : star (signs f).val=(signs f).val := by
  ext i j
  by_cases h : i=j
  · subst j
    by_cases hr : 0≤(f i).re <;> simp [signs,side,hr]
  · simp [signs,h,Ne.symm h]

private theorem scalar_split (z : ℂ) : z+star z=side z*((|z.re|:ℂ)+(|z.re|:ℂ)) := by
  by_cases h : 0≤z.re
  · apply Complex.ext <;> simp [side,h,abs_of_nonneg h]
  · have h' := (lt_of_not_ge h).le
    apply Complex.ext <;> simp [side,h,abs_of_nonpos h']

private theorem split_diagonal (f : I → ℂ) :
    diagonal f+star (diagonal f)=(signs f).val*(magnitude f+magnitude f) := by
  ext i j
  by_cases h : i=j
  · subst j
    simpa [signs,magnitude,Matrix.diagonal_mul] using scalar_split (f i)
  · simp [signs,magnitude,Matrix.diagonal_mul,h,Ne.symm h]

private theorem split_right (f : I → ℂ) :
    (diagonal f+star (diagonal f))*(signs f).val=magnitude f+magnitude f := by
  rw [split_diagonal]
  let S := (signs f).val
  let P := magnitude f
  have h : Commute S P := by
    ext i j
    simp [S,P,signs,magnitude,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.diagonal_apply,mul_comm]
  have hs : S*S=1 := by simpa only [S,star_signs] using (Unitary.mem_iff.mp (signs f).property).1
  rw [show S*(P+P)=(P+P)*S from (h.add_right h).eq,mul_assoc,hs,mul_one]

/-- Averaging the error tests for D, its adjoint, and both sign-conjugate
test vectors leaves the product of the signed anticommutator with |Re D|. -/
theorem signed_gram (W : Mat I) (hW : W∈unitary (Mat I)) (hsW : star W=W)
    (f : I → ℂ) (hf : ∀ i, ‖f i‖=1) (V : unitaryGroup I ℂ) (i : I) :
    let S := (signs f).val
    2-reading V i ((W*S+S*W)*magnitude f) ≤ ‖diagonal f-W‖^2 := by
  intro S
  let D := diagonal f
  let P := magnitude f
  let A := W*S+S*W
  have hD : D∈unitary (Mat I) := mem_unitaryGroup_diagonal_general _ hf
  have hstar : ‖star D-W‖=‖D-W‖ := by
    calc _ = ‖star (D-W)‖ := by rw [star_sub,hsW]
         _ = _ := norm_star _
  have hb (B : unitaryGroup I ℂ) : 2-2*reading B i (W*D)≤‖D-W‖^2 := by
    simpa only [hsW] using column_error B i W D hW hD
  have hc (B : unitaryGroup I ℂ) : 2-2*reading B i (W*star D)≤‖D-W‖^2 := by
    simpa only [hsW,hstar] using column_error B i W (star D) hW (Unitary.star_mem hD)
  have hcon (X : Mat I) : reading V i (S*X*S)=reading (signs f*V) i X := by
    simpa only [star_signs] using reading_conjugate (signs f) V i X
  have he : W*D+W*star D+(S*(W*D)*S+S*(W*star D)*S)=A*P+A*P := by
    calc _ = W*(D+star D)+(S*W)*((D+star D)*S) := by simp only [mul_add,add_mul,mul_assoc]
         _ = W*(S*(P+P))+(S*W)*(P+P) := by rw [show (D+star D)*S=P+P from split_right f,
           show D+star D=S*(P+P) from split_diagonal f]
         _ = _ := by simp only [A,mul_add,add_mul,mul_assoc]; abel
  have h := congrArg (reading V i) he
  simp only [map_add,hcon] at h
  change 2-reading V i (A*P)≤‖D-W‖^2
  linarith only [h,hb V,hc V,hb (signs f*V),hc (signs f*V)]

#print axioms signed_gram
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections.Rounding
