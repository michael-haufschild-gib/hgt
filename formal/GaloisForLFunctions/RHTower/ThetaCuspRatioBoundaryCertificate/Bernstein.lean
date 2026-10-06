import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.TermExpansion
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBernstein.Basis
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open scoped BigOperators
open HTGeometry.EvenCompactBernstein

def boundaryH77 : ℝ := 4/5
def boundaryS77 : ℝ := (6/5)*(361/25)

def boundaryBernstein77 (f : ℕ → ℕ → ℝ) (t v : ℝ) : ℝ :=
  ∑ A ∈ Finset.range 97, ∑ B ∈ Finset.range 37,
    f A B*unscaledBernstein 96 A t*unscaledBernstein 36 B v

theorem boundaryBernstein77_add (f g : ℕ → ℕ → ℝ) (t v : ℝ) :
    boundaryBernstein77 (fun A B => f A B+g A B) t v=
      boundaryBernstein77 f t v+boundaryBernstein77 g t v := by
  simp only [boundaryBernstein77,add_mul,Finset.sum_add_distrib]

theorem boundaryBernstein77_sum {ι : Type*} (I : Finset ι)
    (f : ι → ℕ → ℕ → ℝ) (t v : ℝ) :
    boundaryBernstein77 (fun A B => ∑ i ∈ I, f i A B) t v=
      ∑ i ∈ I, boundaryBernstein77 (f i) t v := by
  simp only [boundaryBernstein77,Finset.sum_mul]
  simp_rw [Finset.sum_comm (s:=Finset.range 37) (t:=I)]
  rw [Finset.sum_comm]

theorem boundaryBernstein77_monomial (c : ℝ) (a p : ℕ)
    (ha : a≤96) (hp : p≤36) (t v : ℝ) :
    boundaryBernstein77 (fun A B =>
      c*degreeElevationCoefficient 96 a A*degreeElevationCoefficient 36 p B) t v=
        c*t^a*v^p :=
  tensor_monomial_bernstein_reconstruction 96 36 a p ha hp c t v

def boundaryTermCoefficient77 (c : ℝ) (a p j A B : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (j+1), ∑ m ∈ Finset.range (l+1),
    (boundaryTermScalar77 c j l m*boundaryH77^(a+2*l+m)*boundaryS77^(p+j+l))*
      degreeElevationCoefficient 96 (a+2*l+m) A*
        degreeElevationCoefficient 36 (p+j+l) B

theorem boundaryTermCoefficient77_reconstruction (c : ℝ) (a p j : ℕ)
    (ha : a+3*j≤96) (hp : p+2*j≤36) (t v : ℝ) :
    boundaryBernstein77 (boundaryTermCoefficient77 c a p j) t v=
      boundaryTerm77 c a p j (boundaryH77*t) (boundaryS77*v) := by
  rw [boundaryTerm77_expansion]
  unfold boundaryTermCoefficient77
  rw [boundaryBernstein77_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [boundaryBernstein77_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hlj : l≤j := by have := Finset.mem_range.mp hl; omega
  have hml : m≤l := by have := Finset.mem_range.mp hm; omega
  have ha' : a+2*l+m≤96 := by omega
  have hp' : p+j+l≤36 := by omega
  rw [boundaryBernstein77_monomial _ _ _ ha' hp']
  simp only [mul_pow]
  ring

end
end HTGeometry.ThetaRatioInfinity
