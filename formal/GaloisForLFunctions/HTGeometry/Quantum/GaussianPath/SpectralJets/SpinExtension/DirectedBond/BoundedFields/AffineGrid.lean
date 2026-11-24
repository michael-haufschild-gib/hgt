import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.BoundedFields.PositiveGrid
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.LinearMomentQuotient

/-! # Bounded positive fields along an affine family of Pauli coefficients -/
open MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

def affinePoint {n m : ℕ} (c : Fin m→ℂ) (V : Fin n→Fin m→ℂ) (y : Fin n→ℂ) (i : Fin m) :=
  c i+∑ s, V s i*y s

/-- A single nonzero evaluation on an affine family guarantees a positive
integer point of the same family with each input at most d+1. -/
theorem positive_grid_on_family {n m d : ℕ} (Q : MvPolynomial (Fin m) ℂ)
    (c : Fin m→ℂ) (V : Fin n→Fin m→ℂ) (y : Fin n→ℂ)
    (hn : eval (affinePoint c V y) Q≠0) (hd : Q.totalDegree≤d) :
    ∃ b : Fin n→ℕ, (∀ i, b i≤d) ∧ eval (affinePoint c V (fun s => (b s:ℂ)+1)) Q≠0 := by
  let J (i : Fin m) : MvPolynomial (Fin n) ℂ := C (c i)+∑ s, C (V s i)*X s
  let F := bind₁ J
  have he (u : Fin n→ℂ) (p : MvPolynomial (Fin m) ℂ) :
      eval u (F p)=eval (affinePoint c V u) p := by
    induction p using MvPolynomial.induction_on with
    | C a => simp [F]
    | add p q hp hq => simp only [map_add,hp,hq]
    | mul_X p i hp => simp [F,J,affinePoint,map_mul,←hp]
  have hF : F Q≠0 := by
    intro hz
    apply hn
    rw [←he y,hz,map_zero]
  have hJ (i : Fin m) : (F (X i)).totalDegree≤1 := by
    change ((bind₁ J) (X i)).totalDegree≤1
    rw [bind₁_X_right]
    apply (totalDegree_add ..).trans (max_le ?_ ?_)
    · simp
    · apply totalDegree_finsetSum_le
      intro s _
      exact (totalDegree_mul ..).trans (by simp)
  have hdeg := (ArithmeticHarmonicAnalysis.polynomialMap_totalDegree_le ℂ F hJ Q).trans hd
  obtain ⟨b,hb,hQ⟩ := positive_grid (F Q) hF hdeg
  exact ⟨b,hb,by rwa [he] at hQ⟩

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
