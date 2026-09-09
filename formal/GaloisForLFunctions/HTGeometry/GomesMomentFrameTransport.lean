import GaloisForLFunctions.HTGeometry.SecondKindMomentPolynomials
import GaloisForLFunctions.HTGeometry.GomesJacobiPositiveMetric

/-!
# Internal-frame area transport for the actual moment corpus

Application of associated-frame geometry from https://arxiv.org/abs/2404.10461
and the invariant-tensor viewpoint of https://arxiv.org/abs/2607.24901.
The existing first- and second-kind polynomials form a real frame whose exact
area character is the existing moment Wronskian. No positivity is assumed here.
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- Evaluation of the corpus's two-solution moment transfer frame. -/
def gomesMomentFrame (s : ℕ → ℝ) (n : ℕ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(monicOrtho s (n+1)).eval x,(secondKind s (n+1)).eval x;
    (monicOrtho s n).eval x,(secondKind s n).eval x]

/-- The recurrence frame is precisely entrywise evaluation of the existing polynomial frame. -/
theorem gomesMomentFrame_eq_eval (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    gomesMomentFrame s n x = (momentTransfer s n).map (Polynomial.eval x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The frame's determinant is the evaluated two-solution Wronskian. -/
theorem gomesMomentFrame_det (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (gomesMomentFrame s n x).det = (momentWronskian s n).eval x := by
  simp [gomesMomentFrame,Matrix.det_fin_two,momentWronskian,mul_comm]

/-- The full polynomial recurrence frame transports area by its Wronskian, even without positivity. -/
theorem gomesMomentFrame_area (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (gomesMomentFrame s n x)ᵀ * gomesShearAreaMatrix ℝ * gomesMomentFrame s n x =
      (momentWronskian s n).eval x • gomesShearAreaMatrix ℝ := by
  rw [gomesShearArea_transport,gomesMomentFrame_det]

end GaloisForLFunctions.HTGeometry
