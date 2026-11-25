import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.Pencil
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.UnivariateSublevel

/-! # Conditional small windows for a specified energy gap -/

open Matrix MeasureTheory ProbabilityTheory Set Polynomial
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A bounded spectrum and one gap within δ of the forecast control the
whole gap determinant, with just one small factor. -/
theorem gap_determinant_bound (H : Matrix I I ℂ) (h : H.IsHermitian) (b L : ℝ)
    (hL : ∀ i, |h.eigenvalues i|≤L) (i j : I) :
    ‖(Matrix.scalar (I × I) (b:ℂ)-gapOperator H).det‖ ≤
      |b-(h.eigenvalues i-h.eigenvalues j)|*(1+|b|+2*max L 0)^(Fintype.card I^2) := by
  classical
  let M := 1+|b|+2*max L 0
  have hM : 1≤M := by dsimp only [M]; linarith only [abs_nonneg b,le_max_right L 0]
  let g (p : I × I) := |b-(h.eigenvalues p.1-h.eigenvalues p.2)|
  have hg (p : I × I) : g p≤M := calc
    _ ≤ |b|+(|h.eigenvalues p.1|+|h.eigenvalues p.2|) :=
      (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
    _ ≤ M := by dsimp only [M]; linarith only [hL p.1,hL p.2,le_max_left L 0]
  have hrest := Finset.prod_le_prod (s:=Finset.univ.erase (i,j)) (fun p _ => abs_nonneg _)
    (fun p _ => hg p)
  rw [gap_determinant H h,norm_prod]
  simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  change (∏ p, g p)≤g (i,j)*M^(Fintype.card I^2)
  rw [←Finset.mul_prod_erase Finset.univ g (Finset.mem_univ (i,j))]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  refine hrest.trans ?_
  rw [Finset.prod_const]
  apply pow_le_pow_right₀ hM
  simpa only [Finset.card_univ,Fintype.card_prod,pow_two] using Finset.card_le_card (Finset.erase_subset (i,j) Finset.univ)

/-- With one Gaussian field unrevealed, the probability that a pair gap
falls in a window of radius c r^(D²), while all energies are bounded by L,
is at most 2D² r. The constant is positive for every nonzero gap polynomial. -/
theorem gap_small_window (A Z : Matrix I I ℂ) (hH : ∀ y : ℝ, (A+(y:ℂ) • Z).IsHermitian)
    (b L : ℝ) (hn : (gapPencil A Z b).det≠0) :
    ∃ c > (0:ℝ), ∀ r∈Ioc (0:ℝ) 1,
      (gaussianReal 0 1).real {y : ℝ | (∀ i, |(hH y).eigenvalues i|≤L) ∧
        ∃ i j, |b-((hH y).eigenvalues i-(hH y).eigenvalues j)|<c*r^(Fintype.card I^2)} ≤
          2*(Fintype.card I^2:ℕ)*r := by
  let P := (gapPencil A Z b).det
  let D := Fintype.card I^2
  let M := (1+|b|+2*max L 0)^D
  have hM : 0<M := pow_pos (by linarith only [abs_nonneg b,le_max_right L 0]) _
  have hp : 0<‖P.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hn)
  refine ⟨‖P.leadingCoeff‖/M,div_pos hp hM,fun r hr => ?_⟩
  have hdeg : P.natDegree≤D := gapPencil_degree A Z b
  have hsub : {y : ℝ | (∀ i, |(hH y).eigenvalues i|≤L) ∧
      ∃ i j, |b-((hH y).eigenvalues i-(hH y).eigenvalues j)|<‖P.leadingCoeff‖/M*r^D} ⊆
      {y : ℝ | ‖P.eval (y:ℂ)‖<‖P.leadingCoeff‖*r^P.natDegree} := by
    rintro y ⟨hL,i,j,hij⟩
    change ‖P.eval (y:ℂ)‖<_
    rw [show P.eval (y:ℂ)=_ from eval_gapPencil A Z b y]
    apply (gap_determinant_bound _ (hH y) b L hL i j).trans_lt
    apply (mul_lt_mul_of_pos_right hij hM).trans_le
    rw [mul_right_comm,div_mul_cancel₀ _ hM.ne']
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr.1.le hr.2 hdeg) hp.le
  exact (measureReal_mono hsub).trans ((gaussian_polynomial_sublevel P r hr.1.le).trans
    (by gcongr))

#print axioms gap_small_window
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
