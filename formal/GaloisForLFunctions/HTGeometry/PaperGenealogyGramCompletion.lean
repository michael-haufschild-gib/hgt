import GaloisForLFunctions.HTGeometry.ScalarGenealogyGramCompletion
import GaloisForLFunctions.HTGeometry.PaperGenealogyFredholmRecovery

/-! # The normalized determinant completion on the original certificate fibre

The full genealogy retains infinite compact-ideal cost. Its normalized Gram
determinants nevertheless have a canonical finite positive completion exactly
when its deviation from identity is Hilbert–Schmidt. The completion is the
regularized determinant of the original full-carrier Gram perturbation.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt _root_.ContinuousLinearMap Filter Topology
open scoped ENNReal

section Unitary
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem genealogyGramPerturbation_unitaryPush (u : H ≃ₗᵢ[ℂ] K) (G : H →L[ℂ] H) :
    genealogyGramPerturbation (RHTower.unitaryPush u G) =
      RHTower.unitaryPush u (genealogyGramPerturbation G) := by
  change (1 / 2 : ℂ) • ((RHTower.unitaryPush u G).adjoint * RHTower.unitaryPush u G - 1) =
    RHTower.unitaryPush u ((1 / 2 : ℂ) • (G.adjoint * G - 1))
  simp only [RHTower.unitaryPush_smul, RHTower.unitaryPush_sub, RHTower.unitaryPush_mul,
    RHTower.unitaryPush_one, RHTower.adjoint_unitaryPush]

omit [CompleteSpace H] [CompleteSpace K] in
theorem det2Op_unitaryPush {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ H) (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    RHTower.det2Op (unitaryHilbertBasis b u) (RHTower.unitaryPush u T) = RHTower.det2Op b T := by
  simp only [RHTower.det2Op, coordMatrix_unitaryHilbertBasis]

theorem isHilbertSchmidt_unitaryPush_iff (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    IsHilbertSchmidt (RHTower.unitaryPush u T) ↔ IsHilbertSchmidt T := by
  constructor
  · intro h
    have hb : IsHilbertSchmidt (RHTower.unitaryPush u.symm (RHTower.unitaryPush u T)) :=
      (h.comp_right (u : H →L[ℂ] K)).comp_left (u.symm : K →L[ℂ] H)
    rwa [RHTower.unitaryPush_symm_unitaryPush] at hb
  · intro h
    exact (h.comp_right (u.symm : K →L[ℂ] H)).comp_left (u : H →L[ℂ] K)

end Unitary

def scalarCoordinateGenealogy (a : OpCertStream 1) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  RHTower.unitaryPush scalarCertificateCoordinates a.genealogy

theorem scalarCoordinateGenealogy_apply (a : OpCertStream 1)
    (f : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    scalarCoordinateGenealogy a f n = f n - scalarCertificateCoefficient a n * f (n + 1) := by
  rw [scalarCoordinateGenealogy, RHTower.unitaryPush_apply, scalarCertificateCoordinates_genealogy]
  simp only [LinearIsometryEquiv.apply_symm_apply]

theorem scalarCoordinateGenealogy_basis (a : OpCertStream 1) (j : ℕ) :
    scalarCoordinateGenealogy a (lpBasisVec j) = finiteGenealogyColumn (scalarCertificateCoefficient a) j :=
  fullScalarGenealogy_basis_of_apply (scalarCoordinateGenealogy_apply a) j

theorem paperGenealogy_eq_unitaryPush_scalarCoordinates (a : OpCertStream 1) :
    a.genealogy = RHTower.unitaryPush scalarCertificateCoordinates.symm (scalarCoordinateGenealogy a) :=
  (RHTower.unitaryPush_symm_unitaryPush scalarCertificateCoordinates a.genealogy).symm

theorem paperGenealogy_weight_isHilbertSchmidt_iff (a : OpCertStream 1) :
    IsHilbertSchmidt (1 - a.genealogy) ↔ Summable (fun n => ‖scalarCertificateCoefficient a n‖ ^ 2) := by
  have h := fullGenealogyWeight_isHilbertSchmidt_iff (scalarCoordinateGenealogy_basis a)
  have he : 1 - scalarCoordinateGenealogy a =
      RHTower.unitaryPush scalarCertificateCoordinates (1 - a.genealogy) := by
    simp only [scalarCoordinateGenealogy, RHTower.unitaryPush_sub, RHTower.unitaryPush_one]
  rw [he, isHilbertSchmidt_unitaryPush_iff] at h
  exact h

def paperGenealogyNormalizedGram (a : OpCertStream 1) (N : ℕ) : ℂ :=
  paperGenealogyGramDet a N / 2 ^ N

theorem paperGenealogyNormalizedGram_eq (a : OpCertStream 1) (N : ℕ) :
    paperGenealogyNormalizedGram a N = (normalizedGenealogyGram (scalarCertificateCoefficient a) N : ℂ) := by
  simp [paperGenealogyNormalizedGram, paperGenealogyGramDet_eq, normalizedGenealogyGram]

def paperGenealogyGramCompletion (a : OpCertStream 1) : ℂ :=
  RHTower.det2Op scalarCertificateBasis (genealogyGramPerturbation a.genealogy) *
    Complex.exp ((1 / 2 : ℂ) * ((∑' n, ‖scalarCertificateCoefficient a n‖ ^ 2 : ℝ) : ℂ))

theorem paperGenealogyGramCompletion_eq_scalar (a : OpCertStream 1) :
    paperGenealogyGramCompletion a =
      scalarGenealogyGramCompletion (scalarCoordinateGenealogy a) (scalarCertificateCoefficient a) := by
  rw [paperGenealogyGramCompletion, paperGenealogy_eq_unitaryPush_scalarCoordinates,
    genealogyGramPerturbation_unitaryPush, scalarCertificateBasis, det2Op_unitaryPush]
  rfl

theorem paperGenealogyGramCompletion_iff (a : OpCertStream 1) :
    ((paperGenealogyGramCompletion a).im = 0 ∧ 1 ≤ (paperGenealogyGramCompletion a).re ∧
      Tendsto (paperGenealogyNormalizedGram a) atTop (𝓝 (paperGenealogyGramCompletion a))) ↔
      Summable (fun n => ‖scalarCertificateCoefficient a n‖ ^ 2) := by
  have he : paperGenealogyNormalizedGram a =
      fun N => (normalizedGenealogyGram (scalarCertificateCoefficient a) N : ℂ) :=
    funext (paperGenealogyNormalizedGram_eq a)
  rw [he, paperGenealogyGramCompletion_eq_scalar]
  exact scalarGenealogyGramCompletion_spec_iff (scalarCoordinateGenealogy_basis a)

theorem paperGenealogyGramCompletion_hilbertSchmidt_iff (a : OpCertStream 1) :
    ((paperGenealogyGramCompletion a).im = 0 ∧ 1 ≤ (paperGenealogyGramCompletion a).re ∧
      Tendsto (paperGenealogyNormalizedGram a) atTop (𝓝 (paperGenealogyGramCompletion a))) ↔
      IsHilbertSchmidt (1 - a.genealogy) :=
  (paperGenealogyGramCompletion_iff a).trans (paperGenealogy_weight_isHilbertSchmidt_iff a).symm

theorem paperGenealogyNormalizedGram_diverges_iff (a : OpCertStream 1) :
    Tendsto (fun N => (paperGenealogyNormalizedGram a N).re) atTop atTop ↔
      ¬ Summable (fun n => ‖scalarCertificateCoefficient a n‖ ^ 2) := by
  simpa only [paperGenealogyNormalizedGram_eq, Complex.ofReal_re]
    using normalizedGenealogyGram_tendsto_atTop_iff (scalarCertificateCoefficient a)

theorem paperGenealogyGramCompletion_infiniteCost (a : OpCertStream 1) :
    compactOperatorTraceCost (FibSeq 1) a.genealogy = ∞ ∧
      (((paperGenealogyGramCompletion a).im = 0 ∧ 1 ≤ (paperGenealogyGramCompletion a).re ∧
        Tendsto (paperGenealogyNormalizedGram a) atTop (𝓝 (paperGenealogyGramCompletion a))) ↔
        IsHilbertSchmidt (1 - a.genealogy)) :=
  ⟨compactOperatorTraceCost_genealogy 0 a, paperGenealogyGramCompletion_hilbertSchmidt_iff a⟩

end
end GaloisForLFunctions.HTGeometry
