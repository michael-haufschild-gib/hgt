import GaloisForLFunctions.HTGeometry.GomesHiggsResidualCircle
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Matrix.Normed

/-!
# Explicit smooth weak frame of the Higgs doublet

The rank-two gauge reduction in Gomes, arXiv:2509.25276v7, Proposition 1,
is implemented on the corpus's actual doublet without a choice of transporter.
The doublet and its conjugate form a scalar-Gram quaternionic matrix. Normalizing
by the proved radial amplitude produces an SU(2) frame exactly on the nonzero
locus. Its adjoint fixes radial gauge, the frame is smooth on that locus, and it
transforms equivariantly under the existing weak gauge action. The zero matrix
extension does not assert regularity at the singular zero doublet.
-/

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Quaternionic weak matrices have scalar Hermitian Gram operator. -/
theorem spinFlipQuaternionMatrix_gram (a b : ℂ) :
    (spinFlipQuaternionMatrix a b)ᴴ * spinFlipQuaternionMatrix a b =
      ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinFlipQuaternionMatrix,Matrix.mul_apply,Fin.sum_univ_two,
      Complex.normSq_eq_conj_mul_self] <;> ring

/-- The determinant records precisely the spinor norm. -/
theorem spinFlipQuaternionMatrix_det (a b : ℂ) :
    (spinFlipQuaternionMatrix a b).det = ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) := by
  simp [spinFlipQuaternionMatrix,Matrix.det_fin_two,Complex.normSq_eq_conj_mul_self]
  ring

/-- Exact weak-group membership of every quaternionic coefficient pair. -/
theorem spinFlipQuaternionMatrix_specialUnitary_iff (a b : ℂ) :
    spinFlipQuaternionMatrix a b ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ↔
      Complex.normSq a + Complex.normSq b = 1 := by
  constructor
  · intro h
    have hd := (Matrix.mem_specialUnitaryGroup_iff.mp h).2
    rw [spinFlipQuaternionMatrix_det] at hd
    exact Complex.ofReal_inj.mp hd
  · intro h
    rw [Matrix.mem_specialUnitaryGroup_iff,Matrix.mem_unitaryGroup_iff']
    change (spinFlipQuaternionMatrix a b)ᴴ * spinFlipQuaternionMatrix a b = 1 ∧ _
    rw [spinFlipQuaternionMatrix_gram,spinFlipQuaternionMatrix_det,h]
    simp

/-- Explicit quaternionic frame of the nonzero Higgs doublet; zero extends to the zero matrix. -/
def higgsCanonicalFrame (H : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  spinFlipQuaternionMatrix
    (H 0 / (Real.sqrt (abelianHiggsSpinorNormSq H) : ℂ))
    (H 1 / (Real.sqrt (abelianHiggsSpinorNormSq H) : ℂ))

/-- The explicit frame belongs to SU(2) exactly away from the singular zero orbit. -/
theorem higgsCanonicalFrame_specialUnitary_iff (H : Fin 2 → ℂ) :
    higgsCanonicalFrame H ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ↔ H ≠ 0 := by
  rw [higgsCanonicalFrame,spinFlipQuaternionMatrix_specialUnitary_iff]
  have hn : 0 ≤ abelianHiggsSpinorNormSq H :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  rw [Complex.normSq_div,Complex.normSq_div,← add_div,Complex.normSq_ofReal,← pow_two,
    Real.sq_sqrt hn]
  change abelianHiggsSpinorNormSq H / abelianHiggsSpinorNormSq H = 1 ↔ H ≠ 0
  rw [div_self_eq_one₀]
  exact (higgs_normSq_eq_zero_iff H).not

/-- The frame recovers the exact Higgs doublet from its canonical radial representative. -/
theorem higgsCanonicalFrame_radial (H : Fin 2 → ℂ) :
    (higgsCanonicalFrame H).mulVec (higgsRadialRepresentative H) = H := by
  by_cases hH : H=0
  · subst H
    simp [higgsCanonicalFrame,higgsRadialRepresentative,abelianHiggsSpinorNormSq,
      spinFlipQuaternionMatrix]
  · have hr := (higgs_radial_amplitude_eq_zero_iff H).not.mpr hH
    funext i
    fin_cases i <;> simp [higgsCanonicalFrame,higgsRadialRepresentative,
      spinFlipQuaternionMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two,hr]

/-- The adjoint frame is an explicit radial gauge, including the zero identity of vectors. -/
theorem higgsCanonicalFrame_adjoint (H : Fin 2 → ℂ) :
    (higgsCanonicalFrame H)ᴴ.mulVec H = higgsRadialRepresentative H := by
  by_cases hH : H=0
  · subst H
    funext i
    fin_cases i <;> simp [higgsRadialRepresentative,abelianHiggsSpinorNormSq]
  · have hu := Matrix.specialUnitaryGroup_le_unitaryGroup
      ((higgsCanonicalFrame_specialUnitary_iff H).mpr hH)
    have hh := Matrix.mem_unitaryGroup_iff'.mp hu
    change (higgsCanonicalFrame H)ᴴ * higgsCanonicalFrame H = 1 at hh
    calc
      (higgsCanonicalFrame H)ᴴ.mulVec H =
          (higgsCanonicalFrame H)ᴴ.mulVec ((higgsCanonicalFrame H).mulVec (higgsRadialRepresentative H)) :=
        congrArg (higgsCanonicalFrame H)ᴴ.mulVec (higgsCanonicalFrame_radial H).symm
      _ = _ := by rw [Matrix.mulVec_mulVec,hh,Matrix.one_mulVec]

/-- The actual Higgs norm is smooth as a real polynomial on the doublet carrier. -/
theorem contDiff_higgsNormSq : ContDiff ℝ (⊤ : WithTop ℕ∞) abelianHiggsSpinorNormSq := by
  have hr (i : Fin 2) : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun H : Fin 2 → ℂ => (H i).re) :=
    Complex.reCLM.contDiff.comp (by fun_prop)
  have hi (i : Fin 2) : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun H : Fin 2 → ℂ => (H i).im) :=
    Complex.imCLM.contDiff.comp (by fun_prop)
  unfold abelianHiggsSpinorNormSq
  simp only [Complex.normSq_apply]
  exact (((hr 0).mul (hr 0)).add ((hi 0).mul (hi 0))).add
    (((hr 1).mul (hr 1)).add ((hi 1).mul (hi 1)))

/-- Unlike the earlier choice-based transport, this explicit gauge frame is smooth
on the entire nonzero-doublet locus. -/
theorem contDiffOn_higgsCanonicalFrame :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) higgsCanonicalFrame {H : Fin 2 → ℂ | H ≠ 0} := by
  let S : Set (Fin 2 → ℂ) := {H | H ≠ 0}
  have hn : ∀ H ∈ S, abelianHiggsSpinorNormSq H ≠ 0 := by
    intro H hH
    exact (higgs_normSq_eq_zero_iff H).not.mpr hH
  have hr : ContDiffOn ℝ (⊤ : WithTop ℕ∞)
      (fun H => Real.sqrt (abelianHiggsSpinorNormSq H)) S :=
    contDiff_higgsNormSq.contDiffOn.sqrt hn
  have hd : ContDiffOn ℝ (⊤ : WithTop ℕ∞)
      (fun H => (Real.sqrt (abelianHiggsSpinorNormSq H) : ℂ)) S :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hr
  have hdne : ∀ H ∈ S, (Real.sqrt (abelianHiggsSpinorNormSq H) : ℂ) ≠ 0 := by
    intro H hH
    exact (higgs_radial_amplitude_eq_zero_iff H).not.mpr hH
  have hq (i : Fin 2) : ContDiffOn ℝ (⊤ : WithTop ℕ∞)
      (fun H => H i / (Real.sqrt (abelianHiggsSpinorNormSq H) : ℂ)) S := by
    simp only [div_eq_mul_inv]
    exact (by fun_prop : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun H : Fin 2 → ℂ => H i) S).mul
      (hd.fun_inv hdne)
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    dsimp [higgsCanonicalFrame,spinFlipQuaternionMatrix]
  · exact hq 0
  · have hc := Complex.conjCLE.contDiff.comp_contDiffOn (hq 1)
    exact hc.neg
  · exact hq 1
  · exact Complex.conjCLE.contDiff.comp_contDiffOn (hq 0)

/-- The explicit smooth frame is equivariant under the actual weak gauge action. -/
theorem higgsCanonicalFrame_gauge_covariance
    (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) (H : Fin 2 → ℂ) :
    higgsCanonicalFrame ((A : Matrix (Fin 2) (Fin 2) ℂ).mulVec H) =
      (A : Matrix (Fin 2) (Fin 2) ℂ) * higgsCanonicalFrame H := by
  have hn := (higgs_norm_eq_iff_specialUnitary_orbit H
    ((A : Matrix (Fin 2) (Fin 2) ℂ).mulVec H)).mpr ⟨A,A.property,rfl⟩
  rw [higgsCanonicalFrame,higgsCanonicalFrame,← hn]
  obtain ⟨a,b,hA⟩ := specialUnitary_quaternionic_matrix_form A
  rw [hA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinFlipQuaternionMatrix,Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_two]
  all_goals ring

end GaloisForLFunctions.HTGeometry
