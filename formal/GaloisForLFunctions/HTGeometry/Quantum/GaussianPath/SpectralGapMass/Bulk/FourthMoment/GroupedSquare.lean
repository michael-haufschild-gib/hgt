import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.FourthMoment.ProductMultiplicity
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum

/-! # Pauli coefficients of the squared physical path Hamiltonian -/

open Finset Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.FourthMoment
noncomputable section

/-- Contribution of one ordered pair to the Pauli expansion of the square. -/
def pairWeight {n : ℕ} (u : PathShell n) (z : PathLabel n × PathLabel n) : ℂ :=
  ((u z.1*u z.2:ℝ):ℂ)*optPhaseProd (pathWord z.1) (pathWord z.2)

def squareWeight {n : ℕ} (u : PathShell n) (Q : Word n) := ∑ z ∈ factors Q, pairWeight u z

theorem norm_pairWeight {n : ℕ} (u : PathShell n) (z : PathLabel n × PathLabel n) :
    ‖pairWeight u z‖=|u z.1*u z.2| := by
  rw [pairWeight,norm_mul,norm_optPhaseProd,mul_one,Complex.norm_real,Real.norm_eq_abs]

/-- Grouping by product word counts each ordered factorization exactly once. -/
theorem sum_factors {n : ℕ} {M : Type*} [AddCommMonoid M] (f : PathLabel n × PathLabel n → M) :
    (∑ Q : Word n, ∑ z ∈ factors Q, f z)=∑ z, f z := by
  classical
  simp only [factors,sum_filter]
  rw [sum_comm]
  simp

theorem square_expansion {n : ℕ} (u : PathShell n) :
    pathHamiltonian u^2=∑ Q, squareWeight u Q • finitePauliMatrix Q := by
  classical
  let F (z : PathLabel n × PathLabel n) := pairWeight u z • finitePauliMatrix (productWord z)
  have he : pathHamiltonian u^2=∑ z, F z := by
    rw [sq,pathHamiltonian_eq_sum,sum_mul,Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm,finitePauliMatrix_mul',smul_smul]
    simp only [F,pairWeight,productWord,Complex.ofReal_mul]
  rw [he,←sum_factors F]
  refine sum_congr rfl fun Q _ => ?_
  rw [squareWeight,sum_smul]
  apply sum_congr rfl
  intro z hz
  have hQ := (mem_filter.mp hz).2
  dsimp only [F]
  rw [show productWord z=Q from hQ]

private theorem identity_product {n : ℕ} (i j : PathLabel n) :
    productWord (i,j)=pauliIdentityLabel (n+2) ↔ i=j := by
  constructor
  · intro h
    apply pathWord_injective
    funext s
    exact (optMul_eq_none_iff ..).mp (congrFun h s)
  · rintro rfl
    funext s
    exact optMul_self _

/-- Only the identical-factor pairs contribute to the identity word. -/
theorem sum_identity {n : ℕ} {M : Type*} [AddCommMonoid M] (f : PathLabel n × PathLabel n → M) :
    (∑ z ∈ factors (pauliIdentityLabel (n+2)), f z)=∑ i, f (i,i) := by
  classical
  simp only [factors,sum_filter,Fintype.sum_prod_type,identity_product]
  simp

theorem identity_weight {n : ℕ} (u : PathShell n) :
    squareWeight u (pauliIdentityLabel (n+2))=((∑ i, u i^2:ℝ):ℂ) := by
  rw [squareWeight,sum_identity,Complex.ofReal_sum]
  apply sum_congr rfl
  intro i _
  simp [pairWeight,optPhaseProd,optPhase_self,sq]

/-- The squared Pauli coefficients of the square give the fourth spectral moment. -/
theorem fourth_energy {n : ℕ} (u : PathShell n) :
    (∑ j, (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues j^4)=
      (2:ℝ)^(n+2)*∑ Q, ‖squareWeight u Q‖^2 := by
  rw [sum_pow_eigenvalues_eq_trace_pow_re']
  have h := ofReal_frobSq_eq_trace (pathHamiltonian u^2)
  rw [star_pow,(isSelfAdjoint_pathHamiltonian u).star_eq,←pow_add] at h
  have htr := congrArg Complex.re h
  change frobSq (pathHamiltonian u^2)=(pathHamiltonian u^4).trace.re at htr
  rw [←htr,square_expansion,frobSq_pauliCombination,Fintype.card_fin]

#print axioms fourth_energy
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.FourthMoment
