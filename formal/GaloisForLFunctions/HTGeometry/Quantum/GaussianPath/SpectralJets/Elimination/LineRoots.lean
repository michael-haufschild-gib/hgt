import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Finite real cuts for a polynomial restricted to an affine line -/

open MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι : Type*}

/-- Substitute a univariate polynomial for each parameter. -/
def linePolynomial (z : ι → Polynomial ℂ) (p : MvPolynomial ι ℂ) : Polynomial ℂ :=
  eval₂ Polynomial.C z p

theorem eval_linePolynomial (z : ι → Polynomial ℂ) (p : MvPolynomial ι ℂ) (t : ℂ) :
    (linePolynomial z p).eval t = eval (fun i => (z i).eval t) p := by
  have he : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by ext; simp
  rw [linePolynomial,polynomial_eval_eval₂,he]
  rfl

/-- Affine substitution preserves the total-degree upper bound. -/
theorem linePolynomial_degree [Fintype ι] (z : ι → Polynomial ℂ)
    (hz : ∀ i, (z i).natDegree ≤ 1) (p : MvPolynomial ι ℂ) :
    (linePolynomial z p).natDegree ≤ p.totalDegree := by
  classical
  rw [linePolynomial,eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  apply Polynomial.natDegree_mul_le.trans
  rw [Polynomial.natDegree_C,zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  have he (i : ι) : ((z i)^(s i)).natDegree ≤ s i :=
    Polynomial.natDegree_pow_le.trans ((Nat.mul_le_mul_left _ (hz i)).trans_eq (Nat.mul_one _))
  apply (Finset.sum_le_sum fun i _ => he i).trans
  have hsum : ∑ i, s i = s.sum fun _ e => e := by
    rw [Finsupp.sum_fintype]
    intro i
    rfl
  exact hsum.trans_le (le_totalDegree hs)

/-- Real parts of the roots cover every real zero, with at most one cut per degree. -/
def lineCuts (p : Polynomial ℂ) : Finset ℝ := p.roots.toFinset.image Complex.re

theorem lineCuts_card (p : Polynomial ℂ) : (lineCuts p).card ≤ p.natDegree :=
  Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _))

theorem mem_lineCuts {p : Polynomial ℂ} (hp : p ≠ 0) {t : ℝ} (h : p.eval (t:ℂ) = 0) :
    t ∈ lineCuts p := by
  apply Finset.mem_image.mpr
  exact ⟨(t:ℂ),Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr h),rfl⟩

#print axioms linePolynomial_degree
#print axioms mem_lineCuts
end
end GaloisForLFunctions.HTGeometry.SpectralJets
