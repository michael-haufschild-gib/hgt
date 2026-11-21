import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

/-! # Polynomial numerators of mixed derivatives of an implicit root

The variable indexed by `none` is the root. The variables indexed by
`some i` are the independent parameters. All operations are integral.
-/
open MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι R : Type*} [CommRing R]

/-- Differentiation tangent to the polynomial level set, multiplied by
the root partial derivative. -/
def tangent (p : MvPolynomial (Option ι) R) (i : ι) (b : MvPolynomial (Option ι) R) :=
  pderiv none p * pderiv (some i) b - pderiv (some i) p * pderiv none b

/-- Differentiating a quotient with denominator the root partial to power
2j gives this numerator with denominator the root partial to power 2j+2. -/
def numerator (p : MvPolynomial (Option ι) R) : List ι → MvPolynomial (Option ι) R
  | [] => X none
  | i :: w => pderiv none p * tangent p i (numerator p w) -
      (2*w.length) • (numerator p w * tangent p i (pderiv none p))

/-- Put derivatives of different orders over the same denominator. -/
def cleared (p : MvPolynomial (Option ι) R) (L : ℕ) (w : List ι) :=
  (pderiv none p)^(2*(L-w.length))*numerator p w

theorem totalDegree_partial_le {σ : Type*} (i : σ) (p : MvPolynomial σ R) :
    (pderiv i p).totalDegree ≤ p.totalDegree := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := mem_support_iff.mp hm
  rw [coeff_pderiv] at hc
  have hm' : m + Finsupp.single i 1 ∈ p.support :=
    mem_support_iff.mpr (fun h => hc (by rw [h,zero_mul]))
  have h := le_totalDegree hm'
  simp [Finsupp.sum_add_index'] at h
  omega

private theorem tangent_degree (p b : MvPolynomial (Option ι) R) (i : ι) :
    (tangent p i b).totalDegree ≤ p.totalDegree + b.totalDegree := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans (Nat.add_le_add (totalDegree_partial_le _ _) (totalDegree_partial_le _ _))
  · exact (totalDegree_mul _ _).trans (Nat.add_le_add (totalDegree_partial_le _ _) (totalDegree_partial_le _ _))

/-- Each differentiation increases the total degree by at most twice the
degree of the defining polynomial, independently of the number of roots. -/
theorem numerator_degree [Nontrivial R] (p : MvPolynomial (Option ι) R) (w : List ι) :
    (numerator p w).totalDegree ≤ 1 + 2*w.length*p.totalDegree := by
  induction w with
  | nil => simp [numerator]
  | cons i w ih =>
    rw [numerator]
    apply (totalDegree_sub _ _).trans
    have h₁ := totalDegree_partial_le (none : Option ι) p
    have h₂ := tangent_degree p (numerator p w) i
    have h₃ := tangent_degree p (pderiv none p) i
    simp only [List.length_cons,Nat.mul_add,Nat.add_mul]
    apply max_le
    · exact (totalDegree_mul _ _).trans (by omega)
    · exact (totalDegree_smul_le _ _).trans ((totalDegree_mul _ _).trans (by omega))

theorem cleared_degree [Nontrivial R] (p : MvPolynomial (Option ι) R)
    (L : ℕ) (w : List ι) (hw : w.length ≤ L) :
    (cleared p L w).totalDegree ≤ 1 + 2*L*p.totalDegree := by
  apply (totalDegree_mul _ _).trans
  have h := (totalDegree_pow (pderiv none p) (2*(L-w.length))).trans
    (Nat.mul_le_mul_left _ (totalDegree_partial_le none p))
  have hn := numerator_degree p w
  have hL : 2*(L-w.length)*p.totalDegree + 2*w.length*p.totalDegree = 2*L*p.totalDegree := by
    rw [← Nat.add_mul,← Nat.mul_add,Nat.sub_add_cancel hw]
  omega

#print axioms cleared_degree
end
end GaloisForLFunctions.HTGeometry.SpectralJets
