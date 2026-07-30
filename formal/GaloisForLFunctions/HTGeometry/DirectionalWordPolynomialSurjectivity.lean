import GaloisForLFunctions.HTGeometry.DirectionalProjectiveCompleteRealization
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.List.OfFn

/-!
# Ordered words span every homogeneous law polynomial

The commutative collapse from ordered words of length `n` to degree-`n` monomials is surjective.
This is the remaining algebraic bridge from the complete word-tree horizon theorem to arbitrary
projective algebraic sets.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

universe u v

variable {K : Type u} {ι : Type v} [Field K] [Fintype ι]

/-- The commutative exponent vector of an ordered word. -/
def projectiveWordExponent {n : ℕ} (w : Fin n → ι) : ι →₀ ℕ :=
  ∑ r, Finsupp.single (w r) 1

/-- Turning the exponent vector back into a multiset forgets exactly the ordering of the word. -/
theorem toMultiset_projectiveWordExponent : ∀ {n : ℕ} (w : Fin n → ι),
    Finsupp.toMultiset (projectiveWordExponent w) = (List.ofFn w : Multiset ι) := by
  intro n
  induction n with
  | zero =>
      intro w
      simp [projectiveWordExponent]
  | succ n ih =>
      intro w
      rw [← Fin.cons_self_tail w]
      simp only [projectiveWordExponent, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Finsupp.toMultiset_add, Finsupp.toMultiset_single]
      change 1 • {w 0} + Finsupp.toMultiset (projectiveWordExponent (Fin.tail w)) = _
      rw [ih (Fin.tail w), List.ofFn_cons]
      rfl

/-- The total degree of a word exponent is its word length. -/
@[simp]
theorem projectiveWordExponent_sum {n : ℕ} (w : Fin n → ι) :
    (projectiveWordExponent w).sum (fun _ e ↦ e) = n := by
  have hcard := congrArg Multiset.card (toMultiset_projectiveWordExponent w)
  simpa using! hcard

/-- The commutative monomial attached to a word is the monomial of its exponent vector. -/
theorem projectiveWordMonomial_eq_monomial {n : ℕ} (w : Fin n → ι) :
    (∏ r, MvPolynomial.X (w r) : MvPolynomial ι K) =
      MvPolynomial.monomial (projectiveWordExponent w) 1 := by
  induction n with
  | zero => simp [projectiveWordExponent]
  | succ n ih =>
      rw [← Fin.cons_self_tail w, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [ih (Fin.tail w)]
      simp only [projectiveWordExponent, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [show Finsupp.single (w 0) 1 + ∑ r, Finsupp.single (Fin.tail w r) 1 =
          (∑ r, Finsupp.single (Fin.tail w r) 1) + Finsupp.single (w 0) 1 by
            exact add_comm _ _]
      rw [MvPolynomial.monomial_add_single]
      simp [mul_comm]

/-- Every finite-support exponent vector of total degree `n` is represented by an ordered word of
length `n`. -/
theorem exists_projectiveWordExponent_eq
    (s : ι →₀ ℕ) (n : ℕ) (hs : s.sum (fun _ e ↦ e) = n) :
    ∃ w : Fin n → ι, projectiveWordExponent w = s := by
  classical
  let l : List ι := (Finsupp.toMultiset s).toList
  have hcard : Multiset.card (Finsupp.toMultiset s) = n := by
    simpa [Function.id_def] using hs
  have hl : l.length = n := by simpa [l] using hcard
  cases hl
  refine ⟨l.get, ?_⟩
  rw [← Finsupp.toMultiset_toFinsupp (projectiveWordExponent l.get),
    ← Finsupp.toMultiset_toFinsupp s]
  congr 1
  rw [toMultiset_projectiveWordExponent, List.ofFn_get]
  exact Multiset.coe_toList _

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

universe u v

variable {K : Type u} {ι η : Type v} [Field K] [Fintype ι]

/-- Every homogeneous commutative law polynomial is the collapse of ordered-word coefficients of
its degree.  No ordering on the variable type is required: one representative word is chosen for
each exponent in the finite support. -/
theorem exists_wordCoefficients_sum_eq_homogeneousPolynomial
    (P : MvPolynomial ι K) (n : ℕ) (hP : P.IsHomogeneous n) :
    ∃ b : (Fin n → ι) → K,
      ∑ w, MvPolynomial.C (b w) * ∏ r, MvPolynomial.X (w r) = P := by
  classical
  let S := {s : ι →₀ ℕ // s ∈ P.support}
  have hdegree (s : S) : s.1.sum (fun _ e ↦ e) = n := by
    simpa [Finsupp.sum] using (hP.degree_eq_sum_deg_support s.2).symm
  let rep : S → (Fin n → ι) := fun s ↦
    Classical.choose (exists_projectiveWordExponent_eq s.1 n (hdegree s))
  have hrep (s : S) : projectiveWordExponent (rep s) = s.1 :=
    Classical.choose_spec (exists_projectiveWordExponent_eq s.1 n (hdegree s))
  let b : (Fin n → ι) → K := fun w ↦
    ∑ s : S, if rep s = w then P.coeff s.1 else 0
  refine ⟨b, ?_⟩
  calc
    (∑ w, MvPolynomial.C (b w) * ∏ r, MvPolynomial.X (w r)) =
        ∑ w, MvPolynomial.C (b w) *
          MvPolynomial.monomial (projectiveWordExponent w) 1 := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [projectiveWordMonomial_eq_monomial]
    _ = ∑ w, MvPolynomial.monomial (projectiveWordExponent w) (b w) := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [MvPolynomial.C_mul_monomial, mul_one]
    _ = ∑ w, ∑ s : S,
          if rep s = w then MvPolynomial.monomial s.1 (P.coeff s.1) else 0 := by
          apply Finset.sum_congr rfl
          intro w hw
          change MvPolynomial.monomial (projectiveWordExponent w)
              (∑ s : S, if rep s = w then P.coeff s.1 else 0) = _
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro s hs
          split_ifs with h
          · rw [← h, hrep]
          · simp
    _ = ∑ s : S, MvPolynomial.monomial s.1 (P.coeff s.1) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s hs
          exact Fintype.sum_ite_eq (rep s) _
    _ = ∑ s ∈ P.support, MvPolynomial.monomial s (P.coeff s) := by
          symm
          exact Finset.sum_subtype P.support (fun _ ↦ Iff.rfl) _
    _ = P := MvPolynomial.support_sum_monomial_coeff P

/-- Simultaneous ordered-word realization of every common-degree homogeneous law family. -/
theorem exists_projectiveWordCoefficients_lawPolynomials_eq
    (P : η → MvPolynomial ι K) (n : ℕ)
    (hP : ∀ j, (P j).IsHomogeneous n) :
    ∃ a : η → ProjectiveWordState ι → K,
      ∀ j, projectiveWordLawPolynomial a j n = P j := by
  classical
  choose b hb using fun j ↦
    exists_wordCoefficients_sum_eq_homogeneousPolynomial (P j) n (hP j)
  let a : η → ProjectiveWordState ι → K := fun j s ↦
    if h : s.1 = n then b j (h ▸ s.2) else 0
  refine ⟨a, ?_⟩
  intro j
  simpa [projectiveWordLawPolynomial, a] using hb j

variable [Fintype η]

/-- **Every common-degree projective algebraic set is a complete hypertranscendence horizon.**
For any finite family of homogeneous equations of one positive degree, there is a rational
function field, a finite derivation pencil, and one root observable whose complete directional jet
is algebraically dependent at a nonzero law direction exactly on their simultaneous zero locus. -/
theorem exists_completeJet_horizon_eq_homogeneousZeroLocus
    (P : η → MvPolynomial ι K) (n : ℕ)
    (hP : ∀ j, (P j).IsHomogeneous (n + 1)) :
    ∃ a : η → ProjectiveWordState ι → K,
      ∀ (c : ι → K), (∃ i, c i ≠ 0) →
        ((¬ AlgebraicIndependent K
            (fun r : ℕ ↦ directionalJet (projectiveCompleteDerivation a (n + 1)) c r
              (projectiveCompleteRoot (K := K) (ι := ι) (η := η)))) ↔
          ∀ j, MvPolynomial.eval c (P j) = 0) := by
  obtain ⟨a, ha⟩ :=
    exists_projectiveWordCoefficients_lawPolynomials_eq P (n + 1) hP
  refine ⟨a, ?_⟩
  intro c hc
  rw [projectiveCompleteJet_dependent_iff_lawPolynomials_zero a n c hc]
  simp_rw [ha]

end

end GaloisForLFunctions.HTGeometry
