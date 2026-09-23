import GaloisForLFunctions.HTGeometry.GammaIterationFirstJetBoundaryAlgebra
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Dominant derivative boundary for Gamma first jets

The reciprocal Riccati relation mixes derivative degrees.  Therefore it disappears after one first
takes the maximal total derivative degree of a polynomial relation.  This file makes that grading
argument exact.  On each derivative-homogeneous slice the full first-jet factorial boundary is
injective, and its image is an explicit nonzero polynomial in the preceding first-jet coordinates.
-/

namespace GaloisForLFunctions

noncomputable section

def firstJetDerivativeWeight (i : Fin k × Fin 2) : ℕ :=
  Fin.cases 1 (fun _ => 0) i.2

def firstJetDerivativeDegree (a : (Fin k × Fin 2) →₀ ℕ) : ℕ :=
  Finsupp.weight firstJetDerivativeWeight a

theorem firstJetDerivativeDegree_eq (a : (Fin (k + 1) × Fin 2) →₀ ℕ) :
    firstJetDerivativeDegree a =
      a (0, 0) + ∑ j : Fin k, a (j.succ, 0) := by
  rw [firstJetDerivativeDegree, Finsupp.weight_apply,
    Finsupp.sum_fintype, Fintype.sum_prod_type, Fin.sum_univ_succ]
  · simp [firstJetDerivativeWeight, Fin.sum_univ_two]
  · intro i
    simp

def firstJetBoundaryExponent (a : (Fin (k + 1) × Fin 2) →₀ ℕ) :
    GammaIterateFirstJetIndex k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => match i with
    | Sum.inl _ => a (0, 1) + 2 * firstJetDerivativeDegree a
    | Sum.inr (j, slot) => a (j.succ, slot)

theorem firstJetBoundaryExponent_apply_point
    (a : (Fin (k + 1) × Fin 2) →₀ ℕ) :
    firstJetBoundaryExponent a (Sum.inl 0) =
      a (0, 1) + 2 * firstJetDerivativeDegree a := rfl

theorem firstJetBoundaryExponent_apply_rest
    (a : (Fin (k + 1) × Fin 2) →₀ ℕ) (j : Fin k) (slot : Fin 2) :
    firstJetBoundaryExponent a (Sum.inr (j, slot)) = a (j.succ, slot) := rfl

theorem firstJetBoundaryExponent_injective_of_degree_eq
    {a b : (Fin (k + 1) × Fin 2) →₀ ℕ}
    (hdeg : firstJetDerivativeDegree a = firstJetDerivativeDegree b)
    (hab : firstJetBoundaryExponent a = firstJetBoundaryExponent b) : a = b := by
  apply Finsupp.ext
  rintro ⟨j, slot⟩
  induction j using Fin.cases with
  | zero =>
      induction slot using Fin.cases with
      | zero =>
          have hrest : (∑ j : Fin k, a (j.succ, 0)) =
              ∑ j : Fin k, b (j.succ, 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact congrArg (fun c => c (Sum.inr (j, 0))) hab
          rw [firstJetDerivativeDegree_eq, firstJetDerivativeDegree_eq, hrest] at hdeg
          exact Nat.add_right_cancel hdeg
      | succ slot =>
          have hslot : slot = 0 := Subsingleton.elim _ _
          subst slot
          have hp := congrArg (fun c => c (Sum.inl (0 : Fin 1))) hab
          simp only [firstJetBoundaryExponent_apply_point, hdeg] at hp
          exact Nat.add_right_cancel hp
  | succ j =>
      exact congrArg (fun c => c (Sum.inr (j, slot))) hab

noncomputable def firstJetHomogeneousBoundaryForm
    (P : MvPolynomial (Fin (k + 1) × Fin 2) ℂ) :
    MvPolynomial (GammaIterateFirstJetIndex k) ℂ :=
  ∑ a ∈ P.support,
    MvPolynomial.monomial (firstJetBoundaryExponent a) (MvPolynomial.coeff a P)

/-- The first-jet boundary is injective on every fixed total derivative degree. -/
theorem firstJetHomogeneousBoundaryForm_ne_zero
    {P : MvPolynomial (Fin (k + 1) × Fin 2) ℂ} {d : ℕ}
    (hP : P ≠ 0)
    (hh : MvPolynomial.IsWeightedHomogeneous firstJetDerivativeWeight P d) :
    firstJetHomogeneousBoundaryForm P ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := MvPolynomial.support_nonempty.mpr hP
  intro hzero
  have hcoeff := congrArg
    (MvPolynomial.coeff (firstJetBoundaryExponent b)) hzero
  rw [firstJetHomogeneousBoundaryForm, MvPolynomial.coeff_sum] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single b] at hcoeff
  · rw [MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
    exact (MvPolynomial.mem_support_iff.mp hb) hcoeff
  · intro a ha hab
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro heq
    apply hab
    apply firstJetBoundaryExponent_injective_of_degree_eq
    · exact (hh (MvPolynomial.mem_support_iff.mp ha)).trans
        (hh (MvPolynomial.mem_support_iff.mp hb)).symm
    · exact heq
  · intro hbnot
    exact (hbnot hb).elim

theorem eval_monomial_firstJetBoundaryExponent
    (a : (Fin (k + 1) × Fin 2) →₀ ℕ) (c : ℂ) (z : ℂ)
    (r : Fin k × Fin 2 → ℂ) :
    MvPolynomial.eval (fun i => i.elim (fun _ => z) r)
        (MvPolynomial.monomial (firstJetBoundaryExponent a) c) =
      MvPolynomial.eval (fun i => Fin.cases
        (Fin.cases (z ^ (2 : ℕ)) (fun _ => z) i.2)
        (fun j => Fin.cases (z ^ (2 : ℕ) * r (j, 0))
          (fun _ => r (j, 1)) i.2) i.1)
        (MvPolynomial.monomial a c) := by
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  congr 1
  classical
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · simp only [Fintype.prod_sum_type, Fintype.prod_prod_type,
      Fin.prod_univ_succ, firstJetBoundaryExponent,
      firstJetDerivativeDegree_eq, pow_add, mul_pow, Finset.prod_mul_distrib,
      Finsupp.coe_equivFunOnFinite_symm,
      Sum.elim_inl, Sum.elim_inr, Fin.cases_zero,
      Fin.cases_succ]
    have hzprod : (∏ x : Fin k, (z ^ (2 : ℕ)) ^ a (x.succ, 0)) =
        (z ^ (2 : ℕ)) ^ ∑ x : Fin k, a (x.succ, 0) := by
      simpa using Finset.prod_pow_eq_pow_sum Finset.univ
        (fun x : Fin k => a (x.succ, 0)) (z ^ (2 : ℕ))
    rw [hzprod, ← pow_mul, ← pow_mul]
    rw [mul_add, pow_add]
    simp
    ring
  · intro i
    simp
  · intro i
    simp

theorem eval_firstJetHomogeneousBoundaryForm
    (P : MvPolynomial (Fin (k + 1) × Fin 2) ℂ) (z : ℂ)
    (r : Fin k × Fin 2 → ℂ) :
    MvPolynomial.eval (fun i => i.elim (fun _ => z) r)
        (firstJetHomogeneousBoundaryForm P) =
      MvPolynomial.eval (fun i => Fin.cases
        (Fin.cases (z ^ (2 : ℕ)) (fun _ => z) i.2)
        (fun j => Fin.cases (z ^ (2 : ℕ) * r (j, 0))
          (fun _ => r (j, 1)) i.2) i.1) P := by
  classical
  rw [firstJetHomogeneousBoundaryForm, map_sum]
  conv_rhs => rw [MvPolynomial.as_sum P, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact eval_monomial_firstJetBoundaryExponent a (MvPolynomial.coeff a P) z r

theorem eval_firstJetHomogeneousBoundaryForm_gamma
    (P : MvPolynomial (Fin (k + 1) × Fin 2) ℂ) (z : ℂ) :
    MvPolynomial.eval (gammaIterateFirstJetTuple k z)
        (firstJetHomogeneousBoundaryForm P) =
      MvPolynomial.eval (gammaFirstJetBoundaryTail k z) P := by
  rw [show gammaIterateFirstJetTuple k z =
      fun i => i.elim (fun _ => z)
        (fun j => gammaIterateFirstJetTuple k z (Sum.inr j)) by
    funext i
    rcases i with (i | i) <;> rfl]
  rw [eval_firstJetHomogeneousBoundaryForm]
  apply congrArg (fun h => MvPolynomial.eval h P)
  funext i
  rcases i with ⟨j, slot⟩
  induction j using Fin.cases with
  | zero =>
      induction slot using Fin.cases with
      | zero =>
          simp [gammaFirstJetBoundaryTail, gammaFirstJetCompositionTail,
            gammaFirstJetCompositionData, gammaIterate, iteratedDeriv_one]
      | succ slot =>
          have hslot : slot = 0 := Subsingleton.elim _ _
          subst slot
          simp [gammaFirstJetBoundaryTail, gammaFirstJetCompositionTail,
            gammaFirstJetCompositionData, gammaIterate]
  | succ j =>
      induction slot using Fin.cases with
      | zero =>
          simp [gammaFirstJetBoundaryTail, gammaFirstJetCompositionTail,
            gammaFirstJetCompositionData, gammaIterateFirstJetTuple]
      | succ slot =>
          have hslot : slot = 0 := Subsingleton.elim _ _
          subst slot
          simp [gammaFirstJetBoundaryTail, gammaFirstJetCompositionTail,
            gammaFirstJetCompositionData, gammaIterateFirstJetTuple]

def firstJetPointExponent
    (a : GammaIterateFirstJetIndex k →₀ ℕ) : ℕ := a (Sum.inl 0)

def firstJetTailExponent
    (a : GammaIterateFirstJetIndex k →₀ ℕ) : (Fin k × Fin 2) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => a (Sum.inr i)

def firstJetFullDerivativeDegree
    (a : GammaIterateFirstJetIndex k →₀ ℕ) : ℕ :=
  firstJetDerivativeDegree (firstJetTailExponent a)

theorem firstJetExponent_eq_of_point_tail_eq
    {a b : GammaIterateFirstJetIndex k →₀ ℕ}
    (hp : firstJetPointExponent a = firstJetPointExponent b)
    (ht : firstJetTailExponent a = firstJetTailExponent b) : a = b := by
  apply Finsupp.ext
  intro i
  rcases i with (i | i)
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa [firstJetPointExponent] using hp
  · exact congrArg (fun c => c i) ht

def firstJetTopDerivativeDegree
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ) : ℕ :=
  P.support.sup firstJetFullDerivativeDegree

def firstJetTopDerivativeSupport
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ) :=
  P.support.filter fun a =>
    firstJetFullDerivativeDegree a = firstJetTopDerivativeDegree P

def firstJetTopPointDegree
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ) : ℕ :=
  (firstJetTopDerivativeSupport P).sup firstJetPointExponent

def firstJetDominantTailPolynomial
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ) :
    MvPolynomial (Fin k × Fin 2) ℂ :=
  ∑ a ∈ (firstJetTopDerivativeSupport P).filter fun a =>
      firstJetPointExponent a = firstJetTopPointDegree P,
    MvPolynomial.monomial (firstJetTailExponent a)
      ((-1 : ℂ) ^ firstJetTopPointDegree P * MvPolynomial.coeff a P)

theorem exists_firstJetDominantExponent
    {P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ} (hP : P ≠ 0) :
    ∃ a ∈ P.support,
      firstJetFullDerivativeDegree a = firstJetTopDerivativeDegree P ∧
      firstJetPointExponent a = firstJetTopPointDegree P := by
  have hsupp : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  obtain ⟨a, ha, haD⟩ := Finset.exists_mem_eq_sup P.support hsupp
    firstJetFullDerivativeDegree
  have haTop : a ∈ firstJetTopDerivativeSupport P := by
    exact Finset.mem_filter.mpr ⟨ha, haD.symm⟩
  have htopSupp : (firstJetTopDerivativeSupport P).Nonempty := ⟨a, haTop⟩
  obtain ⟨b, hb, hbp⟩ := Finset.exists_mem_eq_sup
    (firstJetTopDerivativeSupport P) htopSupp firstJetPointExponent
  exact ⟨b, (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2, hbp.symm⟩

theorem firstJetDominantTailPolynomial_ne_zero
    {P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ} (hP : P ≠ 0) :
    firstJetDominantTailPolynomial P ≠ 0 := by
  classical
  obtain ⟨b, hb, hbD, hbp⟩ := exists_firstJetDominantExponent hP
  have hbTop : b ∈ (firstJetTopDerivativeSupport P).filter fun a =>
      firstJetPointExponent a = firstJetTopPointDegree P :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hb, hbD⟩, hbp⟩
  intro hzero
  have hcoeff := congrArg (MvPolynomial.coeff (firstJetTailExponent b)) hzero
  rw [firstJetDominantTailPolynomial, MvPolynomial.coeff_sum] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single b] at hcoeff
  · rw [MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
    exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (MvPolynomial.mem_support_iff.mp hb)) hcoeff
  · intro a ha hab
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro htail
    apply hab
    apply firstJetExponent_eq_of_point_tail_eq
    · exact (Finset.mem_filter.mp ha).2.trans hbp.symm
    · exact htail
  · intro hbnot
    exact (hbnot hbTop).elim

theorem firstJetDominantTailPolynomial_isWeightedHomogeneous
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ) :
    MvPolynomial.IsWeightedHomogeneous firstJetDerivativeWeight
      (firstJetDominantTailPolynomial P) (firstJetTopDerivativeDegree P) := by
  classical
  rw [firstJetDominantTailPolynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro a ha
  apply MvPolynomial.isWeightedHomogeneous_monomial
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2

end

end GaloisForLFunctions
