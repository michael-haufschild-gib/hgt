import GaloisForLFunctions.HTGeometry.GomesPolynomialFiniteMomentIntegration

/-!
# Finite-moment reconstruction of polynomial exponential profiles

A raw finite polynomial log-density is determined by moments zero through its
comparison degree cutoff. The exact coefficient-moment pairing is strictly positive
on distinct profiles. This turns the reconstruction experiment into a finite
observation theorem on every bounded-degree polynomial sector.
-/

noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Separation is an explicit finite pairing of coefficient and moment differences. -/
theorem gomesPolynomialSeparation_eq_moment_sum (P Q : GomesFinitePolynomialProfile) :
    gomesPolynomialSeparation P Q =
      ∑ n ∈ Finset.range (max P.val.natDegree Q.val.natDegree + 1),
        (P.val - Q.val).coeff n *
          ((∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure P.val)) -
            ∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure Q.val)) := by
  let A : {A : ℝ[X] // A.natDegree ≤ max P.val.natDegree Q.val.natDegree} :=
    ⟨P.val - Q.val, natDegree_sub_le P.val Q.val⟩
  rw [gomesPolynomialSeparation_integral_difference]
  change (∫ x : ℝ, A.val.eval x ∂(gomesDilatonMeasure P.val)) -
    (∫ x : ℝ, A.val.eval x ∂(gomesDilatonMeasure Q.val)) = _
  rw [gomesPolynomialMeasure_integral_eval_prefix P _ A,
    gomesPolynomialMeasure_integral_eval_prefix Q _ A, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  change A.val.coeff n * _ - A.val.coeff n * _ = A.val.coeff n * (_ - _)
  ring

/-- The finite coefficient-moment pairing is strictly positive exactly off the diagonal. -/
theorem gomesPolynomialMomentPairing_pos_iff (P Q : GomesFinitePolynomialProfile) :
    (0 < ∑ n ∈ Finset.range (max P.val.natDegree Q.val.natDegree + 1),
      (P.val - Q.val).coeff n *
        ((∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure P.val)) -
          ∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure Q.val))) ↔ P ≠ Q := by
  rw [← gomesPolynomialSeparation_eq_moment_sum, gomesPolynomialSeparation_pos_iff]

/-- A finite raw moment prefix determines the entire polynomial log-density. -/
theorem gomesPolynomialMeasure_finite_moments_reconstruct (P Q : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, n ≤ max P.val.natDegree Q.val.natDegree →
      (∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure P.val)) =
        ∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure Q.val)) ↔ P = Q := by
  constructor
  · intro h
    apply (gomesPolynomialSeparation_zero_iff P Q).mp
    rw [gomesPolynomialSeparation_eq_moment_sum]
    apply Finset.sum_eq_zero
    intro n hn
    rw [h n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)), sub_self, mul_zero]
  · rintro rfl n _
    rfl

/-- Distinct profiles are distinguished by some moment within the explicit degree cutoff. -/
theorem gomesPolynomialMeasure_distinguishing_finite_moment (P Q : GomesFinitePolynomialProfile) :
    P ≠ Q ↔ ∃ n : ℕ, n ≤ max P.val.natDegree Q.val.natDegree ∧
      (∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure P.val)) ≠
        ∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure Q.val) := by
  classical
  constructor
  · intro h
    by_contra hn
    apply h
    apply (gomesPolynomialMeasure_finite_moments_reconstruct P Q).mp
    intro n hd
    by_contra he
    exact hn ⟨n, hd, he⟩
  · rintro ⟨n, _, hn⟩ h
    subst Q
    exact hn rfl

/-- The finite polynomial sector with a fixed degree bound. -/
abbrev GomesBoundedPolynomialProfile (d : ℕ) :=
  {P : GomesFinitePolynomialProfile // P.val.natDegree ≤ d}

/-- A finite vector of raw moments, including total mass. -/
def gomesBoundedPolynomialMomentRecord (d : ℕ) (P : GomesBoundedPolynomialProfile d) :
    Fin (d + 1) → ℝ :=
  fun n => ∫ x : ℝ, x ^ n.val ∂(gomesDilatonMeasure P.val.val)

/-- The finite moment vector is injective on every bounded-degree profile sector. -/
theorem gomesBoundedPolynomialMomentRecord_injective (d : ℕ) :
    Function.Injective (gomesBoundedPolynomialMomentRecord d) := by
  intro P Q h
  apply Subtype.ext
  apply (gomesPolynomialMeasure_finite_moments_reconstruct P.val Q.val).mp
  intro n hn
  have hd : n ≤ d := hn.trans (max_le P.property Q.property)
  exact congrFun h ⟨n, Nat.lt_succ_of_le hd⟩

end GaloisForLFunctions.HTGeometry
