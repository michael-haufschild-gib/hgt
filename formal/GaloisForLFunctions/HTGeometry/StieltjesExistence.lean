import GaloisForLFunctions.HTGeometry.HamburgerExistence
import GaloisForLFunctions.HTGeometry.LimitCarrier
import GaloisForLFunctions.HTGeometry.StieltjesMomentProblem
import GaloisForLFunctions.HTGeometry.RootCofactor

/-!
# Existence in the strict Stieltjes moment problem

This module proves the sufficient direction of the Stieltjes criterion for a strictly positive
ordinary moment form and a semidefinite shifted form.  Shifted positivity forces every Gaussian
quadrature node onto `[0,∞)`; Prokhorov compactness then produces a representing probability
measure, and portmanteau preserves the half-line support.
-/

open scoped BigOperators
open MeasureTheory Filter Polynomial Set

namespace HTGeometry

variable {s : ℕ → ℝ}

theorem momentFunctional_add_sequence (s r : ℕ → ℝ) (p : Polynomial ℝ) :
    momentFunctional (fun n => s n + r n) p =
      momentFunctional s p + momentFunctional r p := by
  simp only [momentFunctional_eq_support_sum, mul_add, Finset.sum_add_distrib]

theorem momentFunctional_smul_sequence (s : ℕ → ℝ) (c : ℝ) (p : Polynomial ℝ) :
    momentFunctional (fun n => c * s n) p = c * momentFunctional s p := by
  simp only [momentFunctional_eq_support_sum, ← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem momentFunctional_perturb_sequence (s r : ℕ → ℝ) (c : ℝ)
    (p : Polynomial ℝ) :
    momentFunctional (fun n => s n + c * r n) p =
      momentFunctional s p + c * momentFunctional r p := by
  rw [show (fun n => s n + c * r n) =
      fun n => s n + (fun k => c * r k) n by rfl,
    momentFunctional_add_sequence, momentFunctional_smul_sequence]

theorem momentInner_perturb_sequence (s r : ℕ → ℝ) (c : ℝ)
    (p q : Polynomial ℝ) :
    momentInner (fun n => s n + c * r n) p q =
      momentInner s p q + c * momentInner r p q := by
  simp only [momentInner_def, momentFunctional_perturb_sequence]

/-- Adding any positive multiple of a strict reference sequence turns a semidefinite moment
form into a strict one. -/
theorem positiveMomentForm_perturb
    {r : ℕ → ℝ}
    (hs : ∀ p : Polynomial ℝ, 0 ≤ momentInner s p p)
    (hr : PositiveMomentForm r) {c : ℝ} (hc : 0 < c) :
    PositiveMomentForm (fun n => s n + c * r n) := by
  refine ⟨fun p hp => ?_⟩
  rw [momentInner_perturb_sequence]
  exact add_pos_of_nonneg_of_pos (hs p) (mul_pos hc (hr.pos_of_ne_zero p hp))

theorem shiftedMomentForm_nonnegative_perturb
    {r : ℕ → ℝ}
    (hs : ∀ p : Polynomial ℝ, 0 ≤ momentFunctional s (X * p ^ 2))
    (hr : ∀ p : Polynomial ℝ, 0 ≤ momentFunctional r (X * p ^ 2))
    {c : ℝ} (hc : 0 ≤ c) (p : Polynomial ℝ) :
    0 ≤ momentFunctional (fun n => s n + c * r n) (X * p ^ 2) := by
  rw [momentFunctional_perturb_sequence]
  exact add_nonneg (hs p) (mul_nonneg hc (hr p))

/-- Strict Hamburger positivity plus shifted Stieltjes positivity forces every Gaussian
quadrature node onto the nonnegative half-line. -/
theorem monicOrtho_root_nonneg_of_shifted
    (h : PositiveMomentForm s)
    (hshift : ∀ p : Polynomial ℝ,
      0 ≤ momentFunctional s (X * p ^ 2))
    (n : ℕ) {xi : ℝ}
    (hxi : (monicOrtho s (n + 1)).eval xi = 0) :
    0 ≤ xi := by
  obtain ⟨G, hG, _⟩ := exists_cofactor h n hxi
  have hGne : G ≠ 0 := cofactor_ne_zero s n hG
  have hdeg : G.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have hlin : ((X - C xi) : Polynomial ℝ) ≠ 0 := X_sub_C_ne_zero xi
    have hnd : (monicOrtho s (n + 1)).natDegree = 1 + G.natDegree := by
      rw [hG, natDegree_mul hlin hGne, natDegree_X_sub_C]
    have hQnd : (monicOrtho s (n + 1)).natDegree = n + 1 :=
      natDegree_eq_of_degree_eq_some (monicOrtho_degree s (n + 1))
    rw [degree_eq_natDegree hGne]
    exact_mod_cast (by omega : G.natDegree < n + 1)
  have hzero : momentInner s (monicOrtho s (n + 1)) G = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt h (n + 1) (n + 1) le_rfl G hdeg
  have hpoly : ((X - C xi) * G) * G = X * G ^ 2 - xi • G ^ 2 := by
    simp only [Polynomial.smul_eq_C_mul]
    ring
  rw [momentInner_def, hG, hpoly, momentFunctional_sub,
    momentFunctional_smul] at hzero
  have hden : 0 < momentFunctional s (G ^ 2) := by
    rw [← momentInner_self]
    exact h.pos_of_ne_zero G hGne
  nlinarith [hshift G]

theorem gaussNodes_nonnegative_of_shifted
    (h : PositiveMomentForm s)
    (hshift : ∀ p : Polynomial ℝ,
      0 ≤ momentFunctional s (X * p ^ 2))
    (n : ℕ) {xi : ℝ} (hxi : xi ∈ gaussNodes s n) :
    0 ≤ xi := by
  exact monicOrtho_root_nonneg_of_shifted h hshift n
    ((mem_gaussNodes_iff n xi).mp hxi)

/-- Strict Stieltjes existence: a strictly positive Hamburger form whose shifted form is
semidefinite has a representing probability measure supported on `[0,∞)`. -/
theorem exists_probabilityMeasure_hasStieltjesMoments
    (h : PositiveMomentForm s)
    (hshift : ∀ p : Polynomial ℝ,
      0 ≤ momentFunctional s (X * p ^ 2)) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ k : ℕ,
        Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
          ∫ x, x ^ k ∂(μ : Measure ℝ) = (s 0)⁻¹ * s k) ∧
      ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x := by
  obtain ⟨μ, φ, hφ, hlim⟩ := exists_subseq_tendsto_gaussProbMeasure h
  have hopen : ∀ G, IsOpen G →
      (μ : Measure ℝ) G ≤ atTop.liminf fun i => gaussProb s (φ i + 1) G :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  have hmom : ∀ k : ℕ,
      Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
        ∫ x, x ^ k ∂(μ : Measure ℝ) = (s 0)⁻¹ * s k :=
    fun k => hasMoments_of_tendsto h hφ hopen hlim k
  have hzero : (μ : Measure ℝ) (Iio 0) = 0 := by
    apply measure_eq_zero_of_isOpen_le_liminf hopen isOpen_Iio
    intro i
    apply gaussProb_eq_zero_of_disjoint_nodes
    · exact measurableSet_Iio
    · intro xi hxi hneg
      exact (not_lt_of_ge
        (gaussNodes_nonnegative_of_shifted h hshift (φ i + 1) hxi)) hneg
  refine ⟨μ, hmom, ?_⟩
  rw [ae_iff]
  have hset : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by
    ext x
    simp
  rw [hset]
  exact hzero

end HTGeometry
