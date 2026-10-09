import GaloisForLFunctions.HTGeometry.QKrawtchoukEdgeMoments
import GaloisForLFunctions.HTGeometry.BoundedNodesDeterminate

/-!
# Determinacy of the Al-Salam--Carlitz companion edge

The bounded recurrence in arXiv:2609.24149, Proposition 8.1, has a unique
probability realization. We prove a uniform bound on its Gauss nodes directly
from the three-term recurrence, then use the corpus's compact moment
determinacy theorem. This separates the companion edge from the indeterminate
inverse-q Hermite edge without assuming a spectral realization.
-/

noncomputable section
open MeasureTheory

namespace HTGeometry

private theorem favard_eval_abs_ge_one (α β : ℕ → ℝ) (A B x : ℝ)
    (hα : ∀ n, |α n| ≤ A) (hβ : ∀ n, |β (n + 1)| ≤ B)
    (hx : 1 + A + B < |x|) (n : ℕ) :
    1 ≤ |(favardPoly α β n).eval x| := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hβ 0)
  have hgap (j : ℕ) : 1 + B ≤ |x - α j| := by
    have ht := abs_add_le (x - α j) (α j)
    rw [sub_add_cancel] at ht
    linarith [hα j]
  have hrec : ∀ k, 1 ≤ |(favardPoly α β k).eval x| ∧
      |(favardPoly α β k).eval x| ≤ |(favardPoly α β (k + 1)).eval x| := by
    intro k
    induction k with
    | zero =>
        simp only [Nat.zero_add, favardPoly_zero, favardPoly_one, Polynomial.eval_one,
          Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, abs_one]
        exact ⟨le_rfl, by linarith [hgap 0]⟩
    | succ k hk =>
        refine ⟨hk.1.trans hk.2, ?_⟩
        rw [show k + 1 + 1 = k + 2 by omega, favardPoly_succ_succ]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_X, Polynomial.eval_C]
        have ht := abs_add_le
          ((x - α (k + 1)) * (favardPoly α β (k + 1)).eval x -
            β (k + 1) * (favardPoly α β k).eval x)
          (β (k + 1) * (favardPoly α β k).eval x)
        rw [sub_add_cancel, abs_mul, abs_mul] at ht
        have hlow := mul_le_mul_of_nonneg_right (hgap (k + 1))
          (abs_nonneg ((favardPoly α β (k + 1)).eval x))
        have hhigh : |β (k + 1)| * |(favardPoly α β k).eval x| ≤
            B * |(favardPoly α β (k + 1)).eval x| :=
          (mul_le_mul_of_nonneg_right (hβ k) (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hk.2 hB)
        nlinarith
  exact (hrec n).1

/-- Uniform diagonal bound, independent of degree. -/
theorem alSalamCarlitzDiagonal_abs_le (t u : ℝ) (n : ℕ) :
    |alSalamCarlitzDiagonal t u n| ≤ 1 + Real.exp u := by
  have hc := Real.exp_pos u
  have hq := Real.exp_pos (-Real.exp t * n)
  have hq1 : Real.exp (-Real.exp t * n) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have : 0 ≤ Real.exp t * (n : ℝ) := by positivity
      linarith)
  have ha : |1 - Real.exp u| ≤ 1 + Real.exp u := by
    rw [abs_le]
    constructor <;> linarith
  rw [alSalamCarlitzDiagonal, abs_mul, abs_of_pos hq]
  calc
    _ ≤ (1 + Real.exp u) * 1 := mul_le_mul ha hq1 hq.le (by positivity)
    _ = _ := mul_one _

/-- Uniform lower-recurrence bound, independent of degree. -/
theorem alSalamCarlitzLower_abs_le (t u : ℝ) (n : ℕ) :
    |alSalamCarlitzLower t u (n + 1)| ≤ Real.exp u := by
  rw [abs_of_pos (alSalamCarlitzLower_succ_pos t u n)]
  simp only [alSalamCarlitzLower, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  have hc := Real.exp_pos u
  have hq := Real.exp_pos (-Real.exp t * n)
  have hq1 : Real.exp (-Real.exp t * n) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have : 0 ≤ Real.exp t * (n : ℝ) := by positivity
      linarith)
  have hz := Real.exp_pos (-Real.exp t * ((n : ℝ) + 1))
  calc
    _ ≤ Real.exp u * Real.exp (-Real.exp t * n) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc.le hq.le)
    _ ≤ Real.exp u := by nlinarith

/-- Every finite Gauss node lies in one explicit compact interval. -/
theorem alSalamCarlitzMoment_nodes_bounded (t u : ℝ) :
    ∀ n : ℕ, ∀ x ∈ gaussNodes (alSalamCarlitzMoment t u) n,
      x ∈ Set.Icc (-(2 + 2 * Real.exp u)) (2 + 2 * Real.exp u) := by
  intro n x hx
  have hroot := (mem_gaussNodes_iff n x).mp hx
  rw [alSalamCarlitzMoment_monicOrtho] at hroot
  apply abs_le.mp
  by_contra hbound
  have hxabs : 1 + (1 + Real.exp u) + Real.exp u < |x| := by
    have := lt_of_not_ge hbound
    linarith
  have h := favard_eval_abs_ge_one (alSalamCarlitzDiagonal t u)
    (alSalamCarlitzLower t u) (1 + Real.exp u) (Real.exp u) x
    (alSalamCarlitzDiagonal_abs_le t u) (alSalamCarlitzLower_abs_le t u) hxabs (n + 1)
  rw [hroot, abs_zero] at h
  linarith

/-- The companion edge has a unique probability law, and that law is carried
by an explicit compact interval. No measure, support, or determinacy premise
is supplied by the caller. -/
theorem alSalamCarlitzMoment_compact_unique (t u : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments (alSalamCarlitzMoment t u)
        (μ : Measure ℝ) ∧
      (μ : Measure ℝ) (Set.Icc (-(2 + 2 * Real.exp u)) (2 + 2 * Real.exp u))ᶜ = 0 ∧
      ∀ ν : ProbabilityMeasure ℝ,
        GaloisForLFunctions.HTGeometry.HasHamburgerMoments (alSalamCarlitzMoment t u)
          (ν : Measure ℝ) → ν = μ := by
  obtain ⟨μ, hcar, hm⟩ := exists_carried_representative_of_nodes_bounded
    (alSalamCarlitzMoment_positive t u) (alSalamCarlitzMoment_nodes_bounded t u)
  have hm' : GaloisForLFunctions.HTGeometry.HasHamburgerMoments
      (alSalamCarlitzMoment t u) (μ : Measure ℝ) := by
    intro k
    simpa only [alSalamCarlitzMoment_zero, inv_one, one_mul] using hm k
  refine ⟨μ, hm', hcar, ?_⟩
  intro ν hν
  apply ProbabilityMeasure.toMeasure_injective
  apply measure_eq_of_nodes_bounded (alSalamCarlitzMoment_positive t u)
    (by positivity : 0 < 2 + 2 * Real.exp u) (alSalamCarlitzMoment_nodes_bounded t u)
  · intro k
    simpa only [alSalamCarlitzMoment_zero, inv_one, one_mul] using (hν k).2.symm
  · exact fun k => (hν k).1
  · exact fun k => (hm k).2.symm
  · exact fun k => (hm k).1

end HTGeometry
