import GaloisForLFunctions.HTGeometry.CofinalCholeskySelection
import Mathlib.Analysis.Polynomial.Basic

/-!
# Polynomial rigidity of positive-metric gauge families

The algebraic obstruction in Gomes, arXiv:2607.24901v1, Proposition 2,
excludes charged algebraic additive-group representations. A complementary
positive-metric obstruction needs no representation law: a finite family of
real polynomial coordinates with constant squared norm is constant.
Consequently polynomial orthogonal-matrix families are constant, and the
corpus's injective rational Cayley family has no polynomial coordinates.
This is a consequence inspired by the obstruction, not a restatement of the
paper's classification of one-dimensional algebraic groups.
-/

open scoped BigOperators
open Polynomial Filter
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- A constant sum of polynomial squares forces every coordinate to be constant. -/
theorem polynomial_sum_squares_constant_iff {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℝ) :
    (∀ t : ℝ, ∑ i, ((p i).eval t)^2 = ∑ i, ((p i).eval 0)^2) ↔
      ∀ i, p i = Polynomial.C ((p i).eval 0) := by
  classical
  constructor
  · intro h i
    have hbound : IsBoundedUnder (· ≤ ·) atTop (fun t : ℝ => |(p i).eval t|) := by
      refine ⟨(∑ j, ((p j).eval 0)^2) + 1, ?_⟩
      apply eventually_map.mpr
      apply Eventually.of_forall
      intro t
      have hs : ((p i).eval t)^2 ≤ ∑ j, ((p j).eval t)^2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg ((p j).eval t)) (Finset.mem_univ i)
      rw [h t] at hs
      nlinarith [sq_abs ((p i).eval t), sq_nonneg (|(p i).eval t| - 1/2)]
    have hc := Polynomial.eq_C_of_degree_le_zero
      ((Polynomial.isBoundedUnder_abs_atTop_iff (p i)).mp hbound)
    simpa only [← Polynomial.coeff_zero_eq_eval_zero] using hc
  · intro h t
    apply Finset.sum_congr rfl
    intro i _
    have he : (p i).eval t = (p i).eval 0 := by
      conv_lhs => rw [h i, Polynomial.eval_C]
    rw [he]

/-- Unit-circle polynomial coordinates are precisely constant unit vectors. -/
theorem polynomial_circle_coordinates_iff (p q : Polynomial ℝ) :
    (∀ t : ℝ, (p.eval t)^2 + (q.eval t)^2 = 1) ↔
      p = Polynomial.C (p.eval 0) ∧ q = Polynomial.C (q.eval 0) ∧
        (p.eval 0)^2 + (q.eval 0)^2 = 1 := by
  constructor
  · intro h
    let f : Bool → Polynomial ℝ := fun b => if b then p else q
    have hs : ∀ t : ℝ, ∑ b, ((f b).eval t)^2 = ∑ b, ((f b).eval 0)^2 := by
      intro t
      simpa [f, add_comm] using (h t).trans (h 0).symm
    have hc := (polynomial_sum_squares_constant_iff f).mp hs
    exact ⟨by simpa [f] using hc true, by simpa [f] using hc false, h 0⟩
  · rintro ⟨hp, hq, h0⟩ t
    rw [hp, hq, Polynomial.eval_C, Polynomial.eval_C]
    exact h0

/-- Orthogonal polynomial matrix families carry no nonconstant real-parameter motion. -/
theorem polynomial_orthogonal_family_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (Polynomial ℝ)) :
    (∀ t : ℝ, (P.map (Polynomial.eval t)).transpose * P.map (Polynomial.eval t) = 1) ↔
      (∀ i j, P i j = Polynomial.C ((P i j).eval 0)) ∧
        (P.map (Polynomial.eval 0)).transpose * P.map (Polynomial.eval 0) = 1 := by
  constructor
  · intro h
    refine ⟨?_, h 0⟩
    intro i j
    have hs : ∀ t : ℝ, ∑ k, ((P k j).eval t)^2 = ∑ k, ((P k j).eval 0)^2 := by
      intro t
      have ht := congrFun₂ (h t) j j
      have h0 := congrFun₂ (h 0) j j
      simpa [Matrix.mul_apply, pow_two] using ht.trans h0.symm
    exact (polynomial_sum_squares_constant_iff (fun k => P k j)).mp hs i
  · rintro ⟨hc, h0⟩ t
    have he : P.map (Polynomial.eval t) = P.map (Polynomial.eval 0) := by
      ext i j
      change (P i j).eval t = (P i j).eval 0
      conv_lhs => rw [hc i j, Polynomial.eval_C]
    rw [he]
    exact h0

/-- The existing rational Cayley curve cannot be replaced by polynomial real coordinates. -/
theorem realCayley_no_polynomial_coordinates :
    ¬ ∃ p q : Polynomial ℝ,
      ∀ t : ℝ, realCayley t = ((p.eval t : ℝ) : ℂ) + Complex.I * ((q.eval t : ℝ) : ℂ) := by
  rintro ⟨p, q, he⟩
  have hs : ∀ t : ℝ, (p.eval t)^2 + (q.eval t)^2 = 1 := by
    intro t
    have hn : Complex.normSq (realCayley t) = 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_realCayley, one_pow]
    rw [he t] at hn
    simpa [Complex.normSq_apply, pow_two] using hn
  obtain ⟨hp, hq, _⟩ := (polynomial_circle_coordinates_iff p q).mp hs
  have heq : realCayley 0 = realCayley 1 := by
    rw [he 0, he 1, hp, hq]
    simp only [Polynomial.eval_C]
  exact zero_ne_one (injective_realCayley heq)

end GaloisForLFunctions.HTGeometry
