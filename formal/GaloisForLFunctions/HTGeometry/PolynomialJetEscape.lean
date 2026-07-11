import GaloisForLFunctions.HTGeometry.CauchyJetControllability
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomial escape inside a positive finite-mass cone

A nonzero complex multivariate polynomial cannot vanish on a neighborhood of a finite complex
packet.  More specifically, every affine line joining an arbitrary base packet to one nonvanishing
packet contains nonvanishing points at arbitrarily small positive real parameters.

Combining this elementary algebraic rigidity with a surjective finitely supported real control map
gives the constraint-side statement needed for Herglotz carriers: every fixed algebraic jet relation
can be escaped by an arbitrarily small control that preserves all strictly positive base masses.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The restriction of a multivariate polynomial to the affine line from `x` to `y`. -/
noncomputable def mvPolynomialLine {σ : Type*}
    (P : MvPolynomial σ ℂ) (x y : σ → ℂ) : ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (y i - x i)) P

theorem eval_mvPolynomialLine {σ : Type*}
    (P : MvPolynomial σ ℂ) (x y : σ → ℂ) (t : ℂ) :
    (mvPolynomialLine P x y).eval t =
      MvPolynomial.eval (fun i => x i + t * (y i - x i)) P := by
  rw [mvPolynomialLine]
  change (Polynomial.evalRingHom t)
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (y i - x i)) P) = _
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext c
    simp
  · funext i
    simp
  · rfl

/-- If the endpoint `y` does not lie on the hypersurface, the polynomial restricted to the line
from `x` to `y` is nonzero. -/
theorem mvPolynomialLine_ne_zero {σ : Type*}
    (P : MvPolynomial σ ℂ) (x y : σ → ℂ)
    (hy : MvPolynomial.eval y P ≠ 0) :
    mvPolynomialLine P x y ≠ 0 := by
  intro h
  have h1 := congrArg (Polynomial.eval (1 : ℂ)) h
  rw [eval_mvPolynomialLine] at h1
  simp at h1
  exact hy h1

/-- Every sufficiently short positive real interval on an affine line to a nonvanishing endpoint
contains a nonvanishing point. -/
theorem exists_small_real_line_eval_ne_zero {σ : Type*}
    (P : MvPolynomial σ ℂ) (x y : σ → ℂ)
    (hy : MvPolynomial.eval y P ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < η ∧
      MvPolynomial.eval (fun i => x i + (ε : ℂ) * (y i - x i)) P ≠ 0 := by
  let Q := mvPolynomialLine P x y
  have hQ : Q ≠ 0 := mvPolynomialLine_ne_zero P x y hy
  have hS : (Complex.ofReal '' Set.Ioo (0 : ℝ) η).Infinite :=
    (Set.Ioo_infinite hη).image Complex.ofReal_injective.injOn
  have hnot : ¬ Complex.ofReal '' Set.Ioo (0 : ℝ) η ⊆ {z | Q.IsRoot z} := by
    intro hsub
    exact (Polynomial.finite_setOf_isRoot hQ).not_infinite (hS.mono hsub)
  obtain ⟨z, ⟨ε, hε, rfl⟩, hz⟩ := Set.not_subset.mp hnot
  refine ⟨ε, hε.1, hε.2, ?_⟩
  rw [← eval_mvPolynomialLine]
  simpa [Polynomial.IsRoot] using hz

/-- A nonzero multivariate polynomial over `ℂ` is nonzero at some point. -/
theorem exists_mvPolynomial_eval_ne_zero {σ : Type*}
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0) :
    ∃ y : σ → ℂ, MvPolynomial.eval y P ≠ 0 := by
  by_contra h
  have hall : ∀ y : σ → ℂ, MvPolynomial.eval y P = 0 := fun y =>
    not_ne_iff.mp ((not_exists.mp h) y)
  exact hP (MvPolynomial.funext (fun y => by simpa using hall y))

/-- The complement of a nonzero complex algebraic hypersurface is dense in every finite complex
packet space. -/
theorem mvPolynomial_nonzero_eval_dense {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    Dense {x : σ → ℂ | MvPolynomial.eval x P ≠ 0} := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  rw [Metric.mem_closure_iff]
  intro r hr
  obtain ⟨y, hy⟩ := exists_mvPolynomial_eval_ne_zero hP
  let line : ℝ → (σ → ℂ) := fun t i => x i + (t : ℂ) * (y i - x i)
  have hline : Continuous line := by
    apply continuous_pi
    intro i
    exact continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const)
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.mp hline.continuousAt) r hr
  obtain ⟨ε, hε, hεδ, hne⟩ :=
    exists_small_real_line_eval_ne_zero P x y hy hδ
  refine ⟨line ε, ?_, ?_⟩
  · exact hne
  · have hdist : dist ε (0 : ℝ) < δ := by
      simpa [Real.dist_eq, abs_of_pos hε] using hεδ
    simpa [line, dist_comm] using hclose hdist

theorem mvPolynomial_zero_set_isClosed {σ : Type*} (P : MvPolynomial σ ℂ) :
    IsClosed {x : σ → ℂ | MvPolynomial.eval x P = 0} := by
  exact isClosed_singleton.preimage P.continuous_eval

/-- The zero set of a nonzero complex multivariate polynomial on a finite packet is nowhere dense. -/
theorem mvPolynomial_zero_set_isNowhereDense {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    IsNowhereDense {x : σ → ℂ | MvPolynomial.eval x P = 0} := by
  rw [(mvPolynomial_zero_set_isClosed P).isNowhereDense_iff]
  rw [interior_eq_empty_iff_dense_compl]
  have heq : {x : σ → ℂ | MvPolynomial.eval x P = 0}ᶜ =
      {x : σ → ℂ | MvPolynomial.eval x P ≠ 0} := by
    ext x
    simp
  rw [heq]
  exact mvPolynomial_nonzero_eval_dense P hP

/-- Positivity at one parameter persists at every smaller nonnegative parameter along the same
finitely supported mass direction. -/
theorem positive_finsupp_perturbation_of_le
    {κ : Type*} (w : κ → ℝ) (hw : ∀ p, 0 < w p) (a : κ →₀ ℝ)
    {ε δ : ℝ} (hδ : 0 ≤ δ) (hδε : δ ≤ ε)
    (hpos : ∀ p, 0 < w p + ε * a p) :
    ∀ p, 0 < w p + δ * a p := by
  intro p
  by_cases ha : 0 ≤ a p
  · nlinarith [hw p]
  · nlinarith [hpos p]

/-- **Positive algebraic escape law.** If finitely supported real controls surject onto a finite
complex packet, then from every strictly positive base mass and every base packet, an arbitrarily
small positive control time preserves all masses and escapes any prescribed nonzero polynomial
relation on that packet. -/
theorem surjective_positive_control_escapes_mvPolynomial
    {κ σ : Type*} [Fintype σ]
    (L : (κ →₀ ℝ) →ₗ[ℝ] (σ → ℂ)) (hL : Function.Surjective L)
    (w : κ → ℝ) (hw : ∀ p, 0 < w p)
    (x : σ → ℂ) (P : MvPolynomial σ ℂ) (hP : P ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ a : κ →₀ ℝ, ∃ ε : ℝ,
      0 < ε ∧ ε < η ∧
      (∀ p, 0 < w p + ε * a p) ∧
      MvPolynomial.eval (x + ε • L a) P ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_mvPolynomial_eval_ne_zero hP
  obtain ⟨a, ha⟩ := hL (y - x)
  obtain ⟨ρ, hρ, hρη, hρpos⟩ :=
    exists_small_positive_finsupp_perturbation w hw a hη
  obtain ⟨ε, hε, hερ, hne⟩ :=
    exists_small_real_line_eval_ne_zero P x y hy hρ
  refine ⟨a, ε, hε, hερ.trans hρη, ?_, ?_⟩
  · exact positive_finsupp_perturbation_of_le w hw a hε.le hερ.le hρpos
  · have hcoord : x + ε • L a = fun i => x i + (ε : ℂ) * (y i - x i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [ha]
      simp
    rw [hcoord]
    exact hne

end GaloisForLFunctions.HTGeometry
