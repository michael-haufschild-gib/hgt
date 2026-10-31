import GaloisForLFunctions.HTGeometry.MomentInnerProduct
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Ritz velocity for a heat moment form

For a fixed finite polynomial space, differentiating its weak eigenvalue equation
cancels the eigenvector derivative. The eigenvalue velocity times its squared
norm is minus the squared residual `(X - λ) P`. A positive moment form therefore
forces every differentiable Ritz branch to move strictly left.
-/

open Polynomial Filter Topology HTGeometry
open scoped BigOperators

noncomputable section
namespace HilbertMetric.MomentFlow

/-- Polynomial represented by coefficients in a fixed finite family. -/
def polynomialCombination {n : ℕ} (b : Fin n → ℝ[X]) (v : Fin n → ℝ) : ℝ[X] :=
  ∑ i, v i • b i

theorem momentInner_combination {n : ℕ} (s : ℕ → ℝ)
    (b : Fin n → ℝ[X]) (v : Fin n → ℝ) (Q : ℝ[X]) :
    momentInner s (polynomialCombination b v) Q =
      ∑ i, v i * momentInner s (b i) Q := by
  simp only [polynomialCombination, momentInner_sum_left, momentInner_smul_left]

/-- Differentiation of a polynomial path against a fixed test polynomial. -/
theorem hasDerivAt_momentInner_combination {n : ℕ} {s : ℝ → ℕ → ℝ}
    {a : ℝ} (b : Fin n → ℝ[X]) {v : ℝ → Fin n → ℝ} {v' : Fin n → ℝ}
    (hs : ∀ P Q, HasDerivAt (fun t => momentInner (s t) P Q)
      (-momentInner (s a) P (X * Q)) a)
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) a) (Q : ℝ[X]) :
    HasDerivAt (fun t => momentInner (s t) (polynomialCombination b (v t)) Q)
      (momentInner (s a) (polynomialCombination b v') Q -
        momentInner (s a) (polynomialCombination b (v a)) (X * Q)) a := by
  simp only [momentInner_combination]
  convert HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hv i).mul (hs (b i) Q)) using 1
  simp only [mul_neg, ← Finset.sum_sub_distrib, sub_eq_add_neg]

/-- Exact velocity identity, valid even for an indefinite moment form. -/
theorem ritz_velocity_identity {n : ℕ} {s : ℝ → ℕ → ℝ} {a : ℝ}
    (b : Fin n → ℝ[X]) {v : ℝ → Fin n → ℝ} {v' : Fin n → ℝ}
    {lam : ℝ → ℝ} {lam' : ℝ}
    (hs : ∀ P Q, HasDerivAt (fun t => momentInner (s t) P Q)
      (-momentInner (s a) P (X * Q)) a)
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) a)
    (hlam : HasDerivAt lam lam' a)
    (heig : ∀ᶠ t in 𝓝 a, ∀ w : Fin n → ℝ,
      momentInner (s t) (polynomialCombination b (v t))
          (X * polynomialCombination b w) =
        lam t * momentInner (s t) (polynomialCombination b (v t))
          (polynomialCombination b w)) :
    lam' * momentInner (s a) (polynomialCombination b (v a))
        (polynomialCombination b (v a)) =
      -momentInner (s a) ((X - C (lam a)) * polynomialCombination b (v a))
        ((X - C (lam a)) * polynomialCombination b (v a)) := by
  let P := polynomialCombination b (v a)
  let D := polynomialCombination b v'
  have hbase := heig.self_of_nhds
  have hPP : momentInner (s a) P (X * P) = lam a * momentInner (s a) P P :=
    hbase (v a)
  have hDP : momentInner (s a) D (X * P) = lam a * momentInner (s a) D P := by
    rw [momentInner_comm, momentInner_X_mul]
    simpa only [momentInner_comm (s a) P D] using hbase v'
  have hleft := hasDerivAt_momentInner_combination b hs hv (X * P)
  have hright := hlam.mul (hasDerivAt_momentInner_combination b hs hv P)
  have heq : (fun t => momentInner (s t) (polynomialCombination b (v t)) (X * P))
      =ᶠ[𝓝 a] (fun t => lam t *
        momentInner (s t) (polynomialCombination b (v t)) P) :=
    heig.mono fun t ht => ht (v a)
  have hderiv := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  change momentInner (s a) D (X * P) - momentInner (s a) P (X * (X * P)) =
    lam' * momentInner (s a) P P +
      lam a * (momentInner (s a) D P - momentInner (s a) P (X * P)) at hderiv
  rw [hDP, hPP, ← momentInner_X_mul] at hderiv
  have hexpand : momentInner (s a) ((X - C (lam a)) * P) ((X - C (lam a)) * P) =
      momentInner (s a) (X * P) (X * P) - lam a ^ 2 * momentInner (s a) P P := by
    have hp : (X - C (lam a)) * P = X * P + (-lam a) • P := by
      rw [Polynomial.smul_eq_C_mul]
      simp only [map_neg]
      ring
    rw [hp]
    simp only [momentInner_add_left, momentInner_add_right,
      momentInner_smul_left, momentInner_smul_right,
      momentInner_comm (s a) (X * P) P, hPP]
    ring
  change lam' * momentInner (s a) P P = _
  rw [hexpand]
  linarith only [hderiv]

/-- No stationary or right-moving Ritz branch exists for a positive heat moment form. -/
theorem ritz_velocity_neg {n : ℕ} {s : ℝ → ℕ → ℝ} {a : ℝ}
    (b : Fin n → ℝ[X]) {v : ℝ → Fin n → ℝ} {v' : Fin n → ℝ}
    {lam : ℝ → ℝ} {lam' : ℝ}
    (hs : ∀ P Q, HasDerivAt (fun t => momentInner (s t) P Q)
      (-momentInner (s a) P (X * Q)) a)
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) a)
    (hlam : HasDerivAt lam lam' a)
    (heig : ∀ᶠ t in 𝓝 a, ∀ w : Fin n → ℝ,
      momentInner (s t) (polynomialCombination b (v t))
          (X * polynomialCombination b w) =
        lam t * momentInner (s t) (polynomialCombination b (v t))
          (polynomialCombination b w))
    (hpos : PositiveMomentForm (s a))
    (hne : polynomialCombination b (v a) ≠ 0) : lam' < 0 := by
  have hid := ritz_velocity_identity b hs hv hlam heig
  have hnorm := hpos.pos_of_ne_zero _ hne
  have hres := hpos.pos_of_ne_zero _ (mul_ne_zero (X_sub_C_ne_zero (lam a)) hne)
  exact (mul_neg_iff_of_pos_right hnorm).mp (hid ▸ neg_neg_of_pos hres)

end HilbertMetric.MomentFlow
