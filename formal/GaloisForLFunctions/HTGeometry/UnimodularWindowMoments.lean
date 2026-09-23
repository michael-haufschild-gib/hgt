import GaloisForLFunctions.HTGeometry.BlockRayleighLowerBound
import GaloisForLFunctions.HTGeometry.UnimodularMomentApproximation

/-!
# Prescribed moments from unimodular weights on a window

Combining the two halves of Andersson's argument at a single window:

* the Hankel system with a Rayleigh floor produces *disc* coefficients — the values of a polynomial
  bounded by one on the node interval — whose weighted moments hit any small enough target;
* rounding replaces those coefficients by *unimodular* ones at the cost of `J` times the size of a
  single moment vector.

The composite says: on a window carrying enough weighted nodes, unimodular coefficients realize any
prescribed moment vector up to an additive error `J · C`, where `C` bounds a single weight.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- The Hankel image of a coefficient vector is the weighted nodal moment of its polynomial. -/
theorem mulVec_atomicHankel_apply {N J : ℕ} (w x : Fin N → ℝ) (c : Fin J → ℝ) (j : Fin J) :
    (atomicHankel w x J).mulVec c j
      = ∑ r : Fin N, w r * Polynomial.eval (x r) (Polynomial.ofFn J c) * x r ^ (j : ℕ) := by
  have hev : ∀ r : Fin N, Polynomial.eval (x r) (Polynomial.ofFn J c)
      = ∑ i : Fin J, c i * x r ^ (i : ℕ) := by
    intro r
    rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.eval_monomial]
  simp only [Matrix.mulVec, dotProduct, atomicHankel_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hev r, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add]
  ring

/-- **Unimodular realization of prescribed window moments.** -/
theorem exists_unimodular_window_moments {N J : ℕ} (hJ : 0 < J) {lam : ℝ} (hlam : 0 < lam)
    (x w : Fin N → ℝ) (hx : ∀ r, x r ∈ Set.Icc (0:ℝ) 1) {C : ℝ} (hC : ∀ r, |w r| ≤ C)
    (hC0 : 0 ≤ C)
    (hquad : ∀ a : Fin J → ℝ, lam * (∑ i, a i ^ (2 : ℕ)) ≤ a ⬝ᵥ (atomicHankel w x J).mulVec a)
    (ξ : Fin J → ℝ) (hξ : (J : ℝ) * (∑ k, ξ k ^ (2 : ℕ)) ≤ lam ^ (2 : ℕ)) :
    ∃ b : Fin N → ℂ, (∀ r, ‖b r‖ = 1) ∧
      ∀ j : Fin J, ‖(∑ r : Fin N, b r * ((w r * x r ^ (j : ℕ) : ℝ) : ℂ)) - (ξ j : ℂ)‖
        ≤ (J : ℝ) * C := by
  classical
  obtain ⟨c, hc, hcbound⟩ := exists_unit_polynomial_solution hJ hlam x w hquad ξ hξ
  set a : Fin N → ℂ := fun r => ((Polynomial.eval (x r) (Polynomial.ofFn J c) : ℝ) : ℂ) with ha_def
  set v : Fin N → Fin J → ℂ := fun r j => ((w r * x r ^ (j : ℕ) : ℝ) : ℂ) with hv_def
  have ha : ∀ r, ‖a r‖ ≤ 1 := by
    intro r
    rw [ha_def]
    simpa using hcbound (x r) (hx r)
  have hvC : ∀ r j, ‖v r j‖ ≤ C := by
    intro r j
    rw [hv_def]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_mul, abs_pow]
    have hxr := hx r
    have hpow : |x r| ^ (j : ℕ) ≤ 1 := by
      rw [abs_of_nonneg hxr.1]
      exact pow_le_one₀ hxr.1 hxr.2
    calc |w r| * |x r| ^ (j : ℕ) ≤ |w r| * 1 :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ = |w r| := by ring
      _ ≤ C := hC r
  obtain ⟨b, hb1, hb2⟩ := exists_unimodular_moment_approx v a ha hvC hC0
  refine ⟨b, hb1, fun j => ?_⟩
  have hmoment : (∑ r : Fin N, a r * v r j) = (ξ j : ℂ) := by
    have hreal : ∑ r : Fin N, Polynomial.eval (x r) (Polynomial.ofFn J c) * (w r * x r ^ (j : ℕ))
        = ξ j := by
      rw [← congrFun hc j, mulVec_atomicHankel_apply]
      exact Finset.sum_congr rfl fun r _ => by ring
    calc (∑ r : Fin N, a r * v r j)
        = ∑ r : Fin N, ((Polynomial.eval (x r) (Polynomial.ofFn J c)
            * (w r * x r ^ (j : ℕ)) : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [ha_def, hv_def]
          push_cast
          ring
      _ = ((∑ r : Fin N, Polynomial.eval (x r) (Polynomial.ofFn J c)
            * (w r * x r ^ (j : ℕ)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
      _ = (ξ j : ℂ) := by rw [hreal]
  have := hb2 j
  rwa [hmoment] at this

/-- **Unimodular realization of a complex prescribed moment vector.**  Real and imaginary parts are
solved separately; the half-sum of the two unit-bounded polynomials is a disc coefficient, which the
rounding lemma then replaces by a unimodular one. -/
theorem exists_unimodular_window_moments_complex {N J : ℕ} (hJ : 0 < J) {lam : ℝ} (hlam : 0 < lam)
    (x w : Fin N → ℝ) (hx : ∀ r, x r ∈ Set.Icc (0:ℝ) 1) {C : ℝ} (hC : ∀ r, |w r| ≤ C)
    (hC0 : 0 ≤ C)
    (hquad : ∀ a : Fin J → ℝ, lam * (∑ i, a i ^ (2 : ℕ)) ≤ a ⬝ᵥ (atomicHankel w x J).mulVec a)
    (ζ : Fin J → ℂ) (hζ : (J : ℝ) * (∑ k, ‖2 * ζ k‖ ^ (2 : ℕ)) ≤ lam ^ (2 : ℕ)) :
    ∃ b : Fin N → ℂ, (∀ r, ‖b r‖ = 1) ∧
      ∀ j : Fin J, ‖(∑ r : Fin N, b r * ((w r * x r ^ (j : ℕ) : ℝ) : ℂ)) - ζ j‖
        ≤ (J : ℝ) * C := by
  classical
  have hre : (J : ℝ) * (∑ k, (2 * (ζ k).re) ^ (2 : ℕ)) ≤ lam ^ (2 : ℕ) := by
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_)
      (by positivity : (0:ℝ) ≤ (J : ℝ))) hζ
    have h1 : |2 * (ζ k).re| ≤ ‖2 * ζ k‖ := by
      have : (2 * ζ k).re = 2 * (ζ k).re := by simp
      rw [← this]
      exact Complex.abs_re_le_norm _
    calc (2 * (ζ k).re) ^ (2 : ℕ) = |2 * (ζ k).re| ^ (2 : ℕ) := (sq_abs _).symm
      _ ≤ ‖2 * ζ k‖ ^ (2 : ℕ) := by
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have him : (J : ℝ) * (∑ k, (2 * (ζ k).im) ^ (2 : ℕ)) ≤ lam ^ (2 : ℕ) := by
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_)
      (by positivity : (0:ℝ) ≤ (J : ℝ))) hζ
    have h1 : |2 * (ζ k).im| ≤ ‖2 * ζ k‖ := by
      have : (2 * ζ k).im = 2 * (ζ k).im := by simp
      rw [← this]
      exact Complex.abs_im_le_norm _
    calc (2 * (ζ k).im) ^ (2 : ℕ) = |2 * (ζ k).im| ^ (2 : ℕ) := (sq_abs _).symm
      _ ≤ ‖2 * ζ k‖ ^ (2 : ℕ) := by
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  obtain ⟨cr, hcr, hcrb⟩ :=
    exists_unit_polynomial_solution hJ hlam x w hquad (fun k => 2 * (ζ k).re) hre
  obtain ⟨ci, hci, hcib⟩ :=
    exists_unit_polynomial_solution hJ hlam x w hquad (fun k => 2 * (ζ k).im) him
  set a : Fin N → ℂ := fun r =>
    ((Polynomial.eval (x r) (Polynomial.ofFn J cr) : ℝ) : ℂ) / 2
      + Complex.I * ((Polynomial.eval (x r) (Polynomial.ofFn J ci) : ℝ) : ℂ) / 2 with ha_def
  set v : Fin N → Fin J → ℂ := fun r j => ((w r * x r ^ (j : ℕ) : ℝ) : ℂ) with hv_def
  have ha : ∀ r, ‖a r‖ ≤ 1 := by
    intro r
    have h1 : |Polynomial.eval (x r) (Polynomial.ofFn J cr)| ≤ 1 := hcrb (x r) (hx r)
    have h2 : |Polynomial.eval (x r) (Polynomial.ofFn J ci)| ≤ 1 := hcib (x r) (hx r)
    rw [ha_def]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_div, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    simp only [Complex.norm_ofNat]
    linarith
  have hvC : ∀ r j, ‖v r j‖ ≤ C := by
    intro r j
    rw [hv_def]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_mul, abs_pow]
    have hxr := hx r
    have hpow : |x r| ^ (j : ℕ) ≤ 1 := by
      rw [abs_of_nonneg hxr.1]
      exact pow_le_one₀ hxr.1 hxr.2
    calc |w r| * |x r| ^ (j : ℕ) ≤ |w r| * 1 :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ = |w r| := by ring
      _ ≤ C := hC r
  obtain ⟨b, hb1, hb2⟩ := exists_unimodular_moment_approx v a ha hvC hC0
  refine ⟨b, hb1, fun j => ?_⟩
  have hmoment : (∑ r : Fin N, a r * v r j) = ζ j := by
    have hrsum : ∑ r : Fin N, Polynomial.eval (x r) (Polynomial.ofFn J cr) * (w r * x r ^ (j : ℕ))
        = 2 * (ζ j).re := by
      rw [← congrFun hcr j, mulVec_atomicHankel_apply]
      exact Finset.sum_congr rfl fun r _ => by ring
    have hisum : ∑ r : Fin N, Polynomial.eval (x r) (Polynomial.ofFn J ci) * (w r * x r ^ (j : ℕ))
        = 2 * (ζ j).im := by
      rw [← congrFun hci j, mulVec_atomicHankel_apply]
      exact Finset.sum_congr rfl fun r _ => by ring
    have hexpand : (∑ r : Fin N, a r * v r j)
        = ((∑ r : Fin N, Polynomial.eval (x r) (Polynomial.ofFn J cr)
              * (w r * x r ^ (j : ℕ)) : ℝ) : ℂ) / 2
          + Complex.I * ((∑ r : Fin N, Polynomial.eval (x r) (Polynomial.ofFn J ci)
              * (w r * x r ^ (j : ℕ)) : ℝ) : ℂ) / 2 := by
      rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.sum_div, Finset.mul_sum, Finset.sum_div,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [ha_def, hv_def]
      push_cast
      ring
    rw [hexpand, hrsum, hisum]
    push_cast
    apply Complex.ext <;> simp
  have := hb2 j
  rwa [hmoment] at this

end GaloisForLFunctions.HTGeometry

end
