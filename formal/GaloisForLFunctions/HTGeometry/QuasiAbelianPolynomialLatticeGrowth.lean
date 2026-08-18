import GaloisForLFunctions.HTGeometry.QuasiAbelianGaussianLatticeDecay
import GaloisForLFunctions.HTGeometry.QuasiAbelianPoincareGaussianMajorant

/-!
# Polynomial growth along a real lattice

The third factor of Abe's interpolation seed is an arbitrary polynomial.  Evaluated at a lattice
translate `x + k` of a compact set it grows at most like `∏_i (1 + |k_i|)^{deg_i P}`, which is
exactly the polynomial part of `polynomialGaussianLatticeWeight`.

The bound is coefficientwise: each monomial contributes `∏_i ‖y_i‖^{a_i}` with `a_i ≤ deg_i P`, and
`‖x_i + k_i‖ ≤ (1 + R)(1 + |k_i|)` on a compact set of radius `R`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem exists_norm_mvPolynomial_eval_le {d : ℕ} (P : MvPolynomial (Fin d) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Fin d → ℂ,
      ‖MvPolynomial.eval y P‖ ≤ C * ∏ i, (1 + ‖y i‖) ^ (P.degreeOf i) := by
  classical
  refine ⟨∑ a ∈ P.support, ‖MvPolynomial.coeff a P‖,
    Finset.sum_nonneg fun _ _ => norm_nonneg _, fun y => ?_⟩
  have hone : ∀ i : Fin d, (1 : ℝ) ≤ 1 + ‖y i‖ := fun i => by
    have := norm_nonneg (y i)
    linarith
  rw [MvPolynomial.eval_eq]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [norm_mul, norm_prod]
  simp only [norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hstep0 : ∏ i ∈ a.support, ‖y i‖ ^ (a i) = ∏ i : Fin d, ‖y i‖ ^ (a i) := by
    refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
    have hzero : a i = 0 := by simpa using hi
    rw [hzero, pow_zero]
  have hstep1 : ∏ i : Fin d, ‖y i‖ ^ (a i) ≤ ∏ i : Fin d, (1 + ‖y i‖) ^ (a i) := by
    refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    linarith [norm_nonneg (y i)]
  have hstep3 : ∏ i : Fin d, (1 + ‖y i‖) ^ (a i)
      ≤ ∏ i : Fin d, (1 + ‖y i‖) ^ (P.degreeOf i) := by
    refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
    refine pow_le_pow_right₀ (hone i) ?_
    exact MvPolynomial.monomial_le_degreeOf i ha
  rw [hstep0]
  exact le_trans hstep1 hstep3

/-! ## Along the lattice -/

theorem exists_norm_mvPolynomial_lattice_le {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    {K : Set (Fin d → ℂ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin d → ℤ) (x : Fin d → ℂ), x ∈ K →
      ‖MvPolynomial.eval (x + integerCastVector k) P‖
        ≤ C * ∏ i, (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i) := by
  classical
  obtain ⟨C₀, hC₀, hC⟩ := exists_norm_mvPolynomial_eval_le P
  obtain ⟨R, hR⟩ := (hK.isBounded).subset_closedBall 0
  set R' : ℝ := max R 0 with hR'def
  have hR'0 : 0 ≤ R' := le_max_right _ _
  refine ⟨C₀ * ∏ i : Fin d, (1 + R') ^ (P.degreeOf i), by positivity, fun k x hx => ?_⟩
  have hxR : ‖x‖ ≤ R' := by
    have := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact le_trans this (le_max_left _ _)
  have hcoord : ∀ i : Fin d,
      1 + ‖(x + integerCastVector k) i‖ ≤ (1 + R') * (1 + ((k i).natAbs : ℝ)) := by
    intro i
    have hxi : ‖x i‖ ≤ R' := le_trans (norm_le_pi_norm x i) hxR
    have hki : ‖((k i : ℤ) : ℂ)‖ = ((k i).natAbs : ℝ) := by
      rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    have hval : (x + integerCastVector k) i = x i + ((k i : ℤ) : ℂ) := rfl
    rw [hval]
    have hsum : ‖x i + ((k i : ℤ) : ℂ)‖ ≤ R' + ((k i).natAbs : ℝ) := by
      refine le_trans (norm_add_le _ _) ?_
      rw [hki]
      linarith
    have hnat : (0 : ℝ) ≤ ((k i).natAbs : ℝ) := by positivity
    nlinarith [hsum, hR'0, hnat]
  refine le_trans (hC _) ?_
  have hprod : ∏ i : Fin d, (1 + ‖(x + integerCastVector k) i‖) ^ (P.degreeOf i)
      ≤ ∏ i : Fin d, ((1 + R') * (1 + ((k i).natAbs : ℝ))) ^ (P.degreeOf i) := by
    refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
    exact pow_le_pow_left₀ (by positivity) (hcoord i) _
  refine le_trans (mul_le_mul_of_nonneg_left hprod hC₀) (le_of_eq ?_)
  have hsplit : ∀ i : Fin d, ((1 + R') * (1 + ((k i).natAbs : ℝ))) ^ (P.degreeOf i)
      = (1 + R') ^ (P.degreeOf i) * (1 + ((k i).natAbs : ℝ)) ^ (P.degreeOf i) := fun i =>
    mul_pow _ _ _
  rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_mul_distrib]
  ring

end

end GaloisForLFunctions.HTGeometry
