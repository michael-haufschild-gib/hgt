import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheWeightedEnergyOfATruncatedResonator

/-!
# Sharp finite means of resonators

The product polynomial is grouped by its actual integer frequency. The
sharp mean-value error retains the frequency weight on each coefficient,
so the length of the full product is never substituted for that weight.
-/

noncomputable section
open Real Finset Filter Topology MeasureTheory
open _root_.RHTower

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

/-- Every weighted truncated energy is the finite sum on its product support. -/
theorem sum_fin_truncResonatorCoeff_eq_tsum {A : Finset ℕ} (r : ℕ → ℂ)
    {σ : ℝ} (hσ : σ ≠ 0) {N K : ℕ} (hK : ∀ m ∈ A, m * N ≤ K) (w : ℕ → ℝ) :
    (∑ n : Fin K, w (n.val + 1) *
      ‖truncResonatorCoeff A r σ N (n.val + 1)‖ ^ 2) =
      ∑' k : ℕ, w k * ‖truncResonatorCoeff A r σ N k‖ ^ 2 := by
  rw [Sieve.sum_fin_eq_sum_Icc K
    (fun k => w k * ‖truncResonatorCoeff A r σ N k‖ ^ 2)]
  symm
  apply tsum_eq_sum
  intro k hk
  have hout : k = 0 ∨ K < k := by
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · right
      by_contra h
      exact hk (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  rw [truncResonatorCoeff_eq_zero r hσ hK hout, norm_zero, zero_pow two_ne_zero, mul_zero]

/-- The sharp finite mean has error at most `208/T` times the weighted energy. -/
theorem abs_resonatorMean_head_sub_diagonal_le {A : Finset ℕ}
    (hA : ∀ m ∈ A, m ≠ 0) (r : ℕ → ℂ) {σ : ℝ} (hσ : σ ≠ 0)
    (N : ℕ) {T : ℝ} (hT : 0 < T) :
    |dyadicSquareMean (fun t => headPoly A r t * zetaDirichletHead N σ t) T -
      (∑' k : ℕ, ‖truncResonatorCoeff A r σ N k‖ ^ 2)| ≤
        208 * (∑' k : ℕ, (k : ℝ) * ‖truncResonatorCoeff A r σ N k‖ ^ 2) / T := by
  classical
  let K := (A.sup id) * N
  let E := A ×ˢ Finset.Icc 1 N
  let c : ℕ × ℕ → ℂ := fun q => r q.1 * lineWeight σ q.2
  have hK : ∀ m ∈ A, m * N ≤ K := fun m hm =>
    Nat.mul_le_mul_right N (Finset.le_sup (f := id) hm)
  have hk : ∀ q ∈ E, 1 ≤ q.1 * q.2 ∧ q.1 * q.2 ≤ K := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
    have h2' := Finset.mem_Icc.mp h2
    refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (hA _ h1) (by omega)), ?_⟩
    exact (Nat.mul_le_mul_left _ h2'.2).trans (hK _ h1)
  have hfib (n : Fin K) : fiberCoeff E (fun q => q.1 * q.2) c K n =
      truncResonatorCoeff A r σ N (n.val + 1) :=
    sum_fiber_eq_truncResonatorCoeff hA r σ N _ (by omega)
  have hdiag : (∑ n : Fin K, ‖fiberCoeff E (fun q => q.1 * q.2) c K n‖ ^ 2) =
      ∑' k : ℕ, ‖truncResonatorCoeff A r σ N k‖ ^ 2 := by
    simp_rw [hfib]
    simpa only [one_mul] using sum_fin_truncResonatorCoeff_eq_tsum r hσ hK (fun _ => 1)
  have hweight : (∑ n : Fin K, ((n : ℝ) + 1) *
      ‖fiberCoeff E (fun q => q.1 * q.2) c K n‖ ^ 2) =
      ∑' k : ℕ, (k : ℝ) * ‖truncResonatorCoeff A r σ N k‖ ^ 2 := by
    simp_rw [hfib]
    simpa only [Nat.cast_add, Nat.cast_one] using
      sum_fin_truncResonatorCoeff_eq_tsum r hσ hK (fun k => (k : ℝ))
  have hfun : (fun t => ‖headPoly A r t * zetaDirichletHead N σ t‖ ^ 2) =
      fun t => ‖Sieve.dirPoly K (fiberCoeff E (fun q => q.1 * q.2) c K) t‖ ^ 2 := by
    funext t
    rw [norm_mul_zetaDirichletHead hA r N σ t, dirPoly_fiberCoeff c hk t]
  have h := Sieve.dirichlet_meanValue_sharp_window K
    (fiberCoeff E (fun q => q.1 * q.2) c K) T (2 * T)
  rw [hdiag, hweight, show 2 * T - T = T by ring] at h
  rw [dyadicSquareMean, hfun, div_sub' hT.ne', abs_div, abs_of_pos hT]
  exact div_le_div_of_nonneg_right h hT.le

/-- The finite mean error is uniform over the coefficient array. -/
theorem abs_resonatorMean_head_sub_diagonal_le_power {ε σ : ℝ} (hε : 0 < ε)
    (hεσ : ε < 2 * σ - 1) (hσ1 : σ < 1)
    {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0) (r : ℕ → ℂ)
    {M : ℕ} (hM : ∀ m ∈ A, m ≤ M) (N : ℕ) {T : ℝ} (hT : 0 < T) :
    |dyadicSquareMean (fun t => headPoly A r t * zetaDirichletHead N σ t) T -
      (∑' k : ℕ, ‖truncResonatorCoeff A r σ N k‖ ^ 2)| ≤
        (208 * Sieve.divisorBoundConst ε * (M : ℝ) ^ (1 + ε) *
          ((N : ℝ) ^ (2 + ε - 2 * σ) / (2 + ε - 2 * σ) + 1) / T) *
            ∑ m ∈ A, ‖r m‖ ^ 2 := by
  have hσ : σ ≠ 0 := by linarith only [hε, hεσ]
  apply (abs_resonatorMean_head_sub_diagonal_le hA r hσ N hT).trans
  have he := (summable_weighted_truncResonatorCoeff_sq_and_bound hε hεσ hσ1 hA r N).2
  have hw := sum_resonator_weighted_energy_le
    (by linarith only [hε] : 0 ≤ 1 + ε) hM r
  have hp : 0 ≤ (N : ℝ) ^ (2 + ε - 2 * σ) / (2 + ε - 2 * σ) + 1 := by
    have hd : 0 < 2 + ε - 2 * σ := by linarith only [hε, hσ1]
    positivity
  calc
    _ ≤ 208 * (Sieve.divisorBoundConst ε *
        ((M : ℝ) ^ (1 + ε) * ∑ m ∈ A, ‖r m‖ ^ 2) *
          ((N : ℝ) ^ (2 + ε - 2 * σ) / (2 + ε - 2 * σ) + 1)) / T := by
      apply div_le_div_of_nonneg_right _ hT.le
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact he.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw (Sieve.divisorBoundConst_pos hε).le) hp)
    _ = _ := by ring

#print axioms abs_resonatorMean_head_sub_diagonal_le
#print axioms abs_resonatorMean_head_sub_diagonal_le_power

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
