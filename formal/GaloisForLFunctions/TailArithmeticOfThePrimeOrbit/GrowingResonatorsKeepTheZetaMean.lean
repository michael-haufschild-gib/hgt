import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.GrowingResonatorsRetainZetaTruncation
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheFiniteMeanOfAGrowingResonator
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheResonatorDiagonalHasAUniformTail
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.UniformApproximationSurvivesResonatorWeights

/-!
# The zeta mean for polynomially growing resonators

On `1/2 < σ < 1`, the squared mean of `R ζ` has its full convolution
diagonal uniformly for all coefficient arrays supported below `T^κ`,
provided `κ < 2σ-1`. The error is small relative to the coefficient
energy. No bound on individual coefficients is imposed.
-/

noncomputable section
open Real Finset Filter Topology MeasureTheory
open _root_.RHTower

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

private theorem support_rpow_le {p κ T : ℝ} (hp : 0 ≤ p) (hT : 0 < T)
    {M : ℕ} (hM : (M : ℝ) ≤ T ^ κ) : (M : ℝ) ^ p ≤ T ^ (κ * p) :=
  (Real.rpow_le_rpow (Nat.cast_nonneg _) hM hp).trans_eq (Real.rpow_mul hT.le _ _).symm

/-- Uniform Carlson mean for all resonators with support `M ≤ T^κ`, `κ < 2σ-1`.
The error is measured against the original coefficient energy. -/
theorem eventually_resonatorMean_zeta_uniform {σ κ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hκ0 : 0 ≤ κ) (hκ : κ < 2 * σ - 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ (A : Finset ℕ) (r : ℕ → ℂ) (M : ℕ),
      (∀ m ∈ A, m ≠ 0) → (∀ m ∈ A, m ≤ M) → (M : ℝ) ≤ T ^ κ →
        |dyadicSquareMean (fun t => headPoly A r t *
            riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)) T -
          (∑' k : ℕ, ‖resonatorCoeff A r σ k‖ ^ 2)| ≤
            η * ∑ m ∈ A, ‖r m‖ ^ 2 := by
  obtain ⟨a, ε, m, ha, hε, hεσ, hew, hhm, hdt⟩ :=
    exists_growing_resonator_truncation hσ hσ1 hκ0 hκ
  let N : ℝ → ℕ := superlinearCutoff a
  let e : ℝ → ℝ := fun T => zetaTruncationErrorScale σ m (N T) T
  let Z : ℝ → ℂ := fun t => riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
  let α := 2 + ε - 2 * σ
  let β := (1 + ε - 2 * σ) / 2
  let P := ∑' n : ℕ, (n : ℝ) ^ (ε - 2 * σ)
  let CH := 208 * Sieve.divisorBoundConst ε * (1 / α + 1)
  let CD := Sieve.divisorBoundConst ε * (P + 2 / (2 * σ - ε - 1))
  let H : ℝ → ℝ := fun T => T ^ (κ * (1 + ε)) * (N T : ℝ) ^ α / T
  let D : ℝ → ℝ := fun T => T ^ (κ * ε) * (N T : ℝ) ^ β
  let F : ℝ → ℝ := fun T => CH * H T + CD * D T +
    (T ^ κ * e T) * (dyadicSquareMean Z T + 1 + e T)
  have hσ0 : 0 < σ := by linarith only [hσ]
  have ha0 : 0 ≤ a := (zero_lt_one.trans ha).le
  have hα : 0 < α := by dsimp [α]; linarith only [hε, hσ1]
  have hden : 0 < 2 * σ - ε - 1 := by linarith only [hεσ]
  have hDiv : 0 ≤ Sieve.divisorBoundConst ε := (Sieve.divisorBoundConst_pos hε).le
  have hP : 0 ≤ P := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hCH : 0 ≤ CH := by dsimp [CH]; positivity
  have hCD : 0 ≤ CD := by dsimp [CD]; positivity
  have he0 (T : ℝ) (hT : 1 ≤ T) : 0 ≤ e T :=
    zetaTruncationErrorScale_nonneg hσ0 (zero_le_one.trans hT) m (N T)
  have helim : Tendsto e atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hew
    · exact (eventually_ge_atTop (1 : ℝ)).mono fun T hT => he0 T hT
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      exact le_mul_of_one_le_left (he0 T hT) (Real.one_le_rpow hT hκ0)
  have hZcont : Continuous Z := by
    have h := (continuous_zetaDirichletHead 0 σ).add
      (continuous_zetaDirichletTail 0 (ne_of_lt hσ1))
    exact h.congr fun t => by dsimp [Z, zetaDirichletTail]; ring
  have hZlim : Tendsto (dyadicSquareMean Z) atTop (𝓝 (zetaCoefficientTailMass 0 σ)) := by
    simpa [Z, zetaDirichletTail, zetaDirichletHead, edPoly] using
      carlson_zeta_tail_dyadicMeanSquare 0 hσ hσ1
  have hFlim : Tendsto F atTop (𝓝 0) := by
    have h := ((hhm.const_mul CH).add (hdt.const_mul CD)).add
      (hew.mul ((hZlim.add_const 1).add helim))
    simpa only [mul_zero, zero_mul, add_zero, zero_add] using h
  filter_upwards [eventually_ge_atTop (1 : ℝ), hFlim.eventually_lt_const hη]
    with T hT hFT A r M hA hM hMT
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hN : 1 ≤ N T := (superlinearCutoff_bounds ha0 hT).1
  have hNR : (1 : ℝ) ≤ N T := Nat.cast_le.mpr hN
  have hNE : 1 ≤ (N T : ℝ) ^ α := Real.one_le_rpow hNR hα.le
  have hE : 0 ≤ ∑ n ∈ A, ‖r n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hMp := support_rpow_le (by linarith only [hε] : 0 ≤ 1 + ε) hT0 hMT
  have hMε := support_rpow_le hε.le hT0 hMT
  have hcut : (N T : ℝ) ^ α / α + 1 ≤ (1 / α + 1) * (N T : ℝ) ^ α := by
    nlinarith only [hNE]
  have hhead : |dyadicSquareMean (fun t => headPoly A r t * zetaDirichletHead (N T) σ t) T -
      (∑' k : ℕ, ‖truncResonatorCoeff A r σ (N T) k‖ ^ 2)| ≤
        (CH * H T) * ∑ n ∈ A, ‖r n‖ ^ 2 := by
    apply (abs_resonatorMean_head_sub_diagonal_le_power hε hεσ hσ1 hA r hM (N T) hT0).trans
    apply mul_le_mul_of_nonneg_right _ hE
    calc
      _ ≤ 208 * Sieve.divisorBoundConst ε * T ^ (κ * (1 + ε)) *
          ((1 / α + 1) * (N T : ℝ) ^ α) / T := by
        apply div_le_div_of_nonneg_right _ hT0.le
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hMp (by positivity)
        · exact hcut
        · exact add_nonneg (div_nonneg (by positivity) hα.le) zero_le_one
        · positivity
      _ = _ := by dsimp only [CH, H]; ring
  have hdiag : |(∑' k : ℕ, ‖resonatorCoeff A r σ k‖ ^ 2) -
      ∑' k : ℕ, ‖truncResonatorCoeff A r σ (N T) k‖ ^ 2| ≤
        (CD * D T) * ∑ n ∈ A, ‖r n‖ ^ 2 := by
    apply (abs_resonator_diagonal_sub_trunc_le_power hε hεσ hA r hM hN).trans
    apply mul_le_mul_of_nonneg_right _ hE
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hMε (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hCD
  have hclose : ∀ t ∈ Set.Icc T (2 * T), ‖zetaDirichletHead (N T) σ t - Z t‖ ≤ e T := by
    intro t ht
    rw [norm_sub_rev]
    exact norm_zeta_sub_head_le_arbitraryOrder hσ0 hT ht hN m
  have htransfer : |dyadicSquareMean (fun t => headPoly A r t * Z t) T -
      dyadicSquareMean (fun t => headPoly A r t * zetaDirichletHead (N T) σ t) T| ≤
        ((T ^ κ * e T) * (dyadicSquareMean Z T + 1 + e T)) * ∑ n ∈ A, ‖r n‖ ^ 2 := by
    rw [abs_sub_comm]
    apply (abs_resonatorMean_sub_le_uniform_error hA r hM
      (continuous_zetaDirichletHead (N T) σ) hZcont hT0 (he0 T hT) hclose).trans
    apply mul_le_mul_of_nonneg_right _ hE
    apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMT (he0 T hT))
    exact add_nonneg (add_nonneg (dyadicSquareMean_nonneg Z hT0.le) zero_le_one) (he0 T hT)
  have htotal : |dyadicSquareMean (fun t => headPoly A r t * Z t) T -
      (∑' k : ℕ, ‖resonatorCoeff A r σ k‖ ^ 2)| ≤ F T * ∑ n ∈ A, ‖r n‖ ^ 2 := by
    have htri := abs_sub_le
      (dyadicSquareMean (fun t => headPoly A r t * Z t) T)
      (dyadicSquareMean (fun t => headPoly A r t * zetaDirichletHead (N T) σ t) T)
      (∑' k : ℕ, ‖resonatorCoeff A r σ k‖ ^ 2)
    have htri' := abs_sub_le
      (dyadicSquareMean (fun t => headPoly A r t * zetaDirichletHead (N T) σ t) T)
      (∑' k : ℕ, ‖truncResonatorCoeff A r σ (N T) k‖ ^ 2)
      (∑' k : ℕ, ‖resonatorCoeff A r σ k‖ ^ 2)
    rw [abs_sub_comm (∑' k : ℕ, ‖truncResonatorCoeff A r σ (N T) k‖ ^ 2)] at htri'
    dsimp only [F]
    nlinarith only [htri, htri', hhead, hdiag, htransfer]
  exact htotal.trans (mul_le_mul_of_nonneg_right hFT.le hE)

#print axioms eventually_resonatorMean_zeta_uniform

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
