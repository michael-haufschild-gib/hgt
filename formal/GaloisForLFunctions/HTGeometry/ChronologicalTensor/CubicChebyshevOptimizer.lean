import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicGradedRecovery
import GaloisForLFunctions.HTGeometry.WeightedMinimax.Coefficient

/-!
# The chronological weighted Chebyshev optimizer

The intrinsic interval weight of chronological recovery is `W(r) = 1 - √(1-4r)` on `[0,1/4]`, and
the physical homogeneous recovery errors at weight `k` are exactly the `W^k`-weighted polynomial
suprema with one prescribed coefficient (`cubicHomogeneousRecoveryErrors_interval`). The general
weighted minimax theory therefore applies verbatim: for every `k ≥ 1` the monic degree-`k`
minimizer exists, has `k` distinct roots in the open interval `(0,1/4)`, equals the product of the
corresponding linear factors, has every coefficient nonzero, and controls every coefficient of
every competitor. Its penultimate coefficient is minus the sum of its roots, so the already
formalized graded recovery gap is the optimizer's norm divided by that root sum, and the optimal
normalized residual is unique.

Nothing is assumed: the weight hypotheses of the general theory are discharged here.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section
open Set Polynomial
open GaloisForLFunctions.HTGeometry.WeightedMinimax

/-- The intrinsic interval weight of chronological recovery, raised to the physical weight. -/
def cubicIntervalWeight (k : ℕ) : ℝ → ℝ := fun r => cubicRadialWeight r ^ k

theorem cubicWeightedIntervalNorm_eq (k : ℕ) :
    cubicWeightedIntervalNorm k = wsup (cubicIntervalWeight k) 0 (1/4) := rfl

theorem cubicRadialWeight_continuous : Continuous cubicRadialWeight := by
  unfold cubicRadialWeight
  exact continuous_const.sub
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_const.mul continuous_id)))

theorem cubicRadialWeight_zero : cubicRadialWeight 0 = 0 := by
  unfold cubicRadialWeight
  norm_num

theorem cubicRadialWeight_pos_of_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1/4) :
    0 < cubicRadialWeight r := by
  have hnn : (0:ℝ) ≤ 1 - 4*r := by linarith
  have hs := Real.sq_sqrt hnn
  have hs0 := Real.sqrt_nonneg (1 - 4*r)
  unfold cubicRadialWeight
  nlinarith

/-- The chronological interval weight is admissible for the weighted minimax theory. -/
theorem cubicIntervalWeight_isWeight (k : ℕ) : IsWeight (cubicIntervalWeight k) 0 (1/4) where
  le := by norm_num
  cont := cubicRadialWeight_continuous.pow k
  nonneg := by
    intro r hr
    exact pow_nonneg (cubicRadialWeight_bounds ⟨r, hr⟩).1 k
  infinite := by
    refine Set.Infinite.mono ?_ (Set.Ioc_infinite (by norm_num : (0:ℝ) < 1/4))
    intro r hr
    refine ⟨⟨le_of_lt hr.1, hr.2⟩, ?_⟩
    exact pow_ne_zero k (ne_of_gt (cubicRadialWeight_pos_of_pos hr.1 hr.2))

/-- At positive weight the interval weight vanishes exactly at the left endpoint. -/
theorem cubicIntervalWeight_pos (k : ℕ) (hk : 1 ≤ k) :
    ∀ r ∈ Set.Icc (0:ℝ) (1/4), cubicIntervalWeight k r ≠ 0 → 0 < r := by
  intro r hr hne
  rcases lt_or_eq_of_le hr.1 with h | h
  · exact h
  · exfalso
    apply hne
    unfold cubicIntervalWeight
    rw [← h, cubicRadialWeight_zero]
    exact zero_pow (by omega)

/-- `T` is the weighted Chebyshev optimizer of degree `k` for the chronological interval weight. -/
def IsCubicChebyshev (k : ℕ) (T : Polynomial ℝ) : Prop :=
  T.natDegree ≤ k ∧ T.coeff k = 1 ∧
    ∀ p : Polynomial ℝ, p.natDegree ≤ k → p.coeff k = 1 →
      cubicWeightedIntervalNorm k T ≤ cubicWeightedIntervalNorm k p

theorem IsCubicChebyshev.mem {k : ℕ} {T : Polynomial ℝ} (h : IsCubicChebyshev k T) :
    T ∈ monicDeg k := ⟨h.1, h.2.1⟩

theorem IsCubicChebyshev.minimal {k : ℕ} {T : Polynomial ℝ} (h : IsCubicChebyshev k T) :
    ∀ p ∈ monicDeg k, wsup (cubicIntervalWeight k) 0 (1/4) T
      ≤ wsup (cubicIntervalWeight k) 0 (1/4) p :=
  fun p hp => h.2.2 p hp.1 hp.2

/-- The optimizer exists at every degree and has strictly positive weighted norm. -/
theorem exists_isCubicChebyshev (k : ℕ) :
    ∃ T : Polynomial ℝ, IsCubicChebyshev k T ∧ 0 < cubicWeightedIntervalNorm k T := by
  obtain ⟨T, hTmem, hTpos, hTmin⟩ :=
    exists_monicDeg_minimizer (cubicIntervalWeight_isWeight k) k
  exact ⟨T, ⟨hTmem.1, hTmem.2, fun p hp1 hp2 => hTmin p ⟨hp1, hp2⟩⟩, hTpos⟩

/-- **The optimizer's root structure.** The degree-`k` optimizer has `k` distinct roots in the
open interval `(0,1/4)`, is their product of linear factors, and its penultimate coefficient is
minus their (strictly positive) sum. -/
theorem isCubicChebyshev_roots (k : ℕ) (hk : 1 ≤ k) {T : Polynomial ℝ}
    (hT : IsCubicChebyshev k T) :
    ∃ s : Finset ℝ, s.card = k ∧ (∀ r ∈ s, 0 < r ∧ r < 1/4) ∧
      T = ∏ r ∈ s, (Polynomial.X - Polynomial.C r) ∧
      T.coeff (k - 1) = -∑ r ∈ s, r ∧ 0 < ∑ r ∈ s, r :=
  coeff_pred_eq_neg_sum_roots (cubicIntervalWeight_isWeight k)
    (cubicIntervalWeight_pos k hk) (by omega) hT.mem hT.minimal

/-- Every coefficient of the optimizer is nonzero. -/
theorem isCubicChebyshev_coeff_ne_zero (k : ℕ) (hk : 1 ≤ k) {T : Polynomial ℝ}
    (hT : IsCubicChebyshev k T) : ∀ j ≤ k, T.coeff j ≠ 0 :=
  coeff_monicDeg_minimizer_ne_zero (cubicIntervalWeight_isWeight k)
    (cubicIntervalWeight_pos k hk) hT.mem hT.minimal

/-- **Coefficient duality.** The optimizer maximizes every coefficient-to-norm ratio. -/
theorem isCubicChebyshev_coeff_duality (k : ℕ) (hk : 1 ≤ k) {T : Polynomial ℝ}
    (hT : IsCubicChebyshev k T) {j : ℕ} (hj : j ≤ k) {R : Polynomial ℝ}
    (hR : R.natDegree ≤ k) :
    |R.coeff j| * cubicWeightedIntervalNorm k T ≤ |T.coeff j| * cubicWeightedIntervalNorm k R :=
  coeff_mul_wsup_le (cubicIntervalWeight_isWeight k) (cubicIntervalWeight_pos k hk)
    hT.mem hT.minimal hj hR

/-- **Equality case.** Equality in coefficient duality forces a nonzero real multiple of the
optimizer. -/
theorem isCubicChebyshev_eq_const_mul (k : ℕ) (hk : 1 ≤ k) {T : Polynomial ℝ}
    (hT : IsCubicChebyshev k T) {j : ℕ} (hj : j ≤ k) {R : Polynomial ℝ}
    (hR : R.natDegree ≤ k) (hRne : R ≠ 0)
    (heq : |R.coeff j| * cubicWeightedIntervalNorm k T
      = |T.coeff j| * cubicWeightedIntervalNorm k R) :
    ∃ μ : ℝ, μ ≠ 0 ∧ R = Polynomial.C μ * T :=
  eq_const_mul_of_coeff_eq (cubicIntervalWeight_isWeight k) (cubicIntervalWeight_pos k hk)
    hT.mem hT.minimal hj hR hRne heq

/-- **Uniqueness of the normalized optimizer.** -/
theorem isCubicChebyshev_normalized_unique (k : ℕ) (hk : 1 ≤ k) {T : Polynomial ℝ}
    (hT : IsCubicChebyshev k T) {j : ℕ} (hj : j ≤ k) {S : Polynomial ℝ}
    (hS1 : S.natDegree ≤ k) (hS2 : S.coeff j = 1)
    (hSmin : ∀ p : Polynomial ℝ, p.natDegree ≤ k → p.coeff j = 1 →
      cubicWeightedIntervalNorm k S ≤ cubicWeightedIntervalNorm k p) :
    S = Polynomial.C (T.coeff j)⁻¹ * T :=
  coeffSet_minimizer_eq (cubicIntervalWeight_isWeight k) (cubicIntervalWeight_pos k hk)
    hT.mem hT.minimal hj ⟨hS1, hS2⟩ (fun p hp => hSmin p hp.1 hp.2)

/-! ### The graded recovery gap as an exact ratio -/

/-- The already formalized graded recovery gap is the optimizer's weighted norm divided by the
absolute value of its missing coefficient. -/
theorem cubicGradedRecoveryGap_eq_div (k : ℕ) {T : Polynomial ℝ}
    (hT : IsCubicChebyshev (k + 1) T) :
    cubicGradedRecoveryGap k = cubicWeightedIntervalNorm (k + 1) T / |T.coeff k| := by
  obtain ⟨hmem, hminS, hval⟩ := coeffSet_minimizer_value (cubicIntervalWeight_isWeight (k + 1))
    (cubicIntervalWeight_pos (k + 1) (by omega)) hT.mem hT.minimal (show k ≤ k + 1 by omega)
  have hleast : IsLeast (cubicHomogeneousRecoveryErrors k)
      (wsup (cubicIntervalWeight (k + 1)) 0 (1/4)
        (Polynomial.C (T.coeff k)⁻¹ * T)) := by
    rw [cubicHomogeneousRecoveryErrors_interval, cubicWeightedIntervalNorm_eq]
    refine ⟨⟨_, hmem, rfl⟩, ?_⟩
    rintro y ⟨p, hp, rfl⟩
    exact hminS p hp
  rw [(cubicGradedRecoveryGap_isLeast k).unique hleast, hval, cubicWeightedIntervalNorm_eq]

/-- **The exact graded recovery gap.** For every weight there is a weighted Chebyshev optimizer of
degree `k+1` with `k+1` distinct roots in `(0,1/4)`; the physical recovery gap is its weighted norm
divided by the sum of those roots, and the optimal normalized residual is unique. -/
theorem cubicGradedRecoveryGap_eq_rootSum (k : ℕ) :
    ∃ (T : Polynomial ℝ) (s : Finset ℝ), IsCubicChebyshev (k + 1) T ∧
      0 < cubicWeightedIntervalNorm (k + 1) T ∧
      s.card = k + 1 ∧ (∀ r ∈ s, 0 < r ∧ r < 1/4) ∧
      T = ∏ r ∈ s, (Polynomial.X - Polynomial.C r) ∧
      0 < ∑ r ∈ s, r ∧
      cubicGradedRecoveryGap k = cubicWeightedIntervalNorm (k + 1) T / ∑ r ∈ s, r ∧
      (∀ R : Polynomial ℝ, R.natDegree ≤ k + 1 → R.coeff k = 1 →
        cubicWeightedIntervalNorm (k + 1) R = cubicGradedRecoveryGap k →
        R = Polynomial.C (T.coeff k)⁻¹ * T) := by
  obtain ⟨T, hT, hTpos⟩ := exists_isCubicChebyshev (k + 1)
  obtain ⟨s, hcard, hspos, hprod, hcoeff, hsum⟩ :=
    isCubicChebyshev_roots (k + 1) (by omega) hT
  have habs : |T.coeff k| = ∑ r ∈ s, r := by
    rw [show k = (k + 1) - 1 from by omega, hcoeff, abs_neg, abs_of_pos hsum]
  refine ⟨T, s, hT, hTpos, hcard, hspos, hprod, hsum, ?_, ?_⟩
  · rw [cubicGradedRecoveryGap_eq_div k hT, habs]
  · intro R hR1 hR2 hRval
    refine isCubicChebyshev_normalized_unique (k + 1) (by omega) hT (show k ≤ k + 1 by omega)
      hR1 hR2 ?_
    intro p hp1 hp2
    rw [hRval]
    exact (cubicGradedRecoveryGap_isLeast k).2 (by
      rw [cubicHomogeneousRecoveryErrors_interval]
      exact ⟨p, ⟨hp1, hp2⟩, rfl⟩)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
