import GaloisForLFunctions.RHTower.Sieve.InghamRightEdgePowerSaving

/-!
# Eventual pointwise nonvanishing of Ingham's right edge

Above `Re s = 1`, the sharp Möbius convolution defect is an absolutely convergent Dirichlet series
supported strictly beyond the cutoff. Its absolute tail tends to zero uniformly in the ordinate.
Consequently `|zeta(s) M_X(s) - 1| < 1` on every fixed right edge for all large cutoffs, so the
classical factor `1 - (zeta M_X - 1)^2` and the pole-regularized detector are pointwise nonzero on
the whole edge. This supplies the right-boundary premise of Route T's weighted Littlewood identity.
-/

open Complex MeasureTheory Set Filter Topology ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

noncomputable def inghamRightEdgeAbsoluteTail (beta : ℝ) (X : ℕ) : ℝ :=
  ∑' k : ℕ, (((k + (X + 1)).divisors.card : ℝ) *
    ((k + (X + 1) : ℕ) : ℝ) ^ (-beta))

theorem tendsto_inghamRightEdgeAbsoluteTail_zero {beta : ℝ} (hbeta : 1 < beta) :
    Tendsto (inghamRightEdgeAbsoluteTail beta) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun n => (n.divisors.card : ℝ) * (n : ℝ) ^ (-beta)
  have ha : Summable a := summable_card_divisors_mul_rpow hbeta
  have ht := (tendsto_sum_nat_add a).comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun X => ∑' k : ℕ, a (k + (X + 1))) atTop (𝓝 0)
  change Tendsto (fun X => ∑' k : ℕ, a (k + (X + 1))) atTop (𝓝 0) at ht
  exact ht

private theorem norm_LSeriesTerm_moebiusZetaDefect_le
    {beta : ℝ} {X : ℕ} (hX : 1 ≤ X)
    (t : ℝ) (n : ℕ) :
    ‖LSeries.term (complexCoeff (moebiusZetaDefect X))
        ((beta : ℂ) + (t : ℂ) * I) n‖ ≤
      (n.divisors.card : ℝ) * (n : ℝ) ^ (-beta) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [LSeries.norm_term_eq, if_neg hn.ne']
    have hcoeff := norm_complexCoeff_moebiusZetaDefect_le_card_divisors hX n
    have hre : (((beta : ℂ) + (t : ℂ) * I)).re = beta := by simp
    rw [hre, div_eq_mul_inv, ← Real.rpow_neg hnR.le]
    exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hnR.le _)

theorem norm_inghamMollifiedError_right_le_absoluteTail
    {beta : ℝ} (hbeta : 1 < beta) {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    ‖riemannZeta ((beta : ℂ) + (t : ℂ) * I) *
          inghamMollifier X ((beta : ℂ) + (t : ℂ) * I) - 1‖ ≤
      inghamRightEdgeAbsoluteTail beta X := by
  let s : ℂ := (beta : ℂ) + (t : ℂ) * I
  let coeff : ℕ → ℂ := complexCoeff (moebiusZetaDefect X)
  let major : ℕ → ℝ := fun n => (n.divisors.card : ℝ) * (n : ℝ) ^ (-beta)
  have hmajor : Summable major := summable_card_divisors_mul_rpow hbeta
  have htermLe : ∀ n, ‖LSeries.term coeff s n‖ ≤ major n := by
    intro n
    exact norm_LSeriesTerm_moebiusZetaDefect_le hX t n
  have hterm : Summable (fun n => ‖LSeries.term coeff s n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) htermLe hmajor
  have hshiftTerm :
      ∑' n, ‖LSeries.term coeff s n‖ =
        ∑' k, ‖LSeries.term coeff s (k + X + 1)‖ := by
    have hsplit := hterm.sum_add_tsum_nat_add (X + 1)
    have hzero : ∑ n ∈ Finset.range (X + 1), ‖LSeries.term coeff s n‖ = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hc0 : coeff n = 0 := by
        dsimp only [coeff]
        rw [complexCoeff_apply,
          moebiusZetaDefect_vanishesBelow X n (Finset.mem_range.mp hn)]
        simp
      simp only [LSeries.term_def, hc0, norm_eq_zero]
      split_ifs <;> simp
    rw [hzero, zero_add] at hsplit
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm
  have hmajorShift : Summable (fun k => major (k + X + 1)) := by
    simpa [Nat.add_assoc] using (summable_nat_add_iff (X + 1)).mpr hmajor
  have htermShift : Summable (fun k => ‖LSeries.term coeff s (k + X + 1)‖) := by
    simpa [Nat.add_assoc] using (summable_nat_add_iff (X + 1)).mpr hterm
  have htailBound :
      (∑' k, ‖LSeries.term coeff s (k + X + 1)‖) ≤
        ∑' k, major (k + X + 1) := by
    exact Summable.tsum_le_tsum (fun k => htermLe (k + X + 1)) htermShift hmajorShift
  have hseries :
      ‖LSeries coeff s‖ ≤ ∑' k, major (k + X + 1) := by
    calc
      ‖LSeries coeff s‖ = ‖∑' n, LSeries.term coeff s n‖ := rfl
      _ ≤ ∑' n, ‖LSeries.term coeff s n‖ := norm_tsum_le_tsum_norm hterm
      _ = ∑' k, ‖LSeries.term coeff s (k + X + 1)‖ := hshiftTerm
      _ ≤ ∑' k, major (k + X + 1) := htailBound
  have hEq : riemannZeta s * inghamMollifier X s - 1 =
      -LSeries coeff s := by
    rw [LSeries_complexCoeff_moebiusZetaDefect_eq X (by simp [s]; exact hbeta)]
    ring
  rw [show (beta : ℂ) + (t : ℂ) * I = s from rfl, hEq, norm_neg]
  simpa only [inghamRightEdgeAbsoluteTail, major, Nat.add_assoc] using hseries

theorem eventually_inghamDetector_ne_zero_on_rightEdge
    {beta : ℝ} (hbeta : 1 < beta) :
    ∀ᶠ X : ℕ in atTop, ∀ t : ℝ,
      inghamDetector X ((beta : ℂ) + (t : ℂ) * I) ≠ 0 := by
  have htail := tendsto_inghamRightEdgeAbsoluteTail_zero hbeta
  have hsmall : ∀ᶠ X : ℕ in atTop, inghamRightEdgeAbsoluteTail beta X < 1 :=
    htail.eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with X htailX hX
  intro t
  let s : ℂ := (beta : ℂ) + (t : ℂ) * I
  let e : ℂ := riemannZeta s * inghamMollifier X s - 1
  have hs1 : s ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp [s] at hre
    linarith
  have heNorm : ‖e‖ < 1 := lt_of_le_of_lt
    (norm_inghamMollifiedError_right_le_absoluteTail hbeta hX t) htailX
  have hclassical : 1 - e ^ 2 ≠ 0 := by
    intro hz
    have heq : e ^ 2 = 1 := (sub_eq_zero.mp hz).symm
    have hn := congrArg norm heq
    rw [norm_pow, norm_one] at hn
    nlinarith [norm_nonneg e]
  rw [inghamDetector_eq_poleCleared X hs1]
  exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hs1)) hclassical

theorem eventually_inghamDetector_ne_zero_on_powerSavingRightEdge :
    ∀ᶠ X : ℕ in atTop, ∀ t : ℝ,
      inghamDetector X
        ((inghamPowerSavingRightEdge : ℂ) + (t : ℂ) * I) ≠ 0 := by
  exact eventually_inghamDetector_ne_zero_on_rightEdge
    (by norm_num [inghamPowerSavingRightEdge])

end

end RHTower.Sieve

