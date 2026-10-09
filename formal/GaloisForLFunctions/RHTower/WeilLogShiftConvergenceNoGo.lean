import GaloisForLFunctions.RHTower.WeilLogShiftSampledPotentialCone

/-!
# Convergence is essential for totalized potential criteria

A diagonal reciprocal-kernel construction gives a zero-excess minorant whose
signed potential partial sums tend to minus infinity at every integer-log sample.
The totalized `tsum` potentials nevertheless vanish at all these samples and at
the origin. Thus their inequalities alone do not imply asymptotic positivity.
The sparse-convergence criterion remains the exact positive survivor.
-/

open Filter Topology

namespace RHTower

open WeilExcess

/-- A single nonnegative weight can dominate any prescribed nonnegative envelope
against every member of a countable family of strictly positive kernels.
The construction vanishes below index two and uses only a finite reciprocal sum. -/
theorem exists_nonneg_diagonal_weight_for_positive_kernels
    (P : ℕ → ℕ → ℝ) (hP : ∀ m n : ℕ, 0 < P m n)
    (r : ℕ → ℝ) (hr : ∀ n : ℕ, 0 ≤ r n) :
    ∃ v : ℕ → ℝ, (∀ n, 0 ≤ v n) ∧ (∀ n, n < 2 → v n = 0) ∧
      ∀ m n : ℕ, 2 ≤ n → m ≤ n → r n ≤ v n * P m n := by
  let v (n : ℕ) := if 2 ≤ n then r n * ∑ j ∈ Finset.range (n + 1), (P j n)⁻¹ else 0
  refine ⟨v, ?_, ?_, ?_⟩
  · intro n
    dsimp only [v]
    split_ifs with hn
    · exact mul_nonneg (hr n) (Finset.sum_nonneg fun j _ => inv_nonneg.mpr (hP j n).le)
    · exact le_rfl
  · intro n hn
    simp only [v, if_neg (by omega : ¬2 ≤ n)]
  · intro m n hn hmn
    have hinv : (P m n)⁻¹ ≤ ∑ j ∈ Finset.range (n + 1), (P j n)⁻¹ :=
      Finset.single_le_sum (fun j _ => inv_nonneg.mpr (hP j n).le)
        (Finset.mem_range.mpr (by omega))
    have hdiag : 1 ≤ (∑ j ∈ Finset.range (n + 1), (P j n)⁻¹) * P m n := by
      simpa only [inv_mul_cancel₀ (hP m n).ne'] using
        mul_le_mul_of_nonneg_right hinv (hP m n).le
    dsimp only [v]
    rw [if_pos hn]
    calc
      r n = r n * 1 := by ring
      _ ≤ r n * ((∑ j ∈ Finset.range (n + 1), (P j n)⁻¹) * P m n) :=
        mul_le_mul_of_nonneg_left hdiag (hr n)
      _ = _ := by ring

/-- An unconditional zero-excess counterexample: every sampled signed series
diverges to minus infinity, but all its totalized potential values are zero.
It is a strict minorant at two and fails asymptotic log-shift positivity. -/
theorem exists_zero_excess_divergent_potential :
    ∃ lam : ℕ → ℝ,
      (∀ n : ℕ, lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) ∧
      lam 2 < (ArithmeticFunction.vonMangoldt 2 : ℝ) ∧
      (∀ n : ℕ, deviationExcess lam n = 0) ∧
      (∀ m : ℕ, ¬Summable fun n : ℕ => weilDeviation lam n *
        (riemannAutocorr (Real.log m + Real.log n) + riemannAutocorr (Real.log m - Real.log n))) ∧
      (∀ m : ℕ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, weilDeviation lam n *
        (riemannAutocorr (Real.log m + Real.log n) + riemannAutocorr (Real.log m - Real.log n)))
        atTop atBot) ∧
      deviationPotential lam 0 = 0 ∧
      (∀ m : ℕ, deviationPotential lam (Real.log m) = 0) ∧
      ¬WeilLogShiftAsymptoticPositive lam := by
  let P (m n : ℕ) := riemannAutocorr (Real.log m + Real.log n) +
    riemannAutocorr (Real.log m - Real.log n)
  have hP (m n : ℕ) : 0 < P m n := add_pos (riemannAutocorr_pos _) (riemannAutocorr_pos _)
  obtain ⟨v, hv, hvsmall, hdiag⟩ := exists_nonneg_diagonal_weight_for_positive_kernels
    P hP (fun _ => 1) (fun _ => by norm_num)
  let lam (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ) - Real.sqrt n * v n
  have hminor (n : ℕ) : lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    sub_le_self _ (mul_nonneg (Real.sqrt_nonneg _) (hv n))
  have hdev (n : ℕ) : weilDeviation lam n = -v n := by
    by_cases hn : 2 ≤ n
    · rw [weilDeviation, if_pos hn]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnpos).ne'
      dsimp only [lam]
      field_simp [hsqrt]
      ring
    · rw [weilDeviation, if_neg hn, hvsmall n (by omega), neg_zero]
  have hexcess (n : ℕ) : deviationExcess lam n = 0 := by
    rw [deviationExcess, hdev, max_eq_right (neg_nonpos.mpr (hv n))]
  have hexc : Summable (deviationExcess lam) := by
    exact summable_zero.congr fun n => (hexcess n).symm
  have hv2 : 0 < v 2 := (mul_pos_iff_of_pos_right (hP 0 2)).mp
    (lt_of_lt_of_le zero_lt_one (hdiag 0 2 (by omega) (by omega)))
  have hstrict : lam 2 < (ArithmeticFunction.vonMangoldt 2 : ℝ) := by
    have hdelta : 0 < Real.sqrt (2 : ℕ) * v 2 :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) hv2
    dsimp only [lam]
    linarith only [hdelta]
  have hnonneg (m n : ℕ) : 0 ≤ v n * P m n := mul_nonneg (hv n) (hP m n).le
  have hevent (m : ℕ) : ∀ᶠ n : ℕ in atTop, -(v n * P m n) ≤ -1 := by
    refine eventually_atTop.mpr ⟨max 2 m, fun n hn => ?_⟩
    have h := hdiag m n ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
    linarith only [h]
  have hnotpos (m : ℕ) : ¬Summable fun n : ℕ => v n * P m n := by
    intro hs
    have hbad : (0 : ℝ) ≤ -1 := le_of_tendsto hs.neg.tendsto_atTop_zero (hevent m)
    norm_num at hbad
  have hnotsigned (m : ℕ) : ¬Summable fun n : ℕ => weilDeviation lam n * P m n := by
    intro hs
    apply hnotpos m
    simpa only [hdev, neg_mul, neg_neg] using hs.neg
  have hdivsigned (m : ℕ) : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, weilDeviation lam n * P m n) atTop atBot := by
    have hpos := (not_summable_iff_tendsto_nat_atTop_of_nonneg (hnonneg m)).mp (hnotpos m)
    have hneg := tendsto_neg_atTop_atBot.comp hpos
    simpa only [Function.comp_def, hdev, neg_mul, Finset.sum_neg_distrib] using hneg
  have hpot (m : ℕ) : deviationPotential lam (Real.log m) = 0 :=
    tsum_eq_zero_of_not_summable (hnotsigned m)
  have hzero : deviationPotential lam 0 = 0 := by
    simpa only [Nat.cast_one, Real.log_one] using hpot 1
  refine ⟨lam, hminor, hstrict, hexcess, hnotsigned, hdivsigned, hzero, hpot, ?_⟩
  intro hpos
  exact hnotsigned 2 (summable_potential_of_logShiftAsymptoticPositive hpos hexc (Real.log 2))

/-- Totalized potential inequalities alone are not a valid receiver for
asymptotic positivity, even when the excess is identically zero in the witness. -/
theorem not_logShift_potential_only_receiver :
    ¬(∀ lam : ℕ → ℝ, Summable (deviationExcess lam) →
      (∀ m : ℕ, 2 ≤ m → deviationPotential lam 0 ≤ deviationPotential lam (Real.log m)) →
      WeilLogShiftAsymptoticPositive lam) := by
  intro hreceiver
  obtain ⟨lam, _, _, hexcess, _, _, hzero, hpot, hnot⟩ := exists_zero_excess_divergent_potential
  have hexc : Summable (deviationExcess lam) := by
    exact summable_zero.congr fun n => (hexcess n).symm
  apply hnot (hreceiver lam hexc ?_)
  intro m _
  simp only [hzero, hpot m, le_refl]

end RHTower
