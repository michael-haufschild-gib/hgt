import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.ElevenPacket
import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.ElevenTrialMargin
import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.PrimeFlipCompleteForm

/-!
# A fixed-width negative witness for the eleven flip

The unit-sign prime-square trial has a negative completed upper limit at
ratio `99 / 100`. Exact zero padding along integer-multiple horizons carries
the same tests to larger rational ratios without a width-continuity argument.
-/

noncomputable section

open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

open RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics
  ArithmeticCountingPositivity SpacingScaleHarmonicAnalysis

/-- The explicit eleven-square test at a strictly separated width. -/
def elevenTrialTest (N : ℕ) : ℝ → ℝ :=
  atomicTest N (fun n => primeSquareTrial 11 n / Real.sqrt n)
    (atomDilate transMetzlerProfile ((99 / 100) / N))

/-- An upper bound on the complete twisted energy in logarithmic atom-mass units. -/
def elevenUpperEnergy (N : ℕ) : ℝ :=
  weilQuad (elevenTrialTest N) / (((99 / 100) / N) * Real.log N) +
    (∫ u, transMetzlerProfile u ^ 2) * (primeSquareFlipBound 11 N / Real.log N)

theorem tendsto_elevenUpperEnergy :
    Tendsto elevenUpperEnergy atTop
      (𝓝 ((∫ u, transMetzlerProfile u ^ 2) * elevenTrialUpperMargin)) := by
  have h := tendsto_elevenTrial_weil.add
    ((tendsto_primeSquareFlipBound (by norm_num : Nat.Prime 11)).const_mul
      (∫ u, transMetzlerProfile u ^ 2))
  have heq :
      (∫ u, transMetzlerProfile u ^ 2) *
        (completeWeilSelfFinitePart transMetzlerProfile (99 / 100) + 4 * Real.log 11 / 11 +
          completeWeilPoleShift transMetzlerProfile (99 / 100) * (101 / 121 : ℝ) ^ 2) +
        (∫ u, transMetzlerProfile u ^ 2) *
          (-4 * Real.log (11 : ℕ) / (11 : ℕ) + 4 * Real.log (11 : ℕ) *
            (2 / ((11 : ℕ) : ℝ) ^ 3 + 1 / (((11 : ℕ) : ℝ) ^ 2 * (((11 : ℕ) : ℝ) - 1)))) =
      (∫ u, transMetzlerProfile u ^ 2) * elevenTrialUpperMargin := by
    norm_num only [Nat.cast_ofNat, elevenTrialUpperMargin, elevenPrimeTailCost]
    ring
  rw [heq] at h
  exact h

theorem eventually_elevenTrial_le_upper :
    ∀ᶠ N : ℕ in atTop,
      weilQuadTw (primeFlipWeight 11) (elevenTrialTest N) /
        (((99 / 100) / N) * Real.log N) ≤ elevenUpperEnergy N := by
  filter_upwards [eventually_div_horizon_lt_atomSpacing
    (by norm_num : (0 : ℝ) < 99 / 100) (by norm_num : (99 / 100 : ℝ) < 1),
    eventually_ge_atTop 2] with N hsep hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw : (0 : ℝ) < (99 / 100) / N := by positivity
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  obtain ⟨hg, hsupp, hgc⟩ := atomDilate_facts contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) hw
  have h := div_le_div_of_nonneg_right
    (primeSquareTrial_complete_le hg hgc hsupp hsep.2.2 (by norm_num : Nat.Prime 11))
    (mul_pos hw hlog).le
  rw [add_div, integral_atomDilate_sq hw] at h
  have hscale :
      (((99 / 100 : ℝ) / N) * (∫ u, transMetzlerProfile u ^ 2) * primeSquareFlipBound 11 N) /
          (((99 / 100) / N) * Real.log N) =
        (∫ u, transMetzlerProfile u ^ 2) * (primeSquareFlipBound 11 N / Real.log N) := by
    field_simp [hN0.ne', hw.ne', hlog.ne']
  simpa only [hscale, elevenUpperEnergy, elevenTrialTest] using h

/-- The actual complete eleven-flip form is eventually negative at ratio `99 / 100`. -/
theorem eventually_elevenFlip_negative :
    ∀ᶠ N : ℕ in atTop, weilQuadTw (primeFlipWeight 11) (elevenTrialTest N) < 0 := by
  have hlimit : (∫ u, transMetzlerProfile u ^ 2) * elevenTrialUpperMargin < 0 :=
    mul_neg_of_pos_of_neg integral_transMetzlerProfile_sq_pos elevenTrialUpperMargin_neg
  filter_upwards [eventually_elevenTrial_le_upper,
    tendsto_elevenUpperEnergy.eventually (gt_mem_nhds hlimit), eventually_ge_atTop 2]
    with N hle hneg hN
  have hden : (0 : ℝ) < ((99 / 100) / N) * Real.log N := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact mul_pos (by positivity) (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  have h := (div_lt_iff₀ hden).mp (hle.trans_lt hneg)
  simpa only [zero_mul] using h

/-- Extending an atomic coefficient vector by zero leaves the actual test unchanged. -/
theorem atomicTest_zero_padding {M N : ℕ} (hMN : M ≤ N) (x : ℕ → ℝ) (g : ℝ → ℝ) :
    atomicTest N (fun n => if n ≤ M then x n else 0) g = atomicTest M x g := by
  funext u
  unfold atomicTest
  calc
    _ = ∑ n ∈ Icc 1 M, (if n ≤ M then x n else 0) * g (u - Real.log n) := by
      apply (sum_subset (Icc_subset_Icc_right hMN) ?_).symm
      intro n hn hnM
      have hnot : ¬ n ≤ M := fun h => hnM (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, h⟩)
      simp only [if_neg hnot, zero_mul]
    _ = _ := sum_congr rfl fun n hn => by simp only [if_pos (mem_Icc.mp hn).2]

/-- Rationally related horizons transfer negative tests with exactly the same atom width. -/
theorem frequently_elevenFlip_negative_of_padding {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    {c : ℝ} (hc : (a : ℝ) * c = (b : ℝ) * (99 / 100)) :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (primeFlipWeight 11) (atomicTest N x (atomDilate transMetzlerProfile (c / N))) < 0 := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp eventually_elevenFlip_negative
  rw [Filter.frequently_atTop]
  intro K
  let k := max (max M₀ K) 1
  have hk : 0 < k := (by omega : 0 < (1 : ℕ)).trans_le (le_max_right _ _)
  have hb : 0 < b := ha.trans_le hab
  have hK : K ≤ b * k := calc
    K ≤ k := (le_max_right M₀ K).trans (le_max_left _ _)
    _ = 1 * k := (one_mul k).symm
    _ ≤ b * k := Nat.mul_le_mul_right k hb
  have hM : M₀ ≤ a * k := calc
    M₀ ≤ k := (le_max_left M₀ K).trans (le_max_left _ _)
    _ = 1 * k := (one_mul k).symm
    _ ≤ a * k := Nat.mul_le_mul_right k ha
  refine ⟨b * k, hK, (fun n => if n ≤ a * k then primeSquareTrial 11 n / Real.sqrt n else 0), ?_⟩
  rw [atomicTest_zero_padding (Nat.mul_le_mul_right k hab)]
  have hwidth : c / ((b * k : ℕ) : ℝ) = (99 / 100) / ((a * k : ℕ) : ℝ) := by
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    rw [Nat.cast_mul, Nat.cast_mul]
    apply (div_eq_div_iff (mul_ne_zero hbR hkR) (mul_ne_zero haR hkR)).2
    calc
      _ = ((a : ℝ) * c) * k := by ring
      _ = ((b : ℝ) * (99 / 100)) * k := by rw [hc]
      _ = _ := by ring
  rw [hwidth]
  exact hM₀ (a * k) hM

/-- Ratio two admits infinitely many negative eleven-flip atomic tests. -/
theorem frequently_elevenFlip_negative_two :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (primeFlipWeight 11) (atomicTest N x (atomDilate transMetzlerProfile (2 / N))) < 0 :=
  frequently_elevenFlip_negative_of_padding (a := 99) (b := 200)
    (by norm_num) (by norm_num) (by norm_num)

/-- The eleven flip also fails eventual nonnegativity at the explicit first-overlap ratio. -/
theorem frequently_elevenFlip_negative_cZero :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (primeFlipWeight 11)
        (atomicTest N x (atomDilate transMetzlerProfile (cZero / N))) < 0 :=
  frequently_elevenFlip_negative_of_padding (a := 99 * 10 ^ 18) (b := 100 * (10 ^ 18 + 1))
    (by norm_num) (by norm_num) (by norm_num [cZero, deltaZero])

end GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.eventually_elevenFlip_negative
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.frequently_elevenFlip_negative_two
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.frequently_elevenFlip_negative_cZero
