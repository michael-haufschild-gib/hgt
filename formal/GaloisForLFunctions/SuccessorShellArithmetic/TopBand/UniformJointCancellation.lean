import GaloisForLFunctions.SuccessorShellArithmetic.TheShellsAndThePoleCancelOnTheTopBand

/-!
# Joint top-band cancellation uniform in overlap

The cell remainder is proportional to `(G + A₁)/N`, where `A₁` belongs to the fixed
profile and `G = (c/N)∫φ²`. Keeping this factor gives `Oφ(G(c + log N))` throughout
`1 ≤ c ≤ N/4`. Thus the logarithmic top-band bound remains uniform for growing
overlap `c ≤ log N`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.SuccessorShellArithmetic

open RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- A single profile constant controls every overlap up to a quarter of the horizon. -/
theorem exists_abs_jointWitnessCoefficient_le_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c : ℝ) (N : ℕ), 1 ≤ c → 8 ≤ N → 4 * c ≤ N →
      |jointWitnessCoefficient (atomDilate φ (c / N)) N (c / N)| ≤
        K * (∫ u, atomDilate φ (c / N) u ^ 2) * (c + 1 + Real.log N) := by
  obtain ⟨A₁, hA₁0, hA₁⟩ := exists_abs_deriv_shellAutocorr_le hφ hsupp
  set M := ∫ u, φ u ^ 2
  set q := (1 / 4 : ℝ) + A₁ / M
  have hq : 0 ≤ q := add_nonneg (by norm_num) (div_nonneg hA₁0 hM.le)
  refine ⟨19 + 84 * q, by positivity, fun c N hc1 hN8 hNc => ?_⟩
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog := Real.log_natCast_nonneg N
  have hw : c / (N : ℝ) ≤ 1 / 4 := by
    rw [div_le_iff₀ hN0]
    linarith only [hNc]
  set G := ∫ u, atomDilate φ (c / N) u ^ 2
  have hG : G = (c / N) * M := integral_atomDilate_sq (div_pos hc hN0)
  have hG0 : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have heq : (18 * c + 24) * ((G + A₁) / N) =
      (18 + 24 / c) * (c / N + A₁ / M) * G := by
    rw [hG]
    field_simp [hc.ne', hN0.ne', hM.ne']
  have hratio : 24 / c ≤ (24 : ℝ) := by
    rw [div_le_iff₀ hc]
    linarith only [hc1]
  have hrow : (18 * c + 24) * ((G + A₁) / N) ≤ 42 * q * G := by
    rw [heq]
    apply mul_le_mul_of_nonneg_right _ hG0
    apply mul_le_mul
      (show 18 + 24 / c ≤ (42 : ℝ) by linarith only [hratio])
      (show c / N + A₁ / M ≤ q by dsimp only [q]; linarith only [hw])
      (add_nonneg (div_nonneg hc.le hN0.le) (div_nonneg hA₁0 hM.le))
      (by norm_num)
  have herror : (18 * c + 24) * (2 + Real.log N) * ((G + A₁) / N) ≤
      84 * q * (1 + Real.log N) * G := by
    calc
      _ = ((18 * c + 24) * ((G + A₁) / N)) * (2 + Real.log N) := by ring
      _ ≤ (42 * q * G) * (2 + Real.log N) :=
        mul_le_mul_of_nonneg_right hrow (by positivity)
      _ ≤ 84 * q * (1 + Real.log N) * G := by
        have hqG : 0 ≤ q * G := mul_nonneg hq hG0
        nlinarith only [hqG, hlog]
  have hbound := abs_jointWitnessCoefficient_le_rowRemainder hφ hsupp hM hc hA₁0 hA₁ hN8 hNc
  refine hbound.trans ?_
  have hfirst : 17 * c * G ≤ 17 * (c + 1 + Real.log N) * G :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith only [hlog]) (by norm_num : (0 : ℝ) ≤ 17)) hG0
  have hsecond : (2 + 84 * q) * (1 + Real.log N) * G ≤
      (2 + 84 * q) * (c + 1 + Real.log N) * G :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith only [hc.le]) (by positivity)) hG0
  have hlogG : 2 * Real.log N * G ≤ 2 * (1 + Real.log N) * G := by
    nlinarith only [hG0]
  nlinarith only [herror, hfirst, hsecond, hlogG]

/-- On logarithmic overlaps, the joint coefficient has one bound independent of the overlap. -/
theorem exists_abs_jointWitnessCoefficient_le_uniform_log_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c : ℝ) (N : ℕ), 1 ≤ c → c ≤ Real.log N →
      8 ≤ N → 4 * c ≤ N →
        |jointWitnessCoefficient (atomDilate φ (c / N)) N (c / N)| ≤
          K * (∫ u, atomDilate φ (c / N) u ^ 2) * (1 + Real.log N) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_abs_jointWitnessCoefficient_le_uniform_overlap hφ hsupp hM
  refine ⟨2 * K, mul_pos two_pos hK, fun c N hc hlog hN hNc => ?_⟩
  refine (hbound c N hc hN hNc).trans ?_
  have hG : 0 ≤ ∫ u, atomDilate φ (c / N) u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have h := mul_le_mul_of_nonneg_left
    (show c + 1 + Real.log N ≤ 2 * (1 + Real.log N) by linarith only [hlog])
    (mul_nonneg hK.le hG)
  nlinarith only [h]

#print axioms exists_abs_jointWitnessCoefficient_le_uniform_overlap
#print axioms exists_abs_jointWitnessCoefficient_le_uniform_log_overlap

end GaloisForLFunctions.SuccessorShellArithmetic
