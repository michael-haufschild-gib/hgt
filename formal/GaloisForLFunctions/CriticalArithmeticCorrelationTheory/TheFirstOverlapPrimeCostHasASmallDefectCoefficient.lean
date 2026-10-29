import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.IntegerSeparationShrinksTheNonRatioPrimeRows
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheArchimedeanCrossEnergyIsOneSided

/-!
# A small prime-defect cost for the first genuine overlap

The actual non-ratio prime form is bounded by a constant times
`((c-1)+1/N) * (D_N(x)+sum x_n^2)` throughout `1<=c<=2`.
The overlap length pays the small factor; the divisor identity pays the
remaining top-row logarithm. No prime-pair cancellation is assumed.
-/

noncomputable section

open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry RenormalizedArithmeticPotentialTheory

private def firstOverlapRowConstant : ℝ :=
  4 * (Real.log 4 + 4) * Real.exp (5 / 2) +
    4 * Real.exp (3 / 2) * (3 + 2 * psiConstant)

private theorem firstOverlapRowConstant_pos : 0 < firstOverlapRowConstant := by
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  have hpsi := psiConstant_pos
  unfold firstOverlapRowConstant
  positivity

private theorem sum_nonRatioRow_le_defect {c : ℝ} (hc0 : 0 ≤ c) (hc2 : c ≤ 2)
    {N : ℕ} (hN : 2 ≤ N) (x : ℕ → ℝ) :
    (∑ m ∈ Icc 1 N, x m ^ 2 * nonRatioRow (c / N) N m) ≤
      firstOverlapRowConstant * (poleDefect N x + ∑ m ∈ Icc 1 N, x m ^ 2) := by
  let S : ℝ := ∑ m ∈ Icc 1 N, x m ^ 2
  let T : ℝ := ∑ m ∈ Icc 1 N, (m : ℝ) / N * Real.log m * x m ^ 2
  let A : ℝ := 4 * (Real.log 4 + 4) * Real.exp (5 / 2)
  let B : ℝ := 4 * Real.exp (3 / 2)
  have hA : 0 ≤ A := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    dsimp only [A]
    positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hS : 0 ≤ S := sum_nonneg fun m _ => sq_nonneg _
  have hD : 0 ≤ poleDefect N x := poleDefect_nonneg N x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hrow : ∀ m ∈ Icc 1 N,
      nonRatioRow (c / N) N m ≤ A + B * ((m : ℝ) / N * Real.log m + 1) := by
    intro m hm
    have h := nonRatioRow_le_of_ratio (K := 2) (show 1 ≤ N by omega)
      (div_nonneg hc0 hN0.le) ((div_le_one hN0).mpr (hc2.trans hN2))
      (div_le_div_of_nonneg_right hc2 hN0.le) (mem_Icc.mp hm).1
    have hmN : (m : ℝ) / N ≤ 1 :=
      (div_le_one hN0).mpr (by exact_mod_cast (mem_Icc.mp hm).2)
    calc
      _ ≤ A + B * ((m : ℝ) / N) * (Real.log m + 1) := by
        dsimp only [A, B]
        convert h using 1
        ring
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hmN hB]
  have hsum : (∑ m ∈ Icc 1 N, x m ^ 2 * nonRatioRow (c / N) N m) ≤
      A * S + B * (T + S) := by
    calc
      _ ≤ ∑ m ∈ Icc 1 N, x m ^ 2 * (A + B * ((m : ℝ) / N * Real.log m + 1)) :=
        sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _)
      _ = _ := by
        simp only [S, T, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun m _ => by ring
  have htop : T ≤ 2 * poleDefect N x + 2 * psiConstant * S := by
    simpa only [T, S, one_div_one, one_add_one_eq_two] using
      sum_top_le_poleDefect_param N x (show (0 : ℝ) < 1 by norm_num)
  have hC : firstOverlapRowConstant = A + B * (3 + 2 * psiConstant) := rfl
  have hpsi := psiConstant_pos.le
  have hCD : 2 * B ≤ firstOverlapRowConstant := by
    rw [hC]
    nlinarith only [hA, hB, mul_nonneg hB hpsi]
  have hCS : A + B * (1 + 2 * psiConstant) ≤ firstOverlapRowConstant := by
    rw [hC]
    nlinarith only [hB]
  calc
    _ ≤ A * S + B * (T + S) := hsum
    _ ≤ 2 * B * poleDefect N x + (A + B * (1 + 2 * psiConstant)) * S := by
      nlinarith only [mul_le_mul_of_nonneg_left htop hB]
    _ ≤ firstOverlapRowConstant * poleDefect N x + firstOverlapRowConstant * S :=
      add_le_add (mul_le_mul_of_nonneg_right hCD hD) (mul_le_mul_of_nonneg_right hCS hS)
    _ = _ := by rw [mul_add]

private theorem normalized_overlap_length_le {c : ℝ} (hc : 1 ≤ c)
    {N : ℕ} (hN : 1 ≤ N) :
    max 0 (c / N - 1 / ((N : ℝ) + 1)) / (c / N) ≤ c - 1 + 1 / (N : ℝ) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : 0 < (N : ℝ) + 1 := by positivity
  have hr : 1 / ((N : ℝ) + 1) ≤ 1 / (N : ℝ) :=
    one_div_le_one_div_of_le hN0 (by linarith)
  have hgap : 0 ≤ c / N - 1 / ((N : ℝ) + 1) := sub_nonneg.mpr
    (hr.trans (div_le_div_of_nonneg_right hc hN0.le))
  rw [max_eq_right hgap]
  have hnum : 0 ≤ c - 1 + 1 / ((N : ℝ) + 1) :=
    add_nonneg (sub_nonneg.mpr hc) (by positivity)
  calc
    _ = (c - 1 + 1 / ((N : ℝ) + 1)) / c := by
      field_simp [hN0.ne', hN1.ne', hc0.ne']
      ring
    _ ≤ c - 1 + 1 / ((N : ℝ) + 1) := div_le_self hnum hc
    _ ≤ _ := add_le_add le_rfl hr

/-- An explicit profile-height constant pays the whole normalized prime correction
by a small multiple of the actual prime defect and coefficient mass. -/
theorem abs_normalized_nonRatioForm_le_small_defect {φ : ℝ → ℝ} {B : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (hB : 0 ≤ B) (hheight : ∀ u, |φ u| ≤ B)
    {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) {N : ℕ} (hN : 2 ≤ N) (x : ℕ → ℝ) :
    |nonRatioForm (atomDilate φ (c / N)) N x| / (∫ u, atomDilate φ (c / N) u ^ 2) ≤
      (B ^ 2 / (∫ u, φ u ^ 2) * firstOverlapRowConstant) * (c - 1 + 1 / (N : ℝ)) *
        (poleDefect N x + ∑ m ∈ Icc 1 N, x m ^ 2) := by
  let w : ℝ := c / N
  let M : ℝ := ∫ u, φ u ^ 2
  let S : ℝ := poleDefect N x + ∑ m ∈ Icc 1 N, x m ^ 2
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw : 0 < w := div_pos hc0 hN0
  obtain ⟨hg, hgsupp, _⟩ := atomDilate_facts hφ hsupp hw
  have hheightg : ∀ u, |atomDilate φ w u| ≤ B := fun u => hheight (u / w)
  have hraw := abs_nonRatioForm_le_overlap_rows hg.continuous hgsupp hw.le hB hheightg N x
  have hrow := sum_nonRatioRow_le_defect hc0.le hc2 hN x
  have hS : 0 ≤ S := add_nonneg (poleDefect_nonneg N x) (sum_nonneg fun m _ => sq_nonneg _)
  have hgeometry := normalized_overlap_length_le hc1 (show 1 ≤ N by omega)
  have hG : 0 < ∫ u, atomDilate φ w u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  calc
    _ ≤ ((B ^ 2 * max 0 (w - 1 / ((N : ℝ) + 1))) *
        ∑ m ∈ Icc 1 N, x m ^ 2 * nonRatioRow w N m) / (∫ u, atomDilate φ w u ^ 2) :=
      div_le_div_of_nonneg_right hraw hG.le
    _ ≤ ((B ^ 2 * max 0 (w - 1 / ((N : ℝ) + 1))) *
        (firstOverlapRowConstant * S)) / (∫ u, atomDilate φ w u ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrow
        (mul_nonneg (sq_nonneg B) (le_max_left _ _))) hG.le
    _ = (B ^ 2 / M * firstOverlapRowConstant * S) *
        (max 0 (w - 1 / ((N : ℝ) + 1)) / w) := by
      rw [integral_atomDilate_sq hw]
      dsimp only [M]
      ring
    _ ≤ (B ^ 2 / M * firstOverlapRowConstant * S) * (c - 1 + 1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hgeometry
        (mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg B) hM.le) firstOverlapRowConstant_pos.le) hS)
    _ = _ := by dsimp only [M, S]; ring

/-- Every actual smooth nonzero profile supplies its own small-overlap prime-defect constant. -/
theorem exists_small_overlap_nonRatio_defect_budget {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 1 ≤ c → c ≤ 2 → ∀ N : ℕ, 2 ≤ N → ∀ x : ℕ → ℝ,
      |nonRatioForm (atomDilate φ (c / N)) N x| / (∫ u, atomDilate φ (c / N) u ^ 2) ≤
        C * (c - 1 + 1 / (N : ℝ)) * (poleDefect N x + ∑ m ∈ Icc 1 N, x m ^ 2) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  obtain ⟨L, hL, hLip⟩ := ArithmeticCriticalityTheory.exists_lipschitz_bound_of_compactSupport
    (hφ.of_le (by norm_num)) hφc
  let B : ℝ := 1 + 2 * L
  have hB : 0 < B := by dsimp only [B]; positivity
  have hm : φ (-1) = 0 := hsupp (-1) (by norm_num)
  have hheight : ∀ u, |φ u| ≤ B := by
    intro u
    by_cases hu : u ∈ Set.Icc 0 1
    · have h := hLip (-1) u
      have hu0 : 0 ≤ u + 1 := by linarith only [hu.1]
      simp only [hm, sub_zero, sub_neg_eq_add, abs_of_nonneg hu0] at h
      calc
        _ ≤ L * (u + 1) := h
        _ ≤ L * 2 := mul_le_mul_of_nonneg_left (by linarith only [hu.2]) hL
        _ ≤ B := by dsimp only [B]; linarith
    · rw [hsupp u hu, abs_zero]
      exact hB.le
  refine ⟨B ^ 2 / (∫ u, φ u ^ 2) * firstOverlapRowConstant,
    mul_pos (div_pos (sq_pos_of_pos hB) hM) firstOverlapRowConstant_pos, ?_⟩
  intro c hc1 hc2 N hN x
  exact abs_normalized_nonRatioForm_le_small_defect hφ hsupp hM hB.le hheight hc1 hc2 hN x

/-- A positive interval of genuine overlaps has arbitrarily small prime-defect cost,
with one horizon for all ratios in that interval and all vectors. -/
theorem exists_overlap_interval_with_small_nonRatio_cost {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ᶠ N : ℕ in atTop,
      ∀ c : ℝ, 1 ≤ c → c ≤ 1 + δ → ∀ x : ℕ → ℝ,
        |nonRatioForm (atomDilate φ (c / N)) N x| / (∫ u, atomDilate φ (c / N) u ^ 2) ≤
          ε * (poleDefect N x + ∑ m ∈ Icc 1 N, x m ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_small_overlap_nonRatio_defect_budget hφ hsupp hM
  let δ := min 1 (ε / (2 * C))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hCδ : C * δ ≤ ε / 2 := by
    have h := mul_le_mul_of_nonneg_left (min_le_right 1 (ε / (2 * C))) hC.le
    calc
      _ ≤ C * (ε / (2 * C)) := h
      _ = _ := by field_simp [hC.ne']
  have hlim : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine ⟨δ, hδ, hδ1, ?_⟩
  filter_upwards [eventually_ge_atTop 2,
    hlim.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity))] with N hN hsmall
  intro c hc1 hcδ x
  have hcost : C * (c - 1 + 1 / (N : ℝ)) ≤ ε := by
    have h := mul_le_mul_of_nonneg_left (show c - 1 ≤ δ by linarith only [hcδ]) hC.le
    rw [mul_add, mul_one_div]
    linarith only [h, hCδ, hsmall]
  exact (hb c hc1 (by linarith only [hcδ, hδ1]) N hN x).trans
    (mul_le_mul_of_nonneg_right hcost
      (add_nonneg (poleDefect_nonneg N x) (sum_nonneg fun m _ => sq_nonneg _)))

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_small_overlap_nonRatio_defect_budget
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_overlap_interval_with_small_nonRatio_cost
