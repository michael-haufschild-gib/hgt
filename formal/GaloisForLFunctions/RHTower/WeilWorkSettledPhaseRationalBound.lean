import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseRationalProfiles

/-!
# Rational cosine twists have bounded normalized Mellin transforms

Two opposite coefficient choices bound the reciprocal cross term. Periodicity
and induction on the denominator then reach every rational frequency.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem eventually_abs_le_of_tendsto {f : ℝ → ℝ} {L : ℝ}
    (h : Tendsto f (𝓝[>] 1) (𝓝 L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ σ in 𝓝[>] 1, |f σ| ≤ C := by
  refine ⟨|L| + 1, by positivity, ?_⟩
  exact ((h.abs).eventually_lt_const (by linarith : |L| < |L| + 1)).mono
    fun _ hx => hx.le

theorem exists_abs_sourceNormalizedCosineMellin_one_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ σ in 𝓝[>] 1,
      |sourceNormalizedCosineMellin lam 1 σ| ≤ C :=
  eventually_abs_le_of_tendsto (tendsto_sourceNormalizedCosineMellin_one hW)

private def reciprocalWeight (m n : ℕ) (σ : ℝ) : ℝ :=
  (1 / (n : ℝ)) * (((m : ℝ) / n) ^ 2) ^ (-(σ / 2))

private theorem reciprocalWeight_pos {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (σ : ℝ) :
    0 < reciprocalWeight m n σ := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  exact mul_pos (one_div_pos.mpr hn0)
    (Real.rpow_pos_of_pos (sq_pos_of_pos (div_pos hm0 hn0)) _)

private theorem tendsto_reciprocalWeight {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Tendsto (reciprocalWeight m n) (𝓝[>] 1) (𝓝 (reciprocalWeight m n 1)) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : Continuous (reciprocalWeight m n) := by
    exact continuous_const.mul ((Real.continuous_const_rpow
      (pow_ne_zero 2 (div_ne_zero hm0 hn0))).comp (by fun_prop))
  exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

private theorem exists_abs_reciprocal_cross_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ σ in 𝓝[>] 1,
      |reciprocalWeight m n σ * sourceNormalizedCosineMellin lam ((m : ℝ) / n) σ +
        reciprocalWeight n m σ * sourceNormalizedCosineMellin lam ((n : ℝ) / m) σ| ≤ C := by
  let N := max m n
  have hmN : m ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hm, le_max_left _ _⟩
  have hnN : n ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hn, le_max_right _ _⟩
  obtain ⟨Bplus, hBplus⟩ := exists_re_mellin_sourceFiniteCosineProfile_le hW N (sourceTwoLabelCoeff m n 1)
  obtain ⟨Bminus, hBminus⟩ := exists_re_mellin_sourceFiniteCosineProfile_le hW N (sourceTwoLabelCoeff m n (-1))
  obtain ⟨D, hD0, hD⟩ := exists_abs_sourceNormalizedCosineMellin_one_le hW
  let a : ℝ := 1 / (m : ℝ) + 1 / (n : ℝ)
  refine ⟨|Bplus| + |Bminus| + |a| * D, by positivity, ?_⟩
  have hu : ∀ᶠ σ : ℝ in 𝓝[>] 1, σ < 3 / 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (isOpen_Iio.mem_nhds (show (1 : ℝ) ∈ Iio (3 / 2) by norm_num))
  filter_upwards [self_mem_nhdsWithin, hu, hD] with σ hσ hσu hDσ
  have hσ' : 1 < σ := hσ
  have hs0 := sq_nonneg (σ - 1)
  have hs1 : (σ - 1) ^ 2 ≤ 1 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left (hBplus σ hσ' hσu) hs0
  have hm' := mul_le_mul_of_nonneg_left (hBminus σ hσ' hσu) hs0
  rw [re_mellin_sourceTwoLabelProfile hW hmN hnN 1 hσ'] at hp
  rw [re_mellin_sourceTwoLabelProfile hW hmN hnN (-1) hσ'] at hm'
  have hb (B : ℝ) : (σ - 1) ^ 2 * B ≤ |B| :=
    (mul_le_mul_of_nonneg_left (le_abs_self B) hs0).trans
      (mul_le_of_le_one_left (abs_nonneg B) hs1)
  have hd : |a * sourceNormalizedCosineMellin lam 1 σ| ≤ |a| * D := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hDσ (abs_nonneg a)
  have hp' : a * sourceNormalizedCosineMellin lam 1 σ +
      (reciprocalWeight m n σ * sourceNormalizedCosineMellin lam ((m : ℝ) / n) σ +
        reciprocalWeight n m σ * sourceNormalizedCosineMellin lam ((n : ℝ) / m) σ) ≤ |Bplus| := by
    convert hp.trans (hb Bplus) using 1
    · rfl
    · dsimp only [sourceNormalizedCosineMellin, reciprocalWeight, a]
      ring
  have hm'' : a * sourceNormalizedCosineMellin lam 1 σ -
      (reciprocalWeight m n σ * sourceNormalizedCosineMellin lam ((m : ℝ) / n) σ +
        reciprocalWeight n m σ * sourceNormalizedCosineMellin lam ((n : ℝ) / m) σ) ≤ |Bminus| := by
    convert hm'.trans (hb Bminus) using 1
    · rfl
    · dsimp only [sourceNormalizedCosineMellin, reciprocalWeight, a]
      ring
  rw [abs_le] at hd ⊢
  constructor <;> linarith [hd.1, hd.2, abs_nonneg Bplus, abs_nonneg Bminus]

private theorem rational_bound_of_reciprocal {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hrec : ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ σ in 𝓝[>] 1,
      |sourceNormalizedCosineMellin lam ((n : ℝ) / m) σ| ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ σ in 𝓝[>] 1,
      |sourceNormalizedCosineMellin lam ((m : ℝ) / n) σ| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_reciprocal_cross_le hW hm hn
  obtain ⟨D, hD0, hD⟩ := hrec
  obtain ⟨B, hB0, hB⟩ := eventually_abs_le_of_tendsto (tendsto_reciprocalWeight hn hm)
  let a := reciprocalWeight m n 1 / 2
  have ha : 0 < a := half_pos (reciprocalWeight_pos hm hn 1)
  have hlow : ∀ᶠ σ in 𝓝[>] 1, a ≤ reciprocalWeight m n σ :=
    (tendsto_reciprocalWeight hm hn).eventually_const_le
      (half_lt_self (reciprocalWeight_pos hm hn 1))
  refine ⟨(C + B * D) / a, by positivity, ?_⟩
  filter_upwards [hC, hD, hB, hlow] with σ hCσ hDσ hBσ hlowσ
  let x := sourceNormalizedCosineMellin lam ((m : ℝ) / n) σ
  let y := sourceNormalizedCosineMellin lam ((n : ℝ) / m) σ
  have hy : |reciprocalWeight n m σ * y| ≤ B * D := by
    rw [abs_mul]
    exact mul_le_mul hBσ hDσ (abs_nonneg _) hB0
  have hx : |reciprocalWeight m n σ * x| ≤ C + B * D := by
    calc
      _ = |(reciprocalWeight m n σ * x + reciprocalWeight n m σ * y) -
          reciprocalWeight n m σ * y| := by congr 1; ring
      _ ≤ |reciprocalWeight m n σ * x + reciprocalWeight n m σ * y| +
          |reciprocalWeight n m σ * y| := abs_sub _ _
      _ ≤ _ := add_le_add hCσ hy
  rw [abs_mul, abs_of_pos (reciprocalWeight_pos hm hn σ)] at hx
  apply (le_div_iff₀ ha).mpr
  calc
    |x| * a = a * |x| := mul_comm _ _
    _ ≤ reciprocalWeight m n σ * |x| := mul_le_mul_of_nonneg_right hlowσ (abs_nonneg x)
    _ ≤ C + B * D := hx

/-- Every fixed rational cosine frequency has a bounded double-pole normalization,
from full positivity of the original source alone. -/
theorem exists_abs_sourceNormalizedCosineMellin_rat_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (p : ℕ) {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ σ in 𝓝[>] 1,
      |sourceNormalizedCosineMellin lam ((p : ℝ) / q) σ| ≤ C := by
  induction q using Nat.strong_induction_on generalizing p with
  | h q ih =>
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have he : (p : ℝ) / q = ((p % q : ℕ) : ℝ) / q + (p / q : ℕ) := by
      apply (div_eq_iff hq0).mpr
      have h := Nat.mod_add_div p q
      have h' : ((p % q : ℕ) : ℝ) + (q : ℝ) * (p / q : ℕ) = p := by exact_mod_cast h
      field_simp
      nlinarith
    have hperiod (σ : ℝ) : sourceNormalizedCosineMellin lam ((p : ℝ) / q) σ =
        sourceNormalizedCosineMellin lam (((p % q : ℕ) : ℝ) / q) σ := by
      rw [he, sourceNormalizedCosineMellin_add_nat]
    simp_rw [hperiod]
    rcases Nat.eq_zero_or_pos (p % q) with hk | hk
    · simpa only [hk, Nat.cast_zero, zero_div, sourceNormalizedCosineMellin,
        sourceCosineProfile_zero, sourceCosineProfile_one] using
        exists_abs_sourceNormalizedCosineMellin_one_le hW
    · exact rational_bound_of_reciprocal hW hk hq (ih (p % q) (Nat.mod_lt p hq) q hk)

/-- The same bound for the literal rationally twisted Dirichlet series. -/
theorem exists_abs_sourceCosineSeries_rat_normalized_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (p : ℕ) {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ σ : ℝ in 𝓝[>] 1,
      |(σ - 1) ^ 2 * (Gammaℝ (σ : ℂ) *
        sourceCosineSeries lam ((p : ℝ) / q) (σ : ℂ)).re| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_sourceNormalizedCosineMellin_rat_le hW p hq
  refine ⟨C, hC0, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hC] with σ hσ hCσ
  simpa only [sourceNormalizedCosineMellin, mellin_sourceCosineProfile hW _
    (show 1 < (σ : ℂ).re from hσ)] using hCσ

end RHTower.WeilSingularArithmetic
