import GaloisForLFunctions.RHTower.BurnolCoPoissonCorrectionConstant
import GaloisForLFunctions.RHTower.BurnolCoPoissonIntertwiningL2

/-!
# The reciprocal-indicator co-Poisson vector

For the reciprocal of the indicator seed every nonzero term in the co-Poisson sum is exactly
`1 / |t|`.  The number of terms is the number of integers in the multiplicative window
`[|t| b, |t| / b]`.  Floor/ceiling discrepancy therefore gives an explicit `O(1 / |t|)` bound.
This supplies, without any Fourier assumption, all analytic hypotheses needed to apply the
`L²` co-Poisson intertwining theorem to the indicator seed.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The reciprocal of the indicator seed is measurable. -/
theorem measurable_coPoissonReciprocalSeed_coPoissonIndicatorSeed
    {b : ℝ} (hb : 0 < b) :
    Measurable (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) := by
  rw [show coPoissonReciprocalSeed (coPoissonIndicatorSeed b) =
      Set.indicator (Icc b b⁻¹) (fun v : ℝ => ((v : ℝ) : ℂ)⁻¹) from
    funext (coPoissonReciprocalSeed_coPoissonIndicatorSeed hb)]
  exact (by fun_prop : Measurable fun v : ℝ => ((v : ℝ) : ℂ)⁻¹).indicator measurableSet_Icc

/-- The reciprocal of the indicator seed is integrable. -/
theorem integrable_coPoissonReciprocalSeed_coPoissonIndicatorSeed
    {b : ℝ} (hb : 0 < b) :
    Integrable (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) := by
  rw [show coPoissonReciprocalSeed (coPoissonIndicatorSeed b) =
      Set.indicator (Icc b b⁻¹) (fun v : ℝ => ((v : ℝ) : ℂ)⁻¹) from
    funext (coPoissonReciprocalSeed_coPoissonIndicatorSeed hb)]
  refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).integrable_indicator
    measurableSet_Icc
  intro v hv
  have hv0 : v ≠ 0 := ne_of_gt (hb.trans_le hv.1)
  exact ContinuousAt.continuousWithinAt
    ((Complex.continuous_ofReal.continuousAt).inv₀ (Complex.ofReal_ne_zero.mpr hv0))

/-- A reciprocal-indicator term is the indicator of the same window, scaled by `1/t`. -/
theorem coPoissonReciprocalIndicator_term {b t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (n : ℕ) :
    (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonReciprocalSeed (coPoissonIndicatorSeed b)
          (t / ((n + 1 : ℕ) : ℝ)) =
      ((t : ℝ) : ℂ)⁻¹ * coPoissonIndicatorSeed b
        (t / ((n + 1 : ℕ) : ℝ)) := by
  rw [coPoissonReciprocalSeed_coPoissonIndicatorSeed hb]
  by_cases hmem : t / ((n + 1 : ℕ) : ℝ) ∈ Icc b b⁻¹
  · rw [Set.indicator_of_mem hmem, coPoissonIndicatorSeed_of_mem hmem]
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    have hn0 : ((((n + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by positivity)
    push_cast
    field_simp
  · rw [Set.indicator_of_notMem hmem, coPoissonIndicatorSeed_of_notMem hmem, mul_zero, mul_zero]

/-- The unweighted indicator count is exactly the cardinality of the integer window. -/
theorem coPoissonIndicatorCount_eq_finset_card {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    (∑' n : ℕ, coPoissonIndicatorSeed b (t / ((n + 1 : ℕ) : ℝ))) =
      ((Finset.Icc ⌈t * b⌉₊ ⌊t / b⌋₊).card : ℂ) := by
  set m : ℕ := ⌈t * b⌉₊ with hm
  set N : ℕ := ⌊t / b⌋₊ with hN
  have hmpos : 1 ≤ m := Nat.one_le_ceil_iff.mpr (by positivity)
  have hvanish : ∀ n : ℕ, n ∉ Finset.range N →
      coPoissonIndicatorSeed b (t / ((n + 1 : ℕ) : ℝ)) = 0 := by
    intro n hn
    by_contra hz
    have hmem : t / ((n + 1 : ℕ) : ℝ) ∈ Icc b b⁻¹ :=
      support_coPoissonIndicatorSeed b (Function.mem_support.mpr hz)
    have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hle : ((n + 1 : ℕ) : ℝ) ≤ t / b := by
      rw [le_div_iff₀ hb, mul_comm]
      exact (le_div_iff₀ hnpos).mp hmem.1
    have : n + 1 ≤ N := Nat.le_floor hle
    exact (Finset.mem_range.not.mp hn) (by omega)
  rw [tsum_eq_sum hvanish]
  have hreindex : ∀ f : ℕ → ℂ,
      ∑ n ∈ Finset.range N, f (n + 1) = ∑ k ∈ Finset.Icc 1 N, f k := by
    intro f
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 N (c := 1)]
    simp only [Finset.Ico_add_one_right_eq_Icc, zero_add]
  rw [hreindex (fun k => coPoissonIndicatorSeed b (t / (k : ℝ)))]
  have hsubset : Finset.Icc m N ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_left hmpos
  have houtside : ∀ k ∈ Finset.Icc 1 N, k ∉ Finset.Icc m N →
      coPoissonIndicatorSeed b (t / (k : ℝ)) = 0 := by
    intro k hk hkn
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    have hklt : k < m := by
      by_contra hc
      exact hkn (Finset.mem_Icc.mpr ⟨not_lt.mp hc, hkN⟩)
    have hkreal : (k : ℝ) < t * b := Nat.lt_ceil.mp hklt
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    refine coPoissonIndicatorSeed_of_notMem ?_
    rintro ⟨-, hupper⟩
    rw [div_le_iff₀ hkpos, inv_mul_eq_div, le_div_iff₀ hb] at hupper
    linarith
  rw [← Finset.sum_subset hsubset houtside]
  calc
    ∑ k ∈ Finset.Icc m N, coPoissonIndicatorSeed b (t / (k : ℝ)) =
        ∑ _k ∈ Finset.Icc m N, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
          have hkpos : 0 < k := lt_of_lt_of_le hmpos hk1
          have hlow : t * b ≤ (k : ℝ) :=
            le_trans (Nat.le_ceil _) (by exact_mod_cast hk1)
          have hhigh : (k : ℝ) ≤ t / b :=
            le_trans (by exact_mod_cast hk2) (Nat.floor_le (by positivity))
          exact coPoissonIndicatorSeed_of_mem
            (coPoissonIndicatorSeed_scale_mem hb hkpos hlow hhigh)
    _ = ((Finset.Icc m N).card : ℂ) := by simp

/-- The raw reciprocal-indicator sum is its integer-window cardinality divided by `t`. -/
theorem coPoissonReciprocalIndicatorSum_eq_card {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonReciprocalSeed (coPoissonIndicatorSeed b)
          (t / ((n + 1 : ℕ) : ℝ))) =
      ((t : ℝ) : ℂ)⁻¹ * ((Finset.Icc ⌈t * b⌉₊ ⌊t / b⌋₊).card : ℂ) := by
  rw [tsum_congr (coPoissonReciprocalIndicator_term hb ht), tsum_mul_left,
    coPoissonIndicatorCount_eq_finset_card hb ht]

/-- The correction of the reciprocal indicator is the length of the multiplicative window. -/
theorem coPoissonReciprocalIndicator_correction {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    coPoissonCorrectionConstant
        (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) =
      (((b⁻¹ - b : ℝ)) : ℂ) := by
  rw [coPoissonCorrectionConstant_reciprocalSeed]
  have hble : b ≤ b⁻¹ := le_inv_self_of_le_one hb hb1
  have hsub : Ioi (0 : ℝ) ∩ Icc b b⁻¹ = Icc b b⁻¹ := by
    rw [inter_eq_right]
    intro y hy
    exact lt_of_lt_of_le hb hy.1
  simp only [coPoissonIndicatorSeed]
  rw [setIntegral_indicator measurableSet_Icc, hsub, setIntegral_const,
    Real.volume_real_Icc_of_le hble, Complex.real_smul, mul_one, Complex.ofReal_sub,
    Complex.ofReal_inv]

/-- Exact pointwise cardinality formula for the reciprocal-indicator co-Poisson value. -/
theorem burnolCoPoissonRightSum_reciprocalIndicator_eq_card
    {b t : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (ht : 0 < t) :
    burnolCoPoissonRightSum
        (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t =
      ((((Finset.Icc ⌈t * b⌉₊ ⌊t / b⌋₊).card : ℝ) / t - (b⁻¹ - b) : ℝ) : ℂ) := by
  rw [burnolCoPoissonRightSum_eq_sub_correction, abs_of_pos ht,
    coPoissonReciprocalIndicatorSum_eq_card hb ht,
    coPoissonReciprocalIndicator_correction hb hb1]
  push_cast
  ring

/-- Floor/ceiling discrepancy gives the sharp-order reciprocal-indicator tail bound. -/
theorem norm_burnolCoPoissonRightSum_reciprocalIndicator_le
    {b t : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (ht : 2 / b ≤ t) :
    ‖burnolCoPoissonRightSum
        (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t‖ ≤ 2 / t := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity : 0 < 2 / b) ht
  set m : ℕ := ⌈t * b⌉₊ with hm
  set N : ℕ := ⌊t / b⌋₊ with hN
  have hmpos : 1 ≤ m := Nat.one_le_ceil_iff.mpr (by positivity)
  have hNnonneg : 0 ≤ t / b := by positivity
  have hfloor_lo : (N : ℝ) ≤ t / b := Nat.floor_le hNnonneg
  have hfloor_hi : t / b < (N : ℝ) + 1 := by
    simpa using Nat.lt_floor_add_one (t / b)
  have hceil_lo : t * b ≤ (m : ℝ) := Nat.le_ceil _
  have hceil_hi : (m : ℝ) < t * b + 1 := Nat.ceil_lt_add_one (by positivity)
  have hgap : 0 ≤ b⁻¹ - b := sub_nonneg.mpr (le_inv_self_of_le_one hb hb1)
  rw [burnolCoPoissonRightSum_reciprocalIndicator_eq_card hb hb1 htpos,
    Complex.norm_real, Real.norm_eq_abs]
  by_cases hmn : m ≤ N
  · have hcard : ((Finset.Icc m N).card : ℝ) = (N : ℝ) + 1 - (m : ℝ) := by
      rw [Nat.card_Icc, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hcard]
    have hdiff :
        |((N : ℝ) + 1 - (m : ℝ)) - (t / b - t * b)| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    have heq :
        ((N : ℝ) + 1 - (m : ℝ)) / t - (b⁻¹ - b) =
          (((N : ℝ) + 1 - (m : ℝ)) - (t / b - t * b)) / t := by
      field_simp
    rw [heq, abs_div, abs_of_pos htpos]
    exact (div_le_div_iff_of_pos_right htpos).mpr hdiff
  · have hNm : N < m := Nat.lt_of_not_ge hmn
    have hcard : (Finset.Icc m N).card = 0 := by
      rw [Nat.card_Icc]
      omega
    rw [hcard]
    norm_num only [Nat.cast_zero, zero_div, zero_sub, abs_neg, abs_of_nonneg hgap]
    have hsmall : t * (b⁻¹ - b) ≤ 2 := by
      have hNmR : (N : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hNm
      have : t / b - t * b < 1 := by linarith
      have heq : t * (b⁻¹ - b) = t / b - t * b := by
        rw [mul_sub, div_eq_mul_inv]
      rw [heq]
      linarith
    rw [le_div_iff₀ htpos, mul_comm]
    exact hsmall

/-- A uniform local bound for the reciprocal-indicator value. -/
theorem norm_burnolCoPoissonRightSum_reciprocalIndicator_le_local
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (t : ℝ) :
    ‖burnolCoPoissonRightSum
        (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t‖ ≤
      2 / b + (b⁻¹ - b) := by
  have hgap : 0 ≤ b⁻¹ - b := sub_nonneg.mpr (le_inv_self_of_le_one hb hb1)
  by_cases ht0 : t = 0
  · subst t
    rw [burnolCoPoissonRightSum_eq_const
      (support_coPoissonReciprocalSeed hb (support_coPoissonIndicatorSeed b))]
    · rw [show (∫ y in Ioi (0 : ℝ),
          ((y : ℂ)⁻¹ * coPoissonReciprocalSeed (coPoissonIndicatorSeed b) y⁻¹)) =
            (((b⁻¹ - b : ℝ)) : ℂ) from
          coPoissonReciprocalIndicator_correction hb hb1,
        norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgap]
      have h2b : (0 : ℝ) ≤ 2 / b := by positivity
      linarith
    · simpa using hb
  · have habs : 0 < |t| := abs_pos.mpr ht0
    have heven : burnolCoPoissonRightSum
          (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t =
        burnolCoPoissonRightSum
          (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) |t| := by
      simp only [burnolCoPoissonRightSum, abs_abs]
    rw [heven, burnolCoPoissonRightSum_reciprocalIndicator_eq_card hb hb1 habs,
      Complex.norm_real, Real.norm_eq_abs]
    have hmpos : 1 ≤ ⌈|t| * b⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
    have hcardNat : (Finset.Icc ⌈|t| * b⌉₊ ⌊|t| / b⌋₊).card ≤ ⌊|t| / b⌋₊ := by
      rw [Nat.card_Icc]
      omega
    have hcard : ((Finset.Icc ⌈|t| * b⌉₊ ⌊|t| / b⌋₊).card : ℝ) ≤ |t| / b := by
      calc ((Finset.Icc ⌈|t| * b⌉₊ ⌊|t| / b⌋₊).card : ℝ) ≤ ((⌊|t| / b⌋₊ : ℕ) : ℝ) := by
            exact_mod_cast hcardNat
        _ ≤ |t| / b := Nat.floor_le (by positivity)
    have hq : ((Finset.Icc ⌈|t| * b⌉₊ ⌊|t| / b⌋₊).card : ℝ) / |t| ≤ b⁻¹ := by
      rw [div_le_iff₀ habs]
      calc ((Finset.Icc ⌈|t| * b⌉₊ ⌊|t| / b⌋₊).card : ℝ) ≤ |t| / b := hcard
        _ = b⁻¹ * |t| := by
            rw [div_eq_mul_inv]
            ring
    have hnn : (0 : ℝ) ≤ ((Finset.Icc ⌈|t| * b⌉₊ ⌊|t| / b⌋₊).card : ℝ) / |t| := by positivity
    have hb2 : b⁻¹ ≤ 2 / b := by
      rw [le_div_iff₀ hb, inv_mul_cancel₀ (ne_of_gt hb)]
      norm_num
    rw [abs_le]
    constructor <;> linarith

/-- A square-integrable decay profile for the reciprocal-indicator co-Poisson value. -/
theorem norm_burnolCoPoissonRightSum_reciprocalIndicator_le_profile
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (t : ℝ) :
    ‖burnolCoPoissonRightSum
        (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t‖ ≤
      (4 + (2 / b + (b⁻¹ - b)) * (1 + 2 / b)) * (1 + |t|)⁻¹ := by
  have hgap : 0 ≤ b⁻¹ - b := sub_nonneg.mpr (le_inv_self_of_le_one hb hb1)
  have hB : 0 ≤ 2 / b + (b⁻¹ - b) := by positivity
  have hden : 0 < 1 + |t| := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hden]
  rcases le_or_gt (2 / b) |t| with hfar | hnear
  · have habs : 0 < |t| := lt_of_lt_of_le (by positivity : 0 < 2 / b) hfar
    have heven : burnolCoPoissonRightSum
          (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t =
        burnolCoPoissonRightSum
          (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) |t| := by
      simp only [burnolCoPoissonRightSum, abs_abs]
    have htail := norm_burnolCoPoissonRightSum_reciprocalIndicator_le hb hb1 hfar
    rw [← heven] at htail
    have htwo : 1 ≤ |t| := by
      have : (2 : ℝ) ≤ 2 / b := by
        rw [le_div_iff₀ hb]
        nlinarith
      linarith
    have hmul : (2 / |t|) * (1 + |t|) ≤ 4 := by
      have hstep : 1 + |t| ≤ 2 * |t| := by linarith
      calc
        (2 / |t|) * (1 + |t|) ≤ (2 / |t|) * (2 * |t|) := by gcongr
        _ = 4 := by
            field_simp
            norm_num
    have hstep2 : ‖burnolCoPoissonRightSum
          (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t‖ * (1 + |t|) ≤
        2 / |t| * (1 + |t|) := mul_le_mul_of_nonneg_right htail hden.le
    have hextra : (0 : ℝ) ≤ (2 / b + (b⁻¹ - b)) * (1 + 2 / b) := by positivity
    linarith
  · have hlocal := norm_burnolCoPoissonRightSum_reciprocalIndicator_le_local hb hb1 t
    have hfactor : 1 + |t| ≤ 1 + 2 / b := by linarith
    have h1 : ‖burnolCoPoissonRightSum
          (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t‖ * (1 + |t|) ≤
        (2 / b + (b⁻¹ - b)) * (1 + |t|) := mul_le_mul_of_nonneg_right hlocal hden.le
    have h2 : (2 / b + (b⁻¹ - b)) * (1 + |t|) ≤ (2 / b + (b⁻¹ - b)) * (1 + 2 / b) :=
      mul_le_mul_of_nonneg_left hfactor hB
    linarith

/-- The reciprocal-indicator co-Poisson value lies in `L²(ℝ)`. -/
theorem memLp_two_burnolCoPoissonRightSum_reciprocalIndicator
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    MemLp (burnolCoPoissonRightSum
      (coPoissonReciprocalSeed (coPoissonIndicatorSeed b))) 2 volume :=
  HTGeometry.memLp_two_of_decayProfile
    (measurable_burnolCoPoissonRightSum hb
      (measurable_coPoissonReciprocalSeed_coPoissonIndicatorSeed hb)
      (support_coPoissonReciprocalSeed hb (support_coPoissonIndicatorSeed b))).aestronglyMeasurable
    (norm_burnolCoPoissonRightSum_reciprocalIndicator_le_profile hb hb1)

/-- The indicator co-Poisson value is real-valued. -/
theorem star_burnolCoPoissonRightSum_coPoissonIndicatorSeed
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (t : ℝ) :
    (starRingEnd ℂ) (burnolCoPoissonRightSum (coPoissonIndicatorSeed b) t) =
      burnolCoPoissonRightSum (coPoissonIndicatorSeed b) t := by
  by_cases ht0 : t = 0
  · subst t
    rw [burnolCoPoissonRightSum_eq_const (support_coPoissonIndicatorSeed b)]
    · rw [show (∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * coPoissonIndicatorSeed b y⁻¹)) =
          (((2 * Real.log b⁻¹ : ℝ)) : ℂ) from
        coPoissonIndicatorSeed_correction hb hb1]
      rw [map_neg, Complex.conj_ofReal]
    · simpa using hb
  · have habs : 0 < |t| := abs_pos.mpr ht0
    have heven : burnolCoPoissonRightSum (coPoissonIndicatorSeed b) t =
        burnolCoPoissonRightSum (coPoissonIndicatorSeed b) |t| := by
      simp only [burnolCoPoissonRightSum, abs_abs]
    rw [heven, burnolCoPoissonRightSum_coPoissonIndicatorSeed hb hb1 habs]
    exact Complex.conj_ofReal _

/-- The reciprocal-indicator co-Poisson value is real-valued. -/
theorem star_burnolCoPoissonRightSum_reciprocalIndicator
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (t : ℝ) :
    (starRingEnd ℂ) (burnolCoPoissonRightSum
        (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t) =
      burnolCoPoissonRightSum
        (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t := by
  by_cases ht0 : t = 0
  · subst t
    rw [burnolCoPoissonRightSum_eq_const
      (support_coPoissonReciprocalSeed hb (support_coPoissonIndicatorSeed b))]
    · rw [show (∫ y in Ioi (0 : ℝ),
          ((y : ℂ)⁻¹ * coPoissonReciprocalSeed (coPoissonIndicatorSeed b) y⁻¹)) =
            (((b⁻¹ - b : ℝ)) : ℂ) from
          coPoissonReciprocalIndicator_correction hb hb1]
      rw [map_neg, Complex.conj_ofReal]
    · simpa using hb
  · have habs : 0 < |t| := abs_pos.mpr ht0
    have heven : burnolCoPoissonRightSum
          (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t =
        burnolCoPoissonRightSum
          (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) |t| := by
      simp only [burnolCoPoissonRightSum, abs_abs]
    rw [heven, burnolCoPoissonRightSum_reciprocalIndicator_eq_card hb hb1 habs]
    exact Complex.conj_ofReal _

end RHTower
