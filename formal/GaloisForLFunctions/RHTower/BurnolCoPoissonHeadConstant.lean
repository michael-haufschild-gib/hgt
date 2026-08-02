import GaloisForLFunctions.RHTower.BurnolCoPoissonSourceSpace

/-!
# The co-Poisson sum has a constant aperture head

If the seed vanishes below the aperture then every term of the co-Poisson sum vanishes on the
aperture head: for `|t| < b` and `n ≥ 1` the argument `|t|/n` is again below `b`.  The whole sum is
therefore empty there and the co-Poisson value reduces to its correction term, which is a constant.

This is the mechanism behind Burnol's landing statement, and it settles the first of the two
defining Sonine conditions for every seed supported above the aperture, with no analytic hypothesis
beyond the support condition.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

theorem burnolCoPoissonRightSum_term_eq_zero {b : ℝ} {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {t : ℝ} (ht : |t| < b) (n : ℕ) :
    g (|t| / ((n + 1 : ℕ) : ℝ)) = 0 := by
  by_contra hne
  have hmem : |t| / ((n + 1 : ℕ) : ℝ) ∈ Icc b b⁻¹ :=
    hsupp (Function.mem_support.mpr hne)
  have hle : |t| / ((n + 1 : ℕ) : ℝ) ≤ |t| := by
    refine div_le_self (abs_nonneg t) ?_
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
  have := hmem.1
  linarith

/-- **The co-Poisson head is empty below the aperture.**  For a seed supported above `b` the sum
part of the co-Poisson value vanishes on the aperture head. -/
theorem burnolCoPoissonRightSum_eq_const {b : ℝ} {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {t : ℝ} (ht : |t| < b) :
    burnolCoPoissonRightSum g t = -∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * g y⁻¹) := by
  have hzero : ∀ n : ℕ,
      (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ)) = 0 := by
    intro n
    rw [burnolCoPoissonRightSum_term_eq_zero hsupp ht n, mul_zero]
  rw [burnolCoPoissonRightSum, tsum_congr hzero, tsum_zero, zero_sub]

/-- **Constant aperture head of the co-Poisson sum.**  A seed supported above the aperture makes the
co-Poisson sum almost everywhere constant on the aperture head, so the first defining Sonine
condition holds unconditionally. -/
theorem soninHeadConstant_burnolCoPoissonRightSum {b : ℝ} {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) :
    SoninHeadConstant b (burnolCoPoissonRightSum g) := by
  refine ⟨-∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * g y⁻¹), ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  refine burnolCoPoissonRightSum_eq_const hsupp ?_
  rw [abs_of_pos ht.1]
  exact ht.2

/-- The same statement for the seed of an inhabited co-Poisson source. -/
theorem soninHeadConstant_burnolCoPoissonSource_seed {b : ℝ} (g : BurnolCoPoissonSource b) :
    SoninHeadConstant b (burnolCoPoissonRightSum g.seed) :=
  soninHeadConstant_burnolCoPoissonRightSum g.seed_support


/-! ## The co-Poisson sum is locally finite -/

/-- **Only finitely many co-Poisson terms are nonzero.**  A seed supported above `b` contributes at
`t` only through indices `n` with `n b ≤ |t|`, of which there are finitely many. -/
theorem burnolCoPoissonRightSum_hasFiniteSupport {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) (t : ℝ) :
    Function.HasFiniteSupport
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ))) := by
  refine Set.Finite.subset (Set.finite_Iio ⌈|t| / b⌉₊) ?_
  intro n hn
  have hterm : (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ)) ≠ 0 :=
    Function.mem_support.mp hn
  have hne : g (|t| / ((n + 1 : ℕ) : ℝ)) ≠ 0 := by
    intro h
    exact hterm (by rw [h, mul_zero])
  have hmem : |t| / ((n + 1 : ℕ) : ℝ) ∈ Icc b b⁻¹ :=
    hsupp (Function.mem_support.mpr hne)
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hle : b ≤ |t| / ((n + 1 : ℕ) : ℝ) := hmem.1
  have hmul : ((n + 1 : ℕ) : ℝ) * b ≤ |t| := by
    rw [mul_comm]
    exact (le_div_iff₀ hnpos).mp hle
  have hbound : ((n + 1 : ℕ) : ℝ) ≤ |t| / b := (le_div_iff₀ hb).mpr hmul
  have hceil : ((n + 1 : ℕ) : ℝ) ≤ (⌈|t| / b⌉₊ : ℝ) := le_trans hbound (Nat.le_ceil _)
  have hnat : n + 1 ≤ ⌈|t| / b⌉₊ := by exact_mod_cast hceil
  exact Set.mem_Iio.mpr (by omega)

theorem burnolCoPoissonRightSum_summable {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) (t : ℝ) :
    Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ)) :=
  summable_of_hasFiniteSupport (burnolCoPoissonRightSum_hasFiniteSupport hb hsupp t)

theorem burnolCoPoissonRightSum_summable_source {b : ℝ} (hb : 0 < b)
    (g : BurnolCoPoissonSource b) (t : ℝ) :
    Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g.seed (|t| / ((n + 1 : ℕ) : ℝ)) :=
  burnolCoPoissonRightSum_summable hb g.seed_support t


/-- **Lower index bound.**  A contributing index also lies above `|t| b`, so the contributing
indices of the co-Poisson sum at `t` fill exactly the window `[|t| b, |t| / b]`. -/
theorem burnolCoPoissonRightSum_index_lower {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {t : ℝ} {n : ℕ}
    (hn : g (|t| / ((n + 1 : ℕ) : ℝ)) ≠ 0) :
    |t| * b ≤ ((n + 1 : ℕ) : ℝ) := by
  have hmem : |t| / ((n + 1 : ℕ) : ℝ) ∈ Icc b b⁻¹ :=
    hsupp (Function.mem_support.mpr hn)
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hup : |t| / ((n + 1 : ℕ) : ℝ) ≤ b⁻¹ := hmem.2
  have hle : |t| ≤ b⁻¹ * ((n + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hnpos] at hup
    linarith
  have hprod := mul_le_mul_of_nonneg_right hle hb.le
  have hcancel : b⁻¹ * ((n + 1 : ℕ) : ℝ) * b = ((n + 1 : ℕ) : ℝ) := by
    field_simp
  rw [hcancel] at hprod
  exact hprod

/-- **The contributing window.**  At `t` the co-Poisson sum is supported on the indices `n` with
`|t| b ≤ n ≤ |t| / b`, a window of length `|t| (b⁻¹ - b)` at height `|t|`.  This is the localization
that turns the sum into a Riemann sum of mesh `1/|t|` for the correction integral. -/
theorem burnolCoPoissonRightSum_index_window {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {t : ℝ} {n : ℕ}
    (hn : g (|t| / ((n + 1 : ℕ) : ℝ)) ≠ 0) :
    |t| * b ≤ ((n + 1 : ℕ) : ℝ) ∧ ((n + 1 : ℕ) : ℝ) ≤ |t| / b := by
  refine ⟨burnolCoPoissonRightSum_index_lower hb hsupp hn, ?_⟩
  have hmem : |t| / ((n + 1 : ℕ) : ℝ) ∈ Icc b b⁻¹ :=
    hsupp (Function.mem_support.mpr hn)
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hmul : ((n + 1 : ℕ) : ℝ) * b ≤ |t| := by
    rw [mul_comm]
    exact (le_div_iff₀ hnpos).mp hmem.1
  exact (le_div_iff₀ hb).mpr hmul


/-! ## Dictionary with the multiplicative Poisson sum -/

/-- The reciprocal seed attached to a co-Poisson seed: `G v = g (1/v) / v`. -/
def coPoissonReciprocalSeed (g : ℝ → ℂ) (v : ℝ) : ℂ := ((v : ℂ))⁻¹ * g v⁻¹

/-- **Termwise dictionary.**  Each co-Poisson term is a term of the plain multiplicative sum of the
reciprocal seed at scale `1/t`. -/
theorem coPoissonRightSum_term_eq {g : ℝ → ℂ} {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((n + 1 : ℕ) : ℝ)) =
      ((t : ℂ))⁻¹ * coPoissonReciprocalSeed g (((n + 1 : ℕ) : ℝ) / t) := by
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hnne : (((n + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hnpos)
  have harg : ((((n + 1 : ℕ) : ℝ) / t)⁻¹ : ℝ) = t / ((n + 1 : ℕ) : ℝ) := by
    field_simp
  rw [coPoissonReciprocalSeed, harg]
  push_cast
  field_simp

/-- **Sum dictionary.**  The co-Poisson sum is the multiplicative sum of the reciprocal seed at
scale `1/t`, scaled by `1/t`. -/
theorem coPoissonRightSum_sum_eq {g : ℝ → ℂ} {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((n + 1 : ℕ) : ℝ))) =
      ((t : ℂ))⁻¹ *
        ∑' n : ℕ, coPoissonReciprocalSeed g ((t : ℝ)⁻¹ * (((n : ℝ)) + 1)) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hrw : (t : ℝ)⁻¹ * (((n : ℝ)) + 1) = (((n + 1 : ℕ) : ℝ)) / t := by
    push_cast
    field_simp
  rw [hrw]
  exact coPoissonRightSum_term_eq ht n

/-- **The co-Poisson value in multiplicative-Poisson form.**  For `t > 0` the literal co-Poisson sum
is `1/t` times the plain multiplicative sum of the reciprocal seed at scale `1/t`, minus the
half-line mass of that seed.  This is the shape consumed by the intertwining. -/
theorem burnolCoPoissonRightSum_eq_multiplicative {g : ℝ → ℂ} {t : ℝ} (ht : 0 < t) :
    burnolCoPoissonRightSum g t =
      ((t : ℂ))⁻¹ * (∑' n : ℕ, coPoissonReciprocalSeed g ((t : ℝ)⁻¹ * (((n : ℝ)) + 1))) -
        ∫ y in Ioi (0 : ℝ), coPoissonReciprocalSeed g y := by
  rw [burnolCoPoissonRightSum, abs_of_pos ht, coPoissonRightSum_sum_eq ht]
  rfl


/-! ## Uniform finite truncation on bounded regions -/

/-- **The co-Poisson sum is a fixed finite sum on each bounded region.**  For a seed supported above
`b`, all contributing indices at any `t` with `|t| ≤ R` lie below `⌈R / b⌉`, so on that region the
sum is the same finite sum. -/
theorem burnolCoPoissonRightSum_eq_finset_sum {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {R t : ℝ} (ht : |t| ≤ R) :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ))) =
      ∑ n ∈ Finset.range ⌈R / b⌉₊,
        (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ)) := by
  refine tsum_eq_sum ?_
  intro n hn
  by_contra hne
  have hgne : g (|t| / ((n + 1 : ℕ) : ℝ)) ≠ 0 := by
    intro h
    exact hne (by rw [h, mul_zero])
  have hwin := (burnolCoPoissonRightSum_index_window hb hsupp hgne).2
  have hmono : |t| / b ≤ R / b := by
    exact div_le_div_of_nonneg_right ht hb.le
  have hbound : ((n + 1 : ℕ) : ℝ) ≤ R / b := le_trans hwin hmono
  have hceil : ((n + 1 : ℕ) : ℝ) ≤ (⌈R / b⌉₊ : ℝ) := le_trans hbound (Nat.le_ceil _)
  have hnat : n + 1 ≤ ⌈R / b⌉₊ := by exact_mod_cast hceil
  exact hn (Finset.mem_range.mpr (by omega))


/-- **Measurability of the co-Poisson sum.**  The partial sums are finite sums of dilated copies of
the seed and converge pointwise, so the co-Poisson value is measurable whenever the seed is. -/
theorem measurable_burnolCoPoissonRightSum {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Measurable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) :
    Measurable (burnolCoPoissonRightSum g) := by
  have hterm : ∀ n : ℕ,
      Measurable fun t : ℝ => (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ)) := by
    intro n
    exact (hg.comp (measurable_abs.div_const _)).const_mul _
  have hpartial : ∀ N : ℕ, Measurable fun t : ℝ =>
      ∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ)) :=
    fun N => Finset.measurable_sum _ fun n _ => hterm n
  have hlim : Filter.Tendsto
      (fun N : ℕ => fun t : ℝ =>
        ∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ)))
      Filter.atTop
      (nhds fun t : ℝ =>
        ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ))) := by
    rw [tendsto_pi_nhds]
    intro t
    exact (burnolCoPoissonRightSum_summable hb hsupp t).hasSum.tendsto_sum_nat
  have hsum := measurable_of_tendsto_metrizable hpartial hlim
  show Measurable fun t : ℝ =>
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ))) -
      ∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * g y⁻¹)
  exact hsum.sub measurable_const


/-! ## Uniform bound -/

/-- **Uniform bound on the co-Poisson sum.**  Every contributing index exceeds `|t| b`, so each term
is at most `M / (|t| b)`, and there are at most `⌈|t| / b⌉` of them. -/
theorem norm_burnolCoPoissonSum_le {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} {M : ℝ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) (hM : ∀ x : ℝ, ‖g x‖ ≤ M)
    {t : ℝ} (ht : 0 < |t|) :
    ‖∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ))‖ ≤
      (⌈|t| / b⌉₊ : ℝ) * (M / (|t| * b)) := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hden : (0 : ℝ) < |t| * b := mul_pos ht hb
  have hterm : ∀ n : ℕ,
      ‖(((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ))‖ ≤ M / (|t| * b) := by
    intro n
    by_cases hz : g (|t| / ((n + 1 : ℕ) : ℝ)) = 0
    · rw [hz, mul_zero, norm_zero]
      positivity
    · have hlow := burnolCoPoissonRightSum_index_lower hb hsupp hz
      have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hnpos]
      calc (((n + 1 : ℕ) : ℝ))⁻¹ * ‖g (|t| / ((n + 1 : ℕ) : ℝ))‖
          ≤ (((n + 1 : ℕ) : ℝ))⁻¹ * M :=
            mul_le_mul_of_nonneg_left (hM _) (by positivity)
        _ ≤ (|t| * b)⁻¹ * M := by
            refine mul_le_mul_of_nonneg_right ?_ hMnn
            have h := one_div_le_one_div_of_le hden hlow
            rwa [one_div, one_div] at h
        _ = M / (|t| * b) := by
            rw [inv_mul_eq_div]
  rw [burnolCoPoissonRightSum_eq_finset_sum hb hsupp (le_refl |t|)]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ (M / (|t| * b)) fun n _ => hterm n) ?_
  rw [Finset.card_range, nsmul_eq_mul]

end RHTower
