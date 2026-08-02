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

end RHTower
