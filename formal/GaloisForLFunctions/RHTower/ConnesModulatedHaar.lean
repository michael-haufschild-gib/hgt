import Mathlib

/-!
# The normalized Haar measure of a modulated group

Formalization of "Normalization of Haar measure on modulated group", Appendix II b of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Throughout the paper the multiplicative Haar measure of a group `G` with a proper module
`| · | : G → ℝ*₊` of cocompact range is normalized by

  `∫_{|g| ∈ [1, Λ]} d*g ~ log Λ`   as `Λ → ∞`.       (II b (2))

Connes determines this measure in the two cases that occur: `N = ℝ*₊` (number fields) and
`N = μ^ℤ` (function fields, `μ = q`).

* `connes_logWindow_real` - II b (6): on `ℝ*₊` the window mass of `dλ/λ` is *exactly* `log Λ`.
* `connes_normalization_unique` - the normalization (2) pins the constant.
* `connes_logWindow_discrete_set`, `connes_logWindow_discrete_card` - the window
  `{n : μⁿ ≤ Λ}` is `{0, …, ⌊log Λ / log μ⌋}`.
* `connes_logWindow_discrete_asymp` - II b (7)(8): the counting measure with weight `α` satisfies
  (2) exactly when `α = log μ`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open Filter Topology Set

/-- **Appendix II b (6).**  On `N = ℝ*₊` the normalized measure is `dλ/λ`: the mass of the window
`{λ : 1 ≤ λ ≤ Λ}` is exactly `log Λ`, so the asymptotic normalization (2) holds on the nose. -/
theorem connes_logWindow_real {Λ : ℝ} (hΛ : 0 < Λ) :
    ∫ x in (1:ℝ)..Λ, x⁻¹ = Real.log Λ := by
  rw [integral_inv_of_pos one_pos hΛ, div_one]

/-- The asymptotic normalization (2) determines the scaling constant. -/
theorem connes_normalization_unique {c : ℝ}
    (h : Tendsto (fun Λ : ℝ => c * Real.log Λ / Real.log Λ) atTop (𝓝 1)) : c = 1 := by
  have heq : ∀ᶠ Λ : ℝ in atTop, c * Real.log Λ / Real.log Λ = c := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with Λ hΛ
    have : Real.log Λ ≠ 0 := ne_of_gt (Real.log_pos hΛ)
    field_simp
  have : Tendsto (fun _ : ℝ => c) atTop (𝓝 1) := h.congr' heq
  exact tendsto_nhds_unique tendsto_const_nhds this

/-- **Appendix II b (7).**  The lattice window `{n : μⁿ ≤ Λ}` is the initial segment
`{0, …, ⌊log Λ / log μ⌋}`. -/
theorem connes_logWindow_discrete_set {μ Λ : ℝ} (hμ : 1 < μ) (hΛ : 1 ≤ Λ) :
    {n : ℕ | μ ^ n ≤ Λ} = Iic ⌊Real.log Λ / Real.log μ⌋₊ := by
  have hμ0 : (0:ℝ) < μ := lt_trans one_pos hμ
  have hlogμ : 0 < Real.log μ := Real.log_pos hμ
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hquot : 0 ≤ Real.log Λ / Real.log μ := div_nonneg hlogΛ hlogμ.le
  ext n
  simp only [mem_setOf_eq, mem_Iic]
  constructor
  · intro h
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hlogμ]
    have := Real.log_le_log (by positivity) h
    rwa [Real.log_pow] at this
  · intro h
    have hle : (n : ℝ) ≤ Real.log Λ / Real.log μ := (Nat.le_floor_iff hquot).mp h
    rw [le_div_iff₀ hlogμ] at hle
    have hexp : μ ^ n = Real.exp ((n : ℝ) * Real.log μ) := by
      rw [mul_comm, Real.exp_mul, Real.exp_log hμ0, ← Real.rpow_natCast μ n]
    rw [hexp]
    calc Real.exp ((n : ℝ) * Real.log μ) ≤ Real.exp (Real.log Λ) := Real.exp_le_exp.mpr hle
      _ = Λ := Real.exp_log (lt_of_lt_of_le one_pos hΛ)

/-- **Appendix II b (7).**  The number of lattice points in the window. -/
theorem connes_logWindow_discrete_card {μ Λ : ℝ} (hμ : 1 < μ) (hΛ : 1 ≤ Λ) :
    Nat.card {n : ℕ // μ ^ n ≤ Λ} = ⌊Real.log Λ / Real.log μ⌋₊ + 1 := by
  have h := connes_logWindow_discrete_set hμ hΛ
  have hcard : Nat.card {n : ℕ // n ∈ {n : ℕ | μ ^ n ≤ Λ}}
      = Nat.card {n : ℕ // n ∈ Iic ⌊Real.log Λ / Real.log μ⌋₊} := by rw [h]
  have hequiv : {n : ℕ // n ∈ Iic ⌊Real.log Λ / Real.log μ⌋₊}
      ≃ Fin (⌊Real.log Λ / Real.log μ⌋₊ + 1) :=
    (Equiv.subtypeEquivRight (fun n => by simp)).trans Fin.equivSubtype.symm
  rw [show Nat.card {n : ℕ // μ ^ n ≤ Λ}
      = Nat.card {n : ℕ // n ∈ {n : ℕ | μ ^ n ≤ Λ}} from rfl, hcard, Nat.card_congr hequiv,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **Appendix II b (8).**  The counting measure with weight `α` on `N = μ^ℤ` satisfies the
normalization (2) exactly when `α = log μ`. -/
theorem connes_logWindow_discrete_asymp {μ : ℝ} (hμ : 1 < μ) :
    Tendsto (fun Λ : ℝ => Real.log μ *
        (Nat.card {n : ℕ // μ ^ n ≤ Λ} : ℝ) / Real.log Λ) atTop (𝓝 1) := by
  have hlogμ : 0 < Real.log μ := Real.log_pos hμ
  have hlow : ∀ᶠ Λ : ℝ in atTop,
      (1:ℝ) ≤ Real.log μ * (Nat.card {n : ℕ // μ ^ n ≤ Λ} : ℝ) / Real.log Λ := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with Λ hΛ
    have hL : 0 < Real.log Λ := Real.log_pos hΛ
    rw [connes_logWindow_discrete_card hμ (le_of_lt hΛ)]
    rw [le_div_iff₀ hL]
    have hfl : Real.log Λ / Real.log μ ≤ (⌊Real.log Λ / Real.log μ⌋₊ : ℝ) + 1 :=
      le_of_lt (Nat.lt_floor_add_one _)
    have hkey : Real.log μ * (Real.log Λ / Real.log μ) = Real.log Λ := by
      field_simp
    have h1 : Real.log μ * (Real.log Λ / Real.log μ)
        ≤ Real.log μ * ((⌊Real.log Λ / Real.log μ⌋₊ : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hfl hlogμ.le
    rw [hkey] at h1
    push_cast
    linarith
  have hhigh : ∀ᶠ Λ : ℝ in atTop,
      Real.log μ * (Nat.card {n : ℕ // μ ^ n ≤ Λ} : ℝ) / Real.log Λ
        ≤ 1 + Real.log μ / Real.log Λ := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with Λ hΛ
    have hL : 0 < Real.log Λ := Real.log_pos hΛ
    rw [connes_logWindow_discrete_card hμ (le_of_lt hΛ)]
    rw [div_le_iff₀ hL]
    have hquot : 0 ≤ Real.log Λ / Real.log μ := div_nonneg hL.le hlogμ.le
    have hfl : (⌊Real.log Λ / Real.log μ⌋₊ : ℝ) ≤ Real.log Λ / Real.log μ :=
      Nat.floor_le hquot
    have hkey : Real.log μ * (Real.log Λ / Real.log μ) = Real.log Λ := by
      field_simp
    have h1 : Real.log μ * (⌊Real.log Λ / Real.log μ⌋₊ : ℝ)
        ≤ Real.log μ * (Real.log Λ / Real.log μ) :=
      mul_le_mul_of_nonneg_left hfl hlogμ.le
    rw [hkey] at h1
    have h2 : (1 + Real.log μ / Real.log Λ) * Real.log Λ = Real.log Λ + Real.log μ := by
      field_simp
    rw [h2]
    push_cast
    linarith
  have htend : Tendsto (fun Λ : ℝ => 1 + Real.log μ / Real.log Λ) atTop (𝓝 1) := by
    have : Tendsto (fun Λ : ℝ => Real.log μ / Real.log Λ) atTop (𝓝 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact Real.tendsto_log_atTop
    simpa using tendsto_const_nhds.add this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend hlow hhigh

end

end GaloisForLFunctions.RHTower
