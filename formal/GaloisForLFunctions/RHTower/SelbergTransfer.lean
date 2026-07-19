/-
Doc 70 ((SEL-PS) by transfer): the Riemann–Siegel half-sum bricks, machine-checked.

On R–S blocks the completed matched truncation's line profile equals ζ up to
O(t^{−1/4}), so the designed carrier's small-values are policed by Selberg's
unconditional CLT for ζ. The four joints of that chain that are pure
algebra/measure theory are proved here:

* `norm_add_sq_unit_conj_eq` — the half-sum identity: for a unit `v`,
  `‖S + v²·conj S‖ = 2·|Re(conj v · S)|` — the algebraic heart of
  `g_N(½+it) = S_N + χ·conj S_N` being a rotated real profile (doc 70 §1).
* `norm_add_sq_unit_conj_le` — its corollary `‖g_N‖ ≤ 2‖S_N‖` on the line,
  i.e. the one-sided sum dominates half the completed profile.
* `sublevel_split_subset` — doc 70 §2's split: under `Z = A₀·g + τ`
  pointwise, carrier-small forces plateau-small or taper-difference-large.
* `sublevel_transfer_subset` — the per-block transfer: where `‖g − ζ‖ ≤ ε`,
  plateau-small lands in the ζ-sublevel set at threshold `2λ + ε`.
* `blockwise_transfer_measure_le` — the aggregation: re-anchored per-block
  small-sets are measured by ONE global set (Selberg's) plus the per-block
  exceptional sets (taper Chebyshev), so Selberg is consumed once, globally.

The `norm_sublevel_*` declarations expose the common law for arbitrary real normed spaces and
independent carrier/tail thresholds; the named Selberg declarations are its equal-threshold complex
specializations.

The analytic inputs (R–S error, Selberg 1946, MV on blocks) are
hypothesis-typed per the house pattern; docs 70 §§1–2 discharge them.
-/
import Mathlib

namespace RHTower

open MeasureTheory Set Complex

/-- **The half-sum identity (doc 70 §1).** For a unit modulus `v`,
`S + v²·conj S = v·(w + conj w)` with `w = conj v · S`, hence its norm is
`2·|Re(conj v · S)|`. Applied with `v² = χ(½+it)` and `S` the one-sided
matched sum, this is the statement that the completed truncation's line
profile is a rotated real signal (Hardy `Z`-shape). -/
theorem norm_add_sq_unit_conj_eq (v S : ℂ) (hv : ‖v‖ = 1) :
    ‖S + v ^ 2 * (starRingEnd ℂ) S‖ = 2 * |((starRingEnd ℂ) v * S).re| := by
  have key : S + v ^ 2 * (starRingEnd ℂ) S
      = v * (((starRingEnd ℂ) v * S) + (starRingEnd ℂ) ((starRingEnd ℂ) v * S)) := by
    have hvv : v * (starRingEnd ℂ) v = 1 := by
      have := Complex.mul_conj v
      rw [this]
      norm_cast
      simp [Complex.normSq_eq_norm_sq, hv]
    calc S + v ^ 2 * (starRingEnd ℂ) S
        = (v * (starRingEnd ℂ) v) * S + v ^ 2 * (starRingEnd ℂ) S := by
          rw [hvv, one_mul]
      _ = v * (((starRingEnd ℂ) v * S) + (starRingEnd ℂ) ((starRingEnd ℂ) v * S)) := by
          rw [map_mul, Complex.conj_conj]; ring
  rw [key, norm_mul, hv, one_mul, Complex.add_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_mul]
  norm_num

/-- The one-sided sum dominates half the completed line profile:
`‖S + v²·conj S‖ ≤ 2‖S‖`. Contrapositively, a small one-sided sum is only
possible where the completed profile (= `ζ` up to the R–S error) is small. -/
theorem norm_add_sq_unit_conj_le (v S : ℂ) (hv : ‖v‖ = 1) :
    ‖S + v ^ 2 * (starRingEnd ℂ) S‖ ≤ 2 * ‖S‖ := by
  rw [norm_add_sq_unit_conj_eq v S hv]
  have h1 : |((starRingEnd ℂ) v * S).re| ≤ ‖(starRingEnd ℂ) v * S‖ :=
    Complex.abs_re_le_norm _
  have h2 : ‖(starRingEnd ℂ) v * S‖ = ‖S‖ := by
    rw [norm_mul, Complex.norm_conj, hv, one_mul]
  linarith

/-- **Two-threshold normed sublevel split.** Under `Z = A₀ • g + τ` with `A₀ > 0`,
carrier smallness at threshold `A₀λ` forces either plateau smallness at threshold `λ + κ`
or exceptional-tail largeness at threshold `A₀κ`. -/
theorem norm_sublevel_split_subset {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z g τ : α → E) (A0 lam kappa : ℝ)
    (hA0 : 0 < A0) (hid : ∀ t, Z t = A0 • g t + τ t) :
    {t | ‖Z t‖ ≤ A0 * lam} ⊆
      {t | ‖g t‖ ≤ lam + kappa} ∪ {t | A0 * kappa ≤ ‖τ t‖} := by
  intro t ht
  by_cases hτ : A0 * kappa ≤ ‖τ t‖
  · exact Or.inr hτ
  · left
    replace hτ : ‖τ t‖ < A0 * kappa := not_le.mp hτ
    have h1 : ‖A0 • g t‖ ≤ ‖Z t‖ + ‖τ t‖ := by
      have hZ : A0 • g t = Z t - τ t := by rw [hid t]; abel
      rw [hZ]; exact norm_sub_le _ _
    have h2 : ‖A0 • g t‖ = A0 * ‖g t‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hA0]
    have h3 : A0 * ‖g t‖ ≤ A0 * (lam + kappa) := by
      have := ht
      simp only [mem_setOf_eq] at this
      rw [h2] at h1
      nlinarith
    exact le_of_mul_le_mul_left h3 hA0

/-- **The sublevel split (doc 70 §2).** Under the pointwise identity
`Z = A₀·g + τ` with `A₀ > 0`: wherever the carrier `Z` is `A₀λ`-small,
either the plateau `g` is `2λ`-small or the taper-difference `τ` is
`A₀λ`-large. -/
theorem sublevel_split_subset {α : Type*} (Z g τ : α → ℂ) (A0 lam : ℝ)
    (hA0 : 0 < A0) (hid : ∀ t, Z t = (A0 : ℂ) * g t + τ t) :
    {t | ‖Z t‖ ≤ A0 * lam} ⊆ {t | ‖g t‖ ≤ 2 * lam} ∪ {t | A0 * lam ≤ ‖τ t‖} := by
  simpa only [two_mul] using
    norm_sublevel_split_subset Z g τ A0 lam lam hA0 fun t => by
      simpa only [Complex.real_smul] using hid t

/-- **Normed sublevel transfer.** On a set `B` where `g` tracks `zeta` within `eps`,
the `r`-sublevel set of `g` lands in the `(r + eps)`-sublevel set of `zeta`. -/
theorem norm_sublevel_transfer_subset {α E : Type*} [NormedAddCommGroup E]
    (g zeta : α → E) (B : Set α) (r eps : ℝ)
    (hprox : ∀ t ∈ B, ‖g t - zeta t‖ ≤ eps) :
    {t | ‖g t‖ ≤ r} ∩ B ⊆ {t | ‖zeta t‖ ≤ r + eps} := by
  rintro t ⟨ht, htB⟩
  simp only [mem_setOf_eq] at ht ⊢
  have h1 : ‖zeta t‖ - ‖g t‖ ≤ ‖zeta t - g t‖ := norm_sub_norm_le _ _
  have h2 : ‖zeta t - g t‖ = ‖g t - zeta t‖ := norm_sub_rev _ _
  have h3 := hprox t htB
  linarith

/-- **The per-block transfer (doc 70 §1).** On a block `B` where the
completed truncation `g` tracks `ζ` within `ε` (the R–S error), the
`2λ`-sublevel set of `g` lands inside the `(2λ+ε)`-sublevel set of `ζ`. -/
theorem sublevel_transfer_subset {α : Type*} (g zeta : α → ℂ) (B : Set α)
    (lam eps : ℝ) (hprox : ∀ t ∈ B, ‖g t - zeta t‖ ≤ eps) :
    {t | ‖g t‖ ≤ 2 * lam} ∩ B ⊆ {t | ‖zeta t‖ ≤ 2 * lam + eps} :=
  norm_sublevel_transfer_subset g zeta B (2 * lam) eps hprox

/-- **Composed two-threshold normed transfer.** Carrier-small points on `B` lie in one
reference sublevel set or in the local exceptional-tail set. -/
theorem norm_sublevel_split_transfer_subset {α E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z g τ zeta : α → E) (B : Set α) (A0 lam kappa eps : ℝ) (hA0 : 0 < A0)
    (hid : ∀ t, Z t = A0 • g t + τ t)
    (hprox : ∀ t ∈ B, ‖g t - zeta t‖ ≤ eps) :
    {t | ‖Z t‖ ≤ A0 * lam} ∩ B
      ⊆ {t | ‖zeta t‖ ≤ lam + kappa + eps} ∪
        ({t | A0 * kappa ≤ ‖τ t‖} ∩ B) := by
  intro t ht
  have hsplit := norm_sublevel_split_subset Z g τ A0 lam kappa hA0 hid ht.1
  rcases hsplit with hg | hτ
  · exact Or.inl (norm_sublevel_transfer_subset g zeta B (lam + kappa) eps hprox ⟨hg, ht.2⟩)
  · exact Or.inr ⟨hτ, ht.2⟩

/-- **The composed per-block transfer.** Carrier-small on a block is covered by
the global ζ-sublevel set together with the taper exceptional set. This is the
local Selberg-transfer coverage produced by `sublevel_split_subset` followed by
`sublevel_transfer_subset`. -/
theorem sublevel_split_transfer_subset {α : Type*} (Z g τ zeta : α → ℂ) (B : Set α)
    (A0 lam eps : ℝ) (hA0 : 0 < A0)
    (hid : ∀ t, Z t = (A0 : ℂ) * g t + τ t)
    (hprox : ∀ t ∈ B, ‖g t - zeta t‖ ≤ eps) :
    {t | ‖Z t‖ ≤ A0 * lam} ∩ B
      ⊆ {t | ‖zeta t‖ ≤ 2 * lam + eps} ∪
        ({t | A0 * lam ≤ ‖τ t‖} ∩ B) := by
  simpa only [two_mul] using
    norm_sublevel_split_transfer_subset Z g τ zeta B A0 lam lam eps hA0
      (fun t => by simpa only [Complex.real_smul] using hid t) hprox

/-- **The blockwise aggregation (doc 70 §2).** If on each block `B j` the
small-set `E j` is covered by ONE global set `F` (the ζ-sublevel set fed to
Selberg) together with a per-block exceptional set `G j` (taper Chebyshev),
then the total measure of the re-anchored small-sets is bounded by `μ F`
plus the sum of the exceptional measures. Selberg's theorem is consumed
once, on the full window — never per block. -/
theorem blockwise_transfer_measure_le {α : Type*} [MeasurableSpace α]
    {ι : Type*} [Countable ι] (μ : Measure α) (E G B : ι → Set α) (F : Set α)
    (h : ∀ j, E j ∩ B j ⊆ F ∪ (G j ∩ B j)) :
    μ (⋃ j, E j ∩ B j) ≤ μ F + ∑' j, μ (G j ∩ B j) := by
  have hsub : (⋃ j, E j ∩ B j) ⊆ F ∪ ⋃ j, (G j ∩ B j) := by
    refine iUnion_subset fun j => (h j).trans ?_
    exact union_subset_union_right F (subset_iUnion (fun j => G j ∩ B j) j)
  calc μ (⋃ j, E j ∩ B j) ≤ μ (F ∪ ⋃ j, (G j ∩ B j)) := measure_mono hsub
    _ ≤ μ F + μ (⋃ j, (G j ∩ B j)) := measure_union_le _ _
    _ ≤ μ F + ∑' j, μ (G j ∩ B j) :=
        add_le_add le_rfl (measure_iUnion_le _)

/-- **Full blockwise two-threshold normed transfer.** The pointwise normed split and proximity
law aggregate into one global reference sublevel measure plus the local exceptional measures. -/
theorem blockwise_norm_sublevel_transfer_measure_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Countable ι] (μ : Measure α)
    (Z g τ : ι → α → E) (zeta : α → E) (B : ι → Set α)
    (A0 lam kappa eps : ℝ) (hA0 : 0 < A0)
    (hid : ∀ j t, Z j t = A0 • g j t + τ j t)
    (hprox : ∀ j, ∀ t ∈ B j, ‖g j t - zeta t‖ ≤ eps) :
    μ (⋃ j, {t | ‖Z j t‖ ≤ A0 * lam} ∩ B j)
      ≤ μ {t | ‖zeta t‖ ≤ lam + kappa + eps}
        + ∑' j, μ ({t | A0 * kappa ≤ ‖τ j t‖} ∩ B j) :=
  blockwise_transfer_measure_le μ
    (fun j => {t | ‖Z j t‖ ≤ A0 * lam})
    (fun j => {t | A0 * kappa ≤ ‖τ j t‖})
    B {t | ‖zeta t‖ ≤ lam + kappa + eps}
    fun j => norm_sublevel_split_transfer_subset (Z j) (g j) (τ j) zeta (B j)
      A0 lam kappa eps hA0 (hid j) (hprox j)

/-- **The full blockwise Selberg-transfer bound.** The algebraic split, the
per-block ζ-approximation, and the global aggregation are composed into one
measure endpoint: all carrier-small blocks are bounded by one ζ-sublevel set
plus the sum of taper exceptional measures. -/
theorem blockwise_sublevel_transfer_measure_le {α : Type*} [MeasurableSpace α]
    {ι : Type*} [Countable ι] (μ : Measure α)
    (Z g τ : ι → α → ℂ) (zeta : α → ℂ) (B : ι → Set α)
    (A0 lam eps : ℝ) (hA0 : 0 < A0)
    (hid : ∀ j t, Z j t = (A0 : ℂ) * g j t + τ j t)
    (hprox : ∀ j, ∀ t ∈ B j, ‖g j t - zeta t‖ ≤ eps) :
    μ (⋃ j, {t | ‖Z j t‖ ≤ A0 * lam} ∩ B j)
      ≤ μ {t | ‖zeta t‖ ≤ 2 * lam + eps}
        + ∑' j, μ ({t | A0 * lam ≤ ‖τ j t‖} ∩ B j) := by
  simpa only [two_mul] using
    blockwise_norm_sublevel_transfer_measure_le μ Z g τ zeta B A0 lam lam eps hA0
      (fun j t => by simpa only [Complex.real_smul] using hid j t) hprox

end RHTower
