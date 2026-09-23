import GaloisForLFunctions.RHTower.XiHeatCassiniWoldPositiveTenthAllSourceGraphNoGo
import GaloisForLFunctions.RHTower.XiHeatCassiniPrimeGapMomentThreshold

/-!
# T2 prime-clock strict-interior Abel-singularity no-go

Divisor tomography reduces Route T2 to regularity of the canonical natural Abel carrier on the
translated strict-right half-sector.  This module tests whether all source topology currently
proved for the Wold primitive can produce that regularity.

The test fails sharply on the literal ordered-prime clock.  For every `α > 0`, the residual
`r_N = exp (-α log p_N)` has an absolutely convergent Stieltjes--Abel germ on `-α < s < 0`, but the
germ has no continuous extension at `s = -α`.  Its positive radial mass diverges along the
intrinsic cofinal approach `q_M = α / (2 + α log p_M)`.  The proof uses only positivity,
Bertrand's unit bound for a prime-log cell, and the exact telescope
`sum_{N<M} (log p_{N+1} - log p_N) = log p_M - log p_0`.

At `α = 1/20`, this is exactly the existing T2 counterresidual.  That residual tends to zero,
belongs to every polynomial graph domain in the harmonic, activation-Fisher, and literal
essential-edge Hilbert sources, and satisfies the height-`1/10` Bohr square-summability law.
Nevertheless it has a genuine strict-interior Abel singularity at `s=-1/20`.  Hence those source
laws cannot be the missing producer for the RH-equivalent strict-interior regularity theorem.

The positive survivor is structural: T2 needs a positive exponential source radius,
source-marked noncompact boundary mass, or an arithmetic identity not visible to the intersection
of all finite polynomial graph domains.
-/

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive radial mass of a residual `exp (-α h)` on the ordered-prime Stieltjes clock. -/
def primeClockAbelRadialAtom (α q : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-q * xiMassNthPrimeLogHeight (N + 1)) *
    (1 - Real.exp (-((α - q) * xiHeatCassiniOrderedPrimeLogGap N)))

def primeClockAbelRadialCurrent (α q : ℝ) : ℝ :=
  ∑' N : ℕ, primeClockAbelRadialAtom α q N

/-- Intrinsic cofinal approach to the abscissa `-α`. -/
def primeClockAbelApproach (α : ℝ) (M : ℕ) : ℝ :=
  α / (2 + α * xiMassNthPrimeLogHeight M)

def primeClockAbelLowerScale (α : ℝ) : ℝ :=
  (α / 2) * Real.exp (-(1 + α))

def primeClockExpResidual (α : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-α * xiMassNthPrimeLogHeight N)

/-- Prime-clock Stieltjes first-difference atom. -/
def primeClockResidualStieltjesAtom (r : ℕ → ℝ) (s : ℝ) (N : ℕ) : ℝ :=
  r (N + 1) *
    (Real.exp (-s * xiMassNthPrimeLogHeight N) -
      Real.exp (-s * xiMassNthPrimeLogHeight (N + 1)))

def primeClockResidualStieltjesCurrent (r : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑' N : ℕ, primeClockResidualStieltjesAtom r s N

private theorem one_sub_exp_neg_ge_mul_exp_neg {x : ℝ} :
    x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x)
    (Real.exp_nonneg (-x))
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [add_mul, one_mul, hcancel] at h
  linarith

theorem primeClockAbelRadialAtom_nonneg
    {α q : ℝ} (_hq0 : 0 < q) (hqa : q < α) (N : ℕ) :
    0 ≤ primeClockAbelRadialAtom α q N := by
  have hg0 := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hk0 : 0 ≤ (α - q) * xiHeatCassiniOrderedPrimeLogGap N :=
    mul_nonneg (sub_nonneg.mpr hqa.le) hg0
  unfold primeClockAbelRadialAtom
  exact mul_nonneg (Real.exp_nonneg _)
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hk0)))

theorem summable_primeClockAbelRadialAtom
    {α q : ℝ} (hq0 : 0 < q) (hqa : q < α) :
    Summable (primeClockAbelRadialAtom α q) := by
  have hmajor := (summable_primeLogGap_mul_exp_neg_height hq0).mul_left α
  refine Summable.of_nonneg_of_le
    (primeClockAbelRadialAtom_nonneg hq0 hqa) (fun N => ?_) hmajor
  let g := xiHeatCassiniOrderedPrimeLogGap N
  let h := xiMassNthPrimeLogHeight N
  let h' := xiMassNthPrimeLogHeight (N + 1)
  have hg0 : 0 ≤ g := by
    simpa [g] using xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hα0 : 0 < α := lt_trans hq0 hqa
  have hk0 : 0 ≤ (α - q) * g := mul_nonneg (sub_nonneg.mpr hqa.le) hg0
  have hone : 1 - Real.exp (-((α - q) * g)) ≤ (α - q) * g := by
    have := Real.add_one_le_exp (-((α - q) * g))
    linarith
  have hheight : h ≤ h' := by
    have hh := nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)
    simpa [h, h', xiMassNthPrimeLogHeight] using hh
  have hexp : Real.exp (-q * h') ≤ Real.exp (-q * h) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hgap : (α - q) * g ≤ α * g := by
    nlinarith
  dsimp only [primeClockAbelRadialAtom, g, h, h']
  calc
    Real.exp (-q * h') * (1 - Real.exp (-((α - q) * g))) ≤
        Real.exp (-q * h') * ((α - q) * g) :=
      mul_le_mul_of_nonneg_left hone (Real.exp_nonneg _)
    _ ≤ Real.exp (-q * h') * (α * g) :=
      mul_le_mul_of_nonneg_left hgap (Real.exp_nonneg _)
    _ ≤ Real.exp (-q * h) * (α * g) :=
      mul_le_mul_of_nonneg_right hexp (mul_nonneg hα0.le hg0)
    _ = α * (g * Real.exp (-q * h)) := by ring

theorem primeClockAbelApproach_pos {α : ℝ} (hα : 0 < α) (M : ℕ) :
    0 < primeClockAbelApproach α M := by
  unfold primeClockAbelApproach
  have hh := xiMassNthPrimeLogHeight_pos M
  exact div_pos hα (by nlinarith [mul_pos hα hh])

theorem primeClockAbelApproach_lt_half {α : ℝ} (hα : 0 < α) (M : ℕ) :
    primeClockAbelApproach α M < α / 2 := by
  unfold primeClockAbelApproach
  have hh := xiMassNthPrimeLogHeight_pos M
  have hden : 0 < 2 + α * xiMassNthPrimeLogHeight M := by
    nlinarith [mul_pos hα hh]
  rw [div_lt_iff₀ hden]
  nlinarith [mul_pos hα hh]

theorem primeClockAbelApproach_tendsto_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (primeClockAbelApproach α) atTop (𝓝 0) := by
  have hden : Tendsto (fun M : ℕ => 2 + α * xiMassNthPrimeLogHeight M)
      atTop atTop := by
    have hm := tendsto_xiMassNthPrimeLogHeight_atTop.const_mul_atTop hα
    exact tendsto_atTop.2 (fun b => by
      filter_upwards [tendsto_atTop.1 hm (b - 2)] with M hM
      linarith)
  change Tendsto (fun M : ℕ => α / (2 + α * xiMassNthPrimeLogHeight M))
    atTop (𝓝 0)
  exact tendsto_const_nhds.div_atTop hden

theorem primeClockAbelLowerScale_pos {α : ℝ} (hα : 0 < α) :
    0 < primeClockAbelLowerScale α := by
  unfold primeClockAbelLowerScale
  positivity

theorem primeClockAbelRadialAtom_lower_on_approach
    {α : ℝ} (hα : 0 < α) {N M : ℕ} (hNM : N < M) :
    primeClockAbelLowerScale α * xiHeatCassiniOrderedPrimeLogGap N ≤
      primeClockAbelRadialAtom α (primeClockAbelApproach α M) N := by
  let q := primeClockAbelApproach α M
  let g := xiHeatCassiniOrderedPrimeLogGap N
  let h' := xiMassNthPrimeLogHeight (N + 1)
  let hM := xiMassNthPrimeLogHeight M
  let κ := (α - q) * g
  have hq0 : 0 < q := by simpa [q] using primeClockAbelApproach_pos hα M
  have hqhalf : q < α / 2 := by
    simpa [q] using primeClockAbelApproach_lt_half hα M
  have hqa : q < α := by linarith
  have hg0 : 0 ≤ g := by
    simpa [g] using xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hg1 : g ≤ 1 := by
    simpa [g] using xiHeatCassiniOrderedPrimeLogGap_le_one N
  have hκ0 : 0 ≤ κ := by
    exact mul_nonneg (sub_nonneg.mpr hqa.le) hg0
  have hκa : κ ≤ α := by
    have hsub : α - q ≤ α := by linarith
    calc
      κ ≤ α * g := by
        exact mul_le_mul_of_nonneg_right hsub hg0
      _ ≤ α * 1 := mul_le_mul_of_nonneg_left hg1 hα.le
      _ = α := mul_one α
  have hh'le : h' ≤ hM := by
    have hh := nthPrimeSubtype_log_strictMono.monotone
      (show N + 1 ≤ M by omega)
    simpa [h', hM, xiMassNthPrimeLogHeight] using hh
  have hden : 0 < 2 + α * hM := by
    have hhM : 0 < hM := by simpa [hM] using xiMassNthPrimeLogHeight_pos M
    nlinarith [mul_pos hα hhM]
  have hqhm : q * hM < 1 := by
    have hhM : 0 < hM := by simpa [hM] using xiMassNthPrimeLogHeight_pos M
    dsimp only [q, primeClockAbelApproach]
    rw [div_mul_eq_mul_div, div_lt_one hden]
    nlinarith
  have hqh' : q * h' < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hh'le hq0.le) hqhm
  have hexpHeight : Real.exp (-1) ≤ Real.exp (-q * h') := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hκlower : (α / 2) * g ≤ κ := by
    exact mul_le_mul_of_nonneg_right (by linarith) hg0
  have hexpGap : Real.exp (-α) ≤ Real.exp (-κ) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hgapTerm :
      (α / 2) * g * Real.exp (-α) ≤ 1 - Real.exp (-κ) := by
    calc
      (α / 2) * g * Real.exp (-α) ≤ κ * Real.exp (-α) :=
        mul_le_mul_of_nonneg_right hκlower (Real.exp_nonneg _)
      _ ≤ κ * Real.exp (-κ) :=
        mul_le_mul_of_nonneg_left hexpGap hκ0
      _ ≤ 1 - Real.exp (-κ) := one_sub_exp_neg_ge_mul_exp_neg
  have hproduct :
      Real.exp (-1) * ((α / 2) * g * Real.exp (-α)) ≤
        Real.exp (-q * h') * (1 - Real.exp (-κ)) := by
    exact mul_le_mul hexpHeight hgapTerm
      (mul_nonneg (mul_nonneg (by positivity) hg0) (Real.exp_nonneg _))
      (Real.exp_nonneg _)
  dsimp only [primeClockAbelLowerScale, primeClockAbelRadialAtom, q, g, h', κ]
  rw [show -(1 + α) = -1 + -α by ring, Real.exp_add]
  nlinarith

theorem sum_range_xiHeatCassiniOrderedPrimeLogGap (M : ℕ) :
    ∑ N ∈ Finset.range M, xiHeatCassiniOrderedPrimeLogGap N =
      xiMassNthPrimeLogHeight M - xiMassNthPrimeLogHeight 0 := by
  unfold xiHeatCassiniOrderedPrimeLogGap
  calc
    ∑ N ∈ Finset.range M,
        (xiMassNthPrimeLogHeight (N + 1) - xiMassNthPrimeLogHeight N) =
      -(∑ N ∈ Finset.range M,
        (xiMassNthPrimeLogHeight N - xiMassNthPrimeLogHeight (N + 1))) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro N _
          ring
    _ = -(xiMassNthPrimeLogHeight 0 - xiMassNthPrimeLogHeight M) := by
      rw [Finset.sum_range_sub']
    _ = xiMassNthPrimeLogHeight M - xiMassNthPrimeLogHeight 0 := by ring

theorem primeClockAbelRadialCurrent_lower_on_approach
    {α : ℝ} (hα : 0 < α) (M : ℕ) :
    primeClockAbelLowerScale α *
        (xiMassNthPrimeLogHeight M - xiMassNthPrimeLogHeight 0) ≤
      primeClockAbelRadialCurrent α (primeClockAbelApproach α M) := by
  have hq0 := primeClockAbelApproach_pos hα M
  have hqa : primeClockAbelApproach α M < α := by
    have := primeClockAbelApproach_lt_half hα M
    linarith
  have hsum := summable_primeClockAbelRadialAtom hq0 hqa
  calc
    primeClockAbelLowerScale α *
        (xiMassNthPrimeLogHeight M - xiMassNthPrimeLogHeight 0) =
      ∑ N ∈ Finset.range M,
        primeClockAbelLowerScale α * xiHeatCassiniOrderedPrimeLogGap N := by
          rw [← sum_range_xiHeatCassiniOrderedPrimeLogGap M,
            Finset.mul_sum]
    _ ≤ ∑ N ∈ Finset.range M,
        primeClockAbelRadialAtom α (primeClockAbelApproach α M) N := by
      exact Finset.sum_le_sum fun N hN =>
        primeClockAbelRadialAtom_lower_on_approach hα
          (Finset.mem_range.mp hN)
    _ ≤ primeClockAbelRadialCurrent α (primeClockAbelApproach α M) := by
      exact hsum.sum_le_tsum (Finset.range M)
        (fun N _ => primeClockAbelRadialAtom_nonneg hq0 hqa N)

theorem tendsto_primeClockAbelLowerProfile_atTop
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun M : ℕ => primeClockAbelLowerScale α *
      (xiMassNthPrimeLogHeight M - xiMassNthPrimeLogHeight 0)) atTop atTop := by
  have hsub : Tendsto (fun M : ℕ =>
      xiMassNthPrimeLogHeight M - xiMassNthPrimeLogHeight 0) atTop atTop := by
    exact tendsto_atTop.2 (fun b => by
      filter_upwards [tendsto_atTop.1 tendsto_xiMassNthPrimeLogHeight_atTop
        (b + xiMassNthPrimeLogHeight 0)] with M hM
      linarith)
  exact hsub.const_mul_atTop (primeClockAbelLowerScale_pos hα)

/-- The positive radial mass diverges at every exponential residual abscissa `-α`. -/
theorem tendsto_primeClockAbelRadialCurrent_approach_atTop
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun M : ℕ =>
      primeClockAbelRadialCurrent α (primeClockAbelApproach α M)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [tendsto_atTop.1 (tendsto_primeClockAbelLowerProfile_atTop hα) b]
    with M hM
  exact hM.trans (primeClockAbelRadialCurrent_lower_on_approach hα M)

/-- No finite continuous boundary value can extend the radial germ at `q=0`. -/
theorem not_exists_continuousAt_primeClockAbelRadialCurrent_zero
    {α : ℝ} (hα : 0 < α) :
    ¬ ∃ F : ℝ → ℝ, ContinuousAt F 0 ∧
      ∀ q : ℝ, 0 < q → q < α → F q = primeClockAbelRadialCurrent α q := by
  rintro ⟨F, hF, hagree⟩
  have hq := primeClockAbelApproach_tendsto_zero hα
  have hfinite : Tendsto (fun M : ℕ =>
      primeClockAbelRadialCurrent α (primeClockAbelApproach α M))
      atTop (𝓝 (F 0)) := by
    apply (hF.tendsto.comp hq).congr'
    filter_upwards with M
    simpa only [Function.comp_apply] using
      hagree _ (primeClockAbelApproach_pos hα M)
        (lt_trans (primeClockAbelApproach_lt_half hα M) (by linarith))
  have hinfinite := tendsto_primeClockAbelRadialCurrent_approach_atTop hα
  have hlarge : ∀ᶠ M : ℕ in atTop,
      F 0 + 1 ≤ primeClockAbelRadialCurrent α (primeClockAbelApproach α M) :=
    tendsto_atTop.1 hinfinite (F 0 + 1)
  have hsmall : ∀ᶠ M : ℕ in atTop,
      primeClockAbelRadialCurrent α (primeClockAbelApproach α M) < F 0 + 1 / 2 :=
    hfinite (Iio_mem_nhds (by norm_num : F 0 < F 0 + 1 / 2))
  obtain ⟨M, hMlarge, hMsmall⟩ := (hlarge.and hsmall).exists
  linarith

theorem neg_primeClockExpResidualStieltjesAtom_eq_radial
    (α q : ℝ) (N : ℕ) :
    -primeClockResidualStieltjesAtom (primeClockExpResidual α) (-α + q) N =
      primeClockAbelRadialAtom α q N := by
  let h := xiMassNthPrimeLogHeight N
  let h' := xiMassNthPrimeLogHeight (N + 1)
  let g := xiHeatCassiniOrderedPrimeLogGap N
  have hh : h' = h + g := by
    simp only [h, h', g, xiHeatCassiniOrderedPrimeLogGap]
    ring
  change -(Real.exp (-α * h') *
      (Real.exp (-(-α + q) * h) - Real.exp (-(-α + q) * h'))) =
    Real.exp (-q * h') * (1 - Real.exp (-((α - q) * g)))
  rw [mul_sub, neg_sub, ← Real.exp_add, ← Real.exp_add,
    mul_sub, mul_one, ← Real.exp_add]
  congr 1 <;> rw [hh] <;> ring_nf

theorem primeClockExpResidualStieltjesCurrent_eq_neg_radial
    (α q : ℝ) :
    primeClockResidualStieltjesCurrent (primeClockExpResidual α) (-α + q) =
      -primeClockAbelRadialCurrent α q := by
  rw [primeClockResidualStieltjesCurrent, primeClockAbelRadialCurrent, ← tsum_neg]
  apply tsum_congr
  intro N
  linarith [neg_primeClockExpResidualStieltjesAtom_eq_radial α q N]

/-- The Stieltjes series is an honest absolutely convergent germ on its maximal open radial
strip `-α < s < 0`. -/
theorem summable_primeClockExpResidualStieltjesAtom
    {α s : ℝ} (hs0 : -α < s) (hs1 : s < 0) :
    Summable (primeClockResidualStieltjesAtom (primeClockExpResidual α) s) := by
  let q := s + α
  have hq0 : 0 < q := by dsimp only [q]; linarith
  have hqa : q < α := by dsimp only [q]; linarith
  have hradial := (summable_primeClockAbelRadialAtom hq0 hqa).neg
  refine hradial.congr (fun N => ?_)
  have heq := neg_primeClockExpResidualStieltjesAtom_eq_radial α q N
  rw [show -α + q = s by dsimp only [q]; ring] at heq
  linarith

/-- The prime-clock Stieltjes germ has no continuous extension at its strict-interior
abscissa `s=-α`. -/
theorem not_exists_continuousAt_primeClockExpResidualStieltjesCurrent
    {α : ℝ} (hα : 0 < α) :
    ¬ ∃ F : ℝ → ℝ, ContinuousAt F (-α) ∧
      ∀ s : ℝ, -α < s → s < 0 →
        F s = primeClockResidualStieltjesCurrent (primeClockExpResidual α) s := by
  intro h
  apply not_exists_continuousAt_primeClockAbelRadialCurrent_zero hα
  obtain ⟨F, hF, hagree⟩ := h
  refine ⟨fun q => -F (-α + q), ?_, ?_⟩
  · have hshift : Tendsto (fun q : ℝ => -α + q) (𝓝 0) (𝓝 (-α + 0)) :=
      tendsto_const_nhds.add tendsto_id
    change Tendsto (fun q : ℝ => -F (-α + q)) (𝓝 0)
      (𝓝 (-F (-α + 0)))
    simpa only [Function.comp_apply, add_zero] using
      (hF.tendsto.comp (by simpa using hshift)).neg
  · intro q hq0 hqa
    change -F (-α + q) = primeClockAbelRadialCurrent α q
    rw [hagree (-α + q) (by linarith) (by linarith),
      primeClockExpResidualStieltjesCurrent_eq_neg_radial]
    simp

theorem t2BohrTerminalCounterResidual_eq_primeClockExpResidual :
    t2BohrTerminalCounterResidual = primeClockExpResidual (1 / 20) := by
  funext N
  unfold t2BohrTerminalCounterResidual primeClockExpResidual
  congr 1
  ring

/-- Reconstruction principle asserting that all currently proved T2 source laws force a
continuous prime-clock Abel germ throughout the translated strict interior. -/
def T2PrimeClockBohrAllSourceGraphInteriorAbelRegularityPrinciple : Prop :=
  ∀ r : ℕ → ℝ,
    Tendsto r atTop (𝓝 0) →
    (∀ k : ℕ, Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) /
          (nthPrimeSubtype N : ℝ) * r N ^ (2 : ℕ))) →
    (∀ k : ℕ, Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          primeActivationOccupancyFisherDensity (nthPrimeSubtype N) * r N ^ (2 : ℕ))) →
    (∀ k : ℕ, Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          primeFirstTraceEssentialHarmonicCoordinate (nthPrimeSubtype N) * r N ^ (2 : ℕ))) →
    Summable (fun N : ℕ =>
      ‖(((r (N + 1) - r N : ℝ) : ℂ) *
        (Real.exp (xiMassNthPrimeLogHeight (N + 1) / 10) : ℂ))‖ ^ (2 : ℕ)) →
    ∃ F : ℝ → ℝ, ContinuousAt F (-(1 / 20 : ℝ)) ∧
      ∀ s : ℝ, -(1 / 20 : ℝ) < s → s < 0 →
        F s = primeClockResidualStieltjesCurrent r s

/-- **T2 strict-interior Abel-regularity route kill.** Every proved polynomial graph law in all
three source geometries, primitive vanishing, and the height-`1/10` Bohr law remain compatible
with an actual Stieltjes--Abel singularity at `s=-1/20`. -/
theorem not_T2PrimeClockBohrAllSourceGraphInteriorAbelRegularityPrinciple :
    ¬ T2PrimeClockBohrAllSourceGraphInteriorAbelRegularityPrinciple := by
  intro hregular
  obtain ⟨F, hF, hagree⟩ := hregular t2BohrTerminalCounterResidual
    t2BohrTerminalCounterResidual_tendsto_zero
    summable_t2BohrTerminalCounterResidual_allLogGraphEnergy
    summable_t2BohrTerminalCounterResidual_activationFisherAllLogGraphEnergy
    summable_t2BohrTerminalCounterResidual_actualEssentialEdgeAllLogGraphEnergy
    summable_norm_sq_t2BohrTerminalCounterCoefficient
  apply not_exists_continuousAt_primeClockExpResidualStieltjesCurrent
    (by norm_num : (0 : ℝ) < 1 / 20)
  refine ⟨F, hF, ?_⟩
  intro s hs0 hs1
  rw [← t2BohrTerminalCounterResidual_eq_primeClockExpResidual]
  exact hagree s hs0 hs1

end

end RHTower
