import GaloisForLFunctions.RHTower.ZetaVoroninUniversalityOnSmallDiscs
import GaloisForLFunctions.RHTower.ZetaRecurrenceAtEveryPointModuloItsZeros
import GaloisForLFunctions.RHTower.XiSliceTypicalOrderPowerSaving

/-!
# The self-return threshold of `ζ` on a disc is its distance to the nonvanishing targets

Let `D = closedBall z₀ r` be a closed disc of the strip `½ < Re s < 1`.  Bagchi's self-return set
`zetaReturnSet D ε = {τ : sup_D |ζ(s + iτ) − ζ(s)| < ε}` has positive lower density for every
`ε > 0` iff `ζ` has no zero near `D`, and around a zero it has density zero for small `ε` (the
local Bagchi criterion).  This file identifies the exact threshold in `ε` and the exact size of
the return set on both sides of it.

* `nonvanishingDiscTargets z₀ r` are the functions analytic and nonvanishing on a neighbourhood of
  `D`; `zetaNonvanishingDistance z₀ r` is the infimum of the tolerances `ε` for which some such
  target is within `ε` of `ζ` uniformly on `D`.
* **Above the threshold** (`exists_pos_density_zetaReturnSet_of_distance_lt`): if the doubled disc
  lies in the strip and `d < ε`, the `ε`-self-returns have positive lower density.  A target within
  `ε₁ < ε` of `ζ` is approximated by `ζ(· + iτ)` at positive density (universality on small discs),
  and those heights are `ε`-self-returns by the triangle inequality.
* **Below the threshold** (`exists_zero_of_mem_zetaReturnSet_of_lt_distance`): if `ε < d`, every
  `ε`-self-return height `τ` carries a zero of `ζ` in the translated disc `D + iτ`, since otherwise
  `ζ(· + iτ)` itself would be an admissible target within `ε`.  The self-returns therefore lie in
  the shadow of the zeros with real part `≥ Re z₀ − r`, and the Ingham–Huxley zero-density
  estimate makes them power-saving rare: `|zetaReturnSet D ε ∩ [0, T]| ≤ T^θ` with `θ < 1`
  (`exists_volume_zetaReturnSet_le_rpow_of_lt_distance`, through the dyadic-to-prefix lemma
  `exists_forall_volume_inter_Icc_zero_le_rpow_of_window`).
* **The threshold vanishes exactly off the zeros** (`zetaNonvanishingDistance_eq_zero_iff`):
  `d = 0` iff `ζ` has no zero in the open disc.  Scaling `ζ` towards the centre gives admissible
  targets arbitrarily close to `ζ` when the open disc is zero-free; a zero inside forces, by the
  minimum modulus principle, every admissible target to stay at distance at least half the minimum
  of `|ζ|` on a small circle around it.

Consequences.  On every disc of the strip with doubled closure in the strip the self-return
measure obeys a dichotomy with no intermediate regime (`zetaReturnSet_volume_dichotomy`): linear
in `T` above `d`, at most `T^θ` below `d`.  Strong recurrence on `closedBall z₀ r` is equivalent to
`d = 0` and to the absence of zeros in `ball z₀ r` (`zetaDiscStronglyRecurrentOn_iff_distance_eq_zero`,
`zetaDiscStronglyRecurrentOn_iff_forall_ball_ne_zero`).  The local Bagchi criterion sharpens to the
**power-saving receiver** (`riemannZeta_ne_zero_iff_zetaReturnSet_not_powerSaving`): `ζ(z₀) ≠ 0`
iff on some disc about `z₀` the self-return measure exceeds `T^θ` infinitely often, for every
tolerance and every `θ < 1`.  Around an off-line zero the self-returns are power-saving rare
(`exists_volume_zetaReturnSet_le_rpow_of_zero`), sharpening `exists_zetaSelfReturn_density_zero`.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

/-! ## 1. Nonvanishing targets and the distance -/

/-- The targets analytic and nonvanishing on a neighbourhood of `closedBall z₀ r`. -/
def nonvanishingDiscTargets (z₀ : ℂ) (r : ℝ) : Set (ℂ → ℂ) :=
  {g | ∃ η > 0, AnalyticOnNhd ℂ g (ball z₀ (r + η)) ∧ ∀ z ∈ ball z₀ (r + η), g z ≠ 0}

/-- The admissible tolerances: `ε` such that some nonvanishing target is within `ε` of `ζ`
uniformly on the closed disc. -/
def zetaNonvanishingTolerances (z₀ : ℂ) (r : ℝ) : Set ℝ :=
  {ε | ∃ g ∈ nonvanishingDiscTargets z₀ r, ∀ z ∈ closedBall z₀ r, ‖riemannZeta z - g z‖ < ε}

/-- The distance from `ζ` to the nonvanishing targets on `closedBall z₀ r`: the infimum of the
admissible tolerances. -/
def zetaNonvanishingDistance (z₀ : ℂ) (r : ℝ) : ℝ :=
  sInf (zetaNonvanishingTolerances z₀ r)

theorem zetaNonvanishingTolerances_upward {z₀ : ℂ} {r ε ε' : ℝ}
    (h : ε ∈ zetaNonvanishingTolerances z₀ r) (hle : ε ≤ ε') :
    ε' ∈ zetaNonvanishingTolerances z₀ r := by
  obtain ⟨g, hg, hε⟩ := h
  exact ⟨g, hg, fun z hz => (hε z hz).trans_le hle⟩

theorem pos_of_mem_zetaNonvanishingTolerances {z₀ : ℂ} {r ε : ℝ} (hr : 0 ≤ r)
    (h : ε ∈ zetaNonvanishingTolerances z₀ r) : 0 < ε := by
  obtain ⟨g, -, hε⟩ := h
  exact (norm_nonneg _).trans_lt (hε z₀ (mem_closedBall_self hr))

theorem bddBelow_zetaNonvanishingTolerances (z₀ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    BddBelow (zetaNonvanishingTolerances z₀ r) :=
  ⟨0, fun _ h => (pos_of_mem_zetaNonvanishingTolerances hr h).le⟩

/-- `ζ` is continuous on a closed disc left of `Re s = 1`. -/
theorem continuousOn_riemannZeta_closedBall {z₀ : ℂ} {r : ℝ} (h1 : z₀.re + r < 1) :
    ContinuousOn riemannZeta (closedBall z₀ r) := by
  intro z hz
  have hne : z ≠ 1 := by
    intro h
    have := (abs_le.mp ((abs_re_le_norm (z - z₀)).trans (mem_closedBall_iff_norm.mp hz))).2
    rw [sub_re, h, one_re] at this
    linarith
  exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt

theorem nonempty_zetaNonvanishingTolerances {z₀ : ℂ} {r : ℝ} (h1 : z₀.re + r < 1) :
    (zetaNonvanishingTolerances z₀ r).Nonempty := by
  have hc : ContinuousOn (fun z => riemannZeta z - 1) (closedBall z₀ r) :=
    (continuousOn_riemannZeta_closedBall h1).sub continuousOn_const
  obtain ⟨C, hC⟩ := (isCompact_closedBall z₀ r).exists_bound_of_continuousOn hc
  refine ⟨C + 1, fun _ => 1, ⟨1, one_pos, analyticOnNhd_const, fun _ _ => one_ne_zero⟩,
    fun z hz => ?_⟩
  linarith [hC z hz]

theorem zetaNonvanishingDistance_nonneg {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ zetaNonvanishingDistance z₀ r :=
  Real.sInf_nonneg fun _ h => (pos_of_mem_zetaNonvanishingTolerances hr h).le

/-- Above the distance, every tolerance is admissible. -/
theorem mem_zetaNonvanishingTolerances_of_distance_lt {z₀ : ℂ} {r ε : ℝ}
    (h1 : z₀.re + r < 1) (hε : zetaNonvanishingDistance z₀ r < ε) :
    ε ∈ zetaNonvanishingTolerances z₀ r := by
  obtain ⟨ε₁, hε₁, hlt⟩ := exists_lt_of_csInf_lt (nonempty_zetaNonvanishingTolerances h1) hε
  exact zetaNonvanishingTolerances_upward hε₁ hlt.le

/-- Below the distance, no tolerance is admissible. -/
theorem not_mem_zetaNonvanishingTolerances_of_lt_distance {z₀ : ℂ} {r ε : ℝ} (hr : 0 ≤ r)
    (hε : ε < zetaNonvanishingDistance z₀ r) :
    ε ∉ zetaNonvanishingTolerances z₀ r := fun h =>
  absurd (csInf_le (bddBelow_zetaNonvanishingTolerances z₀ hr) h) (not_le.mpr hε)

/-! ## 2. Nonvanishing on a closed disc extends to a neighbourhood -/

/-- A function continuous on `closedBall z₀ R` and nonvanishing on `closedBall z₀ r`, `r < R`, is
nonvanishing on some larger open ball `ball z₀ (r + η)`: its zero set in the big disc is compact
and misses the small disc, so it stays at positive distance from the centre beyond `r`. -/
theorem exists_pos_ball_ne_zero_of_closedBall {g : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ} (hrR : r < R)
    (hg : ContinuousOn g (closedBall z₀ R)) (h0 : ∀ z ∈ closedBall z₀ r, g z ≠ 0) :
    ∃ η > 0, r + η ≤ R ∧ ∀ z ∈ ball z₀ (r + η), g z ≠ 0 := by
  set Z : Set ℂ := closedBall z₀ R ∩ g ⁻¹' {0} with hZ
  have hZc : IsCompact Z := (isCompact_closedBall z₀ R).of_isClosed_subset
    (hg.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton) inter_subset_left
  by_cases hne : Z.Nonempty
  · obtain ⟨z₁, hz₁, hmin⟩ :=
      hZc.exists_isMinOn hne (continuous_id.dist continuous_const).continuousOn
    have hz₁0 : g z₁ = 0 := hz₁.2
    have hz₁r : r < dist z₁ z₀ := by
      by_contra hle
      exact h0 z₁ (mem_closedBall.mpr (not_lt.mp hle)) hz₁0
    have hm1 := min_le_left (R - r) ((dist z₁ z₀ - r) / 2)
    have hm2 := min_le_right (R - r) ((dist z₁ z₀ - r) / 2)
    refine ⟨min (R - r) ((dist z₁ z₀ - r) / 2), lt_min (by linarith) (by linarith),
      by linarith, fun z hz hgz => ?_⟩
    have h2 := mem_ball.mp hz
    have hzZ : z ∈ Z := ⟨mem_closedBall.mpr (by linarith), hgz⟩
    have h3 : dist z₁ z₀ ≤ dist z z₀ := isMinOn_iff.mp hmin z hzZ
    linarith
  · refine ⟨R - r, by linarith, by linarith, fun z hz hgz => hne ⟨z, ?_, hgz⟩⟩
    rw [show r + (R - r) = R by ring] at hz
    exact ball_subset_closedBall hz

/-! ## 3. The shifted `ζ` as a target -/

/-- `ζ(· + iτ)` is continuous on every closed disc left of `Re s = 1`. -/
theorem continuousOn_riemannZeta_shift_closedBall {z₀ : ℂ} {R : ℝ} (hR : z₀.re + R < 1)
    (τ : ℝ) : ContinuousOn (fun z => riemannZeta (z + τ * I)) (closedBall z₀ R) := by
  intro z hz
  have hne : z + τ * I ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, one_re] at h'
    have := (abs_le.mp ((abs_re_le_norm (z - z₀)).trans (mem_closedBall_iff_norm.mp hz))).2
    rw [sub_re] at this
    linarith
  exact ((differentiableAt_riemannZeta hne).comp z
    (differentiableAt_id.add_const _)).continuousAt.continuousWithinAt

/-- `ζ(· + iτ)` is analytic on every open ball left of `Re s = 1`. -/
theorem analyticOnNhd_riemannZeta_shift {z₀ : ℂ} {R : ℝ} (hR : z₀.re + R < 1) (τ : ℝ) :
    AnalyticOnNhd ℂ (fun z => riemannZeta (z + τ * I)) (ball z₀ R) := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_ball
  have hne : z + τ * I ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, one_re] at h'
    have := (abs_lt.mp ((abs_re_le_norm (z - z₀)).trans_lt (mem_ball_iff_norm.mp hz))).2
    rw [sub_re] at this
    linarith
  exact ((differentiableAt_riemannZeta hne).comp z
    (differentiableAt_id.add_const _)).differentiableWithinAt

/-- **Below the threshold, a self-return transports a zero.**  If `ε < d`, every `ε`-self-return
height `τ` carries a zero of `ζ` in the translated closed disc. -/
theorem exists_zero_of_mem_zetaReturnSet_of_lt_distance {z₀ : ℂ} {r ε τ : ℝ} (hr : 0 < r)
    (h1 : z₀.re + r < 1) (hε : ε < zetaNonvanishingDistance z₀ r)
    (hτ : τ ∈ zetaReturnSet (closedBall z₀ r) ε) :
    ∃ z ∈ closedBall z₀ r, riemannZeta (z + τ * I) = 0 := by
  by_contra hno
  push Not at hno
  set R : ℝ := r + (1 - z₀.re - r) / 2 with hR
  have hrR : r < R := by rw [hR]; linarith
  have hR1 : z₀.re + R < 1 := by rw [hR]; linarith
  obtain ⟨η, hη, hηR, hne⟩ := exists_pos_ball_ne_zero_of_closedBall hrR
    (continuousOn_riemannZeta_shift_closedBall hR1 τ) hno
  apply not_mem_zetaNonvanishingTolerances_of_lt_distance hr.le hε
  refine ⟨fun z => riemannZeta (z + τ * I),
    ⟨η, hη, analyticOnNhd_riemannZeta_shift (by linarith) τ, hne⟩, fun z hz => ?_⟩
  rw [norm_sub_rev]
  exact hτ z hz

/-! ## 4. Below the threshold: self-returns lie in the zero shadow -/

/-- Below the threshold, the `ε`-self-return heights, shifted by `Im z₀`, lie in the shadow
`zetaZeroShadow (Re z₀ − r) 2` of the zeros with real part `≥ Re z₀ − r`. -/
theorem zetaReturnSet_subset_shadow_of_lt_distance {z₀ : ℂ} {r ε : ℝ} (hr : 0 < r)
    (h1 : z₀.re + r < 1) (hr2 : r ≤ 2) (hε : ε < zetaNonvanishingDistance z₀ r) :
    zetaReturnSet (closedBall z₀ r) ε ⊆
      (fun τ => z₀.im + τ) ⁻¹' zetaZeroShadow (z₀.re - r) 2 := by
  intro τ hτ
  obtain ⟨z, hz, hz0⟩ := exists_zero_of_mem_zetaReturnSet_of_lt_distance hr h1 hε hτ
  have hzn := mem_closedBall_iff_norm.mp hz
  have hre := abs_le.mp ((abs_re_le_norm (z - z₀)).trans hzn)
  have him := abs_le.mp ((abs_im_le_norm (z - z₀)).trans hzn)
  rw [sub_re] at hre
  rw [sub_im] at him
  refine ⟨z + τ * I, hz0, ?_, ?_⟩
  · simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    linarith [hre.1]
  · simp only [add_im, mul_im, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      add_zero]
    rw [abs_le]
    constructor <;> linarith [him.1, him.2]

/-- A set carried by the translation `τ ↦ γ + τ` into `Sh` has, on the dyadic window `[T, 2T]`,
at most the measure of `Sh` on the three dyadic windows `[T/2, T]`, `[T, 2T]`, `[2T, 4T]`,
once `T ≥ 2|γ|`. -/
theorem volume_inter_Icc_le_three_windows {R Sh : Set ℝ} {γ : ℝ}
    (hsub : R ⊆ (fun τ => γ + τ) ⁻¹' Sh) {T : ℝ} (hT : 2 * |γ| ≤ T) :
    volume (R ∩ Icc T (2 * T)) ≤
      volume (Sh ∩ Icc (T / 2) (2 * (T / 2))) + volume (Sh ∩ Icc T (2 * T)) +
        volume (Sh ∩ Icc (2 * T) (2 * (2 * T))) := by
  have hγ1 := le_abs_self γ
  have hγ2 := neg_abs_le γ
  have hcover : Icc (T + γ) (2 * T + γ) ⊆
      Icc (T / 2) (2 * (T / 2)) ∪ Icc T (2 * T) ∪ Icc (2 * T) (2 * (2 * T)) := by
    intro x hx
    rcases le_total x T with h | h
    · exact Or.inl (Or.inl ⟨by linarith [hx.1], by linarith⟩)
    rcases le_total x (2 * T) with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr ⟨h', by linarith [hx.2]⟩
  have hpre : R ∩ Icc T (2 * T) ⊆ (fun τ => γ + τ) ⁻¹' (Sh ∩ Icc (T + γ) (2 * T + γ)) := by
    rintro τ ⟨hτ, hτT⟩
    exact ⟨hsub hτ, by linarith [hτT.1], by linarith [hτT.2]⟩
  calc volume (R ∩ Icc T (2 * T))
      ≤ volume ((fun τ => γ + τ) ⁻¹' (Sh ∩ Icc (T + γ) (2 * T + γ))) := measure_mono hpre
    _ = volume (Sh ∩ Icc (T + γ) (2 * T + γ)) := measure_preimage_add _ _ _
    _ ≤ volume (Sh ∩ Icc (T / 2) (2 * (T / 2)) ∪ Sh ∩ Icc T (2 * T) ∪
          Sh ∩ Icc (2 * T) (2 * (2 * T))) := by
        refine measure_mono ?_
        rw [← inter_union_distrib_left, ← inter_union_distrib_left]
        exact inter_subset_inter_right _ hcover
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)

/-- A polylogarithmic window bound at `T₁ ≤ a ≤ 2T` is dominated by the bound at `2T`. -/
theorem volume_window_le_of_le {Sh : Set ℝ} {C E T₁ : ℝ} {B : ℕ} (hC : 0 ≤ C) (hE0 : 0 ≤ E)
    (hshadow : ∀ T : ℝ, T₁ ≤ T → volume (Sh ∩ Icc T (2 * T)) ≤
      ENNReal.ofReal (C * (1 + Real.log T) ^ B * T ^ E))
    {T a : ℝ} (hT : 2 * T₁ ≤ T) (hT2 : 2 ≤ T) (ha1 : T / 2 ≤ a) (ha2 : a ≤ 2 * T) :
    volume (Sh ∩ Icc a (2 * a)) ≤
      ENNReal.ofReal (C * (1 + Real.log (2 * T)) ^ B * (2 * T) ^ E) := by
  have ha0 : 1 ≤ a := by linarith
  refine (hshadow a (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hl : 0 ≤ 1 + Real.log a := by linarith [Real.log_nonneg ha0]
  have h1' : (1 + Real.log a) ^ B ≤ (1 + Real.log (2 * T)) ^ B :=
    pow_le_pow_left₀ hl (by linarith [Real.log_le_log (by linarith : (0 : ℝ) < a) ha2]) B
  have h2' : a ^ E ≤ (2 * T) ^ E := Real.rpow_le_rpow (by linarith) ha2 hE0
  gcongr

/-- The polylogarithmic window bound at `2T` is absorbed into the one at `T`, for `0 ≤ E ≤ 2`. -/
theorem three_mul_window_bound_le {C E : ℝ} {B : ℕ} (hC : 0 ≤ C) (hE0 : 0 ≤ E) (hE2 : E ≤ 2)
    {T : ℝ} (hT1 : 1 ≤ T) :
    3 * (C * (1 + Real.log (2 * T)) ^ B * (2 * T) ^ E) ≤
      12 * 2 ^ B * C * (1 + Real.log T) ^ B * T ^ E := by
  have hT0 : 0 < T := by linarith
  have hlogT := Real.log_nonneg hT1
  have hlog2T0 : 0 ≤ 1 + Real.log (2 * T) := by
    linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * T)]
  have hlog2T : 1 + Real.log (2 * T) ≤ 2 * (1 + Real.log T) := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    linarith [Real.log_two_lt_d9]
  have hpowlog : (1 + Real.log (2 * T)) ^ B ≤ 2 ^ B * (1 + Real.log T) ^ B := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hlog2T0 hlog2T B
  have hTE0 : 0 ≤ T ^ E := by positivity
  have hpow2 : (2 * T) ^ E ≤ 4 * T ^ E := by
    rw [Real.mul_rpow (by norm_num) hT0.le]
    have h4 : (2 : ℝ) ^ E ≤ 4 := by
      calc (2 : ℝ) ^ E ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hE2
        _ = 4 := by rw [Real.rpow_two]; norm_num
    exact mul_le_mul_of_nonneg_right h4 hTE0
  have hlogT0 : 0 ≤ (1 + Real.log T) ^ B := by positivity
  calc 3 * (C * (1 + Real.log (2 * T)) ^ B * (2 * T) ^ E)
      ≤ 3 * (C * (2 ^ B * (1 + Real.log T) ^ B) * (4 * T ^ E)) := by gcongr
    _ = 12 * 2 ^ B * C * (1 + Real.log T) ^ B * T ^ E := by ring

/-- **Below the threshold the self-returns are power-saving rare on dyadic windows.**  For
`ε < d` there is `θ < 1` with `|zetaReturnSet D ε ∩ [T, 2T]| ≤ T^θ` for all large `T`, from the
Ingham–Huxley bound on the zero shadow. -/
theorem exists_volume_zetaReturnSet_window_le_rpow_of_lt_distance {z₀ : ℂ} {r ε : ℝ}
    (hr : 0 < r) (h0 : 1 / 2 < z₀.re - r) (h1 : z₀.re + r < 1)
    (hε : ε < zetaNonvanishingDistance z₀ r) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      volume (zetaReturnSet (closedBall z₀ r) ε ∩ Icc T (2 * T)) ≤ ENNReal.ofReal (T ^ θ) := by
  set σ : ℝ := z₀.re - r with hσdef
  have hσ : 1 / 2 < σ := h0
  have hσ1 : σ ≤ 1 := by rw [hσdef]; linarith
  set g : ℝ := 1 - inghamHuxleyExponent σ * (1 - σ) with hg
  have hg0 : 0 < g := by rw [hg]; linarith [inghamHuxleyExponent_mul_lt_one hσ]
  set ε' : ℝ := min 1 g with hε'
  have hε'0 : 0 < ε' := lt_min one_pos hg0
  have hε'1 : ε' ≤ 1 := min_le_left _ _
  obtain ⟨C, hC, B, T₁, hT₁, hshadow⟩ :=
    exists_volume_zetaZeroShadow_le_inghamHuxley hσ hσ1 hε'0 hε'1
  set E : ℝ := (inghamHuxleyExponent σ + ε') * (1 - σ) with hE
  have hA := inghamHuxleyExponent_mem hσ
  have hE0 : 0 ≤ E := mul_nonneg (by linarith [hA.1]) (by linarith)
  have hE2 : E ≤ 2 := by rw [hE]; nlinarith [hA.2]
  have hEg : E ≤ 1 - g / 2 := by
    have hεg : ε' ≤ g := min_le_right _ _
    have h12 : 1 - σ ≤ 1 / 2 := by linarith
    have h0' : 0 ≤ 1 - σ := by linarith
    have : ε' * (1 - σ) ≤ g / 2 := by nlinarith
    rw [hE]; nlinarith
  set γ₀ : ℝ := z₀.im with hγ₀
  have hsub := zetaReturnSet_subset_shadow_of_lt_distance hr h1 (by linarith) hε
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow B (c := g / 4) (by positivity) (12 * 2 ^ B * C))
  refine ⟨1 - g / 4, by linarith, by linarith, max (max (2 * T₁) T₂) (max (2 * |γ₀|) 1),
    le_trans (le_max_right _ _) (le_max_right _ _), fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hTT₁ : 2 * T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTT₂ : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTγ : 2 * |γ₀| ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT0 : 0 < T := by linarith
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = C * (1 + Real.log (2 * T)) ^ B * (2 * T) ^ E := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hW]
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * T)
    positivity
  have hwin : ∀ a : ℝ, T / 2 ≤ a → a ≤ 2 * T →
      volume (zetaZeroShadow σ 2 ∩ Icc a (2 * a)) ≤ ENNReal.ofReal W := fun a ha1 ha2 =>
    hW ▸ volume_window_le_of_le hC hE0 hshadow hTT₁ (by linarith) ha1 ha2
  calc volume (zetaReturnSet (closedBall z₀ r) ε ∩ Icc T (2 * T))
      ≤ _ := volume_inter_Icc_le_three_windows hsub hTγ
    _ ≤ ENNReal.ofReal W + ENNReal.ofReal W + ENNReal.ofReal W :=
        add_le_add (add_le_add (hwin _ le_rfl (by linarith)) (hwin _ (by linarith) (by linarith)))
          (hwin _ (by linarith) le_rfl)
    _ = ENNReal.ofReal (3 * W) := by
        rw [← ENNReal.ofReal_add hW0 hW0, ← ENNReal.ofReal_add (by linarith) hW0]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (T ^ (1 - g / 4)) := by
        apply ENNReal.ofReal_le_ofReal
        have hW' := three_mul_window_bound_le (B := B) hC hE0 hE2 hT1
        rw [← hW] at hW'
        have habs := hT₂ T hTT₂
        have hsplit : T ^ (g / 4) * T ^ E = T ^ (g / 4 + E) := (Real.rpow_add hT0 _ _).symm
        have hfinal : T ^ (g / 4 + E) ≤ T ^ (1 - g / 4) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
        have hTE0 : 0 ≤ T ^ E := by positivity
        calc 3 * W ≤ 12 * 2 ^ B * C * (1 + Real.log T) ^ B * T ^ E := hW'
          _ ≤ T ^ (g / 4) * T ^ E := by gcongr
          _ = T ^ (g / 4 + E) := hsplit
          _ ≤ T ^ (1 - g / 4) := hfinal

/-! ## 5. Dyadic windows to prefixes -/

/-- **Dyadic windows to prefixes.**  A power-saving bound `|S ∩ [a, 2a]| ≤ a^θ'` on every dyadic
window with `a ≥ a₀` gives `|S ∩ [0, T]| ≤ T^θ` for every `θ > θ'` and all large `T`: a prefix
`[0, T]` is covered by `O(log T)` dyadic windows and one bounded initial piece. -/
theorem exists_forall_volume_inter_Icc_zero_le_rpow_of_window {S : Set ℝ} {θ' a₀ : ℝ}
    (hθ' : 0 ≤ θ') (ha₀ : 1 ≤ a₀)
    (hwin : ∀ a : ℝ, a₀ ≤ a → volume (S ∩ Icc a (2 * a)) ≤ ENNReal.ofReal (a ^ θ'))
    {θ : ℝ} (hθ : θ' < θ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → volume (S ∩ Icc 0 T) ≤ ENNReal.ofReal (T ^ θ) := by
  -- dyadic induction: `n` windows cover `[0, a₀ 2^n]`
  have hstep : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T → T ≤ a₀ * 2 ^ n →
      volume (S ∩ Icc 0 T) ≤ ENNReal.ofReal (2 * a₀ + n * T ^ θ') := by
    intro n
    induction n with
    | zero =>
      intro T hT0 hT
      calc volume (S ∩ Icc 0 T) ≤ volume (Icc 0 T) := measure_mono inter_subset_right
        _ = ENNReal.ofReal T := by rw [Real.volume_Icc, sub_zero]
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          simp only [pow_zero, mul_one] at hT
          simp only [Nat.cast_zero, zero_mul, add_zero]
          linarith
    | succ n ih =>
      intro T hT0 hT
      have hTθ : 0 ≤ T ^ θ' := Real.rpow_nonneg hT0 _
      by_cases hsmall : T ≤ a₀ * 2 ^ n
      · refine (ih T hT0 hsmall).trans (ENNReal.ofReal_le_ofReal ?_)
        push_cast
        nlinarith
      · push Not at hsmall
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          calc volume (S ∩ Icc 0 T) ≤ volume (Icc 0 T) := measure_mono inter_subset_right
            _ = ENNReal.ofReal T := by rw [Real.volume_Icc, sub_zero]
            _ ≤ _ := by
              apply ENNReal.ofReal_le_ofReal
              norm_num at hT ⊢
              linarith
        · have h2n : (2 : ℝ) ≤ 2 ^ n := by
            calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
              _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
          have hhalf : a₀ ≤ T / 2 := by
            have : a₀ * 2 ≤ a₀ * 2 ^ n := mul_le_mul_of_nonneg_left h2n (by linarith)
            linarith
          have hhalf' : T / 2 ≤ a₀ * 2 ^ n := by
            have : a₀ * 2 ^ (n + 1) = 2 * (a₀ * 2 ^ n) := by ring
            linarith
          have hsplit : S ∩ Icc 0 T ⊆ S ∩ Icc 0 (T / 2) ∪ S ∩ Icc (T / 2) (2 * (T / 2)) := by
            rw [← inter_union_distrib_left]
            refine inter_subset_inter_right _ fun x hx => ?_
            rcases le_total x (T / 2) with h | h
            · exact Or.inl ⟨hx.1, h⟩
            · exact Or.inr ⟨h, by linarith [hx.2]⟩
          have hmono : (T / 2) ^ θ' ≤ T ^ θ' :=
            Real.rpow_le_rpow (by positivity) (by linarith) hθ'
          calc volume (S ∩ Icc 0 T)
              ≤ volume (S ∩ Icc 0 (T / 2)) + volume (S ∩ Icc (T / 2) (2 * (T / 2))) :=
                (measure_mono hsplit).trans (measure_union_le _ _)
            _ ≤ ENNReal.ofReal (2 * a₀ + n * (T / 2) ^ θ') + ENNReal.ofReal ((T / 2) ^ θ') :=
                add_le_add (ih (T / 2) (by positivity) hhalf') (hwin (T / 2) hhalf)
            _ = ENNReal.ofReal (2 * a₀ + n * (T / 2) ^ θ' + (T / 2) ^ θ') := by
                rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            _ ≤ ENNReal.ofReal (2 * a₀ + (n + 1 : ℕ) * T ^ θ') := by
                apply ENNReal.ofReal_le_ofReal
                push_cast
                nlinarith
  -- the number of windows needed up to `T` is `O(log T)`
  have hcount : ∀ T : ℝ, 1 ≤ T →
      volume (S ∩ Icc 0 T) ≤ ENNReal.ofReal (2 * a₀ + 3 * (1 + Real.log T) * T ^ θ') := by
    intro T hT1
    set m : ℕ := ⌈T / a₀⌉₊ with hm
    set n : ℕ := Nat.log 2 m + 1 with hn
    have hm0 : m ≠ 0 := (Nat.ceil_pos.mpr (by positivity)).ne'
    have hTn : T ≤ a₀ * 2 ^ n := by
      have h1 : T / a₀ ≤ m := Nat.le_ceil _
      have h2 : (m : ℝ) < 2 ^ n := by
        have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
        rw [hn]
        exact_mod_cast this
      calc T = a₀ * (T / a₀) := by field_simp
        _ ≤ a₀ * m := by gcongr
        _ ≤ a₀ * 2 ^ n := by gcongr
    have hnlog : (n : ℝ) ≤ 3 * (1 + Real.log T) := by
      have hpow : (2 : ℝ) ^ (Nat.log 2 m) ≤ m := by exact_mod_cast Nat.pow_log_le_self 2 hm0
      have hmT : (m : ℝ) ≤ 2 * T := by
        have h1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ T / a₀)
        have h2 : T / a₀ ≤ T := div_le_self (by linarith) ha₀
        linarith
      have hlog : (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log (2 * T) := by
        have := Real.log_le_log (by positivity) hpow
        rw [Real.log_pow] at this
        exact this.trans (Real.log_le_log (by positivity) hmT)
      have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hlog2T : Real.log (2 * T) ≤ 1 + Real.log T := by
        rw [Real.log_mul (by norm_num) (by linarith)]
        linarith [Real.log_two_lt_d9]
      have hk : (Nat.log 2 m : ℝ) ≤ 2 * (1 + Real.log T) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 m)]
      have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
      rw [hn]
      push_cast
      linarith
    refine (hstep n T (by linarith) hTn).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ T ^ θ' := Real.rpow_nonneg (by linarith) _
    nlinarith
  -- absorb the logarithm into the gap `θ − θ'`
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 1 (c := θ - θ') (by linarith) 6)
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by linarith : 0 < θ)).eventually_ge_atTop (4 * a₀))
  refine ⟨max (max T₁ T₂) 1, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTT₂ : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  refine (hcount T hT1).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 := hT₁ T hTT₁
  have h2 := hT₂ T hTT₂
  have hsplitpow : T ^ (θ - θ') * T ^ θ' = T ^ θ := by
    rw [← Real.rpow_add (by linarith)]
    ring_nf
  have hTθ' : 0 ≤ T ^ θ' := by positivity
  rw [pow_one] at h1
  nlinarith [mul_le_mul_of_nonneg_right h1 hTθ']

/-- **Below the threshold the self-returns are power-saving rare.**  For `ε < d` there is `θ < 1`
with `|zetaReturnSet D ε ∩ [0, T]| ≤ T^θ` for all large `T`. -/
theorem exists_volume_zetaReturnSet_le_rpow_of_lt_distance {z₀ : ℂ} {r ε : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < z₀.re - r) (h1 : z₀.re + r < 1) (hε : ε < zetaNonvanishingDistance z₀ r) :
    ∃ θ : ℝ, θ < 1 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume (zetaReturnSet (closedBall z₀ r) ε ∩ Icc 0 T) ≤ ENNReal.ofReal (T ^ θ) := by
  obtain ⟨θ', hθ'0, hθ'1, T₁, hT₁, hwin⟩ :=
    exists_volume_zetaReturnSet_window_le_rpow_of_lt_distance hr h0 h1 hε
  obtain ⟨T₀, hT₀⟩ := exists_forall_volume_inter_Icc_zero_le_rpow_of_window hθ'0 hT₁ hwin
    (show θ' < (1 + θ') / 2 by linarith)
  exact ⟨(1 + θ') / 2, by linarith, T₀, hT₀⟩

end

end RHTower
