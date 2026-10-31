import GaloisForLFunctions.RHTower.Heat.HeatRepairFromLocalDepthAndCount
import GaloisForLFunctions.RHTower.Heat.TheHeatDetectionRateIsQuadraticInTheDepth
import GaloisForLFunctions.RHTower.XiSliceHeatLargeHeightPositivity
import GaloisForLFunctions.RHTower.Heat.HeatDetectionFromTheLocalZeroConfiguration
import GaloisForLFunctions.RHTower.XiSliceHeatRateInteriorLindelof
import GaloisForLFunctions.RHTower.XiSliceHeatNegativeFailure
import GaloisForLFunctions.RHTower.XiSliceHeatThresholdTouching
import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCriterion
import GaloisForLFunctions.RHTower.XiSliceCoeffDensity
import GaloisForLFunctions.RHTower.Heat.SizeOnlyRepairNearTheWeylFloor
import GaloisForLFunctions.RHTower.XiSliceHeatFromAbscissa

/-!
# The local heat threshold is depth squared over the local count

The **local heat threshold** at height `t` is

  `λ_t = inf{λ ≥ 0 : every T_n(λ, 0, t) is nonnegative}`        (`localHeatThreshold`),

the least heat that repairs the slice at that one height.  Heat positivity is closed upward in `λ`
(`xiSliceHeatTransfer_nonneg_of_le_of_forall`), and the global WD threshold is the supremum of the
local ones, `λ_WD = sup_t λ_t` (`wdHeatThreshold_eq_iSup_localHeatThreshold`).

**Theorem.**  Let `Ξ(t) ≠ 0`.
* **Lower bound** (`le_localHeatThreshold_of_offLine_zero`).  A zero `ρ` with `Re ρ > ½` and
  `Im ρ = t ≥ e^{1600}` gives `λ_t ≥ (Re ρ − ½)²/(200 log t)`.
* **Upper bound** (`localHeatThreshold_le_of_depth_count`).  If the zeros with `|Im ρ − t| < ½` have
  depth `≤ δ`, `R² ≥ 2δ²` and the radius-`R` head holds `N(t, R) ≥ 1` copies, then
  `λ_t ≤ 64R²/N(t, R)`; with an empty radius-`√2δ` head, `λ_t = 0`
  (`localHeatThreshold_eq_zero_of_depth`).

* **Support** (`localHeatThreshold_pos_iff`, any height).  `λ_t > 0` iff some unheated slice
  coefficient at `t` is negative; so `λ_{Im ρ} > 0` whenever `Re ρ > ½`
  (`localHeatThreshold_pos_of_offLine_zero`), and `λ_t = 0` on a set of heights of lower density
  `29/50` (`eventually_volume_localHeatThreshold_eq_zero_ge`).
* **Density** (`eventually_volume_localHeatThreshold_gt_le`).  For every `κ > 0` the heights in
  `[U/4 + 2, U/2 − 2]` with `λ_t > κ/log U` have measure `o(U)`.
* **Openness** (`lowerSemicontinuous_localHeatThreshold`, `isOpen_setOf_localHeatThreshold_pos`).
  `λ_t`
  is lower semicontinuous in `t`, so the failure set `{t : λ_t > 0}` is open; it is null iff RH
  (`riemannHypothesis_iff_volume_setOf_localHeatThreshold_pos_eq_zero`).
* **Cone-defect bound** (`localHeatThreshold_le_of_cone`, any `t`).  If every zero satisfies
  `(Im z)² ≤ (Re z − t)² + 3λ`, then `λ_t ≤ λ`; so `λ_t > 0` only if some zero lies strictly inside
  its depth cone, `|Re z − t| < |Im z|` (`exists_inside_cone_of_localHeatThreshold_pos`).

So `λ_t` is `≍ depth²/(local count)` at every height: `≍ δ/log t` for regularly spaced zeros and
`≍ δ²/log t` for a cluster of `≍ log t` zeros within `O(δ)`.  When every zero within `½` of `t` is
critical, `δ = 0` and `λ_t = 0`.  When the zero-growth functional at an off-line zero is regular,
`Ψ_{t,r}(ρ) ≤ c log t · ρ + bδ log t`, the lower bound is linear: `λ_t ≥ δ/(3000(b + c + 1) log t)`
(`le_localHeatThreshold_of_zeroGrowth`), and so is the bound for the de Bruijn–Newman constant
(`le_newmanConstant_of_zeroGrowth`).  With size repair, `λ_t log t ≤ 2/3 + ε` at large heights for
every `ε > 0`
(`exists_localHeatThreshold_mul_log_le_two_thirds_add`), and `≤ 67/100` with explicit constants, so
every
off-line zero high enough satisfies `(Re ρ − ½)²/200 ≤ λ_{Im ρ} log Im ρ ≤ 67/100`
(`exists_heat_pincer`).
-/

open Complex Filter Topology Polynomial
open scoped ComplexOrder
open GaloisForLFunctions.ArithmeticLocalDivisorGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- The heats `λ ≥ 0` at which every heated slice coefficient at height `t` is nonnegative. -/
def localHeatAdmissible (t : ℝ) : Set ℝ :=
  {lam | 0 ≤ lam ∧ ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam 0 t n}

/-- **The local heat threshold** `λ_t = inf localHeatAdmissible t`. -/
def localHeatThreshold (t : ℝ) : ℝ := sInf (localHeatAdmissible t)

theorem eighth_mem_localHeatAdmissible (t : ℝ) : (1 / 8 : ℝ) ∈ localHeatAdmissible t :=
  ⟨by norm_num, fun n => (xiSliceHeatTransfer_nonneg le_rfl t n).2⟩

theorem localHeatAdmissible_nonempty (t : ℝ) : (localHeatAdmissible t).Nonempty :=
  ⟨_, eighth_mem_localHeatAdmissible t⟩

theorem localHeatAdmissible_bddBelow (t : ℝ) : BddBelow (localHeatAdmissible t) :=
  ⟨0, fun _ h => h.1⟩

theorem localHeatThreshold_nonneg (t : ℝ) : 0 ≤ localHeatThreshold t :=
  le_csInf (localHeatAdmissible_nonempty t) fun _ h => h.1

theorem localHeatThreshold_le {t lam : ℝ} (h : lam ∈ localHeatAdmissible t) :
    localHeatThreshold t ≤ lam :=
  csInf_le (localHeatAdmissible_bddBelow t) h

/-- The local threshold is at most the global WD threshold. -/
theorem localHeatThreshold_le_wdHeatThreshold (t : ℝ) : localHeatThreshold t ≤ wdHeatThreshold := by
  refine le_of_forall_gt_imp_ge_of_dense fun lam hlam => localHeatThreshold_le ⟨?_, ?_⟩
  · exact wdHeatThreshold_nonneg.trans hlam.le
  · exact fun n => mem_wdHeatAdmissible_of_lt hlam t n

/-- Every heat above the local threshold is admissible at that height. -/
theorem mem_localHeatAdmissible_of_lt {t lam : ℝ} (h : localHeatThreshold t < lam) :
    lam ∈ localHeatAdmissible t := by
  obtain ⟨s, hs, hslt⟩ := (csInf_lt_iff (localHeatAdmissible_bddBelow t)
    (localHeatAdmissible_nonempty t)).mp h
  exact ⟨hs.1.trans hslt.le, fun n => xiSliceHeatTransfer_nonneg_of_le_of_forall hslt.le hs.2 n⟩

/-- **The global threshold is the supremum of the local ones**: `λ_WD = sup_t λ_t`. -/
theorem wdHeatThreshold_eq_iSup_localHeatThreshold :
    wdHeatThreshold = ⨆ t : ℝ, localHeatThreshold t := by
  have hbdd : BddAbove (Set.range localHeatThreshold) :=
    ⟨wdHeatThreshold, by rintro _ ⟨t, rfl⟩; exact localHeatThreshold_le_wdHeatThreshold t⟩
  refine le_antisymm ?_ (ciSup_le localHeatThreshold_le_wdHeatThreshold)
  refine le_of_forall_gt_imp_ge_of_dense fun lam hlam => ?_
  refine csInf_le wdHeatAdmissible_bddBelow fun t n => ?_
  exact (mem_localHeatAdmissible_of_lt ((le_ciSup hbdd t).trans_lt hlam)).2 n

/-- **Lower bound.**  A zero `ρ` with `Re ρ > ½` and `Im ρ ≥ e^{1600}` gives
`λ_{Im ρ} ≥ (Re ρ − ½)²/(200 log Im ρ)`. -/
theorem le_localHeatThreshold_of_offLine_zero {ρ : ℂ} (hρ : xi ρ = 0) (hre : 1 / 2 < ρ.re)
    (hγ : Real.exp 1600 ≤ ρ.im) :
    (ρ.re - 1 / 2) ^ 2 / 200 / Real.log ρ.im ≤ localHeatThreshold ρ.im := by
  set r := (ρ.re - 1 / 2) ^ 2 / 200 with hr
  have hδ0 : 0 < ρ.re - 1 / 2 := by linarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hL : 0 < Real.log ρ.im :=
    Real.log_pos (lt_of_lt_of_le (by have := Real.add_one_le_exp (1600 : ℝ); linarith) hγ)
  refine le_csInf (localHeatAdmissible_nonempty _) fun lam hlam => ?_
  by_contra hlt
  push Not at hlt
  set lam' := max lam (r / (2 * Real.log ρ.im)) with hlam'
  have hlam'0 : 0 < lam' := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hlam'lt : lam' < r / Real.log ρ.im := by
    refine max_lt hlt ?_
    rw [div_lt_div_iff₀ (by positivity) hL]; nlinarith
  have hpos : ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam' 0 ρ.im n :=
    xiSliceHeatTransfer_nonneg_of_le_of_forall (le_max_left _ _) hlam.2
  set κ := lam' * Real.log ρ.im with hκ
  have hκ0 : 0 < κ := by positivity
  have hκle : κ ≤ (ρ.re - 1 / 2) ^ 2 / 200 := by
    rw [hκ]; rw [lt_div_iff₀ hL] at hlam'lt; linarith
  obtain ⟨n, hn⟩ := RHTower.re_xiSliceHeatTransfer_neg_of_slice_zero_quadratic hγ hδ0
    (RHTower.xiSliceReal_offset_eq_zero hρ) hκ0 hκle
  rw [show κ / Real.log ρ.im = lam' by rw [hκ]; field_simp] at hn
  exact absurd (Complex.nonneg_iff.mp (hpos n)).1 (not_le.mpr hn)

/-- **Upper bound.**  If `Ξ(t) ≠ 0`, every zero copy with `|Re z − t| < ½` has `(Im z)² ≤ δ²`,
`0 ≤ R`, `2δ² ≤ R²` and the radius-`R` head is nonempty, then `λ_t ≤ 64R²/N(t, R)`. -/
theorem localHeatThreshold_le_of_depth_count {t R δ : ℝ} (ht : XiC t ≠ 0) (hR : 0 ≤ R)
    (hδR : 2 * δ ^ 2 ≤ R ^ 2)
    (hdepth : ∀ q : XiZeroCopy, |(xiSpectralPoint q).re - t| < 1 / 2 →
      (xiSpectralPoint q).im ^ 2 ≤ δ ^ 2)
    (hcard : 0 < (xiSliceGaussianRadiusHead t R).card) :
    localHeatThreshold t ≤ 64 * R ^ 2 / (xiSliceGaussianRadiusHead t R).card := by
  have hN : (0 : ℝ) < (xiSliceGaussianRadiusHead t R).card := by exact_mod_cast hcard
  have hR0 : 0 < R := by
    rcases eq_or_lt_of_le hR with h0 | h0
    · exfalso
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hcard
      rw [mem_xiSliceGaussianRadiusHead, ← h0] at hq
      exact xiSpectralPoint_ne_ofReal ht q (sub_eq_zero.mp (norm_le_zero_iff.mp hq))
    · exact h0
  refine localHeatThreshold_le ⟨by positivity, fun n => ?_⟩
  refine xiSliceHeatTransfer_nonneg_of_depth_count (by positivity) ht hR hδR hdepth ?_ n
  rw [div_mul_cancel₀ _ hN.ne']

/-- **Empty head.**  If `Ξ(t) ≠ 0`, the zero copies with `|Re z − t| < ½` have `(Im z)² ≤ δ²` and no
copy lies within `√2 δ` of `t`, then `λ_t = 0`. -/
theorem localHeatThreshold_eq_zero_of_depth {t δ : ℝ} (hδ : 0 ≤ δ)
    (hdepth : ∀ q : XiZeroCopy, |(xiSpectralPoint q).re - t| < 1 / 2 →
      (xiSpectralPoint q).im ^ 2 ≤ δ ^ 2)
    (hempty : xiSliceGaussianRadiusHead t (Real.sqrt 2 * δ) = ∅) :
    localHeatThreshold t = 0 := by
  have hR2 : (Real.sqrt 2 * δ) ^ 2 = 2 * δ ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
  refine le_antisymm (localHeatThreshold_le ⟨le_rfl, fun n => ?_⟩) (localHeatThreshold_nonneg t)
  refine xiSliceHeatTransfer_nonneg_of_heatedCone_all le_rfl (fun q => ?_) n
  have hq : q ∉ xiSliceGaussianRadiusHead t (Real.sqrt 2 * δ) := by rw [hempty]; simp
  have h := im_sq_le_of_not_mem_radiusHead_of_depth (by positivity) hR2.ge hdepth hq
  linarith

/-- **The local heat threshold is lower semicontinuous in the height.**  A heat `λ₁ < λ_t` fails at
`t` in some order `n`; the failure `Re T_n(λ₁, 0, ·) < 0` is open in the height, and positivity is
closed upward in `λ`. -/
theorem lowerSemicontinuous_localHeatThreshold : LowerSemicontinuous localHeatThreshold := by
  intro t y hy
  rcases lt_or_ge y 0 with hy0 | hy0
  · exact Filter.Eventually.of_forall fun t' => lt_of_lt_of_le hy0 (localHeatThreshold_nonneg t')
  obtain ⟨l₁, hyl, hlt⟩ := exists_between hy
  have hl₁0 : 0 ≤ l₁ := hy0.trans hyl.le
  have hfail : ∃ n, (xiSliceHeatTransfer l₁ 0 t n).re < 0 := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have hmem : l₁ ∈ localHeatAdmissible t := ⟨hl₁0, fun n =>
      Complex.nonneg_iff.mpr ⟨h n, (xiSliceHeatTransfer_im_eq_zero hl₁0 t n).symm⟩⟩
    exact absurd (localHeatThreshold_le hmem) (not_le.mpr hlt)
  obtain ⟨n, hn⟩ := hfail
  have hcont : Continuous fun t' => (xiSliceHeatTransfer l₁ 0 t' n).re :=
    Complex.continuous_re.comp (continuous_xiSliceHeatTransfer hl₁0 0 n)
  filter_upwards [(hcont.tendsto t).eventually (gt_mem_nhds hn)] with t' ht'
  refine lt_of_lt_of_le hyl (le_csInf (localHeatAdmissible_nonempty t') fun lam hlam => ?_)
  by_contra hle
  simp only [not_le] at hle
  have h1 := xiSliceHeatTransfer_nonneg_of_le_of_forall hle.le hlam.2 n
  have h2 := (Complex.nonneg_iff.mp h1).1
  linarith

/-- **The heat failure set `{t : λ_t > 0}` is open.** -/
theorem isOpen_setOf_localHeatThreshold_pos : IsOpen {t : ℝ | 0 < localHeatThreshold t} :=
  lowerSemicontinuous_localHeatThreshold.isOpen_preimage 0

/-- **RH iff the heat failure set is null.**  The set `{t : λ_t > 0}` is open, so it is null only
when empty, and then `λ_WD = sup_t λ_t = 0`. -/
theorem riemannHypothesis_iff_volume_setOf_localHeatThreshold_pos_eq_zero :
    RiemannHypothesis ↔ MeasureTheory.volume {t : ℝ | 0 < localHeatThreshold t} = 0 := by
  constructor
  · intro hRH
    have h0 := riemannHypothesis_iff_wdHeatThreshold_eq_zero.mp hRH
    have hempty : {t : ℝ | 0 < localHeatThreshold t} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact h0 ▸ localHeatThreshold_le_wdHeatThreshold t
    rw [hempty, MeasureTheory.measure_empty]
  · intro hvol
    have hempty := (isOpen_setOf_localHeatThreshold_pos.measure_eq_zero_iff
      MeasureTheory.volume).mp hvol
    refine riemannHypothesis_iff_wdHeatThreshold_eq_zero.mpr (le_antisymm ?_ wdHeatThreshold_nonneg)
    rw [wdHeatThreshold_eq_iSup_localHeatThreshold]
    refine ciSup_le fun t => ?_
    by_contra h
    have : t ∈ {t : ℝ | 0 < localHeatThreshold t} := not_le.mp h
    rw [hempty] at this
    exact this

/-- **The cone-defect bound.**  If every zero satisfies `(Im z)² ≤ (Re z − t)² + 3λ` with `λ ≥ 0`,
then `λ_t ≤ λ`.  So `λ_t ≤ (1/3) sup_z ((Im z)² − (Re z − t)²)₊`, with no count. -/
theorem localHeatThreshold_le_of_cone {t lam : ℝ} (hlam : 0 ≤ lam)
    (hcone : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + 3 * lam) :
    localHeatThreshold t ≤ lam :=
  localHeatThreshold_le ⟨hlam, fun n => xiSliceHeatTransfer_nonneg_of_heatedCone_all hlam hcone n⟩

/-- **The support of the local heat threshold.**  If `λ_t > 0`, some zero lies strictly inside its
depth cone at `t`: `(Re z − t)² < (Im z)²`. -/
theorem exists_inside_cone_of_localHeatThreshold_pos {t : ℝ} (h : 0 < localHeatThreshold t) :
    ∃ q : XiZeroCopy, ((xiSpectralPoint q).re - t) ^ 2 < (xiSpectralPoint q).im ^ 2 := by
  by_contra hne
  simp only [not_exists, not_lt] at hne
  have := localHeatThreshold_le_of_cone (t := t) le_rfl fun q => by linarith [hne q]
  linarith

/-- At an off-line ordinate some unheated slice coefficient is negative: the slice vanishes at the
depth `δ > 0`, and a power series with nonnegative coefficients that vanishes at `δ` is zero. -/
theorem exists_re_xiSliceCoeff_neg_of_offLine_zero {ρ : ℂ} (hρ : xi ρ = 0) (hre : 1 / 2 < ρ.re) :
    ∃ n : ℕ, (xiSliceCoeff ρ.im n).re < 0 := by
  by_contra hall
  simp only [not_exists, not_lt] at hall
  have hδ0 : 0 < ρ.re - 1 / 2 := by linarith
  have hzero : xiSliceProduct ρ.im ((ρ.re - 1 / 2 : ℝ) : ℂ) = 0 := by
    unfold xiSliceProduct
    have e : (1 : ℂ) / 2 + ((ρ.re - 1 / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I = ρ := by
      apply Complex.ext <;> simp
    rw [e, hρ, zero_mul]
  have hnn : ∀ n, 0 ≤ xiSliceCoeff ρ.im n * ((ρ.re - 1 / 2 : ℝ) : ℂ) ^ n := fun n => by
    have h1 : 0 ≤ xiSliceCoeff ρ.im n :=
      Complex.nonneg_iff.mpr ⟨hall n, (xiSliceCoeff_im_eq_zero ρ.im n).symm⟩
    have h2 : (0 : ℂ) ≤ ((ρ.re - 1 / 2 : ℝ) : ℂ) ^ n := by
      rw [← Complex.ofReal_pow]; exact Complex.zero_le_real.mpr (pow_nonneg hδ0.le n)
    exact mul_nonneg h1 h2
  have hsum := hasSum_xiSliceCoeff ρ.im ((ρ.re - 1 / 2 : ℝ) : ℂ)
  rw [hzero] at hsum
  have hall0 := (hasSum_zero_iff_of_nonneg hnn).mp hsum
  have hc0 : ∀ n, xiSliceCoeff ρ.im n = 0 := fun n => by
    have h := congrFun hall0 n
    simp only [Pi.zero_apply, mul_eq_zero] at h
    rcases h with h | h
    · exact h
    · exact absurd (pow_eq_zero_iff'.mp h).1 (by exact_mod_cast hδ0.ne')
  have hs := hasSum_xiSliceCoeff ρ.im (3 / 2 - ρ.im * I)
  simp only [hc0, zero_mul] at hs
  exact xiSliceProduct_ne_zero ρ.im (hs.unique hasSum_zero)

/-- A negative unheated coefficient at `t` gives `λ_t > 0`: by continuity of `T_n(λ, 0, t)` in `λ`
it stays negative for small heat. -/
theorem localHeatThreshold_pos_of_re_xiSliceCoeff_neg {t : ℝ} {n : ℕ}
    (hn : (xiSliceCoeff t n).re < 0) : 0 < localHeatThreshold t := by
  have hcont : Continuous fun lam : ℝ => (xiSliceHeatTransfer lam 0 t n).re :=
    Complex.continuous_re.comp ((continuous_xiSliceHeatTransfer_joint 0 n).comp
      (continuous_id.prodMk continuous_const))
  have h0 : (xiSliceHeatTransfer 0 0 t n).re < 0 := by rw [xiSliceHeatTransfer_zero_eq]; exact hn
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_lt hcont continuous_const) 0 h0
  refine lt_of_lt_of_le (half_pos hε)
    (le_csInf (localHeatAdmissible_nonempty t) fun lam hlam => ?_)
  by_contra hlt
  simp only [not_le] at hlt
  have hmem : lam ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hlam.1]; linarith
  have hneg : (xiSliceHeatTransfer lam 0 t n).re < 0 := hball hmem
  have := (Complex.nonneg_iff.mp (hlam.2 n)).1
  linarith

/-- **The heat failure set is the unheated failure set**: `λ_t > 0` iff some slice coefficient at
`t` is negative. -/
theorem localHeatThreshold_pos_iff (t : ℝ) :
    0 < localHeatThreshold t ↔ ∃ n : ℕ, (xiSliceCoeff t n).re < 0 := by
  refine ⟨fun h => ?_, fun ⟨n, hn⟩ => localHeatThreshold_pos_of_re_xiSliceCoeff_neg hn⟩
  by_contra hne
  simp only [not_exists, not_lt] at hne
  have hmem : (0 : ℝ) ∈ localHeatAdmissible t := ⟨le_rfl, fun n => by
    rw [xiSliceHeatTransfer_zero_eq]
    exact Complex.nonneg_iff.mpr ⟨hne n, (xiSliceCoeff_im_eq_zero t n).symm⟩⟩
  linarith [localHeatThreshold_le hmem]

/-- **Every off-line ordinate has a positive local heat threshold**, at every height:
`λ_{Im ρ} > 0` for every zero with `Re ρ > ½`. -/
theorem localHeatThreshold_pos_of_offLine_zero {ρ : ℂ} (hρ : xi ρ = 0) (hre : 1 / 2 < ρ.re) :
    0 < localHeatThreshold ρ.im :=
  let ⟨_, hn⟩ := exists_re_xiSliceCoeff_neg_of_offLine_zero hρ hre
  localHeatThreshold_pos_of_re_xiSliceCoeff_neg hn

/-- **The local heat threshold vanishes on more than half of the heights**: eventually
`vol{t ∈ [0, V] : λ_t = 0} ≥ (29/50) V − 21/100`. -/
theorem eventually_volume_localHeatThreshold_eq_zero_ge :
    ∀ᶠ V in atTop, ENNReal.ofReal (29 / 50 * V - 21 / 100) ≤
      MeasureTheory.volume {t ∈ Set.Icc (0 : ℝ) V | localHeatThreshold t = 0} := by
  filter_upwards [eventually_volume_sliceCoeff_nonneg_ge] with V hV
  refine hV.trans (MeasureTheory.measure_mono fun t ht => ⟨ht.1, ?_⟩)
  refine le_antisymm (not_lt.mp fun h => ?_) (localHeatThreshold_nonneg t)
  obtain ⟨n, hn⟩ := (localHeatThreshold_pos_iff t).mp h
  exact absurd (Complex.nonneg_iff.mp (ht.2 n)).1 (not_le.mpr hn)

/-- **Linear lower bound for a regular configuration.**  Let `ρ` be a zero with `Re ρ > ½`,
`t = Im ρ ≥ e^{16}`, `Ξ(t) ≠ 0`, `δ = Re ρ − ½`, `δ log t ≥ 1`, and `δ/8 ≤ r ≤ δ/4` with
`f_t(r) ≠ 0`.  If `Ψ_{t,r}(ρ') ≤ c log t · ρ' + bδ log t` on `[0, 3/2]` (`c ≥ 2`, `b ≥ 0`), then
`λ_t ≥ δ/(3000(b + c + 1) log t)`, hence `Λ ≥ λ_WD ≥ δ/(3000(b + c + 1) log t)`. -/
theorem le_localHeatThreshold_of_zeroGrowth {ρ : ℂ} (hρ : xi ρ = 0) (hre : 1 / 2 < ρ.re)
    (ht16 : Real.exp 16 ≤ ρ.im) (hΞ : XiC ρ.im ≠ 0) (hδL : 1 ≤ (ρ.re - 1 / 2) * Real.log ρ.im)
    {r b c : ℝ} (hr8 : (ρ.re - 1 / 2) / 8 ≤ r) (hr4 : 4 * r ≤ ρ.re - 1 / 2)
    (hfr : RHTower.xiSliceReal ρ.im r ≠ 0) (hc : 2 ≤ c) (hb : 0 ≤ b)
    (hΨ : ∀ y : ℝ, 0 ≤ y → y ≤ 3 / 2 → RHTower.zeroGrowthSum ρ.im r y
      ≤ c * Real.log ρ.im * y + b * (ρ.re - 1 / 2) * Real.log ρ.im) :
    (ρ.re - 1 / 2) / (3000 * (b + c + 1)) / Real.log ρ.im ≤ localHeatThreshold ρ.im := by
  set δ := ρ.re - 1 / 2 with hδ
  set rate := δ / (3000 * (b + c + 1)) with hrate
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hrate0 : 0 < rate := by rw [hrate]; positivity
  have hL : 0 < Real.log ρ.im := Real.log_pos (lt_of_lt_of_le
    (by have := Real.add_one_le_exp (16 : ℝ); linarith) ht16)
  refine le_csInf (localHeatAdmissible_nonempty _) fun lam hlam => ?_
  by_contra hlt
  push Not at hlt
  set lam' := max lam (rate / (2 * Real.log ρ.im)) with hlam'
  have hlam'0 : 0 < lam' := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hlam'lt : lam' < rate / Real.log ρ.im := by
    refine max_lt hlt ?_
    rw [div_lt_div_iff₀ (by positivity) hL]; nlinarith
  have hpos : ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam' 0 ρ.im n :=
    xiSliceHeatTransfer_nonneg_of_le_of_forall (le_max_left _ _) hlam.2
  set κ := lam' * Real.log ρ.im with hκ
  have hκ0 : 0 < κ := by positivity
  have hκle : κ ≤ δ / (3000 * (b + c + 1)) := by
    rw [hκ]; rw [lt_div_iff₀ hL] at hlam'lt; rw [← hrate]; linarith
  obtain ⟨n, hn⟩ := RHTower.re_xiSliceHeatTransfer_neg_of_zeroGrowth_linear ht16 hΞ hδ0
    (RHTower.xiSliceReal_offset_eq_zero hρ) hδL hr8 hr4 hfr hc hb hΨ hκ0 hκle
  rw [show κ / Real.log ρ.im = lam' by rw [hκ]; field_simp] at hn
  exact absurd (Complex.nonneg_iff.mp (hpos n)).1 (not_le.mpr hn)

/-- The same bound for the de Bruijn–Newman constant. -/
theorem le_newmanConstant_of_zeroGrowth {ρ : ℂ} (hρ : xi ρ = 0) (hre : 1 / 2 < ρ.re)
    (ht16 : Real.exp 16 ≤ ρ.im) (hΞ : XiC ρ.im ≠ 0) (hδL : 1 ≤ (ρ.re - 1 / 2) * Real.log ρ.im)
    {r b c : ℝ} (hr8 : (ρ.re - 1 / 2) / 8 ≤ r) (hr4 : 4 * r ≤ ρ.re - 1 / 2)
    (hfr : RHTower.xiSliceReal ρ.im r ≠ 0) (hc : 2 ≤ c) (hb : 0 ≤ b)
    (hΨ : ∀ y : ℝ, 0 ≤ y → y ≤ 3 / 2 → RHTower.zeroGrowthSum ρ.im r y
      ≤ c * Real.log ρ.im * y + b * (ρ.re - 1 / 2) * Real.log ρ.im) :
    (ρ.re - 1 / 2) / (3000 * (b + c + 1)) / Real.log ρ.im ≤ newmanConstant :=
  ((le_localHeatThreshold_of_zeroGrowth hρ hre ht16 hΞ hδL hr8 hr4 hfr hc hb hΨ).trans
    (localHeatThreshold_le_wdHeatThreshold _)).trans wdHeatThreshold_le_newmanConstant

/-- **Size repair.**  For `|t| ≥ t₀`, `λ_t log |t| ≤ 67/100`
(`exists_xiSliceHeatTransfer_pos_heat_weylFloor`). -/
theorem exists_localHeatThreshold_mul_log_le :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ |t| → localHeatThreshold t * Real.log |t| ≤ 67 / 100 := by
  obtain ⟨t₀, ht₀, hpos⟩ := exists_xiSliceHeatTransfer_pos_heat_weylFloor
  refine ⟨t₀, ht₀, fun t ht => ?_⟩
  have hL : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hlam : 0 ≤ (67 / 100) / Real.log |t| := by positivity
  have hadm : (67 / 100) / Real.log |t| ∈ localHeatAdmissible t := by
    refine ⟨hlam, fun n => ?_⟩
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact (hpos t ht _ le_rfl m).le
    · rw [xiSliceHeatTransfer_odd_eq_zero hlam]
  have h := localHeatThreshold_le hadm
  rw [le_div_iff₀ hL] at h
  exact h

/-- **The local heat rate vanishes in density.**  For every `κ > 0` and `ε > 0`, eventually the
heights `t ∈ [U/4 + 2, U/2 − 2]` with `λ_t > κ/log U` have measure `≤ εU`.  A heat `κ/log U` that
fails at `t` fails in an even order, and `κ/log U ≥ 100(c/log U)²` once `log U ≥ 100c²/κ`
(`eventually_volume_xiSliceHeatTransfer_fail_le`). -/
theorem eventually_volume_localHeatThreshold_gt_le {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∀ᶠ U in atTop, MeasureTheory.volume {t ∈ Set.Icc (U / 4 + 2) (U / 2 - 2) |
      κ / Real.log U < localHeatThreshold t} ≤ ENNReal.ofReal (ε * U) := by
  obtain ⟨c, hc, hfail⟩ := eventually_volume_xiSliceHeatTransfer_fail_le hε
  filter_upwards [hfail,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (100 * c ^ 2 / κ + 1))]
    with U hU hlogU
  refine le_trans (MeasureTheory.measure_mono ?_) hU
  intro t ht
  refine ⟨ht.1, ?_⟩
  have hL : 0 < Real.log U := lt_of_lt_of_le (by positivity) hlogU
  have hlam0 : 0 < κ / Real.log U := by positivity
  refine ⟨κ / Real.log U, hlam0, ?_, ?_⟩
  · rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) hL]
    have h1 : 100 * c ^ 2 ≤ κ * Real.log U := by
      have : 100 * c ^ 2 / κ ≤ Real.log U := by linarith
      rw [div_le_iff₀ hκ] at this
      linarith
    nlinarith
  · by_contra hall
    simp only [not_exists, not_not] at hall
    have hmem : κ / Real.log U ∈ localHeatAdmissible t := ⟨hlam0.le, fun n => by
      obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
      · exact hall m
      · rw [xiSliceHeatTransfer_odd_eq_zero hlam0.le]⟩
    exact absurd (localHeatThreshold_le hmem) (not_le.mpr ht.2)

/-- **Size repair at the Weyl floor.**  For every `ε > 0`, `λ_t log |t| ≤ 2/3 + ε` for all large
`|t|` (`exists_xiSliceHeatTransfer_pos_heat_two_thirds_add`). -/
theorem exists_localHeatThreshold_mul_log_le_two_thirds_add {ε : ℝ} (hε : 0 < ε) :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ |t| →
      localHeatThreshold t * Real.log |t| ≤ 2 / 3 + ε := by
  obtain ⟨t₀, ht₀, hpos⟩ := exists_xiSliceHeatTransfer_pos_heat_two_thirds_add hε
  refine ⟨t₀, ht₀, fun t ht => ?_⟩
  have hL : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hlam : 0 ≤ (2 / 3 + ε) / Real.log |t| := by positivity
  have hadm : (2 / 3 + ε) / Real.log |t| ∈ localHeatAdmissible t := by
    refine ⟨hlam, fun n => ?_⟩
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact (hpos t ht _ le_rfl m).le
    · rw [xiSliceHeatTransfer_odd_eq_zero hlam]
  have h := localHeatThreshold_le hadm
  rw [le_div_iff₀ hL] at h
  exact h

/-- **The heat pincer at one height.**  There is `t₁` such that every zero `ρ` with `Re ρ > ½` and
`Im ρ ≥ t₁` satisfies `(Re ρ − ½)²/200 ≤ λ_{Im ρ} log Im ρ ≤ 67/100`. -/
theorem exists_heat_pincer :
    ∃ t₁ : ℝ, ∀ ρ : ℂ, xi ρ = 0 → 1 / 2 < ρ.re → t₁ ≤ ρ.im →
      (ρ.re - 1 / 2) ^ 2 / 200 ≤ localHeatThreshold ρ.im * Real.log ρ.im ∧
        localHeatThreshold ρ.im * Real.log ρ.im ≤ 67 / 100 := by
  obtain ⟨t₀, ht₀, hsize⟩ := exists_localHeatThreshold_mul_log_le
  refine ⟨max t₀ (Real.exp 1600), fun ρ hρ hre hγ => ⟨?_, ?_⟩⟩
  · have hγ' : Real.exp 1600 ≤ ρ.im := le_trans (le_max_right _ _) hγ
    have hL : 0 < Real.log ρ.im := Real.log_pos (lt_of_lt_of_le
      (by have := Real.add_one_le_exp (1600 : ℝ); linarith) hγ')
    have h := le_localHeatThreshold_of_offLine_zero hρ hre hγ'
    rwa [div_le_iff₀ hL] at h
  · have h0 : 0 ≤ ρ.im := le_trans (le_trans (by linarith) (le_max_left _ _)) hγ
    have h := hsize ρ.im (by rw [abs_of_nonneg h0]; exact le_trans (le_max_left _ _) hγ)
    rwa [abs_of_nonneg h0] at h

end

end RHTower.DeBruijn

