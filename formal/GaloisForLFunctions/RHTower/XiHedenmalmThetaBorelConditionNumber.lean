import GaloisForLFunctions.RHTower.XiHedenmalmThetaBorelHolonomy

/-!
# Exact condition number of the Borel holonomy on a finite window

Multiplication by the dilation character `M α` on `L²((0,T), b x dt)` has essential operator data
governed by the two essential suprema of `‖M α‖` and `‖M (-α)‖`.  Because the source density
`b x` is strictly positive, every nonempty relatively open subset of the window carries positive
mass, so these essential suprema are the genuine endpoint values of the radial power.

The resulting two-sided condition number is exactly

`(1 + T) ^ (|Im α| / 2)`,

and at the geometric samples `1 + t = r ^ (2 j)` it is `r ^ (j |Im α|)`, i.e. the `j`-th power of the
horizontal displacement of the centered zero.  It equals one exactly on the critical line.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace RHTower

/-! ## The positive Borel source measure -/

/-- The Borel source measure of the theta right tail based at `x`. -/
def hedenmalmBorelWeight (x : ℝ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal (hedenmalmBorelDensity x t)

theorem measurable_hedenmalmBorelChart : Measurable hedenmalmBorelChart := by
  unfold hedenmalmBorelChart
  exact (Real.measurable_log.comp (measurable_const.add measurable_id)).div_const 2

theorem measurable_hedenmalmBorelDensity (x : ℝ) :
    Measurable (hedenmalmBorelDensity x) := by
  unfold hedenmalmBorelDensity
  exact
    (contDiff_thetaCuspFullSource.continuous.measurable.comp
        (measurable_const.add measurable_hedenmalmBorelChart)).div
      (measurable_const.mul (measurable_const.add measurable_id))

theorem measurable_ofReal_hedenmalmBorelDensity (x : ℝ) :
    Measurable fun t => ENNReal.ofReal (hedenmalmBorelDensity x t) :=
  ENNReal.measurable_ofReal.comp (measurable_hedenmalmBorelDensity x)

/-- **Full support of the Borel source measure.**  Strict positivity of the theta tail gives every
nonempty open subset of the Borel ray positive source mass. -/
theorem hedenmalmBorelWeight_ne_zero_of_isOpen {x : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hne : U.Nonempty) (hsub : U ⊆ Ioi (-1 : ℝ)) :
    hedenmalmBorelWeight x U ≠ 0 := by
  rw [hedenmalmBorelWeight, withDensity_apply _ hU.measurableSet]
  intro hzero
  rw [lintegral_eq_zero_iff (measurable_ofReal_hedenmalmBorelDensity x)] at hzero
  rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet] at hzero
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ U := by
    filter_upwards [hzero] with t ht
    intro htU
    have hpos := hedenmalmBorelDensity_pos x (mem_Ioi.mp (hsub htU))
    have : hedenmalmBorelDensity x t ≤ 0 := ENNReal.ofReal_eq_zero.mp (ht htU)
    linarith
  rw [ae_iff] at hae
  simp only [not_not, Set.setOf_mem_eq] at hae
  exact (ne_of_gt (hU.measure_pos volume hne)) hae

/-- A two-sided characterization of an essential supremum. -/
theorem essSup_eq_of_ae_le_of_forall_lt {μ : Measure ℝ} {f : ℝ → ℝ≥0∞} {c : ℝ≥0∞}
    (hle : ∀ᵐ t ∂μ, f t ≤ c) (hlt : ∀ b, b < c → μ {t | b < f t} ≠ 0) :
    essSup f μ = c := by
  refine le_antisymm (essSup_le_of_ae_le c hle) ?_
  by_contra hcon
  exact hlt _ (not_le.mp hcon) meas_essSup_lt

/-! ## The exact window essential supremum -/

private theorem essSup_rpow_window (x : ℝ) {T : ℝ} (hT : 0 < T) (e : ℝ) :
    essSup (fun t => ENNReal.ofReal ((1 + t) ^ e))
        ((hedenmalmBorelWeight x).restrict (Ioo 0 T)) =
      ENNReal.ofReal (max 1 ((1 + T) ^ e)) := by
  have hT1 : (1 : ℝ) ≤ 1 + T := by linarith
  have hbound : ∀ t ∈ Ioo (0 : ℝ) T, (1 + t) ^ e ≤ max 1 ((1 + T) ^ e) := by
    intro t ht
    obtain ⟨ht0, htT⟩ := ht
    rcases le_or_gt 0 e with he | he
    · exact le_trans (Real.rpow_le_rpow (by linarith) (by linarith) he) (le_max_right _ _)
    · refine le_trans ?_ (le_max_left _ _)
      have := Real.rpow_le_rpow_of_nonpos (x := 1) (y := 1 + t) one_pos (by linarith) he.le
      rwa [Real.one_rpow] at this
  refine essSup_eq_of_ae_le_of_forall_lt ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ENNReal.ofReal_le_ofReal (hbound t ht)
  · intro b hb
    set M : ℝ := max 1 ((1 + T) ^ e) with hM
    have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
    set p : ℝ := if 1 ≤ (1 + T) ^ e then T else 0 with hp
    have hpval : (1 + p) ^ e = M := by
      rw [hp, hM]
      split_ifs with h
      · rw [max_eq_right h]
      · rw [add_zero, Real.one_rpow, max_eq_left (not_le.mp h).le]
    have hp1 : (0 : ℝ) < 1 + p := by
      rw [hp]
      split_ifs <;> linarith
    have hnb : (𝓝[Ioo (0 : ℝ) T] p).NeBot := by
      rw [hp]
      split_ifs
      · exact right_nhdsWithin_Ioo_neBot hT
      · exact left_nhdsWithin_Ioo_neBot hT
    have hcont : ContinuousAt (fun t : ℝ => ENNReal.ofReal ((1 + t) ^ e)) p := by
      refine ENNReal.continuous_ofReal.continuousAt.comp ?_
      exact (Real.continuousAt_rpow_const (1 + p) e (Or.inl (ne_of_gt hp1))).comp
        (continuousAt_const.add continuousAt_id)
    have hev : ∀ᶠ t in 𝓝 p, b < ENNReal.ofReal ((1 + t) ^ e) := by
      refine hcont.eventually (eventually_gt_nhds ?_)
      show b < ENNReal.ofReal ((1 + p) ^ e)
      rw [hpval]
      exact hb
    have hmem : {t : ℝ | b < ENNReal.ofReal ((1 + t) ^ e)} ∈ 𝓝[Ioo (0 : ℝ) T] p :=
      nhdsWithin_le_nhds hev
    obtain ⟨U, hUopen, hpU, hUsub⟩ := mem_nhdsWithin.mp hmem
    have hUne : (U ∩ Ioo (0 : ℝ) T).Nonempty := by
      refine Filter.nonempty_of_mem (f := 𝓝[Ioo (0 : ℝ) T] p) ?_
      exact Filter.inter_mem (hUopen.mem_nhds hpU |> nhdsWithin_le_nhds) self_mem_nhdsWithin
    intro hcontra
    have hsubnull := measure_mono_null hUsub hcontra
    rw [Measure.restrict_apply (hUopen.measurableSet.inter measurableSet_Ioo)] at hsubnull
    rw [inter_assoc, inter_self] at hsubnull
    exact hedenmalmBorelWeight_ne_zero_of_isOpen (x := x)
      (hUopen.inter isOpen_Ioo) hUne
      (fun t ht => mem_Ioi.mpr (by have := ht.2.1; linarith)) hsubnull

/-- **Exact essential supremum of the Borel multiplier on a finite window.** -/
theorem essSup_norm_hedenmalmBorelCharacter (alpha : ℂ) (x : ℝ) {T : ℝ} (hT : 0 < T) :
    essSup (fun t => ENNReal.ofReal ‖hedenmalmBorelCharacter alpha t‖)
        ((hedenmalmBorelWeight x).restrict (Ioo 0 T)) =
      ENNReal.ofReal (max 1 ((1 + T) ^ (-alpha.im / 2))) := by
  rw [← essSup_rpow_window x hT (-alpha.im / 2)]
  refine essSup_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [norm_hedenmalmBorelCharacter_rpow alpha (by have := ht.1; linarith)]

/-- **Exact two-sided condition number.**  The product of the two reflected essential suprema is the
radial power fixed by the horizontal displacement of the spectral parameter. -/
theorem essSup_norm_mul_essSup_norm_hedenmalmBorelCharacter
    (alpha : ℂ) (x : ℝ) {T : ℝ} (hT : 0 < T) :
    essSup (fun t => ENNReal.ofReal ‖hedenmalmBorelCharacter alpha t‖)
        ((hedenmalmBorelWeight x).restrict (Ioo 0 T)) *
      essSup (fun t => ENNReal.ofReal ‖hedenmalmBorelCharacter (-alpha) t‖)
        ((hedenmalmBorelWeight x).restrict (Ioo 0 T)) =
      ENNReal.ofReal ((1 + T) ^ (|alpha.im| / 2)) := by
  have hT1 : (1 : ℝ) ≤ 1 + T := by linarith
  have hT0 : (0 : ℝ) < 1 + T := by linarith
  rw [essSup_norm_hedenmalmBorelCharacter alpha x hT,
    essSup_norm_hedenmalmBorelCharacter (-alpha) x hT, Complex.neg_im,
    ← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left _ _))]
  congr 1
  have hup : ∀ e : ℝ, 0 ≤ e → max 1 ((1 + T) ^ e) = (1 + T) ^ e := by
    intro e he
    refine max_eq_right ?_
    have := Real.rpow_le_rpow zero_le_one hT1 he
    rwa [Real.one_rpow] at this
  have hdown : ∀ e : ℝ, e ≤ 0 → max 1 ((1 + T) ^ e) = 1 := by
    intro e he
    refine max_eq_left ?_
    have := Real.rpow_le_rpow_of_nonpos (x := 1) (y := 1 + T) one_pos hT1 he
    rwa [Real.one_rpow] at this
  rcases le_or_gt alpha.im 0 with him | him
  · rw [hup (-alpha.im / 2) (by linarith), hdown (- -alpha.im / 2) (by linarith),
      mul_one, abs_of_nonpos him]
  · rw [hdown (-alpha.im / 2) (by linarith), hup (- -alpha.im / 2) (by linarith),
      one_mul, abs_of_pos him]
    congr 1
    ring

/-- **The condition number at the geometric Sonin samples.**  At `1 + t = r ^ (2 j)` the two-sided
condition number is the `j`-th power of the horizontal displacement of the centered zero. -/
theorem essSup_norm_mul_essSup_norm_hedenmalmBorelCharacter_geometric_sample
    (alpha : ℂ) (x : ℝ) {r : ℝ} (hr : 1 < r) {j : ℕ} (hj : 0 < j) :
    essSup (fun t => ENNReal.ofReal ‖hedenmalmBorelCharacter alpha t‖)
        ((hedenmalmBorelWeight x).restrict (Ioo 0 (r ^ (2 * j) - 1))) *
      essSup (fun t => ENNReal.ofReal ‖hedenmalmBorelCharacter (-alpha) t‖)
        ((hedenmalmBorelWeight x).restrict (Ioo 0 (r ^ (2 * j) - 1))) =
      ENNReal.ofReal (r ^ ((j : ℝ) * |alpha.im|)) := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hpow : (1 : ℝ) < r ^ (2 * j) := one_lt_pow₀ hr (by omega)
  have hT : (0 : ℝ) < r ^ (2 * j) - 1 := by linarith
  rw [essSup_norm_mul_essSup_norm_hedenmalmBorelCharacter alpha x hT]
  congr 1
  have hbase : (1 : ℝ) + (r ^ (2 * j) - 1) = r ^ (2 * j) := by ring
  rw [hbase, ← Real.rpow_natCast r (2 * j), ← Real.rpow_mul hr0.le]
  congr 1
  push_cast
  ring

/-- The condition number is one exactly on the critical line. -/
theorem essSup_norm_mul_essSup_norm_hedenmalmBorelCharacter_eq_one_iff
    (alpha : ℂ) (x : ℝ) {T : ℝ} (hT : 0 < T) :
    essSup (fun t => ENNReal.ofReal ‖hedenmalmBorelCharacter alpha t‖)
          ((hedenmalmBorelWeight x).restrict (Ioo 0 T)) *
        essSup (fun t => ENNReal.ofReal ‖hedenmalmBorelCharacter (-alpha) t‖)
          ((hedenmalmBorelWeight x).restrict (Ioo 0 T)) = 1 ↔
      (1 / 2 + alpha * Complex.I).re = 1 / 2 := by
  have hT0 : (0 : ℝ) < 1 + T := by linarith
  have hT1 : (1 : ℝ) < 1 + T := by linarith
  rw [essSup_norm_mul_essSup_norm_hedenmalmBorelCharacter alpha x hT,
    show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
    ENNReal.ofReal_eq_ofReal_iff (Real.rpow_nonneg hT0.le _) zero_le_one,
    re_centeredSpectralPoint]
  constructor
  · intro h
    have habs : |alpha.im| / 2 = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hpos : 0 ≤ |alpha.im| / 2 := by positivity
        linarith
      · have := Real.one_lt_rpow_iff_of_pos hT0 |>.mpr (Or.inl ⟨hT1, hgt⟩)
        linarith
    have : alpha.im = 0 := by
      have : |alpha.im| = 0 := by linarith
      exact abs_eq_zero.mp this
    rw [this]
    ring
  · intro h
    have him : alpha.im = 0 := by linarith
    rw [him]
    simp

end RHTower
