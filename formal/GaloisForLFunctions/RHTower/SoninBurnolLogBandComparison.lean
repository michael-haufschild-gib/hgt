import GaloisForLFunctions.RHTower.EvenBoundedMultiplier
import GaloisForLFunctions.RHTower.SoninBurnolLogShellWeyl

/-!
# The step conductor approximates the logarithm to within the tower ratio

The step channel on the geometric shell tower is multiplication by a step symbol; the genuine
logarithmic multiplier, cut to the same band, is multiplication by `log|t|`.  On the layer between
`rᵏa` and `rᵏ⁺¹a` the two symbols differ by `log|t| - log(rᵏa) ∈ [0, log r]`, so their difference
is a bounded symbol with bound `log r`.

Hence the operator distance between the step conductor and the band logarithm is at most `log r`,
uniformly in the truncation length and the base aperture.  Refining the tower drives the step
conductor to the genuine logarithm in operator norm.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Set

/-! ## The two symbols -/

/-- Symbol of the step conductor: the value on the `k`-th layer is `log(rᵏa)`. -/
def soninStepLogSymbol (a r : ℝ) (n : ℕ) : ℝ → ℂ :=
  fun t => ∑ k ∈ Finset.range n,
    ((Real.log (logShellRadius a r k) : ℝ) : ℂ) *
      ((centralInterval (logShellRadius a r (k + 1))).indicator (fun _ => (1 : ℂ)) t -
        (centralInterval (logShellRadius a r k)).indicator (fun _ => (1 : ℂ)) t)

/-- Symbol of the genuine logarithm cut to the tower band. -/
def soninBandLogSymbol (a r : ℝ) (n : ℕ) : ℝ → ℂ :=
  Set.indicator
    ((fun t : ℝ => |t|) ⁻¹' Set.Ioc (logShellRadius a r 0) (logShellRadius a r n))
    (fun t => ((Real.log |t| : ℝ) : ℂ))

theorem mem_centralInterval_iff (s t : ℝ) : t ∈ centralInterval s ↔ |t| ≤ s := by
  rw [centralInterval, Set.mem_Icc, abs_le]

/-! ## Pointwise evaluation of the step symbol -/

theorem soninStepLogSymbol_eq_zero_of_le_base {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    (n : ℕ) {t : ℝ} (ht : |t| ≤ logShellRadius a r 0) :
    soninStepLogSymbol a r n t = 0 := by
  unfold soninStepLogSymbol
  refine Finset.sum_eq_zero fun k _ => ?_
  have h1 : t ∈ centralInterval (logShellRadius a r (k + 1)) :=
    (mem_centralInterval_iff _ _).mpr
      (ht.trans (logShellRadius_mono ha hr (Nat.zero_le (k + 1))))
  have h2 : t ∈ centralInterval (logShellRadius a r k) :=
    (mem_centralInterval_iff _ _).mpr
      (ht.trans (logShellRadius_mono ha hr (Nat.zero_le k)))
  rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, sub_self, mul_zero]

theorem soninStepLogSymbol_eq_zero_of_gt_top {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    (n : ℕ) {t : ℝ} (ht : logShellRadius a r n < |t|) :
    soninStepLogSymbol a r n t = 0 := by
  unfold soninStepLogSymbol
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkn : k + 1 ≤ n := Finset.mem_range.mp hk
  have h1 : t ∉ centralInterval (logShellRadius a r (k + 1)) := by
    rw [mem_centralInterval_iff]
    exact not_le.mpr (lt_of_le_of_lt (logShellRadius_mono ha hr hkn) ht)
  have h2 : t ∉ centralInterval (logShellRadius a r k) := by
    rw [mem_centralInterval_iff]
    exact not_le.mpr
      (lt_of_le_of_lt (logShellRadius_mono ha hr (Nat.le_of_succ_le hkn)) ht)
  rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, sub_self, mul_zero]

theorem soninStepLogSymbol_eq_of_mem_layer {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    (n : ℕ) {t : ℝ} {j : ℕ} (hj : j < n)
    (hlo : logShellRadius a r j < |t|)
    (hhi : |t| ≤ logShellRadius a r (j + 1)) :
    soninStepLogSymbol a r n t =
      ((Real.log (logShellRadius a r j) : ℝ) : ℂ) := by
  classical
  unfold soninStepLogSymbol
  rw [Finset.sum_eq_single j]
  · have h1 : t ∈ centralInterval (logShellRadius a r (j + 1)) :=
      (mem_centralInterval_iff _ _).mpr hhi
    have h2 : t ∉ centralInterval (logShellRadius a r j) := by
      rw [mem_centralInterval_iff]
      exact not_le.mpr hlo
    rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, sub_zero, mul_one]
  · intro k _ hkj
    rcases lt_or_gt_of_ne hkj with hlt | hgt
    · have h1 : t ∉ centralInterval (logShellRadius a r (k + 1)) := by
        rw [mem_centralInterval_iff]
        exact not_le.mpr
          (lt_of_le_of_lt (logShellRadius_mono ha hr (Nat.succ_le_of_lt hlt)) hlo)
      have h2 : t ∉ centralInterval (logShellRadius a r k) := by
        rw [mem_centralInterval_iff]
        exact not_le.mpr (lt_of_le_of_lt (logShellRadius_mono ha hr hlt.le) hlo)
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, sub_self, mul_zero]
    · have h1 : t ∈ centralInterval (logShellRadius a r (k + 1)) :=
        (mem_centralInterval_iff _ _).mpr
          (hhi.trans (logShellRadius_mono ha hr (Nat.succ_le_succ hgt.le)))
      have h2 : t ∈ centralInterval (logShellRadius a r k) :=
        (mem_centralInterval_iff _ _).mpr
          (hhi.trans (logShellRadius_mono ha hr (Nat.succ_le_of_lt hgt)))
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, sub_self, mul_zero]
  · intro hjn
    exact absurd (Finset.mem_range.mpr hj) hjn

/-- Every point of the tower band lies in exactly one layer. -/
theorem exists_logShellLayer {a r : ℝ} (n : ℕ) {t : ℝ}
    (hlo : logShellRadius a r 0 < |t|) (hhi : |t| ≤ logShellRadius a r n) :
    ∃ j < n, logShellRadius a r j < |t| ∧ |t| ≤ logShellRadius a r (j + 1) := by
  induction n with
  | zero => exact absurd hhi (not_le.mpr hlo)
  | succ m ih =>
      by_cases hm : |t| ≤ logShellRadius a r m
      · obtain ⟨j, hj, h1, h2⟩ := ih hm
        exact ⟨j, Nat.lt_succ_of_lt hj, h1, h2⟩
      · exact ⟨m, Nat.lt_succ_self m, lt_of_not_ge hm, hhi⟩

/-! ## The pointwise symbol comparison -/

/-- **Uniform step error.**  The step symbol and the band logarithm differ by at most the tower
ratio, at every point and for every truncation length. -/
theorem norm_soninStepLogSymbol_sub_soninBandLogSymbol_le
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (n : ℕ) (t : ℝ) :
    ‖soninStepLogSymbol a r n t - soninBandLogSymbol a r n t‖ ≤ Real.log r := by
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr.le
  by_cases hband :
      t ∈ (fun s : ℝ => |s|) ⁻¹' Set.Ioc (logShellRadius a r 0) (logShellRadius a r n)
  · have hmem : logShellRadius a r 0 < |t| ∧ |t| ≤ logShellRadius a r n := by
      simpa [Set.mem_preimage, Set.mem_Ioc] using hband
    obtain ⟨hlo, hhi⟩ := hmem
    obtain ⟨j, hj, h1, h2⟩ := exists_logShellLayer (a := a) (r := r) n hlo hhi
    have hstep := soninStepLogSymbol_eq_of_mem_layer ha hr n hj h1 h2
    have hbandval : soninBandLogSymbol a r n t = ((Real.log |t| : ℝ) : ℂ) := by
      unfold soninBandLogSymbol
      exact Set.indicator_of_mem hband _
    have hRj : 0 < logShellRadius a r j := logShellRadius_pos ha hr j
    have hlower : Real.log (logShellRadius a r j) ≤ Real.log |t| :=
      Real.log_le_log hRj h1.le
    have hupper : Real.log |t| ≤ Real.log (logShellRadius a r j) + Real.log r := by
      have hstepR : logShellRadius a r (j + 1) = r * logShellRadius a r j :=
        logShellRadius_succ a r j
      have := Real.log_le_log (lt_of_lt_of_le hRj h1.le) h2
      rw [hstepR, Real.log_mul (zero_lt_one.trans hr).ne' hRj.ne'] at this
      linarith
    rw [hstep, hbandval, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_le]
    constructor <;> linarith
  · have hstep : soninStepLogSymbol a r n t = 0 := by
      rcases not_and_or.mp hband with h | h
      · exact soninStepLogSymbol_eq_zero_of_le_base ha hr n (not_lt.mp h)
      · exact soninStepLogSymbol_eq_zero_of_gt_top ha hr n (not_le.mp h)
    have hbandval : soninBandLogSymbol a r n t = 0 :=
      Set.indicator_of_notMem hband _
    rw [hstep, hbandval, sub_zero, norm_zero]
    exact hlogr

end RHTower

namespace RHTower

open MeasureTheory Set

/-! ## The channel is multiplication by the step symbol -/

theorem evenLogShellChannel_coeFn (a r : ℝ) (n : ℕ) (f : evenSubspace) :
    (((evenLogShellChannel a r n f : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun t => soninStepLogSymbol a r n t *
        (((f : evenSubspace) : SoninL2) : ℝ → ℂ) t := by
  have h := evenCoeFn_sum (Finset.range n)
    (fun k => ((Real.log (logShellRadius a r k) : ℝ) : ℂ) •
      (evenIndicatorCutoff (logShellRadius a r (k + 1)) -
        evenIndicatorCutoff (logShellRadius a r k)))
    (fun k t => ((Real.log (logShellRadius a r k) : ℝ) : ℂ) *
      ((centralInterval (logShellRadius a r (k + 1))).indicator (fun _ => (1 : ℂ)) t -
        (centralInterval (logShellRadius a r k)).indicator (fun _ => (1 : ℂ)) t))
    f (fun k _ => evenSmulCutoffDiff_coeFn _ _ _ f)
  simpa only [evenLogShellChannel, soninStepLogSymbol] using h

/-! ## The band logarithm as a bounded even multiplier -/

theorem measurable_soninBandLogSymbol (a r : ℝ) (n : ℕ) :
    Measurable (soninBandLogSymbol a r n) := by
  unfold soninBandLogSymbol
  refine Measurable.indicator ?_ ?_
  · exact Complex.measurable_ofReal.comp
      (Real.measurable_log.comp continuous_abs.measurable)
  · exact (continuous_abs.measurable) measurableSet_Ioc

theorem soninBandLogSymbol_even (a r : ℝ) (n : ℕ) (t : ℝ) :
    soninBandLogSymbol a r n (-t) = soninBandLogSymbol a r n t := by
  unfold soninBandLogSymbol
  by_cases h : |t| ∈ Set.Ioc (logShellRadius a r 0) (logShellRadius a r n)
  · rw [Set.indicator_of_mem (by simpa [Set.mem_preimage, abs_neg] using h),
      Set.indicator_of_mem (by simpa [Set.mem_preimage] using h), abs_neg]
  · rw [Set.indicator_of_notMem (by simpa [Set.mem_preimage, abs_neg] using h),
      Set.indicator_of_notMem (by simpa [Set.mem_preimage] using h)]

/-- Bound for the band logarithm symbol. -/
def soninBandLogBound (a r : ℝ) (n : ℕ) : ℝ :=
  |Real.log (logShellRadius a r 0)| + |Real.log (logShellRadius a r n)|

theorem soninBandLogBound_nonneg (a r : ℝ) (n : ℕ) : 0 ≤ soninBandLogBound a r n := by
  unfold soninBandLogBound
  positivity

theorem norm_soninBandLogSymbol_le {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (n : ℕ) (t : ℝ) :
    ‖soninBandLogSymbol a r n t‖ ≤ soninBandLogBound a r n := by
  unfold soninBandLogSymbol soninBandLogBound
  by_cases h : t ∈ (fun s : ℝ => |s|) ⁻¹' Set.Ioc (logShellRadius a r 0)
      (logShellRadius a r n)
  · have hmem : logShellRadius a r 0 < |t| ∧ |t| ≤ logShellRadius a r n := by
      simpa [Set.mem_preimage, Set.mem_Ioc] using h
    obtain ⟨hlo, hhi⟩ := hmem
    have hR0 : 0 < logShellRadius a r 0 := logShellRadius_pos ha hr 0
    have hlow : Real.log (logShellRadius a r 0) ≤ Real.log |t| :=
      Real.log_le_log hR0 hlo.le
    have hhigh : Real.log |t| ≤ Real.log (logShellRadius a r n) :=
      Real.log_le_log (lt_trans hR0 hlo) hhi
    rw [Set.indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · have h1 : -|Real.log (logShellRadius a r 0)| ≤
          Real.log (logShellRadius a r 0) := neg_abs_le _
      have h2 : (0 : ℝ) ≤ |Real.log (logShellRadius a r n)| := abs_nonneg _
      linarith
    · have h1 : Real.log (logShellRadius a r n) ≤
          |Real.log (logShellRadius a r n)| := le_abs_self _
      have h2 : (0 : ℝ) ≤ |Real.log (logShellRadius a r 0)| := abs_nonneg _
      linarith
  · rw [Set.indicator_of_notMem h, norm_zero]
    positivity

/-- The genuine logarithm of position, cut to the tower band, as a bounded operator on the even
carrier. -/
def soninBandLogMultiplier (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  evenBoundedMul (measurable_soninBandLogSymbol a r n)
    (soninBandLogBound_nonneg a r n) (norm_soninBandLogSymbol_le ha hr n)
    (soninBandLogSymbol_even a r n)

theorem soninBandLogMultiplier_coeFn (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n : ℕ)
    (f : evenSubspace) :
    (((soninBandLogMultiplier a r ha hr n f : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun t => soninBandLogSymbol a r n t *
        (((f : evenSubspace) : SoninL2) : ℝ → ℂ) t :=
  evenBoundedMul_coeFn (measurable_soninBandLogSymbol a r n)
    (soninBandLogBound_nonneg a r n) (norm_soninBandLogSymbol_le ha hr n)
    (soninBandLogSymbol_even a r n) f

/-! ## The approximation theorem -/

/-- **Uniform approximation of the logarithm by the step conductor.**  The step conductor on the
geometric tower is within `log r` of the genuine logarithm of position cut to the same band, in
operator norm, for every truncation length and every base aperture.  Refining the tower therefore
drives the conductor to the logarithm. -/
theorem norm_evenLogShellChannel_sub_soninBandLogMultiplier_le
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n : ℕ) :
    ‖evenLogShellChannel a r n - soninBandLogMultiplier a r ha hr n‖ ≤ Real.log r := by
  refine norm_le_of_evenCoeFn_mul (Real.log_nonneg hr.le)
    (fun t => norm_soninStepLogSymbol_sub_soninBandLogSymbol_le ha hr n t) ?_
  intro f
  have hsub : (((evenLogShellChannel a r n - soninBandLogMultiplier a r ha hr n) f :
      evenSubspace) : SoninL2) =
      ((evenLogShellChannel a r n f : evenSubspace) : SoninL2) -
        ((soninBandLogMultiplier a r ha hr n f : evenSubspace) : SoninL2) := by
    simp
  rw [hsub]
  filter_upwards [Lp.coeFn_sub ((evenLogShellChannel a r n f : evenSubspace) : SoninL2)
      ((soninBandLogMultiplier a r ha hr n f : evenSubspace) : SoninL2),
    evenLogShellChannel_coeFn a r n f,
    soninBandLogMultiplier_coeFn a r ha hr n f] with t h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3, sub_mul]

end RHTower

namespace RHTower

open MeasureTheory Set

/-! ## Stationarity of the band logarithm on its natural core -/

/-- A vector of the even carrier supported inside the `m`-th tower band. -/
def SoninBandSupported (a r : ℝ) (m : ℕ) (f : evenSubspace) : Prop :=
  ∀ᵐ t ∂(volume : Measure ℝ),
    t ∉ (fun s : ℝ => |s|) ⁻¹'
        Set.Ioc (logShellRadius a r 0) (logShellRadius a r m) →
      (((f : evenSubspace) : SoninL2) : ℝ → ℂ) t = 0

/-- Enlarging the truncation does not change the band logarithm inside the smaller band. -/
theorem soninBandLogSymbol_eq_of_mem_smaller {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    {m n : ℕ} (hmn : m ≤ n) {t : ℝ}
    (ht : t ∈ (fun s : ℝ => |s|) ⁻¹'
      Set.Ioc (logShellRadius a r 0) (logShellRadius a r m)) :
    soninBandLogSymbol a r n t = soninBandLogSymbol a r m t := by
  have hmem : logShellRadius a r 0 < |t| ∧ |t| ≤ logShellRadius a r m := by
    simpa [Set.mem_preimage, Set.mem_Ioc] using ht
  have htn : t ∈ (fun s : ℝ => |s|) ⁻¹'
      Set.Ioc (logShellRadius a r 0) (logShellRadius a r n) := by
    simp only [Set.mem_preimage, Set.mem_Ioc]
    exact ⟨hmem.1, hmem.2.trans (logShellRadius_mono ha hr hmn)⟩
  unfold soninBandLogSymbol
  rw [Set.indicator_of_mem htn, Set.indicator_of_mem ht]

/-- **Stationarity on the core.**  On a vector supported in the `m`-th band, every truncation
beyond `m` gives the same value.  The band logarithms therefore define a single operator on the
union of the band-supported subspaces — the natural core of the logarithm of position. -/
theorem soninBandLogMultiplier_eq_of_bandSupported {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    {m n : ℕ} (hmn : m ≤ n) {f : evenSubspace} (hf : SoninBandSupported a r m f) :
    soninBandLogMultiplier a r ha hr n f = soninBandLogMultiplier a r ha hr m f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [soninBandLogMultiplier_coeFn a r ha hr n f,
    soninBandLogMultiplier_coeFn a r ha hr m f, hf] with t h1 h2 h3
  rw [h1, h2]
  by_cases hmem : t ∈ (fun s : ℝ => |s|) ⁻¹'
      Set.Ioc (logShellRadius a r 0) (logShellRadius a r m)
  · rw [soninBandLogSymbol_eq_of_mem_smaller ha hr hmn hmem]
  · rw [h3 hmem, mul_zero, mul_zero]

/-- The shell units of the tower belong to the core. -/
theorem soninBandSupported_logShellUnit (a r : ℝ) (ha : 0 < a) (hr : 1 < r)
    {k m : ℕ} (hk : k + 1 ≤ m) :
    SoninBandSupported a r m (logShellUnit a r ha hr k) := by
  filter_upwards [normalizedIndicator_ae
    (evenShellCell (logShellRadius a r k) (logShellRadius a r (k + 1)) 0)
    (measurableSet_evenShellCell (logShellRadius a r k)
      (logShellRadius a r (k + 1)) 0)
    (evenShellCell_measure_ne_top (logShellRadius_lt_succ ha hr k) 0)] with t hval
  intro hnot
  have hcell : t ∉ evenShellCell (logShellRadius a r k)
      (logShellRadius a r (k + 1)) 0 := by
    intro hmem
    apply hnot
    have hlow : logShellRadius a r k < |t| :=
      (lt_shellLeft (logShellRadius_lt_succ ha hr k) 0).trans hmem.1
    have hhigh : |t| < logShellRadius a r (k + 1) :=
      hmem.2.trans_lt (shellRight_lt (logShellRadius_lt_succ ha hr k) 0)
    simp only [Set.mem_preimage, Set.mem_Ioc]
    exact ⟨lt_of_le_of_lt (logShellRadius_mono ha hr (Nat.zero_le k)) hlow,
      hhigh.le.trans (logShellRadius_mono ha hr hk)⟩
  change (logShellUnit a r ha hr k : SoninL2) t = 0
  rw [logShellUnit]
  change evenShellVector (logShellRadius a r k) (logShellRadius a r (k + 1))
    (logShellRadius_lt_succ ha hr k) 0 t = 0
  rw [evenShellVector]
  rw [hval, Set.indicator_of_notMem hcell, mul_zero]

end RHTower
