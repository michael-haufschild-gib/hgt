import Mathlib

/-!
# Transferring a quenched time-density law to a deterministic fixed-time law

A jointly measurable event `S ⊆ Ω × ℝ` is observed along the time window `(0,T]`.  Two averages of
its indicator are available: the *time fraction* `t ↦ 1_S(J,t)` spent by a fixed parameter `J`
inside the event, and the *fixed-time probability* `J ↦ 1_S(J,t)` of the event at a fixed time.
Tonelli's theorem says the two window averages agree, and Fatou's lemma turns a quenched lower
density valid on a set `G` of parameters into a lower bound for the window average of the
fixed-time probability, weighted by the mass of `G`.

The final step is elementary: a bounded nonnegative function whose window averages have lower limit
at least `c` cannot be eventually below `c`, so its upper limit along unbounded times is at least
`c` as well.  Concretely, for every `b < c` the fixed-time probability exceeds `b` at an unbounded
set of deterministic times.

Everything is carried out in `ℝ≥0∞`, where Fatou's lemma holds along any countably generated filter
and no integrability side conditions arise.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section QuenchedTransfer

variable {Ω : Type*} [MeasurableSpace Ω] (γ : Measure Ω) [IsProbabilityMeasure γ]

/-- The fraction of the window `(0,T]` that the parameter `J` spends inside the event `S`. -/
def quenchedTimeFraction (S : Set (Ω × ℝ)) (J : Ω) (T : ℝ) : ℝ≥0∞ :=
  volume (Prod.mk J ⁻¹' S ∩ Ioc 0 T) / ENNReal.ofReal T

/-- The probability that the event `S` holds at the deterministic time `t`. -/
def quenchedFixedTimeProb (S : Set (Ω × ℝ)) (t : ℝ) : ℝ≥0∞ := γ {J | (J, t) ∈ S}

/-- The window average over `(0,T]` of the fixed-time probability. -/
def quenchedWindowAverage (S : Set (Ω × ℝ)) (T : ℝ) : ℝ≥0∞ :=
  (∫⁻ t in Ioc 0 T, quenchedFixedTimeProb γ S t) / ENNReal.ofReal T

variable {γ}

theorem quenchedFixedTimeProb_le_one (S : Set (Ω × ℝ)) (t : ℝ) :
    quenchedFixedTimeProb γ S t ≤ 1 :=
  prob_le_one

theorem quenchedTimeFraction_eq_restrict {S : Set (Ω × ℝ)} (hS : MeasurableSet S) (J : Ω) (T : ℝ) :
    quenchedTimeFraction S J T
      = (volume.restrict (Ioc 0 T)) (Prod.mk J ⁻¹' S) / ENNReal.ofReal T := by
  rw [quenchedTimeFraction, Measure.restrict_apply (hS.preimage measurable_prodMk_left)]

theorem measurable_quenchedTimeFraction {S : Set (Ω × ℝ)} (hS : MeasurableSet S) (T : ℝ) :
    Measurable fun J => quenchedTimeFraction S J T := by
  have h : (fun J => quenchedTimeFraction S J T)
      = fun J => (volume.restrict (Ioc 0 T)) (Prod.mk J ⁻¹' S) / ENNReal.ofReal T := by
    funext J
    exact quenchedTimeFraction_eq_restrict hS J T
  rw [h]
  exact (measurable_measure_prodMk_left hS).div_const _

/-- **The two window averages agree.**  Integrating the time fraction over the parameter measure
returns the window average of the fixed-time probability; this is Tonelli's theorem for the
indicator of `S` on `Ω × (0,T]`. -/
theorem lintegral_quenchedTimeFraction_eq {S : Set (Ω × ℝ)} (hS : MeasurableSet S) {T : ℝ}
    (hT : 0 < T) :
    ∫⁻ J, quenchedTimeFraction S J T ∂γ = quenchedWindowAverage γ S T := by
  have hinv : (ENNReal.ofReal T)⁻¹ ≠ ∞ := by
    simp only [ne_eq, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero, not_le]
    exact hT
  calc ∫⁻ J, quenchedTimeFraction S J T ∂γ
      = ∫⁻ J, (volume.restrict (Ioc 0 T)) (Prod.mk J ⁻¹' S) / ENNReal.ofReal T ∂γ := by
        refine lintegral_congr fun J => ?_
        exact quenchedTimeFraction_eq_restrict hS J T
    _ = (∫⁻ J, (volume.restrict (Ioc 0 T)) (Prod.mk J ⁻¹' S) ∂γ) / ENNReal.ofReal T := by
        simp only [div_eq_mul_inv]
        exact lintegral_mul_const' _ _ hinv
    _ = (γ.prod (volume.restrict (Ioc 0 T))) S / ENNReal.ofReal T := by
        rw [Measure.prod_apply hS]
    _ = (∫⁻ t, γ ((fun J => (J, t)) ⁻¹' S) ∂(volume.restrict (Ioc 0 T))) / ENNReal.ofReal T := by
        rw [Measure.prod_apply_symm hS]
    _ = quenchedWindowAverage γ S T := rfl

/-- The event and its complement split the window exactly. -/
theorem quenchedTimeFraction_add_compl {S : Set (Ω × ℝ)} (hS : MeasurableSet S) (J : Ω) {T : ℝ}
    (hT : 0 < T) :
    quenchedTimeFraction S J T + quenchedTimeFraction Sᶜ J T = 1 := by
  have hA : MeasurableSet (Prod.mk J ⁻¹' S) := hS.preimage measurable_prodMk_left
  have hpre : Prod.mk J ⁻¹' Sᶜ = (Prod.mk J ⁻¹' S)ᶜ := rfl
  have hsplit : volume (Prod.mk J ⁻¹' S ∩ Ioc 0 T) + volume ((Prod.mk J ⁻¹' S)ᶜ ∩ Ioc 0 T)
      = ENNReal.ofReal T := by
    have h := measure_inter_add_sdiff (μ := volume) (Ioc (0 : ℝ) T) hA
    have hcomm : Ioc (0 : ℝ) T ∩ Prod.mk J ⁻¹' S = Prod.mk J ⁻¹' S ∩ Ioc 0 T := Set.inter_comm _ _
    have hdiff : Ioc (0 : ℝ) T \ Prod.mk J ⁻¹' S = (Prod.mk J ⁻¹' S)ᶜ ∩ Ioc 0 T := by
      rw [Set.sdiff_eq, Set.inter_comm]
    rw [hcomm, hdiff, Real.volume_Ioc, sub_zero] at h
    exact h
  have hTne : ENNReal.ofReal T ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hT
  rw [quenchedTimeFraction, quenchedTimeFraction, hpre, ← ENNReal.add_div, hsplit,
    ENNReal.div_self hTne ENNReal.ofReal_ne_top]

/-- **The complement form of a quenched density bound.**  If the parameter `J` spends, in the limit,
at most an `η`-fraction of every long window outside the event, then it spends at least a
`1-η`-fraction inside it. -/
theorem le_liminf_quenchedTimeFraction_of_limsup_compl_le {S : Set (Ω × ℝ)} (hS : MeasurableSet S)
    (J : Ω) {η : ℝ≥0∞} (h : limsup (fun T => quenchedTimeFraction Sᶜ J T) atTop ≤ η) :
    1 - η ≤ liminf (fun T => quenchedTimeFraction S J T) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  have hbη : b + η < 1 := lt_tsub_iff_right.mp hb
  have hηlt : η < 1 - b := lt_tsub_iff_right.mpr (by rwa [add_comm] at hbη)
  obtain ⟨η', hη1, hη2⟩ := exists_between hηlt
  have hev : ∀ᶠ T : ℝ in atTop, quenchedTimeFraction Sᶜ J T < η' :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt h hη1)
  have hkey : ∀ᶠ T : ℝ in atTop, b ≤ quenchedTimeFraction S J T := by
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with T hT1 hT2
    have hsum := quenchedTimeFraction_add_compl hS J hT2
    have hble : b + η' ≤ 1 := by
      have := lt_tsub_iff_right.mp hη2
      rw [add_comm] at this
      exact le_of_lt this
    by_contra hcon
    push Not at hcon
    have : quenchedTimeFraction S J T + quenchedTimeFraction Sᶜ J T < b + η' :=
      ENNReal.add_lt_add hcon hT1
    rw [hsum] at this
    exact absurd hble (not_le.mpr this)
  exact le_liminf_of_le (by isBoundedDefault) hkey

/-- **Fatou transfer.**  A quenched lower density valid on a parameter set `G` forces the window
average of the fixed-time probability to have lower limit at least `c` times the mass of `G`. -/
theorem le_liminf_quenchedWindowAverage {S : Set (Ω × ℝ)} (hS : MeasurableSet S) {G : Set Ω}
    (hG : MeasurableSet G) {c : ℝ≥0∞}
    (hGc : ∀ J ∈ G, c ≤ liminf (fun T => quenchedTimeFraction S J T) atTop) :
    c * γ G ≤ liminf (fun T => quenchedWindowAverage γ S T) atTop := by
  have hkey : c * γ G ≤ ∫⁻ J, liminf (fun T => quenchedTimeFraction S J T) atTop ∂γ := by
    calc c * γ G = ∫⁻ _J in G, c ∂γ := (setLIntegral_const G c).symm
      _ ≤ ∫⁻ J in G, liminf (fun T => quenchedTimeFraction S J T) atTop ∂γ :=
          setLIntegral_mono' hG hGc
      _ ≤ ∫⁻ J, liminf (fun T => quenchedTimeFraction S J T) atTop ∂γ :=
          setLIntegral_le_lintegral _ _
  have hfatou : ∫⁻ J, liminf (fun T => quenchedTimeFraction S J T) atTop ∂γ
      ≤ liminf (fun T => ∫⁻ J, quenchedTimeFraction S J T ∂γ) atTop :=
    lintegral_liminf_le fun T => measurable_quenchedTimeFraction hS T
  have hcongr : liminf (fun T => ∫⁻ J, quenchedTimeFraction S J T ∂γ) atTop
      = liminf (fun T => quenchedWindowAverage γ S T) atTop := by
    refine liminf_congr ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact lintegral_quenchedTimeFraction_eq hS hT
  calc c * γ G ≤ ∫⁻ J, liminf (fun T => quenchedTimeFraction S J T) atTop ∂γ := hkey
    _ ≤ liminf (fun T => ∫⁻ J, quenchedTimeFraction S J T ∂γ) atTop := hfatou
    _ = liminf (fun T => quenchedWindowAverage γ S T) atTop := hcongr

/-- **The deterministic fixed-time law.**  A quenched density bound `η` valid on a parameter set of
mass at least one half yields the window-average floor `(1-η)/2`. -/
theorem half_mul_one_sub_le_liminf_quenchedWindowAverage {S : Set (Ω × ℝ)} (hS : MeasurableSet S)
    {G : Set Ω} (hG : MeasurableSet G) (hmass : 1 / 2 ≤ γ G) {η : ℝ≥0∞}
    (hquench : ∀ J ∈ G, limsup (fun T => quenchedTimeFraction Sᶜ J T) atTop ≤ η) :
    (1 - η) / 2 ≤ liminf (fun T => quenchedWindowAverage γ S T) atTop := by
  have hGc : ∀ J ∈ G, (1 - η) ≤ liminf (fun T => quenchedTimeFraction S J T) atTop :=
    fun J hJ => le_liminf_quenchedTimeFraction_of_limsup_compl_le hS J (hquench J hJ)
  refine le_trans ?_ (le_liminf_quenchedWindowAverage hS hG hGc)
  have hstep : (1 - η) * (1 / 2 : ℝ≥0∞) ≤ (1 - η) * γ G := mul_le_mul' le_rfl hmass
  calc (1 - η) / 2 = (1 - η) * (1 / 2 : ℝ≥0∞) := by
        rw [ENNReal.div_eq_inv_mul, one_div, mul_comm]
    _ ≤ (1 - η) * γ G := hstep

/-- **The upper limit of the fixed-time probability dominates its window-average floor.**  A bounded
nonnegative observable whose window averages have lower limit at least `c` must return to within
any neighbourhood of `c` at unbounded times. -/
theorem le_limsup_quenchedFixedTimeProb (S : Set (Ω × ℝ)) {c : ℝ≥0∞}
    (h : c ≤ liminf (fun T => quenchedWindowAverage γ S T) atTop) :
    c ≤ limsup (fun t => quenchedFixedTimeProb γ S t) atTop := by
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hb1, hb2⟩ := exists_between hcon
  have hev : ∀ᶠ t : ℝ in atTop, quenchedFixedTimeProb γ S t ≤ b :=
    (eventually_lt_of_limsup_lt hb1).mono fun t ht => le_of_lt ht
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp hev
  set t₁ : ℝ := max t₀ 1 with ht₁def
  have ht₁pos : 0 < t₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound : ∀ᶠ T : ℝ in atTop,
      quenchedWindowAverage γ S T ≤ ENNReal.ofReal t₁ / ENNReal.ofReal T + b := by
    filter_upwards [eventually_ge_atTop t₁] with T hT
    have hTpos : 0 < T := lt_of_lt_of_le ht₁pos hT
    have hTne : ENNReal.ofReal T ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hTpos
    have hsplit : (∫⁻ t in Ioc 0 T, quenchedFixedTimeProb γ S t)
        = (∫⁻ t in Ioc 0 t₁, quenchedFixedTimeProb γ S t)
          + ∫⁻ t in Ioc t₁ T, quenchedFixedTimeProb γ S t := by
      have hdisj : Disjoint (Ioc (0 : ℝ) t₁) (Ioc t₁ T) :=
        Set.disjoint_left.mpr fun x hx hx' => absurd hx'.1 (not_lt.mpr hx.2)
      rw [← lintegral_union measurableSet_Ioc hdisj,
        Set.Ioc_union_Ioc_eq_Ioc (le_of_lt ht₁pos) hT]
    have hhead : (∫⁻ t in Ioc 0 t₁, quenchedFixedTimeProb γ S t) ≤ ENNReal.ofReal t₁ := by
      calc (∫⁻ t in Ioc 0 t₁, quenchedFixedTimeProb γ S t) ≤ ∫⁻ _t in Ioc (0 : ℝ) t₁, 1 :=
            lintegral_mono fun t => quenchedFixedTimeProb_le_one S t
        _ = volume (Ioc (0 : ℝ) t₁) := by rw [setLIntegral_const, one_mul]
        _ = ENNReal.ofReal t₁ := by rw [Real.volume_Ioc, sub_zero]
    have htail : (∫⁻ t in Ioc t₁ T, quenchedFixedTimeProb γ S t) ≤ b * ENNReal.ofReal T := by
      calc (∫⁻ t in Ioc t₁ T, quenchedFixedTimeProb γ S t) ≤ ∫⁻ _t in Ioc t₁ T, b := by
            refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
            exact ht₀ t (le_trans (le_max_left _ _) (le_of_lt ht.1))
        _ = b * volume (Ioc t₁ T) := by rw [setLIntegral_const]
        _ ≤ b * ENNReal.ofReal T := by
            refine mul_le_mul' le_rfl ?_
            rw [Real.volume_Ioc]
            exact ENNReal.ofReal_le_ofReal (by linarith [le_of_lt ht₁pos])
    calc quenchedWindowAverage γ S T
        = ((∫⁻ t in Ioc 0 t₁, quenchedFixedTimeProb γ S t)
            + ∫⁻ t in Ioc t₁ T, quenchedFixedTimeProb γ S t) / ENNReal.ofReal T := by
          rw [quenchedWindowAverage, hsplit]
      _ ≤ (ENNReal.ofReal t₁ + b * ENNReal.ofReal T) / ENNReal.ofReal T := by
          gcongr
      _ = ENNReal.ofReal t₁ / ENNReal.ofReal T + b := by
          rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hTne ENNReal.ofReal_ne_top]
  have htend : Tendsto (fun T : ℝ => ENNReal.ofReal t₁ / ENNReal.ofReal T + b) atTop (𝓝 b) := by
    have hzero : Tendsto (fun T : ℝ => ENNReal.ofReal t₁ / ENNReal.ofReal T) atTop (𝓝 0) := by
      have heq : (fun T : ℝ => ENNReal.ofReal t₁ / ENNReal.ofReal T)
          =ᶠ[atTop] fun T : ℝ => ENNReal.ofReal (t₁ / T) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
        rw [ENNReal.ofReal_div_of_pos hT]
      have hreal : Tendsto (fun T : ℝ => t₁ / T) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul t₁
      have hE := ENNReal.tendsto_ofReal hreal
      rw [ENNReal.ofReal_zero] at hE
      exact Tendsto.congr' heq.symm hE
    simpa using hzero.add tendsto_const_nhds
  have hle : liminf (fun T => quenchedWindowAverage γ S T) atTop ≤ b := by
    calc liminf (fun T => quenchedWindowAverage γ S T) atTop
        ≤ liminf (fun T : ℝ => ENNReal.ofReal t₁ / ENNReal.ofReal T + b) atTop :=
          liminf_le_liminf hbound
      _ = b := htend.liminf_eq
  exact absurd (le_trans h hle) (not_le.mpr hb2)

/-- **Unbounded common times.**  Every level strictly below the window-average floor is exceeded by
the fixed-time probability at an unbounded set of deterministic times. -/
theorem frequently_lt_quenchedFixedTimeProb (S : Set (Ω × ℝ)) {c b : ℝ≥0∞} (hb : b < c)
    (h : c ≤ liminf (fun T => quenchedWindowAverage γ S T) atTop) :
    ∃ᶠ t : ℝ in atTop, b < quenchedFixedTimeProb γ S t :=
  frequently_lt_of_lt_limsup (by isBoundedDefault)
    (lt_of_lt_of_le hb (le_limsup_quenchedFixedTimeProb S h))

end QuenchedTransfer

end

end GaloisForLFunctions.HTGeometry
