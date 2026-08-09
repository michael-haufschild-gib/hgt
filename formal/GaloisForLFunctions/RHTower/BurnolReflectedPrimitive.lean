import GaloisForLFunctions.RHTower.BurnolReflectedMass

/-!
# The primitive of the reflected source

The reflected source enters a harmonic term at every integer and drops one at every even integer,
so it is right-continuous where terms enter but not where they leave.  Replacing the closed window
`t/2 ≤ k ≤ t` by the half-open window `t/2 < k ≤ t` changes the source only on the integers — a
null set — and produces a representative that is locally constant to the right everywhere.

Its primitive is the staircase `burnolReflectedTruncMass`, so the fundamental theorem of calculus
applies and the reflected mass has a genuine right derivative at every point.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The half-open harmonic window. -/
def burnolReflectedWindowRC (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (⌊t / 2⌋₊ + 1) ⌊t⌋₊, (1 : ℝ) / (k : ℝ)

/-- The right-continuous representative of the reflected source. -/
def burnolReflectedSourceRC (t : ℝ) : ℝ := burnolReflectedWindowRC t - Real.log 2

/-- The real form of the reflected source. -/
def burnolReflectedSourceReal (t : ℝ) : ℝ := burnolHarmonicWindow t - Real.log 2

theorem burnolReflectedRawSource_eq_real {t : ℝ} (ht : 0 < t) :
    burnolReflectedRawSource t = ((burnolReflectedSourceReal t : ℝ) : ℂ) := by
  rw [burnolReflectedRawSource_eq_harmonic ht, burnolReflectedSourceReal, burnolHarmonicWindow]

/-- Off the integer multiples of two the two representatives agree. -/
theorem burnolReflectedSourceRC_eq {t : ℝ} (ht : 0 ≤ t) (hfrac : (⌊t / 2⌋₊ : ℝ) < t / 2) :
    burnolReflectedSourceRC t = burnolReflectedSourceReal t := by
  have hceil : ⌈t / 2⌉₊ = ⌊t / 2⌋₊ + 1 := by
    refine le_antisymm ?_ ?_
    · refine Nat.ceil_le.mpr ?_
      push_cast
      linarith [Nat.lt_floor_add_one (t / 2)]
    · exact Nat.succ_le_of_lt (Nat.lt_ceil.mpr hfrac)
  simp only [burnolReflectedSourceRC, burnolReflectedSourceReal, burnolReflectedWindowRC,
    burnolHarmonicWindow, hceil]

theorem burnolReflectedSourceRC_ae :
    burnolReflectedSourceRC =ᵐ[volume.restrict (Ioi (0 : ℝ))] burnolReflectedSourceReal := by
  have hcount : (Set.range fun n : ℕ => 2 * (n : ℝ)).Countable :=
    Set.countable_range _
  have hmeas : volume {t : ℝ | (⌊t / 2⌋₊ : ℝ) = t / 2} = 0 := by
    refine measure_mono_null ?_ (Set.Countable.measure_zero hcount volume)
    intro t ht
    have ht' : (⌊t / 2⌋₊ : ℝ) = t / 2 := ht
    refine ⟨⌊t / 2⌋₊, ?_⟩
    show 2 * ((⌊t / 2⌋₊ : ℕ) : ℝ) = t
    rw [ht']
    ring
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (MeasureTheory.compl_mem_ae_iff.mpr hmeas)] with t ht hne
  refine burnolReflectedSourceRC_eq (le_of_lt ht) ?_
  have hle : (⌊t / 2⌋₊ : ℝ) ≤ t / 2 := Nat.floor_le (by linarith [mem_Ioi.mp ht])
  exact lt_of_le_of_ne hle hne

/-! ## Right continuity -/

theorem burnolEventually_natFloor_eq_Ici (a : ℝ) (ha : 0 ≤ a) :
    ∀ᶠ y in 𝓝[≥] a, ⌊y⌋₊ = ⌊a⌋₊ := by
  have hmem : Iio ((⌊a⌋₊ : ℝ) + 1) ∈ 𝓝 a := Iio_mem_nhds (Nat.lt_floor_add_one a)
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with y hy hy2
  have hay : a ≤ y := hy2
  have hy0 : (0 : ℝ) ≤ y := le_trans ha hay
  have hylt : y < (⌊a⌋₊ : ℝ) + 1 := hy
  have hlt : ⌊y⌋₊ < ⌊a⌋₊ + 1 := by
    refine (Nat.floor_lt hy0).mpr ?_
    push_cast
    exact hylt
  have hge : ⌊a⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hay
  omega

theorem continuousWithinAt_burnolReflectedSourceRC {a : ℝ} (ha : 0 ≤ a) :
    ContinuousWithinAt burnolReflectedSourceRC (Ici a) a := by
  have hhalf : ∀ᶠ y in 𝓝[≥] a, ⌊y / 2⌋₊ = ⌊a / 2⌋₊ := by
    have hmap : Tendsto (fun y : ℝ => y / 2) (𝓝[≥] a) (𝓝[≥] (a / 2)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact ((continuous_id.div_const 2).tendsto a).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        have hay : a ≤ y := hy
        show a / 2 ≤ y / 2
        linarith
    exact hmap.eventually (burnolEventually_natFloor_eq_Ici (a / 2) (by linarith))
  have hkey : burnolReflectedSourceRC =ᶠ[𝓝[≥] a] fun _ => burnolReflectedSourceRC a := by
    filter_upwards [burnolEventually_natFloor_eq_Ici a ha, hhalf] with y h1 h2
    rw [burnolReflectedSourceRC, burnolReflectedSourceRC, burnolReflectedWindowRC,
      burnolReflectedWindowRC, h1, h2]
  exact (continuousWithinAt_const).congr_of_eventuallyEq hkey rfl


/-! ## The primitive and its right derivative -/

theorem burnolReflectedWindowRC_nonneg (t : ℝ) : 0 ≤ burnolReflectedWindowRC t :=
  Finset.sum_nonneg fun k _ => by positivity

theorem burnolReflectedWindowRC_le {t : ℝ} (ht : 0 ≤ t) : burnolReflectedWindowRC t ≤ t := by
  have hterm : ∀ k ∈ Finset.Icc (⌊t / 2⌋₊ + 1) ⌊t⌋₊, (1 : ℝ) / (k : ℝ) ≤ 1 := by
    intro k hk
    obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    rw [div_le_one (by linarith)]
    linarith
  have hsum := Finset.sum_le_card_nsmul _ _ (1 : ℝ) hterm
  rw [nsmul_eq_mul, mul_one, Nat.card_Icc] at hsum
  refine le_trans hsum ?_
  have hcard : (⌊t⌋₊ + 1 - (⌊t / 2⌋₊ + 1) : ℕ) ≤ ⌊t⌋₊ := by omega
  have hcardR : ((⌊t⌋₊ + 1 - (⌊t / 2⌋₊ + 1) : ℕ) : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hcard
  exact le_trans hcardR (Nat.floor_le ht)

theorem abs_burnolReflectedSourceRC_le {t : ℝ} (ht : 0 ≤ t) :
    |burnolReflectedSourceRC t| ≤ t + 1 := by
  have h0 := burnolReflectedWindowRC_nonneg t
  have h1 := burnolReflectedWindowRC_le ht
  have hlog0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  rw [burnolReflectedSourceRC, abs_le]
  constructor <;> linarith

theorem aestronglyMeasurable_burnolReflectedSourceRC (T : ℝ) :
    AEStronglyMeasurable burnolReflectedSourceRC (volume.restrict (Ioc (0 : ℝ) T)) := by
  have hmono : volume.restrict (Ioc (0 : ℝ) T) ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono (fun x hx => mem_Ioi.mpr hx.1) le_rfl
  have hraw : (fun t : ℝ => (burnolReflectedRawSource t).re) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      burnolReflectedSourceRC := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      burnolReflectedSourceRC_ae] with t ht hrc
    rw [burnolReflectedRawSource_eq_real (mem_Ioi.mp ht), Complex.ofReal_re, hrc]
  refine AEStronglyMeasurable.congr
    ((Complex.measurable_re.comp measurable_burnolReflectedRawSource).aestronglyMeasurable)
    (hraw.filter_mono (ae_mono hmono))

theorem intervalIntegrable_burnolReflectedSourceRC {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable burnolReflectedSourceRC volume 0 T := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hT]
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => T + 1)
    (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) T) measure_Ioc_lt_top.ne)
    (aestronglyMeasurable_burnolReflectedSourceRC T) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  refine le_trans (abs_burnolReflectedSourceRC_le ht.1.le) ?_
  linarith [ht.2]

/-- **The staircase is the primitive of the right-continuous representative.** -/
theorem burnolReflectedTruncMass_eq_integral {T : ℝ} (hT : 0 ≤ T) :
    burnolReflectedTruncMass T = ∫ t in (0 : ℝ)..T, burnolReflectedSourceRC t := by
  rcases eq_or_lt_of_le hT with h | h
  · rw [← h, burnolReflectedTruncMass, intervalIntegral.integral_same]
    norm_num
  have hC : (∫ t in (0 : ℝ)..T, ((burnolReflectedSourceRC t : ℝ) : ℂ)) =
      ((∫ t in (0 : ℝ)..T, burnolReflectedSourceRC t : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT,
      integral_complex_ofReal]
  have hae : (fun t : ℝ => burnolReflectedRawSource t) =ᵐ[volume.restrict (Ioc (0 : ℝ) T)]
      fun t : ℝ => ((burnolReflectedSourceRC t : ℝ) : ℂ) := by
    have hmono : volume.restrict (Ioc (0 : ℝ) T) ≤ volume.restrict (Ioi (0 : ℝ)) :=
      Measure.restrict_mono (fun x hx => mem_Ioi.mpr hx.1) le_rfl
    have hbase : (fun t : ℝ => burnolReflectedRawSource t)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t : ℝ => ((burnolReflectedSourceRC t : ℝ) : ℂ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi,
        burnolReflectedSourceRC_ae] with t ht hrc
      rw [burnolReflectedRawSource_eq_real (mem_Ioi.mp ht), hrc]
    exact hbase.filter_mono (ae_mono hmono)
  have hint : (∫ t in (0 : ℝ)..T, burnolReflectedRawSource t) =
      ∫ t in (0 : ℝ)..T, ((burnolReflectedSourceRC t : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
    exact setIntegral_congr_ae measurableSet_Ioc ((ae_restrict_iff' measurableSet_Ioc).mp hae)
  have hmass := integral_burnolReflectedRawSource_eq_truncMass h
  rw [hint, hC] at hmass
  exact (Complex.ofReal_inj.mp hmass).symm

/-- **The reflected mass has right derivative the reflected source.** -/
theorem measurable_burnolReflectedSourceRCAux :
    Measurable fun t : ℝ => (burnolReflectedRawSource t).re :=
  Complex.measurable_re.comp measurable_burnolReflectedRawSource

theorem hasDerivWithinAt_burnolReflectedTruncMass {a : ℝ} (ha : 0 ≤ a) :
    HasDerivWithinAt burnolReflectedTruncMass (burnolReflectedSourceRC a) (Ici a) a := by
  have hmeasFilter : AEStronglyMeasurable burnolReflectedSourceRC
      (volume.restrict (Ioi a)) := by
    have hmono : volume.restrict (Ioi a) ≤ volume.restrict (Ioi (0 : ℝ)) :=
      Measure.restrict_mono (fun x hx => mem_Ioi.mpr (lt_of_le_of_lt ha hx)) le_rfl
    have hraw : (fun t : ℝ => (burnolReflectedRawSource t).re)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] burnolReflectedSourceRC := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi,
        burnolReflectedSourceRC_ae] with t ht hrc
      rw [burnolReflectedRawSource_eq_real (mem_Ioi.mp ht), Complex.ofReal_re, hrc]
    exact AEStronglyMeasurable.congr
      (measurable_burnolReflectedSourceRCAux.aestronglyMeasurable)
      (hraw.filter_mono (ae_mono hmono))
  have hftc := intervalIntegral.integral_hasDerivWithinAt_right (s := Ici a) (t := Ioi a)
    (intervalIntegrable_burnolReflectedSourceRC ha)
    ⟨Ioi a, self_mem_nhdsWithin, hmeasFilter⟩
    ((continuousWithinAt_burnolReflectedSourceRC ha).mono Ioi_subset_Ici_self)
  refine hftc.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact burnolReflectedTruncMass_eq_integral (le_trans ha hx)
  · exact burnolReflectedTruncMass_eq_integral ha

end RHTower
