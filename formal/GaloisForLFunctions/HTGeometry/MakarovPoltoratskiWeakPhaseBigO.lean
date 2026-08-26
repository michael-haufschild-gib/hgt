import GaloisForLFunctions.HTGeometry.MakarovPoltoratskiAEWeakPhase

/-!
# Strong-growth Makarov--Poltoratski endpoint with weak `L¹` big-O

For phases growing faster than every linear function, the endpoint contradiction needs only a
finite weak-`L¹` bound.  Little-o is unnecessary.  This is the form compatible with boundary
Herglotz transforms of finite measures, including singular mass.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Weak-`L¹` big-O tail with respect to standard Poisson/Cauchy measure. -/
def PoissonWeakL1BigO (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ A : ℝ in atTop,
    A * (cauchyMeasure 0 1 {x | A < |f x|}).toReal ≤ C

/-- Weak-`L¹` big-O only depends on the a.e. representative. -/
theorem PoissonWeakL1BigO.congr {f g : ℝ → ℝ}
    (hf : PoissonWeakL1BigO f) (hfg : f =ᵐ[volume] g) :
    PoissonWeakL1BigO g := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  have hmeasure (A : ℝ) :
      cauchyMeasure 0 1 {x | A < |f x|} =
        cauchyMeasure 0 1 {x | A < |g x|} := by
    rw [standardCauchyMeasure_eq_withDensity]
    apply MeasureTheory.measure_congr
    exact (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
      standardCauchyWeight_pos).mpr
        (hfg.mono fun x hx => by
          apply propext
          change (A < |f x|) ↔ (A < |g x|)
          rw [hx])
  filter_upwards [hC] with A hA
  rwa [← hmeasure A]

/-- Weak-`L¹` big-O is closed under addition. -/
theorem PoissonWeakL1BigO.add {f g : ℝ → ℝ}
    (hf : PoissonWeakL1BigO f) (hg : PoissonWeakL1BigO g) :
    PoissonWeakL1BigO (fun x => f x + g x) := by
  obtain ⟨Cf, hf⟩ := hf
  obtain ⟨Cg, hg⟩ := hg
  refine ⟨2 * (Cf + Cg), ?_⟩
  have hhalf : Tendsto (fun A : ℝ => A / 2) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hfHalf := hhalf.eventually hf
  have hgHalf := hhalf.eventually hg
  filter_upwards [eventually_ge_atTop 0, hfHalf, hgHalf] with A hA hfA hgA
  have hset : {x : ℝ | A < |f x + g x|} ⊆
      {x | A / 2 < |f x|} ∪ {x | A / 2 < |g x|} := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hnot
    change A < |f x + g x| at hx
    linarith [abs_add_le (f x) (g x)]
  have hmeasureENN :
      cauchyMeasure 0 1 {x : ℝ | A < |f x + g x|} ≤
        cauchyMeasure 0 1 {x | A / 2 < |f x|} +
          cauchyMeasure 0 1 {x | A / 2 < |g x|} :=
    (MeasureTheory.measure_mono hset).trans (MeasureTheory.measure_union_le _ _)
  have hfiniteF : cauchyMeasure 0 1 {x | A / 2 < |f x|} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  have hfiniteG : cauchyMeasure 0 1 {x | A / 2 < |g x|} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  have hmeasure :
      (cauchyMeasure 0 1 {x : ℝ | A < |f x + g x|}).toReal ≤
        (cauchyMeasure 0 1 {x | A / 2 < |f x|}).toReal +
          (cauchyMeasure 0 1 {x | A / 2 < |g x|}).toReal := by
    calc
      _ ≤ (cauchyMeasure 0 1 {x | A / 2 < |f x|} +
          cauchyMeasure 0 1 {x | A / 2 < |g x|}).toReal :=
        ENNReal.toReal_mono (by simp [hfiniteF, hfiniteG]) hmeasureENN
      _ = _ := ENNReal.toReal_add hfiniteF hfiniteG
  have hmul := mul_le_mul_of_nonneg_left hmeasure hA
  calc
    A * (cauchyMeasure 0 1 {x : ℝ | A < |f x + g x|}).toReal ≤
        A * ((cauchyMeasure 0 1 {x | A / 2 < |f x|}).toReal +
          (cauchyMeasure 0 1 {x | A / 2 < |g x|}).toReal) := hmul
    _ = 2 * ((A / 2) * (cauchyMeasure 0 1 {x | A / 2 < |f x|}).toReal +
        (A / 2) * (cauchyMeasure 0 1 {x | A / 2 < |g x|}).toReal) := by ring
    _ ≤ 2 * (Cf + Cg) := by linarith

/-- Weak-`L¹` big-O is invariant under negation. -/
theorem PoissonWeakL1BigO.neg {f : ℝ → ℝ}
    (hf : PoissonWeakL1BigO f) : PoissonWeakL1BigO (fun x => -f x) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  filter_upwards [hC] with A hA
  simpa only [abs_neg] using hA

/-- Weak-`L¹` big-O is closed under subtraction. -/
theorem PoissonWeakL1BigO.sub {f g : ℝ → ℝ}
    (hf : PoissonWeakL1BigO f) (hg : PoissonWeakL1BigO g) :
    PoissonWeakL1BigO (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Almost-everywhere phase-coordinate output with a finite weak-`L¹` outer tail. -/
structure AESmirnovToeplitzWeakPhaseBigOWitness (γ : ℝ → ℝ) where
  innerPhase : ℝ → ℝ
  outerHilbertPhase : ℝ → ℝ
  innerPhase_monotone : Monotone innerPhase
  phase_balance_ae : (fun x => γ x + innerPhase x) =ᵐ[volume] outerHilbertPhase
  outerHilbertPhase_weakL1BigO : PoissonWeakL1BigO outerHilbertPhase

/-- Kolmogorov little weak-`L¹` implies a finite weak-`L¹` bound. -/
theorem PoissonWeakL1LittleO.bigO {f : ℝ → ℝ}
    (hf : PoissonWeakL1LittleO f) : PoissonWeakL1BigO f := by
  refine ⟨1, ?_⟩
  exact hf.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))

/-- Every a.e. little weak-phase witness is a weak-big-O witness. -/
noncomputable def AESmirnovToeplitzWeakPhaseWitness.toBigO
    {γ : ℝ → ℝ} (W : AESmirnovToeplitzWeakPhaseWitness γ) :
    AESmirnovToeplitzWeakPhaseBigOWitness γ where
  innerPhase := W.innerPhase
  outerHilbertPhase := W.outerHilbertPhase
  innerPhase_monotone := W.innerPhase_monotone
  phase_balance_ae := W.phase_balance_ae
  outerHilbertPhase_weakL1BigO := W.outerHilbertPhase_weakL1LittleO.bigO

/-- A superlinear phase cannot admit a monotone-inner plus weak-`L¹`-big-O decomposition. -/
theorem not_aeSmirnovToeplitzWeakPhaseBigOWitness_of_ratio_tendsto_atTop
    {γ : ℝ → ℝ} (hgrowth : Tendsto (fun x => γ x / x) atTop atTop) :
    ¬ Nonempty (AESmirnovToeplitzWeakPhaseBigOWitness γ) := by
  rintro ⟨W⟩
  obtain ⟨C, hweak⟩ := W.outerHilbertPhase_weakL1BigO
  let M : ℝ := 5 * Real.pi * (|C| + 1)
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hthreshold : Tendsto (fun A : ℝ => M * A) atTop atTop :=
    tendsto_id.const_mul_atTop hM
  have hweakM : ∀ᶠ A : ℝ in atTop,
      (M * A) *
        (cauchyMeasure 0 1 {x | M * A < |W.outerHilbertPhase x|}).toReal ≤ C :=
    hthreshold.eventually hweak
  have hgrowthLower : ∀ᶠ x : ℝ in atTop, M + 2 ≤ γ x / x :=
    hgrowth.eventually (eventually_ge_atTop (M + 2))
  obtain ⟨R, hR⟩ := eventually_atTop.1 hgrowthLower
  have hlarge : ∀ᶠ A : ℝ in atTop, max (max 1 R) (-W.innerPhase 0) ≤ A :=
    eventually_ge_atTop (max (max 1 R) (-W.innerPhase 0))
  obtain ⟨A, hAall, hweakA⟩ := (hlarge.and hweakM).exists
  have hA : 1 ≤ A := le_trans (le_max_left 1 R) (le_trans (le_max_left _ _) hAall)
  have hAR : R ≤ A := le_trans (le_max_right 1 R) (le_trans (le_max_left _ _) hAall)
  have hAinner : -W.innerPhase 0 ≤ A := le_trans (le_max_right _ _) hAall
  have hsubsetVolume : Icc A (2 * A) ≤ᵐ[volume]
      {x | M * A < |W.outerHilbertPhase x|} := by
    filter_upwards [W.phase_balance_ae] with x hphase hx
    have hxA : A ≤ x := hx.1
    have hxR : R ≤ x := hAR.trans hxA
    have hxpos : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hA) hxA
    have hratio : M + 2 ≤ γ x / x := hR x hxR
    have hgamma : (M + 2) * x ≤ γ x := by
      rwa [le_div_iff₀ hxpos] at hratio
    have hinner : W.innerPhase 0 ≤ W.innerPhase x :=
      W.innerPhase_monotone (le_trans (by linarith [hA]) hxA)
    have houter : (M + 1) * x ≤ W.outerHilbertPhase x := by
      rw [← hphase]
      have hzero : 0 ≤ x + W.innerPhase 0 := by linarith
      linarith
    have houterPos : 0 ≤ W.outerHilbertPhase x :=
      le_trans (mul_nonneg (by positivity) hxpos.le) houter
    change M * A < |W.outerHilbertPhase x|
    rw [abs_of_nonneg houterPos]
    have hMA : M * A ≤ M * x := mul_le_mul_of_nonneg_left hxA hM.le
    nlinarith
  have hsubset : Icc A (2 * A) ≤ᵐ[cauchyMeasure 0 1]
      {x | M * A < |W.outerHilbertPhase x|} := by
    rw [standardCauchyMeasure_eq_withDensity]
    exact (MeasureTheory.withDensity_absolutelyContinuous volume _).ae_le
      hsubsetVolume
  have hmeasure :
      (cauchyMeasure 0 1 (Icc A (2 * A))).toReal ≤
        (cauchyMeasure 0 1
          {x | M * A < |W.outerHilbertPhase x|}).toReal := by
    apply (ENNReal.toReal_le_toReal
      (MeasureTheory.measure_ne_top _ _)
      (MeasureTheory.measure_ne_top _ _)).mpr
    exact MeasureTheory.measure_mono_ae hsubset
  have hmulMeasure := mul_le_mul_of_nonneg_left hmeasure
    (mul_nonneg hM.le (le_trans zero_le_one hA))
  have hlower := mul_cauchyMeasure_Icc_toReal_lower A hA
  have hcontrary : C < (M * A) *
      (cauchyMeasure 0 1
        {x | M * A < |W.outerHilbertPhase x|}).toReal := by
    calc
      C < |C| + 1 := by linarith [le_abs_self C]
      _ = M * (1 / (5 * Real.pi)) := by
        dsimp [M]
        field_simp [Real.pi_ne_zero]
      _ ≤ M * (A * (cauchyMeasure 0 1 (Icc A (2 * A))).toReal) :=
        mul_le_mul_of_nonneg_left hlower hM.le
      _ = (M * A) * (cauchyMeasure 0 1 (Icc A (2 * A))).toReal := by ring
      _ ≤ (M * A) *
          (cauchyMeasure 0 1
            {x | M * A < |W.outerHilbertPhase x|}).toReal := hmulMeasure
  exact (not_lt_of_ge hweakA) hcontrary

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The reciprocal-Gamma Toeplitz phase grows faster than every linear function. -/
theorem tendsto_kapustinToeplitzPhase_div_id_atTop :
    Tendsto (fun x => kapustinToeplitzPhase x / x) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  have hratio : ∀ᶠ x : ℝ in atTop,
      1 ≤ kapustinToeplitzPhase x / (x * Real.log x) :=
    tendsto_kapustinToeplitzPhase_ratio.eventually
      (Ici_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hlog : ∀ᶠ x : ℝ in atTop, max B 0 ≤ Real.log x :=
    (tendsto_atTop.1 Real.tendsto_log_atTop) (max B 0)
  have hxone : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  filter_upwards [hratio, hlog, hxone] with x hr hl hx
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hlog0 : 0 ≤ Real.log x := (le_max_right B 0).trans hl
  have hmul := mul_le_mul_of_nonneg_right hr hlog0
  have hid :
      (kapustinToeplitzPhase x / (x * Real.log x)) * Real.log x =
        kapustinToeplitzPhase x / x := by
    field_simp [hxpos.ne', hlogpos.ne']
  rw [hid] at hmul
  exact (le_max_left B 0).trans (hl.trans (by simpa only [one_mul] using hmul))

/-- Reciprocal-Gamma superlinear growth excludes even a weak-big-O phase witness. -/
theorem noAESmirnovToeplitzWeakPhaseBigOWitness_kapustinToeplitzPhase :
    ¬ Nonempty (AESmirnovToeplitzWeakPhaseBigOWitness kapustinToeplitzPhase) :=
  not_aeSmirnovToeplitzWeakPhaseBigOWitness_of_ratio_tendsto_atTop
    tendsto_kapustinToeplitzPhase_div_id_atTop

end RHTower
