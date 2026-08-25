import GaloisForLFunctions.HTGeometry.CayleyBoundaryL2
import GaloisForLFunctions.RHTower.KapustinGammaToeplitzPhase

/-!
# Makarov--Poltoratski endpoint obstruction in little weak `L¹`

Kolmogorov's theorem does not assert pointwise sublinear growth of a Hilbert transform.  Its exact
conclusion is the little weak-`L¹` estimate for Poisson measure.  This file records that conclusion
and proves the upper-density endpoint contradiction used by the reciprocal-Gamma Toeplitz phase.

The proof is quantitative.  If `γ(x) - x → +∞` and `α` is nondecreasing, the identity
`γ + α = h̃` forces `h̃(x) ≥ x` on a terminal ray.  Every interval `[A,2A]` then lies in a
level set of `|h̃|`, while its standard-Cauchy mass is bounded below by a constant times `A⁻¹`.
This contradicts Kolmogorov's little weak-`L¹` tail.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Elementary lower bound for standard-Cauchy mass on a terminal dyadic interval. -/
theorem cauchyMeasure_Icc_lower (A : ℝ) (hA : 1 ≤ A) :
    ENNReal.ofReal (A / (Real.pi * (1 + 4 * A ^ 2))) ≤
      ProbabilityTheory.cauchyMeasure 0 1 (Icc A (2 * A)) := by
  rw [standardCauchyMeasure_eq_withDensity,
    MeasureTheory.withDensity_apply _ measurableSet_Icc]
  calc
    ENNReal.ofReal (A / (Real.pi * (1 + 4 * A ^ 2))) =
        ∫⁻ _x : ℝ in Icc A (2 * A),
          ENNReal.ofReal (1 / (Real.pi * (1 + 4 * A ^ 2))) := by
      rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
      rw [← ENNReal.ofReal_mul (by positivity :
        0 ≤ 1 / (Real.pi * (1 + 4 * A ^ 2)))]
      congr 1
      field_simp
      ring
    _ ≤ ∫⁻ x : ℝ in Icc A (2 * A),
          (realDensity standardCauchyWeight) x := by
      apply MeasureTheory.setLIntegral_mono
      · exact measurable_realDensity measurable_standardCauchyWeight
      · intro x hx
        rw [realDensity]
        apply ENNReal.ofReal_le_ofReal
        have hA0 : 0 ≤ A := le_trans zero_le_one hA
        have hx0 : 0 ≤ x := le_trans hA0 hx.1
        have hx2 : x ^ 2 ≤ 4 * A ^ 2 := by nlinarith [hx.2]
        have hpi : 0 < Real.pi := Real.pi_pos
        apply one_div_le_one_div_of_le
        · positivity
        · exact mul_le_mul_of_nonneg_left (by linarith) hpi.le

/-- After multiplying by the level, dyadic standard-Cauchy tails stay uniformly nonzero. -/
theorem mul_cauchyMeasure_Icc_toReal_lower (A : ℝ) (hA : 1 ≤ A) :
    1 / (5 * Real.pi) ≤
      A * (ProbabilityTheory.cauchyMeasure 0 1 (Icc A (2 * A))).toReal := by
  have hmeasure := cauchyMeasure_Icc_lower A hA
  have hfinite : ProbabilityTheory.cauchyMeasure 0 1 (Icc A (2 * A)) ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  have hreal := (ENNReal.toReal_le_toReal (by simp) hfinite).mpr hmeasure
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hmul := mul_le_mul_of_nonneg_left hreal hA0
  calc
    1 / (5 * Real.pi) ≤
        A * (A / (Real.pi * (1 + 4 * A ^ 2))) := by
      rw [div_le_iff₀ (by positivity : 0 < 5 * Real.pi)]
      rw [show
        A * (A / (Real.pi * (1 + 4 * A ^ 2))) * (5 * Real.pi) =
          5 * A ^ 2 / (1 + 4 * A ^ 2) by
            field_simp [Real.pi_ne_zero]]
      rw [le_div_iff₀ (by positivity : 0 < 1 + 4 * A ^ 2)]
      nlinarith [sq_nonneg A]
    _ ≤ A * (ProbabilityTheory.cauchyMeasure 0 1
          (Icc A (2 * A))).toReal := hmul

/-- Little weak-`L¹` tail with respect to standard Poisson/Cauchy measure. -/
def PoissonWeakL1LittleO (f : ℝ → ℝ) : Prop :=
  Tendsto (fun A : ℝ =>
    A * (ProbabilityTheory.cauchyMeasure 0 1 {x | A < |f x|}).toReal)
      atTop (nhds 0)

/-- Little weak-`L¹` tails only depend on an almost-everywhere representative. -/
theorem PoissonWeakL1LittleO.congr {f g : ℝ → ℝ}
    (hf : PoissonWeakL1LittleO f) (hfg : f =ᵐ[volume] g) :
    PoissonWeakL1LittleO g := by
  have hmeasure (A : ℝ) :
      ProbabilityTheory.cauchyMeasure 0 1 {x | A < |f x|} =
        ProbabilityTheory.cauchyMeasure 0 1 {x | A < |g x|} := by
    rw [standardCauchyMeasure_eq_withDensity]
    apply MeasureTheory.measure_congr
    exact (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
      standardCauchyWeight_pos).mpr
        (hfg.mono fun x hx => by
          apply propext
          change (A < |f x|) ↔ (A < |g x|)
          rw [hx])
  unfold PoissonWeakL1LittleO at hf ⊢
  convert hf using 1
  funext A
  rw [hmeasure A]

/-- Every uniformly bounded real phase has a little weak-`L¹` Poisson tail. -/
theorem poissonWeakL1LittleO_of_abs_le {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) : PoissonWeakL1LittleO f := by
  unfold PoissonWeakL1LittleO
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop C] with A hA
  have hempty : {x : ℝ | A < |f x|} = ∅ := by
    ext x
    change (A < |f x|) ↔ False
    exact iff_false_intro (not_lt_of_ge (le_trans (hf x) hA.le))
  rw [hempty, measure_empty]
  simp

/-- Little weak-`L¹` Poisson tails are closed under addition. -/
theorem PoissonWeakL1LittleO.add {f g : ℝ → ℝ}
    (hf : PoissonWeakL1LittleO f) (hg : PoissonWeakL1LittleO g) :
    PoissonWeakL1LittleO (fun x => f x + g x) := by
  let mu : Measure ℝ := ProbabilityTheory.cauchyMeasure 0 1
  let Tf : ℝ → ℝ := fun A => A * (mu {x | A < |f x|}).toReal
  let Tg : ℝ → ℝ := fun A => A * (mu {x | A < |g x|}).toReal
  let Tsum : ℝ → ℝ := fun A =>
    A * (mu {x | A < |f x + g x|}).toReal
  have hhalf : Tendsto (fun A : ℝ => A / 2) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hfHalf : Tendsto (fun A => Tf (A / 2)) atTop (nhds 0) := hf.comp hhalf
  have hgHalf : Tendsto (fun A => Tg (A / 2)) atTop (nhds 0) := hg.comp hhalf
  have hupper : Tendsto (fun A => 2 * (Tf (A / 2) + Tg (A / 2)))
      atTop (nhds 0) := by
    convert (hfHalf.add hgHalf).const_mul 2 using 1
    norm_num
  have hnonneg : ∀ᶠ A : ℝ in atTop, 0 ≤ Tsum A := by
    filter_upwards [eventually_ge_atTop 0] with A hA
    exact mul_nonneg hA (ENNReal.toReal_nonneg)
  have hbound : ∀ᶠ A : ℝ in atTop,
      Tsum A ≤ 2 * (Tf (A / 2) + Tg (A / 2)) := by
    filter_upwards [eventually_ge_atTop 0] with A hA
    have hset : {x : ℝ | A < |f x + g x|} ⊆
        {x | A / 2 < |f x|} ∪ {x | A / 2 < |g x|} := by
      intro x hx
      by_contra hnot
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hnot
      change A < |f x + g x| at hx
      have htri := abs_add_le (f x) (g x)
      linarith
    have hmeasureENN :
        mu {x : ℝ | A < |f x + g x|} ≤
          mu {x | A / 2 < |f x|} + mu {x | A / 2 < |g x|} :=
      (MeasureTheory.measure_mono hset).trans
        (MeasureTheory.measure_union_le _ _)
    have hfiniteF : mu {x | A / 2 < |f x|} ≠ ⊤ :=
      MeasureTheory.measure_ne_top _ _
    have hfiniteG : mu {x | A / 2 < |g x|} ≠ ⊤ :=
      MeasureTheory.measure_ne_top _ _
    have hmeasure :
        (mu {x : ℝ | A < |f x + g x|}).toReal ≤
          (mu {x | A / 2 < |f x|}).toReal +
            (mu {x | A / 2 < |g x|}).toReal := by
      calc
        (mu {x : ℝ | A < |f x + g x|}).toReal ≤
            (mu {x | A / 2 < |f x|} +
              mu {x | A / 2 < |g x|}).toReal :=
          ENNReal.toReal_mono (by simp [hfiniteF, hfiniteG]) hmeasureENN
        _ = (mu {x | A / 2 < |f x|}).toReal +
            (mu {x | A / 2 < |g x|}).toReal :=
          ENNReal.toReal_add hfiniteF hfiniteG
    have hmul := mul_le_mul_of_nonneg_left hmeasure hA
    dsimp [Tsum, Tf, Tg, mu] at hmul ⊢
    refine hmul.trans_eq ?_
    ring
  unfold PoissonWeakL1LittleO
  change Tendsto Tsum atTop (nhds 0)
  exact squeeze_zero' hnonneg hbound hupper

/-- Square-integrability for Poisson measure implies the little weak-`L¹` tail required by
Kolmogorov's endpoint criterion. -/
theorem poissonWeakL1LittleO_of_integrable_sq {f : ℝ → ℝ}
    (hf : Integrable (fun x => |f x| ^ 2)
      (ProbabilityTheory.cauchyMeasure 0 1)) :
    PoissonWeakL1LittleO f := by
  let mu : Measure ℝ := ProbabilityTheory.cauchyMeasure 0 1
  let C : ℝ := ∫ x, |f x| ^ 2 ∂mu
  let T : ℝ → ℝ := fun A => A * (mu {x | A < |f x|}).toReal
  have hC : 0 ≤ C :=
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg |f x|)
  have hupperTendsto : Tendsto (fun A : ℝ => C / A) atTop (nhds 0) :=
    tendsto_id.const_div_atTop C
  have hnonneg : ∀ᶠ A : ℝ in atTop, 0 ≤ T A := by
    filter_upwards [eventually_ge_atTop 0] with A hA
    exact mul_nonneg hA ENNReal.toReal_nonneg
  have hbound : ∀ᶠ A : ℝ in atTop, T A ≤ C / A := by
    filter_upwards [eventually_gt_atTop 0] with A hA
    have hset : {x : ℝ | A < |f x|} ⊆ {x | A ^ 2 ≤ |f x| ^ 2} := by
      intro x hx
      change A < |f x| at hx
      change A ^ 2 ≤ |f x| ^ 2
      exact (sq_le_sq₀ hA.le (abs_nonneg _)).mpr hx.le
    have hmeasure :
        (mu {x : ℝ | A < |f x|}).toReal ≤
          (mu {x | A ^ 2 ≤ |f x| ^ 2}).toReal := by
      exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
        (MeasureTheory.measure_mono hset)
    have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
      (μ := mu) (f := fun x => |f x| ^ 2)
      (Filter.Eventually.of_forall fun x => sq_nonneg |f x|) hf (A ^ 2)
    rw [Measure.real_def] at hmark
    change A ^ 2 * (mu {x | A ^ 2 ≤ |f x| ^ 2}).toReal ≤ C at hmark
    have hmulMeasure := mul_le_mul_of_nonneg_left hmeasure hA.le
    dsimp [T]
    refine hmulMeasure.trans ?_
    rw [le_div_iff₀ hA]
    nlinarith [hmark]
  unfold PoissonWeakL1LittleO
  change Tendsto T atTop (nhds 0)
  exact squeeze_zero' hnonneg hbound hupperTendsto

/-- Exact phase-coordinate output of the Smirnov basic criterion needed by the upper-density
argument: a nondecreasing inner phase and a Hilbert phase satisfying Kolmogorov's little weak-`L¹`
estimate.  An almost-everywhere phase identity may always be made pointwise by changing the
Hilbert-phase representative on its null exceptional set. -/
structure SmirnovToeplitzWeakPhaseWitness (γ : ℝ → ℝ) where
  innerPhase : ℝ → ℝ
  outerHilbertPhase : ℝ → ℝ
  innerPhase_monotone : Monotone innerPhase
  phase_balance : ∀ x, γ x + innerPhase x = outerHilbertPhase x
  outerHilbertPhase_weakL1LittleO : PoissonWeakL1LittleO outerHilbertPhase

/-- A bounded phase is itself an outer weak-phase witness, with no inner winding. -/
noncomputable def boundedSmirnovToeplitzWeakPhaseWitness
    (b : ℝ → ℝ) (C : ℝ) (hb : ∀ x, |b x| ≤ C) :
    SmirnovToeplitzWeakPhaseWitness b where
  innerPhase := 0
  outerHilbertPhase := b
  innerPhase_monotone := monotone_const
  phase_balance := by intro x; simp
  outerHilbertPhase_weakL1LittleO := poissonWeakL1LittleO_of_abs_le hb

/-- Toeplitz weak-phase witnesses add under multiplication of their unimodular symbols. -/
noncomputable def SmirnovToeplitzWeakPhaseWitness.add
    {γ δ : ℝ → ℝ} (Wγ : SmirnovToeplitzWeakPhaseWitness γ)
    (Wδ : SmirnovToeplitzWeakPhaseWitness δ) :
    SmirnovToeplitzWeakPhaseWitness (fun x => γ x + δ x) where
  innerPhase := fun x => Wγ.innerPhase x + Wδ.innerPhase x
  outerHilbertPhase := fun x => Wγ.outerHilbertPhase x + Wδ.outerHilbertPhase x
  innerPhase_monotone := Wγ.innerPhase_monotone.add Wδ.innerPhase_monotone
  phase_balance := by
    intro x
    rw [show γ x + δ x + (Wγ.innerPhase x + Wδ.innerPhase x) =
      (γ x + Wγ.innerPhase x) + (δ x + Wδ.innerPhase x) by ring,
      Wγ.phase_balance, Wδ.phase_balance]
  outerHilbertPhase_weakL1LittleO :=
    Wγ.outerHilbertPhase_weakL1LittleO.add Wδ.outerHilbertPhase_weakL1LittleO

/-- Reparameterize a weak-phase witness by a pointwise equal real phase. -/
noncomputable def SmirnovToeplitzWeakPhaseWitness.congr
    {γ δ : ℝ → ℝ} (W : SmirnovToeplitzWeakPhaseWitness γ)
    (h : ∀ x, γ x = δ x) : SmirnovToeplitzWeakPhaseWitness δ where
  innerPhase := W.innerPhase
  outerHilbertPhase := W.outerHilbertPhase
  innerPhase_monotone := W.innerPhase_monotone
  phase_balance := by intro x; rw [← h x, W.phase_balance]
  outerHilbertPhase_weakL1LittleO := W.outerHilbertPhase_weakL1LittleO

/-- Exact bounded-phase multiplier witness at exponent `p = 1/2`.  The fourth Blaschke phase is
the monotone inner term; the bounded residual has a little weak-`L¹` tail. -/
noncomputable def boundedPhaseBlaschkeFourWeakWitness
    (b : ℝ → ℝ) (C : ℝ) (hb : ∀ x, |b x| ≤ C) :
    SmirnovToeplitzWeakPhaseWitness
      (fun x => -8 * Real.arctan x + 2 * b x) where
  innerPhase := fun x => 8 * Real.arctan x
  outerHilbertPhase := fun x => 2 * b x
  innerPhase_monotone := ((show StrictMono Real.arctan from
    fun _ _ h => Real.arctan_lt_arctan_iff.mpr h).const_mul
      (by norm_num : (0 : ℝ) < 8)).monotone
  phase_balance := by intro x; ring
  outerHilbertPhase_weakL1LittleO := by
    apply poissonWeakL1LittleO_of_abs_le (C := 2 * C)
    intro x
    rw [abs_mul]
    simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
      mul_le_mul_of_nonneg_left (hb x) (by norm_num : (0 : ℝ) ≤ 2)

/-- Makarov--Poltoratski upper-density endpoint contradiction at `κ = 0`. -/
theorem not_smirnovToeplitzWeakPhaseWitness_of_sub_id_tendsto_atTop
    {γ : ℝ → ℝ} (hgrowth : Tendsto (fun x => γ x - x) atTop atTop) :
    ¬ Nonempty (SmirnovToeplitzWeakPhaseWitness γ) := by
  rintro ⟨W⟩
  let c : ℝ := 1 / (10 * Real.pi)
  have hc : 0 < c := by positivity
  have hhalf : Tendsto (fun A : ℝ => A / 2) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hweak := W.outerHilbertPhase_weakL1LittleO.comp hhalf
  have hweakSmall : ∀ᶠ A : ℝ in atTop,
      (A / 2) *
          (ProbabilityTheory.cauchyMeasure 0 1
            {x | A / 2 < |W.outerHilbertPhase x|}).toReal < c :=
    hweak.eventually (Iio_mem_nhds hc)
  have hgrowthLower : ∀ᶠ x : ℝ in atTop,
      -W.innerPhase 0 ≤ γ x - x :=
    hgrowth.eventually (eventually_ge_atTop (-W.innerPhase 0))
  obtain ⟨R, hR⟩ := eventually_atTop.1 hgrowthLower
  have hlarge : ∀ᶠ A : ℝ in atTop, max 1 R ≤ A :=
    eventually_ge_atTop (max 1 R)
  obtain ⟨A, hAR, hsmall⟩ := (hlarge.and hweakSmall).exists
  have hA : 1 ≤ A := le_trans (le_max_left 1 R) hAR
  have hsubset : Icc A (2 * A) ⊆
      {x | A / 2 < |W.outerHilbertPhase x|} := by
    intro x hx
    have hxR : R ≤ x := le_trans (le_trans (le_max_right 1 R) hAR) hx.1
    have hx0 : 0 ≤ x := le_trans (le_trans zero_le_one hA) hx.1
    have hinner : W.innerPhase 0 ≤ W.innerPhase x :=
      W.innerPhase_monotone hx0
    have hphase := W.phase_balance x
    have houter : x ≤ W.outerHilbertPhase x := by
      linarith [hR x hxR]
    change A / 2 < |W.outerHilbertPhase x|
    rw [abs_of_nonneg (le_trans hx0 houter)]
    linarith [hx.1]
  have hmeasure :
      (ProbabilityTheory.cauchyMeasure 0 1 (Icc A (2 * A))).toReal ≤
        (ProbabilityTheory.cauchyMeasure 0 1
          {x | A / 2 < |W.outerHilbertPhase x|}).toReal := by
    apply (ENNReal.toReal_le_toReal
      (MeasureTheory.measure_ne_top _ _)
      (MeasureTheory.measure_ne_top _ _)).mpr
    exact MeasureTheory.measure_mono hsubset
  have hmulMeasure := mul_le_mul_of_nonneg_left hmeasure (by positivity : 0 ≤ A / 2)
  have hlower := mul_cauchyMeasure_Icc_toReal_lower A hA
  have hcLower : c ≤
      (A / 2) *
        (ProbabilityTheory.cauchyMeasure 0 1
          {x | A / 2 < |W.outerHilbertPhase x|}).toReal := by
    calc
      c = (1 / 2) * (1 / (5 * Real.pi)) := by
        dsimp [c]
        field_simp [Real.pi_ne_zero]
        norm_num
      _ ≤ (1 / 2) *
          (A * (ProbabilityTheory.cauchyMeasure 0 1
            (Icc A (2 * A))).toReal) :=
        mul_le_mul_of_nonneg_left hlower (by norm_num)
      _ = (A / 2) *
          (ProbabilityTheory.cauchyMeasure 0 1
            (Icc A (2 * A))).toReal := by ring
      _ ≤ (A / 2) *
          (ProbabilityTheory.cauchyMeasure 0 1
            {x | A / 2 < |W.outerHilbertPhase x|}).toReal := hmulMeasure
  exact (not_lt_of_ge hcLower) hsmall

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Exact weak-`L¹` form of Kapustin's bounded-phase collision.  The only analytic input is the
basic-criterion witness for the bounded gauge's phase-reflection symbol. -/
noncomputable def kapustinToeplitzWeakPhaseWitness_of_boundedCancellation
    (psi b : ℝ → ℝ) (C : ℝ)
    (hpsi : SmirnovToeplitzWeakPhaseWitness (fun x => -2 * psi x))
    (hb : ∀ x, |b x| ≤ C)
    (hphase : ∀ x,
      kapustinToeplitzPhase x =
        -2 * psi x + (-8 * Real.arctan x + 2 * b x)) :
    SmirnovToeplitzWeakPhaseWitness kapustinToeplitzPhase :=
  (hpsi.add (boundedPhaseBlaschkeFourWeakWitness b C hb)).congr
    fun x => (hphase x).symm

/-- Exact little weak-`L¹` upper-density obstruction for the reciprocal-Gamma phase. -/
theorem noSmirnovToeplitzWeakPhaseWitness_kapustinToeplitzPhase :
    ¬ Nonempty (SmirnovToeplitzWeakPhaseWitness kapustinToeplitzPhase) :=
  not_smirnovToeplitzWeakPhaseWitness_of_sub_id_tendsto_atTop
    tendsto_kapustinToeplitzPhase_sub_id_atTop

end RHTower
