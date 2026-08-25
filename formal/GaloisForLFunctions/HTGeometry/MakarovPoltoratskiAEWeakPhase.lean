import GaloisForLFunctions.HTGeometry.MakarovPoltoratskiWeakPhase

/-!
# Makarov--Poltoratski endpoint obstruction for almost-everywhere phase identities

Boundary factorizations naturally identify phases only almost everywhere.  This file records the
matching weak-phase witness and proves that the upper-density contradiction needs no pointwise
choice of a phase representative.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Almost-everywhere phase-coordinate output of the Smirnov basic criterion. -/
structure AESmirnovToeplitzWeakPhaseWitness (γ : ℝ → ℝ) where
  innerPhase : ℝ → ℝ
  outerHilbertPhase : ℝ → ℝ
  innerPhase_monotone : Monotone innerPhase
  phase_balance_ae : (fun x => γ x + innerPhase x) =ᵐ[volume] outerHilbertPhase
  outerHilbertPhase_weakL1LittleO : PoissonWeakL1LittleO outerHilbertPhase

/-- A pointwise weak-phase witness is, in particular, an almost-everywhere one. -/
noncomputable def SmirnovToeplitzWeakPhaseWitness.toAE
    {γ : ℝ → ℝ} (W : SmirnovToeplitzWeakPhaseWitness γ) :
    AESmirnovToeplitzWeakPhaseWitness γ where
  innerPhase := W.innerPhase
  outerHilbertPhase := W.outerHilbertPhase
  innerPhase_monotone := W.innerPhase_monotone
  phase_balance_ae := Filter.Eventually.of_forall W.phase_balance
  outerHilbertPhase_weakL1LittleO := W.outerHilbertPhase_weakL1LittleO

/-- A bounded phase is an a.e. weak-phase witness with zero inner winding. -/
noncomputable def boundedAESmirnovToeplitzWeakPhaseWitness
    (b : ℝ → ℝ) (C : ℝ) (hb : ∀ x, |b x| ≤ C) :
    AESmirnovToeplitzWeakPhaseWitness b :=
  (boundedSmirnovToeplitzWeakPhaseWitness b C hb).toAE

/-- Almost-everywhere weak-phase witnesses add under multiplication of symbols. -/
noncomputable def AESmirnovToeplitzWeakPhaseWitness.add
    {γ δ : ℝ → ℝ} (Wγ : AESmirnovToeplitzWeakPhaseWitness γ)
    (Wδ : AESmirnovToeplitzWeakPhaseWitness δ) :
    AESmirnovToeplitzWeakPhaseWitness (fun x => γ x + δ x) where
  innerPhase := fun x => Wγ.innerPhase x + Wδ.innerPhase x
  outerHilbertPhase := fun x => Wγ.outerHilbertPhase x + Wδ.outerHilbertPhase x
  innerPhase_monotone := Wγ.innerPhase_monotone.add Wδ.innerPhase_monotone
  phase_balance_ae := by
    filter_upwards [Wγ.phase_balance_ae, Wδ.phase_balance_ae] with x hγ hδ
    rw [show γ x + δ x + (Wγ.innerPhase x + Wδ.innerPhase x) =
      (γ x + Wγ.innerPhase x) + (δ x + Wδ.innerPhase x) by ring, hγ, hδ]
  outerHilbertPhase_weakL1LittleO :=
    Wγ.outerHilbertPhase_weakL1LittleO.add Wδ.outerHilbertPhase_weakL1LittleO

/-- Reparameterize an a.e. witness by an almost-everywhere equal real phase. -/
noncomputable def AESmirnovToeplitzWeakPhaseWitness.congr
    {γ δ : ℝ → ℝ} (W : AESmirnovToeplitzWeakPhaseWitness γ)
    (h : γ =ᵐ[volume] δ) : AESmirnovToeplitzWeakPhaseWitness δ where
  innerPhase := W.innerPhase
  outerHilbertPhase := W.outerHilbertPhase
  innerPhase_monotone := W.innerPhase_monotone
  phase_balance_ae := by
    filter_upwards [W.phase_balance_ae, h] with x hphase hγδ
    rw [← hγδ, hphase]
  outerHilbertPhase_weakL1LittleO := W.outerHilbertPhase_weakL1LittleO

/-- Makarov--Poltoratski upper-density contradiction needs only an a.e. phase balance. -/
theorem not_aeSmirnovToeplitzWeakPhaseWitness_of_sub_id_tendsto_atTop
    {γ : ℝ → ℝ} (hgrowth : Tendsto (fun x => γ x - x) atTop atTop) :
    ¬ Nonempty (AESmirnovToeplitzWeakPhaseWitness γ) := by
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
  have hsubsetVolume : Icc A (2 * A) ≤ᵐ[volume]
      {x | A / 2 < |W.outerHilbertPhase x|} := by
    filter_upwards [W.phase_balance_ae] with x hphase hx
    have hxR : R ≤ x := le_trans (le_trans (le_max_right 1 R) hAR) hx.1
    have hx0 : 0 ≤ x := le_trans (le_trans zero_le_one hA) hx.1
    have hinner : W.innerPhase 0 ≤ W.innerPhase x :=
      W.innerPhase_monotone hx0
    have houter : x ≤ W.outerHilbertPhase x := by
      linarith [hR x hxR]
    change A / 2 < |W.outerHilbertPhase x|
    rw [abs_of_nonneg (le_trans hx0 houter)]
    linarith [hx.1]
  have hsubset : Icc A (2 * A) ≤ᵐ[ProbabilityTheory.cauchyMeasure 0 1]
      {x | A / 2 < |W.outerHilbertPhase x|} := by
    rw [standardCauchyMeasure_eq_withDensity]
    exact (MeasureTheory.withDensity_absolutelyContinuous volume _).ae_le
      hsubsetVolume
  have hmeasure :
      (ProbabilityTheory.cauchyMeasure 0 1 (Icc A (2 * A))).toReal ≤
        (ProbabilityTheory.cauchyMeasure 0 1
          {x | A / 2 < |W.outerHilbertPhase x|}).toReal := by
    apply (ENNReal.toReal_le_toReal
      (MeasureTheory.measure_ne_top _ _)
      (MeasureTheory.measure_ne_top _ _)).mpr
    exact MeasureTheory.measure_mono_ae hsubset
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

/-- Exact a.e. weak-phase obstruction for the reciprocal-Gamma Toeplitz phase. -/
theorem noAESmirnovToeplitzWeakPhaseWitness_kapustinToeplitzPhase :
    ¬ Nonempty (AESmirnovToeplitzWeakPhaseWitness kapustinToeplitzPhase) :=
  not_aeSmirnovToeplitzWeakPhaseWitness_of_sub_id_tendsto_atTop
    tendsto_kapustinToeplitzPhase_sub_id_atTop

end RHTower
