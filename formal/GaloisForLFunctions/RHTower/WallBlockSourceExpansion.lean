import GaloisForLFunctions.RHTower.WallTailIntegrationByParts
import GaloisForLFunctions.HTGeometry.BlockWindowFubini

/-!
# The block source and its tail expansion

The source of the one-block equation is the shifted-line transform of a profile supported in a single
unit block,

`b(t+iσ) = −(i/2)∫_{I_m} e^{-itL} g(L) dL`,   `g = e^{σL}G`,

and the transport applied to it enters the block integral, because a bounded operator commutes with
a Bochner integral.  The frequency integral and the block integral then commute as well: the
integrand is jointly measurable — the frequency dependence is continuous and the block dependence
only measurable — and is dominated by `M‖g(L)‖` with `M` the uniform transport bound on the window.

Consequently the frequency integral of the propagated source is the block average of the *pointwise*
frequency integrals, and each of those is given by the two-fold integration by parts: after
evaluation at the block vector, the expansion reads as three operators applied to `g(L)`, two
boundary terms and one remainder whose amplitude decays quadratically.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- The block source on the shifted line: the transform of a profile supported in one unit block. -/
def blockSource (g : ℝ → X) (m : ℝ) (t : ℝ) : X :=
  (-(Complex.I) / 2 : ℂ) •
    ∫ L in Icc m (m + 1), Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ)) • g L

theorem norm_expPhase (L t : ℝ) : ‖Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ))‖ = 1 := by
  have h : -(Complex.I) * (L : ℂ) * (t : ℂ) = ((-(L * t) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem continuous_expPhase₂ :
    Continuous (fun p : ℝ × ℝ => Complex.exp (-(Complex.I) * (p.1 : ℂ) * (p.2 : ℂ))) := by
  fun_prop

theorem continuous_expPhase_freq (L : ℝ) :
    Continuous (fun t : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ))) :=
  continuous_expPhase₂.comp (continuous_const.prodMk continuous_id)

theorem continuous_expPhase_block (t : ℝ) :
    Continuous (fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ))) :=
  continuous_expPhase₂.comp (continuous_id.prodMk continuous_const)

set_option maxHeartbeats 1000000 in
/-- The inverse propagator is continuous along the shifted line. -/
theorem continuous_stripPropagatorInv_line
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous (fun t : ℝ => stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_stripPropagatorInv_line hEdiff hE hEne hσ0 hσ1 t).continuousAt

theorem continuous_wallPhaseMap
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (L : ℝ) :
    Continuous (wallPhaseMap E T σ L) :=
  (continuous_expPhase_freq L).smul
    (continuous_stripPropagatorInv_line hEdiff hE hEne hσ0 hσ1)

/-! ## The propagated block source -/

omit [CompleteSpace X] in
theorem integrableOn_expPhase_smul {g : ℝ → X} {m : ℝ}
    (hg : IntegrableOn g (Icc m (m + 1))) (t : ℝ) :
    IntegrableOn (fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ)) • g L)
      (Icc m (m + 1)) := by
  have hmeas : AEStronglyMeasurable
      (fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ)) • g L)
      (volume.restrict (Icc m (m + 1))) :=
    ((continuous_expPhase_block t).aestronglyMeasurable).smul hg.aestronglyMeasurable
  refine Integrable.mono' hg.norm hmeas (Filter.Eventually.of_forall fun L => ?_)
  rw [norm_smul, norm_expPhase, one_mul]

/-- **The inverse propagator enters the block integral.** -/
theorem stripPropagatorInv_blockSource {g : ℝ → X} {m σ : ℝ}
    (hg : IntegrableOn g (Icc m (m + 1))) (t : ℝ) :
    stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (blockSource g m t)
      = (-(Complex.I) / 2 : ℂ) • ∫ L in Icc m (m + 1), wallPhaseMap E T σ L t (g L) := by
  rw [blockSource, map_smul]
  congr 1
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrableOn_expPhase_smul hg t)]
  refine setIntegral_congr_fun measurableSet_Icc fun L _ => ?_
  rw [map_smul, wallPhaseMap, smul_apply]

/-! ## The interchange -/

set_option maxHeartbeats 1000000 in
/-- **The block integral and the frequency window commute.** -/
theorem integral_blockSource_swap
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m : ℝ} (hg : IntegrableOn g (Icc m (m + 1)))
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (blockSource g m t))
      = (-(Complex.I) / 2 : ℂ) •
          ∫ L in Icc m (m + 1), ∫ t in a..b, wallPhaseMap E T σ L t (g L) := by
  have hInvCont := continuous_stripPropagatorInv_line (T := T) hEdiff hE hEne hσ0 hσ1
  -- the uniform bound on the window
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hInvCont.continuousOn)
  -- pull the constant out
  have hstep : (∫ t in a..b,
        stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (blockSource g m t))
      = ∫ t in a..b, (-(Complex.I) / 2 : ℂ) •
          ∫ L in Icc m (m + 1), wallPhaseMap E T σ L t (g L) :=
    intervalIntegral.integral_congr fun t _ => stripPropagatorInv_blockSource hg t
  rw [hstep, intervalIntegral.integral_smul]
  congr 1
  -- Fubini
  refine (integral_swap_block_of_dominated (s := Icc m (m + 1)) hab hg
    (M := M) ?_ ?_).symm
  · -- joint measurability
    have hgfst : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1)
        ((volume.restrict (Icc m (m + 1))).prod (volume.restrict (Ioc a b))) :=
      hg.aestronglyMeasurable.comp_fst
    have hAsnd : AEStronglyMeasurable
        (fun p : ℝ × ℝ => stripPropagatorInv E T ((p.2 : ℂ) + (σ : ℂ) * Complex.I))
        ((volume.restrict (Icc m (m + 1))).prod (volume.restrict (Ioc a b))) :=
      hInvCont.aestronglyMeasurable.comp_snd
    have hev : AEStronglyMeasurable
        (fun p : ℝ × ℝ => stripPropagatorInv E T ((p.2 : ℂ) + (σ : ℂ) * Complex.I) (g p.1))
        ((volume.restrict (Icc m (m + 1))).prod (volume.restrict (Ioc a b))) :=
      ContinuousLinearMap.aestronglyMeasurable_comp₂ (ContinuousLinearMap.apply ℂ X) hgfst hAsnd
    have hph : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Complex.exp (-(Complex.I) * (p.1 : ℂ) * (p.2 : ℂ)))
        ((volume.restrict (Icc m (m + 1))).prod (volume.restrict (Ioc a b))) :=
      continuous_expPhase₂.aestronglyMeasurable
    exact hph.smul hev
  · -- the domination
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Ioc)] with p hp
    have ht : p.2 ∈ Icc a b := Ioc_subset_Icc_self hp.2
    have hop : ‖stripPropagatorInv E T ((p.2 : ℂ) + (σ : ℂ) * Complex.I) (g p.1)‖
        ≤ M * ‖g p.1‖ := by
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      exact mul_le_mul_of_nonneg_right (hM p.2 ht) (norm_nonneg _)
    show ‖wallPhaseMap E T σ p.1 p.2 (g p.1)‖ ≤ M * ‖g p.1‖
    rw [wallPhaseMap, smul_apply, norm_smul, norm_expPhase, one_mul]
    exact hop

/-! ## The expansion applied to a block vector -/

theorem intervalIntegrable_wallPhaseMap
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (L a b : ℝ) :
    IntervalIntegrable (wallPhaseMap E T σ L) volume a b :=
  (continuous_wallPhaseMap hEdiff hE hEne hσ0 hσ1 L).intervalIntegrable a b

/-- **Evaluation passes through the frequency integral.** -/
theorem integral_wallPhaseMap_apply
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (L a b : ℝ) (v : X) :
    (∫ t in a..b, wallPhaseMap E T σ L t v)
      = (∫ t in a..b, wallPhaseMap E T σ L t) v := by
  have hint : IntervalIntegrable (wallPhaseMap E T σ L) volume a b :=
    intervalIntegrable_wallPhaseMap hEdiff hE hEne hσ0 hσ1 L a b
  have := ContinuousLinearMap.intervalIntegral_comp_comm
    (ContinuousLinearMap.apply ℂ X v) hint
  simpa using this

/-- **`(18)` applied to a block vector.**  The two-fold expansion holds after evaluation, which is
how the block estimate consumes it: each term is an operator applied to the block profile. -/
theorem integral_wallPhaseMap_apply_ibp
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {L a b : ℝ}
    (hgap : ∀ t ∈ uIcc a b, 0 < wallFloor T σ t + L) (v : X) :
    (∫ t in a..b, wallPhaseMap E T σ L t v)
      = ((Complex.I : ℂ) • (wallPhaseMap E T σ L b * invFamily (wallGeneratorShift T σ L) b
            - wallPhaseMap E T σ L a * invFamily (wallGeneratorShift T σ L) a)
          + (wallPhaseMap E T σ L b * invFamilyProduct (wallGeneratorShift T σ L)
                (wallGeneratorD1 X σ) b
             - wallPhaseMap E T σ L a * invFamilyProduct (wallGeneratorShift T σ L)
                (wallGeneratorD1 X σ) a)
          - ∫ t in a..b, wallPhaseMap E T σ L t
              * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                (wallGeneratorD2 X σ) t) v := by
  rw [integral_wallPhaseMap_apply hEdiff hE hEne hσ0 hσ1 L a b v]
  congr 1
  have hbase := wall_phase_ibp_twice hEdiff hE hEne hσ0 hσ1 (L := L) hgap
  simpa using hbase

end GaloisForLFunctions.RHTower
