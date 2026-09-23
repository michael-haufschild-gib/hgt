import GaloisForLFunctions.RHTower.Sieve.MaynardCommonModePhaseDerivativeReserve
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientPacketInterval
import GaloisForLFunctions.RHTower.Sieve.MaynardWeightedSpatialMellinL2

/-!
# Spatial boundary of Route T's extracted phase

After common-mode extraction, the surviving point-mass phase is exactly a unit-cell Mellin
packet at real part zero.  Thus the available spatial `L²` theorem applies without any new
analytic assumption.  Its unavoidable prefactor is the physical-base length `x` itself.
The paired-kernel packet used below the seam has a width-dependent coefficient that removes this
factor; the bare phase does not.  Consequently a phase continuation must first produce an
anchored phase difference (or an equivalent correlation) with one reciprocal physical-base gain.
This is a sharp positive target, not a claim that generic `L²` closes the phase window.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set

/-- The point-mass object left by common-mode phase extraction on an integer ordinate shell. -/
def routeTPointMassPhasePacket (a : ℝ → ℂ) (lambda : ℝ) (lo hi : ℕ) : ℂ :=
  ∫ y : ℝ in (lo : ℝ)..(hi : ℝ),
    a y * (lambda : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1)

/-- The interval tiling needed here is proved locally from the foundational range tiling, so the
phase boundary remains independent of the natural-shell bridge and its unrelated dependencies. -/
private theorem intervalIntegral_sum_Ico_unitCells_eq_phase
    {f : ℝ → ℂ} (hf : Continuous f) {lo hi : ℕ} (hlohi : lo ≤ hi) :
    (∫ v : ℝ in (0 : ℝ)..1, ∑ m ∈ Finset.Ico lo hi, f ((m : ℝ) + v)) =
      ∫ y : ℝ in (lo : ℝ)..(hi : ℝ), f y := by
  have hsum : (fun v : ℝ => ∑ m ∈ Finset.Ico lo hi, f ((m : ℝ) + v)) =
      fun v : ℝ =>
        (∑ m ∈ Finset.range hi, f ((m : ℝ) + v)) -
          ∑ m ∈ Finset.range lo, f ((m : ℝ) + v) := by
    funext v
    exact Finset.sum_Ico_eq_sub (fun m => f ((m : ℝ) + v)) hlohi
  rw [hsum, intervalIntegral.integral_sub]
  · rw [intervalIntegral_sum_range_unitCells_eq hf hi,
      intervalIntegral_sum_range_unitCells_eq hf lo]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (0 : ℝ) (lo : ℝ))
      (hf.intervalIntegrable (lo : ℝ) (hi : ℝ))]
    ring
  · exact (continuous_finsetSum (Finset.range hi) fun m _ =>
      hf.comp (continuous_const.add continuous_id)).intervalIntegrable 0 1
  · exact (continuous_finsetSum (Finset.range lo) fun m _ =>
      hf.comp (continuous_const.add continuous_id)).intervalIntegrable 0 1

/-- The extracted phase is exactly the zero-real-part unit-cell Mellin packet.  This exposes the
full physical-base factor in its spatial energy, rather than hiding it in a discretisation. -/
theorem routeTPointMassPhasePacket_eq_unitCellMellinPacket
    {a : ℝ → ℂ} (ha : Continuous a) {lambda : ℝ} (hlambda : 0 < lambda)
    {lo hi : ℕ} (hlohi : lo ≤ hi) :
    routeTPointMassPhasePacket a lambda lo hi =
      maynardUnitCellMellinPacket (Finset.Ico lo hi)
        (fun m v => a ((m : ℝ) + v)) 0 lambda := by
  have hphase : ∀ y : ℝ,
      (lambda : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1) =
        (lambda : ℂ) ^ (((0 : ℝ) : ℂ) + (y : ℝ) * Complex.I) := by
    intro y
    congr 1
    push_cast
    ring
  have hpower : Continuous fun y : ℝ =>
      (lambda : ℂ) ^ (((0 : ℝ) : ℂ) + (y : ℝ) * Complex.I) := by
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (by exact_mod_cast hlambda.ne')
  have htiling := intervalIntegral_sum_Ico_unitCells_eq_phase
    (ha.mul hpower) hlohi
  simp only [routeTPointMassPhasePacket, maynardUnitCellMellinPacket,
    maynardUnitCellMellinIntegrand]
  calc
    (∫ y : ℝ in (lo : ℝ)..(hi : ℝ),
        a y * (lambda : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1)) =
        ∫ y : ℝ in (lo : ℝ)..(hi : ℝ),
          a y * (lambda : ℂ) ^ (((0 : ℝ) : ℂ) + (y : ℝ) * Complex.I) := by
            apply intervalIntegral.integral_congr
            intro y hy
            change a y * (lambda : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1) =
              a y * (lambda : ℂ) ^ (((0 : ℝ) : ℂ) + (y : ℝ) * Complex.I)
            rw [hphase]
    _ = ∫ v : ℝ in (0 : ℝ)..1, ∑ m ∈ Finset.Ico lo hi,
          a ((m : ℝ) + v) *
            (lambda : ℂ) ^ (((0 : ℝ) : ℂ) + (((m : ℝ) + v : ℝ) : ℂ) * Complex.I) := by
          simpa only [Pi.mul_apply] using htiling.symm

/-- Phase extraction is covariant under a global source phase.  Every current common-mode
lower bound is a norm lower bound, hence invariant under this gauge. -/
theorem routeTPointMassPhasePacket_const_mul
    (c : ℂ) (a : ℝ → ℂ) (lambda : ℝ) (lo hi : ℕ) :
    routeTPointMassPhasePacket (fun y => c * a y) lambda lo hi =
      c * routeTPointMassPhasePacket a lambda lo hi := by
  unfold routeTPointMassPhasePacket
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  ring

/-- In particular, the sign-reversed source has exactly the opposite extracted phase. -/
theorem routeTPointMassPhasePacket_neg
    (a : ℝ → ℂ) (lambda : ℝ) (lo hi : ℕ) :
    routeTPointMassPhasePacket (fun y => -a y) lambda lo hi =
      -routeTPointMassPhasePacket a lambda lo hi := by
  simpa using routeTPointMassPhasePacket_const_mul (-1 : ℂ) a lambda lo hi

/-- Norm-only phase information cannot yield a positive real phase orientation: the two globally
gauge-related sources have identical norm data but opposite real extracted phases.  A nonlocal
Route-T phase receiver must therefore use a source-specific, non-gauge-invariant correlation. -/
theorem not_routeTPointMassPhasePacket_re_lower_both_gauges
    {a : ℝ → ℂ} {lambda B : ℝ} {lo hi : ℕ} (hB : 0 < B)
    (hplus : B ≤ (routeTPointMassPhasePacket a lambda lo hi).re)
    (hminus : B ≤ (routeTPointMassPhasePacket (fun y => -a y) lambda lo hi).re) : False := by
  rw [routeTPointMassPhasePacket_neg] at hminus
  change B ≤ -(routeTPointMassPhasePacket a lambda lo hi).re at hminus
  linarith

/-- Exact spatial `L²` cost of the bare extracted phase.  The exponent `2 * 0 + 1 = 1` leaves a
factor `x` in front of the squared cell envelope.  Any phase receiver that reaches the Route-T
second-count scale must improve this by one reciprocal physical-base factor before this step. -/
theorem integral_norm_sq_routeTPointMassPhasePacket_le_weighted_envelope
    {x : ℝ} {cellCount lo hi : ℕ} (hx : 1 ≤ x) (hlohi : lo ≤ hi)
    (hhi : hi ≤ cellCount) (a : ℝ → ℂ) (ha : Continuous a)
    (A : ℕ → ℝ) (hA : ∀ m ∈ Finset.Ico lo hi, 0 ≤ A m)
    (hbound : ∀ m ∈ Finset.Ico lo hi, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + v)‖ ≤ A m) :
    (∫ lambda : ℝ in x..(2 * x), ‖routeTPointMassPhasePacket a lambda lo hi‖ ^ 2) ≤
      8 * x * (1 + 2 * (1 + Real.log cellCount)) *
        ∑ m ∈ Finset.Ico lo hi, (A m) ^ 2 := by
  have hS : Finset.Ico lo hi ⊆ Finset.range cellCount := by
    intro m hm
    exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hm).2.trans_le hhi)
  have hcontinuous : ∀ m ∈ Finset.Ico lo hi,
      Continuous (fun v : ℝ => a ((m : ℝ) + v)) := by
    intro m hm
    exact ha.comp (continuous_const.add continuous_id)
  have hL2 := integral_norm_sq_maynardUnitCellMellinPacket_le_weighted_envelope
    hx (by norm_num : (0 : ℝ) ≤ 0) (Finset.Ico lo hi) hS
      (fun m v => a ((m : ℝ) + v)) hcontinuous A hA hbound
  calc
    (∫ lambda : ℝ in x..(2 * x), ‖routeTPointMassPhasePacket a lambda lo hi‖ ^ 2) =
        ∫ lambda : ℝ in x..(2 * x),
          ‖maynardUnitCellMellinPacket (Finset.Ico lo hi)
            (fun m v => a ((m : ℝ) + v)) 0 lambda‖ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro lambda hlambda
          rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hlambda
          change ‖routeTPointMassPhasePacket a lambda lo hi‖ ^ 2 = _
          rw [routeTPointMassPhasePacket_eq_unitCellMellinPacket ha
            (lt_of_lt_of_le zero_lt_one (hx.trans hlambda.1)) hlohi]
    _ ≤ 4 * (2 * x) ^ (2 * (0 : ℝ) + 1) *
          (1 + 2 * (1 + Real.log cellCount)) *
          ∑ m ∈ Finset.Ico lo hi, (A m) ^ 2 := hL2
    _ = 8 * x * (1 + 2 * (1 + Real.log cellCount)) *
          ∑ m ∈ Finset.Ico lo hi, (A m) ^ 2 := by
          rw [show 2 * (0 : ℝ) + 1 = 1 by ring, Real.rpow_one]
          ring

/-- The exact survivor criterion: a phase-side bad-measure estimate with the missing reciprocal
base gain has precisely the ordinary Route-T second-count shape, so the existing two-alternative
receiver can consume it without further exponent loss. -/
theorem routeT_phaseSpatial_reciprocalGain_closes_secondCount
    {B R T x sigma eps : ℝ} (hT : 0 ≤ T) (hx : 0 < x) (hR : 0 ≤ R)
    (hphaseMeasure : B ≤ x ^ (2 * sigma - 1 + eps) * R)
    (hsecond : R ≤ T * x ^ (1 + routeTGapMomentNu - 2 * sigma)) :
    B ≤ T * x ^ (routeTGapMomentNu + eps) :=
  routeT_second_count_L2_bad_measure hT hx hR hphaseMeasure hsecond

/-- A local anchor inside one prime-free physical interval cannot create the required phase
difference.  In the integrated phase window, the phase frequency times the available relative
physical width has a strictly negative base exponent, with a uniform margin. -/
theorem routeT_phaseExtraction_localAnchorExponent_neg
    {mu : ℝ} (hmu : routeTPhaseExtractionIntegratedTargetMu < mu) :
    1 / mu - (49 / 80 : ℝ) < -(49 / 160 : ℝ) := by
  have hmu0 : 0 < mu := by
    dsimp only [routeTPhaseExtractionIntegratedTargetMu] at hmu
    norm_num at hmu ⊢
    linarith
  have hinv : 1 / mu < (49 / 160 : ℝ) := by
    apply (div_lt_iff₀ hmu0).2
    dsimp only [routeTPhaseExtractionIntegratedTargetMu] at hmu
    norm_num at hmu ⊢
    nlinarith
  linarith

/-- Quantitative form of the local-anchor no-go.  If the physical base is `M` and the phase shell
has height `M^(1/mu)`, then its oscillation across one target-width interval is at most the
strictly decaying scale `M^(-49/160)`.  Hence any viable phase correlation must span separated
bases or use a new signed source law; endpoint differencing inside one prime-free interval is
asymptotically phase-flat. -/
theorem routeT_phaseExtraction_localAnchorScale_lt
    {M mu : ℝ} (hM : 1 < M)
    (hmu : routeTPhaseExtractionIntegratedTargetMu < mu) :
    M ^ (1 / mu - (49 / 80 : ℝ)) < M ^ (-(49 / 160 : ℝ)) := by
  exact Real.rpow_lt_rpow_of_exponent_lt hM
    (routeT_phaseExtraction_localAnchorExponent_neg hmu)

end RHTower.Sieve
