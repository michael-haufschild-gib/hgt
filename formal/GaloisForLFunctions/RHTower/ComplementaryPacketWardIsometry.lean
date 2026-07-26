import GaloisForLFunctions.RHTower.ComplementaryPacketAffineFlux
import GaloisForLFunctions.RHTower.ComplementaryPacketCriticalEnergy
import GaloisForLFunctions.RHTower.EulerSquarefreeAffineFisherCutoffWard
import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentHilbertLift

/-!
# The packet edge flux is the critical Fisher--Ward score

Conditioning the packet edge field `G(H, H') = 2 (B_{H'} - B_H)` on its first endpoint and applying
the affine flux of `ComplementaryPacketAffineFlux` produces, exactly,

```text
W(H) = -(ε/c_ω) · E_{H'}[Φ_ω(G(H, H'))] = -2 (H - E H) ,
```

the centered logarithmic score of the source.  The exact flux law makes this an identity, not a
choice of isometry between two equal-norm vectors: the kernel `k_ω` cancels completely and only the
incoming constant survives.

On the escaping squarefree critical clock both sides carry four units of energy — the score energy
is `4·Var`, which is the projective Fisher energy already known to tend to four, and the packet edge
energy is the source-framed packet energy of `ComplementaryPacketCriticalEnergy` — so the flux map
is an asymptotic isometry on the distinguished critical edge field.
-/

open MeasureTheory Set Filter

namespace RHTower

noncomputable section

/-! ### The first moment of the rescaled critical clock -/

theorem integrable_squarefreeMobiusCriticalClock_id {sigma : ℝ} (hsigma : 1 < sigma) :
    Integrable (fun y : ℝ => y)
      (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ) := by
  let p := squarefreeMobiusCriticalPMF sigma
  let clock := squarefreeMobiusCriticalClock sigma
  have hsum : Summable (fun n : ℕ => (p n).toReal * ‖clock n‖) := by
    have h := (summable_squarefreeMobiusLogMoment 1 hsigma).mul_left (sigma - 1)
    apply h.congr
    intro n
    simp only [p, squarefreeMobiusCriticalPMF_toReal hsigma, Real.norm_eq_abs]
    unfold clock squarefreeMobiusCriticalClock
    rw [abs_of_nonneg (mul_nonneg (by linarith) (Real.log_natCast_nonneg n))]
    ring
  have hsource : Integrable (fun n : ℕ => clock n) p.toMeasure := by
    rw [pmf_toMeasure_eq_sum_smul_dirac]
    exact integrable_sum_dirac (fun n => p.apply_ne_top n) hsum
  unfold squarefreeMobiusCriticalClockProbabilityMeasure
    squarefreeMobiusCriticalIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  exact (integrable_map_measure continuous_id.aestronglyMeasurable
    (Measurable.of_discrete.aemeasurable : AEMeasurable clock p.toMeasure)).2 hsource

theorem integral_squarefreeMobiusCriticalClock_id {sigma : ℝ} (hsigma : 1 < sigma) :
    (∫ y : ℝ, y ∂(squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ))
      = (sigma - 1) * squarefreeMobiusLogMoment 1 sigma := by
  let p := squarefreeMobiusCriticalPMF sigma
  let clock := squarefreeMobiusCriticalClock sigma
  have hsource : Integrable (fun n : ℕ => clock n) p.toMeasure := by
    have hmap := integrable_squarefreeMobiusCriticalClock_id hsigma
    rw [squarefreeMobiusCriticalClockProbabilityMeasure] at hmap
    exact (integrable_map_measure continuous_id.aestronglyMeasurable
      (Measurable.of_discrete.aemeasurable : AEMeasurable clock p.toMeasure)).1 hmap
  unfold squarefreeMobiusCriticalClockProbabilityMeasure
    squarefreeMobiusCriticalIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  rw [integral_map
    (Measurable.of_discrete.aemeasurable : AEMeasurable clock p.toMeasure)
    (show AEStronglyMeasurable (fun y : ℝ => y) (Measure.map clock p.toMeasure) from
      measurable_id.aestronglyMeasurable)]
  rw [PMF.integral_eq_tsum p _ hsource]
  simp only [smul_eq_mul]
  simp only [p]
  simp_rw [squarefreeMobiusCriticalPMF_toReal hsigma]
  unfold clock squarefreeMobiusCriticalClock squarefreeMobiusLogMoment
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

theorem ae_nonneg_squarefreeMobiusCriticalClockProbabilityMeasure {sigma : ℝ} (hsigma : 1 < sigma) :
    ∀ᵐ y ∂(squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ), 0 ≤ y := by
  rw [ae_iff]
  simpa only [not_le] using squarefreeMobiusCriticalClockProbabilityMeasure_Iio_zero hsigma

/-! ### The conditional edge flux -/

/-- The conditional affine flux of the packet edge field, read at the rescaled clock: the clock law
carries `ε·log d`, so the packet based at `log d` is read at `x/ε`. -/
def packetEdgeWardScore (ω ε : ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ :=
  -(ε / complementaryPacketConstant ω) *
    ∫ y, 2 * (affinePacketFlux ω (y / ε) - affinePacketFlux ω (x / ε)) ∂μ

/-- **Edge-to-score Ward identity.**  The conditional affine flux of the packet edge field is the
centered clock score.  The packet kernel cancels exactly; only the incoming constant survives, and
it is removed by the normalisation `ε/c_ω`. -/
theorem packetEdgeWardScore_eq {ω ε : ℝ} (hω : 0 ≤ ω) (hε : 0 < ε) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hint : Integrable (fun y : ℝ => y) μ)
    (hsupp : ∀ᵐ y ∂μ, 0 ≤ y) {x : ℝ} (hx : 0 ≤ x) :
    packetEdgeWardScore ω ε μ x = -(2 * (x - ∫ y, y ∂μ)) := by
  have hc : 0 < complementaryPacketConstant ω := complementaryPacketConstant_pos hω
  have hxe : 0 ≤ x / ε := by positivity
  have hcongr : (∫ y, 2 * (affinePacketFlux ω (y / ε) - affinePacketFlux ω (x / ε)) ∂μ)
      = ∫ y, (-(2 * complementaryPacketConstant ω / ε) * (y - x)) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with y hy
    have hye : 0 ≤ y / ε := by positivity
    rw [affinePacketFlux_sub ω hω hxe hye]
    field_simp
  have hval : (∫ y, (-(2 * complementaryPacketConstant ω / ε) * (y - x)) ∂μ)
      = -(2 * complementaryPacketConstant ω / ε) * ((∫ y, y ∂μ) - x) := by
    rw [integral_const_mul, integral_sub hint (integrable_const x), integral_const]
    simp
  rw [packetEdgeWardScore, hcongr, hval]
  field_simp
  ring

/-- **The completed squarefree Fisher tangent is the packet edge flux score.**  The scalar
coefficient of `infiniteMobiusCriticalFisherTangentWeight` is exactly the conditional affine flux of
the packet edge field, evaluated at the rescaled clock of the divisor.  The score is therefore not
chosen by norm matching between two equal-norm vectors: it is produced by the same packet incidence
cocycle whose connection synthesises the Euler source. -/
theorem infiniteMobiusCriticalFisherTangentWeight_eq_packetEdgeWardScore
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    infiniteMobiusCriticalFisherTangentWeight sigma n
      = ((packetEdgeWardScore ((sigma - 1) / 2) (sigma - 1)
            (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ)
            ((sigma - 1) * Real.log n) : ℝ) : ℂ) * infiniteMobiusSignedWeight sigma n := by
  have hω : (0 : ℝ) ≤ (sigma - 1) / 2 := by linarith
  have hε : (0 : ℝ) < sigma - 1 := by linarith
  have hx : (0 : ℝ) ≤ (sigma - 1) * Real.log n :=
    mul_nonneg (by linarith) (Real.log_natCast_nonneg n)
  rw [packetEdgeWardScore_eq hω hε
      (integrable_squarefreeMobiusCriticalClock_id hsigma)
      (ae_nonneg_squarefreeMobiusCriticalClockProbabilityMeasure hsigma) hx,
    integral_squarefreeMobiusCriticalClock_id hsigma,
    infiniteMobiusCriticalFisherTangentWeight]
  congr 2
  ring

/-! ### The Ward energy of the edge score -/

/-- The energy of the conditional edge flux score. -/
def packetEdgeWardEnergy (ω ε : ℝ) (μ : Measure ℝ) : ℝ :=
  ∫ x, packetEdgeWardScore ω ε μ x ^ 2 ∂μ

/-- **The edge flux score carries four times the clock variance.** -/
theorem packetEdgeWardEnergy_eq {ω ε : ℝ} (hω : 0 ≤ ω) (hε : 0 < ε) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hint : Integrable (fun y : ℝ => y) μ)
    (hsq : Integrable (fun y : ℝ => y ^ 2) μ) (hsupp : ∀ᵐ y ∂μ, 0 ≤ y) :
    packetEdgeWardEnergy ω ε μ = 4 * ((∫ x, x ^ 2 ∂μ) - (∫ x, x ∂μ) ^ 2) := by
  set m : ℝ := ∫ y, y ∂μ with hm
  have h1 : Integrable (fun x : ℝ => 4 * x ^ 2) μ := hsq.const_mul 4
  have h2 : Integrable (fun x : ℝ => (-8 * m) * x) μ := hint.const_mul _
  have h3 : Integrable (fun _ : ℝ => 4 * m ^ 2) μ := integrable_const _
  have h23 : Integrable (fun x : ℝ => (-8 * m) * x + 4 * m ^ 2) μ := h2.add h3
  have hcongr : packetEdgeWardEnergy ω ε μ
      = ∫ x, (4 * x ^ 2 + ((-8 * m) * x + 4 * m ^ 2)) ∂μ := by
    rw [packetEdgeWardEnergy]
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with x hx
    rw [packetEdgeWardScore_eq hω hε hint hsupp hx, ← hm]
    ring
  rw [hcongr, integral_add h1 h23, integral_add h2 h3, integral_const_mul,
    integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [← hm]
  ring

/-! ### The critical Ward isometry -/

/-- The critical Ward energy of the squarefree packet edge score. -/
def complementaryPacketCriticalWardEnergy (sigma : ℝ) : ℝ :=
  packetEdgeWardEnergy ((sigma - 1) / 2) (sigma - 1)
    (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ)

/-- The edge flux score of the squarefree source **is** the projective Fisher tangent. -/
theorem complementaryPacketCriticalWardEnergy_eq {sigma : ℝ} (hsigma : 1 < sigma) :
    complementaryPacketCriticalWardEnergy sigma
      = squarefreeMobiusCriticalProjectiveFisherEnergy sigma := by
  have hω : (0 : ℝ) ≤ (sigma - 1) / 2 := by linarith
  have hε : (0 : ℝ) < sigma - 1 := by linarith
  rw [complementaryPacketCriticalWardEnergy,
    packetEdgeWardEnergy_eq hω hε
      (integrable_squarefreeMobiusCriticalClock_id hsigma)
      (integrable_squarefreeMobiusCriticalClock_sq hsigma)
      (ae_nonneg_squarefreeMobiusCriticalClockProbabilityMeasure hsigma),
    integral_squarefreeMobiusCriticalClock_sq hsigma,
    integral_squarefreeMobiusCriticalClock_id hsigma,
    squarefreeMobiusCriticalProjectiveFisherEnergy, squarefreeMobiusCriticalClockVariance]

/-- **The critical Ward score carries exactly four energy units.** -/
theorem tendsto_complementaryPacketCriticalWardEnergy :
    Tendsto complementaryPacketCriticalWardEnergy (nhdsWithin 1 (Ioi 1)) (nhds 4) := by
  refine tendsto_squarefreeMobiusCriticalProjectiveFisherEnergy.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  exact (complementaryPacketCriticalWardEnergy_eq hsigma).symm

/-- **Critical Ward isometry.**  The conditional affine flux is asymptotically norm preserving on
the distinguished escaping edge field: the score energy and the source-framed packet energy have the
same four-unit critical limit. -/
theorem tendsto_complementaryPacketWardIsometryRatio :
    Tendsto (fun sigma : ℝ =>
        complementaryPacketCriticalWardEnergy sigma / complementaryPacketCriticalEnergy sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
  have h := tendsto_complementaryPacketCriticalWardEnergy.div
    tendsto_complementaryPacketCriticalEnergy (by norm_num : (4 : ℝ) ≠ 0)
  rwa [show (4 : ℝ) / 4 = 1 by norm_num] at h

end

end RHTower
