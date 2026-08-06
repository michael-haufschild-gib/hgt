import GaloisForLFunctions.RHTower.MobiusCriticalTransportAssembly
import GaloisForLFunctions.RHTower.ComplementaryPacketTwoPointDistance
import GaloisForLFunctions.RHTower.ComplementaryPacketModulusMeasurable
import GaloisForLFunctions.RHTower.ComplementaryPacketFourUnitEnergy

/-!
# Vanishing complementary-packet transport cost

The monotone coupling of the two critical clocks has vanishing transport cost, and the squared
packet distance grows at most affinely in the clock separation.  The two facts together make the
critical complementary-packet transport cost vanish: the packets carried by the squarefree clock
and by the Euler prime current become indistinguishable in the packet metric.

The uniform packet defect is what makes this work: the bounded local part of the packet distance is
annihilated by the escaping scale, and the affine part is exactly the transport cost.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The critical coupling of the two clocks, before the thermal rescaling. -/
def criticalClockCoupling (σ : ℝ) : Measure (ℝ × ℝ) :=
  monotoneCoupling (squarefreeClockLaw σ) (eulerClockLaw σ)

/-- The complementary-packet transport cost of the critical coupling at escape `ε`. -/
def criticalPacketCost (ε : ℝ) : ℝ :=
  ε * ∫ z, RHTower.packetPathDistanceSq (ε / 2) z.1 z.2 ∂(criticalClockCoupling (1 + ε))

theorem criticalPacketCost_nonneg {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ criticalPacketCost ε :=
  mul_nonneg hε (integral_nonneg fun _ => RHTower.packetPathDistanceSq_nonneg _ _ _)

/-- The packet distance of the coupled clock values is the packet modulus of their gap. -/
theorem ae_packetPathDistanceSq_eq {σ : ℝ} (hσ : 1 < σ) {ω : ℝ} (hω : 0 ≤ ω) :
    ∀ᵐ z ∂(criticalClockCoupling σ), RHTower.packetPathDistanceSq ω z.1 z.2
      = RHTower.packetTranslationModulus (RHTower.complementaryPacketKernel ω)
        (RHTower.complementaryPacketConstant ω) |z.1 - z.2| := by
  haveI := isProbabilityMeasure_squarefreeClockLaw hσ
  haveI := isProbabilityMeasure_eulerClockLaw hσ
  rw [criticalClockCoupling]
  filter_upwards [ae_nonneg_fst_monotoneCoupling _ _ (squarefreeClockLaw_Iio_zero σ),
    ae_nonneg_snd_monotoneCoupling _ _ (eulerClockLaw_Iio_zero σ)] with z h1 h2
  exact RHTower.packetPathDistanceSq_eq_abs hω h1 h2

/-- The packet distance is integrable against the critical coupling. -/
theorem integrable_packetPathDistanceSq {σ : ℝ} (hσ : 1 < σ) {ω : ℝ} (hω : 0 ≤ ω) :
    Integrable (fun z : ℝ × ℝ => RHTower.packetPathDistanceSq ω z.1 z.2)
      (criticalClockCoupling σ) := by
  haveI := isProbabilityMeasure_squarefreeClockLaw hσ
  haveI := isProbabilityMeasure_eulerClockLaw hσ
  have hgap : Integrable (fun x : ℝ => |x|)
      (gapLaw (squarefreeClockLaw σ) (eulerClockLaw σ)) :=
    integrable_abs_gapLaw _ _ (integrable_id_squarefreeClockLaw hσ) (integrable_id_eulerClockLaw hσ)
  have hmod : Integrable (fun x : ℝ =>
      RHTower.packetTranslationModulus (RHTower.complementaryPacketKernel ω)
        (RHTower.complementaryPacketConstant ω) |x|)
      (gapLaw (squarefreeClockLaw σ) (eulerClockLaw σ)) :=
    RHTower.integrable_packetTranslationModulus_abs
      (RHTower.measurable_complementaryPacketKernel ω hω)
      (RHTower.integrableOn_complementaryPacketKernel ω hω)
      (RHTower.integrableOn_complementaryPacketKernel_sq ω hω)
      (le_refl _) (le_refl _) hgap
  have hmeas : AEStronglyMeasurable (fun x : ℝ =>
      RHTower.packetTranslationModulus (RHTower.complementaryPacketKernel ω)
        (RHTower.complementaryPacketConstant ω) |x|)
      (gapLaw (squarefreeClockLaw σ) (eulerClockLaw σ)) := hmod.aestronglyMeasurable
  have hcomp := integrable_comp_gap (squarefreeClockLaw σ) (eulerClockLaw σ) hmeas hmod
  rw [criticalClockCoupling]
  refine hcomp.congr ?_
  filter_upwards [ae_packetPathDistanceSq_eq hσ hω] with z hz
  exact hz.symm

/-- **The packet cost is bounded by the transport cost and the uniform defect.** -/
theorem criticalPacketCost_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    criticalPacketCost ε
      ≤ (∫ z, |z.1 - z.2|
          ∂(monotoneCoupling (scaledSquarefreeClockLaw (1 + ε)) (scaledEulerClockLaw (1 + ε))))
        + 24 * ε := by
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  haveI := isProbabilityMeasure_squarefreeClockLaw hσ
  haveI := isProbabilityMeasure_eulerClockLaw hσ
  set ω : ℝ := ε / 2 with hωdef
  have hω : (0 : ℝ) ≤ ω := by positivity
  have hω1 : ω ≤ 1 := by
    rw [hωdef]
    linarith
  set c : ℝ := RHTower.complementaryPacketConstant ω with hcdef
  have hcpos : 0 < c := RHTower.complementaryPacketConstant_pos hω
  have hcle : c ≤ 1 := by
    rw [hcdef, RHTower.complementaryPacketConstant]
    rw [div_le_one (by linarith)]
    linarith
  -- the uniform defect on the clamped range
  have hdefect : 5 * (4 : ℝ) ^ ω + 2 * |c| * 2 ^ ω ≤ 24 := by
    have h4 : (4 : ℝ) ^ ω ≤ 4 := by
      calc (4 : ℝ) ^ ω ≤ (4 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hω1
        _ = 4 := Real.rpow_one 4
    have h2 : (2 : ℝ) ^ ω ≤ 2 := by
      calc (2 : ℝ) ^ ω ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hω1
        _ = 2 := Real.rpow_one 2
    have habs : |c| ≤ 1 := by
      rw [abs_of_pos hcpos]
      exact hcle
    have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ ω := Real.rpow_nonneg (by norm_num) ω
    nlinarith [abs_nonneg c]
  -- the pointwise bound under the coupling
  have hgapInt : Integrable (fun z : ℝ × ℝ => |z.1 - z.2|) (criticalClockCoupling (1 + ε)) := by
    rw [criticalClockCoupling]
    exact integrable_abs_sub_monotoneCoupling _ _ (integrable_id_squarefreeClockLaw hσ)
      (integrable_id_eulerClockLaw hσ)
  have hdom : Integrable (fun z : ℝ × ℝ => c ^ 2 * |z.1 - z.2| + 24)
      (criticalClockCoupling (1 + ε)) := by
    haveI : IsProbabilityMeasure (criticalClockCoupling (1 + ε)) := by
      rw [criticalClockCoupling]
      infer_instance
    exact (hgapInt.const_mul (c ^ 2)).add (integrable_const 24)
  have hbound : (∫ z, RHTower.packetPathDistanceSq ω z.1 z.2 ∂(criticalClockCoupling (1 + ε)))
      ≤ ∫ z, (c ^ 2 * |z.1 - z.2| + 24) ∂(criticalClockCoupling (1 + ε)) := by
    refine integral_mono_ae (integrable_packetPathDistanceSq hσ hω) hdom ?_
    rw [criticalClockCoupling]
    filter_upwards [ae_nonneg_fst_monotoneCoupling _ _ (squarefreeClockLaw_Iio_zero (1 + ε)),
      ae_nonneg_snd_monotoneCoupling _ _ (eulerClockLaw_Iio_zero (1 + ε))] with z h1 h2
    have h := RHTower.packetPathDistanceSq_le hω h1 h2
    have hdef := hdefect
    rw [← hcdef] at h
    linarith
  have hsplit : (∫ z, (c ^ 2 * |z.1 - z.2| + 24) ∂(criticalClockCoupling (1 + ε)))
      = c ^ 2 * (∫ z, |z.1 - z.2| ∂(criticalClockCoupling (1 + ε))) + 24 := by
    haveI : IsProbabilityMeasure (criticalClockCoupling (1 + ε)) := by
      rw [criticalClockCoupling]
      infer_instance
    rw [integral_add (hgapInt.const_mul (c ^ 2)) (integrable_const 24), integral_const_mul,
      integral_const]
    simp
  -- the transport cost after rescaling
  have hscale : (∫ z, |z.1 - z.2|
      ∂(monotoneCoupling (scaledSquarefreeClockLaw (1 + ε)) (scaledEulerClockLaw (1 + ε))))
      = ε * ∫ z, |z.1 - z.2| ∂(criticalClockCoupling (1 + ε)) := by
    have hεeq : (1 : ℝ) + ε - 1 = ε := by ring
    rw [scaledSquarefreeClockLaw, scaledEulerClockLaw, hεeq, criticalClockCoupling,
      integral_monotoneCoupling_abs_sub_scaleLaw hε]
  have hgapnn : 0 ≤ ∫ z, |z.1 - z.2| ∂(criticalClockCoupling (1 + ε)) :=
    integral_nonneg fun z => abs_nonneg _
  have hcsq : c ^ 2 ≤ 1 := by nlinarith
  rw [criticalPacketCost, hscale, ← hωdef]
  calc ε * ∫ z, RHTower.packetPathDistanceSq ω z.1 z.2 ∂(criticalClockCoupling (1 + ε))
      ≤ ε * (c ^ 2 * (∫ z, |z.1 - z.2| ∂(criticalClockCoupling (1 + ε))) + 24) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hε)
        rw [← hsplit]
        exact hbound
    _ ≤ ε * ((∫ z, |z.1 - z.2| ∂(criticalClockCoupling (1 + ε))) + 24) := by
        have h1 : c ^ 2 * (∫ z, |z.1 - z.2| ∂(criticalClockCoupling (1 + ε)))
            ≤ ∫ z, |z.1 - z.2| ∂(criticalClockCoupling (1 + ε)) :=
          mul_le_of_le_one_left hgapnn hcsq
        exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hε)
    _ = ε * (∫ z, |z.1 - z.2| ∂(criticalClockCoupling (1 + ε))) + 24 * ε := by ring

/-- **`(19)`: the critical complementary-packet transport cost vanishes.**  The monotone coupling
of the squarefree clock with the Euler prime current carries the packets to each other with
vanishing packet energy at criticality. -/
theorem tendsto_criticalPacketCost :
    Tendsto criticalPacketCost (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hrhs : Tendsto (fun ε : ℝ => (∫ z, |z.1 - z.2|
      ∂(monotoneCoupling (scaledSquarefreeClockLaw (1 + ε)) (scaledEulerClockLaw (1 + ε))))
      + 24 * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := tendsto_integral_monotoneCoupling_criticalClocks.add
      ((tendsto_id.mono_left nhdsWithin_le_nhds).const_mul (24 : ℝ))
    simpa using h
  refine squeeze_zero' ?_ ?_ hrhs
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact criticalPacketCost_nonneg (le_of_lt hε)
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε hε1
    exact criticalPacketCost_le hε (le_of_lt hε1.2)

/-! ### The packet edge fields -/

/-- Two independent copies of the critical coupling. -/
def criticalCouplingSquare (σ : ℝ) : Measure ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (criticalClockCoupling σ).prod (criticalClockCoupling σ)

theorem isProbabilityMeasure_criticalClockCoupling {σ : ℝ} (hσ : 1 < σ) :
    IsProbabilityMeasure (criticalClockCoupling σ) := by
  haveI := isProbabilityMeasure_squarefreeClockLaw hσ
  haveI := isProbabilityMeasure_eulerClockLaw hσ
  rw [criticalClockCoupling]
  infer_instance

/-- The complementary-packet edge cost of the critical coupling at escape `ε`. -/
def criticalPacketEdgeCost (ε : ℝ) : ℝ :=
  ε * ∫ W, RHTower.packetEdgeFieldDistanceSq (ε / 2) W.1.1 W.1.2 W.2.1 W.2.2
    ∂(criticalCouplingSquare (1 + ε))

theorem criticalPacketEdgeCost_nonneg {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ criticalPacketEdgeCost ε :=
  mul_nonneg hε (integral_nonneg fun _ => RHTower.packetEdgeFieldDistanceSq_nonneg _ _ _ _ _)

/-- **The edge cost is at most sixteen times the packet transport cost.** -/
theorem criticalPacketEdgeCost_le {ε : ℝ} (hε : 0 < ε) :
    criticalPacketEdgeCost ε ≤ 16 * criticalPacketCost ε := by
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  haveI := isProbabilityMeasure_criticalClockCoupling hσ
  set ω : ℝ := ε / 2 with hωdef
  have hω : (0 : ℝ) ≤ ω := by positivity
  set π : Measure (ℝ × ℝ) := criticalClockCoupling (1 + ε) with hπdef
  have hPint : Integrable (fun z : ℝ × ℝ => RHTower.packetPathDistanceSq ω z.1 z.2) π :=
    integrable_packetPathDistanceSq hσ hω
  have hfst : Integrable (fun W : (ℝ × ℝ) × (ℝ × ℝ) =>
      RHTower.packetPathDistanceSq ω W.1.1 W.1.2) (π.prod π) :=
    integrable_comp_fst_prod π π hPint
  have hsnd : Integrable (fun W : (ℝ × ℝ) × (ℝ × ℝ) =>
      RHTower.packetPathDistanceSq ω W.2.1 W.2.2) (π.prod π) :=
    integrable_comp_snd_prod π π hPint
  have hdom : Integrable (fun W : (ℝ × ℝ) × (ℝ × ℝ) =>
      8 * RHTower.packetPathDistanceSq ω W.2.1 W.2.2
      + 8 * RHTower.packetPathDistanceSq ω W.1.1 W.1.2) (π.prod π) :=
    (hsnd.const_mul 8).add (hfst.const_mul 8)
  have hnn : ∀ᵐ W ∂(π.prod π), 0 ≤ W.1.1 ∧ 0 ≤ W.1.2 ∧ 0 ≤ W.2.1 ∧ 0 ≤ W.2.2 := by
    have hz : ∀ᵐ z ∂π, 0 ≤ z.1 ∧ 0 ≤ z.2 := by
      rw [hπdef, criticalClockCoupling]
      haveI := isProbabilityMeasure_squarefreeClockLaw hσ
      haveI := isProbabilityMeasure_eulerClockLaw hσ
      filter_upwards [ae_nonneg_fst_monotoneCoupling _ _ (squarefreeClockLaw_Iio_zero (1 + ε)),
        ae_nonneg_snd_monotoneCoupling _ _ (eulerClockLaw_Iio_zero (1 + ε))] with z h1 h2
      exact ⟨h1, h2⟩
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := π) (ν := π)).ae hz
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := π) (ν := π)).ae hz
    filter_upwards [h1, h2] with W hW1 hW2
    exact ⟨hW1.1, hW1.2, hW2.1, hW2.2⟩
  have hbound : (∫ W, RHTower.packetEdgeFieldDistanceSq ω W.1.1 W.1.2 W.2.1 W.2.2 ∂(π.prod π))
      ≤ ∫ W, (8 * RHTower.packetPathDistanceSq ω W.2.1 W.2.2
        + 8 * RHTower.packetPathDistanceSq ω W.1.1 W.1.2) ∂(π.prod π) := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun W => RHTower.packetEdgeFieldDistanceSq_nonneg _ _ _ _ _)
      hdom ?_
    filter_upwards [hnn] with W hW
    exact RHTower.packetEdgeFieldDistanceSq_le hω hW.1 hW.2.1 hW.2.2.1 hW.2.2.2
  have hvalue : (∫ W, (8 * RHTower.packetPathDistanceSq ω W.2.1 W.2.2
      + 8 * RHTower.packetPathDistanceSq ω W.1.1 W.1.2) ∂(π.prod π))
      = 16 * ∫ z, RHTower.packetPathDistanceSq ω z.1 z.2 ∂π := by
    rw [integral_add (hsnd.const_mul 8) (hfst.const_mul 8), integral_const_mul, integral_const_mul,
      integral_comp_fst_prod π π hPint.aestronglyMeasurable,
      integral_comp_snd_prod π π hPint.aestronglyMeasurable]
    ring
  rw [criticalPacketEdgeCost, criticalPacketCost, criticalCouplingSquare, ← hωdef, ← hπdef]
  calc ε * ∫ W, RHTower.packetEdgeFieldDistanceSq ω W.1.1 W.1.2 W.2.1 W.2.2 ∂(π.prod π)
      ≤ ε * (16 * ∫ z, RHTower.packetPathDistanceSq ω z.1 z.2 ∂π) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hε)
        rw [← hvalue]
        exact hbound
    _ = 16 * (ε * ∫ z, RHTower.packetPathDistanceSq ω z.1 z.2 ∂π) := by ring

/-- **`(21)`: the complementary-packet edge fields are asymptotically isometric.**  Under two
independent copies of the critical coupling the two edge fields — the squarefree one and the Euler
prime-current one — differ by vanishing packet energy at criticality. -/
theorem tendsto_criticalPacketEdgeCost :
    Tendsto criticalPacketEdgeCost (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hrhs : Tendsto (fun ε : ℝ => 16 * criticalPacketCost ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_criticalPacketCost.const_mul (16 : ℝ)
  refine squeeze_zero' ?_ ?_ hrhs
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact criticalPacketEdgeCost_nonneg (le_of_lt hε)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact criticalPacketEdgeCost_le hε

/-! ### The four-unit budget of the Euler edge field -/

/-- The packet shift of the critical scaling, clamped to the range where the packet defect is
uniformly bounded. -/
def packetShift (ε : ℝ) : ℝ := if 0 < ε then min (ε / 2) (1 / 2) else 0

theorem packetShift_nonneg (ε : ℝ) : 0 ≤ packetShift ε := by
  unfold packetShift
  split
  · exact le_min (by linarith) (by norm_num)
  · exact le_rfl

theorem packetShift_le_one (ε : ℝ) : packetShift ε ≤ 1 := by
  unfold packetShift
  split
  · exact le_trans (min_le_right _ _) (by norm_num)
  · norm_num

theorem packetShift_eq_of_le_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : packetShift ε = ε / 2 := by
  rw [packetShift, if_pos hε, min_eq_left (by linarith)]

theorem tendsto_packetShift : Tendsto packetShift (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hhalf : Tendsto (fun ε : ℝ => ε / 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε / 2) (𝓝 (0 : ℝ)) (𝓝 (0 / 2)) :=
      (continuous_id.div_const 2).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  refine hhalf.congr' ?_
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε hε1
  exact (packetShift_eq_of_le_one hε (le_of_lt hε1.2)).symm

/-- The uniform packet defect on the clamped shift range. -/
theorem abs_packetModulus_sub_le_uniform (ε a : ℝ) (ha : 0 ≤ a) :
    |RHTower.packetTranslationModulus (RHTower.complementaryPacketKernel (packetShift ε))
        (RHTower.complementaryPacketConstant (packetShift ε)) a
      - RHTower.complementaryPacketConstant (packetShift ε) ^ 2 * a| ≤ 24 := by
  set ω : ℝ := packetShift ε with hωdef
  have hω : (0 : ℝ) ≤ ω := packetShift_nonneg ε
  have hω1 : ω ≤ 1 := packetShift_le_one ε
  have hcpos : 0 < RHTower.complementaryPacketConstant ω :=
    RHTower.complementaryPacketConstant_pos hω
  have hcle : RHTower.complementaryPacketConstant ω ≤ 1 := by
    rw [RHTower.complementaryPacketConstant, div_le_one (by linarith)]
    linarith
  have h4 : (4 : ℝ) ^ ω ≤ 4 := by
    calc (4 : ℝ) ^ ω ≤ (4 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hω1
      _ = 4 := Real.rpow_one 4
  have h2 : (2 : ℝ) ^ ω ≤ 2 := by
    calc (2 : ℝ) ^ ω ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hω1
      _ = 2 := Real.rpow_one 2
  have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ ω := Real.rpow_nonneg (by norm_num) ω
  have habs : |RHTower.complementaryPacketConstant ω| ≤ 1 := by
    rw [abs_of_pos hcpos]
    exact hcle
  have hbound := RHTower.abs_complementaryPacketModulus_sub_le ω hω ha
  have hdefect : 5 * (4 : ℝ) ^ ω + 2 * |RHTower.complementaryPacketConstant ω| * 2 ^ ω ≤ 24 := by
    nlinarith [abs_nonneg (RHTower.complementaryPacketConstant ω)]
  linarith

/-- The critical Euler packet edge energy: the energy of the edge field of two independent copies
of the Euler prime-current clock. -/
def criticalEulerEdgeEnergy (ε : ℝ) : ℝ :=
  ε * ∫ w : ℝ × ℝ, (∫ t in Ioi (0 : ℝ),
      RHTower.packetEdgeField (packetShift ε) w.1 w.2 t ^ 2)
    ∂((eulerClockLaw (escape ε)).prod (eulerClockLaw (escape ε)))

/-- The Euler edge energy is four times the packet energy of the clock gap. -/
theorem criticalEulerEdgeEnergy_eq (ε : ℝ) :
    criticalEulerEdgeEnergy ε
      = 4 * ε * ∫ x, RHTower.packetTranslationModulus
          (RHTower.complementaryPacketKernel (packetShift ε))
          (RHTower.complementaryPacketConstant (packetShift ε)) |x|
        ∂(independentGapLaw (eulerClockLaw (escape ε)) (eulerClockLaw (escape ε))) := by
  haveI := isProbabilityMeasure_eulerClockLaw (one_lt_escape ε)
  set ω : ℝ := packetShift ε with hωdef
  have hω : (0 : ℝ) ≤ ω := packetShift_nonneg ε
  have hmeasD : Measurable fun x : ℝ => RHTower.packetTranslationModulus
      (RHTower.complementaryPacketKernel ω) (RHTower.complementaryPacketConstant ω) |x| :=
    (RHTower.measurable_packetTranslationModulus
      (RHTower.measurable_complementaryPacketKernel ω hω)
      (RHTower.integrableOn_complementaryPacketKernel ω hω)
      (RHTower.integrableOn_complementaryPacketKernel_sq ω hω) _).comp continuous_abs.measurable
  have hgap : (∫ x, RHTower.packetTranslationModulus
        (RHTower.complementaryPacketKernel ω) (RHTower.complementaryPacketConstant ω) |x|
        ∂(independentGapLaw (eulerClockLaw (escape ε)) (eulerClockLaw (escape ε))))
      = ∫ w : ℝ × ℝ, RHTower.packetTranslationModulus
          (RHTower.complementaryPacketKernel ω) (RHTower.complementaryPacketConstant ω)
          |w.1 - w.2| ∂((eulerClockLaw (escape ε)).prod (eulerClockLaw (escape ε))) :=
    integral_independentGapLaw _ _ hmeasD.aestronglyMeasurable
  have hpt : (∫ w : ℝ × ℝ, (∫ t in Ioi (0 : ℝ), RHTower.packetEdgeField ω w.1 w.2 t ^ 2)
        ∂((eulerClockLaw (escape ε)).prod (eulerClockLaw (escape ε))))
      = ∫ w : ℝ × ℝ, 4 * RHTower.packetTranslationModulus
          (RHTower.complementaryPacketKernel ω) (RHTower.complementaryPacketConstant ω)
          |w.1 - w.2| ∂((eulerClockLaw (escape ε)).prod (eulerClockLaw (escape ε))) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_nonneg_fst_prod (eulerClockLaw (escape ε)) (eulerClockLaw (escape ε))
        (eulerClockLaw_Iio_zero (escape ε)),
      ae_nonneg_snd_prod (eulerClockLaw (escape ε)) (eulerClockLaw (escape ε))
        (eulerClockLaw_Iio_zero (escape ε))] with w h1 h2
    rw [RHTower.integral_packetEdgeField_sq, RHTower.packetPathDistanceSq_eq_abs hω h2 h1,
      abs_sub_comm]
  rw [criticalEulerEdgeEnergy, hgap, ← hωdef, hpt, integral_const_mul]
  ring

/-- **The critical Euler edge field carries exactly four units.** -/
theorem tendsto_criticalEulerEdgeEnergy :
    Tendsto criticalEulerEdgeEnergy (𝓝[>] (0 : ℝ)) (𝓝 4) := by
  haveI hprob : ∀ ε : ℝ, IsProbabilityMeasure (eulerClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_eulerClockLaw (one_lt_escape ε)
  set μ : ℝ → Measure ℝ := fun ε =>
    independentGapLaw (eulerClockLaw (escape ε)) (eulerClockLaw (escape ε)) with hμdef
  haveI : ∀ ε : ℝ, IsProbabilityMeasure (μ ε) := fun ε => by
    rw [hμdef]
    infer_instance
  have habs : ∀ ε : ℝ, Integrable (fun x : ℝ => |x|) (μ ε) := fun ε =>
    integrable_abs_independentGapLaw _ _ (integrable_id_eulerClockLaw (one_lt_escape ε))
      (integrable_id_eulerClockLaw (one_lt_escape ε))
  have hDint : ∀ ε : ℝ, Integrable (fun x : ℝ => RHTower.packetTranslationModulus
      (RHTower.complementaryPacketKernel (packetShift ε))
      (RHTower.complementaryPacketConstant (packetShift ε)) |x|) (μ ε) := fun ε =>
    RHTower.integrable_packetTranslationModulus_abs
      (RHTower.measurable_complementaryPacketKernel _ (packetShift_nonneg ε))
      (RHTower.integrableOn_complementaryPacketKernel _ (packetShift_nonneg ε))
      (RHTower.integrableOn_complementaryPacketKernel_sq _ (packetShift_nonneg ε))
      (le_refl _) (le_refl _) (habs ε)
  have hεabs : Tendsto (fun ε : ℝ => ε * ∫ x, |x| ∂(μ ε)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine tendsto_integral_abs_sub_prod_scaledEulerClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : (0 : ℝ) < ε := hε
    haveI := hprob ε
    haveI := isProbabilityMeasure_eulerClockLaw (show (1 : ℝ) < 1 + ε by linarith)
    have hgap : (∫ x, |x| ∂(μ ε))
        = ∫ w : ℝ × ℝ, |w.1 - w.2|
          ∂((eulerClockLaw (escape ε)).prod (eulerClockLaw (escape ε))) := by
      rw [hμdef]
      exact integral_independentGapLaw _ _ (f := fun x : ℝ => |x|)
        (measurable_id.abs).aestronglyMeasurable
    rw [hgap, scaledEulerClockLaw, escape_eq_of_pos hεpos,
      show (1 : ℝ) + ε - 1 = ε by ring, integral_abs_sub_prod_scaleLaw hεpos]
  have hc : Tendsto (fun ε : ℝ => RHTower.complementaryPacketConstant (packetShift ε))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hcont : Tendsto (fun ω : ℝ => 1 / (1 + ω)) (𝓝 (0 : ℝ)) (𝓝 (1 / (1 + 0))) := by
      refine Filter.Tendsto.div tendsto_const_nhds (tendsto_const_nhds.add tendsto_id) ?_
      norm_num
    have h := hcont.comp tendsto_packetShift
    simpa [RHTower.complementaryPacketConstant, Function.comp_def] using h
  have hmain := RHTower.tendsto_four_mul_packetEnergy
    (F := 𝓝[>] (0 : ℝ)) (μ := μ) (ε := fun ε : ℝ => ε)
    (c := fun ε : ℝ => RHTower.complementaryPacketConstant (packetShift ε))
    (D := fun ε : ℝ => RHTower.packetTranslationModulus
      (RHTower.complementaryPacketKernel (packetShift ε))
      (RHTower.complementaryPacketConstant (packetShift ε)))
    (C := 24)
    (fun ε a ha => abs_packetModulus_sub_le_uniform ε a ha) hDint habs
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using le_of_lt hε)
    (tendsto_id.mono_left nhdsWithin_le_nhds) hεabs hc
  refine hmain.congr fun ε => ?_
  rw [criticalEulerEdgeEnergy_eq ε, hμdef]

/-- **`(22)`: the Gamma/Sonin budget.**  Any transform whose packet energy is bounded by a factor
tending to one — entrywise Gamma multiplication, whose norm tends to one, composed with the
contractive Sonin compression — carries the critical Euler edge field with limiting energy at most
four.  This is the card's `limsup ≤ 4`, stated as an eventual bound. -/
theorem eventually_criticalEulerTransformedEnergy_le (T : ℝ → (ℝ → ℝ) → ℝ → ℝ) (m : ℝ → ℝ)
    (hT : ∀ ε f, IntegrableOn (fun t => f t ^ 2) (Ioi (0 : ℝ)) →
      (∫ t in Ioi (0 : ℝ), T ε f t ^ 2) ≤ m ε ^ 2 * ∫ t in Ioi (0 : ℝ), f t ^ 2)
    (hmlim : Tendsto (fun ε => m ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * ∫ w : ℝ × ℝ, (∫ t in Ioi (0 : ℝ),
        T ε (RHTower.packetEdgeField (packetShift ε) w.1 w.2) t ^ 2)
        ∂((eulerClockLaw (escape ε)).prod (eulerClockLaw (escape ε)))
      ≤ 4 + δ := by
  haveI hprob : ∀ ε : ℝ, IsProbabilityMeasure (eulerClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_eulerClockLaw (one_lt_escape ε)
  have hlim : Tendsto (fun ε : ℝ => m ε ^ 2 * criticalEulerEdgeEnergy ε) (𝓝[>] (0 : ℝ)) (𝓝 4) := by
    have h := hmlim.mul tendsto_criticalEulerEdgeEnergy
    simpa using h
  have hev := hlim.eventually (eventually_lt_nhds (by linarith : (4 : ℝ) < 4 + δ))
  filter_upwards [self_mem_nhdsWithin, hev] with ε hε hlt
  have hεpos : (0 : ℝ) < ε := hε
  haveI := hprob ε
  -- the energy of the edge field is integrable against the independent product
  have hedgeInt : Integrable (fun w : ℝ × ℝ => ∫ t in Ioi (0 : ℝ),
      RHTower.packetEdgeField (packetShift ε) w.1 w.2 t ^ 2)
      ((eulerClockLaw (escape ε)).prod (eulerClockLaw (escape ε))) := by
    have hω : (0 : ℝ) ≤ packetShift ε := packetShift_nonneg ε
    have hmeasD : Measurable fun x : ℝ => RHTower.packetTranslationModulus
        (RHTower.complementaryPacketKernel (packetShift ε))
        (RHTower.complementaryPacketConstant (packetShift ε)) |x| :=
      (RHTower.measurable_packetTranslationModulus
        (RHTower.measurable_complementaryPacketKernel _ hω)
        (RHTower.integrableOn_complementaryPacketKernel _ hω)
        (RHTower.integrableOn_complementaryPacketKernel_sq _ hω) _).comp continuous_abs.measurable
    have habs : Integrable (fun x : ℝ => |x|)
        (independentGapLaw (eulerClockLaw (escape ε)) (eulerClockLaw (escape ε))) :=
      integrable_abs_independentGapLaw _ _ (integrable_id_eulerClockLaw (one_lt_escape ε))
        (integrable_id_eulerClockLaw (one_lt_escape ε))
    have hDint : Integrable (fun x : ℝ => RHTower.packetTranslationModulus
        (RHTower.complementaryPacketKernel (packetShift ε))
        (RHTower.complementaryPacketConstant (packetShift ε)) |x|)
        (independentGapLaw (eulerClockLaw (escape ε)) (eulerClockLaw (escape ε))) :=
      RHTower.integrable_packetTranslationModulus_abs
        (RHTower.measurable_complementaryPacketKernel _ hω)
        (RHTower.integrableOn_complementaryPacketKernel _ hω)
        (RHTower.integrableOn_complementaryPacketKernel_sq _ hω) (le_refl _) (le_refl _) habs
    have hcomp := integrable_comp_independentGap (eulerClockLaw (escape ε))
      (eulerClockLaw (escape ε)) hmeasD.aestronglyMeasurable hDint
    refine (hcomp.const_mul 4).congr ?_
    filter_upwards [ae_nonneg_fst_prod (eulerClockLaw (escape ε)) (eulerClockLaw (escape ε))
        (eulerClockLaw_Iio_zero (escape ε)),
      ae_nonneg_snd_prod (eulerClockLaw (escape ε)) (eulerClockLaw (escape ε))
        (eulerClockLaw_Iio_zero (escape ε))] with w h1 h2
    rw [RHTower.integral_packetEdgeField_sq, RHTower.packetPathDistanceSq_eq_abs hω h2 h1,
      abs_sub_comm]
  have hbound : (∫ w : ℝ × ℝ, (∫ t in Ioi (0 : ℝ),
        T ε (RHTower.packetEdgeField (packetShift ε) w.1 w.2) t ^ 2)
        ∂((eulerClockLaw (escape ε)).prod (eulerClockLaw (escape ε))))
      ≤ m ε ^ 2 * ∫ w : ℝ × ℝ, (∫ t in Ioi (0 : ℝ),
        RHTower.packetEdgeField (packetShift ε) w.1 w.2 t ^ 2)
        ∂((eulerClockLaw (escape ε)).prod (eulerClockLaw (escape ε))) := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun w =>
        setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
      (hedgeInt.const_mul _) ?_
    filter_upwards [ae_nonneg_fst_prod (eulerClockLaw (escape ε)) (eulerClockLaw (escape ε))
        (eulerClockLaw_Iio_zero (escape ε)),
      ae_nonneg_snd_prod (eulerClockLaw (escape ε)) (eulerClockLaw (escape ε))
        (eulerClockLaw_Iio_zero (escape ε))] with w h1 h2
    exact hT ε (RHTower.packetEdgeField (packetShift ε) w.1 w.2)
      (RHTower.integrableOn_packetEdgeField_sq (packetShift_nonneg ε) h1 h2)
  calc ε * ∫ w : ℝ × ℝ, (∫ t in Ioi (0 : ℝ),
        T ε (RHTower.packetEdgeField (packetShift ε) w.1 w.2) t ^ 2)
        ∂((eulerClockLaw (escape ε)).prod (eulerClockLaw (escape ε)))
      ≤ ε * (m ε ^ 2 * ∫ w : ℝ × ℝ, (∫ t in Ioi (0 : ℝ),
          RHTower.packetEdgeField (packetShift ε) w.1 w.2 t ^ 2)
          ∂((eulerClockLaw (escape ε)).prod (eulerClockLaw (escape ε)))) :=
        mul_le_mul_of_nonneg_left hbound (le_of_lt hεpos)
    _ = m ε ^ 2 * criticalEulerEdgeEnergy ε := by
        rw [criticalEulerEdgeEnergy]
        ring
    _ ≤ 4 + δ := le_of_lt hlt

/-! ### The squarefree edge field and the asymptotic isometry -/

/-- The critical squarefree packet edge energy: the energy of the edge field of two independent
copies of the squarefree divisor clock, in the same framing as the Euler one. -/
def criticalSquarefreeEdgeEnergy (ε : ℝ) : ℝ :=
  ε * ∫ w : ℝ × ℝ, (∫ t in Ioi (0 : ℝ),
      RHTower.packetEdgeField (packetShift ε) w.1 w.2 t ^ 2)
    ∂((squarefreeClockLaw (escape ε)).prod (squarefreeClockLaw (escape ε)))

/-- The squarefree edge energy is four times the packet energy of the clock gap. -/
theorem criticalSquarefreeEdgeEnergy_eq (ε : ℝ) :
    criticalSquarefreeEdgeEnergy ε
      = 4 * ε * ∫ x, RHTower.packetTranslationModulus
          (RHTower.complementaryPacketKernel (packetShift ε))
          (RHTower.complementaryPacketConstant (packetShift ε)) |x|
        ∂(independentGapLaw (squarefreeClockLaw (escape ε)) (squarefreeClockLaw (escape ε))) := by
  haveI := isProbabilityMeasure_squarefreeClockLaw (one_lt_escape ε)
  set ω : ℝ := packetShift ε with hωdef
  have hω : (0 : ℝ) ≤ ω := packetShift_nonneg ε
  have hmeasD : Measurable fun x : ℝ => RHTower.packetTranslationModulus
      (RHTower.complementaryPacketKernel ω) (RHTower.complementaryPacketConstant ω) |x| :=
    (RHTower.measurable_packetTranslationModulus
      (RHTower.measurable_complementaryPacketKernel ω hω)
      (RHTower.integrableOn_complementaryPacketKernel ω hω)
      (RHTower.integrableOn_complementaryPacketKernel_sq ω hω) _).comp continuous_abs.measurable
  have hgap : (∫ x, RHTower.packetTranslationModulus
        (RHTower.complementaryPacketKernel ω) (RHTower.complementaryPacketConstant ω) |x|
        ∂(independentGapLaw (squarefreeClockLaw (escape ε)) (squarefreeClockLaw (escape ε))))
      = ∫ w : ℝ × ℝ, RHTower.packetTranslationModulus
          (RHTower.complementaryPacketKernel ω) (RHTower.complementaryPacketConstant ω)
          |w.1 - w.2| ∂((squarefreeClockLaw (escape ε)).prod (squarefreeClockLaw (escape ε))) :=
    integral_independentGapLaw _ _ hmeasD.aestronglyMeasurable
  have hpt : (∫ w : ℝ × ℝ, (∫ t in Ioi (0 : ℝ), RHTower.packetEdgeField ω w.1 w.2 t ^ 2)
        ∂((squarefreeClockLaw (escape ε)).prod (squarefreeClockLaw (escape ε))))
      = ∫ w : ℝ × ℝ, 4 * RHTower.packetTranslationModulus
          (RHTower.complementaryPacketKernel ω) (RHTower.complementaryPacketConstant ω)
          |w.1 - w.2| ∂((squarefreeClockLaw (escape ε)).prod (squarefreeClockLaw (escape ε))) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_nonneg_fst_prod (squarefreeClockLaw (escape ε))
        (squarefreeClockLaw (escape ε)) (squarefreeClockLaw_Iio_zero (escape ε)),
      ae_nonneg_snd_prod (squarefreeClockLaw (escape ε)) (squarefreeClockLaw (escape ε))
        (squarefreeClockLaw_Iio_zero (escape ε))] with w h1 h2
    rw [RHTower.integral_packetEdgeField_sq, RHTower.packetPathDistanceSq_eq_abs hω h2 h1,
      abs_sub_comm]
  rw [criticalSquarefreeEdgeEnergy, hgap, ← hωdef, hpt, integral_const_mul]
  ring

/-- **The critical squarefree edge field carries exactly four units.** -/
theorem tendsto_criticalSquarefreeEdgeEnergy :
    Tendsto criticalSquarefreeEdgeEnergy (𝓝[>] (0 : ℝ)) (𝓝 4) := by
  haveI hprob : ∀ ε : ℝ, IsProbabilityMeasure (squarefreeClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_squarefreeClockLaw (one_lt_escape ε)
  set μ : ℝ → Measure ℝ := fun ε =>
    independentGapLaw (squarefreeClockLaw (escape ε)) (squarefreeClockLaw (escape ε)) with hμdef
  haveI : ∀ ε : ℝ, IsProbabilityMeasure (μ ε) := fun ε => by
    rw [hμdef]
    infer_instance
  have habs : ∀ ε : ℝ, Integrable (fun x : ℝ => |x|) (μ ε) := fun ε =>
    integrable_abs_independentGapLaw _ _ (integrable_id_squarefreeClockLaw (one_lt_escape ε))
      (integrable_id_squarefreeClockLaw (one_lt_escape ε))
  have hDint : ∀ ε : ℝ, Integrable (fun x : ℝ => RHTower.packetTranslationModulus
      (RHTower.complementaryPacketKernel (packetShift ε))
      (RHTower.complementaryPacketConstant (packetShift ε)) |x|) (μ ε) := fun ε =>
    RHTower.integrable_packetTranslationModulus_abs
      (RHTower.measurable_complementaryPacketKernel _ (packetShift_nonneg ε))
      (RHTower.integrableOn_complementaryPacketKernel _ (packetShift_nonneg ε))
      (RHTower.integrableOn_complementaryPacketKernel_sq _ (packetShift_nonneg ε))
      (le_refl _) (le_refl _) (habs ε)
  have hεabs : Tendsto (fun ε : ℝ => ε * ∫ x, |x| ∂(μ ε)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine tendsto_integral_abs_sub_prod_scaledSquarefreeClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : (0 : ℝ) < ε := hε
    haveI := hprob ε
    haveI := isProbabilityMeasure_squarefreeClockLaw (show (1 : ℝ) < 1 + ε by linarith)
    have hgap : (∫ x, |x| ∂(μ ε))
        = ∫ w : ℝ × ℝ, |w.1 - w.2|
          ∂((squarefreeClockLaw (escape ε)).prod (squarefreeClockLaw (escape ε))) := by
      rw [hμdef]
      exact integral_independentGapLaw _ _ (f := fun x : ℝ => |x|)
        (measurable_id.abs).aestronglyMeasurable
    rw [hgap, scaledSquarefreeClockLaw, escape_eq_of_pos hεpos,
      show (1 : ℝ) + ε - 1 = ε by ring, integral_abs_sub_prod_scaleLaw hεpos]
  have hc : Tendsto (fun ε : ℝ => RHTower.complementaryPacketConstant (packetShift ε))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hcont : Tendsto (fun ω : ℝ => 1 / (1 + ω)) (𝓝 (0 : ℝ)) (𝓝 (1 / (1 + 0))) := by
      refine Filter.Tendsto.div tendsto_const_nhds (tendsto_const_nhds.add tendsto_id) ?_
      norm_num
    have h := hcont.comp tendsto_packetShift
    simpa [RHTower.complementaryPacketConstant, Function.comp_def] using h
  have hmain := RHTower.tendsto_four_mul_packetEnergy
    (F := 𝓝[>] (0 : ℝ)) (μ := μ) (ε := fun ε : ℝ => ε)
    (c := fun ε : ℝ => RHTower.complementaryPacketConstant (packetShift ε))
    (D := fun ε : ℝ => RHTower.packetTranslationModulus
      (RHTower.complementaryPacketKernel (packetShift ε))
      (RHTower.complementaryPacketConstant (packetShift ε)))
    (C := 24)
    (fun ε a ha => abs_packetModulus_sub_le_uniform ε a ha) hDint habs
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using le_of_lt hε)
    (tendsto_id.mono_left nhdsWithin_le_nhds) hεabs hc
  refine hmain.congr fun ε => ?_
  rw [criticalSquarefreeEdgeEnergy_eq ε, hμdef]

/-- **`(21)` as an asymptotic isometry of the complete source packet fields.**  Both edge fields
carry exactly four units in the limit, and their mutual packet distance vanishes: the squarefree
and Euler packet fields are asymptotically isometric, not merely equal in one scalar. -/
theorem criticalPacketFields_asymptotic_isometry :
    Tendsto criticalSquarefreeEdgeEnergy (𝓝[>] (0 : ℝ)) (𝓝 4) ∧
      Tendsto criticalEulerEdgeEnergy (𝓝[>] (0 : ℝ)) (𝓝 4) ∧
      Tendsto criticalPacketEdgeCost (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  ⟨tendsto_criticalSquarefreeEdgeEnergy, tendsto_criticalEulerEdgeEnergy,
    tendsto_criticalPacketEdgeCost⟩

/-- **A Gamma/Sonin model satisfies the budget hypotheses.**  Entrywise multiplication by a scalar
`c ε` composed with a pointwise contraction `q` — the model of Gamma multiplication followed by
Sonin compression — has packet energy bounded by `|c ε|²`, so `(22)` applies to it. -/
theorem gammaSoninModel_energy_le (c : ℝ → ℝ) (q : ℝ → ℝ) (hq : ∀ t, |q t| ≤ 1) (ε : ℝ)
    (f : ℝ → ℝ) (hf : IntegrableOn (fun t => f t ^ 2) (Ioi (0 : ℝ))) :
    (∫ t in Ioi (0 : ℝ), (c ε * q t * f t) ^ 2)
      ≤ |c ε| ^ 2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun t => sq_nonneg _) (hf.const_mul _)
    (Filter.Eventually.of_forall fun t => ?_)
  have hq1 : q t ^ 2 ≤ 1 := by
    have h := hq t
    nlinarith [abs_nonneg (q t), sq_abs (q t)]
  have hc : c ε ^ 2 = |c ε| ^ 2 := (sq_abs _).symm
  have hnn : 0 ≤ c ε ^ 2 * f t ^ 2 := by positivity
  calc (c ε * q t * f t) ^ 2 = c ε ^ 2 * f t ^ 2 * q t ^ 2 := by ring
    _ ≤ c ε ^ 2 * f t ^ 2 * 1 := by
        exact mul_le_mul_of_nonneg_left hq1 hnn
    _ = |c ε| ^ 2 * f t ^ 2 := by rw [mul_one, hc]

/-- **`(22)` is not vacuous.**  The Gamma/Sonin model with a scalar tending to one satisfies both
hypotheses of the budget theorem, so the four-unit ceiling applies to a genuine transform family. -/
theorem eventually_gammaSoninModel_energy_le_four {c : ℝ → ℝ}
    (hc : Tendsto (fun ε => |c ε| ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 1)) (q : ℝ → ℝ) (hq : ∀ t, |q t| ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * ∫ w : ℝ × ℝ, (∫ t in Ioi (0 : ℝ),
        (c ε * q t * RHTower.packetEdgeField (packetShift ε) w.1 w.2 t) ^ 2)
        ∂((eulerClockLaw (escape ε)).prod (eulerClockLaw (escape ε)))
      ≤ 4 + δ :=
  eventually_criticalEulerTransformedEnergy_le
    (fun ε f t => c ε * q t * f t) (fun ε => |c ε|)
    (fun ε f hf => gammaSoninModel_energy_le c q hq ε f hf) hc hδ

end

end GaloisForLFunctions.HTGeometry
