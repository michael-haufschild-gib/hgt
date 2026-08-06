import GaloisForLFunctions.RHTower.ComplementaryPacketAffineFlux
import GaloisForLFunctions.RHTower.ComplementaryPacketCofinalIsometry

/-!
# The two-point distance of the boundary affine packet

The boundary affine packet based at a clock value `h ≥ 0` is the full-line profile translated to
`h`, read on the physical half line.  Two such packets differ by a square-integrable function even
though neither is square integrable, and the squared distance between them is exactly the two-point
modulus of the packet at their separation:

```text
∫₀^∞ (B_h - B_k)² = D_ω(|h - k|) .
```

The proof translates the base point away and splits the half line at the separation: before it the
difference is the incoming constant against the kernel, after it the difference of two translates
of the kernel.
-/

open MeasureTheory Set Filter

namespace RHTower

noncomputable section

variable {ω : ℝ}

/-- Translating a square-integrable kernel keeps it square integrable on the shifted half line. -/
theorem integrableOn_sub_const_sq {K : ℝ → ℝ} (hsq : IntegrableOn (fun r => K r ^ 2) (Ioi 0))
    (a : ℝ) : IntegrableOn (fun r => K (r - a) ^ 2) (Ioi a) := by
  have hmp : MeasurePreserving (fun r : ℝ => r - a) volume volume :=
    measurePreserving_sub_right volume a
  have hme : MeasurableEmbedding (fun r : ℝ => r - a) :=
    (Homeomorph.subRight a).measurableEmbedding
  have hpre : (fun r : ℝ => r - a) ⁻¹' (Ioi (0 : ℝ)) = Ioi a := by
    ext r
    simp
  have h := (hmp.integrableOn_comp_preimage hme (f := fun r => K r ^ 2) (s := Ioi (0 : ℝ))).2 hsq
  rwa [hpre] at h

/-- The squared distance between two points of the boundary affine packet path. -/
def packetPathDistanceSq (ω h k : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (affinePacketProfile ω (t - h) - affinePacketProfile ω (t - k)) ^ 2

/-- The packet difference vanishes before the base point. -/
theorem packet_difference_of_neg (ω : ℝ) {a r : ℝ} (ha : 0 ≤ a) (hr : r < 0) :
    affinePacketProfile ω (r - a) - affinePacketProfile ω r = 0 := by
  rw [affinePacketProfile_of_neg ω (by linarith), affinePacketProfile_of_neg ω hr, sub_self]

/-- Between the two base points the packet difference is the kernel against the incoming
constant. -/
theorem packet_difference_of_mem_Ioo (ω : ℝ) {a r : ℝ} (hr : r ∈ Ioo (0 : ℝ) a) :
    (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2
      = (complementaryPacketKernel ω r + complementaryPacketConstant ω) ^ 2 := by
  rw [affinePacketProfile_of_neg ω (by linarith [hr.2] : r - a < 0),
    affinePacketProfile_of_nonneg ω (le_of_lt hr.1)]
  ring_nf

/-- Past the separation the packet difference is a difference of two kernel translates. -/
theorem packet_difference_of_mem_Ioi (ω : ℝ) {a r : ℝ} (ha : 0 ≤ a) (hr : r ∈ Ioi a) :
    (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2
      = (complementaryPacketKernel ω (r - a) - complementaryPacketKernel ω r) ^ 2 := by
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt ha hr
  have hra : a < r := hr
  rw [affinePacketProfile_of_nonneg ω (by linarith : (0 : ℝ) ≤ r - a),
    affinePacketProfile_of_nonneg ω (le_of_lt hr0)]

/-- The packet difference is square integrable up to the separation. -/
theorem integrableOn_packet_difference_Ioc (hω : 0 ≤ ω) (a : ℝ) :
    IntegrableOn (fun r => (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2)
      (Ioc (0 : ℝ) a) := by
  have hK2 : IntegrableOn (fun r => complementaryPacketKernel ω r ^ 2) (Ioc (0 : ℝ) a) :=
    (integrableOn_complementaryPacketKernel_sq ω hω).mono_set Ioc_subset_Ioi_self
  have hK1 : IntegrableOn (complementaryPacketKernel ω) (Ioc (0 : ℝ) a) :=
    (integrableOn_complementaryPacketKernel ω hω).mono_set Ioc_subset_Ioi_self
  have hconst : IntegrableOn (fun _ : ℝ => complementaryPacketConstant ω ^ 2) (Ioc (0 : ℝ) a) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hsum : IntegrableOn (fun r => complementaryPacketKernel ω r ^ 2
      + 2 * complementaryPacketConstant ω * complementaryPacketKernel ω r
      + complementaryPacketConstant ω ^ 2) (Ioc (0 : ℝ) a) :=
    (hK2.add (hK1.const_mul (2 * complementaryPacketConstant ω))).add hconst
  have hmeas : Measurable fun r =>
      (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2 :=
    (((measurable_affinePacketProfile ω hω).comp (measurable_id.sub_const a)).sub
      (measurable_affinePacketProfile ω hω)).pow_const 2
  refine (Integrable.mono hsum hmeas.aestronglyMeasurable ?_)
  have hae : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) a)), r ∈ Ioo (0 : ℝ) a := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := a)] with r hr hrIoc
    exact hr.mpr hrIoc
  filter_upwards [hae] with r hr
  rw [Real.norm_eq_abs, Real.norm_eq_abs, packet_difference_of_mem_Ioo ω hr,
    abs_of_nonneg (sq_nonneg _)]
  have hexp : (complementaryPacketKernel ω r + complementaryPacketConstant ω) ^ 2
      = complementaryPacketKernel ω r ^ 2
        + 2 * complementaryPacketConstant ω * complementaryPacketKernel ω r
        + complementaryPacketConstant ω ^ 2 := by ring_nf
  rw [hexp]
  exact le_abs_self _

/-- The packet difference is square integrable past the separation. -/
theorem integrableOn_packet_difference_Ioi (hω : 0 ≤ ω) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun r => (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2)
      (Ioi a) := by
  have hK2 : IntegrableOn (fun r => complementaryPacketKernel ω r ^ 2) (Ioi a) :=
    (integrableOn_complementaryPacketKernel_sq ω hω).mono_set (Ioi_subset_Ioi ha)
  have hK2' : IntegrableOn (fun r => complementaryPacketKernel ω (r - a) ^ 2) (Ioi a) :=
    integrableOn_sub_const_sq (integrableOn_complementaryPacketKernel_sq ω hω) a
  have hsum : IntegrableOn (fun r => 2 * complementaryPacketKernel ω (r - a) ^ 2
      + 2 * complementaryPacketKernel ω r ^ 2) (Ioi a) :=
    (hK2'.const_mul 2).add (hK2.const_mul 2)
  have hmeas : Measurable fun r =>
      (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2 :=
    (((measurable_affinePacketProfile ω hω).comp (measurable_id.sub_const a)).sub
      (measurable_affinePacketProfile ω hω)).pow_const 2
  refine (Integrable.mono hsum hmeas.aestronglyMeasurable ?_)
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, packet_difference_of_mem_Ioi ω ha hr,
    abs_of_nonneg (sq_nonneg _)]
  refine le_trans ?_ (le_abs_self _)
  nlinarith [sq_nonneg (complementaryPacketKernel ω (r - a) + complementaryPacketKernel ω r)]

/-- **The shifted packet difference has the two-point modulus as its energy.** -/
theorem integral_packet_difference_sq (hω : 0 ≤ ω) {a : ℝ} (ha : 0 ≤ a) :
    (∫ r in Ioi (0 : ℝ), (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2)
      = packetTranslationModulus (complementaryPacketKernel ω)
        (complementaryPacketConstant ω) a := by
  have hsplit : (∫ r in Ioi (0 : ℝ),
        (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2)
      = (∫ r in Ioc (0 : ℝ) a, (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2)
        + ∫ r in Ioi a, (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2 := by
    rw [← Ioc_union_Ioi_eq_Ioi ha,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (integrableOn_packet_difference_Ioc hω a) (integrableOn_packet_difference_Ioi hω ha)]
  have hfirst : (∫ r in Ioc (0 : ℝ) a,
        (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2)
      = ∫ r in Ioc (0 : ℝ) a,
        (complementaryPacketKernel ω r + complementaryPacketConstant ω) ^ 2 := by
    rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun r hr =>
      packet_difference_of_mem_Ioo ω hr
  have hsecond : (∫ r in Ioi a, (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2)
      = ∫ r in Ioi (0 : ℝ),
        (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2 := by
    have hcongr : (∫ r in Ioi a, (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2)
        = ∫ r in Ioi a,
          (complementaryPacketKernel ω (r - a) - complementaryPacketKernel ω r) ^ 2 :=
      setIntegral_congr_fun measurableSet_Ioi fun r hr =>
        packet_difference_of_mem_Ioi ω ha hr
    rw [hcongr, ← setIntegral_Ioi_zero_comp_add_right
      (fun s => (complementaryPacketKernel ω (s - a) - complementaryPacketKernel ω s) ^ 2) a]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [add_sub_cancel_right]
    rw [← neg_sub (complementaryPacketKernel ω (r + a)) (complementaryPacketKernel ω r),
      neg_pow_two]
  rw [hsplit, hfirst, hsecond, packetTranslationModulus]

/-- **The two-point distance of the boundary affine packet.**  The squared distance between the
packets based at two nonnegative clock values is the two-point modulus at their separation. -/
theorem packetPathDistanceSq_eq (hω : 0 ≤ ω) {h k : ℝ} (hk : 0 ≤ k) (hkh : k ≤ h) :
    packetPathDistanceSq ω h k
      = packetTranslationModulus (complementaryPacketKernel ω)
        (complementaryPacketConstant ω) (h - k) := by
  have ha : (0 : ℝ) ≤ h - k := by linarith
  have htrans : packetPathDistanceSq ω h k
      = ∫ r in Ioi (-k), (affinePacketProfile ω (r - (h - k)) - affinePacketProfile ω r) ^ 2 := by
    have h1 := setIntegral_Ioi_comp_add_right'
      (fun s => (affinePacketProfile ω (s - h) - affinePacketProfile ω (s - k)) ^ 2) (-k) k
    rw [neg_add_cancel] at h1
    rw [packetPathDistanceSq, ← h1]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    have e1 : r + k - h = r - (h - k) := by ring_nf
    have e2 : r + k - k = r := by ring_nf
    rw [e1, e2]
  have hzero : (∫ r in Ioc (-k) (0 : ℝ),
      (affinePacketProfile ω (r - (h - k)) - affinePacketProfile ω r) ^ 2) = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
    rw [packet_difference_of_neg ω ha hr.2]
    ring_nf
  have hsplit : (∫ r in Ioi (-k),
        (affinePacketProfile ω (r - (h - k)) - affinePacketProfile ω r) ^ 2)
      = (∫ r in Ioc (-k) (0 : ℝ),
          (affinePacketProfile ω (r - (h - k)) - affinePacketProfile ω r) ^ 2)
        + ∫ r in Ioi (0 : ℝ),
          (affinePacketProfile ω (r - (h - k)) - affinePacketProfile ω r) ^ 2 := by
    have hle : (-k : ℝ) ≤ 0 := by linarith
    have hint1 : IntegrableOn
        (fun r => (affinePacketProfile ω (r - (h - k)) - affinePacketProfile ω r) ^ 2)
        (Ioc (-k) (0 : ℝ)) := by
      have hmeas : Measurable fun r =>
          (affinePacketProfile ω (r - (h - k)) - affinePacketProfile ω r) ^ 2 :=
        (((measurable_affinePacketProfile ω hω).comp (measurable_id.sub_const (h - k))).sub
          (measurable_affinePacketProfile ω hω)).pow_const 2
      refine Integrable.mono (integrableOn_const (C := (0 : ℝ)) (hs := measure_Ioc_lt_top.ne))
        hmeas.aestronglyMeasurable ?_
      have hae : ∀ᵐ r ∂(volume.restrict (Ioc (-k) (0 : ℝ))), r ∈ Ioo (-k) (0 : ℝ) := by
        rw [ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [Ioo_ae_eq_Ioc (a := (-k : ℝ)) (b := (0 : ℝ))] with r hr hrIoc
        exact hr.mpr hrIoc
      filter_upwards [hae] with r hr
      rw [packet_difference_of_neg ω ha hr.2]
      simp
    have hint2 : IntegrableOn
        (fun r => (affinePacketProfile ω (r - (h - k)) - affinePacketProfile ω r) ^ 2)
        (Ioi (0 : ℝ)) := by
      have hsplit2 := integrableOn_packet_difference_Ioc hω (h - k)
      have hsplit3 := integrableOn_packet_difference_Ioi hω ha
      rw [← Ioc_union_Ioi_eq_Ioi ha]
      exact hsplit2.union hsplit3
    rw [← Ioc_union_Ioi_eq_Ioi hle,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint1 hint2]
  rw [htrans, hsplit, hzero, zero_add, integral_packet_difference_sq hω ha]

/-- The two-point distance is symmetric. -/
theorem packetPathDistanceSq_symm (ω h k : ℝ) :
    packetPathDistanceSq ω h k = packetPathDistanceSq ω k h := by
  rw [packetPathDistanceSq, packetPathDistanceSq]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [← neg_sub (affinePacketProfile ω (t - h)) (affinePacketProfile ω (t - k)), neg_pow_two]

/-- **The two-point distance of the boundary affine packet at arbitrary clock values.** -/
theorem packetPathDistanceSq_eq_abs (hω : 0 ≤ ω) {h k : ℝ} (hh : 0 ≤ h) (hk : 0 ≤ k) :
    packetPathDistanceSq ω h k
      = packetTranslationModulus (complementaryPacketKernel ω)
        (complementaryPacketConstant ω) |h - k| := by
  rcases le_total k h with hkh | hhk
  · rw [packetPathDistanceSq_eq hω hk hkh, abs_of_nonneg (by linarith : (0 : ℝ) ≤ h - k)]
  · rw [packetPathDistanceSq_symm, packetPathDistanceSq_eq hω hh hhk,
      abs_of_nonpos (by linarith : h - k ≤ (0 : ℝ)), neg_sub]

/-- **The cofinal bound at the two-point distance.**  The squared packet distance between two
clock values exceeds the affine term by at most the uniform defect. -/
theorem packetPathDistanceSq_le (hω : 0 ≤ ω) {h k : ℝ} (hh : 0 ≤ h) (hk : 0 ≤ k) :
    packetPathDistanceSq ω h k
      ≤ complementaryPacketConstant ω ^ 2 * |h - k| + (5 * 4 ^ ω
        + 2 * |complementaryPacketConstant ω| * 2 ^ ω) := by
  have hbound := abs_complementaryPacketModulus_sub_le ω hω (abs_nonneg (h - k))
  have h := (abs_le.mp hbound).2
  rw [packetPathDistanceSq_eq_abs hω hh hk]
  linarith

/-- The two-point distance is nonnegative. -/
theorem packetPathDistanceSq_nonneg (ω h k : ℝ) : 0 ≤ packetPathDistanceSq ω h k :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _

/-! ### The packet edge field -/

/-- The shifted packet difference is square integrable on every half line reaching the origin. -/
theorem integrableOn_packet_shifted_difference (hω : 0 ≤ ω) {a : ℝ} (ha : 0 ≤ a) {L : ℝ}
    (hL : L ≤ 0) :
    IntegrableOn (fun r => (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2)
      (Ioi L) := by
  have hmeas : Measurable fun r =>
      (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2 :=
    (((measurable_affinePacketProfile ω hω).comp (measurable_id.sub_const a)).sub
      (measurable_affinePacketProfile ω hω)).pow_const 2
  have hint1 : IntegrableOn
      (fun r => (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2)
      (Ioc L (0 : ℝ)) := by
    refine Integrable.mono (integrableOn_const (C := (0 : ℝ)) (hs := measure_Ioc_lt_top.ne))
      hmeas.aestronglyMeasurable ?_
    have hae : ∀ᵐ r ∂(volume.restrict (Ioc L (0 : ℝ))), r ∈ Ioo L (0 : ℝ) := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [Ioo_ae_eq_Ioc (a := L) (b := (0 : ℝ))] with r hr hrIoc
      exact hr.mpr hrIoc
    filter_upwards [hae] with r hr
    rw [packet_difference_of_neg ω ha hr.2]
    simp
  have hint2 : IntegrableOn
      (fun r => (affinePacketProfile ω (r - a) - affinePacketProfile ω r) ^ 2)
      (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha]
    exact (integrableOn_packet_difference_Ioc hω a).union
      (integrableOn_packet_difference_Ioi hω ha)
  rw [← Ioc_union_Ioi_eq_Ioi hL]
  exact hint1.union hint2

/-- The packet difference of two nonnegative clock values is square integrable. -/
theorem integrableOn_packetPathDifference (hω : 0 ≤ ω) {h k : ℝ} (hh : 0 ≤ h) (hk : 0 ≤ k) :
    IntegrableOn (fun t => (affinePacketProfile ω (t - h) - affinePacketProfile ω (t - k)) ^ 2)
      (Ioi (0 : ℝ)) := by
  have key : ∀ {u v : ℝ}, 0 ≤ v → v ≤ u →
      IntegrableOn (fun t => (affinePacketProfile ω (t - u) - affinePacketProfile ω (t - v)) ^ 2)
        (Ioi (0 : ℝ)) := by
    intro u v hv hvu
    have ha : (0 : ℝ) ≤ u - v := by linarith
    have hmp : MeasurePreserving (fun t : ℝ => t - v) volume volume :=
      measurePreserving_sub_right volume v
    have hme : MeasurableEmbedding (fun t : ℝ => t - v) :=
      (Homeomorph.subRight v).measurableEmbedding
    have hpre : (fun t : ℝ => t - v) ⁻¹' (Ioi (-v)) = Ioi (0 : ℝ) := by
      ext t
      simp
    have hbase := integrableOn_packet_shifted_difference hω ha (by linarith : (-v : ℝ) ≤ 0)
    have hI := (hmp.integrableOn_comp_preimage hme
      (f := fun r => (affinePacketProfile ω (r - (u - v)) - affinePacketProfile ω r) ^ 2)
      (s := Ioi (-v))).2 hbase
    rw [hpre] at hI
    refine hI.congr_fun (fun t _ => ?_) measurableSet_Ioi
    show (affinePacketProfile ω (t - v - (u - v)) - affinePacketProfile ω (t - v)) ^ 2
      = (affinePacketProfile ω (t - u) - affinePacketProfile ω (t - v)) ^ 2
    have e : t - v - (u - v) = t - u := by ring_nf
    rw [e]
  rcases le_total k h with hkh | hhk
  · exact key hk hkh
  · refine (key hh hhk).congr_fun (fun t _ => ?_) measurableSet_Ioi
    show (affinePacketProfile ω (t - k) - affinePacketProfile ω (t - h)) ^ 2
      = (affinePacketProfile ω (t - h) - affinePacketProfile ω (t - k)) ^ 2
    rw [← neg_sub (affinePacketProfile ω (t - h)) (affinePacketProfile ω (t - k)), neg_pow_two]

/-- The complementary-packet edge field of a clock pair: twice the packet increment between the
two independent clock values. -/
def packetEdgeField (ω h h' t : ℝ) : ℝ :=
  2 * (affinePacketProfile ω (t - h') - affinePacketProfile ω (t - h))

/-- The squared distance between two packet edge fields. -/
def packetEdgeFieldDistanceSq (ω h k h' k' : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (packetEdgeField ω h h' t - packetEdgeField ω k k' t) ^ 2

theorem packetEdgeFieldDistanceSq_nonneg (ω h k h' k' : ℝ) :
    0 ≤ packetEdgeFieldDistanceSq ω h k h' k' :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _

/-- **The edge fields are within the packet distances of their endpoints.**  This is the
parallelogram bound that turns vanishing packet transport cost into an asymptotic isometry of the
edge fields. -/
theorem packetEdgeFieldDistanceSq_le (hω : 0 ≤ ω) {h k h' k' : ℝ} (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hh' : 0 ≤ h') (hk' : 0 ≤ k') :
    packetEdgeFieldDistanceSq ω h k h' k'
      ≤ 8 * packetPathDistanceSq ω h' k' + 8 * packetPathDistanceSq ω h k := by
  have hint1 := integrableOn_packetPathDifference hω hh' hk'
  have hint2 := integrableOn_packetPathDifference hω hh hk
  have hdom : IntegrableOn (fun t =>
      8 * (affinePacketProfile ω (t - h') - affinePacketProfile ω (t - k')) ^ 2
      + 8 * (affinePacketProfile ω (t - h) - affinePacketProfile ω (t - k)) ^ 2)
      (Ioi (0 : ℝ)) := (hint1.const_mul 8).add (hint2.const_mul 8)
  have hmeas : Measurable fun t =>
      (packetEdgeField ω h h' t - packetEdgeField ω k k' t) ^ 2 := by
    have hb : ∀ x : ℝ, Measurable fun t : ℝ => affinePacketProfile ω (t - x) := fun x =>
      (measurable_affinePacketProfile ω hω).comp (measurable_id.sub_const x)
    exact ((((hb h').sub (hb h)).const_mul 2).sub (((hb k').sub (hb k)).const_mul 2)).pow_const 2
  have hpt : ∀ t : ℝ, (packetEdgeField ω h h' t - packetEdgeField ω k k' t) ^ 2
      ≤ 8 * (affinePacketProfile ω (t - h') - affinePacketProfile ω (t - k')) ^ 2
        + 8 * (affinePacketProfile ω (t - h) - affinePacketProfile ω (t - k)) ^ 2 := by
    intro t
    rw [packetEdgeField, packetEdgeField]
    nlinarith [sq_nonneg ((affinePacketProfile ω (t - h') - affinePacketProfile ω (t - k'))
      + (affinePacketProfile ω (t - h) - affinePacketProfile ω (t - k)))]
  have hintLHS : IntegrableOn (fun t =>
      (packetEdgeField ω h h' t - packetEdgeField ω k k' t) ^ 2) (Ioi (0 : ℝ)) := by
    refine Integrable.mono hdom hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤
        8 * (affinePacketProfile ω (t - h') - affinePacketProfile ω (t - k')) ^ 2
        + 8 * (affinePacketProfile ω (t - h) - affinePacketProfile ω (t - k)) ^ 2)]
    exact hpt t
  calc packetEdgeFieldDistanceSq ω h k h' k'
      ≤ ∫ t in Ioi (0 : ℝ),
          (8 * (affinePacketProfile ω (t - h') - affinePacketProfile ω (t - k')) ^ 2
            + 8 * (affinePacketProfile ω (t - h) - affinePacketProfile ω (t - k)) ^ 2) :=
        integral_mono_ae hintLHS hdom (Filter.Eventually.of_forall hpt)
    _ = 8 * packetPathDistanceSq ω h' k' + 8 * packetPathDistanceSq ω h k := by
        rw [integral_add (hint1.const_mul 8) (hint2.const_mul 8), integral_const_mul,
          integral_const_mul, packetPathDistanceSq, packetPathDistanceSq]

/-- The squared edge field is integrable on the physical half line. -/
theorem integrableOn_packetEdgeField_sq (hω : 0 ≤ ω) {h h' : ℝ} (hh : 0 ≤ h) (hh' : 0 ≤ h') :
    IntegrableOn (fun t => packetEdgeField ω h h' t ^ 2) (Ioi (0 : ℝ)) := by
  have h4 : IntegrableOn
      (fun t => 4 * (affinePacketProfile ω (t - h') - affinePacketProfile ω (t - h)) ^ 2)
      (Ioi (0 : ℝ)) := (integrableOn_packetPathDifference hω hh' hh).const_mul 4
  refine MeasureTheory.IntegrableOn.congr_fun h4 (fun t _ => ?_) measurableSet_Ioi
  show 4 * (affinePacketProfile ω (t - h') - affinePacketProfile ω (t - h)) ^ 2
    = packetEdgeField ω h h' t ^ 2
  rw [packetEdgeField]
  ring

/-- **The edge-field distance is measurable in the four clock values.**  Joint measurability of the
integrand in the parameters and the half-line variable gives it by Fubini. -/
theorem measurable_packetEdgeFieldDistanceSq (hω : 0 ≤ ω) :
    Measurable fun W : (ℝ × ℝ) × (ℝ × ℝ) =>
      packetEdgeFieldDistanceSq ω W.1.1 W.1.2 W.2.1 W.2.2 := by
  have hprof : ∀ f : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ → ℝ, Measurable f →
      Measurable fun p : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ => affinePacketProfile ω (p.2 - f p) := by
    intro f hf
    exact (measurable_affinePacketProfile ω hω).comp (measurable_snd.sub hf)
  have h1 := hprof (fun p => p.1.2.1) (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have h2 := hprof (fun p => p.1.1.1) (measurable_fst.comp (measurable_fst.comp measurable_fst))
  have h3 := hprof (fun p => p.1.2.2) (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have h4 := hprof (fun p => p.1.1.2) (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hjoint : StronglyMeasurable fun p : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ =>
      (packetEdgeField ω p.1.1.1 p.1.2.1 p.2 - packetEdgeField ω p.1.1.2 p.1.2.2 p.2) ^ 2 := by
    have h : Measurable fun p : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ =>
        (2 * (affinePacketProfile ω (p.2 - p.1.2.1) - affinePacketProfile ω (p.2 - p.1.1.1))
          - 2 * (affinePacketProfile ω (p.2 - p.1.2.2)
            - affinePacketProfile ω (p.2 - p.1.1.2))) ^ 2 :=
      (((h1.sub h2).const_mul 2).sub ((h3.sub h4).const_mul 2)).pow_const 2
    exact h.stronglyMeasurable
  exact (hjoint.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable

/-- **The energy of a packet edge field is four times the two-point distance.** -/
theorem integral_packetEdgeField_sq (ω h h' : ℝ) :
    (∫ t in Ioi (0 : ℝ), packetEdgeField ω h h' t ^ 2) = 4 * packetPathDistanceSq ω h' h := by
  rw [packetPathDistanceSq, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [packetEdgeField]
  ring_nf

end

end RHTower
