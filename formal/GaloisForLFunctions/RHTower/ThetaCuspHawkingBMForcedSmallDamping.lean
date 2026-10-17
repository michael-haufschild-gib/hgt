import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPrincipalSmallDamping
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalCausalGreenBand

/-! Every positive damping admits the unchanged forced physical response in L2.
The construction retains the literal cusp source and all principal commutators. -/

open MeasureTheory Set Filter Topology
namespace RHTower.D4BMForcedSmallDamping
open D4BMJointSource D4BMJointWave D4BMNativeCircle D4BMNativeLaplace
open D4BMPrincipalSmallDamping GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem source_integrable (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t => expRay (c:ℂ) t • causalCuspSourceVector q branch amp t) (Ioi 0) := by
  simpa only [expRay,neg_mul] using
    causalCuspSourceVector_laplace_integrable_pos q branch amp c hc

/-- Holomorphy of the actual causal source response holds throughout the positive half-plane. -/
theorem causalJointFrequencyResponse_differentiableAt_pos (q : XiZeroCopy) (branch : Bool)
    (amp w : ℂ) (hw : 0 < w.re) :
    DifferentiableAt ℂ (causalJointFrequencyResponse q branch amp) w := by
  have hS : DifferentiableAt ℂ (causalCuspLaplace q branch amp) w :=
    bochnerLaplaceRay_differentiableAt (causalCuspSourceVector_continuous q branch amp).aestronglyMeasurable
      (source_integrable q branch amp (w.re/2) (by linarith)) w (by linarith)
  change DifferentiableAt ℂ (fun z => jointEmbedding
    (waveEnergyInverse jointEmbedding z (jointEmbedding.adjoint (causalCuspLaplace q branch amp z)))) w
  exact jointEmbedding.differentiableAt.comp w
    ((waveEnergyInverse_differentiableAt jointEmbedding jointEmbedding_norm_le w hw).clm_apply
      (jointEmbedding.adjoint.differentiableAt.comp w hS))

private def sourceSize (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (c : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ), ‖expRay (c:ℂ) t • causalCuspSourceVector q branch amp t‖

private theorem sourceSize_nonneg (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (c : ℝ) :
    0 ≤ sourceSize q branch amp c := integral_nonneg (fun _ => norm_nonneg _)

private def admittedBoundary (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (c : ℝ) (hc : 0 < c) : CauchyBoundedHilbertMap SpatialSpace where
  value := fun w => causalJointFrequencyResponse q branch amp (w+c)
  shift := c
  shift_pos := hc
  bound := sourceSize q branch amp c/c
  holo := by
    intro w hw
    apply (causalJointFrequencyResponse_differentiableAt_pos q branch amp (w+c) ?_).comp w
      (differentiableAt_id.add_const _)
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith
  norm_le := by
    intro w hw
    have hwr : 0 < (w+(c:ℂ)).re := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
    have hne : w+(c:ℂ) ≠ 0 := by
      intro he
      have h := congrArg Complex.re he
      simp only [Complex.zero_re] at h
      linarith
    have hnorm : 0 < ‖w+(c:ℂ)‖ := norm_pos_iff.mpr hne
    have hsize := bochnerLaplaceRay_norm_le (source_integrable q branch amp c hc) (w+c)
      (show c ≤ (w+(c:ℂ)).re by simp only [Complex.add_re,Complex.ofReal_re]; linarith)
    have hmass : 0 ≤ sourceSize q branch amp c := sourceSize_nonneg q branch amp c
    calc
      ‖causalJointFrequencyResponse q branch amp (w+c)‖ ≤
          ‖causalCuspLaplace q branch amp (w+c)‖/((w+(c:ℂ)).re*‖w+(c:ℂ)‖) :=
        waveSpatialResolvent_bound jointEmbedding jointEmbedding_norm_le (w+c) hwr _
      _ ≤ sourceSize q branch amp c/((w+(c:ℂ)).re*‖w+(c:ℂ)‖) :=
        div_le_div_of_nonneg_right hsize (mul_nonneg hwr.le hnorm.le)
      _ = (sourceSize q branch amp c/(w+(c:ℂ)).re)*‖(w+(c:ℂ))⁻¹‖ := by
        rw [norm_inv]
        field_simp
      _ ≤ (sourceSize q branch amp c/c)*‖(w+(c:ℂ))⁻¹‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply div_le_div_of_nonneg_left hmass hc
        simp only [Complex.add_re,Complex.ofReal_re]
        linarith

private def admittedResponse (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (c : ℝ) (hc : 0 < c) (t : ℝ) : SpatialSpace :=
  expRay (-(c:ℂ)) t • (admittedBoundary q branch amp c hc).causalDatum t

private theorem admitted_integrand (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (c : ℝ) (hc : 0 < c) (w : ℂ) (t : ℝ) :
    expRay w t • admittedResponse q branch amp c hc t =
      expRay (w-c) t • (admittedBoundary q branch amp c hc).causalDatum t := by
  simp only [admittedResponse,smul_smul,expRay,← Complex.exp_add]
  congr 2
  ring

private theorem admitted_weighted_memLp (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (c : ℝ) (hc : 0 < c) (k : ℝ) (hk : c < k) :
    MemLp (fun t => expRay (k:ℂ) t • admittedResponse q branch amp c hc t)
      2 (volume.restrict (Ioi (0:ℝ))) := by
  have h := (admittedBoundary q branch amp c hc).causalDatum_memLp_pos (k-c) (sub_pos.mpr hk)
  apply h.ae_eq
  filter_upwards [] with t
  simp only [admitted_integrand,Complex.ofReal_sub]

private theorem admitted_integrable (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (c : ℝ) (hc : 0 < c) (w : ℂ) (hw : c < w.re) :
    IntegrableOn (fun t => expRay w t • admittedResponse q branch amp c hc t) (Ioi 0) := by
  have hp : 0 < (w-(c:ℂ)).re := by simp only [Complex.sub_re,Complex.ofReal_re]; linarith
  apply ((admittedBoundary q branch amp c hc).causalDatum_integrable_rightHalfPlane (w-c) hp).congr
  filter_upwards [] with t
  exact (admitted_integrand q branch amp c hc w t).symm

private theorem admitted_laplace (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (c : ℝ) (hc : 0 < c) (w : ℂ) (hw : c < w.re) :
    (∫ t in Ioi (0:ℝ), expRay w t • admittedResponse q branch amp c hc t) =
      causalJointFrequencyResponse q branch amp w := by
  simp_rw [admitted_integrand]
  have hp : 0 < (w-(c:ℂ)).re := by simp only [Complex.sub_re,Complex.ofReal_re]; linarith
  have h := (admittedBoundary q branch amp c hc).causalDatum_laplace_rightHalfPlane (w-c) hp
  change _ = causalJointFrequencyResponse q branch amp ((w-c)+c) at h
  simpa only [sub_add_cancel] using h

private theorem weighted_probe_transform {U : ℝ → SpatialSpace} (L : SpatialSpace →L[ℂ] ℂ)
    (k : ℝ) (w : ℂ) (hi : IntegrableOn (fun t => expRay (w+k) t • U t) (Ioi 0)) :
    laplaceRay (fun t => L (expRay (k:ℂ) t • U t)) w =
      L (∫ t in Ioi (0:ℝ), expRay (w+k) t • U t) := by
  calc
    _ = ∫ t in Ioi (0:ℝ), L (expRay (w+k) t • U t) := by
      unfold laplaceRay
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [map_smul,smul_eq_mul]
      have he : expRay (k:ℂ) t*expRay w t = expRay (w+k) t := by
        simp only [expRay,← Complex.exp_add]
        congr 1
        ring
      calc
        _ = (expRay (k:ℂ) t*expRay w t)*L (U t) := by ring
        _ = _ := by rw [he]
    _ = _ := L.integral_comp_comm hi

/-- Laplace uniqueness identifies the auxiliary shifted construction with the already
defined physical response; the small-damping theorem does not replace the target. -/
private theorem admitted_eq_original (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (c : ℝ) (hc : 0 < c) :
    admittedResponse q branch amp c hc =ᵐ[volume.restrict (Ioi (0:ℝ))]
      causalJointForcedResponse q branch amp := by
  let k := max (principalKernelGrowth q) c+1
  have hkc : c < k := by dsimp [k]; linarith [le_max_right (principalKernelGrowth q) c]
  have hkg : principalKernelGrowth q < k := by
    dsimp [k]; linarith [le_max_left (principalKernelGrowth q) c]
  let A := fun t => expRay (k:ℂ) t • admittedResponse q branch amp c hc t
  let B := fun t => expRay (k:ℂ) t • causalJointForcedResponse q branch amp t
  have hA : MemLp A 2 (volume.restrict (Ioi (0:ℝ))) := admitted_weighted_memLp q branch amp c hc k hkc
  have hB : MemLp B 2 (volume.restrict (Ioi (0:ℝ))) :=
    causalJointForcedResponse_memLp_of_native q branch amp k hkg
  have hp (v : SpatialSpace) : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), inner ℂ v (A t-B t)=0 := by
    let L : SpatialSpace →L[ℂ] ℂ := innerSL ℂ v
    have hLA := L.comp_memLp' hA
    have hLB := L.comp_memLp' hB
    have hz := ae_eq_zero_of_laplaceRay_eq_zero (hLA.sub hLB) (fun w hw => by
      have hwc : c < (w+(k:ℂ)).re := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
      have hwg : principalKernelGrowth q < (w+(k:ℂ)).re := by
        simp only [Complex.add_re,Complex.ofReal_re]; linarith
      change (∫ t in Ioi (0:ℝ), (L (A t)-L (B t))*expRay w t) = 0
      simp_rw [sub_mul]
      have hsub := integral_sub (integrableOn_laplaceRay hLA hw) (integrableOn_laplaceRay hLB hw)
      simp only [Function.comp_def] at hsub
      rw [hsub]
      change laplaceRay (fun t => L (expRay (k:ℂ) t • admittedResponse q branch amp c hc t)) w-
        laplaceRay (fun t => L (expRay (k:ℂ) t • causalJointForcedResponse q branch amp t)) w=0
      rw [weighted_probe_transform L k w (admitted_integrable q branch amp c hc (w+k) hwc),
        weighted_probe_transform L k w (causalJointForcedResponse_integrable_of_native q branch amp (w+k) hwg),
        admitted_laplace q branch amp c hc (w+k) hwc,
        causalJointForcedResponse_laplace_of_native q branch amp (w+k) hwg,sub_self])
    filter_upwards [hz] with t ht
    change inner ℂ v (A t)-inner ℂ v (B t)=0 at ht
    simpa only [inner_sub_right] using ht
  have hz := bochnerL2_ae_zero_on_of_inner_probes (fun t => A t-B t) (hA.sub hB)
    Set.univ MeasurableSet.univ (fun v => (hp v).mono (fun _ h _ => h))
  filter_upwards [hz] with t ht
  have he : A t=B t := sub_eq_zero.mp (ht (Set.mem_univ t))
  have hcancel := congrArg (fun v : SpatialSpace => (expRay (k:ℂ) t)⁻¹ • v) he
  have hne : expRay (k:ℂ) t ≠ 0 := Complex.exp_ne_zero _
  simpa only [A,B,smul_smul,inv_mul_cancel₀ hne,one_smul] using hcancel

/-- Every strictly positive damping admits the original forced response in the original
time L2 space. The source-dependent lower damping threshold is removed unconditionally. -/
theorem causalJointForcedResponse_memLp_pos (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (k : ℝ) (hk : 0 < k) :
    MemLp (fun t => expRay (k:ℂ) t • causalJointForcedResponse q branch amp t)
      2 (volume.restrict (Ioi (0:ℝ))) := by
  have hc : 0 < k/2 := by linarith
  apply (admitted_weighted_memLp q branch amp (k/2) hc k (by linarith)).ae_eq
  exact (admitted_eq_original q branch amp (k/2) hc).mono (fun t ht => congrArg (fun v => expRay (k:ℂ) t • v) ht)

/-- The unchanged physical response has an absolute Bochner Laplace integral at every
frequency in the positive half-plane. -/
theorem causalJointForcedResponse_integrable_pos (q : XiZeroCopy) (branch : Bool) (amp w : ℂ)
    (hw : 0 < w.re) :
    IntegrableOn (fun t => expRay w t • causalJointForcedResponse q branch amp t) (Ioi 0) := by
  have hc : 0 < w.re/2 := by linarith
  apply (admitted_integrable q branch amp (w.re/2) hc w (by linarith)).congr
  exact (admitted_eq_original q branch amp (w.re/2) hc).mono (fun t ht => congrArg (fun v => expRay w t • v) ht)

/-- The newly admitted integral recovers the literal original causal frequency response;
all three principal channels and the native square remainder remain present. -/
theorem causalJointForcedResponse_laplace_pos (q : XiZeroCopy) (branch : Bool) (amp w : ℂ)
    (hw : 0 < w.re) :
    (∫ t in Ioi (0:ℝ), expRay w t • causalJointForcedResponse q branch amp t) =
      causalJointFrequencyResponse q branch amp w := by
  have hc : 0 < w.re/2 := by linarith
  calc
    _ = ∫ t in Ioi (0:ℝ), expRay w t • admittedResponse q branch amp (w.re/2) hc t :=
      integral_congr_ae ((admitted_eq_original q branch amp (w.re/2) hc).symm.mono
        (fun t ht => congrArg (fun v => expRay w t • v) ht))
    _ = _ := admitted_laplace q branch amp (w.re/2) hc w (by linarith)

end
end RHTower.D4BMForcedSmallDamping
