import GaloisForLFunctions.HTGeometry.HorizontalLayerBlaschke
import GaloisForLFunctions.HTGeometry.ProjectiveCauchyDensityControl

open Complex Filter Topology
open scoped OnePoint

noncomputable section

namespace GaloisForLFunctions.HTGeometry

abbrev ProjectiveBoundary := C(OnePoint ℝ, ℂ)

/-- Totalized projective resolvent. At nonreal poles this is the literal Cauchy resolvent;
at real poles it is set to zero. Horizontal-layer arguments only use nonreal poles. -/
def projectiveNonrealResolvent (z : ℂ) : ProjectiveBoundary :=
  if hz : z.im ≠ 0 then
    ⟨projectiveCauchyPower z 0, continuous_projectiveCauchyPower z hz 0⟩
  else 0

@[simp]
theorem projectiveNonrealResolvent_infty (z : ℂ) :
    projectiveNonrealResolvent z ∞ = 0 := by
  unfold projectiveNonrealResolvent
  split <;> simp

theorem projectiveNonrealResolvent_coe {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    projectiveNonrealResolvent z (x : OnePoint ℝ) = ((x : ℂ) - z)⁻¹ := by
  simp [projectiveNonrealResolvent, hz]

/-- Projectively completed boundary symbol of one horizontal Blaschke layer. -/
def horizontalLayerProjective (a ω : ℝ) : ProjectiveBoundary :=
  let upper := (2 * I * ((a + ω : ℝ) : ℂ)) •
    projectiveNonrealResolvent (-((a + ω : ℝ) : ℂ) * I)
  let lower := (2 * I * ((a - ω : ℝ) : ℂ)) •
    projectiveNonrealResolvent (((a - ω : ℝ) : ℂ) * I)
  (1 - upper) * (1 + lower)

/-- Projectively completed derivative symbol of one horizontal Blaschke layer. -/
def horizontalLayerInfinitesimalProjective (a : ℝ) : ProjectiveBoundary :=
  (-2 * I) • projectiveNonrealResolvent ((a : ℂ) * I) +
    (-2 * I) • projectiveNonrealResolvent (-(a : ℂ) * I)

@[simp]
theorem horizontalLayerProjective_infty (a ω : ℝ) :
    horizontalLayerProjective a ω ∞ = 1 := by
  simp [horizontalLayerProjective]

@[simp]
theorem horizontalLayerInfinitesimalProjective_infty (a : ℝ) :
    horizontalLayerInfinitesimalProjective a ∞ = 0 := by
  simp [horizontalLayerInfinitesimalProjective]

theorem horizontalLayerProjective_coe {a ω : ℝ}
    (hplus : a + ω ≠ 0) (hminus : a - ω ≠ 0) (x : ℝ) :
    horizontalLayerProjective a ω (x : OnePoint ℝ) =
      horizontalLayerFactorRaw a ω x := by
  have hzplus : (-((a + ω : ℝ) : ℂ) * I).im ≠ 0 := by
    simpa [add_comm] using (neg_ne_zero.mpr hplus)
  have hzminus : (((a - ω : ℝ) : ℂ) * I).im ≠ 0 := by
    simp [hminus]
  rw [horizontalLayerProjective]
  simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
    ContinuousMap.one_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [projectiveNonrealResolvent_coe hzplus,
    projectiveNonrealResolvent_coe hzminus]
  have hdenplus :
      (x : ℂ) - (-((a + ω : ℝ) : ℂ) * I) =
        (x : ℂ) + ((a + ω : ℝ) : ℂ) * I := by ring
  rw [hdenplus]
  have hp := real_add_mul_I_ne_zero (x := x) hplus
  have hm := real_sub_mul_I_ne_zero (x := x) hminus
  have hfirst :
      1 - (2 * I * ((a + ω : ℝ) : ℂ)) *
          (((x : ℂ) + ((a + ω : ℝ) : ℂ) * I)⁻¹) =
        ((x : ℂ) - ((a + ω : ℝ) : ℂ) * I) /
          ((x : ℂ) + ((a + ω : ℝ) : ℂ) * I) := by
    apply (eq_div_iff hp).2
    rw [sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ hp, mul_one]
    ring
  have hsecond :
      1 + (2 * I * ((a - ω : ℝ) : ℂ)) *
          (((x : ℂ) - ((a - ω : ℝ) : ℂ) * I)⁻¹) =
        ((x : ℂ) + ((a - ω : ℝ) : ℂ) * I) /
          ((x : ℂ) - ((a - ω : ℝ) : ℂ) * I) := by
    apply (eq_div_iff hm).2
    rw [add_mul, one_mul, mul_assoc, inv_mul_cancel₀ hm, mul_one]
    ring
  rw [hfirst, hsecond]
  rfl

theorem horizontalLayerInfinitesimalProjective_coe {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    horizontalLayerInfinitesimalProjective a (x : OnePoint ℝ) =
      horizontalLayerFullInfinitesimalSymbol a x := by
  have hzplus : (((a : ℝ) : ℂ) * I).im ≠ 0 := by simp [ha]
  have hzminus : (-(a : ℂ) * I).im ≠ 0 := by simp [ha]
  rw [horizontalLayerInfinitesimalProjective]
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [projectiveNonrealResolvent_coe hzplus,
    projectiveNonrealResolvent_coe hzminus]
  unfold horizontalLayerFullInfinitesimalSymbol
  ring

/-- Normalized projective one-layer slope. -/
def horizontalLayerNormalizedProjective (a ω : ℝ) : ProjectiveBoundary :=
  ((ω : ℂ)⁻¹) • (horizontalLayerProjective a ω - 1)

theorem horizontalLayerNormalizedProjective_coe {a ω : ℝ}
    (hplus : a + ω ≠ 0) (hminus : a - ω ≠ 0) (x : ℝ) :
    horizontalLayerNormalizedProjective a ω (x : OnePoint ℝ) =
      (horizontalLayerFactorRaw a ω x - 1) / (ω : ℂ) := by
  rw [horizontalLayerNormalizedProjective]
  simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
    smul_eq_mul, horizontalLayerProjective_coe hplus hminus]
  rw [div_eq_inv_mul]

theorem norm_horizontalLayerNormalizedProjective_sub_le {a ω : ℝ} (ha : 0 < a)
    (hω : ω ≠ 0) (hsmall : |ω| ≤ a / 2) :
    ‖horizontalLayerNormalizedProjective a ω -
        horizontalLayerInfinitesimalProjective a‖ ≤ 48 * |ω| / a ^ 2 := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  cases t with
  | infty =>
      simp [horizontalLayerNormalizedProjective]
      positivity
  | coe x =>
      have hωbounds := abs_le.mp hsmall
      have hplus : 0 < a + ω := by linarith
      have hminus : 0 < a - ω := by linarith
      simp only [ContinuousMap.sub_apply]
      rw [horizontalLayerNormalizedProjective_coe hplus.ne' hminus.ne',
        horizontalLayerInfinitesimalProjective_coe ha.ne']
      exact norm_horizontalLayerFactorRaw_normalized_sub_le ha hω hsmall x

theorem tendsto_horizontalLayerNormalizedProjective (a : ℝ) (ha : 0 < a) :
    Tendsto (horizontalLayerNormalizedProjective a) (𝓝[≠] 0)
      (𝓝 (horizontalLayerInfinitesimalProjective a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hid : Tendsto (fun ω : ℝ => ω) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have habs : Tendsto (fun ω : ℝ => |ω|) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hid.abs
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · have hsmall : ∀ᶠ ω : ℝ in 𝓝[≠] 0, |ω| ≤ a / 2 := by
      have hmetric := (Metric.tendsto_nhds.mp habs) (a / 2) (by linarith)
      filter_upwards [hmetric] with ω hω
      simpa only [Real.dist_eq, sub_zero, abs_abs] using le_of_lt hω
    filter_upwards [self_mem_nhdsWithin, hsmall] with ω hω hωsmall
    apply norm_horizontalLayerNormalizedProjective_sub_le ha
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hω
    · exact hωsmall
  · simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      habs.const_mul (48 * (a ^ 2)⁻¹)

theorem tendsto_horizontalLayerProjective (a : ℝ) (ha : 0 < a) :
    Tendsto (horizontalLayerProjective a) (𝓝[≠] 0) (𝓝 1) := by
  have hid : Tendsto (fun ω : ℝ => ω) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hscalar : Tendsto (fun ω : ℝ => (ω : ℂ)) (𝓝[≠] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp hid
  have hnormalized := tendsto_horizontalLayerNormalizedProjective a ha
  have hone : Tendsto (fun _ : ℝ => (1 : ProjectiveBoundary)) (𝓝[≠] 0) (𝓝 1) :=
    tendsto_const_nhds
  have hsum := hone.add (hscalar.smul hnormalized)
  simp only [zero_smul, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with ω hω
  have hω' : ω ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hω
  ext t
  simp [horizontalLayerNormalizedProjective, hω']

lemma projectiveNormalizedMul_eq (F G : ProjectiveBoundary) {ω : ℝ} (hω : ω ≠ 0) :
    ((ω : ℂ)⁻¹) • (F * G - 1) =
      F * (((ω : ℂ)⁻¹) • (G - 1)) + ((ω : ℂ)⁻¹) • (F - 1) := by
  ext t
  simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    ContinuousMap.add_apply, ContinuousMap.one_apply, smul_eq_mul]
  field_simp [ofReal_ne_zero.mpr hω]
  ring

def finiteHorizontalLayerProjective {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ω : ℝ) :
    ProjectiveBoundary :=
  s.prod fun i => horizontalLayerProjective (a i) ω

def finiteHorizontalLayerInfinitesimalProjective {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ProjectiveBoundary :=
  s.sum fun i => horizontalLayerInfinitesimalProjective (a i)

def finiteHorizontalLayerNormalizedProjective {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (ω : ℝ) : ProjectiveBoundary :=
  ((ω : ℂ)⁻¹) • (finiteHorizontalLayerProjective s a ω - 1)

theorem tendsto_finiteHorizontalLayerProjective {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) :
    Tendsto (finiteHorizontalLayerProjective s a) (𝓝[≠] 0) (𝓝 1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change Tendsto (fun _ : ℝ => (1 : ProjectiveBoundary)) (𝓝[≠] 0) (𝓝 1)
      exact tendsto_const_nhds
  | @insert i s hi ih =>
      rw [show finiteHorizontalLayerProjective (insert i s) a =
          fun ω => horizontalLayerProjective (a i) ω *
            finiteHorizontalLayerProjective s a ω by
        funext ω
        simp [finiteHorizontalLayerProjective, hi]]
      simpa using (tendsto_horizontalLayerProjective (a i)
        (ha i (Finset.mem_insert_self i s))).mul
          (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

theorem tendsto_finiteHorizontalLayerNormalizedProjective {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) :
    Tendsto (finiteHorizontalLayerNormalizedProjective s a) (𝓝[≠] 0)
      (𝓝 (finiteHorizontalLayerInfinitesimalProjective s a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change Tendsto
        (fun ω : ℝ => ((ω : ℂ)⁻¹) • ((1 : ProjectiveBoundary) - 1))
        (𝓝[≠] 0) (𝓝 0)
      simpa only [sub_self, smul_zero] using (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (0 : ProjectiveBoundary)) (𝓝[≠] 0) (𝓝 0))
  | @insert i s hi ih =>
      have hi0 := tendsto_horizontalLayerProjective (a i)
        (ha i (Finset.mem_insert_self i s))
      have hi1 := tendsto_horizontalLayerNormalizedProjective (a i)
        (ha i (Finset.mem_insert_self i s))
      have hs0 := tendsto_finiteHorizontalLayerProjective s a
        (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hs1 := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hlim := hi0.mul hs1 |>.add hi1
      have heq :
          (fun ω => horizontalLayerProjective (a i) ω *
              finiteHorizontalLayerNormalizedProjective s a ω +
            horizontalLayerNormalizedProjective (a i) ω) =ᶠ[𝓝[≠] 0]
            finiteHorizontalLayerNormalizedProjective (insert i s) a := by
        filter_upwards [self_mem_nhdsWithin] with ω hω
        have hω' : ω ≠ 0 := by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hω
        simpa [finiteHorizontalLayerNormalizedProjective,
          finiteHorizontalLayerProjective, horizontalLayerNormalizedProjective, hi] using
          (projectiveNormalizedMul_eq (horizontalLayerProjective (a i) ω)
            (finiteHorizontalLayerProjective s a ω) hω').symm
      simpa [finiteHorizontalLayerInfinitesimalProjective, hi, add_comm] using
        hlim.congr' heq

end GaloisForLFunctions.HTGeometry
