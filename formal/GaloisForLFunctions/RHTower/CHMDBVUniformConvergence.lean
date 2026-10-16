import GaloisForLFunctions.RHTower.CHMDBVUniformGraph
import GaloisForLFunctions.HTGeometry.BoundedVariationNormAlgebra

/-! # Uniform convergence with bounded variation reaches the full jump graph -/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower.CHMDDoobGraph
open GaloisForLFunctions.HTGeometry

theorem bvLift_sub (v w : ℝ → ℝ) (hv : BoundedVariationOn v univ)
    (hw : BoundedVariationOn w univ) :
    bvLift (fun x => v x - w x) (boundedVariationOn_sub hv hw) =
      bvLift v hv - bvLift w hw := by
  apply source_projection_injective
  exact (bv_memLp_mass hv).toLp_sub (bv_memLp_mass hw)

theorem tendsto_bvLift_zero_of_uniform {ι : Type*} {l : Filter ι}
    {v : ι → ℝ → ℝ} (hv : ∀ i, BoundedVariationOn (v i) univ)
    (hc : ∀ i, HasCompactSupport (v i)) {V : ℝ}
    (hV : ∀ i, (eVariationOn (v i) univ).toReal ≤ V)
    (hu : TendstoUniformly v (fun _ => 0) l) :
    Tendsto (fun i => bvLift (v i) (hv i)) l (𝓝 0) := by
  obtain ⟨C, hC, hθ, _⟩ := theta_global_and_exponential_bound
  let A := massMeasure.real univ + 4 * (Measure.sum primeMeasure).real univ
  let D := 4 * C ^ 2 * ∫ t in Ioi (0 : ℝ), t * archLevyDensity t
  have hD : 0 ≤ D := by
    apply mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C))
    exact setIntegral_nonneg measurableSet_Ioi
      (fun t ht => mul_nonneg ht.le (archLevyDensity_pos ht).le)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hcont : Continuous (fun r : ℝ => A * r ^ 2 + D * r * V) := by fun_prop
  have hlim : Tendsto (fun r : ℝ => A * r ^ 2 + D * r * V) (𝓝 0) (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, add_zero]
      using hcont.tendsto 0
  have hp : ∀ᶠ r : ℝ in 𝓝 0, A * r ^ 2 + D * r * V < ε ^ 2 :=
    hlim.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  obtain ⟨r, hr, hpr⟩ := Metric.mem_nhds_iff.mp hp
  have hhalf : r / 2 ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith
  have hsmall := hpr hhalf
  filter_upwards [(Metric.tendstoUniformly_iff.mp hu) (r / 2) (half_pos hr)] with i hi
  have hb : ∀ x, |v i x| ≤ r / 2 := fun x => by
    simpa only [dist_zero_left, Real.norm_eq_abs] using (hi x).le
  have hn := bvLift_norm_sq_le_of_bound (hv i) (hc i) (half_pos hr).le hb hC hθ
  change ‖bvLift (v i) (hv i)‖ ^ 2 ≤
    A * (r / 2) ^ 2 + D * (r / 2) * (eVariationOn (v i) univ).toReal at hn
  have hvar := mul_le_mul_of_nonneg_left (hV i) (mul_nonneg hD (half_pos hr).le)
  have hsq : ‖bvLift (v i) (hv i)‖ ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt (hn.trans (add_le_add le_rfl hvar)) hsmall
  simpa only [dist_zero_right] using (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq

theorem tendsto_bvLift_of_uniform {ι : Type*} {l : Filter ι}
    {v : ι → ℝ → ℝ} {w : ℝ → ℝ}
    (hv : ∀ i, BoundedVariationOn (v i) univ) (hw : BoundedVariationOn w univ)
    (hc : ∀ i, HasCompactSupport (v i)) (hwc : HasCompactSupport w) {V : ℝ}
    (hV : ∀ i, (eVariationOn (v i) univ).toReal ≤ V)
    (hu : TendstoUniformly v w l) :
    Tendsto (fun i => bvLift (v i) (hv i)) l (𝓝 (bvLift w hw)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  have hvar (i : ι) : (eVariationOn (fun x => v i x - w x) univ).toReal ≤
      |V| + (eVariationOn w univ).toReal := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (eVariationOn_sub_le_of_finite (hv i) hw)
    rw [ENNReal.toReal_ofReal (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)] at h
    exact h.trans (add_le_add ((hV i).trans (le_abs_self V)) le_rfl)
  have hzero : TendstoUniformly (fun i x => v i x - w x) (fun _ => 0) l := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp hu) ε hε] with i hi
    intro x
    simpa only [dist_zero_left, Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using hi x
  have h := tendsto_bvLift_zero_of_uniform
    (fun i => boundedVariationOn_sub (hv i) hw) (fun i => (hc i).sub hwc) hvar hzero
  have he : (fun i => bvLift (fun x => v i x - w x) (boundedVariationOn_sub (hv i) hw)) =
      (fun i => bvLift (v i) (hv i) - bvLift w hw) :=
    funext fun i => bvLift_sub (v i) w (hv i) hw
  rw [he] at h
  exact h

theorem continuous_bvLift_of_common_compact {v : ℝ → ℝ → ℝ}
    (hv : ∀ t, BoundedVariationOn (v t) univ)
    (hc : ∀ t, HasCompactSupport (v t))
    (hjoint : Continuous (fun p : ℝ × ℝ => v p.1 p.2))
    {K : Set ℝ} (hK : IsCompact K) (hz : ∀ t x, x ∉ K → v t x = 0)
    {V : ℝ} (hV : ∀ t, (eVariationOn (v t) univ).toReal ≤ V) :
    Continuous (fun t => bvLift (v t) (hv t)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply continuous_iff_continuousAt.mpr
  intro t
  have hrestricted : Continuous (fun p : ℝ × K => v p.1 p.2) :=
    hjoint.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have huK := Continuous.tendstoUniformly (fun a (x : K) => v a x) hrestricted t
  have hu : TendstoUniformly v (v t) (𝓝 t) := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp huK) ε hε] with a ha
    intro x
    by_cases hx : x ∈ K
    · exact ha ⟨x, hx⟩
    · simpa only [hz t x hx, hz a x hx, dist_self] using hε
  exact tendsto_bvLift_of_uniform hv (hv t) hc (hc t) hV hu

end RHTower.CHMDDoobGraph
