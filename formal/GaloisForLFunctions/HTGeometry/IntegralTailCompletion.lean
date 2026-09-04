import GaloisForLFunctions.HTGeometry.BurnolDepthCompletion

/-!
# Integral tail completion

If a norm-summable sequence retains dense real span after every finite deletion,
its integer span is dense too. Approximate on a late tail and round coefficients;
the total rounding error is bounded by the norm tail, independently of coefficient size.

Every real Burnol depth tail is complete. Consequently any nonzero summable
amplitude weighting still has dense integer span. This concerns unrestricted
integer combinations in the ordinary output topology, not multiplicative Euler
formation, bounded coefficient height, or actual theta/Xi admission.
-/

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace HTGeometry
noncomputable section

/-- Summable generators with dense real span after every finite deletion also have dense
integer span. Coefficient rounding is performed only on a late tail. -/
theorem dense_integer_span_of_summable_tail_dense
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℕ → E) (hs : Summable (fun n => ‖v n‖))
    (hd : ∀ N : ℕ, Dense (Submodule.span ℝ
      (Set.range (fun n => v (n + N))) : Set E)) :
    Dense (Submodule.span ℤ (Set.range v) : Set E) := by
  classical
  intro x
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have ht : Tendsto (fun N => ∑' n, ‖v (n + N)‖) atTop (𝓝 0) :=
    tendsto_sum_nat_add (fun n => ‖v n‖)
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hd N x) (ε / 2) (half_pos hε)
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  let z : E := ∑ n ∈ c.support, (round (c n)) • v (n + N)
  have hz : z ∈ Submodule.span ℤ (Set.range v) := by
    apply Submodule.sum_mem
    intro n hn
    exact Submodule.smul_mem _ (round (c n)) (Submodule.subset_span ⟨n + N, rfl⟩)
  have herr : ‖(c.sum fun n a => a • v (n + N)) - z‖ ≤ ∑' n, ‖v (n + N)‖ := by
    change ‖(∑ n ∈ c.support, c n • v (n + N)) -
      ∑ n ∈ c.support, (round (c n)) • v (n + N)‖ ≤ _
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ c.support, ‖c n • v (n + N) - (round (c n)) • v (n + N)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ c.support, ‖v (n + N)‖ := by
        apply Finset.sum_le_sum
        intro n hn
        rw [← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, norm_smul, Real.norm_eq_abs]
        calc
          _ ≤ (1 / 2 : ℝ) * ‖v (n + N)‖ :=
            mul_le_mul_of_nonneg_right (abs_sub_round _) (norm_nonneg _)
          _ ≤ ‖v (n + N)‖ := by nlinarith [norm_nonneg (v (n + N))]
      _ ≤ ∑' n, ‖v (n + N)‖ :=
        ((summable_nat_add_iff N).mpr hs).sum_le_tsum c.support (fun _ _ => norm_nonneg _)
  refine ⟨z, hz, ?_⟩
  have hyz : dist (c.sum fun n a => a • v (n + N)) z < ε / 2 := by
    rw [dist_eq_norm]
    exact herr.trans_lt hN
  exact (dist_triangle x _ z).trans_lt (by linarith)

abbrev RealBurnolHalfLineL2 := Lp ℝ 2 (volume.restrict (Ioi (0 : ℝ)))

def realBurnolDepthFeature (ell : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  t * Real.exp (-((n + 1 : ℝ) * ell * t))

theorem memLp_realBurnolDepthFeature {ell : ℝ} (hell : 0 < ell) (n : ℕ) :
    MemLp (realBurnolDepthFeature ell n) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  exact (memLp_burnolDepthFeature hell n).re

def realBurnolDepthFeatureL2 (ell : Ioi (0 : ℝ)) (n : ℕ) : RealBurnolHalfLineL2 :=
  (memLp_realBurnolDepthFeature ell.property n).toLp (realBurnolDepthFeature ell n)

theorem realBurnolDepthFeatureL2_ae (ell : Ioi (0 : ℝ)) (n : ℕ) :
    (realBurnolDepthFeatureL2 ell n : ℝ → ℝ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      realBurnolDepthFeature ell n := (memLp_realBurnolDepthFeature ell.property n).coeFn_toLp

theorem realBurnolDepthFeature_add (ell : ℝ) (n N : ℕ) (t : ℝ) :
    realBurnolDepthFeature ell (n + N) t =
      Real.exp (-ell * t) ^ n * realBurnolDepthFeature ell N t := by
  unfold realBurnolDepthFeature
  rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- Every finite deletion of a depth tower remains complete; no finite collection of its
columns carries a continuous coordinate unavailable in the tail. -/
theorem dense_realBurnolDepthTail (ell : Ioi (0 : ℝ)) (N : ℕ) :
    Dense (Submodule.span ℝ (Set.range
      (fun n => realBurnolDepthFeatureL2 ell (n + N))) : Set RealBurnolHalfLineL2) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  refine (Submodule.eq_bot_iff _).mpr fun g hg => ?_
  have hmom (n : ℕ) : ∫ t in Ioi (0 : ℝ),
      Real.exp (-(ell : ℝ) * t) ^ n *
        (realBurnolDepthFeature ell N t * g t) = 0 := by
    have h := (Submodule.mem_orthogonal _ g).mp hg (realBurnolDepthFeatureL2 ell (n + N))
      (Submodule.subset_span ⟨n, rfl⟩)
    rw [L2.inner_def] at h
    calc
      _ = ∫ t in Ioi (0 : ℝ), inner ℝ
          (realBurnolDepthFeatureL2 ell (n + N) t) (g t) := by
        apply integral_congr_ae
        filter_upwards [realBurnolDepthFeatureL2_ae ell (n + N)] with t ht
        rw [ht, Real.inner_apply, realBurnolDepthFeature_add]
        ring
      _ = 0 := h
  have hell : 0 < (ell : ℝ) := ell.property
  have hφ : MeasurableEmbedding (fun t : ℝ => Real.exp (-(ell : ℝ) * t)) := by
    apply (show Continuous (fun t : ℝ => Real.exp (-(ell : ℝ) * t)) by
      fun_prop).measurableEmbedding
    intro x y hxy
    exact mul_left_cancel₀ (neg_ne_zero.mpr (ne_of_gt hell)) (Real.exp_injective hxy)
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      |Real.exp (-(ell : ℝ) * t)| ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hell.le) (show 0 ≤ t from le_of_lt ht))
  have hzero := ae_eq_zero_of_boundedCoordinate_moments hφ hbound
    ((memLp_realBurnolDepthFeature ell.property N).integrable_mul (Lp.memLp g)) hmom
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hzero, ae_restrict_mem measurableSet_Ioi] with t ht htpos
  have hw : realBurnolDepthFeature ell N t ≠ 0 :=
    mul_ne_zero (ne_of_gt htpos) (Real.exp_ne_zero _)
  exact (mul_eq_zero.mp ht).resolve_left hw

theorem norm_realBurnolDepthFeatureL2_le (ell : Ioi (0 : ℝ)) (n : ℕ) :
    ‖realBurnolDepthFeatureL2 ell n‖ ≤ ‖realBurnolDepthFeatureL2 ell 0‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [realBurnolDepthFeatureL2_ae ell n, realBurnolDepthFeatureL2_ae ell 0,
    ae_restrict_mem measurableSet_Ioi] with t hn h0 ht
  rw [hn, h0]
  have hpos : 0 < t := ht
  simp only [realBurnolDepthFeature, Nat.cast_zero, zero_add, one_mul, Real.norm_eq_abs,
    abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hpos]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hpos.le
  have hell : 0 < (ell : ℝ) := ell.property
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (mul_nonneg hell.le hpos.le)]

theorem dense_weighted_realBurnolDepthTail (ell : Ioi (0 : ℝ))
    (b : ℕ → ℝ) (hb : ∀ n, b n ≠ 0) (N : ℕ) :
    Dense (Submodule.span ℝ (Set.range
      (fun n => b (n + N) • realBurnolDepthFeatureL2 ell (n + N))) : Set RealBurnolHalfLineL2) := by
  have heq : Submodule.span ℝ (Set.range
      (fun n => b (n + N) • realBurnolDepthFeatureL2 ell (n + N))) =
      Submodule.span ℝ (Set.range (fun n => realBurnolDepthFeatureL2 ell (n + N))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      change realBurnolDepthFeatureL2 ell (n + N) ∈ Submodule.span ℝ (Set.range
        (fun n => b (n + N) • realBurnolDepthFeatureL2 ell (n + N)))
      have h := (Submodule.span ℝ (Set.range
        (fun n => b (n + N) • realBurnolDepthFeatureL2 ell (n + N)))).smul_mem
          (b (n + N))⁻¹ (Submodule.subset_span ⟨n, rfl⟩)
      simpa only [smul_smul, inv_mul_cancel₀ (hb _), one_smul] using h
  rw [heq]
  exact dense_realBurnolDepthTail ell N

/-- Summably weighted literal depth columns lose coefficient integrality in their ordinary
output completion. This is a completion theorem, not an arithmetic admission theorem. -/
theorem dense_integer_weighted_realBurnolDepthSpan (ell : Ioi (0 : ℝ))
    (b : ℕ → ℝ) (hb : ∀ n, b n ≠ 0) (hs : Summable (fun n => |b n|)) :
    Dense (Submodule.span ℤ (Set.range
      (fun n => b n • realBurnolDepthFeatureL2 ell n)) : Set RealBurnolHalfLineL2) := by
  apply dense_integer_span_of_summable_tail_dense
  · apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
      (hs.mul_right ‖realBurnolDepthFeatureL2 ell 0‖)
    intro n
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_realBurnolDepthFeatureL2_le ell n) (abs_nonneg _)
  · exact dense_weighted_realBurnolDepthTail ell b hb

end
end HTGeometry

