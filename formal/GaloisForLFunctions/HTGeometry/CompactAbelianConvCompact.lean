import GaloisForLFunctions.HTGeometry.CompactAbelianConvOperator

/-!
# The convolution operator is compact

A continuous kernel is uniformly continuous on a compact group, so replacing `k (x - z)` by
`k (x - y i)` on a set `A i` of a fine enough finite measurable partition changes the convolution by
at most `ε ‖u‖`.  The replacement is a finite-rank operator: it factors through `ℂ^n`.  Hence the
convolution operator is a norm limit of compact operators, so it is compact.

Compactness is the analytic input of the Peter–Weyl argument: it is what makes the eigenspaces of a
self-adjoint convolution operator finite-dimensional.
-/

open MeasureTheory TopologicalSpace

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- **A finite measurable partition subordinate to a cover by translates.** -/
theorem exists_finite_partition_subordinate {V : Set G} (hV : IsOpen V) (h0 : (0 : G) ∈ V) :
    ∃ (n : ℕ) (y : Fin n → G) (A : Fin n → Set G),
      (∀ i, MeasurableSet (A i)) ∧ (∀ i, ∀ z ∈ A i, z - y i ∈ V) ∧
      (∀ x : G, ∃ i, x ∈ A i) ∧ Pairwise (Function.onFun Disjoint A) := by
  classical
  have hopen : ∀ c : G, IsOpen {z : G | z - c ∈ V} :=
    fun c => hV.preimage (continuous_id.sub continuous_const)
  have hcover : (Set.univ : Set G) ⊆ ⋃ c : G, {z : G | z - c ∈ V} := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, by simpa using h0⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  refine ⟨t.card, fun i => (t.equivFin.symm i : G),
    disjointed fun i => {z : G | z - (t.equivFin.symm i : G) ∈ V}, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [disjointed_apply]
    refine MeasurableSet.diff ((hopen _).measurableSet) ?_
    rw [Finset.sup_set_eq_biUnion]
    exact MeasurableSet.biUnion (Finset.Iio i).countable_toSet fun j _ => (hopen _).measurableSet
  · intro i z hz
    exact disjointed_subset _ i hz
  · intro x
    have hx : x ∈ ⋃ c ∈ t, {z : G | z - c ∈ V} := ht (Set.mem_univ x)
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
    have hmem : x ∈ ⋃ i : Fin t.card, {z : G | z - (t.equivFin.symm i : G) ∈ V} := by
      refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨c, hc⟩, ?_⟩
      simpa using hxc
    rw [← iUnion_disjointed] at hmem
    exact Set.mem_iUnion.mp hmem
  · exact disjoint_disjointed _

section Approx

variable (k : G → ℂ) (hk : Continuous k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)

include hk in
/-- The kernel translated to a sample point, as a continuous function. -/
def kernelShift (c : G) : C(G, ℂ) := ⟨fun x => k (x - c), hk.comp (continuous_id.sub continuous_const)⟩

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
include hk in
@[simp] theorem kernelShift_apply (c x : G) : kernelShift k hk c x = k (x - c) := rfl

variable {n : ℕ} (A : Fin n → Set G)

omit [T2Space G] in
theorem integrable_indicator_lp (hA : ∀ i, MeasurableSet (A i)) (i : Fin n)
    (u : Lp ℂ 2 (haarProb G)) :
    Integrable ((A i).indicator fun z => u z) (haarProb G) :=
  (integrable_lp u).indicator (hA i)

/-- The finite-dimensional sampling map: the integrals of `u` over the pieces of the partition. -/
def sampleLM (hA : ∀ i, MeasurableSet (A i)) :
    Lp ℂ 2 (haarProb G) →ₗ[ℂ] (Fin n → ℂ) where
  toFun u := fun i => ∫ z, (A i).indicator (fun z => u z) z ∂(haarProb G)
  map_add' u v := by
    funext i
    have hco : (fun z => (u + v) z) =ᵐ[haarProb G] fun z => u z + v z := Lp.coeFn_add u v
    have h1 : ∫ z, (A i).indicator (fun z => (u + v) z) z ∂(haarProb G)
        = ∫ z, ((A i).indicator (fun z => u z) z + (A i).indicator (fun z => v z) z)
            ∂(haarProb G) := by
      refine integral_congr_ae ?_
      filter_upwards [hco] with z hz
      by_cases hzA : z ∈ A i
      · rw [Set.indicator_of_mem hzA, Set.indicator_of_mem hzA, Set.indicator_of_mem hzA]
        exact hz
      · rw [Set.indicator_of_notMem hzA, Set.indicator_of_notMem hzA, Set.indicator_of_notMem hzA]
        simp
    rw [h1, integral_add ((integrable_lp u).indicator (hA i)) ((integrable_lp v).indicator (hA i))]
    rfl
  map_smul' c u := by
    funext i
    have hco : (fun z => (c • u) z) =ᵐ[haarProb G] fun z => c • u z := Lp.coeFn_smul c u
    have h1 : ∫ z, (A i).indicator (fun z => (c • u) z) z ∂(haarProb G)
        = ∫ z, c * (A i).indicator (fun z => u z) z ∂(haarProb G) := by
      refine integral_congr_ae ?_
      filter_upwards [hco] with z hz
      by_cases hzA : z ∈ A i
      · rw [Set.indicator_of_mem hzA, Set.indicator_of_mem hzA, hz]
        simp [smul_eq_mul]
      · rw [Set.indicator_of_notMem hzA, Set.indicator_of_notMem hzA]
        simp
    rw [h1, integral_const_mul]
    rfl

omit [T2Space G] in
theorem norm_sampleLM_le (hA : ∀ i, MeasurableSet (A i)) (u : Lp ℂ 2 (haarProb G)) :
    ‖sampleLM A hA u‖ ≤ ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr fun i => ?_
  have h1 : ‖∫ z, (A i).indicator (fun z => u z) z ∂(haarProb G)‖
      ≤ ∫ z, ‖(A i).indicator (fun z => u z) z‖ ∂(haarProb G) := norm_integral_le_integral_norm _
  have h2 : ∫ z, ‖(A i).indicator (fun z => u z) z‖ ∂(haarProb G)
      ≤ ∫ z, ‖u z‖ ∂(haarProb G) := by
    refine integral_mono ((integrable_lp u).indicator (hA i)).norm (integrable_lp u).norm ?_
    intro z
    by_cases hzA : z ∈ A i
    · simp [Set.indicator_of_mem hzA]
    · simp [Set.indicator_of_notMem hzA]
  exact le_trans h1 (le_trans h2 (integral_norm_le_norm u))

/-- The sampling map as a continuous linear map into a finite-dimensional space. -/
def sampleCLM (hA : ∀ i, MeasurableSet (A i)) :
    Lp ℂ 2 (haarProb G) →L[ℂ] (Fin n → ℂ) :=
  LinearMap.mkContinuous (sampleLM A hA) 1 (by simpa using norm_sampleLM_le A hA)

include hk in
/-- The reconstruction map: rebuild a continuous function from the samples. -/
def rebuildCLM (y : Fin n → G) : (Fin n → ℂ) →L[ℂ] C(G, ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ∑ i, z i • kernelShift k hk (y i)
      map_add' := fun z w => by
        simp only [Pi.add_apply, add_smul]
        exact Finset.sum_add_distrib
      map_smul' := fun c z => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
include hk in
theorem rebuildCLM_apply (y : Fin n → G) (z : Fin n → ℂ) (x : G) :
    rebuildCLM k hk y z x = ∑ i, z i * k (x - y i) := by
  show (∑ i, z i • kernelShift k hk (y i)) x = _
  rw [ContinuousMap.coe_sum, Finset.sum_apply]
  simp [smul_eq_mul]

omit [T2Space G] in
/-- The integral splits over the pieces of a finite measurable partition. -/
theorem integral_eq_sum_indicator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hA : ∀ i, MeasurableSet (A i)) (hcov : ∀ x : G, ∃ i, x ∈ A i)
    (hdisj : Pairwise (Function.onFun Disjoint A))
    {f : G → E} (hf : Integrable f (haarProb G)) :
    ∫ z, f z ∂(haarProb G) = ∑ i, ∫ z, (A i).indicator f z ∂(haarProb G) := by
  classical
  rw [← integral_finsetSum _ fun i _ => hf.indicator (hA i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  obtain ⟨i₀, hi₀⟩ := hcov z
  show f z = ∑ i, (A i).indicator f z
  rw [Finset.sum_eq_single i₀]
  · rw [Set.indicator_of_mem hi₀]
  · intro j _ hj
    refine Set.indicator_of_notMem ?_ _
    intro hzj
    exact Set.disjoint_left.mp (hdisj hj) hzj hi₀
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [T2Space G] in
include hk hC in
/-- **The finite-rank approximation error.**  Replacing the kernel by its value at the sample point
of each piece changes the convolution by at most `ε ‖u‖`. -/
theorem norm_convC_sub_rebuild_le {ε : ℝ} (hε : 0 ≤ ε) {V : Set G}
    (hVlt : ∀ x : G, ∀ v ∈ V, ‖k (x + v) - k x‖ < ε) (y : Fin n → G)
    (hA : ∀ i, MeasurableSet (A i)) (hsub : ∀ i, ∀ z ∈ A i, z - y i ∈ V)
    (hcov : ∀ x : G, ∃ i, x ∈ A i) (hdisj : Pairwise (Function.onFun Disjoint A))
    (u : Lp ℂ 2 (haarProb G)) :
    ‖convC k hk hC u - rebuildCLM k hk y (sampleCLM A hA u)‖ ≤ ε * ‖u‖ := by
  classical
  refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
  have hint : Integrable (fun z => u z * k (x - z)) (haarProb G) :=
    integrable_mul_kernel hk hC (integrable_lp u) x
  have hintc : ∀ i : Fin n, Integrable (fun z => u z * k (x - y i)) (haarProb G) :=
    fun i => (integrable_lp u).mul_const _
  have h1 : (convC k hk hC u) x
      = ∑ i, ∫ z, (A i).indicator (fun z => u z * k (x - z)) z ∂(haarProb G) := by
    rw [convC_apply]
    exact integral_eq_sum_indicator A hA hcov hdisj hint
  have h2 : (rebuildCLM k hk y (sampleCLM A hA u)) x
      = ∑ i, ∫ z, (A i).indicator (fun z => u z * k (x - y i)) z ∂(haarProb G) := by
    rw [rebuildCLM_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsplit : ∫ z, (A i).indicator (fun z => u z * k (x - y i)) z ∂(haarProb G)
        = (∫ z, (A i).indicator (fun z => u z) z ∂(haarProb G)) * k (x - y i) := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show (A i).indicator (fun z => (u : G → ℂ) z * k (x - y i)) z
          = (A i).indicator (fun z => (u : G → ℂ) z) z * k (x - y i)
      by_cases hz : z ∈ A i
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
    rw [hsplit]
    rfl
  have hterm : ∀ i : Fin n,
      ‖(∫ z, (A i).indicator (fun z => u z * k (x - z)) z ∂(haarProb G))
        - ∫ z, (A i).indicator (fun z => u z * k (x - y i)) z ∂(haarProb G)‖
        ≤ ∫ z, (A i).indicator (fun z => ε * ‖u z‖) z ∂(haarProb G) := by
    intro i
    rw [← integral_sub (hint.indicator (hA i)) ((hintc i).indicator (hA i))]
    have hcomb : ∀ z : G,
        (A i).indicator (fun z => u z * k (x - z)) z
          - (A i).indicator (fun z => u z * k (x - y i)) z
        = (A i).indicator (fun z => u z * (k (x - z) - k (x - y i))) z := by
      intro z
      by_cases hz : z ∈ A i
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        ring
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
          sub_zero]
    rw [integral_congr_ae (Filter.Eventually.of_forall hcomb)]
    have hdiff : Integrable ((A i).indicator fun z => u z * (k (x - z) - k (x - y i)))
        (haarProb G) := by
      have : Integrable (fun z => u z * k (x - z) - u z * k (x - y i)) (haarProb G) :=
        hint.sub (hintc i)
      refine (this.indicator (hA i)).congr (Filter.Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ A i
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        ring
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine integral_mono hdiff.norm (((integrable_lp u).norm.const_mul ε).indicator (hA i)) ?_
    intro z
    show ‖(A i).indicator (fun w => (u : G → ℂ) w * (k (x - w) - k (x - y i))) z‖
        ≤ (A i).indicator (fun w => ε * ‖(u : G → ℂ) w‖) z
    by_cases hz : z ∈ A i
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, norm_mul]
      have hv : z - y i ∈ V := hsub i z hz
      have hkey : ‖k (x - z) - k (x - y i)‖ ≤ ε := by
        have hw : (x - z) + (z - y i) = x - y i := by abel
        have := hVlt (x - z) (z - y i) hv
        rw [hw] at this
        rw [← norm_neg, neg_sub]
        exact le_of_lt this
      exact mul_le_mul_of_nonneg_left hkey (norm_nonneg _) |>.trans_eq (mul_comm _ _)
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
      simp
  have hsum : ∑ i, ∫ z, (A i).indicator (fun z => ε * ‖u z‖) z ∂(haarProb G)
      = ∫ z, ε * ‖u z‖ ∂(haarProb G) :=
    (integral_eq_sum_indicator A hA hcov hdisj ((integrable_lp u).norm.const_mul ε)).symm
  rw [ContinuousMap.sub_apply, h1, h2, ← Finset.sum_sub_distrib]
  calc ‖∑ i, ((∫ z, (A i).indicator (fun z => u z * k (x - z)) z ∂(haarProb G))
          - ∫ z, (A i).indicator (fun z => u z * k (x - y i)) z ∂(haarProb G))‖
      ≤ ∑ i, ‖(∫ z, (A i).indicator (fun z => u z * k (x - z)) z ∂(haarProb G))
          - ∫ z, (A i).indicator (fun z => u z * k (x - y i)) z ∂(haarProb G)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, ∫ z, (A i).indicator (fun z => ε * ‖u z‖) z ∂(haarProb G) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ∫ z, ε * ‖u z‖ ∂(haarProb G) := hsum
    _ = ε * ∫ z, ‖u z‖ ∂(haarProb G) := integral_const_mul _ _
    _ ≤ ε * ‖u‖ := mul_le_mul_of_nonneg_left (integral_norm_le_norm u) hε

omit [T2Space G] in
/-- On a probability space the embedding of continuous functions into `L²` does not increase the
norm. -/
theorem norm_toLp_le (f : C(G, ℂ)) : ‖ContinuousMap.toLp 2 (haarProb G) ℂ f‖ ≤ ‖f‖ := by
  have hop : ‖(ContinuousMap.toLp 2 (haarProb G) ℂ : C(G, ℂ) →L[ℂ] Lp ℂ 2 (haarProb G))‖ ≤ 1 := by
    have h := ContinuousMap.toLp_norm_le (p := 2) (μ := haarProb G) (𝕜 := ℂ) (E := ℂ)
    have hu : measureUnivNNReal (haarProb G) = 1 := by
      simp [measureUnivNNReal]
    rw [hu] at h
    simpa using h
  calc ‖ContinuousMap.toLp 2 (haarProb G) ℂ f‖
      ≤ ‖(ContinuousMap.toLp 2 (haarProb G) ℂ : C(G, ℂ) →L[ℂ] Lp ℂ 2 (haarProb G))‖ * ‖f‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg f)
    _ = ‖f‖ := one_mul _

include hk in
/-- The finite-rank approximation of the convolution operator. -/
def approxOp (y : Fin n → G) (hA : ∀ i, MeasurableSet (A i)) :
    Lp ℂ 2 (haarProb G) →L[ℂ] Lp ℂ 2 (haarProb G) :=
  ((ContinuousMap.toLp 2 (haarProb G) ℂ).comp (rebuildCLM k hk y)).comp (sampleCLM A hA)

omit [T2Space G] in
include hk in
/-- The approximation is a compact operator: it factors through `ℂⁿ`. -/
theorem isCompactOperator_approxOp (y : Fin n → G) (hA : ∀ i, MeasurableSet (A i)) :
    IsCompactOperator (approxOp k hk A y hA) := by
  have hid : IsCompactOperator (id : (Fin n → ℂ) → (Fin n → ℂ)) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℂ)).mpr inferInstance
  have hB : IsCompactOperator (⇑(sampleCLM A hA)) := by
    have h := hid.comp_clm (sampleCLM A hA)
    rwa [Function.id_comp] at h
  have hS := hB.clm_comp ((ContinuousMap.toLp 2 (haarProb G) ℂ).comp (rebuildCLM k hk y))
  unfold approxOp
  rw [ContinuousLinearMap.coe_comp]
  exact hS

omit [T2Space G] in
include hk hC in
/-- **The operator-norm error of the finite-rank approximation.** -/
theorem norm_convOp_sub_approxOp_le {ε : ℝ} (hε : 0 ≤ ε) {V : Set G}
    (hVlt : ∀ x : G, ∀ v ∈ V, ‖k (x + v) - k x‖ < ε) (y : Fin n → G)
    (hA : ∀ i, MeasurableSet (A i)) (hsub : ∀ i, ∀ z ∈ A i, z - y i ∈ V)
    (hcov : ∀ x : G, ∃ i, x ∈ A i) (hdisj : Pairwise (Function.onFun Disjoint A)) :
    ‖convOp k hk hC - approxOp k hk A y hA‖ ≤ ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ hε fun u => ?_
  have hrw : (convOp k hk hC - approxOp k hk A y hA) u
      = ContinuousMap.toLp 2 (haarProb G) ℂ
          (convC k hk hC u - rebuildCLM k hk y (sampleCLM A hA u)) := by
    rw [sub_apply, map_sub]
    rfl
  rw [hrw]
  calc ‖ContinuousMap.toLp 2 (haarProb G) ℂ
        (convC k hk hC u - rebuildCLM k hk y (sampleCLM A hA u))‖
      ≤ ‖convC k hk hC u - rebuildCLM k hk y (sampleCLM A hA u)‖ := norm_toLp_le _
    _ ≤ ε * ‖u‖ := norm_convC_sub_rebuild_le k hk hC A hε hVlt y hA hsub hcov hdisj u

end Approx

section Compactness

variable (k : G → ℂ) (hk : Continuous k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)

omit [T2Space G] in
include hk hC in
/-- **The convolution operator is compact.** -/
theorem isCompactOperator_convOp : IsCompactOperator (convOp k hk hC) := by
  have key : ∀ m : ℕ, ∃ S : Lp ℂ 2 (haarProb G) →L[ℂ] Lp ℂ 2 (haarProb G),
      IsCompactOperator S ∧ ‖convOp k hk hC - S‖ ≤ 1 / (m + 1) := by
    intro m
    have hpos : (0 : ℝ) < 1 / (m + 1) := by positivity
    obtain ⟨V, hVmem, hVlt⟩ := exists_nhds_zero_norm_sub_lt k hk hpos
    obtain ⟨V', hV'sub, hV'open, hV'0⟩ := mem_nhds_iff.mp hVmem
    obtain ⟨n, y, A, hA, hsub, hcov, hdisj⟩ := exists_finite_partition_subordinate hV'open hV'0
    refine ⟨approxOp k hk A y hA, isCompactOperator_approxOp k hk A y hA, ?_⟩
    exact norm_convOp_sub_approxOp_le k hk hC A hpos.le
      (fun x v hv => hVlt x v (hV'sub hv)) y hA hsub hcov hdisj
  choose S hScomp hSnorm using key
  refine isCompactOperator_of_tendsto (l := Filter.atTop) ?_ (Filter.Eventually.of_forall hScomp)
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun m hm => ?_⟩
  have hdist : dist (S m) (convOp k hk hC) = ‖convOp k hk hC - S m‖ := by
    rw [dist_eq_norm, ← norm_neg, neg_sub]
  rw [hdist]
  refine lt_of_le_of_lt (hSnorm m) ?_
  have hmN : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 : 1 / ε < (m : ℝ) + 1 := by linarith
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at h1
  linarith

end Compactness

end

end CompactAbelian

end GaloisForLFunctions
