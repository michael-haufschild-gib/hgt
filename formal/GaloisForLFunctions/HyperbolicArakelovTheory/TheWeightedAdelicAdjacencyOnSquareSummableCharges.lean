import GaloisForLFunctions.HyperbolicArakelovTheory.TheGroundStateEnergyOfTheAdelicCarrier
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The weighted adelic adjacency on square-summable charges

The positive restricted Green product controls every finite rectangular
section of the actual adjacency matrix. Its weighted Schur estimate gives
the counting Hilbert-space operator even though constant rows diverge.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators Topology InnerProductSpace ENNReal

namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic AdelicAdjacency CoupledProductObstruction

theorem kernel_product_row_le (x y : FiniteVertices) (F : Finset FiniteVertices) :
    (∑ z ∈ F, adjacencyKernel y z * finiteGreenProduct x z) ≤
      edge * finiteGreenProduct x y := by
  rw [← adjacency_finiteSource]
  have hb := boundary_nonneg x F y
  have hs := product_source x y
  have hp := mul_nonneg (product_pos x y).le (profile_nonneg x y)
  unfold boundary at hb
  linarith only [hb, hs, hp]

private theorem kernel_row_square (x y : FiniteVertices) (F : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) :
    (∑ z ∈ F, adjacencyKernel y z * f z) ^ 2 ≤
      (∑ z ∈ F, adjacencyKernel y z * finiteGreenProduct x z) *
      ∑ z ∈ F, adjacencyKernel y z * f z ^ 2 / finiteGreenProduct x z := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul F
    (fun z _ => mul_nonneg (adjacencyKernel_nonneg y z) (product_pos x z).le)
    (fun z _ => div_nonneg (mul_nonneg (adjacencyKernel_nonneg y z) (sq_nonneg _))
      (product_pos x z).le)
  intro z _
  apply le_of_eq
  field_simp [(product_pos x z).ne']

/-- Uniform bound on arbitrary input and output sections of the actual prime sum. -/
theorem finite_adjacency_square_bound (S T : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) :
    (∑ y ∈ T, adjacency (finiteSource S f) y ^ 2) ≤
      edge ^ 2 * ∑ z ∈ S, f z ^ 2 := by
  let x : FiniteVertices := ⟨fun p => baseVertex p, by simp⟩
  have hrow (y : FiniteVertices) :
      adjacency (finiteSource S f) y ^ 2 ≤
        edge * finiteGreenProduct x y *
          ∑ z ∈ S, adjacencyKernel y z * f z ^ 2 / finiteGreenProduct x z := by
    rw [adjacency_finiteSource]
    exact (kernel_row_square x y S f).trans
      (mul_le_mul_of_nonneg_right (kernel_product_row_le x y S)
        (Finset.sum_nonneg fun z _ => div_nonneg
          (mul_nonneg (adjacencyKernel_nonneg y z) (sq_nonneg _)) (product_pos x z).le))
  calc
    _ ≤ ∑ y ∈ T, edge * finiteGreenProduct x y *
        ∑ z ∈ S, adjacencyKernel y z * f z ^ 2 / finiteGreenProduct x z :=
      Finset.sum_le_sum fun y _ => hrow y
    _ = ∑ z ∈ S, edge * (f z ^ 2 / finiteGreenProduct x z) *
        ∑ y ∈ T, adjacencyKernel z y * finiteGreenProduct x y := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro y _
      rw [adjacencyKernel_symm y z]
      ring
    _ ≤ ∑ z ∈ S, edge * (f z ^ 2 / finiteGreenProduct x z) *
        (edge * finiteGreenProduct x z) := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (kernel_product_row_le x z T)
        (mul_nonneg edge_pos.le (div_nonneg (sq_nonneg _) (product_pos x z).le))
    _ = edge ^ 2 * ∑ z ∈ S, f z ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      field_simp [(product_pos x z).ne']

abbrev ChargeSpace := lp (fun _ : FiniteVertices => ℝ) 2

theorem finite_adjacency_memℓp (S : Finset FiniteVertices) (f : FiniteVertices → ℝ) :
    Memℓp (adjacency (finiteSource S f)) 2 := by
  have hs : Summable (fun y => adjacency (finiteSource S f) y ^ 2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) (finite_adjacency_square_bound S · f)
  exact memℓp_gen (hs.congr fun _ => by
    rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs])

/-- A matrix column of the actual adjacency, as a counting square-summable vector. -/
def adjacencyColumn (z : FiniteVertices) : ChargeSpace :=
  ⟨fun y => adjacencyKernel y z, by
    change Memℓp (fun y => adjacencyKernel y z) 2
    have he : adjacency (finiteSource {z} (fun _ => 1)) =
        (fun y => adjacencyKernel y z) := by
      funext y
      rw [adjacency_finiteSource, Finset.sum_singleton, mul_one]
    rw [← he]
    exact finite_adjacency_memℓp {z} (fun _ => 1)⟩

def finiteChargeEmbedding : (FiniteVertices →₀ ℝ) →ₗ[ℝ] ChargeSpace :=
  Finsupp.linearCombination ℝ (fun y => lp.single 2 y (1 : ℝ))

def finiteAdjacency : (FiniteVertices →₀ ℝ) →ₗ[ℝ] ChargeSpace :=
  Finsupp.linearCombination ℝ adjacencyColumn

theorem finiteChargeEmbedding_eq (f : FiniteVertices →₀ ℝ) :
    finiteChargeEmbedding f = ∑ y ∈ f.support, lp.single 2 y (f y) := by
  simp only [finiteChargeEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    ← lp.single_smul, smul_eq_mul, mul_one]

theorem finiteAdjacency_apply (f : FiniteVertices →₀ ℝ) (y : FiniteVertices) :
    finiteAdjacency f y = adjacency (finiteSource f.support f) y := by
  rw [adjacency_finiteSource]
  simp only [finiteAdjacency, Finsupp.linearCombination_apply, Finsupp.sum,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, adjacencyColumn, mul_comm]

theorem finiteChargeEmbedding_norm_sq (f : FiniteVertices →₀ ℝ) :
    ‖finiteChargeEmbedding f‖ ^ 2 = ∑ y ∈ f.support, f y ^ 2 := by
  rw [finiteChargeEmbedding_eq]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    lp.norm_sum_single (p := 2) (by norm_num) (fun y => f y) f.support

theorem finiteAdjacency_norm_le (f : FiniteVertices →₀ ℝ) :
    ‖finiteAdjacency f‖ ≤ edge * ‖finiteChargeEmbedding f‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (mul_nonneg edge_pos.le (norm_nonneg _))
  intro T
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    finiteAdjacency_apply, mul_pow, finiteChargeEmbedding_norm_sq]
  exact finite_adjacency_square_bound f.support T f

theorem finiteChargeEmbedding_dense : DenseRange finiteChargeEmbedding := by
  intro f
  apply isClosed_closure.mem_of_tendsto
    (lp.hasSum_single (E := fun _ : FiniteVertices => ℝ) (p := 2) (by norm_num) f)
  apply Filter.Eventually.of_forall
  intro F
  apply subset_closure
  refine ⟨∑ y ∈ F, Finsupp.single y (f y), ?_⟩
  simp only [map_sum, finiteChargeEmbedding, Finsupp.linearCombination_single,
    ← lp.single_smul, smul_eq_mul, mul_one]

/-- The unique bounded extension of the actual prime adjacency from finite charges. -/
def adjacencyOperator : ChargeSpace →L[ℝ] ChargeSpace :=
  finiteAdjacency.extendOfNorm finiteChargeEmbedding

theorem adjacencyOperator_finite (f : FiniteVertices →₀ ℝ) :
    adjacencyOperator (finiteChargeEmbedding f) = finiteAdjacency f :=
  LinearMap.extendOfNorm_eq finiteChargeEmbedding_dense ⟨edge, finiteAdjacency_norm_le⟩ f

theorem adjacencyOperator_norm_le : ‖adjacencyOperator‖ ≤ edge :=
  LinearMap.opNorm_extendOfNorm_le finiteChargeEmbedding_dense edge_pos.le finiteAdjacency_norm_le

theorem finiteChargeEmbedding_apply (f : FiniteVertices →₀ ℝ) (y : FiniteVertices) :
    finiteChargeEmbedding f y = f y := by
  rw [finiteChargeEmbedding_eq]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

/-- Evaluation of the bounded extension is pairing against its actual matrix row. -/
theorem adjacencyOperator_apply_inner (f : ChargeSpace) (y : FiniteVertices) :
    adjacencyOperator f y = ⟪adjacencyColumn y, f⟫_ℝ := by
  refine finiteChargeEmbedding_dense.induction_on
    (p := fun g => adjacencyOperator g y = ⟪adjacencyColumn y, g⟫_ℝ) f ?_ ?_
  · apply isClosed_eq
    · exact (lp.lipschitzWith_one_eval 2 y).continuous.comp adjacencyOperator.continuous
    · exact continuous_const.inner continuous_id
  intro g
  rw [adjacencyOperator_finite, finiteAdjacency_apply, adjacency_finiteSource,
    finiteChargeEmbedding_eq, inner_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [lp.inner_single_right]
  change adjacencyKernel y z * g z = g z * adjacencyKernel z y
  rw [adjacencyKernel_symm z y, mul_comm]

theorem adjacencyOperator_nonneg (f : ChargeSpace) (hf : ∀ y, 0 ≤ f y)
    (y : FiniteVertices) : 0 ≤ adjacencyOperator f y := by
  rw [adjacencyOperator_apply_inner, lp.inner_eq_tsum]
  exact tsum_nonneg fun z => mul_nonneg (hf z) (adjacencyKernel_nonneg z y)

/-- Symmetry survives completion on the actual counting Hilbert space. -/
theorem adjacencyOperator_symmetric (f g : ChargeSpace) :
    ⟪adjacencyOperator f, g⟫_ℝ = ⟪f, adjacencyOperator g⟫_ℝ := by
  refine finiteChargeEmbedding_dense.induction_on
    (p := fun g => ⟪adjacencyOperator f, g⟫_ℝ = ⟪f, adjacencyOperator g⟫_ℝ) g ?_ ?_
  · exact isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner adjacencyOperator.continuous)
  intro h
  rw [adjacencyOperator_finite]
  rw [finiteChargeEmbedding_eq, inner_sum]
  simp only [finiteAdjacency, Finsupp.linearCombination_apply, Finsupp.sum, inner_sum,
    inner_smul_right]
  apply Finset.sum_congr rfl
  intro z _
  rw [lp.inner_single_right]
  change h z * adjacencyOperator f z = h z * ⟪f, adjacencyColumn z⟫_ℝ
  rw [adjacencyOperator_apply_inner]
  exact congrArg (fun t => h z * t) (real_inner_comm f (adjacencyColumn z))

/-- Each local neighbour sum has the counting square-root bound. -/
theorem localAdj_lp_bound (p : Prime) (f : ChargeSpace) (y : FiniteVertices) :
    |localAdj p f y| ≤ 2 * Real.sqrt p.1 * ‖f‖ := by
  let F := neighborVertices p y
  have hc : F.card = p.1 + 1 := by
    change (neighborVertices p y).card = p.1 + 1
    rw [neighborVertices, Finset.card_image_of_injective _
      (replaceVertex_injective p y), card_neighbors]
  have hs := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) f F
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at hs
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F (fun z => f z) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hp : (1 : ℝ) ≤ p.1 := by exact_mod_cast p.2.one_lt.le
  have hp0 : (0 : ℝ) ≤ p.1 := le_trans zero_le_one hp
  have hcard : (F.card : ℝ) ≤ 4 * p.1 := by
    rw [hc, Nat.cast_add, Nat.cast_one]
    linarith only [hp]
  have hsq : localAdj p f y ^ 2 ≤ (2 * Real.sqrt p.1 * ‖f‖) ^ 2 := by
    rw [localAdj_eq_sum_vertices]
    calc
      _ ≤ (∑ z ∈ F, f z ^ 2) * F.card := hcs
      _ ≤ ‖f‖ ^ 2 * (4 * p.1) :=
        mul_le_mul hs hcard (Nat.cast_nonneg _) (sq_nonneg _)
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hp0]; ring
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsq)

theorem placeTerm_lp_bound (p : Prime) (f : ChargeSpace) (y : FiniteVertices) :
    ‖placeTerm p f y‖ ≤ edgeTerm p * ‖f‖ := by
  rw [placeTerm, Real.norm_eq_abs, abs_mul, abs_of_pos (weight_pos p)]
  exact (mul_le_mul_of_nonneg_left (localAdj_lp_bound p f y) (weight_pos p).le).trans_eq
    (by rw [edgeTerm]; ring)

/-- All counting square-summable charges lie in the actual all-prime domain. -/
theorem chargeSpace_inDomain (f : ChargeSpace) : InDomain f := fun y =>
  Summable.of_norm_bounded (summable_edgeTerm.mul_right ‖f‖)
    (fun p => placeTerm_lp_bound p f y)

private def primeFunctional (p : Prime) (y : FiniteVertices) : ChargeSpace →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => placeTerm p f y
      map_add' := by
        intro f g
        simp only [placeTerm, localAdj, lp.coeFn_add, Pi.add_apply,
          Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro c f
        simp only [placeTerm, localAdj, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
          ← Finset.mul_sum, RingHom.id_apply]
        ring }
    (edgeTerm p) (fun f => placeTerm_lp_bound p f y)

private theorem primeFunctional_summable (y : FiniteVertices) :
    Summable (fun p => primeFunctional p y) := by
  apply Summable.of_norm_bounded summable_edgeTerm
  intro p
  exact (primeFunctional p y).opNorm_le_bound (edgeTerm_pos p).le
    (fun f => placeTerm_lp_bound p f y)

/-- The bounded operator is the original all-prime sum on every square-summable charge. -/
theorem adjacencyOperator_apply (f : ChargeSpace) (y : FiniteVertices) :
    adjacencyOperator f y = adjacency f y := by
  let L : ChargeSpace →L[ℝ] ℝ := ∑' p, primeFunctional p y
  have hL (g : ChargeSpace) : L g = adjacency g y := by
    exact (ContinuousLinearMap.apply ℝ ℝ g).map_tsum (primeFunctional_summable y)
  rw [← hL]
  refine finiteChargeEmbedding_dense.induction_on
    (p := fun g => adjacencyOperator g y = L g) f ?_ ?_
  · exact isClosed_eq
      ((lp.lipschitzWith_one_eval 2 y).continuous.comp adjacencyOperator.continuous)
      L.continuous
  intro g
  rw [adjacencyOperator_finite, finiteAdjacency_apply, hL]
  congr 1
  funext z
  rw [finiteChargeEmbedding_apply]
  unfold finiteSource
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

#print axioms finite_adjacency_square_bound
#print axioms adjacencyOperator_norm_le
#print axioms adjacencyOperator_nonneg
#print axioms adjacencyOperator_symmetric
#print axioms chargeSpace_inDomain
#print axioms adjacencyOperator_apply

end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
