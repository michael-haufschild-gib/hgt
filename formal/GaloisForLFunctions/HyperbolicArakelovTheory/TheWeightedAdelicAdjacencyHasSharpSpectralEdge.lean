import GaloisForLFunctions.HyperbolicArakelovTheory.ThePrimeWalkHasTheSharpTemperedSpectralEdge
import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeightedAdelicAdjacencyOnSquareSummableCharges
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The weighted adelic adjacency has sharp spectral edge

Finite products of local charges preserve their squared norms and separate
coordinate energies. Exhausting the summable prime weights makes the Schur
bound sharp on finite nonnegative charges of the actual adelic carrier.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology InnerProductSpace

namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic AdelicAdjacency
open scoped Classical BigOperators

private def boxVertex (S : Finset Prime) (v : ∀ p : S, LocalVertex p.1) : FiniteVertices :=
  ⟨fun p => if h : p ∈ S then v ⟨p, h⟩ else baseVertex p, by
    apply S.finite_toSet.subset
    intro p hp
    by_contra h
    exact hp (dif_neg h)⟩

private theorem boxVertex_at (S : Finset Prime) (v : ∀ p : S, LocalVertex p.1) (p : S) :
    (boxVertex S v).1 p.1 = v p := by
  simp only [boxVertex, dif_pos p.2]

private theorem boxVertex_injective (S : Finset Prime) : Function.Injective (boxVertex S) := by
  intro v w h
  funext p
  have hp := congrArg (fun y : FiniteVertices => y.1 p.1) h
  simpa only [boxVertex_at] using hp

private def boxEmbedding (S : Finset Prime) : (∀ p : S, LocalVertex p.1) ↪ FiniteVertices :=
  ⟨boxVertex S, boxVertex_injective S⟩

private theorem boxVertex_update (S : Finset Prime) (v : ∀ p : S, LocalVertex p.1)
    (p : S) (z : LocalVertex p.1) :
    boxVertex S (Function.update v p z) = replaceVertex p.1 (boxVertex S v) z := by
  apply Subtype.ext
  funext q
  by_cases hq : q = p.1
  · subst q
    rw [boxVertex_at S _ p, Function.update_self, replaceVertex_at]
  · rw [replaceVertex_away _ _ _ q hq]
    by_cases hqs : q ∈ S
    · rw [boxVertex_at S _ ⟨q,hqs⟩, boxVertex_at S _ ⟨q,hqs⟩,
        Function.update_of_ne (fun h => hq (congrArg Subtype.val h))]
    · simp only [boxVertex, dif_neg hqs]

private def boxAmplitude {ι : Type*} [Fintype ι] {V : ι → Type*}
    (f : ∀ i, V i →₀ ℝ) : (∀ i, V i) →₀ ℝ :=
  Finsupp.onFinset (Fintype.piFinset fun i => (f i).support)
    (fun v => ∏ i, f i (v i)) (by
      intro v hv
      rw [Fintype.mem_piFinset]
      intro i
      apply Finsupp.mem_support_iff.mpr
      intro hi
      exact hv (Finset.prod_eq_zero (Finset.mem_univ i) hi))

private theorem boxAmplitude_apply {ι : Type*} [Fintype ι] {V : ι → Type*}
    (f : ∀ i, V i →₀ ℝ) (v : ∀ i, V i) : boxAmplitude f v = ∏ i, f i (v i) := rfl

private theorem boxAmplitude_support {ι : Type*} [Fintype ι] {V : ι → Type*}
    (f : ∀ i, V i →₀ ℝ) :
    (boxAmplitude f).support = Fintype.piFinset fun i => (f i).support := by
  ext v
  simp only [Finsupp.mem_support_iff, boxAmplitude_apply, Finset.prod_ne_zero_iff,
    Finset.mem_univ, forall_true_left, Fintype.mem_piFinset]

private theorem boxAmplitude_square {ι : Type*} [Fintype ι] {V : ι → Type*}
    (f : ∀ i, V i →₀ ℝ) :
    (∑ v ∈ (boxAmplitude f).support, boxAmplitude f v ^ 2) =
      ∏ i, ∑ y ∈ (f i).support, f i y ^ 2 := by
  simp only [boxAmplitude_support, boxAmplitude_apply, ← Finset.prod_pow]
  exact (Finset.prod_univ_sum (fun i => (f i).support) (fun i y => f i y ^ 2)).symm

private def adelicBoxCharge (S : Finset Prime) (f : ∀ p : S, LocalVertex p.1 →₀ ℝ) :
    FiniteVertices →₀ ℝ := (boxAmplitude f).embDomain (boxEmbedding S)

private theorem adelicBoxCharge_apply (S : Finset Prime)
    (f : ∀ p : S, LocalVertex p.1 →₀ ℝ) (v : ∀ p : S, LocalVertex p.1) :
    adelicBoxCharge S f (boxVertex S v) = ∏ p, f p (v p) :=
  Finsupp.embDomain_apply_self _ _ _

private theorem adelicBoxCharge_norm_sq (S : Finset Prime)
    (f : ∀ p : S, LocalVertex p.1 →₀ ℝ) :
    ‖finiteChargeEmbedding (adelicBoxCharge S f)‖ ^ 2 =
      ∏ p, ∑ y ∈ (f p).support, f p y ^ 2 := by
  rw [finiteChargeEmbedding_norm_sq]
  change ((boxAmplitude f).embDomain (boxEmbedding S)).sum (fun _ r => r ^ 2) = _
  rw [Finsupp.sum_embDomain]
  exact boxAmplitude_square f

private theorem box_product_split (S : Finset Prime)
    (f : ∀ p : S, LocalVertex p.1 →₀ ℝ) (v : ∀ p : S, LocalVertex p.1) (p : S) :
    (∏ q, f q (v q)) = f p (v p) * ∏ q ∈ Finset.univ.erase p, f q (v q) :=
  (Finset.mul_prod_erase Finset.univ (fun q => f q (v q)) (Finset.mem_univ p)).symm

private theorem box_product_update (S : Finset Prime)
    (f : ∀ p : S, LocalVertex p.1 →₀ ℝ) (v : ∀ p : S, LocalVertex p.1)
    (p : S) (z : LocalVertex p.1) :
    (∏ q, f q (Function.update v p z q)) =
      f p z * ∏ q ∈ Finset.univ.erase p, f q (v q) := by
  rw [box_product_split S f _ p, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  rw [Function.update_of_ne (Finset.mem_erase.mp hq).1]

private theorem adelicBoxCharge_localAdj (S : Finset Prime)
    (f : ∀ p : S, LocalVertex p.1 →₀ ℝ) (v : ∀ p : S, LocalVertex p.1) (p : S) :
    localAdj p.1 (adelicBoxCharge S f) (boxVertex S v) =
      (∑ z ∈ neighbors p.1 (v p), f p z) *
        ∏ q ∈ Finset.univ.erase p, f q (v q) := by
  rw [localAdj, boxVertex_at]
  simp_rw [← boxVertex_update S v p, adelicBoxCharge_apply, box_product_update]
  rw [Finset.sum_mul]

private theorem adelicBoxCharge_nonneg (S : Finset Prime)
    (f : ∀ p : S, LocalVertex p.1 →₀ ℝ) (hf : ∀ p y, 0 ≤ f p y)
    (y : FiniteVertices) : 0 ≤ adelicBoxCharge S f y := by
  by_cases hy : y ∈ Set.range (boxEmbedding S)
  · obtain ⟨v, rfl⟩ := hy
    rw [show (boxEmbedding S) v = boxVertex S v from rfl, adelicBoxCharge_apply]
    exact Finset.prod_nonneg fun p _ => hf p _
  · rw [adelicBoxCharge, Finsupp.embDomain_notin_range _ _ _ hy]

private theorem adelicBoxCharge_local_energy (S : Finset Prime)
    (f : ∀ p : S, LocalVertex p.1 →₀ ℝ) (p : S) :
    (∑ y ∈ (adelicBoxCharge S f).support,
      adelicBoxCharge S f y * localAdj p.1 (adelicBoxCharge S f) y) =
      (∑ y ∈ (f p).support, f p y * (∑ z ∈ neighbors p.1 y, f p z)) *
        ∏ q ∈ Finset.univ.erase p, ∑ y ∈ (f q).support, f q y ^ 2 := by
  change ((boxAmplitude f).embDomain (boxEmbedding S)).sum
    (fun y r => r * localAdj p.1 (adelicBoxCharge S f) y) = _
  rw [Finsupp.sum_embDomain]
  change (∑ v ∈ (boxAmplitude f).support,
    boxAmplitude f v * localAdj p.1 (adelicBoxCharge S f) (boxVertex S v)) = _
  rw [boxAmplitude_support]
  let g (q : S) (y : LocalVertex q.1) : ℝ :=
    if q = p then f q y * (∑ z ∈ neighbors q.1 y, f q z) else f q y ^ 2
  have hterm (v : ∀ q : S, LocalVertex q.1) :
      boxAmplitude f v * localAdj p.1 (adelicBoxCharge S f) (boxVertex S v) =
        ∏ q, g q (v q) := by
    rw [boxAmplitude_apply, adelicBoxCharge_localAdj, box_product_split S f v p]
    rw [← Finset.mul_prod_erase Finset.univ (fun q => g q (v q)) (Finset.mem_univ p)]
    simp only [g, if_pos rfl]
    have he : (∏ q ∈ Finset.univ.erase p,
        if q = p then f q (v q) * (∑ z ∈ neighbors q.1 (v q), f q z) else f q (v q) ^ 2) =
        (∏ q ∈ Finset.univ.erase p, f q (v q)) ^ 2 := by
      rw [← Finset.prod_pow]
      exact Finset.prod_congr rfl fun q hq => if_neg (Finset.mem_erase.mp hq).1
    rw [he]
    ring
  simp_rw [hterm]
  trans ∏ q : S, ∑ y ∈ (f q).support, g q y
  · exact (Finset.prod_univ_sum (fun q : S => (f q).support) g).symm
  rw [← Finset.mul_prod_erase Finset.univ
    (fun q => ∑ y ∈ (f q).support, g q y) (Finset.mem_univ p)]
  simp only [g, if_pos rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  simp only [if_neg (Finset.mem_erase.mp hq).1]

private theorem finiteCharge_quadratic (f : FiniteVertices →₀ ℝ) :
    ⟪adjacencyOperator (finiteChargeEmbedding f), finiteChargeEmbedding f⟫_ℝ =
      ∑ y ∈ f.support, f y * adjacency f y := by
  have he : (finiteChargeEmbedding f : FiniteVertices → ℝ) = f :=
    funext (finiteChargeEmbedding_apply f)
  conv_lhs => rhs; rw [finiteChargeEmbedding_eq]
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [lp.inner_single_right, adjacencyOperator_apply, he]
  rfl

private theorem finiteCharge_quadratic_ge (S : Finset Prime) (f : FiniteVertices →₀ ℝ)
    (hf : ∀ y, 0 ≤ f y) :
    (∑ p ∈ S, weight p * ∑ y ∈ f.support, f y * localAdj p f y) ≤
      ⟪adjacencyOperator (finiteChargeEmbedding f), finiteChargeEmbedding f⟫_ℝ := by
  have he : (finiteChargeEmbedding f : FiniteVertices → ℝ) = f :=
    funext (finiteChargeEmbedding_apply f)
  have hd : InDomain f := by
    have h := chargeSpace_inDomain (finiteChargeEmbedding f)
    rwa [he] at h
  rw [finiteCharge_quadratic]
  calc
    _ = ∑ y ∈ f.support, f y * ∑ p ∈ S, placeTerm p f y := by
      simp only [Finset.mul_sum, placeTerm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ _ := Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left
        ((hd y).sum_le_tsum S (fun p _ => placeTerm_nonneg p hf y)) (hf y)

private theorem square_sum_pos {α : Type*} (f : α →₀ ℝ) (hf : f ≠ 0) :
    0 < ∑ y ∈ f.support, f y ^ 2 := by
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp hf
  have hy' : f y ≠ 0 := hy
  exact (sq_pos_of_ne_zero hy').trans_le
    (Finset.single_le_sum (fun z _ => sq_nonneg (f z)) (Finsupp.mem_support_iff.mpr hy'))

/-- Finite nonnegative charges approach the full weighted adelic spectral edge. -/
theorem exists_finite_charge_above (c : ℝ) (hc : c < edge) :
    ∃ f : FiniteVertices →₀ ℝ, (∀ y, 0 ≤ f y) ∧
      c * ‖finiteChargeEmbedding f‖ ^ 2 <
        ⟪adjacencyOperator (finiteChargeEmbedding f), finiteChargeEmbedding f⟫_ℝ := by
  obtain ⟨b, hb, hbe⟩ := exists_between (max_lt hc edge_pos)
  have hb0 : 0 < b := (le_max_right c 0).trans_lt hb
  have hcb : c < b := (le_max_left c 0).trans_lt hb
  have hevent : ∀ᶠ S : Finset Prime in atTop, b < ∑ p ∈ S, edgeTerm p :=
    summable_edgeTerm.hasSum.eventually (lt_mem_nhds hbe)
  obtain ⟨S, hS⟩ := hevent.exists
  let L := ∑ p ∈ S, edgeTerm p
  have hL : 0 < L := hb0.trans hS
  have hSn : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hS
    exact (not_lt_of_ge hb0.le) hS
  let a := b / L
  have ha0 : 0 < a := div_pos hb0 hL
  have ha1 : a < 1 := (div_lt_one hL).mpr hS
  have hlocal (p : S) : ∃ f : LocalVertex p.1 →₀ ℝ, (∀ y, 0 ≤ f y) ∧
      (a * (2 * Real.sqrt p.1.1)) * (∑ y ∈ f.support, f y ^ 2) <
        ∑ y ∈ f.support, f y * (∑ z ∈ neighbors p.1 y, f z) := by
    have hp : (1 : ℝ) < p.1.1 := by exact_mod_cast p.1.2.one_lt
    apply PrimeSpectralEdge.exists_finite_charge_above
    rw [(treeEigen_eq_iff hp (1 / 2)).mpr rfl]
    exact mul_lt_of_lt_one_left (by positivity) ha1
  choose f hf hr using hlocal
  have hn (p : S) : 0 < ∑ y ∈ (f p).support, f p y ^ 2 := by
    apply square_sum_pos
    intro hzero
    have h := hr p
    simp only [hzero, Finsupp.support_zero, Finset.sum_empty, mul_zero, lt_self_iff_false] at h
  let M := ∏ p : S, ∑ y ∈ (f p).support, f p y ^ 2
  have hM : 0 < M := Finset.prod_pos fun p _ => hn p
  refine ⟨adelicBoxCharge S f, adelicBoxCharge_nonneg S f hf, ?_⟩
  rw [adelicBoxCharge_norm_sq]
  change c * M < _
  have hprime (p : S) : a * edgeTerm p.1 * M <
      weight p.1 * ∑ y ∈ (adelicBoxCharge S f).support,
        adelicBoxCharge S f y * localAdj p.1 (adelicBoxCharge S f) y := by
    rw [adelicBoxCharge_local_energy]
    have ht : 0 < ∏ q ∈ Finset.univ.erase p, ∑ y ∈ (f q).support, f q y ^ 2 :=
      Finset.prod_pos fun q _ => hn q
    have h := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right (hr p) ht) (weight_pos p.1)
    have hm : M = (∑ y ∈ (f p).support, f p y ^ 2) *
        ∏ q ∈ Finset.univ.erase p, ∑ y ∈ (f q).support, f q y ^ 2 :=
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p)).symm
    calc
      _ = weight p.1 * (((a * (2 * Real.sqrt p.1.1)) *
          (∑ y ∈ (f p).support, f p y ^ 2)) *
          ∏ q ∈ Finset.univ.erase p, ∑ y ∈ (f q).support, f q y ^ 2) := by
        rw [hm, edgeTerm]
        ring
      _ < _ := h
  have hsum : a * L * M <
      ∑ p ∈ S, weight p * ∑ y ∈ (adelicBoxCharge S f).support,
        adelicBoxCharge S f y * localAdj p (adelicBoxCharge S f) y := by
    have h := Finset.sum_lt_sum_of_nonempty
      (show (Finset.univ : Finset S).Nonempty from ⟨⟨hSn.choose, hSn.choose_spec⟩, Finset.mem_univ _⟩)
      (fun p _ => hprime p)
    simpa only [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_coe_sort, L] using h
  have hab : a * L = b := div_mul_cancel₀ b hL.ne'
  rw [hab] at hsum
  exact (mul_lt_mul_of_pos_right hcb hM).trans
    (hsum.trans_le (finiteCharge_quadratic_ge S _ (adelicBoxCharge_nonneg S f hf)))

/-- The Schur upper bound is attained as a supremum on finite charges. -/
theorem adjacencyOperator_norm_eq_edge : ‖adjacencyOperator‖ = edge := by
  apply le_antisymm adjacencyOperator_norm_le
  by_contra h
  obtain ⟨f, _, hf⟩ := exists_finite_charge_above ‖adjacencyOperator‖ (lt_of_not_ge h)
  have hi := real_inner_le_norm (adjacencyOperator (finiteChargeEmbedding f)) (finiteChargeEmbedding f)
  have hn := mul_le_mul_of_nonneg_right (adjacencyOperator.le_opNorm (finiteChargeEmbedding f))
    (norm_nonneg (finiteChargeEmbedding f))
  have hbound : ⟪adjacencyOperator (finiteChargeEmbedding f), finiteChargeEmbedding f⟫_ℝ ≤
      ‖adjacencyOperator‖ * ‖finiteChargeEmbedding f‖ ^ 2 := by
    exact (hi.trans hn).trans_eq (by ring)
  exact (not_lt_of_ge hbound) hf

#print axioms exists_finite_charge_above
#print axioms adjacencyOperator_norm_eq_edge
end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
