import GaloisForLFunctions.HTGeometry.SimplexFixedPoint
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.IntermediateValue

/-!
# Perron comparison of finite positive kernels

Normalization on the simplex gives a positive right eigenvector. Pairing
with a positive left eigenvector compares two kernels after a diagonal
change of coordinates. A rank-one correction factors into two scalar
pairings and supplies a lower bound on the eigenvalue gap.
-/

open Filter Finset Matrix Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite real kernel with every entry strictly positive. -/
def EntrywisePositiveKernel (ι : Type*) := {A : Matrix ι ι ℝ // ∀ i j, 0 < A i j}

namespace EntrywisePositiveKernel

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
private theorem mulVec_pos (A : EntrywisePositiveKernel ι) (x : stdSimplex ℝ ι) (i : ι) :
    0 < (A.val *ᵥ x.val) i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < x.val j := by
    by_contra! h
    have hz (j : ι) : x.val j = 0 := le_antisymm (h j) (x.property.1 j)
    simpa only [hz, sum_const_zero, zero_ne_one] using x.property.2
  change 0 < ∑ k, A.val i k * x.val k
  exact sum_pos' (fun k _ => mul_nonneg (A.property i k).le (x.property.1 k))
    ⟨j, mem_univ j, mul_pos (A.property i j) hj⟩

/-- A strictly positive kernel has a positive eigenvalue with a normalized
strictly positive eigenvector. -/
theorem exists_positive_eigenpair (A : EntrywisePositiveKernel ι) :
    ∃ λ : ℝ, 0 < λ ∧ ∃ x ∈ stdSimplex ℝ ι, (∀ i, 0 < x i) ∧ A.val *ᵥ x = λ • x := by
  let a (x : stdSimplex ℝ ι) := ∑ i, (A.val *ᵥ x.val) i
  have ha (x : stdSimplex ℝ ι) : 0 < a x :=
    sum_pos (fun i _ => mulVec_pos A x i) univ_nonempty
  let f (x : stdSimplex ℝ ι) : stdSimplex ℝ ι :=
    ⟨fun i => (A.val *ᵥ x.val) i / a x, fun i => (div_pos (mulVec_pos A x i) (ha x)).le, by
      rw [← sum_div]
      exact div_self (ha x).ne'⟩
  have hc (i : ι) : Continuous (fun x : stdSimplex ℝ ι => (A.val *ᵥ x.val) i) := by
    change Continuous (fun x : stdSimplex ℝ ι => ∑ j, A.val i j * x.val j)
    exact continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => (hc i).div (continuous_finsetSum _ fun j _ => hc j)
      fun x => (ha x).ne'
  obtain ⟨x, hx⟩ := exists_fixedPoint_stdSimplex f hf
  have hfixed (i : ι) : (A.val *ᵥ x.val) i / a x = x.val i :=
    congrArg (fun y : stdSimplex ℝ ι => y.val i) hx
  refine ⟨a x, ha x, x.val, x.property, fun i => hfixed i ▸ div_pos (mulVec_pos A x i) (ha x), ?_⟩
  funext i
  change (A.val *ᵥ x.val) i = a x * x.val i
  exact ((div_eq_iff (ha x).ne').mp (hfixed i)).trans (mul_comm _ _)

/-- The positive eigenvalue selected by the simplex map. -/
def perronRoot (A : EntrywisePositiveKernel ι) : ℝ :=
  (exists_positive_eigenpair A).choose

theorem perronRoot_spec (A : EntrywisePositiveKernel ι) :
    0 < A.perronRoot ∧ ∃ x ∈ stdSimplex ℝ ι, (∀ i, 0 < x i) ∧ A.val *ᵥ x = A.perronRoot • x :=
  (exists_positive_eigenpair A).choose_spec

private def transpose (A : EntrywisePositiveKernel ι) : EntrywisePositiveKernel ι :=
  ⟨A.val.transpose, fun i j => A.property j i⟩

omit [Nonempty ι] in
private theorem sum_mulVec_eq_sum_vecMul (A : Matrix ι ι ℝ) (w x : ι → ℝ) :
    ∑ i, w i * (A *ᵥ x) i = ∑ j, (w ᵥ* A) j * x j := by
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => (mul_assoc _ _ _).symm

omit [Nonempty ι] in
private theorem sum_mulVec_of_leftEigen (A : Matrix ι ι ℝ) (w x : ι → ℝ) (λ : ℝ)
    (hw : w ᵥ* A = λ • w) :
    ∑ i, w i * (A *ᵥ x) i = λ * ∑ i, w i * x i := by
  rw [sum_mulVec_eq_sum_vecMul, hw, mul_sum]
  exact sum_congr rfl fun i _ => mul_assoc _ _ _

omit [Nonempty ι] in
private theorem sum_mulVec_of_rightEigen (A : Matrix ι ι ℝ) (w x : ι → ℝ) (λ : ℝ)
    (hx : A *ᵥ x = λ • x) :
    ∑ i, w i * (A *ᵥ x) i = λ * ∑ i, w i * x i := by
  rw [hx, mul_sum]
  exact sum_congr rfl fun i _ => mul_left_comm _ _ _

/-- The Perron root has a normalized strictly positive left eigenvector. -/
theorem exists_positive_leftEigen (A : EntrywisePositiveKernel ι) :
    ∃ w ∈ stdSimplex ℝ ι, (∀ i, 0 < w i) ∧ w ᵥ* A.val = A.perronRoot • w := by
  obtain ⟨_, w, hws, hwp, hw⟩ := perronRoot_spec A.transpose
  obtain ⟨_, x, _, hxp, hx⟩ := perronRoot_spec A
  have hwl : w ᵥ* A.val = A.transpose.perronRoot • w := by
    rw [← hw]
    funext i
    exact sum_congr rfl fun j _ => mul_comm _ _
  have hpair : 0 < ∑ i, w i * x i :=
    sum_pos (fun i _ => mul_pos (hwp i) (hxp i)) univ_nonempty
  have he := (sum_mulVec_of_leftEigen A.val w x A.transpose.perronRoot hwl).symm.trans
    (sum_mulVec_of_rightEigen A.val w x A.perronRoot hx)
  have hroot := mul_right_cancel₀ hpair.ne' he
  rw [hroot] at hwl
  exact ⟨w, hws, hwp, hwl⟩

/-- A positive test vector with row ratios bounded by `lo` and `hi`
certifies the same two bounds for the Perron root. -/
theorem perronRoot_bounds (A : EntrywisePositiveKernel ι) (x : ι → ℝ) (hx : ∀ i, 0 < x i)
    (lo hi : ℝ) (hlo : ∀ i, lo * x i ≤ (A.val *ᵥ x) i)
    (hhi : ∀ i, (A.val *ᵥ x) i ≤ hi * x i) :
    lo ≤ A.perronRoot ∧ A.perronRoot ≤ hi := by
  obtain ⟨w, _, hwp, hw⟩ := exists_positive_leftEigen A
  have hpair : 0 < ∑ i, w i * x i := sum_pos (fun i _ => mul_pos (hwp i) (hx i)) univ_nonempty
  have h := sum_mulVec_of_leftEigen A.val w x A.perronRoot hw
  constructor
  · apply (mul_le_mul_iff_of_pos_right hpair).mp
    rw [← h, mul_sum]
    exact sum_le_sum fun i _ => by
      rw [mul_left_comm lo (w i) (x i)]
      exact mul_le_mul_of_nonneg_left (hlo i) (hwp i).le
  · apply (mul_le_mul_iff_of_pos_right hpair).mp
    rw [← h, mul_sum]
    exact sum_le_sum fun i _ => by
      rw [mul_left_comm hi (w i) (x i)]
      exact mul_le_mul_of_nonneg_left (hhi i) (hwp i).le

/-- A strictly positive eigenvector determines its eigenvalue uniquely. -/
theorem eq_perronRoot_of_positive_eigenvector (A : EntrywisePositiveKernel ι) (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) (λ : ℝ) (h : A.val *ᵥ x = λ • x) : λ = A.perronRoot := by
  have he (i : ι) : (A.val *ᵥ x) i = λ * x i := congrFun h i
  obtain ⟨hlo, hhi⟩ := perronRoot_bounds A x hx λ λ (fun i => (he i).ge) (fun i => (he i).le)
  exact le_antisymm hlo hhi

/-- No eigenvalue of the complexified kernel has modulus above the Perron
root. A maximal coordinate in the weighted sup norm gives the estimate. -/
theorem norm_eigenvalue_le_perronRoot (A : EntrywisePositiveKernel ι) (z : ι → ℂ) (λ : ℂ)
    (hz : z ≠ 0) (he : A.val.map (fun a : ℝ => (a : ℂ)) *ᵥ z = λ • z) :
    ‖λ‖ ≤ A.perronRoot := by
  obtain ⟨_, x, _, hxp, hx⟩ := perronRoot_spec A
  let f (i : ι) := ‖z i‖ / x i
  let M := univ.sup' univ_nonempty f
  obtain ⟨i, _, hi⟩ := exists_mem_eq_sup' univ_nonempty f
  change M = ‖z i‖ / x i at hi
  have hle (j : ι) : ‖z j‖ / x j ≤ M := le_sup' f (mem_univ j)
  have hM : 0 < M := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hz
    exact (div_pos (norm_pos_iff.mpr hj) (hxp j)).trans_le (hle j)
  have hw (j : ι) : ‖z j‖ ≤ M * x j := (div_le_iff₀ (hxp j)).mp (hle j)
  have hi' : ‖z i‖ = M * x i := (div_eq_iff (hxp i).ne').mp hi.symm
  have he' : (A.val.map (fun a : ℝ => (a : ℂ)) *ᵥ z) i = λ * z i := congrFun he i
  apply (mul_le_mul_iff_of_pos_right (mul_pos hM (hxp i))).mp
  calc
    ‖λ‖ * (M * x i) = ‖λ * z i‖ := by rw [norm_mul, hi']
    _ = ‖(A.val.map (fun a : ℝ => (a : ℂ)) *ᵥ z) i‖ := by rw [he']
    _ ≤ ∑ j, A.val i j * ‖z j‖ := by
      change ‖∑ j, (A.val i j : ℂ) * z j‖ ≤ _
      refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (A.property i j)]
    _ ≤ M * (A.val *ᵥ x) i := by
      change _ ≤ M * ∑ j, A.val i j * x j
      rw [mul_sum]
      exact sum_le_sum fun j _ => by
        rw [mul_left_comm M (A.val i j) (x j)]
        exact mul_le_mul_of_nonneg_left (hw j) (A.property i j).le
    _ = A.perronRoot * (M * x i) := by
      rw [hx]
      exact mul_left_comm _ _ _

/-- The change in Perron root is the normalized weighted residual of the
smaller kernel's right eigenvector after applying a diagonal change of coordinates. -/
theorem exists_perronGap_pairing (A B : EntrywisePositiveKernel ι) :
    ∃ x ∈ stdSimplex ℝ ι, ∃ w ∈ stdSimplex ℝ ι, (∀ i, 0 < x i) ∧ (∀ i, 0 < w i) ∧
      ∀ d : ι → ℝ, (B.perronRoot - A.perronRoot) * (∑ i, w i * (d i * x i)) =
        ∑ i, ∑ j, w i * ((B.val i j * d j - d i * A.val i j) * x j) := by
  obtain ⟨_, x, hxs, hxp, hx⟩ := perronRoot_spec A
  obtain ⟨w, hws, hwp, hw⟩ := exists_positive_leftEigen B
  refine ⟨x, hxs, w, hws, hxp, hwp, fun d => ?_⟩
  let y : ι → ℝ := fun i => d i * x i
  have hb := sum_mulVec_of_leftEigen B.val w y B.perronRoot hw
  have ha := sum_mulVec_of_rightEigen A.val (fun i => w i * d i) x A.perronRoot hx
  have hs : ∑ i, w i * d i * x i = ∑ i, w i * y i :=
    sum_congr rfl fun i _ => mul_assoc _ _ _
  rw [hs] at ha
  rw [sub_mul, ← hb, ← ha, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  change w i * (∑ j, B.val i j * (d j * x j)) - (w i * d i) * (∑ j, A.val i j * x j) = _
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by ring

/-- Entrywise comparison after positive diagonal reweighting is strict as
soon as any one of the comparisons is strict. -/
theorem perronRoot_lt_of_weighted_le (A B : EntrywisePositiveKernel ι) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (hle : ∀ i j, d i * A.val i j ≤ B.val i j * d j)
    (hlt : ∃ i j, d i * A.val i j < B.val i j * d j) : A.perronRoot < B.perronRoot := by
  obtain ⟨x, _, w, _, hx, hw, h⟩ := exists_perronGap_pairing A B
  have hpair : 0 < ∑ i, w i * (d i * x i) :=
    sum_pos (fun i _ => mul_pos (hw i) (mul_pos (hd i) (hx i))) univ_nonempty
  have hnonneg (i j : ι) : 0 ≤ w i * ((B.val i j * d j - d i * A.val i j) * x j) :=
    mul_nonneg (hw i).le (mul_nonneg (sub_nonneg.mpr (hle i j)) (hx j).le)
  obtain ⟨i, j, hij⟩ := hlt
  have hpos := mul_pos (hw i) (mul_pos (sub_pos.mpr hij) (hx j))
  have hsum : 0 < ∑ i, ∑ j, w i * ((B.val i j * d j - d i * A.val i j) * x j) :=
    sum_pos' (fun k _ => sum_nonneg fun l _ => hnonneg k l)
      ⟨i, mem_univ i, sum_pos' (fun l _ => hnonneg i l) ⟨j, mem_univ j, hpos⟩⟩
  rw [← h d] at hsum
  exact sub_pos.mp (pos_of_mul_pos_left hsum hpair.le)

/-- A rank-one lower bound for the reweighted residual gives a factored
lower bound for the Perron gap. -/
theorem exists_perronGap_ge_rankOne (A B : EntrywisePositiveKernel ι) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) :
    ∃ x ∈ stdSimplex ℝ ι, ∃ w ∈ stdSimplex ℝ ι, (∀ i, 0 < x i) ∧ (∀ i, 0 < w i) ∧
      ∀ u v : ι → ℝ, (∀ i j, u i * v j ≤ B.val i j * d j - d i * A.val i j) →
        ((∑ i, w i * u i) * (∑ j, v j * x j)) / (∑ i, w i * (d i * x i)) ≤
          B.perronRoot - A.perronRoot := by
  obtain ⟨x, hxs, w, hws, hx, hw, h⟩ := exists_perronGap_pairing A B
  refine ⟨x, hxs, w, hws, hx, hw, fun u v huv => ?_⟩
  have hpair : 0 < ∑ i, w i * (d i * x i) :=
    sum_pos (fun i _ => mul_pos (hw i) (mul_pos (hd i) (hx i))) univ_nonempty
  apply (div_le_iff₀ hpair).mpr
  rw [h d, sum_mul]
  apply sum_le_sum
  intro i _
  rw [mul_sum]
  apply sum_le_sum
  intro j _
  rw [show w i * u i * (v j * x j) = w i * ((u i * v j) * x j) by ring]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (huv i j) (hx j).le) (hw i).le

/-- Entrywise continuity of a finite positive family implies continuity of
its Perron root. The right eigenvector at the base point tests nearby kernels. -/
theorem continuous_perronRoot_family {X : Type*} [TopologicalSpace X] (K : X → EntrywisePositiveKernel ι)
    (hc : ∀ i j, Continuous (fun t => (K t).val i j)) :
    Continuous fun t => (K t).perronRoot := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨_, x, _, hxp, hx⟩ := perronRoot_spec (K t)
  let row (i : ι) (u : X) := ((K u).val *ᵥ x) i / x i
  have hrow (i : ι) : Continuous (row i) := by
    change Continuous (fun u : X => (∑ j, (K u).val i j * x j) / x i)
    exact (continuous_finsetSum _ fun j _ => (hc i j).mul continuous_const).div_const _
  have hbase (i : ι) : row i t = (K t).perronRoot := by
    change ((K t).val *ᵥ x) i / x i = _
    rw [hx]
    change (K t).perronRoot * x i / x i = _
    exact mul_div_cancel_right₀ _ (hxp i).ne'
  change Tendsto (fun u => (K u).perronRoot) (𝓝 t) (𝓝 (K t).perronRoot)
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  let lo := (K t).perronRoot - ε / 2
  let hi := (K t).perronRoot + ε / 2
  have hη := half_pos hε
  have htest (i : ι) : ∀ᶠ u in 𝓝 t, lo < row i u ∧ row i u < hi := by
    have ht := (hrow i).continuousAt (x := t).tendsto
    rw [hbase i] at ht
    exact (ht.eventually (eventually_gt_nhds (sub_lt_self _ hη))).and
      (ht.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hη)))
  filter_upwards [eventually_all.2 htest] with u hu
  obtain ⟨hl, hr⟩ := perronRoot_bounds (K u) x hxp lo hi
    (fun i => ((lt_div_iff₀ (hxp i)).mp (hu i).1).le)
    (fun i => ((div_lt_iff₀ (hxp i)).mp (hu i).2).le)
  rw [Real.dist_eq, abs_lt]
  dsimp only [lo, hi] at hl hr
  exact ⟨by linarith only [hl, hε], by linarith only [hr, hε]⟩

/-- A continuous family with strict entrywise progress crosses level one
exactly once on every bracket containing that level. -/
theorem existsUnique_perronRoot_eq_one (K : ℝ → EntrywisePositiveKernel ι)
    (hc : ∀ i j, Continuous (fun t => (K t).val i j)) {a b : ℝ} (hab : a ≤ b)
    (hmono : ∀ x y, x < y → (∀ i j, (K x).val i j ≤ (K y).val i j) ∧
      ∃ i j, (K x).val i j < (K y).val i j)
    (ha : (K a).perronRoot ≤ 1) (hb : 1 ≤ (K b).perronRoot) :
    ∃! t, t ∈ Icc a b ∧ (K t).perronRoot = 1 := by
  have hp := continuous_perronRoot_family K hc
  have hstrict : StrictMono fun t => (K t).perronRoot := by
    intro x y hxy
    obtain ⟨hle, hlt⟩ := hmono x y hxy
    refine perronRoot_lt_of_weighted_le (K x) (K y) (fun _ => 1) (fun _ => zero_lt_one) ?_ ?_
    · simpa only [one_mul, mul_one] using hle
    · simpa only [one_mul, mul_one] using hlt
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc hab hp.continuousOn ⟨ha, hb⟩
  exact ⟨t, ⟨ht, he⟩, fun u hu => hstrict.injective (hu.2.trans he.symm)⟩

#print axioms exists_positive_eigenpair
#print axioms exists_positive_leftEigen
#print axioms perronRoot_bounds
#print axioms eq_perronRoot_of_positive_eigenvector
#print axioms norm_eigenvalue_le_perronRoot
#print axioms exists_perronGap_pairing
#print axioms perronRoot_lt_of_weighted_le
#print axioms exists_perronGap_ge_rankOne
#print axioms continuous_perronRoot_family
#print axioms existsUnique_perronRoot_eq_one

end EntrywisePositiveKernel

end

end GaloisForLFunctions.HTGeometry
