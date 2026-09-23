import GaloisForLFunctions.RHTower.CCMLocalRatioAnomaly
import Mathlib.Algebra.Order.Chebyshev

/-!
# The higher-subset covariance carrier of a finite local-ratio product

The covariance anomaly of a finite family of multipliers is the coefficient-one readout of a graded
feature map indexed by the subsets of at least two places:

```text
a_v(t) = u_v(t) - 1,   V_V(t)_I = prod_(v in I) a_v(t),   C_V(t) = sum_(|I| >= 2) V_V(t)_I.
```

This module proves the algebraic content of that lift.

* `covIndex`, `covFeature`, `covarianceAnomaly_eq_readout` — equations `(1)`–`(5)`.
* `covKernel`, `covKernel_quadratic_form`, `covKernel_quadratic_form_nonneg` — equations `(6)`–`(7)`:
  every quadratic form of the Gram kernel is a sum of squared norms, so the lift is genuinely positive
  even though the scalar readout is signed.
* `covIndex_subset`, `sum_covIndex_extend` — equation `(8)`: the carriers form a directed system and
  the old coordinates are literally unchanged, because `covFeature` does not mention the ambient set.
* `sum_covIndex_eq_sum_grades`, `sum_powersetCard_two`, `tendsto_covFeature_div_pow`,
  `tendsto_covFeature_div_sq_of_three_le`, `tendsto_covFeature_div_sq_of_card_two` — equations
  `(9)`–`(12)`: each degree-`k` coordinate vanishes to order `k` at the seam, so grades `k >= 3`
  contribute nothing to the quadratic jet and the degree-two grade carries all of it.
* `card_covIndex`, `card_covGradeTwo`, `norm_readout_le`, `norm_readout_ones` — equations
  `(14)`–`(16)`: the carrier has dimension `2^m - m - 1`, its degree-two part has dimension
  `binom(m,2)`, and the coefficient-one readout has norm exactly `sqrt(2^m - m - 1)`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Finset Filter Topology

variable {ι : Type*} [DecidableEq ι]

/-! ## The feature carrier and the readout -/

/-- The index set of the covariance carrier: subsets of at least two places. -/
def covIndex (V : Finset ι) : Finset (Finset ι) := V.powerset.filter fun I => 2 ≤ I.card

/-- The subset feature coordinate `V_V(t)_I = prod_(v in I) a_v(t)`.  It does not mention the ambient
set of places, which is exactly why the carriers form a directed system. -/
def covFeature (u : ι → ℝ → ℂ) (I : Finset ι) (t : ℝ) : ℂ := ∏ v ∈ I, (u v t - 1)

/-- **Equations (4)–(5).**  The covariance anomaly is the coefficient-one readout of the feature
vector. -/
theorem covarianceAnomaly_eq_readout (V : Finset ι) (u : ι → ℝ → ℂ) (t : ℝ) :
    covarianceAnomaly V u t = ∑ I ∈ covIndex V, covFeature u I t :=
  covarianceAnomaly_eq_sum_powerset V u t

/-- The low-degree complement of the carrier: the empty set and the singletons. -/
theorem powerset_filter_card_le_one (V : Finset ι) :
    (V.powerset.filter fun I => I.card ≤ 1)
      = insert (∅ : Finset ι) (V.image fun v => ({v} : Finset ι)) := by
  ext I
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨hsub, hcard⟩
    rcases Nat.lt_or_ge I.card 1 with h | h
    · exact Or.inl (Finset.card_eq_zero.mp (by omega))
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (show I.card = 1 from le_antisymm hcard h)
      exact Or.inr ⟨v, hsub (by rw [hv]; exact Finset.mem_singleton_self v), hv.symm⟩
  · rintro (rfl | ⟨v, hv, rfl⟩)
    · exact ⟨Finset.empty_subset V, by simp⟩
    · exact ⟨Finset.singleton_subset_iff.mpr hv, by simp⟩

theorem empty_notMem_image_singleton (V : Finset ι) :
    (∅ : Finset ι) ∉ V.image fun v => ({v} : Finset ι) := by
  simp only [Finset.mem_image, not_exists]
  intro v hv
  exact (Finset.singleton_ne_empty v) hv.2

/-! ## The positive Gram kernel -/

/-- The Gram kernel of the feature map, `K(x, y) = <V(x), V(y)>`. -/
def covKernel (V : Finset ι) (u : ι → ℝ → ℂ) (x y : ℝ) : ℂ :=
  ∑ I ∈ covIndex V, (starRingEnd ℂ) (covFeature u I x) * covFeature u I y

omit [DecidableEq ι] in
/-- **Equation (7).**  Every quadratic form of the Gram kernel is a sum of squared norms. -/
theorem covKernel_quadratic_form {κ : Type*} (V : Finset ι) (u : ι → ℝ → ℂ) (J : Finset κ)
    (c : κ → ℂ) (t : κ → ℝ) :
    (∑ j ∈ J, ∑ k ∈ J, (starRingEnd ℂ) (c j) * c k * covKernel V u (t j) (t k))
      = (((∑ I ∈ covIndex V, ‖∑ j ∈ J, c j * covFeature u I (t j)‖ ^ (2 : ℕ) : ℝ)) : ℂ) := by
  calc (∑ j ∈ J, ∑ k ∈ J, (starRingEnd ℂ) (c j) * c k * covKernel V u (t j) (t k))
      = ∑ j ∈ J, ∑ k ∈ J, ∑ I ∈ covIndex V,
          (starRingEnd ℂ) (c j * covFeature u I (t j)) * (c k * covFeature u I (t k)) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [covKernel, Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [map_mul]
        ring
    _ = ∑ j ∈ J, ∑ I ∈ covIndex V, ∑ k ∈ J,
          (starRingEnd ℂ) (c j * covFeature u I (t j)) * (c k * covFeature u I (t k)) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ I ∈ covIndex V, ∑ j ∈ J, ∑ k ∈ J,
          (starRingEnd ℂ) (c j * covFeature u I (t j)) * (c k * covFeature u I (t k)) :=
        Finset.sum_comm
    _ = ∑ I ∈ covIndex V, (((‖∑ j ∈ J, c j * covFeature u I (t j)‖ ^ (2 : ℕ) : ℝ)) : ℂ) := by
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [← Finset.sum_mul_sum, ← map_sum, RCLike.conj_mul]
        norm_num
    _ = (((∑ I ∈ covIndex V, ‖∑ j ∈ J, c j * covFeature u I (t j)‖ ^ (2 : ℕ) : ℝ)) : ℂ) := by
        rw [Complex.ofReal_sum]

omit [DecidableEq ι] in
/-- **Equation (7), positivity.**  The Gram kernel is positive semidefinite. -/
theorem covKernel_quadratic_form_nonneg {κ : Type*} (V : Finset ι) (u : ι → ℝ → ℂ) (J : Finset κ)
    (c : κ → ℂ) (t : κ → ℝ) :
    0 ≤ (∑ j ∈ J, ∑ k ∈ J, (starRingEnd ℂ) (c j) * c k * covKernel V u (t j) (t k)).re := by
  rw [covKernel_quadratic_form, Complex.ofReal_re]
  exact Finset.sum_nonneg fun I _ => sq_nonneg _

/-! ## The directed system -/

omit [DecidableEq ι] in
/-- **Equation (8).**  Enlarging the set of places only adds coordinates. -/
theorem covIndex_subset {V W : Finset ι} (h : V ⊆ W) : covIndex V ⊆ covIndex W := by
  intro I hI
  rw [covIndex, Finset.mem_filter, Finset.mem_powerset] at hI ⊢
  exact ⟨hI.1.trans h, hI.2⟩

/-- **Equation (8), isometry.**  Extension by zero on the new coordinates preserves every sum, so the
embedding of carriers is isometric. -/
theorem sum_covIndex_extend {V W : Finset ι} (h : V ⊆ W) (f : Finset ι → ℝ) :
    ∑ I ∈ covIndex V, f I
      = ∑ I ∈ covIndex W, if I ∈ covIndex V then f I else 0 := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (covIndex_subset h)]

/-! ## The grading by subset size -/

/-- The degree-`k` grade of the carrier. -/
def covGrade (V : Finset ι) (k : ℕ) : Finset (Finset ι) := V.powersetCard k

/-- **Equation (9).**  The carrier is the direct sum of its grades of degree at least two. -/
theorem sum_covIndex_eq_sum_grades (V : Finset ι) (f : Finset ι → ℂ) :
    ∑ I ∈ covIndex V, f I
      = ∑ k ∈ Finset.Ico 2 (V.card + 1), ∑ I ∈ covGrade V k, f I := by
  rcases Nat.eq_zero_or_pos V.card with h0 | hpos
  · have hV : V = ∅ := Finset.card_eq_zero.mp h0
    subst hV
    simp [covIndex, Finset.filter_singleton]
  -- the powerset splits both ways
  have hsplit : (∑ I ∈ V.powerset, f I)
      = (∑ I ∈ covIndex V, f I) + ∑ I ∈ V.powerset.filter fun I => I.card ≤ 1, f I := by
    have hfil : (V.powerset.filter fun I => ¬ I.card ≤ 1) = covIndex V := by
      rw [covIndex]
      ext I
      simp only [Finset.mem_filter, not_le]
      exact and_congr_right fun _ => by omega
    rw [← Finset.sum_filter_add_sum_filter_not V.powerset fun I => I.card ≤ 1, hfil]
    ring
  have hlow : (∑ I ∈ V.powerset.filter fun I => I.card ≤ 1, f I)
      = f ∅ + ∑ v ∈ V, f {v} := by
    rw [powerset_filter_card_le_one, Finset.sum_insert (empty_notMem_image_singleton V),
      Finset.sum_image fun v _ w _ hvw => Finset.singleton_injective hvw]
  have hgrade : (∑ I ∈ V.powerset, f I)
      = ∑ k ∈ Finset.range (V.card + 1), ∑ I ∈ covGrade V k, f I := Finset.sum_powerset V f
  have hzero : (∑ I ∈ covGrade V 0, f I) = f ∅ := by
    rw [covGrade, Finset.powersetCard_zero, Finset.sum_singleton]
  have hone : (∑ I ∈ covGrade V 1, f I) = ∑ v ∈ V, f {v} := by
    rw [covGrade, Finset.powersetCard_one, Finset.sum_map]
    rfl
  have hrange : (∑ k ∈ Finset.range (V.card + 1), ∑ I ∈ covGrade V k, f I)
      = ((∑ I ∈ covGrade V 0, f I) + ∑ I ∈ covGrade V 1, f I)
        + ∑ k ∈ Finset.Ico 2 (V.card + 1), ∑ I ∈ covGrade V k, f I := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun k => ∑ I ∈ covGrade V k, f I)
        (by omega : 0 ≤ 2) (by omega : 2 ≤ V.card + 1)]
    congr 1
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_Ico_succ_top (by omega),
      show (1 : ℕ) = 0 + 1 from rfl, Finset.sum_Ico_succ_top (by omega)]
    simp
  rw [hgrade, hrange, hzero, hone] at hsplit
  rw [hlow] at hsplit
  linear_combination -hsplit

omit [DecidableEq ι] in
/-- **Equation (16).**  The degree-two grade of the carrier. -/
theorem card_covGradeTwo (V : Finset ι) : (covGrade V 2).card = V.card.choose 2 :=
  Finset.card_powersetCard 2 V

/-- The degree-two grade sum, in closed form. -/
theorem sum_powersetCard_two (V : Finset ι) (c : ι → ℂ) :
    (∑ I ∈ covGrade V 2, ∏ v ∈ I, c v)
      = ((∑ v ∈ V, c v) ^ (2 : ℕ) - ∑ v ∈ V, c v ^ (2 : ℕ)) / 2 := by
  classical
  induction V using Finset.induction_on with
  | empty =>
    have h : (∅ : Finset ι).powersetCard 2 = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun I hI => ?_
      rw [Finset.mem_powersetCard] at hI
      have hIe := Finset.subset_empty.mp hI.1
      rw [hIe] at hI
      simp at hI
    simp [covGrade, h]
  | insert x V hx ih =>
    have hpc : covGrade (insert x V) 2 = covGrade V 2 ∪ (covGrade V 1).image (insert x) := by
      rw [covGrade, covGrade, covGrade, show (2 : ℕ) = Nat.succ 1 from rfl,
        Finset.powersetCard_succ_insert hx]
    have hdisj : Disjoint (covGrade V 2) ((covGrade V 1).image (insert x)) := by
      refine Finset.disjoint_left.mpr fun I hI hI' => ?_
      rw [covGrade, Finset.mem_powersetCard] at hI
      simp only [Finset.mem_image, covGrade, Finset.mem_powersetCard] at hI'
      obtain ⟨K, hK, rfl⟩ := hI'
      exact hx (hI.1 (Finset.mem_insert_self x K))
    have hinj : ∀ K ∈ covGrade V 1, ∀ L ∈ covGrade V 1, insert x K = insert x L → K = L := by
      intro K hK L hL hKL
      rw [covGrade, Finset.mem_powersetCard] at hK hL
      have hxK : x ∉ K := fun h => hx (hK.1 h)
      have hxL : x ∉ L := fun h => hx (hL.1 h)
      have h1 : (insert x K).erase x = K := Finset.erase_insert hxK
      have h2 : (insert x L).erase x = L := Finset.erase_insert hxL
      rw [← h1, ← h2, hKL]
    have himg : (∑ I ∈ (covGrade V 1).image (insert x), ∏ v ∈ I, c v)
        = c x * ∑ v ∈ V, c v := by
      rw [Finset.sum_image hinj, covGrade, Finset.powersetCard_one, Finset.sum_map,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hvx : x ∉ ({v} : Finset ι) := by
        simp only [Finset.mem_singleton]
        intro h
        exact hx (by rw [h]; exact hv)
      rw [Function.Embedding.coeFn_mk, Finset.prod_insert hvx, Finset.prod_singleton]
    rw [hpc, Finset.sum_union hdisj, ih, himg, Finset.sum_insert hx, Finset.sum_insert hx]
    ring

/-! ## Order of vanishing of each grade -/

omit [DecidableEq ι] in
/-- Each feature coordinate vanishes to order `|I|` at the seam. -/
theorem tendsto_covFeature_div_pow {u : ι → ℝ → ℂ} {c : ι → ℂ}
    (hu : ∀ v, u v 0 = 1) (hd : ∀ v, HasDerivAt (u v) (c v) 0) (I : Finset ι) :
    Tendsto (fun t : ℝ => covFeature u I t / (t : ℂ) ^ I.card) (𝓝[≠] (0 : ℝ))
      (𝓝 (∏ v ∈ I, c v)) := by
  have h : Tendsto (fun t : ℝ => ∏ v ∈ I, ((u v t - 1) / (t : ℂ))) (𝓝[≠] (0 : ℝ))
      (𝓝 (∏ v ∈ I, c v)) :=
    tendsto_finsetProd I fun v _ => tendsto_multiplier_sub_one_div (hu v) (hd v)
  refine h.congr fun t => ?_
  rw [covFeature, Finset.prod_div_distrib, Finset.prod_const]

omit [DecidableEq ι] in
/-- **Equations (10)–(11).**  A degree-two coordinate has quadratic jet `c_v c_w`. -/
theorem tendsto_covFeature_div_sq_of_card_two {u : ι → ℝ → ℂ} {c : ι → ℂ}
    (hu : ∀ v, u v 0 = 1) (hd : ∀ v, HasDerivAt (u v) (c v) 0) {I : Finset ι} (hI : I.card = 2) :
    Tendsto (fun t : ℝ => covFeature u I t / (t : ℂ) ^ (2 : ℕ)) (𝓝[≠] (0 : ℝ)) (𝓝 (∏ v ∈ I, c v)) := by
  have h := tendsto_covFeature_div_pow hu hd I
  rw [hI] at h
  exact h

omit [DecidableEq ι] in
/-- **Equation (10) for the higher grades.**  A coordinate of degree at least three has vanishing
quadratic jet: the higher grades are successively more diagonal-regular. -/
theorem tendsto_covFeature_div_sq_of_three_le {u : ι → ℝ → ℂ} {c : ι → ℂ}
    (hu : ∀ v, u v 0 = 1) (hd : ∀ v, HasDerivAt (u v) (c v) 0) {I : Finset ι} (hI : 3 ≤ I.card) :
    Tendsto (fun t : ℝ => covFeature u I t / (t : ℂ) ^ (2 : ℕ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hbase := tendsto_covFeature_div_pow hu hd I
  have hpow : Tendsto (fun t : ℝ => ((t : ℂ)) ^ (I.card - 2)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hcont : Tendsto (fun t : ℝ => ((t : ℂ))) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => ((t : ℂ))) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    have hne : I.card - 2 ≠ 0 := by omega
    simpa [zero_pow hne] using hcont.pow (I.card - 2)
  have hmul := hbase.mul hpow
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htne : ((t : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simpa using ht)
  have hpne : ((t : ℂ)) ^ (I.card - 2) ≠ 0 := pow_ne_zero _ htne
  have hsplit : ((t : ℂ)) ^ I.card = ((t : ℂ)) ^ (I.card - 2) * ((t : ℂ)) ^ (2 : ℕ) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  field_simp

/-- **Equation (12).**  The whole quadratic jet of the anomaly is the degree-two grade sum: the
cofinal curvature charge lives entirely in `H^(2)`. -/
theorem tendsto_covarianceAnomaly_div_sq_eq_gradeTwo {u : ι → ℝ → ℂ} {c : ι → ℂ}
    (hu : ∀ v, u v 0 = 1) (hd : ∀ v, HasDerivAt (u v) (c v) 0) (V : Finset ι) :
    Tendsto (fun t : ℝ => covarianceAnomaly V u t / (t : ℂ) ^ (2 : ℕ)) (𝓝[≠] (0 : ℝ))
      (𝓝 (∑ I ∈ covGrade V 2, ∏ v ∈ I, c v)) := by
  rw [sum_powersetCard_two V c]
  exact tendsto_covarianceAnomaly_div_sq hu hd V

/-! ## The exact cofinal resource -/

/-- **Equation (14).**  The carrier has dimension `2^m - m - 1`. -/
theorem card_covIndex (V : Finset ι) : (covIndex V).card = 2 ^ V.card - V.card - 1 := by
  have hlow : (V.powerset.filter fun I => I.card ≤ 1).card = V.card + 1 := by
    rw [powerset_filter_card_le_one, Finset.card_insert_of_notMem (empty_notMem_image_singleton V),
      Finset.card_image_of_injective _ Finset.singleton_injective]
  have hfil : (V.powerset.filter fun I => ¬ I.card ≤ 1) = covIndex V := by
    rw [covIndex]
    ext I
    simp only [Finset.mem_filter, not_le]
    exact and_congr_right fun _ => by omega
  have htot := Finset.card_filter_add_card_filter_not (s := V.powerset) fun I => I.card ≤ 1
  rw [hlow, hfil, Finset.card_powerset] at htot
  omega

omit [DecidableEq ι] in
/-- **Equation (15), upper bound.**  The coefficient-one readout is bounded by
`sqrt(dim)` times the carrier norm. -/
theorem norm_readout_le (V : Finset ι) (x : Finset ι → ℂ) :
    ‖∑ I ∈ covIndex V, x I‖
      ≤ Real.sqrt ((covIndex V).card) * Real.sqrt (∑ I ∈ covIndex V, ‖x I‖ ^ (2 : ℕ)) := by
  have h1 : ‖∑ I ∈ covIndex V, x I‖ ≤ ∑ I ∈ covIndex V, ‖x I‖ := norm_sum_le _ _
  have h2 : (∑ I ∈ covIndex V, ‖x I‖) ^ (2 : ℕ)
      ≤ ((covIndex V).card : ℝ) * ∑ I ∈ covIndex V, ‖x I‖ ^ (2 : ℕ) := sq_sum_le_card_mul_sum_sq
  have hnn : 0 ≤ ∑ I ∈ covIndex V, ‖x I‖ := Finset.sum_nonneg fun I _ => norm_nonneg _
  have hsq : Real.sqrt (((covIndex V).card : ℝ) * ∑ I ∈ covIndex V, ‖x I‖ ^ (2 : ℕ))
      = Real.sqrt ((covIndex V).card) * Real.sqrt (∑ I ∈ covIndex V, ‖x I‖ ^ (2 : ℕ)) :=
    Real.sqrt_mul (by positivity) _
  calc ‖∑ I ∈ covIndex V, x I‖ ≤ ∑ I ∈ covIndex V, ‖x I‖ := h1
    _ = Real.sqrt ((∑ I ∈ covIndex V, ‖x I‖) ^ (2 : ℕ)) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (((covIndex V).card : ℝ) * ∑ I ∈ covIndex V, ‖x I‖ ^ (2 : ℕ)) :=
        Real.sqrt_le_sqrt h2
    _ = Real.sqrt ((covIndex V).card) * Real.sqrt (∑ I ∈ covIndex V, ‖x I‖ ^ (2 : ℕ)) := hsq

omit [DecidableEq ι] in
/-- **Equation (15), sharpness.**  The bound is attained at the all-ones vector, so the readout norm
is exactly `sqrt(2^m - m - 1)`. -/
theorem norm_readout_ones (V : Finset ι) :
    ‖∑ _I ∈ covIndex V, (1 : ℂ)‖
      = Real.sqrt ((covIndex V).card) * Real.sqrt (∑ _I ∈ covIndex V, ‖(1 : ℂ)‖ ^ (2 : ℕ)) := by
  have hcard : (0 : ℝ) ≤ ((covIndex V).card : ℝ) := Nat.cast_nonneg _
  rw [Finset.sum_const, Finset.sum_const]
  simp only [nsmul_eq_mul, mul_one, norm_one, one_pow]
  rw [Complex.norm_natCast, ← Real.sqrt_mul_self hcard]
  norm_num

/-! ## The Hardy corner algebra -/

section Hardy

variable {R : Type*} [Ring R] {A : Type*} [CommRing A]

/-- The lower Hardy corner of a symbol, `H(a) = Q M_a P` with `Q = 1 - P`. -/
def hardyCorner (M : A →+* R) (p : R) (a : A) : R := (1 - p) * M a * p

theorem sub_self_mul_sub_self {p : R} (hp : p * p = p) : (1 - p) * (1 - p) = 1 - p := by
  have h : (1 - p) * (1 - p) = 1 - p - p + p * p := by noncomm_ring
  rw [h, hp]
  noncomm_ring

/-- **Equation (19).**  The exact Hardy product formula.  Only idempotence of the projection is
used; no analytic input at all. -/
theorem hardyCorner_mul (M : A →+* R) {p : R} (hp : p * p = p) (a b : A) :
    hardyCorner M p (a * b)
      = hardyCorner M p a * (p * M b * p)
        + ((1 - p) * M a * (1 - p)) * hardyCorner M p b := by
  have h1 := sub_self_mul_sub_self hp
  rw [hardyCorner, hardyCorner, hardyCorner, map_mul]
  have e1 : ((1 - p) * M a * p) * (p * M b * p) = (1 - p) * M a * (p * p) * M b * p := by
    noncomm_ring
  have e2 : ((1 - p) * M a * (1 - p)) * ((1 - p) * M b * p)
      = (1 - p) * M a * ((1 - p) * (1 - p)) * M b * p := by noncomm_ring
  rw [e1, e2, hp, h1]
  noncomm_ring

/-- **The compact-corner algebra.**  If the corners of two symbols lie in a two-sided ideal, so does
the corner of their product.  The card's compactness statement is this with the ideal of compact
operators. -/
theorem hardyCorner_mul_mem (M : A →+* R) {p : R} (hp : p * p = p) {J : Set R}
    (hadd : ∀ x ∈ J, ∀ y ∈ J, x + y ∈ J)
    (hleft : ∀ r : R, ∀ x ∈ J, r * x ∈ J) (hright : ∀ x ∈ J, ∀ r : R, x * r ∈ J)
    {a b : A} (ha : hardyCorner M p a ∈ J) (hb : hardyCorner M p b ∈ J) :
    hardyCorner M p (a * b) ∈ J := by
  rw [hardyCorner_mul M hp a b]
  exact hadd _ (hright _ ha _) _ (hleft _ _ hb)

/-- **Equation (22).**  Every nonempty subset product has its corner in the ideal. -/
theorem hardyCorner_prod_mem {ι' : Type*} [DecidableEq ι'] (M : A →+* R) {p : R} (hp : p * p = p)
    {J : Set R} (hadd : ∀ x ∈ J, ∀ y ∈ J, x + y ∈ J)
    (hleft : ∀ r : R, ∀ x ∈ J, r * x ∈ J) (hright : ∀ x ∈ J, ∀ r : R, x * r ∈ J)
    {a : ι' → A} (h : ∀ v, hardyCorner M p (a v) ∈ J) {I : Finset ι'} (hI : I.Nonempty) :
    hardyCorner M p (∏ v ∈ I, a v) ∈ J := by
  induction hI using Finset.Nonempty.cons_induction with
  | singleton v => rw [Finset.prod_singleton]; exact h v
  | cons v s hv hs ih =>
    rw [Finset.prod_cons]
    exact hardyCorner_mul_mem M hp hadd hleft hright (h v) ih

/-- **Equation (25).**  The corner is additive in the symbol, so the scalar readout of the column
operator is the corner of the readout symbol. -/
theorem hardyCorner_sum (M : A →+* R) (p : R) {κ : Type*} (S : Finset κ) (f : κ → A) :
    hardyCorner M p (∑ i ∈ S, f i) = ∑ i ∈ S, hardyCorner M p (f i) := by
  rw [hardyCorner, map_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [hardyCorner]

end Hardy

end GaloisForLFunctions.RHTower

end
