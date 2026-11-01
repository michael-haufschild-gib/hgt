import GaloisForLFunctions.AdelicKreinGeometry.Haar.PositiveSlopeSplit
import GaloisForLFunctions.AdelicKreinGeometry.Haar.SubgroupOrbits
import GaloisForLFunctions.AdelicKreinGeometry.Haar.SubgroupIndexPreservation
import GaloisForLFunctions.BiarithmeticGeometry.Affine.SubgroupFactorialOrders

/-!
# The positive part of a proper subgroup successor

Let `H < ℚ` be a proper additive subgroup containing `1`, and let `k` be an integer-invariant
Hermitian kernel on `Aff(ℚ)` of finite negative index whose translation reading is the indicator
of `H`. The factorial cyclic moving forms of `k` are monotone, and each column has moving norm at
most one because its fixed projection has norm `1/ord_H(b/slope)` (reciprocal quotient order).
Their limit is an affine-invariant nonnegative form. Its coefficient `p` is positive definite.
Since the quotient orders of the factorial steps `1/n!` modulo `H` diverge, the identity keeps
unit norm in the limit, so `p` has the same successor `1_H`. The remainder `k − p` is invariant
under every rational translation, hence a function `ψ` of the slope, and it carries the entire
negative index of `k` by polynomial index preservation for proper successors.
-/

open Complex Module Filter Topology
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

variable {H : AddSubgroup ℚ} {k : AffineGroupQ → ℂ}

/-! ### Bounded moving forms -/

/-- Each column has moving norm at most one: its fixed part has nonnegative norm `1/ord_H`. -/
theorem subgroup_translationMovingForm_point_le_one (h1 : (1 : ℚ) ∈ H)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (g : AffineGroupQ) :
    (translationMovingForm k hp b (kernelColumnPoint k g) (kernelColumnPoint k g)).re ≤ 1 := by
  have hdiag : kernelColumnPairing k (kernelColumnPoint k g) (kernelColumnPoint k g) = 1 := by
    rw [kernelColumnPairing_point_left hk]
    change k (g⁻¹ * g) = 1
    rw [inv_mul_cancel, hasSubgroupSuccessor_one hs]
  have hP := subgroup_successor_projection_pairing_re h1 hk hi hs hp b g
  have he := congrArg Complex.re (columnPairing_sub_translationMovingForm hk hp b
    (kernelColumnPoint k g) (kernelColumnPoint k g))
  rw [hdiag, Complex.sub_re, Complex.one_re, hP] at he
  have hpos : (0 : ℝ) ≤ (rationalSubgroupOrder H (b / affSlope g) : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  linarith only [he, hpos]

/-- Moving forms are uniformly bounded on every algebraic column vector. -/
theorem subgroup_translationMovingForm_bddAbove (h1 : (1 : ℚ) ∈ H)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (x : kernelColumnSpan k) :
    BddAbove (Set.range (fun b : ℚ => (translationMovingForm k hp b x x).re)) := by
  obtain ⟨n, g, c, rfl⟩ := exists_kernelColumnPoint_fin_sum k x
  refine ⟨(∑ i, ‖c i‖) ^ 2, ?_⟩
  rintro a ⟨b, rfl⟩
  exact positiveHermitianForm_fin_sum_re_le (translationMovingForm_hermitian hk hp b)
    (translationMovingForm_nonneg hk hi hp b) (fun i => kernelColumnPoint k (g i))
    (fun i => subgroup_translationMovingForm_point_le_one h1 hk hi hs hp b (g i)) c

/-! ### The invariant limiting form -/

private theorem factorialMovingForm_monotone' (hk : IsHermKernel k) {r : ℕ}
    (hi : negIndex k ≤ r) (hp : ∀ g, k (g * translation 1) = k g) (x : kernelColumnSpan k) :
    Monotone (fun n => (translationMovingForm k hp (factorialTranslationStep n) x x).re) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [factorialTranslationStep_eq_succ_mul n]
  exact translationMovingForm_re_le_nat_multiple hk hi hp (factorialTranslationStep (n + 1)) (n + 1) x

private theorem factorialMovingForm_bddAbove' (h1 : (1 : ℚ) ∈ H)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (x : kernelColumnSpan k) :
    BddAbove (Set.range
      (fun n => (translationMovingForm k hp (factorialTranslationStep n) x x).re)) := by
  obtain ⟨C, hC⟩ := subgroup_translationMovingForm_bddAbove h1 hk hi hs hp x
  refine ⟨C, ?_⟩
  rintro a ⟨n, rfl⟩
  exact hC ⟨factorialTranslationStep n, rfl⟩

/-- Factorial moving forms converge to the Haar moving limit. -/
theorem subgroup_tendsto_haarMovingLimit (h1 : (1 : ℚ) ∈ H)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (x y : kernelColumnSpan k) :
    Tendsto (fun n => translationMovingForm k hp (factorialTranslationStep n) x y) atTop
      (𝓝 (haarMovingLimit k hp x y)) :=
  tendsto_monotoneHermitianLimit _
    (fun n => translationMovingForm_hermitian hk hp (factorialTranslationStep n))
    (factorialMovingForm_monotone' hk hi hp) (factorialMovingForm_bddAbove' h1 hk hi hs hp) x y

/-- The limiting form is Hermitian and nonnegative. -/
theorem subgroup_haarMovingLimit_hermitian_nonnegative (h1 : (1 : ℚ) ∈ H)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) :
    IsHermitianForm (haarMovingLimit k hp) ∧ ∀ x, 0 ≤ (haarMovingLimit k hp x x).re :=
  monotoneHermitianLimit_isHermitian_nonnegative _
    (fun n => translationMovingForm_hermitian hk hp (factorialTranslationStep n))
    (fun n => translationMovingForm_nonneg hk hi hp (factorialTranslationStep n))
    (factorialMovingForm_monotone' hk hi hp) (factorialMovingForm_bddAbove' h1 hk hi hs hp)

/-- Every cyclic moving form is dominated by the limit (cofinality of factorial steps). -/
theorem subgroup_translationMovingForm_re_le_limit (h1 : (1 : ℚ) ∈ H)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (x : kernelColumnSpan k) :
    (translationMovingForm k hp b x x).re ≤ (haarMovingLimit k hp x x).re := by
  have hnonneg (c : ℚ) (hc : 0 ≤ c) :
      (translationMovingForm k hp c x x).re ≤ (haarMovingLimit k hp x x).re := by
    apply ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp
      (subgroup_tendsto_haarMovingLimit h1 hk hi hs hp x x))
    filter_upwards [eventually_ge_atTop c.den] with n hn
    obtain ⟨m, hm⟩ := eq_nat_mul_factorialTranslationStep c hc hn
    rw [hm]
    exact translationMovingForm_re_le_nat_multiple hk hi hp (factorialTranslationStep n) m x
  by_cases hb : 0 ≤ b
  · exact hnonneg b hb
  · have h := hnonneg (-b) (by linarith only [lt_of_not_ge hb])
    rwa [translationMovingForm_neg] at h

/-- The limiting form is invariant under the whole affine group. -/
theorem subgroup_haarMovingLimit_invariant (h1 : (1 : ℚ) ∈ H)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (g : AffineGroupQ) (x y : kernelColumnSpan k) :
    haarMovingLimit k hp (kernelColumnRepresentation k g x) (kernelColumnRepresentation k g y) =
      haarMovingLimit k hp x y := by
  have hle (a : AffineGroupQ) (v : kernelColumnSpan k) :
      (haarMovingLimit k hp (kernelColumnRepresentation k a v)
          (kernelColumnRepresentation k a v)).re ≤ (haarMovingLimit k hp v v).re := by
    apply le_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp
      (subgroup_tendsto_haarMovingLimit h1 hk hi hs hp _ _))
    intro n
    dsimp only [Function.comp_def]
    rw [translationMovingForm_affine hk]
    exact subgroup_translationMovingForm_re_le_limit h1 hk hi hs hp _ v
  have hdiag (v : kernelColumnSpan k) :
      (haarMovingLimit k hp (kernelColumnRepresentation k g v)
          (kernelColumnRepresentation k g v)).re = (haarMovingLimit k hp v v).re := by
    apply le_antisymm (hle g v)
    have h := hle g⁻¹ (kernelColumnRepresentation k g v)
    have he : kernelColumnRepresentation k g⁻¹ (kernelColumnRepresentation k g v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [he] at h
  have hH := (subgroup_haarMovingLimit_hermitian_nonnegative h1 hk hi hs hp).1
  rw [← hermitianPolarization_diag hH (kernelColumnRepresentation k g x)
    (kernelColumnRepresentation k g y), ← hermitianPolarization_diag hH x y]
  simp only [hermitianPolarization, ← (kernelColumnRepresentation k g).map_smul,
    ← (kernelColumnRepresentation k g).map_add, hdiag]

/-- The discarded form is unchanged by every rational translation of its linear argument. -/
theorem subgroup_columnPairing_sub_haarMovingLimit_translation (h1 : (1 : ℚ) ∈ H)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (x y : kernelColumnSpan k) :
    kernelColumnPairing k y (kernelColumnRepresentation k (translation b) x) -
        haarMovingLimit k hp (kernelColumnRepresentation k (translation b) x) y =
      kernelColumnPairing k y x - haarMovingLimit k hp x y := by
  have hevent : (fun n => kernelColumnPairing k y (kernelColumnRepresentation k (translation b) x) -
      translationMovingForm k hp (factorialTranslationStep n)
        (kernelColumnRepresentation k (translation b) x) y) =ᶠ[atTop]
      (fun n => kernelColumnPairing k y x -
        translationMovingForm k hp (factorialTranslationStep n) x y) := by
    filter_upwards [eventually_ge_atTop b.den] with n hn
    obtain ⟨m, hm⟩ := eq_int_mul_factorialTranslationStep b hn
    rw [columnPairing_sub_translationMovingForm hk, columnPairing_sub_translationMovingForm hk,
      hm, translationFixedProjection_int_multiple]
  have hleft := (tendsto_const_nhds (x :=
    kernelColumnPairing k y (kernelColumnRepresentation k (translation b) x))).sub
      (subgroup_tendsto_haarMovingLimit h1 hk hi hs hp
        (kernelColumnRepresentation k (translation b) x) y)
  have hright := (tendsto_const_nhds (x := kernelColumnPairing k y x)).sub
    (subgroup_tendsto_haarMovingLimit h1 hk hi hs hp x y)
  exact tendsto_nhds_unique (hleft.congr' hevent) hright

/-! ### The positive part and the slope part -/

/-- The coefficient of the invariant moving form is positive definite. -/
theorem subgroup_haarPositivePart_posDef (h1 : (1 : ℚ) ∈ H)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) : IsPosDefKernel (haarPositivePart k hp) := by
  obtain ⟨hH, hpos⟩ := subgroup_haarMovingLimit_hermitian_nonnegative h1 hk hi hs hp
  have h := isPosDefKernel_of_invariantHermitianForm (kernelColumnRepresentation k) hH hpos
    (subgroup_haarMovingLimit_invariant h1 hk hi hs hp) (kernelColumnPoint k 1)
  change IsPosDefKernel (fun g =>
    haarMovingLimit k hp (kernelColumnPoint k g) (kernelColumnPoint k 1))
  simpa only [kernelColumnRepresentation_point, mul_one] using h

/-- The identity keeps unit norm: the factorial steps have diverging order modulo `H`. -/
theorem subgroup_haarPositivePart_one (h1 : (1 : ℚ) ∈ H) (hH : H ≠ ⊤)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) : haarPositivePart k hp 1 = 1 := by
  let v := kernelColumnPoint k 1
  have hbase : kernelColumnPairing k v v = 1 := by
    rw [kernelColumnPairing_point_left hk]
    change k (1⁻¹ * 1) = 1
    rw [inv_one, one_mul, hasSubgroupSuccessor_one hs]
  have hfixed (n : ℕ) : kernelColumnPairing k
      (translationFixedProjection k hp (factorialTranslationStep n) v)
      (translationFixedProjection k hp (factorialTranslationStep n) v) =
        ((rationalSubgroupOrder H (factorialTranslationStep n) : ℂ))⁻¹ := by
    have h := subgroup_successor_projection_pairing h1 hk hi hs hp (factorialTranslationStep n) 1
    rwa [affSlope_one, div_one] at h
  have hn (n : ℕ) : translationMovingForm k hp (factorialTranslationStep n) v v =
      1 - ((rationalSubgroupOrder H (factorialTranslationStep n) : ℂ))⁻¹ := by
    have h := columnPairing_sub_translationMovingForm hk hp (factorialTranslationStep n) v v
    rw [hbase, hfixed] at h
    linear_combination -h
  have hinv : Tendsto (fun n : ℕ =>
      ((rationalSubgroupOrder H (factorialTranslationStep n) : ℂ))⁻¹) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_inv_subgroupOrder_factorialStep H h1 hH)
    rw [Complex.ofReal_zero] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hlim := (tendsto_const_nhds (x := (1 : ℂ))).sub hinv
  have hlim' := hlim.congr' (Eventually.of_forall fun n => (hn n).symm)
  have he := tendsto_nhds_unique (subgroup_tendsto_haarMovingLimit h1 hk hi hs hp v v) hlim'
  simpa only [haarPositivePart, sub_zero] using he

/-- The discarded coefficient is unchanged by every left rational translation. -/
theorem subgroup_haarPositivePart_remainder_translation (h1 : (1 : ℚ) ∈ H)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (g : AffineGroupQ) :
    k (translation b * g) - haarPositivePart k hp (translation b * g) =
      k g - haarPositivePart k hp g := by
  have h := subgroup_columnPairing_sub_haarMovingLimit_translation h1 hk hi hs hp b
    (kernelColumnPoint k g) (kernelColumnPoint k 1)
  rw [kernelColumnRepresentation_point, kernelColumnPairing_point_left hk,
    kernelColumnPairing_point_left hk] at h
  change k (1⁻¹ * (translation b * g)) - haarPositivePart k hp (translation b * g) =
    k (1⁻¹ * g) - haarPositivePart k hp g at h
  simpa only [inv_one, one_mul] using h

/-- The positive part keeps the successor `1_H`. -/
theorem subgroup_haarPositivePart_hasSubgroupSuccessor (h1 : (1 : ℚ) ∈ H) (hH : H ≠ ⊤)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) :
    HasSubgroupSuccessor H (haarPositivePart k hp) := by
  intro b
  have h := subgroup_haarPositivePart_remainder_translation h1 hk hi hs hp b 1
  rw [mul_one, hasSubgroupSuccessor_one hs, subgroup_haarPositivePart_one h1 hH hk hi hs hp,
    sub_self] at h
  exact (sub_eq_zero.mp h).symm.trans (hs b)

/-- The remainder after the positive part is a function of the slope. -/
theorem subgroup_haarPositivePart_add_slope (h1 : (1 : ℚ) ∈ H)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (g : AffineGroupQ) :
    k g = haarPositivePart k hp g + haarSlopePart k hp (slopeUnit g) := by
  have h := subgroup_haarPositivePart_remainder_translation h1 hk hi hs hp (affShift g)
    (dilation (slopeUnit g))
  have hg : translation (affShift g) * dilation (slopeUnit g) = g :=
    (eq_translation_mul_dilation g).symm
  rw [hg] at h
  change k g = haarPositivePart k hp g +
    (k (dilation (slopeUnit g)) - haarPositivePart k hp (dilation (slopeUnit g)))
  linear_combination h

/-- The slope part is Hermitian. -/
theorem subgroup_haarSlopePart_hermitian (h1 : (1 : ℚ) ∈ H)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) : IsHermKernel (haarSlopePart k hp) := by
  have hpos := subgroup_haarPositivePart_posDef h1 hk hi hs hp
  intro u
  change k (dilation u⁻¹) - haarPositivePart k hp (dilation u⁻¹) =
    (starRingEnd ℂ) (k (dilation u) - haarPositivePart k hp (dilation u))
  rw [map_inv, hk, hpos.1, map_sub]

/-! ### Slope kernels -/

/-- The slope of a dilation is its unit. -/
theorem slopeUnit_dilation' (u : ℚˣ) : slopeUnit (dilation u) = u :=
  Units.ext (affSlope_dilation u)

/-- The slope of a translation is one. -/
theorem slopeUnit_translation' (b : ℚ) : slopeUnit (translation b) = 1 :=
  Units.ext (affSlope_translation b)

/-- A kernel of the slope alone is constant on every translation fibre. -/
theorem hasPolynomialTranslationFibres_slope (ψ : ℚˣ → ℂ) :
    HasPolynomialTranslationFibres (fun g => ψ (slopeUnit g)) := by
  intro u
  refine ⟨Polynomial.C (ψ u), fun b => ?_⟩
  change ψ (slopeUnit (translation b * dilation u)) = (Polynomial.C (ψ u)).eval (b : ℂ)
  rw [Polynomial.eval_C, map_mul, slopeUnit_translation', one_mul, slopeUnit_dilation']

/-- Pulling a kernel back along the slope keeps its negative index. -/
theorem negIndex_comp_slopeUnit (ψ : ℚˣ → ℂ) :
    negIndex (fun g => ψ (slopeUnit g)) = negIndex ψ := by
  apply le_antisymm (negIndex_comp_le ψ slopeUnit)
  have h := negIndex_comp_le (fun g => ψ (slopeUnit g)) dilation
  have he : ((fun g => ψ (slopeUnit g)) ∘ dilation) = ψ := by
    funext u
    exact congrArg ψ (slopeUnit_dilation' u)
  rwa [he] at h

/-- Removing the positive part preserves the entire negative index. -/
theorem negIndex_subgroup_haarSlopePart (h1 : (1 : ℚ) ∈ H) (hH : H ≠ ⊤)
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) : negIndex (haarSlopePart k hp) = negIndex k := by
  have hψ := subgroup_haarSlopePart_hermitian h1 hk hi hs hp
  have hherm : IsHermKernel (fun g => haarSlopePart k hp (slopeUnit g)) := hψ.comp slopeUnit
  have h := negIndex_add_positive_subgroup_polynomial H hH
    (subgroup_haarPositivePart_posDef h1 hk hi hs hp)
    (subgroup_haarPositivePart_hasSubgroupSuccessor h1 hH hk hi hs hp) hherm
    (hasPolynomialTranslationFibres_slope (haarSlopePart k hp))
  have he : (fun g => haarPositivePart k hp g + haarSlopePart k hp (slopeUnit g)) = k :=
    funext fun g => (subgroup_haarPositivePart_add_slope h1 hk hi hs hp g).symm
  rw [he, negIndex_comp_slopeUnit] at h
  exact h.symm

end GaloisForLFunctions.AdelicKreinGeometry
