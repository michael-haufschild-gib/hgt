import GaloisForLFunctions.RHTower.SourceHorizontalScalarCalkinInvolutiveReflectionNoGo
import GaloisForLFunctions.HTGeometry.LpShift

/-!
# A universal split Krein reflection receives every source-horizontal packet

The earlier capacity theorems force any bounded involutive all-packet reflection to retain two
noncompact essential sectors. This file proves that boundary sharp for the literal shared
HB/FZZ-P/PW-B/RBH source family.

Take the fixed carrier `ℓ²(ℕ, ℝ) ⊕ ℓ²(ℕ, ℝ)`, the split form

`Q(u,v) = ‖u‖² - ‖v‖²`,

and the bounded involution swapping the two sectors. Every weighted reservoir packet has the exact
factorization

`Σᵢ yᵢ² - (Σᵢ yᵢ)²`,  where `yᵢ = sqrt(wᵢ) xᵢ`.

Its first term is embedded in finitely many coordinates of the first `ℓ²` sector and its sum in one
coordinate of the second. Sector swap negates the form and therefore realizes FE reflection.
For a right-half-plane copy the initial embedding is swapped once.

Thus the same fixed bounded involutive carrier receives every packet of every hypothetical
off-wall Xi copy. Abstract quadratic capacity, infinite index, essential bipolarity, and bounded
linear reflection existence are therefore nonselective: none can supply the missing shared Ward
orientation. Any surviving proof must use source-semantic phase, causal Schwarz oddness, a fixed
Ward law, or nonlinear/singular/domain-changing structure.

The ambient split-Krein construction is classical. The new result is its exact sharpness theorem
for the literal four-route source family and the resulting route-class kill.

`[NEW] [SHARED-WARD ROUTE-CLASS KILL] [SHARPNESS] [UNIVERSAL SPLIT KREIN]`
-/

open scoped BigOperators InnerProductSpace ENNReal

namespace RHTower

noncomputable section

/-- Real square-summable sequences used for each essential orientation sector. -/
abbrev SourceHorizontalSplitL2 : Type :=
  lp (fun _ : ℕ => ℝ) 2

/-- Fixed two-sector carrier, independent of the Xi copy and packet size. -/
abbrev SourceHorizontalSplitKreinCarrier : Type :=
  SourceHorizontalSplitL2 × SourceHorizontalSplitL2

/-- Polar form of the standard split quadratic form. -/
def sourceHorizontalSplitKreinBilin :
    LinearMap.BilinMap ℝ SourceHorizontalSplitKreinCarrier ℝ :=
  LinearMap.mk₂ ℝ
    (fun x y => inner ℝ x.1 y.1 - inner ℝ x.2 y.2)
    (by intro x y z; simp [inner_add_left]; ring)
    (by intro c x y; simp [real_inner_smul_left]; ring)
    (by intro x y z; simp [inner_add_right]; ring)
    (by intro c x y; simp [real_inner_smul_right]; ring)

/-- Standard infinite-index split quadratic form. -/
def sourceHorizontalSplitKreinForm :
    QuadraticForm ℝ SourceHorizontalSplitKreinCarrier :=
  sourceHorizontalSplitKreinBilin.toQuadraticMap

/-- Bounded sector exchange; it negates the split form. -/
def sourceHorizontalSplitSwap :
    SourceHorizontalSplitKreinCarrier →L[ℝ]
      SourceHorizontalSplitKreinCarrier :=
  (ContinuousLinearEquiv.prodComm ℝ SourceHorizontalSplitL2
    SourceHorizontalSplitL2).toContinuousLinearMap

@[simp] theorem sourceHorizontalSplitSwap_apply
    (x : SourceHorizontalSplitKreinCarrier) :
    sourceHorizontalSplitSwap x = (x.2, x.1) := rfl

@[simp] theorem sourceHorizontalSplitKreinForm_apply
    (x : SourceHorizontalSplitKreinCarrier) :
    sourceHorizontalSplitKreinForm x =
      inner ℝ x.1 x.1 - inner ℝ x.2 x.2 := rfl

/-- Sector exchange is an anti-isometry of the split quadratic form. -/
theorem sourceHorizontalSplitKreinForm_swap
    (x : SourceHorizontalSplitKreinCarrier) :
    sourceHorizontalSplitKreinForm (sourceHorizontalSplitSwap x) =
      -sourceHorizontalSplitKreinForm x := by
  simp [sourceHorizontalSplitKreinForm_apply]

/-- Sector exchange is an involution. -/
theorem sourceHorizontalSplitSwap_involutive :
    sourceHorizontalSplitSwap * sourceHorizontalSplitSwap = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- Single-coordinate inclusion into real `ℓ²`. -/
def sourceHorizontalLpSingle (n : ℕ) :
    ℝ →ₗ[ℝ] SourceHorizontalSplitL2 where
  toFun a := lp.single 2 n a
  map_add' a b := by
    ext k
    by_cases h : k = n <;> simp [lp.single_apply, h]
  map_smul' c a := by
    ext k
    by_cases h : k = n <;> simp [lp.single_apply, h]

/-- The weighted `i`-th packet coordinate. -/
def sourceHorizontalPacketCoordinate {m : ℕ} (w : Fin m → ℝ)
    (i : Fin m) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun x := Real.sqrt (w i) * x i
  map_add' x y := by simp [mul_add]
  map_smul' c x := by simp; ring

/-- Embed all weighted packet coordinates in distinct `ℓ²` coordinates. -/
def sourceHorizontalPacketSynthesis {m : ℕ} (w : Fin m → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] SourceHorizontalSplitL2 :=
  ∑ i : Fin m,
    (sourceHorizontalLpSingle (i : ℕ)).comp
      (sourceHorizontalPacketCoordinate w i)

/-- Put the shared-reservoir sum in one coordinate of the opposite sector. -/
def sourceHorizontalPacketAnchor {m : ℕ} (w : Fin m → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] SourceHorizontalSplitL2 :=
  (sourceHorizontalLpSingle 0).comp
    ((reservoirSumLinear m).comp (reservoirScaleLinear w))

/-- Positive-orientation packet embedding. -/
def sourceHorizontalPositiveSplitEmbedding {m : ℕ} (w : Fin m → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] SourceHorizontalSplitKreinCarrier :=
  (sourceHorizontalPacketSynthesis w).prod (sourceHorizontalPacketAnchor w)

@[simp] theorem sourceHorizontalPositiveSplitEmbedding_apply {m : ℕ}
    (w : Fin m → ℝ) (x : Fin m → ℝ) :
    sourceHorizontalPositiveSplitEmbedding w x =
      (∑ i : Fin m, lp.single 2 (i : ℕ) (Real.sqrt (w i) * x i),
        lp.single 2 0 (∑ i : Fin m, Real.sqrt (w i) * x i)) := by
  simp [sourceHorizontalPositiveSplitEmbedding, sourceHorizontalPacketSynthesis,
    sourceHorizontalPacketAnchor, sourceHorizontalPacketCoordinate,
    sourceHorizontalLpSingle, reservoirSumLinear, reservoirScaleLinear]

private theorem coe_sourceHorizontal_sum_single {m : ℕ}
    (c : Fin m → ℝ) (n : ℕ) :
    (((∑ i : Fin m, lp.single 2 (i : ℕ) (c i) : SourceHorizontalSplitL2) : ℕ → ℝ) n) =
      ∑ i : Fin m, if (i : ℕ) = n then c i else 0 := by
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply, Pi.single_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) = n
  · subst n
    simp
  · have h' : n ≠ (i : ℕ) := fun hc => h hc.symm
    simp [h, h']

private theorem norm_rpow_sourceHorizontal_sum_single {m : ℕ}
    (c : Fin m → ℝ) :
    ‖(∑ i : Fin m, lp.single 2 (i : ℕ) (c i) : SourceHorizontalSplitL2)‖ ^ (2 : ℝ) =
      ∑ i : Fin m, ‖c i‖ ^ (2 : ℝ) := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [show ((2 : ℝ)) = (2 : ℝ≥0∞).toReal from h2.symm,
    lp.norm_rpow_eq_tsum hp]
  rw [tsum_eq_sum (s := Finset.univ.image fun i : Fin m => (i : ℕ)) ?_]
  · rw [Finset.sum_image (fun a _ b _ hab => Fin.ext hab)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [coe_sourceHorizontal_sum_single, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have h : (j : ℕ) ≠ (i : ℕ) := fun hc => hji (Fin.ext hc)
      simp [h]
    · simp
  · intro n hn
    rw [coe_sourceHorizontal_sum_single]
    have hz : ∀ i : Fin m, (if (i : ℕ) = n then c i else 0) = 0 := by
      intro i
      have h : (i : ℕ) ≠ n := fun hc => hn (Finset.mem_image.2
        ⟨i, Finset.mem_univ _, hc⟩)
      simp [h]
    rw [Finset.sum_congr rfl (fun i _ => hz i), Finset.sum_const_zero]
    simp

private theorem norm_sq_sourceHorizontal_sum_single {m : ℕ}
    (c : Fin m → ℝ) :
    ‖(∑ i : Fin m, lp.single 2 (i : ℕ) (c i) : SourceHorizontalSplitL2)‖ ^ 2 =
      ∑ i : Fin m, c i ^ 2 := by
  have h := norm_rpow_sourceHorizontal_sum_single c
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num,
    Real.rpow_natCast] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Real.rpow_natCast, Real.norm_eq_abs, sq_abs]

private theorem norm_sq_sourceHorizontal_single_zero (a : ℝ) :
    ‖(lp.single 2 0 a : SourceHorizontalSplitL2)‖ ^ 2 = a ^ 2 := by
  rw [lp.norm_single (by norm_num), Real.norm_eq_abs, sq_abs]

/-- Exact pullback of every positive-orientation shared-reservoir form. -/
theorem sourceHorizontalSplitKreinForm_positiveEmbedding {m : ℕ}
    (w : Fin m → ℝ) (x : Fin m → ℝ) :
    sourceHorizontalSplitKreinForm
        (sourceHorizontalPositiveSplitEmbedding w x) =
      reservoirWeightedForm w x := by
  rw [sourceHorizontalSplitKreinForm_apply]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  rw [sourceHorizontalPositiveSplitEmbedding_apply]
  change
    ‖(∑ i : Fin m, lp.single 2 (i : ℕ) (Real.sqrt (w i) * x i) :
      SourceHorizontalSplitL2)‖ ^ 2 -
      ‖(lp.single 2 0 (∑ i : Fin m, Real.sqrt (w i) * x i) :
        SourceHorizontalSplitL2)‖ ^ 2 = reservoirWeightedForm w x
  rw [norm_sq_sourceHorizontal_sum_single,
    norm_sq_sourceHorizontal_single_zero]
  rw [reservoirWeightedForm, QuadraticMap.comp_apply,
    reservoirBaseForm_apply]
  rfl

/-- Negative-orientation embedding obtained by one sector exchange. -/
def sourceHorizontalNegativeSplitEmbedding {m : ℕ} (w : Fin m → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] SourceHorizontalSplitKreinCarrier :=
  (sourceHorizontalSplitSwap :
    SourceHorizontalSplitKreinCarrier →ₗ[ℝ]
      SourceHorizontalSplitKreinCarrier).comp
    (sourceHorizontalPositiveSplitEmbedding w)

@[simp] theorem sourceHorizontalNegativeSplitEmbedding_apply {m : ℕ}
    (w : Fin m → ℝ) (x : Fin m → ℝ) :
    sourceHorizontalNegativeSplitEmbedding w x =
      sourceHorizontalSplitSwap
        (sourceHorizontalPositiveSplitEmbedding w x) := rfl

/-- Exact pullback of every negative-orientation shared-reservoir form. -/
theorem sourceHorizontalSplitKreinForm_negativeEmbedding {m : ℕ}
    (w : Fin m → ℝ) (x : Fin m → ℝ) :
    sourceHorizontalSplitKreinForm
        (sourceHorizontalNegativeSplitEmbedding w x) =
      -(reservoirWeightedForm w x) := by
  rw [sourceHorizontalNegativeSplitEmbedding_apply,
    sourceHorizontalSplitKreinForm_swap,
    sourceHorizontalSplitKreinForm_positiveEmbedding]

theorem sourceHorizontalSplitSwap_negativeEmbedding {m : ℕ}
    (w : Fin m → ℝ) (x : Fin m → ℝ) :
    sourceHorizontalSplitSwap
        (sourceHorizontalNegativeSplitEmbedding w x) =
      sourceHorizontalPositiveSplitEmbedding w x := by
  simp [sourceHorizontalNegativeSplitEmbedding]

/-- Every left-half-plane packet and its FE reflection land in the fixed split carrier. -/
theorem sourceHorizontalSplitKrein_allPacketLanding_of_left
    (q : XiZeroCopy) (hleft : (q.1 : ℂ).re < 1 / 2) :
    SourceHorizontalAllPacketBoundedReflectionLanding q
      sourceHorizontalSplitKreinForm sourceHorizontalSplitSwap := by
  intro m _hm p _hp
  let w : Fin m → ℝ := sourceZeroHorizontalSharedWeights q p
  have hw : ∀ i, 0 ≤ w i := fun i => abs_nonneg _
  refine ⟨sourceHorizontalPositiveSplitEmbedding w, ?_, ?_⟩
  · intro x
    calc
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
          reservoirWeightedForm w x := by
        rw [sourceZeroHorizontalSharedReservoirMatrix,
          sourceZeroHorizontalOrientation_eq_one_of_left q hleft]
        simpa [w] using DFunLike.congr_fun
          (orientedSourceSharedReservoirMatrix_toQuadraticForm_one hw) x
      _ = sourceHorizontalSplitKreinForm
          (sourceHorizontalPositiveSplitEmbedding w x) :=
        (sourceHorizontalSplitKreinForm_positiveEmbedding w x).symm
  · intro x
    calc
      (sourceZeroHorizontalSharedReservoirMatrix
          (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x =
          -(reservoirWeightedForm w x) := by
        rw [sourceZeroHorizontalSharedReservoirMatrix,
          sourceZeroHorizontalOrientation_reflection,
          sourceZeroHorizontalOrientation_eq_one_of_left q hleft,
          sourceZeroHorizontalSharedWeights_reflection]
        exact DFunLike.congr_fun
          (orientedSourceSharedReservoirMatrix_toQuadraticForm_neg_one hw) x
      _ = sourceHorizontalSplitKreinForm
          (sourceHorizontalSplitSwap
            (sourceHorizontalPositiveSplitEmbedding w x)) := by
        rw [sourceHorizontalSplitKreinForm_swap,
          sourceHorizontalSplitKreinForm_positiveEmbedding]

/-- Every right-half-plane packet and its FE reflection land in the same fixed split carrier. -/
theorem sourceHorizontalSplitKrein_allPacketLanding_of_right
    (q : XiZeroCopy) (hright : 1 / 2 < (q.1 : ℂ).re) :
    SourceHorizontalAllPacketBoundedReflectionLanding q
      sourceHorizontalSplitKreinForm sourceHorizontalSplitSwap := by
  intro m _hm p _hp
  let w : Fin m → ℝ := sourceZeroHorizontalSharedWeights q p
  have hw : ∀ i, 0 ≤ w i := fun i => abs_nonneg _
  refine ⟨sourceHorizontalNegativeSplitEmbedding w, ?_, ?_⟩
  · intro x
    calc
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
          -(reservoirWeightedForm w x) := by
        rw [sourceZeroHorizontalSharedReservoirMatrix,
          sourceZeroHorizontalOrientation_eq_neg_one_of_right q hright]
        exact DFunLike.congr_fun
          (orientedSourceSharedReservoirMatrix_toQuadraticForm_neg_one hw) x
      _ = sourceHorizontalSplitKreinForm
          (sourceHorizontalNegativeSplitEmbedding w x) :=
        (sourceHorizontalSplitKreinForm_negativeEmbedding w x).symm
  · intro x
    calc
      (sourceZeroHorizontalSharedReservoirMatrix
          (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x =
          reservoirWeightedForm w x := by
        rw [sourceZeroHorizontalSharedReservoirMatrix,
          sourceZeroHorizontalOrientation_reflection,
          sourceZeroHorizontalOrientation_eq_neg_one_of_right q hright,
          sourceZeroHorizontalSharedWeights_reflection]
        simpa [w] using DFunLike.congr_fun
          (orientedSourceSharedReservoirMatrix_toQuadraticForm_one hw) x
      _ = sourceHorizontalSplitKreinForm
          (sourceHorizontalSplitSwap
            (sourceHorizontalNegativeSplitEmbedding w x)) := by
        rw [sourceHorizontalSplitSwap_negativeEmbedding,
          sourceHorizontalSplitKreinForm_positiveEmbedding]

/-- Closed route class: abstract bounded split-Krein reflection existence is nonselective. -/
def SourceHorizontalAbstractBoundedSplitKreinReflectionRouteKilled : Prop :=
  sourceHorizontalSplitSwap * sourceHorizontalSplitSwap = 1 ∧
    ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
      SourceHorizontalAllPacketBoundedReflectionLanding q
        sourceHorizontalSplitKreinForm sourceHorizontalSplitSwap

/-- **[SHARED-WARD ROUTE-CLASS KILL].** One fixed bounded involutive split carrier realizes every
literal all-packet source reflection even for every hypothetical off-wall Xi copy. Hence abstract
quadratic capacity or bounded reflection existence cannot force the shared Ward wall. -/
theorem sourceHorizontalAbstractBoundedSplitKreinReflectionRouteKilled :
    SourceHorizontalAbstractBoundedSplitKreinReflectionRouteKilled := by
  refine ⟨sourceHorizontalSplitSwap_involutive, ?_⟩
  intro q hoff
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · exact sourceHorizontalSplitKrein_allPacketLanding_of_left q hleft
  · exact sourceHorizontalSplitKrein_allPacketLanding_of_right q hright

end

end RHTower
