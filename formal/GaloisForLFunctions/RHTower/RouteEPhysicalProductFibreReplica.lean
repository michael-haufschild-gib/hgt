import GaloisForLFunctions.RHTower.RouteEPhysicalFibreCoarea
import GaloisForLFunctions.HTGeometry.TupleHistogramCount

/-!
# Route E physical product-fibre replica coarea

Replica histories are weighted by the actual product probability law and grouped by their literal
multiplicative product.  The induced conditional kernel therefore preserves every recurrence or
Gibbs weight exactly; no uniform-orbit replacement occurs.  This file specializes the generic
physical-fibre projection to those product cells and proves the exact all-depth dissipation law.

For positive integer atoms, unique factorization identifies equality of product cells with equality
of the complete prime-exponent histogram.  Thus the multiplicative label is not a formal proxy for
the incidence data: it is exactly the same finite partition.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-- A finite positive physical source with a signed observable and a multiplicative atom label. -/
structure RouteEProductReplicaSource (V M : Type*) [Fintype V] [CommMonoid M] where
  probability : V → ℝ
  sign : V → ℝ
  atom : V → M
  probability_pos : ∀ v, 0 < probability v
  probability_sum : ∑ v, probability v = 1
  sign_abs_one : ∀ v, |sign v| = 1

namespace RouteEProductReplicaSource

variable {V M : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
  [CommMonoid M] [DecidableEq M]

/-- Physical iid mass of a replica history. -/
def historyMass (S : RouteEProductReplicaSource V M) {m : ℕ} (x : Fin m → V) : ℝ :=
  ∏ r, S.probability (x r)

/-- Literal multiplicative label of a replica history. -/
def historyProduct (S : RouteEProductReplicaSource V M) {m : ℕ} (x : Fin m → V) : M :=
  ∏ r, S.atom (x r)

/-- Finite set of physical product cells at replica order `m`. -/
def ProductCell (S : RouteEProductReplicaSource V M) (m : ℕ) :=
  {q : M // q ∈ Finset.univ.image (fun x : Fin m → V => S.historyProduct x)}

instance productCellFintype (S : RouteEProductReplicaSource V M) (m : ℕ) :
    Fintype (S.ProductCell m) := by
  classical
  unfold ProductCell
  infer_instance

instance productCellDecidableEq (S : RouteEProductReplicaSource V M) (m : ℕ) :
    DecidableEq (S.ProductCell m) := Subtype.instDecidableEq

/-- Canonical product-cell label. -/
def productCellLabel (S : RouteEProductReplicaSource V M) {m : ℕ}
    (x : Fin m → V) : S.ProductCell m :=
  ⟨S.historyProduct x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩

theorem productCellLabel_surjective (S : RouteEProductReplicaSource V M) (m : ℕ) :
    Function.Surjective (S.productCellLabel : (Fin m → V) → S.ProductCell m) := by
  intro q
  obtain ⟨x, _hx, hq⟩ := Finset.mem_image.mp q.2
  exact ⟨x, Subtype.ext hq⟩

theorem historyMass_pos (S : RouteEProductReplicaSource V M) {m : ℕ}
    (x : Fin m → V) : 0 < S.historyMass x :=
  Finset.prod_pos fun r _hr => S.probability_pos (x r)

theorem sum_historyMass (S : RouteEProductReplicaSource V M) (m : ℕ) :
    ∑ x : Fin m → V, S.historyMass x = 1 := by
  classical
  calc
    (∑ x : Fin m → V, S.historyMass x) =
        ∏ _r : Fin m, ∑ v : V, S.probability v := by
      unfold historyMass
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = 1 := by simp [S.probability_sum]

/-- Product-fibre physical projection at positive replica order `m+1`, with the first replica slot
carrying the signed observable. -/
def productFibreData (S : RouteEProductReplicaSource V M) (m : ℕ) :
    RouteEPhysicalFibreData (Fin (m + 1) → V) (S.ProductCell (m + 1)) where
  mass := S.historyMass
  observable x := S.sign (x 0)
  label := S.productCellLabel
  mass_pos := S.historyMass_pos
  mass_sum := S.sum_historyMass (m + 1)
  label_surjective := S.productCellLabel_surjective (m + 1)

@[simp] theorem productFibreData_label (S : RouteEProductReplicaSource V M) (m : ℕ)
    (x : Fin (m + 1) → V) :
    (S.productFibreData m).label x = S.productCellLabel x := rfl

/-- Physical product-fibre mass `B_m(q)`. -/
def productFibreMass (S : RouteEProductReplicaSource V M) (m : ℕ)
    (q : S.ProductCell (m + 1)) : ℝ :=
  (S.productFibreData m).fibreMass q

/-- Signed product-fibre moment `A_m(q)`. -/
def productFibreMoment (S : RouteEProductReplicaSource V M) (m : ℕ)
    (q : S.ProductCell (m + 1)) : ℝ :=
  (S.productFibreData m).fibreMoment q

/-- Conditional signed product field `g_m(q)=A_m(q)/B_m(q)`. -/
def productFibreMean (S : RouteEProductReplicaSource V M) (m : ℕ)
    (q : S.ProductCell (m + 1)) : ℝ :=
  (S.productFibreData m).conditionalMean q

/-- Conditional parity energy `D_m`. -/
def productFibreEnergy (S : RouteEProductReplicaSource V M) (m : ℕ) : ℝ :=
  (S.productFibreData m).projectedEnergy

/-- The physical conditional product-fibre kernel. -/
def productFibreKernel (S : RouteEProductReplicaSource V M) (m : ℕ)
    (x y : Fin (m + 1) → V) : ℝ :=
  (S.productFibreData m).conditionalKernel x y

theorem productFibreKernel_row_sum (S : RouteEProductReplicaSource V M) (m : ℕ)
    (x : Fin (m + 1) → V) :
    ∑ y, S.productFibreKernel m x y = 1 :=
  (S.productFibreData m).conditionalKernel_row_sum x

theorem productFibreKernel_detailedBalance (S : RouteEProductReplicaSource V M) (m : ℕ)
    (x y : Fin (m + 1) → V) :
    S.historyMass x * S.productFibreKernel m x y =
      S.historyMass y * S.productFibreKernel m y x :=
  (S.productFibreData m).conditionalKernel_detailedBalance x y

theorem productFibreKernel_stationary (S : RouteEProductReplicaSource V M) (m : ℕ)
    (y : Fin (m + 1) → V) :
    ∑ x, S.historyMass x * S.productFibreKernel m x y = S.historyMass y :=
  (S.productFibreData m).conditionalKernel_stationary y

theorem productFibreKernel_idempotent (S : RouteEProductReplicaSource V M) (m : ℕ)
    (x y : Fin (m + 1) → V) :
    ∑ z, S.productFibreKernel m x z * S.productFibreKernel m z y =
      S.productFibreKernel m x y :=
  (S.productFibreData m).conditionalKernel_idempotent x y

/-- Exact physical coarea formula `D_m = sum_q A_m(q)^2/B_m(q)`. -/
theorem productFibreEnergy_eq_sum_quotient
    (S : RouteEProductReplicaSource V M) (m : ℕ) :
    S.productFibreEnergy m =
      ∑ q, S.productFibreMoment m q ^ 2 / S.productFibreMass m q :=
  (S.productFibreData m).projectedEnergy_eq_fibreQuotient

/-- The signed iid mean is controlled by physical product-fibre energy with sharp constant one. -/
theorem abs_replicaSignedMean_le_sqrt_productFibreEnergy
    (S : RouteEProductReplicaSource V M) (m : ℕ) :
    |∑ x : Fin (m + 1) → V, S.historyMass x * S.sign (x 0)| ≤
      Real.sqrt (S.productFibreEnergy m) :=
  (S.productFibreData m).abs_mean_le_sqrt_projectedEnergy

/-- Signed iid mean at replica depth `m+1`. -/
def replicaSignedMean (S : RouteEProductReplicaSource V M) (m : ℕ) : ℝ :=
  ∑ x : Fin (m + 1) → V, S.historyMass x * S.sign (x 0)

/-! ## Exact product-cell recursion -/

/-- Append one physical factor to a history. -/
def appendHistory {m : ℕ} (x : Fin m → V) (v : V) : Fin (m + 1) → V :=
  Fin.snoc x v

@[simp] theorem appendHistory_castSucc {m : ℕ} (x : Fin m → V) (v : V) (r : Fin m) :
    appendHistory x v r.castSucc = x r := by
  simp [appendHistory]

@[simp] theorem appendHistory_last {m : ℕ} (x : Fin m → V) (v : V) :
    appendHistory x v (Fin.last m) = v := by
  simp [appendHistory]

theorem appendHistory_init_last {m : ℕ} (x : Fin (m + 1) → V) :
    appendHistory (Fin.init x) (x (Fin.last m)) = x := by
  simpa only [appendHistory] using Fin.snoc_init_self x

theorem historyMass_append {m : ℕ} (S : RouteEProductReplicaSource V M)
    (x : Fin m → V) (v : V) :
    S.historyMass (appendHistory x v) = S.historyMass x * S.probability v := by
  unfold historyMass appendHistory
  rw [Fin.prod_univ_castSucc]
  simp

theorem historyProduct_append {m : ℕ} (S : RouteEProductReplicaSource V M)
    (x : Fin m → V) (v : V) :
    S.historyProduct (appendHistory x v) = S.historyProduct x * S.atom v := by
  unfold historyProduct appendHistory
  rw [Fin.prod_univ_castSucc]
  simp

/-- Product-cell map obtained by appending one factor. -/
def appendProductCell (S : RouteEProductReplicaSource V M) (m : ℕ)
    (p : (Fin (m + 1) → V) × V) : S.ProductCell (m + 2) :=
  S.productCellLabel (appendHistory p.1 p.2)

theorem appendProductCell_surjective (S : RouteEProductReplicaSource V M) (m : ℕ) :
    Function.Surjective (S.appendProductCell m) := by
  intro q
  obtain ⟨x, hx⟩ := S.productCellLabel_surjective (m + 2) q
  refine ⟨(Fin.init x, x (Fin.last (m + 1))), ?_⟩
  unfold appendProductCell
  rw [appendHistory_init_last x]
  exact hx

/-- Splitting a nonempty history into prefix and terminal factor. -/
def appendHistoryEquiv (m : ℕ) :
    ((Fin m → V) × V) ≃ (Fin (m + 1) → V) where
  toFun p := appendHistory p.1 p.2
  invFun x := (Fin.init x, x (Fin.last m))
  left_inv := by
    rintro ⟨x, v⟩
    apply Prod.ext
    · funext r
      simp [appendHistory]
    · simp [appendHistory]
  right_inv := appendHistory_init_last

theorem replicaSignedMean_zero (S : RouteEProductReplicaSource V M) :
    S.replicaSignedMean 0 = ∑ v, S.probability v * S.sign v := by
  classical
  unfold replicaSignedMean
  calc
    (∑ x : Fin 1 → V, S.historyMass x * S.sign (x 0)) =
        ∑ p : (Fin 0 → V) × V,
          S.historyMass (appendHistory p.1 p.2) * S.sign ((appendHistory p.1 p.2) 0) := by
      symm
      refine Fintype.sum_equiv (appendHistoryEquiv (V := V) 0) _ _ ?_
      intro p
      rfl
    _ = ∑ p : (Fin 0 → V) × V, S.probability p.2 * S.sign p.2 := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [S.historyMass_append]
      have hempty : S.historyMass p.1 = 1 := by
        unfold historyMass
        exact Finset.prod_empty
      have hzero : (0 : Fin 1) = Fin.last 0 := rfl
      rw [hzero, appendHistory_last, hempty, one_mul]
    _ = ∑ v, S.probability v * S.sign v := by
      rw [Fintype.sum_prod_type]
      simp

theorem replicaSignedMean_succ (S : RouteEProductReplicaSource V M) (m : ℕ) :
    S.replicaSignedMean (m + 1) = S.replicaSignedMean m := by
  classical
  unfold replicaSignedMean
  have hzero : (0 : Fin (m + 1)).castSucc = (0 : Fin (m + 2)) := rfl
  calc
    (∑ x : Fin (m + 2) → V, S.historyMass x * S.sign (x 0)) =
        ∑ p : (Fin (m + 1) → V) × V,
          S.historyMass (appendHistory p.1 p.2) * S.sign ((appendHistory p.1 p.2) 0) := by
      symm
      refine Fintype.sum_equiv (appendHistoryEquiv (V := V) (m + 1)) _ _ ?_
      intro p
      rfl
    _ = ∑ p : (Fin (m + 1) → V) × V,
        (S.historyMass p.1 * S.probability p.2) * S.sign (p.1 0) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [S.historyMass_append, ← hzero, appendHistory_castSucc]
    _ = ∑ x : Fin (m + 1) → V,
        ∑ v : V, (S.historyMass x * S.probability v) * S.sign (x 0) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ x : Fin (m + 1) → V, S.historyMass x * S.sign (x 0) := by
      apply Finset.sum_congr rfl
      intro x _hx
      calc
        (∑ v : V, (S.historyMass x * S.probability v) * S.sign (x 0)) =
            (S.historyMass x * S.sign (x 0)) * ∑ v, S.probability v := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _hv
          ring
        _ = _ := by rw [S.probability_sum, mul_one]

/-- Replica signed mean is independent of replica depth. -/
theorem replicaSignedMean_eq_single (S : RouteEProductReplicaSource V M) (m : ℕ) :
    S.replicaSignedMean m = ∑ v, S.probability v * S.sign v := by
  induction m with
  | zero => exact S.replicaSignedMean_zero
  | succ m ih => rw [S.replicaSignedMean_succ, ih]

/-- Sharp lower endpoint: squared single-source bias never exceeds product-fibre energy. -/
theorem singleBias_sq_le_productFibreEnergy
    (S : RouteEProductReplicaSource V M) (m : ℕ) :
    (∑ v, S.probability v * S.sign v) ^ 2 ≤ S.productFibreEnergy m := by
  have h := (S.productFibreData m).mean_sq_le_projectedEnergy
  change (S.replicaSignedMean m) ^ 2 ≤ S.productFibreEnergy m at h
  rwa [S.replicaSignedMean_eq_single] at h

/-- Conditional parity energy is at most the unit signed energy. -/
theorem productFibreEnergy_le_one (S : RouteEProductReplicaSource V M) (m : ℕ) :
    S.productFibreEnergy m ≤ 1 := by
  have hanova := (S.productFibreData m).totalEnergy_eq_projected_add_residual
  have htotal :
      (∑ x : Fin (m + 1) → V, S.historyMass x * S.sign (x 0) ^ 2) = 1 := by
    calc
      (∑ x : Fin (m + 1) → V, S.historyMass x * S.sign (x 0) ^ 2) =
          ∑ x, S.historyMass x := by
        apply Finset.sum_congr rfl
        intro x _hx
        have hs : S.sign (x 0) ^ 2 = 1 := by
          rw [← sq_abs, S.sign_abs_one]
          norm_num
        rw [hs, mul_one]
      _ = 1 := S.sum_historyMass (m + 1)
  change (∑ x : Fin (m + 1) → V, S.historyMass x * S.sign (x 0) ^ 2) =
    S.productFibreEnergy m + (S.productFibreData m).residualEnergy at hanova
  linarith [(S.productFibreData m).residualEnergy_nonneg]

/-- Append one atom to a product cell while retaining proof that the output is a physical cell. -/
def cellAppend (S : RouteEProductReplicaSource V M) (m : ℕ)
    (p : S.ProductCell (m + 1) × V) : S.ProductCell (m + 2) := by
  refine ⟨p.1.1 * S.atom p.2, ?_⟩
  obtain ⟨x, _hx, hx⟩ := Finset.mem_image.mp p.1.2
  exact Finset.mem_image.mpr ⟨appendHistory x p.2, Finset.mem_univ _, by
    rw [S.historyProduct_append, hx]⟩

theorem cellAppend_productCellLabel
    (S : RouteEProductReplicaSource V M) (m : ℕ)
    (x : Fin (m + 1) → V) (v : V) :
    S.cellAppend m (S.productCellLabel x, v) =
      S.productCellLabel (appendHistory x v) := by
  apply Subtype.ext
  exact (S.historyProduct_append x v).symm

theorem cellAppend_surjective (S : RouteEProductReplicaSource V M) (m : ℕ) :
    Function.Surjective (S.cellAppend m) := by
  intro q
  obtain ⟨x, hx⟩ := S.productCellLabel_surjective (m + 2) q
  refine ⟨(S.productCellLabel (Fin.init x), x (Fin.last (m + 1))), ?_⟩
  rw [S.cellAppend_productCellLabel, appendHistory_init_last]
  exact hx

/-- Fine independent extension retaining current product cell and appended factor. -/
def extendedFibreData (S : RouteEProductReplicaSource V M) (m : ℕ) :=
  (S.productFibreData m).independentExtensionData
    S.probability S.probability_pos S.probability_sum

/-- Coarse extension obtained by keeping only the new literal product cell. -/
def extendedCoarseData (S : RouteEProductReplicaSource V M) (m : ℕ) :=
  (S.extendedFibreData m).relabel (S.cellAppend m) (S.cellAppend_surjective m)

theorem extendedCoarse_label
    (S : RouteEProductReplicaSource V M) (m : ℕ)
    (p : (Fin (m + 1) → V) × V) :
    (S.extendedCoarseData m).label p =
      S.productCellLabel (appendHistory p.1 p.2) := by
  exact S.cellAppend_productCellLabel m p.1 p.2

theorem extendedCoarse_fibreMass
    (S : RouteEProductReplicaSource V M) (m : ℕ) (q : S.ProductCell (m + 2)) :
    (S.extendedCoarseData m).fibreMass q =
      (S.productFibreData (m + 1)).fibreMass q := by
  classical
  unfold RouteEPhysicalFibreData.fibreMass
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Fintype.sum_equiv (appendHistoryEquiv (V := V) (m + 1)) _ _ ?_
  intro p
  change (if (S.extendedCoarseData m).label p = q then
      S.historyMass p.1 * S.probability p.2 else 0) =
    if (S.productFibreData (m + 1)).label (appendHistory p.1 p.2) = q then
      S.historyMass (appendHistory p.1 p.2) else 0
  rw [S.historyMass_append]
  by_cases hp : (S.extendedCoarseData m).label p = q
  · rw [if_pos hp]
    have hq : (S.productFibreData (m + 1)).label (appendHistory p.1 p.2) = q := by
      change S.productCellLabel (appendHistory p.1 p.2) = q
      rw [← S.extendedCoarse_label m p]
      exact hp
    rw [if_pos hq]
  · rw [if_neg hp]
    have hq : (S.productFibreData (m + 1)).label (appendHistory p.1 p.2) ≠ q := by
      change S.productCellLabel (appendHistory p.1 p.2) ≠ q
      rwa [← S.extendedCoarse_label m p]
    rw [if_neg hq]

theorem extendedCoarse_fibreMoment
    (S : RouteEProductReplicaSource V M) (m : ℕ) (q : S.ProductCell (m + 2)) :
    (S.extendedCoarseData m).fibreMoment q =
      (S.productFibreData (m + 1)).fibreMoment q := by
  classical
  unfold RouteEPhysicalFibreData.fibreMoment
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Fintype.sum_equiv (appendHistoryEquiv (V := V) (m + 1)) _ _ ?_
  intro p
  change (if (S.extendedCoarseData m).label p = q then
      (S.historyMass p.1 * S.probability p.2) * S.sign (p.1 0) else 0) =
    if (S.productFibreData (m + 1)).label (appendHistory p.1 p.2) = q then
      S.historyMass (appendHistory p.1 p.2) * S.sign ((appendHistory p.1 p.2) 0) else 0
  rw [S.historyMass_append]
  have hzero : (0 : Fin (m + 1)).castSucc = (0 : Fin (m + 2)) := rfl
  by_cases hp : (S.extendedCoarseData m).label p = q
  · rw [if_pos hp]
    have hq : (S.productFibreData (m + 1)).label (appendHistory p.1 p.2) = q := by
      change S.productCellLabel (appendHistory p.1 p.2) = q
      rw [← S.extendedCoarse_label m p]
      exact hp
    rw [if_pos hq]
    rw [← hzero, appendHistory_castSucc]
  · rw [if_neg hp]
    have hq : (S.productFibreData (m + 1)).label (appendHistory p.1 p.2) ≠ q := by
      change S.productCellLabel (appendHistory p.1 p.2) ≠ q
      rwa [← S.extendedCoarse_label m p]
    rw [if_neg hq]

theorem extendedCoarse_projectedEnergy
    (S : RouteEProductReplicaSource V M) (m : ℕ) :
    (S.extendedCoarseData m).projectedEnergy = S.productFibreEnergy (m + 1) := by
  change (S.extendedCoarseData m).projectedEnergy =
    (S.productFibreData (m + 1)).projectedEnergy
  rw [(S.extendedCoarseData m).projectedEnergy_eq_fibreQuotient,
    (S.productFibreData (m + 1)).projectedEnergy_eq_fibreQuotient]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [S.extendedCoarse_fibreMass m q, S.extendedCoarse_fibreMoment m q]

theorem extendedCoarse_projection
    (S : RouteEProductReplicaSource V M) (m : ℕ)
    (p : (Fin (m + 1) → V) × V) :
    (S.extendedCoarseData m).projection p =
      (S.productFibreData (m + 1)).projection (appendHistory p.1 p.2) := by
  unfold RouteEPhysicalFibreData.projection RouteEPhysicalFibreData.conditionalMean
  rw [S.extendedCoarse_label m p, S.extendedCoarse_fibreMass,
    S.extendedCoarse_fibreMoment]
  rfl

/-- Reverse-factor dissipation retained at history level, including every physical weight. -/
def productFibreDissipation (S : RouteEProductReplicaSource V M) (m : ℕ) : ℝ :=
  ∑ p : (Fin (m + 1) → V) × V,
    S.historyMass p.1 * S.probability p.2 *
      ((S.productFibreData m).projection p.1 -
        (S.productFibreData (m + 1)).projection (appendHistory p.1 p.2)) ^ 2

/-- **All-depth physical product-fibre dissipation law.** -/
theorem productFibreEnergy_eq_succ_add_dissipation
    (S : RouteEProductReplicaSource V M) (m : ℕ) :
    S.productFibreEnergy m =
      S.productFibreEnergy (m + 1) + S.productFibreDissipation m := by
  have h := (S.productFibreData m).independentExtension_projectedEnergy_eq_relabel_add_defect
    S.probability S.probability_pos S.probability_sum
      (S.cellAppend m) (S.cellAppend_surjective m)
  change S.productFibreEnergy m = (S.extendedCoarseData m).projectedEnergy +
    ∑ p : (Fin (m + 1) → V) × V,
      S.historyMass p.1 * S.probability p.2 *
        ((S.productFibreData m).projection p.1 - (S.extendedCoarseData m).projection p) ^ 2 at h
  rw [S.extendedCoarse_projectedEnergy m] at h
  unfold productFibreDissipation
  simpa only [S.extendedCoarse_projection] using h

theorem productFibreEnergy_antitone_succ
    (S : RouteEProductReplicaSource V M) (m : ℕ) :
    S.productFibreEnergy (m + 1) ≤ S.productFibreEnergy m := by
  calc
    S.productFibreEnergy (m + 1) ≤
        S.productFibreEnergy (m + 1) + S.productFibreDissipation m :=
      le_add_of_nonneg_right
        (Finset.sum_nonneg fun (p : (Fin (m + 1) → V) × V) _hp =>
          mul_nonneg (mul_pos (S.historyMass_pos p.1) (S.probability_pos p.2)).le
            (sq_nonneg _))
    _ = S.productFibreEnergy m := (S.productFibreEnergy_eq_succ_add_dissipation m).symm

/-- Saturation occurs exactly when every admissible reverse factor sees the same conditional signed
field before and after product coarsening. -/
theorem productFibreDissipation_eq_zero_iff_reverseFactor_coherent
    (S : RouteEProductReplicaSource V M) (m : ℕ) :
    S.productFibreDissipation m = 0 ↔
      ∀ p : (Fin (m + 1) → V) × V,
        (S.productFibreData m).projection p.1 =
          (S.productFibreData (m + 1)).projection (appendHistory p.1 p.2) := by
  classical
  unfold productFibreDissipation
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h p
      have hp := h p (Finset.mem_univ p)
      have hmass : 0 < S.historyMass p.1 * S.probability p.2 :=
        mul_pos (S.historyMass_pos p.1) (S.probability_pos p.2)
      have hsquare :
          ((S.productFibreData m).projection p.1 -
            (S.productFibreData (m + 1)).projection (appendHistory p.1 p.2)) ^ 2 = 0 := by
        nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
    · intro h p _hp
      rw [h p, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
  · intro p _hp
    exact mul_nonneg
      (mul_pos (S.historyMass_pos p.1) (S.probability_pos p.2)).le (sq_nonneg _)

end RouteEProductReplicaSource

/-! ## Integer product labels are prime-exponent histograms -/

/-- Total prime exponent carried by an integer-valued history. -/
def routeEPrimeExponentHistogram {V : Type*} {m : ℕ}
    (atom : V → ℕ) (x : Fin m → V) (p : ℕ) : ℕ :=
  ∑ r, (atom (x r)).factorization p

theorem factorization_historyProduct_eq_primeExponentHistogram
    {V : Type*} [Fintype V] {m : ℕ}
    (atom : V → ℕ) (hatom : ∀ v, 0 < atom v)
    (x : Fin m → V) (p : ℕ) :
    (∏ r, atom (x r)).factorization p = routeEPrimeExponentHistogram atom x p := by
  classical
  unfold routeEPrimeExponentHistogram
  rw [Nat.factorization_prod_apply]
  intro r _hr
  exact ne_of_gt (hatom (x r))

/-- **Unique-factorization identification.**  Equality of positive integer product cells is
equivalent to equality of every prime-exponent histogram coordinate. -/
theorem historyProduct_eq_iff_primeExponentHistogram_eq
    {V : Type*} [Fintype V] {m : ℕ}
    (atom : V → ℕ) (hatom : ∀ v, 0 < atom v)
    (x y : Fin m → V) :
    (∏ r, atom (x r)) = (∏ r, atom (y r)) ↔
      ∀ p, routeEPrimeExponentHistogram atom x p =
        routeEPrimeExponentHistogram atom y p := by
  classical
  constructor
  · intro h p
    rw [← factorization_historyProduct_eq_primeExponentHistogram atom hatom,
      ← factorization_historyProduct_eq_primeExponentHistogram atom hatom, h]
  · intro h
    apply Nat.factorization_inj
    · exact Finset.prod_ne_zero_iff.mpr fun r _hr => ne_of_gt (hatom (x r))
    · exact Finset.prod_ne_zero_iff.mpr fun r _hr => ne_of_gt (hatom (y r))
    · apply Finsupp.ext
      intro p
      rw [factorization_historyProduct_eq_primeExponentHistogram atom hatom,
        factorization_historyProduct_eq_primeExponentHistogram atom hatom]
      exact h p

end

end RHTower
