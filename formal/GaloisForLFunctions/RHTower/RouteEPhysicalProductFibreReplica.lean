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

variable {V M : Type*} [Fintype V] [CommMonoid M] [DecidableEq M]

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
    Fintype (S.ProductCell m) :=
  Fintype.ofFinset (Finset.univ.image fun x : Fin m → V => S.historyProduct x) (fun q => q.2)

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
  exact Fin.snoc_init_self

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
  rw [S.appendHistory_init_last x]
  exact hx

/-- Convolution step whose predecessor field is the current product-fibre conditional mean. -/
def convolutionStep (S : RouteEProductReplicaSource V M) (m : ℕ) :
    RouteEPhysicalConvolutionStep (Fin (m + 1) → V) V (S.ProductCell (m + 2)) where
  predecessorMass := S.historyMass
  factorMass := S.probability
  predecessorMean x := (S.productFibreData m).projection x
  combine := S.appendProductCell m
  predecessorMass_pos := S.historyMass_pos
  factorMass_pos := S.probability_pos
  predecessorMass_sum := S.sum_historyMass (m + 1)
  factorMass_sum := S.probability_sum
  combine_surjective := S.appendProductCell_surjective m

theorem convolutionStep_predecessorEnergy
    (S : RouteEProductReplicaSource V M) (m : ℕ) :
    (S.convolutionStep m).predecessorEnergy = S.productFibreEnergy m := by
  rfl

theorem convolutionStep_successorMass
    (S : RouteEProductReplicaSource V M) (m : ℕ) (q : S.ProductCell (m + 2)) :
    (S.convolutionStep m).successorMass q = S.productFibreMass (m + 1) q := by
  classical
  unfold RouteEPhysicalConvolutionStep.successorMass convolutionStep productFibreMass
    RouteEPhysicalFibreData.fibreMass productFibreData appendProductCell
  apply Finset.sum_bij (fun p _hp => appendHistory p.1 p.2)
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ _, hp.2⟩
  · intro p hp
    rw [historyMass_append]
  · intro p hp p' hp' hpp'
    apply Prod.ext
    · funext r
      have := congrFun hpp' r.castSucc
      simpa using this
    · have := congrFun hpp' (Fin.last (m + 1))
      simpa using this
  · intro x hx
    refine ⟨(Fin.init x, x (Fin.last (m + 1))), ?_, ?_⟩
    · rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [appendProductCell, appendHistory_init_last] using hx.2
    · exact appendHistory_init_last x

theorem convolutionStep_successorMoment
    (S : RouteEProductReplicaSource V M) (m : ℕ) (q : S.ProductCell (m + 2)) :
    (S.convolutionStep m).successorMoment q = S.productFibreMoment (m + 1) q := by
  classical
  unfold RouteEPhysicalConvolutionStep.successorMoment convolutionStep productFibreMoment
    RouteEPhysicalFibreData.fibreMoment productFibreData appendProductCell
  apply Finset.sum_bij (fun p _hp => appendHistory p.1 p.2)
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ _, hp.2⟩
  · intro p hp
    rw [historyMass_append]
    simp [RouteEPhysicalFibreData.projection, productFibreData]
  · intro p hp p' hp' hpp'
    apply Prod.ext
    · funext r
      have := congrFun hpp' r.castSucc
      simpa using this
    · have := congrFun hpp' (Fin.last (m + 1))
      simpa using this
  · intro x hx
    refine ⟨(Fin.init x, x (Fin.last (m + 1))), ?_, ?_⟩
    · rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [appendProductCell, appendHistory_init_last] using hx.2
    · exact appendHistory_init_last x

theorem convolutionStep_successorEnergy
    (S : RouteEProductReplicaSource V M) (m : ℕ) :
    (S.convolutionStep m).successorEnergy = S.productFibreEnergy (m + 1) := by
  rw [S.productFibreEnergy_eq_sum_quotient]
  unfold RouteEPhysicalConvolutionStep.successorEnergy
  apply Finset.sum_congr rfl
  intro q _hq
  rw [S.convolutionStep_successorMoment m q, S.convolutionStep_successorMass m q]

/-- Reverse-factor dissipation retained at history level, including every physical weight. -/
def productFibreDissipation (S : RouteEProductReplicaSource V M) (m : ℕ) : ℝ :=
  ∑ p : (Fin (m + 1) → V) × V,
    S.historyMass p.1 * S.probability p.2 *
      ((S.productFibreData m).projection p.1 -
        (S.productFibreData (m + 1)).projection (appendHistory p.1 p.2)) ^ 2

theorem convolutionStep_dissipation
    (S : RouteEProductReplicaSource V M) (m : ℕ) :
    (S.convolutionStep m).dissipation = S.productFibreDissipation m := by
  unfold RouteEPhysicalConvolutionStep.dissipation productFibreDissipation convolutionStep
  apply Finset.sum_congr rfl
  intro p _hp
  congr 2
  rfl

/-- **All-depth physical product-fibre dissipation law.** -/
theorem productFibreEnergy_eq_succ_add_dissipation
    (S : RouteEProductReplicaSource V M) (m : ℕ) :
    S.productFibreEnergy m =
      S.productFibreEnergy (m + 1) + S.productFibreDissipation m := by
  have h := (S.convolutionStep m).predecessorEnergy_eq_successorEnergy_add_dissipation
  rwa [S.convolutionStep_predecessorEnergy, S.convolutionStep_successorEnergy,
    S.convolutionStep_dissipation] at h

theorem productFibreEnergy_antitone_succ
    (S : RouteEProductReplicaSource V M) (m : ℕ) :
    S.productFibreEnergy (m + 1) ≤ S.productFibreEnergy m := by
  rw [S.productFibreEnergy_eq_succ_add_dissipation]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun p _hp =>
      mul_nonneg (mul_pos (S.historyMass_pos p.1) (S.probability_pos p.2)).le (sq_nonneg _))

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
    · funext p
      rw [factorization_historyProduct_eq_primeExponentHistogram atom hatom,
        factorization_historyProduct_eq_primeExponentHistogram atom hatom]
      exact h p

end

end RHTower
