import GaloisForLFunctions.HTGeometry.PrimeResidueValuationAnalyticSuperselection

/-!
# Prime-valuation fusion-completion law

The source observable `1` is multiplicatively neutral, but its valuation lift raises depth:
fusing the depth-`n` carrier of any residue state with the depth-zero vacuum carrier produces the
depth-`n+1` carrier of the same state.  The new carrier is relatively hypertranscendental over the
complete earlier prefix.

The universal consequence is stronger than finite-prefix nonclosure.  Every intermediate field
which contains the complete depth-zero layer and is closed under the exact carrier selected by
prime-valuation fusion must contain every valuation layer.  It therefore contains jointly
differentially independent rectangles of exact rank `d * ∏ i, |A i|` for every `d`.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Module

noncomputable section

universe u

local instance fusionCompletionUpperEndAnalyticDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance fusionCompletionUpperEndMeroComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance fusionCompletionUpperEndMeroDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance fusionCompletionComplexDifferential : Differential ℂ where
  deriv := 0

local instance fusionCompletionUpperEndDifferentialAlgebra :
    DifferentialAlgebra ℂ upperEndMeroField :=
  ⟨fun c => by
    rw [upperEndMero_deriv_complexConstant c]
    change (0 : upperEndMeroField) = algebraMap ℂ upperEndMeroField 0
    rw [map_zero]⟩

@[simp]
theorem pointedSupport_one
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, DecidableEq (A i)] [∀ i, One (A i)] :
    pointedSupport A (fun _ => 1) = ∅ := by
  ext i
  simp [pointedSupport]

@[simp]
theorem pointedUnion_one_right
    {ι : Type u}
    (A : ι → Type u) [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (z : ∀ i, A i) :
    pointedUnion A z (fun _ => 1) = z := by
  funext i
  by_cases hi : z i = 1
  · simp [pointedUnion, hi]
  · simp [pointedUnion, hi]

/-- **Neutral-source creation, formal carrier version.**  The complete next layer is relatively
HT over the complete earlier prefix and has exact residue-state rank.  The prefix tower is strict.
Statewise, fusion with the depth-zero source unit produces the next carrier exactly, but that
carrier is absent from the prefix field. -/
theorem cofiniteTailDenseOn_primeResidueValuationVacuumCreationLaw
    (n : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    GaloisForLFunctions.DifferentialIndependent
        (primeResidueValuationDepthPrefixField n A y)
        (primeResidueValuationNextLayerCarrier (n := n) A y) ∧
      Nat.card (PrimeResidueValuationNextLayerIndex n A) =
        ∏ i, Fintype.card (A i) ∧
      primeResidueValuationDepthPrefixField n A y <
        primeResidueValuationDepthPrefixField (n + 1) A y ∧
      ∀ z : ∀ i, A i,
        primeResidueValuationInteractionCarrier A y n z 0 ∈
            primeResidueValuationDepthPrefixField n A y ∧
          primeResidueValuationInteractionCarrier A y 0 (fun _ => 1) 0 ∈
            primeResidueValuationDepthPrefixField n A y ∧
          primeValuationFusion n 0
              (primeResidueValuationObservableColumn A y n
                (anchoredRestrictedProductBasis A z))
              (primeResidueValuationObservableColumn A y 0
                (anchoredRestrictedProductBasis A (fun _ => 1))) =
            primeResidueValuationObservableColumn A y (n + 1)
              (anchoredRestrictedProductBasis A z) ∧
          primeResidueValuationInteractionCarrier A y (n + 1) z 0 ∉
            primeResidueValuationDepthPrefixField n A y := by
  obtain ⟨hnext, hrank⟩ :=
    cofiniteTailDenseOn_primeResidueValuationNextLayer_relativeHT_over_completePrefix
      n A y hy
  refine ⟨hnext, hrank,
    cofiniteTailDenseOn_primeResidueValuationDepthPrefixField_strictMono n A y hy,
    ?_⟩
  intro z
  have hdis :
      Disjoint (pointedSupport A z) (pointedSupport A (fun _ => 1)) := by
    simp
  simpa using
    (cofiniteTailDenseOn_primeResidueValuationFusion_escapes_completePrefix
      n A y hy z (fun _ => 1) hdis)

/-- **Neutral-source creation, analytic version.**  The same exact law holds for actual
upper-end meromorphic Dirichlet germs.  Fusion is the external coefficient operation; the two
input germs lie in the analytic prefix field and the germ selected by their fusion does not. -/
theorem cofiniteTailDenseOn_primeResidueValuationUpperEndVacuumCreationLaw
    (n : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    GaloisForLFunctions.DifferentialIndependent
        (primeResidueValuationUpperEndDepthPrefixField n A y)
        (primeResidueValuationUpperEndNextLayerCarrier (n := n) A y) ∧
      Nat.card (PrimeResidueValuationNextLayerIndex n A) =
        ∏ i, Fintype.card (A i) ∧
      primeResidueValuationUpperEndDepthPrefixField n A y <
        primeResidueValuationUpperEndDepthPrefixField (n + 1) A y ∧
      ∀ z : ∀ i, A i,
        primeResidueValuationUpperEndCarrier A y n z ∈
            primeResidueValuationUpperEndDepthPrefixField n A y ∧
          primeResidueValuationUpperEndCarrier A y 0 (fun _ => 1) ∈
            primeResidueValuationUpperEndDepthPrefixField n A y ∧
          primeValuationFusion n 0
              (primeResidueValuationObservableColumn A y n
                (anchoredRestrictedProductBasis A z))
              (primeResidueValuationObservableColumn A y 0
                (anchoredRestrictedProductBasis A (fun _ => 1))) =
            primeResidueValuationObservableColumn A y (n + 1)
              (anchoredRestrictedProductBasis A z) ∧
          primeResidueValuationUpperEndCarrier A y (n + 1) z ∉
            primeResidueValuationUpperEndDepthPrefixField n A y := by
  obtain ⟨hnext, hrank⟩ :=
    cofiniteTailDenseOn_primeResidueValuationUpperEndNextLayer_relativeHT n A y hy
  refine ⟨hnext, hrank,
    cofiniteTailDenseOn_primeResidueValuationUpperEndDepthPrefixField_strictMono n A y hy,
    ?_⟩
  intro z
  have hdis :
      Disjoint (pointedSupport A z) (pointedSupport A (fun _ => 1)) := by
    simp
  simpa using
    (cofiniteTailDenseOn_primeResidueValuationUpperEndFusion_escapes_completePrefix
      n A y hy z (fun _ => 1) hdis)

/-- An intermediate meromorphic field is carrier-fusion complete when it contains the exact
union-support carrier selected by prime-valuation fusion whenever it contains two disjoint-support
input carriers.  This is stronger than the vacuum closure used by the completion theorem. -/
def PrimeResidueValuationUpperEndCarrierFusionClosed
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    (L : IntermediateField ℂ upperEndMeroField) : Prop :=
  ∀ (e r : ℕ) (z w : ∀ i, A i),
    Disjoint (pointedSupport A z) (pointedSupport A w) →
      primeResidueValuationUpperEndCarrier A y e z ∈ L →
      primeResidueValuationUpperEndCarrier A y r w ∈ L →
      primeResidueValuationUpperEndCarrier A y (e + r + 1)
        (pointedUnion A z w) ∈ L

/-- Fusion completeness and the complete depth-zero source layer force every valuation layer
into the field.  Only fusion with the source-unit carrier is needed in the induction. -/
theorem primeResidueValuationUpperEnd_allLayers_mem_of_fusionClosed
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    (L : IntermediateField ℂ upperEndMeroField)
    (hzero : ∀ z : ∀ i, A i,
      primeResidueValuationUpperEndCarrier A y 0 z ∈ L)
    (hfusion : PrimeResidueValuationUpperEndCarrierFusionClosed A y L) :
    ∀ (e : ℕ) (z : ∀ i, A i),
      primeResidueValuationUpperEndCarrier A y e z ∈ L := by
  intro e
  induction e with
  | zero => exact hzero
  | succ e ih =>
      intro z
      have hdis :
          Disjoint (pointedSupport A z) (pointedSupport A (fun _ => 1)) := by
        simp
      have hcreated := hfusion e 0 z (fun _ => 1) hdis (ih z) (hzero (fun _ => 1))
      simpa using hcreated

/-- The complete countable valuation carrier family. -/
def primeResidueValuationUpperEndAllLayerCarrier
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    (x : ℕ × (∀ i, A i)) : upperEndMeroField :=
  primeResidueValuationUpperEndCarrier A y x.1 x.2

/-- The canonical differential field generated by every valuation layer. -/
def primeResidueValuationUpperEndFusionCompletionField
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) : IntermediateField ℂ upperEndMeroField :=
  GaloisForLFunctions.differentialAdjoin ℂ
    (Set.range (primeResidueValuationUpperEndAllLayerCarrier A y))

/-- The canonical all-layer field contains the complete depth-zero layer. -/
theorem primeResidueValuationUpperEndFusionCompletionField_zero_mem
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) (z : ∀ i, A i) :
    primeResidueValuationUpperEndCarrier A y 0 z ∈
      primeResidueValuationUpperEndFusionCompletionField A y := by
  exact GaloisForLFunctions.subset_differentialAdjoin ℂ _ ⟨(0, z), rfl⟩

/-- The canonical all-layer field is carrier-fusion complete. -/
theorem primeResidueValuationUpperEndFusionCompletionField_fusionClosed
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) :
    PrimeResidueValuationUpperEndCarrierFusionClosed A y
      (primeResidueValuationUpperEndFusionCompletionField A y) := by
  intro e r z w _hdis _he _hr
  exact GaloisForLFunctions.subset_differentialAdjoin ℂ _
    ⟨(e + r + 1, pointedUnion A z w), rfl⟩

/-- **Canonical minimal fusion completion.**  Every derivation-closed carrier-fusion complete
intermediate field containing the complete depth-zero layer contains the all-layer differential
field. -/
theorem primeResidueValuationUpperEndFusionCompletionField_le
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    (L : IntermediateField ℂ upperEndMeroField)
    (hderiv : GaloisForLFunctions.DerivationClosed L)
    (hzero : ∀ z : ∀ i, A i,
      primeResidueValuationUpperEndCarrier A y 0 z ∈ L)
    (hfusion : PrimeResidueValuationUpperEndCarrierFusionClosed A y L) :
    primeResidueValuationUpperEndFusionCompletionField A y ≤ L := by
  apply GaloisForLFunctions.differentialAdjoin_le ℂ
  · rintro _ ⟨x, rfl⟩
    exact primeResidueValuationUpperEnd_allLayers_mem_of_fusionClosed
      A y L hzero hfusion x.1 x.2
  · exact hderiv

/-- The canonical all-layer field is itself derivation-closed. -/
theorem primeResidueValuationUpperEndFusionCompletionField_derivationClosed
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) :
    GaloisForLFunctions.DerivationClosed
      (primeResidueValuationUpperEndFusionCompletionField A y) := by
  exact GaloisForLFunctions.derivationClosed_differentialAdjoin ℂ _

/-- The constant-fiber valuation grid is canonically a product. -/
def primeResidueValuationInteractionGridIndexEquiv
    (d : ℕ) {ι : Type u} (A : ι → Type u) :
    PrimeResidueValuationInteractionGridIndex d A ≃ Fin d × (∀ i, A i) where
  toFun x := (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact cardinality of a finite valuation-depth by residue-state rectangle. -/
theorem primeResidueValuationInteractionGridIndex_card
    (d : ℕ) {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] :
    Nat.card (PrimeResidueValuationInteractionGridIndex d A) =
      d * ∏ i, Fintype.card (A i) := by
  rw [Nat.card_congr (primeResidueValuationInteractionGridIndexEquiv d A),
    Nat.card_prod, Nat.card_fin, Nat.card_pi]
  simp only [Nat.card_eq_fintype_card]

/-- **Fusion-completion lower bound.**  Every carrier-fusion complete field containing the
complete depth-zero layer contains, for every `d`, a jointly differentially independent analytic
rectangle of exact rank `d * ∏ i, |A i|`.  Thus no finite bound exists on the differential rank
forced inside a fusion-complete realization. -/
theorem cofiniteTailDenseOn_primeResidueValuationUpperEndFusionCompletion_unboundedRank
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ)
    (L : IntermediateField ℂ upperEndMeroField)
    (hzero : ∀ z : ∀ i, A i,
      primeResidueValuationUpperEndCarrier A y 0 z ∈ L)
    (hfusion : PrimeResidueValuationUpperEndCarrierFusionClosed A y L) :
    ∀ d : ℕ,
      GaloisForLFunctions.DifferentialIndependent ℂ
          (primeResidueValuationUpperEndGridCarrier (d := d) A y) ∧
        (∀ x : PrimeResidueValuationInteractionGridIndex d A,
          primeResidueValuationUpperEndGridCarrier A y x ∈ L) ∧
        Nat.card (PrimeResidueValuationInteractionGridIndex d A) =
          d * ∏ i, Fintype.card (A i) := by
  have hall := primeResidueValuationUpperEnd_allLayers_mem_of_fusionClosed
    A y L hzero hfusion
  intro d
  refine ⟨
    cofiniteTailDenseOn_primeResidueValuationUpperEndCarrier_differentialIndependent
      (d := d) A y hy,
    ?_,
    primeResidueValuationInteractionGridIndex_card d A⟩
  intro x
  exact hall x.1 x.2

/-- **Actual-prime fusion-completion law.**  For simultaneous unit residues modulo pairwise
coprime moduli, the exact forced rank is `d * ∏ i, φ(q i)` at every finite depth. -/
theorem pairwiseCoprimePrimeResidueValuationUpperEndFusionCompletion_unboundedRank
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (modulus : ι → ℕ) [∀ i, NeZero (modulus i)]
    [NeZero (∏ i, modulus i)]
    (h : Pairwise (Function.onFun Nat.Coprime modulus))
    (L : IntermediateField ℂ upperEndMeroField) :
    let A := fun i => (ZMod (modulus i))ˣ
    let y := pairwiseCoprimePrimeUnitResidueProfile modulus h
    (∀ z : ∀ i, A i,
      primeResidueValuationUpperEndCarrier A y 0 z ∈ L) →
    PrimeResidueValuationUpperEndCarrierFusionClosed A y L →
    ∀ d : ℕ,
      GaloisForLFunctions.DifferentialIndependent ℂ
          (primeResidueValuationUpperEndGridCarrier (d := d) A y) ∧
        (∀ x : PrimeResidueValuationInteractionGridIndex d A,
          primeResidueValuationUpperEndGridCarrier A y x ∈ L) ∧
        Nat.card (PrimeResidueValuationInteractionGridIndex d A) =
          d * ∏ i, Nat.totient (modulus i) := by
  dsimp only
  intro hzero hfusion
  let A := fun i => (ZMod (modulus i))ˣ
  let y := pairwiseCoprimePrimeUnitResidueProfile modulus h
  letI : TopologicalSpace (∀ i, A i) := ⊥
  letI : DiscreteTopology (∀ i, A i) := ⟨rfl⟩
  have hy : CofiniteTailDenseOn y Set.univ :=
    cofiniteTailDenseOn_univ_of_recurringValueSet_eq_univ y
      (recurringValueSet_pairwiseCoprimePrimeUnitResidueProfile modulus h)
  intro d
  obtain ⟨hind, hmem, hrank⟩ :=
    cofiniteTailDenseOn_primeResidueValuationUpperEndFusionCompletion_unboundedRank
      A y hy L hzero hfusion d
  refine ⟨hind, hmem, ?_⟩
  dsimp [A] at hrank ⊢
  simpa only [ZMod.card_units_eq_totient] using hrank

end

end GaloisForLFunctions.HTGeometry
