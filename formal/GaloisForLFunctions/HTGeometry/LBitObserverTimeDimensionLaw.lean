import GaloisForLFunctions.HTGeometry.LBitGeometricLocalityLaw
import GaloisForLFunctions.HTGeometry.ObserverTemporalDimensionCascadeLaw

/-!
# Exact observer-time dimension of a scaled l-bit spectrum

A birth-order function assigns every finite l-bit interaction support to one
spectral-jet layer.  Walsh orthogonality then identifies the observer-time
directions at resolution `r` with the direct product of the rational
coefficient spaces born in layers below `r`.  Consequently the resolved
dimension is the sum of the layerwise rational ranks; no independence between
different birth layers is required.

For the geometric birth order given by support diameter, resolution `r`
accesses only interactions of range at most `r`.  The existing one-dimensional
window count therefore gives the explicit ceiling `n * 2^(r+1)`.

The resolution parameter here is spectral-jet order.  No claim identifies it
with physical elapsed time.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance lbitObserverTimeFintypeForallBool
    {I : Type*} [Fintype I] :
    Fintype (I → Bool) :=
  Fintype.ofFinite _

/-- Nonempty supports born in one exact spectral-jet layer. -/
abbrev LBitBirthLayerSupport
    (I : Type*) [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ) (order : ℕ) :=
  {S : Finset I // S.Nonempty ∧ birthOrder S = order}

/-- Walsh coefficient packet carried by one exact birth layer, embedded in
the complex spectral codomain. -/
def lbitBirthLayerCoefficient
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (order : ℕ) :
    LBitBirthLayerSupport I birthOrder order → ℂ :=
  fun S => (J S.1 : ℂ)

/-- Rational coefficient space carried by one exact birth layer. -/
def lbitBirthLayerCoefficientSpace
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (order : ℕ) :
    Submodule ℚ ℂ :=
  Submodule.span ℚ
    (Set.range (lbitBirthLayerCoefficient birthOrder J order))

/-- Rational rank carried by one exact birth layer. -/
noncomputable def lbitBirthLayerRank
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (order : ℕ) : ℕ :=
  Module.finrank ℚ
    (lbitBirthLayerCoefficientSpace birthOrder J order)

/-- Spectral jet of a scaled l-bit spectrum.  At order `order` it is exactly
the Walsh sum of coefficients whose supports have that birth order. -/
def scaledLBitSpectralJet
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ)
    (order : ℕ) (x : I → Bool) : ℂ :=
  ∑ S : Finset I,
    if S.Nonempty ∧ birthOrder S = order then
      lbitWalshCharacter S x • (J S : ℂ)
    else 0

/-- Polynomial energy branch obtained by switching on support `S` at the
power prescribed by its birth order. -/
def scaledLBitEnergyPolynomial
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (x : I → Bool) :
    Polynomial ℂ :=
  ∑ S : Finset I,
    Polynomial.monomial (birthOrder S)
      (lbitWalshCharacter S x • (J S : ℂ))

/-- The displayed spectral jet is the exact coefficient of the scaled l-bit
energy polynomial when the irrelevant constant Walsh coefficient vanishes. -/
theorem scaledLBitEnergyPolynomial_coeff
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (hJempty : J ∅ = 0)
    (order : ℕ) (x : I → Bool) :
    (scaledLBitEnergyPolynomial birthOrder J x).coeff order =
      scaledLBitSpectralJet birthOrder J order x := by
  classical
  simp [scaledLBitEnergyPolynomial, scaledLBitSpectralJet,
    Polynomial.coeff_monomial, eq_comm]
  apply Finset.sum_congr rfl
  intro S hSuniv
  by_cases hS : S.Nonempty
  · simp [hS]
  · have hempty : S = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [hJempty]

/-- A nonconstant Walsh character is a projective rational character on the
Boolean configuration spectrum. -/
def lbitWalshProjectiveCharacter
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (hS : S.Nonempty) :
    ProjectiveRationalCharacter (I → Bool) :=
  ⟨fun x => lbitWalshCharacter S x, by
    change ∑ x : I → Bool, lbitWalshCharacter S x = 0
    exact sum_lbitWalshCharacter_eq_zero hS⟩

/-- Complex Walsh orthogonality with an arbitrary complex coefficient. -/
theorem sum_complex_lbitWalshCharacter_mul_smul
    {I : Type*} [Fintype I] [DecidableEq I]
    (S T : Finset I) (z : ℂ) :
    (∑ x : I → Bool,
      (lbitWalshCharacter S x : ℂ) *
        (lbitWalshCharacter T x • z)) =
      (if S = T then (2 : ℚ) ^ Fintype.card I else 0) • z := by
  have horth := sum_lbitWalshCharacter_mul S T
  calc
    (∑ x : I → Bool,
      (lbitWalshCharacter S x : ℂ) *
        (lbitWalshCharacter T x • z)) =
        (∑ x : I → Bool,
          lbitWalshCharacter S x *
            lbitWalshCharacter T x) • z := by
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Algebra.smul_def]
      push_cast
      ac_rfl
    _ = (if S = T then (2 : ℚ) ^ Fintype.card I else 0) • z := by
      rw [horth]

/-- Pairing one Walsh projective character with a scaled l-bit jet extracts
exactly its coefficient at its unique birth layer. -/
theorem projectiveJetMap_scaledLBitSpectralJet_walsh
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ)
    (S : Finset I) (hS : S.Nonempty)
    (r : ℕ) (order : Fin r) :
    projectiveJetMap
        (scaledLBitSpectralJet birthOrder J) r
        (lbitWalshProjectiveCharacter S hS) order =
      if birthOrder S = order then
        ((2 : ℚ) ^ Fintype.card I) • (J S : ℂ)
      else 0 := by
  classical
  change
    (∑ x : I → Bool,
      (lbitWalshCharacter S x : ℂ) *
        scaledLBitSpectralJet birthOrder J order x) = _
  simp_rw [scaledLBitSpectralJet, Finset.mul_sum]
  rw [Finset.sum_comm]
  by_cases hbirth : birthOrder S = order
  · rw [if_pos hbirth]
    rw [Fintype.sum_eq_single S]
    · simp only [if_pos
        (show S.Nonempty ∧ birthOrder S = (order : ℕ) from
          ⟨hS, hbirth⟩)]
      simpa using
        sum_complex_lbitWalshCharacter_mul_smul
          S S (J S : ℂ)
    · intro T hTS
      by_cases hT :
          T.Nonempty ∧ birthOrder T = (order : ℕ)
      · simp only [if_pos hT]
        rw [sum_complex_lbitWalshCharacter_mul_smul]
        simp [hTS.symm]
      · simp [if_neg hT]
  · rw [if_neg hbirth]
    apply Finset.sum_eq_zero
    intro T hT
    by_cases hTbirth :
        T.Nonempty ∧ birthOrder T = (order : ℕ)
    · simp only [if_pos hTbirth]
      rw [sum_complex_lbitWalshCharacter_mul_smul]
      split_ifs with hST
      · subst T
        exact False.elim (hbirth hTbirth.2)
      · simp
    · simp [if_neg hTbirth]

/-- Every evaluated truncated jet coordinate belongs to the coefficient
space of its own birth layer. -/
theorem projectiveJetMap_scaledLBitSpectralJet_apply_mem_layer
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ)
    (r : ℕ)
    (k : ProjectiveRationalCharacter (I → Bool))
    (order : Fin r) :
    projectiveJetMap
        (scaledLBitSpectralJet birthOrder J) r k order ∈
      lbitBirthLayerCoefficientSpace
        birthOrder J order := by
  classical
  change
    (∑ x : I → Bool,
      (k.1 x : ℂ) *
        scaledLBitSpectralJet birthOrder J order x) ∈ _
  simp_rw [scaledLBitSpectralJet, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Submodule.sum_mem
  intro S hSuniv
  by_cases hS :
      S.Nonempty ∧ birthOrder S = (order : ℕ)
  · simp only [if_pos hS]
    have hgenerator :
        (J S : ℂ) ∈
          lbitBirthLayerCoefficientSpace
            birthOrder J order :=
      Submodule.subset_span
        ⟨⟨S, hS⟩, rfl⟩
    have hq :
        ∃ q : ℚ,
          (∑ x : I → Bool,
            (k.1 x : ℂ) *
              (lbitWalshCharacter S x • (J S : ℂ))) =
            q • (J S : ℂ) := by
      refine
        ⟨∑ x : I → Bool,
            k.1 x * lbitWalshCharacter S x, ?_⟩
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Algebra.smul_def]
      push_cast
      ac_rfl
    obtain ⟨q, hq⟩ := hq
    rw [hq]
    exact Submodule.smul_mem _ q hgenerator
  · simp [if_neg hS]

/-- Normalized Walsh extraction produces a vector supported in exactly one
resolved birth coordinate. -/
theorem projectiveJetMap_scaledLBitSpectralJet_normalized_walsh
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ)
    (r : ℕ) (order : Fin r)
    (S : LBitBirthLayerSupport I birthOrder order) :
    projectiveJetMap
        (scaledLBitSpectralJet birthOrder J) r
        (((2 : ℚ) ^ Fintype.card I)⁻¹ •
          lbitWalshProjectiveCharacter S.1 S.2.1) =
      LinearMap.single ℚ (fun _ : Fin r => ℂ)
        order (J S.1 : ℂ) := by
  classical
  ext m
  rw [map_smul]
  change
    (((2 : ℚ) ^ Fintype.card I)⁻¹ : ℚ) •
        projectiveJetMap
          (scaledLBitSpectralJet birthOrder J) r
          (lbitWalshProjectiveCharacter S.1 S.2.1) m =
      LinearMap.single ℚ (fun _ : Fin r => ℂ)
        order (J S.1 : ℂ) m
  rw [projectiveJetMap_scaledLBitSpectralJet_walsh]
  by_cases hm : m = order
  · subst m
    simp [S.2.2]
  · have hbirth :
        birthOrder S.1 ≠ (m : ℕ) := by
      intro h
      apply hm
      apply Fin.ext
      rw [← S.2.2, h]
    simp [hbirth, hm]

/-- **Exact direct-product decomposition.** Truncated observer-time
directions are exactly the independent coordinate product of coefficient
spaces born below the resolution. -/
theorem temporalDirectionSpace_scaledLBitSpectralJet_eq_pi
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (r : ℕ) :
    temporalDirectionSpace
        (scaledLBitSpectralJet birthOrder J) r =
      Submodule.pi Set.univ
        (fun order : Fin r =>
          lbitBirthLayerCoefficientSpace
            birthOrder J order) := by
  classical
  apply le_antisymm
  · rintro y ⟨k, rfl⟩
    rw [Submodule.mem_pi]
    intro order horder
    exact
      projectiveJetMap_scaledLBitSpectralJet_apply_mem_layer
        birthOrder J r k order
  · rw [← Submodule.iSup_map_single]
    apply iSup_le
    intro order
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.2
    rintro z ⟨S, rfl⟩
    change
      LinearMap.single ℚ (fun _ : Fin r => ℂ)
          order (J S.1 : ℂ) ∈
        temporalDirectionSpace
          (scaledLBitSpectralJet birthOrder J) r
    exact
      ⟨((2 : ℚ) ^ Fintype.card I)⁻¹ •
          lbitWalshProjectiveCharacter S.1 S.2.1,
        projectiveJetMap_scaledLBitSpectralJet_normalized_walsh
          birthOrder J r order S⟩

/-- The submodule product of the birth-layer coefficient spaces is linearly
equivalent to the dependent product of their subtype carriers. -/
def lbitBirthLayerCoefficientSpacePiEquiv
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (r : ℕ) :
    (Submodule.pi Set.univ
      (fun order : Fin r =>
        lbitBirthLayerCoefficientSpace
          birthOrder J order)) ≃ₗ[ℚ]
      (∀ order : Fin r,
        lbitBirthLayerCoefficientSpace
          birthOrder J order) where
  toFun f := fun order =>
    ⟨f.1 order, f.2 order (Set.mem_univ order)⟩
  invFun f :=
    ⟨fun order => f order,
      fun order horder => (f order).2⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv f := by
    funext order
    rfl
  map_add' f g := by
    rfl
  map_smul' q f := by
    rfl

/-- **Layer-additive observer-time law.** At every finite resolution, the
observer-time dimension is exactly the sum of the rational ranks of all
coefficient layers born below that resolution. -/
theorem temporalDimension_scaledLBitSpectralJet_eq_sum_layerRank
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (r : ℕ) :
    temporalDimension
        (scaledLBitSpectralJet birthOrder J) r =
      ∑ order : Fin r,
        lbitBirthLayerRank birthOrder J order := by
  letI (order : Fin r) :
      FiniteDimensional ℚ
        (lbitBirthLayerCoefficientSpace
          birthOrder J order) :=
    FiniteDimensional.span_of_finite ℚ
      (Set.finite_range
        (lbitBirthLayerCoefficient birthOrder J order))
  rw [temporalDimension,
    temporalDirectionSpace_scaledLBitSpectralJet_eq_pi]
  calc
    Module.finrank ℚ
        (Submodule.pi Set.univ
          (fun order : Fin r =>
            lbitBirthLayerCoefficientSpace
              birthOrder J order)) =
      Module.finrank ℚ
        (∀ order : Fin r,
          lbitBirthLayerCoefficientSpace
            birthOrder J order) :=
      (lbitBirthLayerCoefficientSpacePiEquiv
        birthOrder J r).finrank_eq
    _ = ∑ order : Fin r,
          Module.finrank ℚ
            (lbitBirthLayerCoefficientSpace
              birthOrder J order) :=
      Module.finrank_pi_fintype ℚ
    _ = ∑ order : Fin r,
          lbitBirthLayerRank birthOrder J order := rfl

/-- The rational rank carried by one birth layer never exceeds the number
of supports in that layer. -/
theorem lbitBirthLayerRank_le_card
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (order : ℕ) :
    lbitBirthLayerRank birthOrder J order ≤
      Fintype.card
        (LBitBirthLayerSupport I birthOrder order) := by
  unfold lbitBirthLayerRank lbitBirthLayerCoefficientSpace
  let s : Set ℂ :=
    Set.range
      (lbitBirthLayerCoefficient birthOrder J order)
  letI : Fintype s := s.toFinite.fintype
  calc
    Module.finrank ℚ (Submodule.span ℚ s) ≤
        s.toFinset.card :=
      finrank_span_le_card s
    _ ≤
        Fintype.card
          (LBitBirthLayerSupport I birthOrder order) := by
      convert Fintype.card_range_le
        (lbitBirthLayerCoefficient birthOrder J order) using 1
      rw [Set.toFinset_card]

/-- Nonempty l-bit supports born strictly below one resolution. -/
def lbitSupportsBornBefore
    (I : Type*) [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ) (r : ℕ) :
    Finset (Finset I) :=
  (Finset.univ.powerset).filter
    (fun S => S.Nonempty ∧ birthOrder S < r)

@[simp] theorem mem_lbitSupportsBornBefore
    {I : Type*} [Fintype I] [DecidableEq I]
    {birthOrder : Finset I → ℕ} {r : ℕ}
    {S : Finset I} :
    S ∈ lbitSupportsBornBefore I birthOrder r ↔
      S.Nonempty ∧ birthOrder S < r := by
  simp [lbitSupportsBornBefore]

/-- Finset realization of one exact birth layer. -/
def lbitBirthLayerSupports
    (I : Type*) [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ) (order : ℕ) :
    Finset (Finset I) :=
  (Finset.univ.powerset).filter
    (fun S => S.Nonempty ∧ birthOrder S = order)

@[simp] theorem mem_lbitBirthLayerSupports
    {I : Type*} [Fintype I] [DecidableEq I]
    {birthOrder : Finset I → ℕ} {order : ℕ}
    {S : Finset I} :
    S ∈ lbitBirthLayerSupports I birthOrder order ↔
      S.Nonempty ∧ birthOrder S = order := by
  simp [lbitBirthLayerSupports]

/-- Cardinality of the subtype birth layer agrees with its concrete support
finset. -/
theorem card_lbitBirthLayerSupport
    (I : Type*) [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ) (order : ℕ) :
    Fintype.card (LBitBirthLayerSupport I birthOrder order) =
      (lbitBirthLayerSupports I birthOrder order).card := by
  exact Fintype.card_of_subtype
    (lbitBirthLayerSupports I birthOrder order)
    (fun S => mem_lbitBirthLayerSupports)

/-- Supports born below `r` are the disjoint union of the exact layers
indexed by `Fin r`. -/
theorem card_lbitSupportsBornBefore_eq_sum_layers
    (I : Type*) [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ) (r : ℕ) :
    (lbitSupportsBornBefore I birthOrder r).card =
      ∑ order : Fin r,
        Fintype.card
          (LBitBirthLayerSupport I birthOrder order) := by
  change
    (lbitSupportsBornBefore I birthOrder r).card =
      ∑ order : Fin r,
        (fun n : ℕ =>
          Fintype.card
            (LBitBirthLayerSupport I birthOrder n)) order
  rw [Fin.sum_univ_eq_sum_range
    (fun n : ℕ =>
      Fintype.card
        (LBitBirthLayerSupport I birthOrder n)) r]
  have hMaps :
      ((lbitSupportsBornBefore I birthOrder r : Finset (Finset I)) :
          Set (Finset I)).MapsTo
        birthOrder (Finset.range r) := by
    intro S hS
    exact Finset.mem_range.mpr
      (mem_lbitSupportsBornBefore.mp hS).2
  rw [Finset.card_eq_sum_card_fiberwise hMaps]
  apply Finset.sum_congr rfl
  intro order horder
  have horderlt : order < r :=
    Finset.mem_range.mp horder
  rw [card_lbitBirthLayerSupport]
  congr 1
  ext S
  simp [lbitSupportsBornBefore, lbitBirthLayerSupports]
  intro hbirth hnonempty
  rw [hbirth]
  exact horderlt

/-- At every resolution, temporal dimension is bounded by the number of
nonempty supports born below that resolution, without any coefficient
independence hypothesis. -/
theorem temporalDimension_scaledLBitSpectralJet_le_card_bornBefore
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (r : ℕ) :
    temporalDimension
        (scaledLBitSpectralJet birthOrder J) r ≤
      (lbitSupportsBornBefore I birthOrder r).card := by
  rw [temporalDimension_scaledLBitSpectralJet_eq_sum_layerRank,
    card_lbitSupportsBornBefore_eq_sum_layers]
  exact Finset.sum_le_sum fun order _ =>
    lbitBirthLayerRank_le_card birthOrder J order

/-- **Coefficient-count law under only layerwise independence.** If the
coefficients born in each resolved layer are rationally independent, the
observer-time dimension is exactly the number of nonempty supports born
before the resolution.  Coefficients in different layers may satisfy
arbitrary cross-layer rational relations. -/
theorem temporalDimension_scaledLBitSpectralJet_eq_card_bornBefore
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (r : ℕ)
    (hIndependent :
      ∀ order : Fin r,
        LinearIndependent ℚ
          (lbitBirthLayerCoefficient
            birthOrder J order)) :
    temporalDimension
        (scaledLBitSpectralJet birthOrder J) r =
      (lbitSupportsBornBefore I birthOrder r).card := by
  rw [temporalDimension_scaledLBitSpectralJet_eq_sum_layerRank]
  rw [card_lbitSupportsBornBefore_eq_sum_layers]
  apply Finset.sum_congr rfl
  intro order horder
  unfold lbitBirthLayerRank
  exact finrank_span_eq_card (hIndependent order)

/-- Geometric birth order of a finite support: its largest pairwise lattice
distance.  Empty and singleton supports have birth order zero. -/
def lbitSupportDiameterBirthOrder
    {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  S.sup fun i =>
    S.sup fun j => Nat.dist i.val j.val

/-- Every pairwise distance is bounded by the geometric birth order. -/
theorem pairwiseDistance_le_lbitSupportDiameterBirthOrder
    {n : ℕ} {S : Finset (Fin n)}
    {i j : Fin n} (hi : i ∈ S) (hj : j ∈ S) :
    Nat.dist i.val j.val ≤
      lbitSupportDiameterBirthOrder S := by
  have hinner :
      Nat.dist i.val j.val ≤
        S.sup (fun k => Nat.dist i.val k.val) :=
    Finset.le_sup (f := fun k => Nat.dist i.val k.val) hj
  have houter :
      S.sup (fun k => Nat.dist i.val k.val) ≤
        S.sup
          (fun k =>
            S.sup (fun l => Nat.dist k.val l.val)) :=
    Finset.le_sup
      (f := fun k =>
        S.sup (fun l => Nat.dist k.val l.val)) hi
  exact hinner.trans houter

/-- Every support born below geometric resolution `r` has physical range at
most `r`, hence belongs to the existing range-`r` locality family. -/
theorem lbitSupportsBornBefore_diameter_subset_geometric
    (n r : ℕ) :
    lbitSupportsBornBefore
        (Fin n) lbitSupportDiameterBirthOrder r ⊆
      lbitGeometricSupports n r := by
  intro S hS
  have hdata := mem_lbitSupportsBornBefore.mp hS
  rw [mem_lbitGeometricSupports]
  refine ⟨hdata.1, ?_⟩
  intro i hi j hj
  exact
    (pairwiseDistance_le_lbitSupportDiameterBirthOrder hi hj).trans
      (Nat.le_of_lt hdata.2)

/-- **Dimension-linear geometric birth ceiling.** The number of supports
visible below diameter resolution `r` is at most `n * 2^(r+1)`. -/
theorem card_lbitSupportsBornBefore_diameter_le_linear
    (n r : ℕ) :
    (lbitSupportsBornBefore
        (Fin n) lbitSupportDiameterBirthOrder r).card ≤
      n * 2 ^ (r + 1) := by
  exact
    (Finset.card_le_card
      (lbitSupportsBornBefore_diameter_subset_geometric n r)).trans
      (card_lbitGeometricSupports_le_linear n r)

/-- **Unconditional dimension-linear geometric birth ceiling.** For every
coefficient family, diameter birth resolution `r` has temporal dimension at
most `n * 2^(r+1)`. -/
theorem temporalDimension_diameterScaledLBitSpectralJet_le_linear_unconditional
    (n r : ℕ) (J : Finset (Fin n) → ℝ) :
    temporalDimension
        (scaledLBitSpectralJet
          lbitSupportDiameterBirthOrder J) r ≤
      n * 2 ^ (r + 1) := by
  exact
    (temporalDimension_scaledLBitSpectralJet_le_card_bornBefore
      lbitSupportDiameterBirthOrder J r).trans
      (card_lbitSupportsBornBefore_diameter_le_linear n r)

/-- **Resolved observer-time ceiling for a geometrically scaled l-bit
spectrum.** Under layerwise rational independence, diameter birth resolution
`r` sees exactly the below-scale supports and its temporal dimension obeys
the explicit dimension-linear ceiling. -/
theorem temporalDimension_diameterScaledLBitSpectralJet_le_linear
    (n r : ℕ) (J : Finset (Fin n) → ℝ)
    (hIndependent :
      ∀ order : Fin r,
        LinearIndependent ℚ
          (lbitBirthLayerCoefficient
            lbitSupportDiameterBirthOrder J order)) :
    temporalDimension
        (scaledLBitSpectralJet
          lbitSupportDiameterBirthOrder J) r ≤
      n * 2 ^ (r + 1) := by
  rw [temporalDimension_scaledLBitSpectralJet_eq_card_bornBefore
    lbitSupportDiameterBirthOrder J r hIndependent]
  exact card_lbitSupportsBornBefore_diameter_le_linear n r

end

end GaloisForLFunctions.HTGeometry
