import GaloisForLFunctions.HTGeometry.BaseGaugeDifferentialIndependence
import GaloisForLFunctions.HTGeometry.DifferentialAdjoinPairClassification

/-!
# Affine base-jet gauge invariance

This module joins three gauge interfaces.  A family may be rescaled coordinatewise by nonzero
elements of the differential base field and then shifted by any correction whose complete jet
sequence remains in that base.  The combined operation preserves both the embedded differential
field and, for finite palettes, differential independence.

The Prop-valued relation below contains literal affine base gauges, arbitrary base-jet
translations, and both alternatives of `SignedBaseJetEquivalentFamilies`.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- Adding a correction whose complete jet family lies in the base field preserves differential
independence in both directions. -/
theorem differentialIndependent_addOfJetsInBase_iff
    {F K ι : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (x c : ι → K)
    (hc : ∀ i n, ∃ b : F, differentialJet n (c i) = algebraMap F K b) :
    DifferentialIndependent F (fun i ↦ x i + c i) ↔
      DifferentialIndependent F x := by
  constructor
  · intro h
    have hcneg : ∀ i n, ∃ b : F,
        differentialJet n (-c i) = algebraMap F K b := by
      intro i n
      obtain ⟨b, hb⟩ := hc i n
      exact ⟨-b, by rw [differentialJet_neg_apply, hb, map_neg]⟩
    have h' := h.addOfJetsInBase hcneg
    simpa only [add_neg_cancel_right] using h'
  · exact fun h ↦ h.addOfJetsInBase hc

/-- A coordinatewise rescaling by nonzero elements of the differential base field leaves the
embedded generated differential field unchanged. -/
theorem differentialAdjoin_range_mulBase_eq
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    (x : ι → K) (a : ι → F) (ha : ∀ i, a i ≠ 0) :
    differentialAdjoin F (Set.range fun i ↦ algebraMap F K (a i) * x i) =
      differentialAdjoin F (Set.range x) := by
  apply le_antisymm
  · apply differentialAdjoin_le F
    · rintro _ ⟨i, rfl⟩
      exact (differentialAdjoin F (Set.range x)).mul_mem
        ((differentialAdjoin F (Set.range x)).algebraMap_mem (a i))
        (subset_differentialAdjoin F (Set.range x) (Set.mem_range_self i))
    · exact derivationClosed_differentialAdjoin F (Set.range x)
  · apply differentialAdjoin_le F
    · rintro _ ⟨i, rfl⟩
      let L := differentialAdjoin F
        (Set.range fun i ↦ algebraMap F K (a i) * x i)
      have hscaled : algebraMap F K (a i) * x i ∈ L :=
        subset_differentialAdjoin F _ (Set.mem_range_self i)
      have hinv : algebraMap F K (a i)⁻¹ ∈ L := L.algebraMap_mem (a i)⁻¹
      have hmul := L.mul_mem hinv hscaled
      change x i ∈ L
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (ha i), map_one, one_mul] at hmul
      exact hmul
    · exact derivationClosed_differentialAdjoin F
        (Set.range fun i ↦ algebraMap F K (a i) * x i)

/-- Differential independence is preserved by coordinatewise nonzero differential-base
rescaling, with no finiteness assumption on the palette. -/
theorem DifferentialIndependent.mulBase
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    {x : ι → K} (hx : DifferentialIndependent F x)
    (a : ι → F) (ha : ∀ i, a i ≠ 0) :
    DifferentialIndependent F (fun i ↦ algebraMap F K (a i) * x i) := by
  classical
  unfold DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  let s : Set ι := Prod.fst '' t
  have hs : s.Finite := ht.image Prod.fst
  letI : Fintype s := hs.fintype
  letI : DecidableEq s := Classical.decEq s
  let xs : s → K := fun i ↦ x i
  let as : s → F := fun i ↦ a i
  have hxs : DifferentialIndependent F xs :=
    hx.comp ((↑) : s → ι) Subtype.val_injective
  have has : ∀ i, as i ≠ 0 := fun i ↦ ha i
  have hscaled : DifferentialIndependent F
      (fun i : s ↦ algebraMap F K (as i) * xs i) :=
    (HTGeometry.differentialIndependent_mulBase_iff xs as has).2 hxs
  let e : t → s × ℕ := fun p ↦
    (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩, p.1.2)
  have he : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : s × ℕ ↦ ((z.1 : ι), z.2)) hpq
  unfold DifferentialIndependent at hscaled
  simpa only [Function.comp_apply, e, as, xs] using hscaled.comp e he

/-- Arbitrary coordinatewise nonzero rescaling by the differential base preserves differential
independence in both directions. -/
theorem differentialIndependent_mulBase_iff
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    (x : ι → K) (a : ι → F) (ha : ∀ i, a i ≠ 0) :
    DifferentialIndependent F (fun i ↦ algebraMap F K (a i) * x i) ↔
      DifferentialIndependent F x := by
  constructor
  · intro h
    have h' := h.mulBase (fun i ↦ (a i)⁻¹) (fun i ↦ inv_ne_zero (ha i))
    have hfun :
        (fun i ↦ algebraMap F K (a i)⁻¹ *
          (algebraMap F K (a i) * x i)) = x := by
      funext i
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (ha i), map_one, one_mul]
    rw [hfun] at h'
    exact h'
  · exact fun h ↦ h.mulBase a ha

/-- The full coordinatewise affine base gauge preserves differential independence for an
arbitrary palette. -/
theorem differentialIndependent_affineBase_iff
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    (x : ι → K) (a b : ι → F) (ha : ∀ i, a i ≠ 0) :
    DifferentialIndependent F
        (fun i ↦ algebraMap F K (a i) * x i + algebraMap F K (b i)) ↔
      DifferentialIndependent F x := by
  rw [differentialIndependent_addBase_iff
    (fun i ↦ algebraMap F K (a i) * x i) b]
  exact differentialIndependent_mulBase_iff x a ha

/-- In a differential extension, requiring all jets of a value to lie in the base is equivalent
to requiring only the value itself to lie in the base. -/
theorem differentialJetsInBase_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K] (c : K) :
    (∀ n, ∃ b : F, differentialJet n c = algebraMap F K b) ↔
      ∃ b : F, c = algebraMap F K b := by
  constructor
  · intro h
    simpa using h 0
  · rintro ⟨b, rfl⟩ n
    exact ⟨differentialJet n b, differentialJet_algebraMap_apply n b⟩

/-- `y` is an affine base-jet gauge of `x` when its linear coefficient is a nonzero base-field
element in every coordinate and the complete jet of the remaining correction lies in the base. -/
def AffineBaseJetEquivalentFamilies
    (F : Type*) {K ι : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (x y : ι → K) : Prop :=
  ∃ a : ι → F, (∀ i, a i ≠ 0) ∧
    ∀ i n, ∃ b : F,
      differentialJet n (y i - algebraMap F K (a i) * x i) = algebraMap F K b

/-- Signed base-jet equivalence is a special case of affine base-jet equivalence. -/
theorem SignedBaseJetEquivalentFamilies.affineBaseJetEquivalentFamilies
    {F K ι : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    {x y : ι → K} (hxy : SignedBaseJetEquivalentFamilies F x y) :
    AffineBaseJetEquivalentFamilies F x y := by
  rcases hxy with hsub | hadd
  · refine ⟨fun _ ↦ 1, fun _ ↦ one_ne_zero, ?_⟩
    intro i n
    obtain ⟨b, hb⟩ := hsub i n
    refine ⟨-b, ?_⟩
    simp only [map_one, one_mul]
    have hneg : y i - x i = -(x i - y i) := by ring
    rw [hneg, differentialJet_neg_apply, hb, map_neg]
  · refine ⟨fun _ ↦ -1, fun _ ↦ neg_ne_zero.mpr one_ne_zero, ?_⟩
    intro i n
    simpa [sub_eq_add_neg, add_comm] using hadd i n

/-- A literal coordinatewise affine gauge over the differential base is affine base-jet
equivalent. -/
theorem affineBaseJetEquivalentFamilies_affineBase
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    (x : ι → K) (a b : ι → F) (ha : ∀ i, a i ≠ 0) :
    AffineBaseJetEquivalentFamilies F x
      (fun i ↦ algebraMap F K (a i) * x i + algebraMap F K (b i)) := by
  refine ⟨a, ha, ?_⟩
  intro i n
  refine ⟨differentialJet n (b i), ?_⟩
  rw [add_sub_cancel_left, differentialJet_algebraMap_apply]

/-- Over a differential base, affine base-jet equivalence is exactly an order-zero affine value
relation; its all-jet Prop interface carries no additional hypothesis. -/
theorem affineBaseJetEquivalentFamilies_iff
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    (x y : ι → K) :
    AffineBaseJetEquivalentFamilies F x y ↔
      ∃ a b : ι → F, (∀ i, a i ≠ 0) ∧
        ∀ i, y i = algebraMap F K (a i) * x i + algebraMap F K (b i) := by
  constructor
  · rintro ⟨a, ha, hbase⟩
    choose b hb using fun i ↦
      (differentialJetsInBase_iff
        (y i - algebraMap F K (a i) * x i)).1 (hbase i)
    refine ⟨a, b, ha, ?_⟩
    intro i
    calc
      y i = algebraMap F K (a i) * x i +
          (y i - algebraMap F K (a i) * x i) := by ring
      _ = algebraMap F K (a i) * x i + algebraMap F K (b i) := by rw [hb i]
  · rintro ⟨a, b, ha, hy⟩
    rw [funext hy]
    exact affineBaseJetEquivalentFamilies_affineBase x a b ha

/-- Affine base-jet equivalence is reflexive. -/
theorem affineBaseJetEquivalentFamilies_refl
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K] (x : ι → K) :
    AffineBaseJetEquivalentFamilies F x x := by
  apply (affineBaseJetEquivalentFamilies_iff x x).2
  exact ⟨fun _ ↦ 1, fun _ ↦ 0, fun _ ↦ one_ne_zero, fun _ ↦ by simp⟩

/-- Affine base-jet equivalence is symmetric. -/
theorem affineBaseJetEquivalentFamilies_symm
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    {x y : ι → K} (hxy : AffineBaseJetEquivalentFamilies F x y) :
    AffineBaseJetEquivalentFamilies F y x := by
  obtain ⟨a, b, ha, hy⟩ := (affineBaseJetEquivalentFamilies_iff x y).1 hxy
  apply (affineBaseJetEquivalentFamilies_iff y x).2
  refine ⟨fun i ↦ (a i)⁻¹, fun i ↦ -(a i)⁻¹ * b i,
    fun i ↦ inv_ne_zero (ha i), ?_⟩
  intro i
  rw [hy i]
  simp only [map_mul, map_neg]
  have hcoeff :
      algebraMap F K (a i)⁻¹ * algebraMap F K (a i) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (ha i), map_one]
  calc
    x i = (algebraMap F K (a i)⁻¹ * algebraMap F K (a i)) * x i := by
      rw [hcoeff, one_mul]
    _ = algebraMap F K (a i)⁻¹ *
          (algebraMap F K (a i) * x i + algebraMap F K (b i)) +
        -algebraMap F K (a i)⁻¹ * algebraMap F K (b i) := by ring

/-- Affine base-jet equivalence is transitive. -/
theorem affineBaseJetEquivalentFamilies_trans
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    {x y z : ι → K}
    (hxy : AffineBaseJetEquivalentFamilies F x y)
    (hyz : AffineBaseJetEquivalentFamilies F y z) :
    AffineBaseJetEquivalentFamilies F x z := by
  obtain ⟨a, b, ha, hy⟩ := (affineBaseJetEquivalentFamilies_iff x y).1 hxy
  obtain ⟨c, d, hc, hz⟩ := (affineBaseJetEquivalentFamilies_iff y z).1 hyz
  apply (affineBaseJetEquivalentFamilies_iff x z).2
  refine ⟨fun i ↦ c i * a i, fun i ↦ c i * b i + d i,
    fun i ↦ mul_ne_zero (hc i) (ha i), ?_⟩
  intro i
  rw [hz i, hy i, map_mul, map_add, map_mul]
  ring

/-- The quotient relation of families modulo coordinatewise invertible affine differential-base
gauge. -/
def affineBaseJetEquivalentFamiliesSetoid
    (F K ι : Type*) [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K] : Setoid (ι → K) where
  r := AffineBaseJetEquivalentFamilies F
  iseqv := {
    refl := affineBaseJetEquivalentFamilies_refl
    symm := affineBaseJetEquivalentFamilies_symm
    trans := affineBaseJetEquivalentFamilies_trans
  }

/-- Affine base-jet equivalent families generate the same embedded differential field. -/
theorem differentialAdjoin_range_eq_of_affineBaseJetEquivalentFamilies
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    (x y : ι → K) (hxy : AffineBaseJetEquivalentFamilies F x y) :
    differentialAdjoin F (Set.range y) = differentialAdjoin F (Set.range x) := by
  obtain ⟨a, ha, hbase⟩ := hxy
  calc
    differentialAdjoin F (Set.range y) =
        differentialAdjoin F (Set.range fun i ↦ algebraMap F K (a i) * x i) :=
      differentialAdjoin_range_eq_of_sub_jetsInBase y
        (fun i ↦ algebraMap F K (a i) * x i) hbase
    _ = differentialAdjoin F (Set.range x) :=
      differentialAdjoin_range_mulBase_eq x a ha

/-- The full coordinatewise affine base gauge leaves the embedded generated differential field
unchanged. -/
theorem differentialAdjoin_range_affineBase_eq
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    (x : ι → K) (a b : ι → F) (ha : ∀ i, a i ≠ 0) :
    differentialAdjoin F
        (Set.range fun i ↦ algebraMap F K (a i) * x i + algebraMap F K (b i)) =
      differentialAdjoin F (Set.range x) :=
  differentialAdjoin_range_eq_of_affineBaseJetEquivalentFamilies x _
    (affineBaseJetEquivalentFamilies_affineBase x a b ha)

/-- On a finite palette, affine base-jet equivalence preserves differential independence in both
directions. -/
theorem differentialIndependent_iff_of_affineBaseJetEquivalentFamilies
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    (x y : ι → K) (hxy : AffineBaseJetEquivalentFamilies F x y) :
    DifferentialIndependent F y ↔ DifferentialIndependent F x := by
  obtain ⟨a, b, ha, hy⟩ := (affineBaseJetEquivalentFamilies_iff x y).1 hxy
  rw [funext hy]
  exact differentialIndependent_affineBase_iff x a b ha

end

end GaloisForLFunctions
