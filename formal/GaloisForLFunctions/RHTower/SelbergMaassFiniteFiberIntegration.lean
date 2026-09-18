import GaloisForLFunctions.RHTower.MaassRationalHeckeFiberTrace
import GaloisForLFunctions.RHTower.SelbergMaassRationalConjugateTrace
import GaloisForLFunctions.RHTower.SelbergMaassMackeyTraceComposition
import GaloisForLFunctions.HTGeometry.PencilCauchySchwarz
import GaloisForLFunctions.HTGeometry.L2PairingEnergy

/-!
# Finite-fibre integration for the rational Maass correspondence

The common cover of the rational-conjugate quotient has a selector which is the
almost-everywhere disjoint finite union of right translates of the rational
selector.  This file turns that selector decomposition into an integral formula.

The result is deliberately stated before passing to `Lp` equivalence classes:
it is the exact measure-theoretic identity required to prove that the raw finite
fibre trace descends to a bounded operator on quotient `L²`.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter UpperHalfPlane
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise Function

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Haar integration over a right translate is integration after right
translation of the integrand. -/
private theorem setIntegral_rightTranslate (q : SL2R) (S : Set SL2R)
    (hS : MeasurableSet S) (φ : SL2R → E) :
    (∫ x in MulOpposite.op q • S, φ x ∂realSL2Haar) =
      ∫ x in S, φ (x * q) ∂realSL2Haar := by
  have hpre : (fun x : SL2R => x * q) ⁻¹' (MulOpposite.op q • S) = S := by
    ext x
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
    change x * q * q⁻¹ ∈ S ↔ x ∈ S
    simp
  have hpres : MeasurePreserving (fun x : SL2R => x * q)
      (realSL2Haar.restrict S) (realSL2Haar.restrict (MulOpposite.op q • S)) := by
    have h := (realSL2Haar_rightTranslation q).restrict_preimage
      (hS.const_smul (MulOpposite.op q))
    rw [hpre] at h
    exact h
  exact (hpres.integral_comp (MeasurableEquiv.mulRight q).measurableEmbedding φ).symm

/-- Integrating over the common-cover selector equals integrating the complete
finite fibre over the rational-conjugate selector.  This is the selector-level
disintegration identity for the non-normal rational Hecke correspondence. -/
theorem setIntegral_rationalConjugateFiniteCoverFundamentalSet_eq_fiberSum
    (N : ℕ) (g : GL (Fin 2) ℚ) (φ : SL2R → E)
    (hφ : IntegrableOn φ (rationalConjugateFiniteCoverFundamentalSet N g) realSL2Haar) :
    (∫ x in rationalConjugateFiniteCoverFundamentalSet N g, φ x ∂realSL2Haar) =
      ∫ x in rationalConjugateSL2FundamentalSet N g,
        ∑ c : (rationalConjugateSL2Group N g) ⧸
          (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g),
          φ (x * c.out.val) ∂realSL2Haar := by
  let D := (rationalConjugateSL2Group N g) ⧸
    (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)
  letI : Fintype D := Fintype.ofFinite _
  let S := rationalConjugateSL2FundamentalSet N g
  have hsum : HasSum (fun c : D =>
      ∫ x in MulOpposite.op c.out.val • S, φ x ∂realSL2Haar)
      (∫ x in ⋃ c : D, MulOpposite.op c.out.val • S, φ x ∂realSL2Haar) := by
    apply hasSum_integral_iUnion_ae
    · intro c
      exact (rationalConjugateSL2FundamentalSet_measurable N g).const_smul _ |>.nullMeasurableSet
    · intro c d hcd
      exact rationalConjugateFiniteCoverFundamentalSet_aedisjoint N g hcd
    · simpa only [rationalConjugateFiniteCoverFundamentalSet, S] using hφ
  have hterm : ∀ c : D,
      IntegrableOn (fun x => φ (x * c.out.val)) S realSL2Haar := by
    intro c
    have hsub : MulOpposite.op c.out.val • S ⊆
        rationalConjugateFiniteCoverFundamentalSet N g := by
      rw [rationalConjugateFiniteCoverFundamentalSet]
      exact Set.subset_iUnion (fun c : D => MulOpposite.op c.out.val • S) c
    have htrans : Integrable φ
        (realSL2Haar.restrict (MulOpposite.op c.out.val • S)) :=
      (hφ.mono_set hsub).integrable
    have hpre : (fun x : SL2R => x * c.out.val) ⁻¹'
        (MulOpposite.op c.out.val • S) = S := by
      ext x
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
      change x * c.out.val * c.out.val⁻¹ ∈ S ↔ x ∈ S
      simp
    have hpres : MeasurePreserving (fun x : SL2R => x * c.out.val)
        (realSL2Haar.restrict S)
        (realSL2Haar.restrict (MulOpposite.op c.out.val • S)) := by
      have h := (realSL2Haar_rightTranslation c.out.val).restrict_preimage
        ((rationalConjugateSL2FundamentalSet_measurable N g).const_smul
          (MulOpposite.op c.out.val))
      rw [hpre] at h
      exact h
    exact (hpres.integrable_comp htrans.aestronglyMeasurable).mpr htrans
  calc
    (∫ x in rationalConjugateFiniteCoverFundamentalSet N g, φ x ∂realSL2Haar) =
        ∑' c : D, ∫ x in MulOpposite.op c.out.val • S, φ x ∂realSL2Haar := by
          simpa only [rationalConjugateFiniteCoverFundamentalSet, S] using hsum.tsum_eq.symm
    _ = ∑ c : D, ∫ x in MulOpposite.op c.out.val • S, φ x ∂realSL2Haar := tsum_fintype _
    _ = ∑ c : D, ∫ x in S, φ (x * c.out.val) ∂realSL2Haar := by
      apply Finset.sum_congr rfl
      intro c hc
      exact setIntegral_rightTranslate c.out.val S
        (rationalConjugateSL2FundamentalSet_measurable N g) φ
    _ = ∫ x in S, ∑ c : D, φ (x * c.out.val) ∂realSL2Haar := by
      symm
      apply integral_finsetSum
      intro c hc
      exact (hterm c).integrable

/-- The raw finite-fibre trace is measurable whenever its common-cover input is
strongly measurable. -/
theorem rationalHeckeConjugateFiberTrace_measurable_of_stronglyMeasurable
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : SL2R ⧸ rationalHeckeCommonCoverReal N g → ℂ)
    (hf : StronglyMeasurable f) :
    Measurable (rationalHeckeConjugateFiberTrace N g f) := by
  rw [QuotientGroup.measurable_from_quotient]
  change Measurable (fun a : SL2R =>
    ∑ c : (rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g),
      f (RHTower.deningerFiberMap (H := rationalHeckeCommonCoverReal N g) a c))
  exact (Finset.stronglyMeasurable_fun_sum Finset.univ fun c _ =>
    hf.comp_measurable (rationalHeckeConjugateFiberCoordinate_continuous N g c).measurable).measurable

/-- The finite-fibre trace respects equality almost everywhere for strongly
measurable representatives.  Hence it has a well-defined action on the
measurable representatives of quotient `L²` classes. -/
theorem rationalHeckeConjugateFiberTrace_congr_ae_of_stronglyMeasurable
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (f h : SL2R ⧸ rationalHeckeCommonCoverReal N g → ℂ)
    (hf : StronglyMeasurable f) (hh : StronglyMeasurable h)
    (hfh : f =ᵐ[integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)] h) :
    rationalHeckeConjugateFiberTrace N g f =ᵐ[rationalConjugateSL2QuotientMeasure N g]
      rationalHeckeConjugateFiberTrace N g h := by
  let K := rationalHeckeCommonCoverReal N g
  let R := rationalConjugateSL2Group N g
  let D := R ⧸ K.subgroupOf R
  letI : Fintype D := Fintype.ofFinite _
  let S := rationalConjugateSL2FundamentalSet N g
  let FC := rationalConjugateFiniteCoverFundamentalSet N g
  let πK : SL2R → SL2R ⧸ K := QuotientGroup.mk
  let πR : SL2R → SL2R ⧸ R := QuotientGroup.mk
  have hπK : Measurable πK := QuotientGroup.measurable_coe
  have hπR : Measurable πR := QuotientGroup.measurable_coe
  have hPmeas : MeasurableSet {x : SL2R | f (πK x) = h (πK x)} :=
    measurableSet_eq_fun (hf.measurable.comp hπK) (hh.measurable.comp hπK)
  have hQmeas : MeasurableSet {x : SL2R ⧸ K | f x = h x} :=
    measurableSet_eq_fun hf.measurable hh.measurable
  have hsource : ∀ᵐ x ∂realSL2Haar.restrict FC, f (πK x) = h (πK x) := by
    rw [integralSubgroupQuotientMeasure_eq_map_rationalConjugateFiniteCoverFundamentalSet N g] at hfh
    exact (ae_map_iff hπK.aemeasurable hQmeas).mp hfh
  have hcoordinate : ∀ c : D,
      ∀ᵐ x ∂realSL2Haar.restrict S, f (πK (x * c.out.val)) = h (πK (x * c.out.val)) := by
    intro c
    have hsub : MulOpposite.op c.out.val • S ⊆ FC := by
      change MulOpposite.op c.out.val • rationalConjugateSL2FundamentalSet N g ⊆
        rationalConjugateFiniteCoverFundamentalSet N g
      rw [rationalConjugateFiniteCoverFundamentalSet]
      exact Set.subset_iUnion (fun c : D =>
        MulOpposite.op c.out.val • rationalConjugateSL2FundamentalSet N g) c
    have htrans : ∀ᵐ x ∂realSL2Haar.restrict (MulOpposite.op c.out.val • S),
        f (πK x) = h (πK x) :=
      (ae_mono (Measure.restrict_mono hsub le_rfl)) hsource
    have hpre : (fun x : SL2R => x * c.out.val) ⁻¹'
        (MulOpposite.op c.out.val • S) = S := by
      ext x
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
      change x * c.out.val * c.out.val⁻¹ ∈ S ↔ x ∈ S
      simp
    have hpres : MeasurePreserving (fun x : SL2R => x * c.out.val)
        (realSL2Haar.restrict S)
        (realSL2Haar.restrict (MulOpposite.op c.out.val • S)) := by
      have hpres0 := (realSL2Haar_rightTranslation c.out.val).restrict_preimage
        ((rationalConjugateSL2FundamentalSet_measurable N g).const_smul
          (MulOpposite.op c.out.val))
      rw [hpre] at hpres0
      exact hpres0
    have hpull : ∀ᵐ x ∂realSL2Haar.restrict S,
        f (πK (x * c.out.val)) = h (πK (x * c.out.val)) := by
      apply (ae_map_iff hpres.measurable.aemeasurable hPmeas).mp
      rw [hpres.map_eq]
      exact htrans
    exact hpull
  have hall : ∀ᵐ x ∂realSL2Haar.restrict S,
      ∀ c : D, f (πK (x * c.out.val)) = h (πK (x * c.out.val)) :=
    ae_all_iff.mpr hcoordinate
  have htf : Measurable (rationalHeckeConjugateFiberTrace N g f) :=
    rationalHeckeConjugateFiberTrace_measurable_of_stronglyMeasurable N g f hf
  have hth : Measurable (rationalHeckeConjugateFiberTrace N g h) :=
    rationalHeckeConjugateFiberTrace_measurable_of_stronglyMeasurable N g h hh
  have hTmeas : MeasurableSet {x : SL2R ⧸ R |
      rationalHeckeConjugateFiberTrace N g f x = rationalHeckeConjugateFiberTrace N g h x} :=
    measurableSet_eq_fun htf hth
  change ∀ᵐ y ∂Measure.map πR (realSL2Haar.restrict S),
    rationalHeckeConjugateFiberTrace N g f y = rationalHeckeConjugateFiberTrace N g h y
  apply (ae_map_iff hπR.aemeasurable hTmeas).mpr
  filter_upwards [hall] with x hx
  rw [rationalHeckeConjugateFiberTrace_mk, rationalHeckeConjugateFiberTrace_mk]
  apply Finset.sum_congr rfl
  intro c hc
  rw [rationalHeckeConjugateFiberCoordinate_eq_mk_out]
  exact hx c

/-- The non-normal finite-fibre trace carries every strongly measurable common-cover
`L²` function to the rational-conjugate quotient `L²` space. -/
theorem rationalHeckeConjugateFiberTrace_memLp_of_stronglyMeasurable
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : SL2R ⧸ rationalHeckeCommonCoverReal N g → ℂ)
    (hf : StronglyMeasurable f)
    (hLf : MemLp f 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))) :
    MemLp (rationalHeckeConjugateFiberTrace N g f) 2
      (rationalConjugateSL2QuotientMeasure N g) := by
  let K := rationalHeckeCommonCoverReal N g
  let R := rationalConjugateSL2Group N g
  let D := R ⧸ K.subgroupOf R
  letI : Fintype D := Fintype.ofFinite _
  let S := rationalConjugateSL2FundamentalSet N g
  let FC := rationalConjugateFiniteCoverFundamentalSet N g
  let πK : SL2R → SL2R ⧸ K := QuotientGroup.mk
  let πR : SL2R → SL2R ⧸ R := QuotientGroup.mk
  have hπK : Measurable πK := QuotientGroup.measurable_coe
  have hπR : Measurable πR := QuotientGroup.measurable_coe
  have htraceMeas : AEStronglyMeasurable (rationalHeckeConjugateFiberTrace N g f)
      (rationalConjugateSL2QuotientMeasure N g) :=
    (rationalHeckeConjugateFiberTrace_measurable_of_stronglyMeasurable N g f hf).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm htraceMeas]
  have hπKpres : MeasurePreserving πK (realSL2Haar.restrict FC)
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) := by
    rw [integralSubgroupQuotientMeasure_eq_map_rationalConjugateFiniteCoverFundamentalSet N g]
    exact ⟨hπK, rfl⟩
  have hπRpres : MeasurePreserving πR (realSL2Haar.restrict S)
      (rationalConjugateSL2QuotientMeasure N g) := by
    change MeasurePreserving (QuotientGroup.mk : SL2R → SL2R ⧸ rationalConjugateSL2Group N g)
      (realSL2Haar.restrict (rationalConjugateSL2FundamentalSet N g))
      (rationalConjugateSL2QuotientMeasure N g)
    exact (rationalConjugateSL2FundamentalSet_isFundamentalDomain N g).measurePreserving_quotient_mk _
  have hfsq : Integrable (fun x => ‖f x‖ ^ 2)
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) :=
    (memLp_two_iff_integrable_sq_norm hLf.aestronglyMeasurable).mp hLf
  have hsourceSq : Integrable (fun x => ‖f (πK x)‖ ^ 2)
      (realSL2Haar.restrict FC) :=
    (hπKpres.integrable_comp hfsq.aestronglyMeasurable).mpr hfsq
  have hfiberSq : ∀ c : D,
      Integrable (fun x => ‖f (πK (x * c.out.val))‖ ^ 2)
        (realSL2Haar.restrict S) := by
    intro c
    have hsub : MulOpposite.op c.out.val • S ⊆ FC := by
      change MulOpposite.op c.out.val • rationalConjugateSL2FundamentalSet N g ⊆
        rationalConjugateFiniteCoverFundamentalSet N g
      rw [rationalConjugateFiniteCoverFundamentalSet]
      exact Set.subset_iUnion (fun c : D =>
        MulOpposite.op c.out.val • rationalConjugateSL2FundamentalSet N g) c
    have htrans : Integrable (fun x => ‖f (πK x)‖ ^ 2)
        (realSL2Haar.restrict (MulOpposite.op c.out.val • S)) :=
      hsourceSq.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hpre : (fun x : SL2R => x * c.out.val) ⁻¹'
        (MulOpposite.op c.out.val • S) = S := by
      ext x
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
      change x * c.out.val * c.out.val⁻¹ ∈ S ↔ x ∈ S
      simp
    have hpres : MeasurePreserving (fun x : SL2R => x * c.out.val)
        (realSL2Haar.restrict S)
        (realSL2Haar.restrict (MulOpposite.op c.out.val • S)) := by
      have hpres0 := (realSL2Haar_rightTranslation c.out.val).restrict_preimage
        ((rationalConjugateSL2FundamentalSet_measurable N g).const_smul
          (MulOpposite.op c.out.val))
      rw [hpre] at hpres0
      exact hpres0
    exact (hpres.integrable_comp htrans.aestronglyMeasurable).mpr htrans
  have hfiberEnergy : Integrable (fun x =>
      ∑ c : D, ‖f (πK (x * c.out.val))‖ ^ 2) (realSL2Haar.restrict S) :=
    integrable_finsetSum Finset.univ fun c _ => hfiberSq c
  have htraceSqMeas : AEStronglyMeasurable (fun x =>
      ‖rationalHeckeConjugateFiberTrace N g f (πR x)‖ ^ 2)
      (realSL2Haar.restrict S) :=
    ((rationalHeckeConjugateFiberTrace_measurable_of_stronglyMeasurable N g f hf).comp hπR).aestronglyMeasurable.norm.pow 2
  have hpoint : ∀ x : SL2R,
      ‖rationalHeckeConjugateFiberTrace N g f (πR x)‖ ^ 2 ≤
        (Fintype.card D : ℝ) * ∑ c : D, ‖f (πK (x * c.out.val))‖ ^ 2 := by
    intro x
    rw [rationalHeckeConjugateFiberTrace_mk]
    simpa only [rationalHeckeConjugateFiberCoordinate_eq_mk_out] using
      GaloisForLFunctions.HTGeometry.norm_sum_sq_le_card_mul
        (fun c : D => f (RHTower.deningerFiberMap (H := K) x c))
  have htraceSq : Integrable (fun x =>
      ‖rationalHeckeConjugateFiberTrace N g f (πR x)‖ ^ 2)
      (realSL2Haar.restrict S) :=
    hfiberEnergy.const_mul (Fintype.card D : ℝ) |>.mono' htraceSqMeas
      (ae_of_all _ fun x => by
        simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hpoint x)
  exact (hπRpres.integrable_comp (htraceMeas.norm.pow 2)).mp htraceSq

/-- The finite-fibre trace has energy at most the fibre cardinality times the
energy on the common-cover quotient.  This is the quantitative form of the
selector disintegration identity. -/
theorem rationalHeckeConjugateFiberTrace_integral_norm_sq_le_of_stronglyMeasurable
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : SL2R ⧸ rationalHeckeCommonCoverReal N g → ℂ)
    (hf : StronglyMeasurable f)
    (hLf : MemLp f 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))) :
    (∫ y, ‖rationalHeckeConjugateFiberTrace N g f y‖ ^ 2
      ∂rationalConjugateSL2QuotientMeasure N g) ≤
      (Fintype.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) : ℝ) *
        ∫ y, ‖f y‖ ^ 2 ∂integralSubgroupQuotientMeasure
          (rationalHeckeIntegralIntersection N g) := by
  let K := rationalHeckeCommonCoverReal N g
  let R := rationalConjugateSL2Group N g
  let D := R ⧸ K.subgroupOf R
  letI : Fintype D := Fintype.ofFinite _
  let S := rationalConjugateSL2FundamentalSet N g
  let FC := rationalConjugateFiniteCoverFundamentalSet N g
  let πK : SL2R → SL2R ⧸ K := QuotientGroup.mk
  let πR : SL2R → SL2R ⧸ R := QuotientGroup.mk
  have hπK : Measurable πK := QuotientGroup.measurable_coe
  have hπR : Measurable πR := QuotientGroup.measurable_coe
  have hfsq : Integrable (fun x => ‖f x‖ ^ 2)
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) :=
    (memLp_two_iff_integrable_sq_norm hLf.aestronglyMeasurable).mp hLf
  have hπKpres : MeasurePreserving πK (realSL2Haar.restrict FC)
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) := by
    rw [integralSubgroupQuotientMeasure_eq_map_rationalConjugateFiniteCoverFundamentalSet N g]
    exact ⟨hπK, rfl⟩
  have hsourceSq : Integrable (fun x => ‖f (πK x)‖ ^ 2)
      (realSL2Haar.restrict FC) := by
    exact (hπKpres.integrable_comp hfsq.aestronglyMeasurable).mpr hfsq
  have hfiberSq : ∀ c : D,
      Integrable (fun x => ‖f (πK (x * c.out.val))‖ ^ 2)
        (realSL2Haar.restrict S) := by
    intro c
    have hsub : MulOpposite.op c.out.val • S ⊆ FC := by
      change MulOpposite.op c.out.val • rationalConjugateSL2FundamentalSet N g ⊆
        rationalConjugateFiniteCoverFundamentalSet N g
      rw [rationalConjugateFiniteCoverFundamentalSet]
      exact Set.subset_iUnion (fun c : D =>
        MulOpposite.op c.out.val • rationalConjugateSL2FundamentalSet N g) c
    have htrans : Integrable (fun x => ‖f (πK x)‖ ^ 2)
        (realSL2Haar.restrict (MulOpposite.op c.out.val • S)) :=
      hsourceSq.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hpre : (fun x : SL2R => x * c.out.val) ⁻¹'
        (MulOpposite.op c.out.val • S) = S := by
      ext x
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
      change x * c.out.val * c.out.val⁻¹ ∈ S ↔ x ∈ S
      simp
    have hpres : MeasurePreserving (fun x : SL2R => x * c.out.val)
        (realSL2Haar.restrict S)
        (realSL2Haar.restrict (MulOpposite.op c.out.val • S)) := by
      have hpres0 := (realSL2Haar_rightTranslation c.out.val).restrict_preimage
        ((rationalConjugateSL2FundamentalSet_measurable N g).const_smul
          (MulOpposite.op c.out.val))
      rw [hpre] at hpres0
      exact hpres0
    exact (hpres.integrable_comp htrans.aestronglyMeasurable).mpr htrans
  have hfiberEnergy : Integrable (fun x =>
      ∑ c : D, ‖f (πK (x * c.out.val))‖ ^ 2) (realSL2Haar.restrict S) :=
    integrable_finsetSum Finset.univ fun c _ => hfiberSq c
  have htraceSq : Integrable (fun x =>
      ‖rationalHeckeConjugateFiberTrace N g f (πR x)‖ ^ 2)
      (realSL2Haar.restrict S) := by
    have htraceSqMeas : AEStronglyMeasurable (fun x =>
        ‖rationalHeckeConjugateFiberTrace N g f (πR x)‖ ^ 2)
        (realSL2Haar.restrict S) :=
      ((rationalHeckeConjugateFiberTrace_measurable_of_stronglyMeasurable N g f hf).comp hπR).aestronglyMeasurable.norm.pow 2
    refine hfiberEnergy.const_mul (Fintype.card D : ℝ) |>.mono' htraceSqMeas ?_
    filter_upwards with x
    rw [rationalHeckeConjugateFiberTrace_mk]
    simpa only [rationalHeckeConjugateFiberCoordinate_eq_mk_out,
      Real.norm_of_nonneg (sq_nonneg _)] using
      GaloisForLFunctions.HTGeometry.norm_sum_sq_le_card_mul
        (fun c : D => f (RHTower.deningerFiberMap (H := K) x c))
  have henergyEq :
      (∫ x in FC, ‖f (πK x)‖ ^ 2 ∂realSL2Haar) =
        ∫ x in S, ∑ c : D, ‖f (πK (x * c.out.val))‖ ^ 2 ∂realSL2Haar :=
    setIntegral_rationalConjugateFiniteCoverFundamentalSet_eq_fiberSum N g
      (fun x => ‖f (πK x)‖ ^ 2) hsourceSq
  have hpointIntegral :
      (∫ x in S, ‖rationalHeckeConjugateFiberTrace N g f (πR x)‖ ^ 2
        ∂realSL2Haar) ≤
        ∫ x in S, (Fintype.card D : ℝ) *
          ∑ c : D, ‖f (πK (x * c.out.val))‖ ^ 2 ∂realSL2Haar := by
    apply integral_mono_ae htraceSq (hfiberEnergy.const_mul (Fintype.card D : ℝ))
    filter_upwards with x
    rw [rationalHeckeConjugateFiberTrace_mk]
    simpa only [rationalHeckeConjugateFiberCoordinate_eq_mk_out] using
      GaloisForLFunctions.HTGeometry.norm_sum_sq_le_card_mul
        (fun c : D => f (RHTower.deningerFiberMap (H := K) x c))
  have htraceSqQ : AEStronglyMeasurable (fun y =>
      ‖rationalHeckeConjugateFiberTrace N g f y‖ ^ 2)
      (rationalConjugateSL2QuotientMeasure N g) :=
    (rationalHeckeConjugateFiberTrace_measurable_of_stronglyMeasurable N g f hf).aestronglyMeasurable.norm.pow 2
  calc
    (∫ y, ‖rationalHeckeConjugateFiberTrace N g f y‖ ^ 2
      ∂rationalConjugateSL2QuotientMeasure N g) =
        ∫ x in S, ‖rationalHeckeConjugateFiberTrace N g f (πR x)‖ ^ 2
          ∂realSL2Haar := by
      change (∫ y, ‖rationalHeckeConjugateFiberTrace N g f y‖ ^ 2
        ∂Measure.map πR (realSL2Haar.restrict S)) = _
      rw [integral_map hπR.aemeasurable htraceSqQ]
    _ ≤ ∫ x in S, (Fintype.card D : ℝ) *
          ∑ c : D, ‖f (πK (x * c.out.val))‖ ^ 2 ∂realSL2Haar := hpointIntegral
    _ = (Fintype.card D : ℝ) *
        ∫ x in S, ∑ c : D, ‖f (πK (x * c.out.val))‖ ^ 2 ∂realSL2Haar := by
      rw [integral_const_mul]
    _ = (Fintype.card D : ℝ) *
        (∫ x in FC, ‖f (πK x)‖ ^ 2 ∂realSL2Haar) := by
      rw [henergyEq]
    _ = (Fintype.card D : ℝ) *
        ∫ y, ‖f y‖ ^ 2 ∂integralSubgroupQuotientMeasure
          (rationalHeckeIntegralIntersection N g) := by
      congr 1
      rw [← hπKpres.map_eq]
      exact (integral_map (μ := realSL2Haar.restrict FC) (φ := πK)
        hπK.aemeasurable (hf.norm.pow 2).aestronglyMeasurable).symm

/-- The canonical finite-fibre trace on quotient almost-everywhere functions.
It first replaces the input by its strongly measurable representative, so it
does not depend on an arbitrary raw `Lp` representative. -/
noncomputable def rationalHeckeConjugateFiberTraceAEEqFun (N : ℕ) (g : GL (Fin 2) ℚ) :
    (SL2R ⧸ rationalHeckeCommonCoverReal N g →ₘ[
      integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)] ℂ) →
      (SL2R ⧸ rationalConjugateSL2Group N g →ₘ[
        rationalConjugateSL2QuotientMeasure N g] ℂ) := fun f =>
  AEEqFun.mk
    (rationalHeckeConjugateFiberTrace N g
      (AEStronglyMeasurable.mk f f.aestronglyMeasurable))
    (rationalHeckeConjugateFiberTrace_measurable_of_stronglyMeasurable N g
      (AEStronglyMeasurable.mk f f.aestronglyMeasurable)
      f.aestronglyMeasurable.stronglyMeasurable_mk).aestronglyMeasurable

/-- The quotient-level trace is represented by the literal finite fibre sum of
the canonical strongly measurable input representative. -/
theorem coe_rationalHeckeConjugateFiberTraceAEEqFun (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : SL2R ⧸ rationalHeckeCommonCoverReal N g →ₘ[
      integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)] ℂ) :
    rationalHeckeConjugateFiberTraceAEEqFun N g f =ᵐ[
      rationalConjugateSL2QuotientMeasure N g]
      rationalHeckeConjugateFiberTrace N g
        (AEStronglyMeasurable.mk f f.aestronglyMeasurable) :=
  AEEqFun.coeFn_mk _ _

/-- The canonical quotient-level trace preserves the `L²` condition. -/
theorem rationalHeckeConjugateFiberTraceAEEqFun_memLp
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : SL2R ⧸ rationalHeckeCommonCoverReal N g →ₘ[
      integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)] ℂ)
    (hf : MemLp f 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))) :
    MemLp (rationalHeckeConjugateFiberTraceAEEqFun N g f) 2
      (rationalConjugateSL2QuotientMeasure N g) := by
  have hfMk : MemLp (AEStronglyMeasurable.mk f f.aestronglyMeasurable) 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) :=
    (memLp_congr_ae f.aestronglyMeasurable.ae_eq_mk).mp hf
  have htrace : MemLp (rationalHeckeConjugateFiberTrace N g
      (AEStronglyMeasurable.mk f f.aestronglyMeasurable)) 2
      (rationalConjugateSL2QuotientMeasure N g) :=
    rationalHeckeConjugateFiberTrace_memLp_of_stronglyMeasurable N g
      (AEStronglyMeasurable.mk f f.aestronglyMeasurable)
      f.aestronglyMeasurable.stronglyMeasurable_mk hfMk
  exact (memLp_congr_ae (coe_rationalHeckeConjugateFiberTraceAEEqFun N g f)).mpr htrace

/-- The generic rational finite-fibre trace on quotient `L²` spaces.  Its
representative is the literal trace of the input's canonical strongly measurable
version. -/
noncomputable def rationalHeckeConjugateFiberTraceLp (N : ℕ) (g : GL (Fin 2) ℚ) :
    Lp ℂ 2 (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) →
      Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g) := fun f =>
  (rationalHeckeConjugateFiberTraceAEEqFun_memLp N g f.1 (Lp.memLp f)).toLp
    (rationalHeckeConjugateFiberTraceAEEqFun N g f.1)

/-- The `L²` trace has the literal finite-fibre trace of its input's canonical
strongly measurable representative as an almost-everywhere representative. -/
theorem coe_rationalHeckeConjugateFiberTraceLp (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : Lp ℂ 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))) :
    rationalHeckeConjugateFiberTraceLp N g f =ᵐ[rationalConjugateSL2QuotientMeasure N g]
      rationalHeckeConjugateFiberTrace N g
        (AEStronglyMeasurable.mk f (Lp.aestronglyMeasurable f)) := by
  exact (MemLp.coeFn_toLp
    (rationalHeckeConjugateFiberTraceAEEqFun_memLp N g f.1 (Lp.memLp f))).trans
      (coe_rationalHeckeConjugateFiberTraceAEEqFun N g f.1)

/-- The bounded quotient trace applied to a genuine Maass source on the common
cover. -/
noncomputable def rationalHeckeConjugateFiberTraceSourceLp (N : ℕ) {lam : ℝ}
    (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g) :=
  rationalHeckeConjugateFiberTraceLp N g (rationalHeckeIntegralCoverSourceLp N g f)

/-- On an actual Maass source, the bounded quotient operator has the literal
finite fibre sum as its almost-everywhere representative. -/
theorem coe_rationalHeckeConjugateFiberTraceSourceLp (N : ℕ) {lam : ℝ}
    (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    rationalHeckeConjugateFiberTraceSourceLp N g f =ᵐ[
      rationalConjugateSL2QuotientMeasure N g]
      rationalHeckeConjugateFiberTrace N g
        (rationalHeckeIntegralCoverSourceFunction N g f) := by
  let F := rationalHeckeIntegralCoverSourceLp N g f
  let u := rationalHeckeIntegralCoverSourceFunction N g f
  have hu : StronglyMeasurable u :=
    (rationalHeckeIntegralCoverSourceFunction_continuous N g f).stronglyMeasurable
  have hF : StronglyMeasurable
      (AEStronglyMeasurable.mk F (Lp.aestronglyMeasurable F)) :=
    (Lp.aestronglyMeasurable F).stronglyMeasurable_mk
  have hrepr : AEStronglyMeasurable.mk F (Lp.aestronglyMeasurable F) =ᵐ[
      integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)] u := by
    exact (Lp.aestronglyMeasurable F).ae_eq_mk.symm.trans
      (MemLp.coeFn_toLp (rationalHeckeIntegralCoverSourceFunction_memLp N g f))
  change rationalHeckeConjugateFiberTraceLp N g F =ᵐ[
      rationalConjugateSL2QuotientMeasure N g]
      rationalHeckeConjugateFiberTrace N g u
  exact (coe_rationalHeckeConjugateFiberTraceLp N g F).trans
    (rationalHeckeConjugateFiberTrace_congr_ae_of_stronglyMeasurable N g
      (AEStronglyMeasurable.mk F (Lp.aestronglyMeasurable F)) u hF hu hrepr)

/-- Relative cosets on the determinant-one rational conjugate agree with the
relative cosets in its `GL₂` realization.  This is the group-theoretic index
identification needed to compare the quotient fibre trace with the existing
automorphic finite trace. -/
noncomputable def rationalPrincipalSL2FiberCosetEquiv (N : ℕ) (g : GL (Fin 2) ℚ) :
    (rationalConjugateSL2Group N g) ⧸
      ((realImage (CongruenceSubgroup.Gamma (N + 1))).subgroupOf
        (rationalConjugateSL2Group N g)) ≃
      (rationalConjugateGroup N g) ⧸
        ((principalCongruenceGL N).subgroupOf (rationalConjugateGroup N g)) := by
  let e := rationalConjugateSL2ToGLEquiv N g
  let Psl := realImage (CongruenceSubgroup.Gamma (N + 1))
  let Rsl := rationalConjugateSL2Group N g
  let Pgl := principalCongruenceGL N
  let Rgl := rationalConjugateGroup N g
  have hsub : Subgroup.map e.toMonoidHom (Psl.subgroupOf Rsl) =
      Pgl.subgroupOf Rgl :=
    rationalConjugateSL2_principalIntersection_map_eq N g
  exact Quotient.congr e.toEquiv (by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    have hmem (x : Rsl) : x ∈ Psl.subgroupOf Rsl ↔ e x ∈ Pgl.subgroupOf Rgl := by
      rw [← hsub]
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hey⟩
        exact e.injective hey.symm ▸ hy
    dsimp only [Psl, Rsl, Pgl, Rgl] at hmem
    change a⁻¹ * b ∈ (realImage (CongruenceSubgroup.Gamma (N + 1))).subgroupOf
        (rationalConjugateSL2Group N g) ↔
      (e a)⁻¹ * e b ∈ (principalCongruenceGL N).subgroupOf
        (rationalConjugateGroup N g)
    simpa only [e.map_inv, e.map_mul] using hmem (a⁻¹ * b))

/-- The common-cover subgroup, viewed inside the rational-conjugate `SL₂`
source, is exactly the principal relative-intersection subgroup. -/
theorem rationalHeckeCommonCover_subgroupOf_eq_principal (N : ℕ) (g : GL (Fin 2) ℚ) :
    (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g) =
      (realImage (CongruenceSubgroup.Gamma (N + 1))).subgroupOf
        (rationalConjugateSL2Group N g) := by
  rw [show rationalHeckeCommonCoverReal N g =
      realImage (CongruenceSubgroup.Gamma (N + 1)) ⊓ rationalConjugateSL2Group N g from
        realImage_rationalHeckeIntegralIntersection N g]
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, x.property⟩

/-- The rational-conjugate `SL₂`--`GL₂` equivalence preserves the upper-half
plane action term by term. -/
theorem rationalConjugateSL2ToGLEquiv_smul (N : ℕ) (g : GL (Fin 2) ℚ)
    (c : rationalConjugateSL2Group N g) (z : ℍ) :
    ((rationalConjugateSL2ToGLEquiv N g c : rationalConjugateGroup N g).val) • z =
      c.val • z := by
  change (Matrix.SpecialLinearGroup.toGL c.val) • z = c.val • z
  rw [MulAction.compHom_smul_def]
  rfl

/-- The original principal Maass source is invariant under the actual `GL₂`
common-cover subgroup inside the rational-conjugate source. -/
noncomputable def rationalCommonCoverGLInvariant (N : ℕ) (g : GL (Fin 2) ℚ)
    {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    glUpperHalfPlaneInvariantFunctions
      (principalCongruenceGL N ⊓ rationalConjugateGroup N g) :=
  ⟨f.1.1, by
    intro h z
    let e := rationalConjugateSL2ToGLEquiv N g
    let Psl := realImage (CongruenceSubgroup.Gamma (N + 1))
    let Rsl := rationalConjugateSL2Group N g
    let Pgl := principalCongruenceGL N
    let Rgl := rationalConjugateGroup N g
    let hr : Rgl := ⟨h.val, h.property.2⟩
    let c : Rsl := e.symm hr
    have hsub : Subgroup.map e.toMonoidHom (Psl.subgroupOf Rsl) =
        Pgl.subgroupOf Rgl :=
      rationalConjugateSL2_principalIntersection_map_eq N g
    have hmem (x : Rsl) : x ∈ Psl.subgroupOf Rsl ↔ e x ∈ Pgl.subgroupOf Rgl := by
      rw [← hsub]
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hey⟩
        exact e.injective hey.symm ▸ hy
    have he : e c = hr := e.apply_symm_apply hr
    have hcsub : c ∈ Psl.subgroupOf Rsl := hmem c |>.mpr (by
      rw [he]
      exact h.property.1)
    have hc : c.val ∈ Psl := hcsub
    have hact : h.val • z = c.val • z := by
      rw [← show (e c).val = h.val from by
        change (e c).val = hr.val
        exact congrArg Subtype.val he]
      exact rationalConjugateSL2ToGLEquiv_smul N g c z
    rw [hact]
    exact f.1.2 ⟨c.val, hc⟩ z⟩

/-- The `GL₂` common-cover subgroup has finite relative index in the rational
conjugate source. -/
theorem rationalCommonCoverGL_isFiniteRelIndex (N : ℕ) (g : GL (Fin 2) ℚ) :
    (principalCongruenceGL N ⊓ rationalConjugateGroup N g).IsFiniteRelIndex
      (rationalConjugateGroup N g) := by
  apply Subgroup.IsFiniteRelIndex.mk
  rw [Subgroup.inf_relIndex_right]
  exact (rationalConjugateGroup_commensurable N g).2

/-- The finite `GL₂` Maass trace from the common cover to the rational-conjugate
source. This is the automorphic-side trace to be identified with the bounded
quotient trace. -/
noncomputable def rationalCommonCoverGLTrace (N : ℕ) (g : GL (Fin 2) ℚ)
    {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    glUpperHalfPlaneInvariantFunctions (rationalConjugateGroup N g) := by
  letI : (principalCongruenceGL N ⊓ rationalConjugateGroup N g).IsFiniteRelIndex
      (rationalConjugateGroup N g) := rationalCommonCoverGL_isFiniteRelIndex N g
  exact maassTraceInvariant (G := principalCongruenceGL N ⊓ rationalConjugateGroup N g)
    (H := rationalConjugateGroup N g) (rationalCommonCoverGLInvariant N g f)

/-- Tracing a function already invariant under the target group multiplies it
by the exact finite relative index. -/
theorem maassTraceFunction_restrict_of_targetInvariant
    {G H : Subgroup (GL (Fin 2) ℝ)} [G.IsFiniteRelIndex H]
    (hGH : G ≤ H) (f : glUpperHalfPlaneInvariantFunctions H) :
    maassTraceFunction (G := G) (H := H) (maassInvariantRestrict hGH f) =
      (Nat.card (H ⧸ G.subgroupOf H) : ℂ) • f.1 := by
  funext z
  letI : Fintype (H ⧸ G.subgroupOf H) := Fintype.ofFinite _
  unfold maassTraceFunction
  change (∑ q : H ⧸ G.subgroupOf H,
      maassTraceQuotientFunc (maassInvariantRestrict hGH f) q z) =
    (Nat.card (H ⧸ G.subgroupOf H) : ℂ) • f.1 z
  rw [show (∑ q : H ⧸ G.subgroupOf H,
      maassTraceQuotientFunc (maassInvariantRestrict hGH f) q z) =
      ∑ _q : H ⧸ G.subgroupOf H, f.1 z by
        apply Finset.sum_congr rfl
        intro q _
        induction q using Quotient.inductionOn with
        | h q =>
          rw [maassTraceQuotientFunc_mk]
          change f.1 (q.val⁻¹ • z) = f.1 z
          exact f.2 q⁻¹ z]
  rw [Finset.sum_const, Nat.card_eq_fintype_card, Finset.card_univ,
    Nat.cast_smul_eq_nsmul]

/-- Restrict the rationally pulled principal source to its actual common cover.
Unlike `rationalCommonCoverGLInvariant`, this source includes rational pullback,
so its subsequent return trace is the rational Hecke correspondence. -/
noncomputable def rationalPulledCommonCoverGLInvariant (N : ℕ) (g : GL (Fin 2) ℚ)
    {lam : ℝ} (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) :
    glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N ⊓ rationalConjugateGroup N g) :=
  maassInvariantRestrict inf_le_right (rationalMaassPullbackInvariant N g f)

/-- The finite common-cover trace of the rationally pulled Maass source. -/
noncomputable def rationalPulledCommonCoverGLTrace (N : ℕ) (g : GL (Fin 2) ℚ)
    {lam : ℝ} (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) :
    glUpperHalfPlaneInvariantFunctions (rationalConjugateGroup N g) := by
  letI : (principalCongruenceGL N ⊓ rationalConjugateGroup N g).IsFiniteRelIndex
      (rationalConjugateGroup N g) := rationalCommonCoverGL_isFiniteRelIndex N g
  exact maassTraceInvariant (G := principalCongruenceGL N ⊓ rationalConjugateGroup N g)
    (H := rationalConjugateGroup N g) (rationalPulledCommonCoverGLInvariant N g f)

/-- The pulled common-cover trace is exactly the fibre cardinality times the
rationally pulled source. -/
theorem rationalPulledCommonCoverGLTrace_eq_card_smul_pullback (N : ℕ)
    (g : GL (Fin 2) ℚ) {lam : ℝ}
    (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) :
    (rationalPulledCommonCoverGLTrace N g f).1 =
      (Nat.card ((rationalConjugateGroup N g) ⧸
        ((principalCongruenceGL N ⊓ rationalConjugateGroup N g).subgroupOf
          (rationalConjugateGroup N g))) : ℂ) •
        (rationalMaassPullbackInvariant N g f).1 := by
  letI : (principalCongruenceGL N ⊓ rationalConjugateGroup N g).IsFiniteRelIndex
      (rationalConjugateGroup N g) := rationalCommonCoverGL_isFiniteRelIndex N g
  exact maassTraceFunction_restrict_of_targetInvariant inf_le_right
    (rationalMaassPullbackInvariant N g f)

/-- Returning the pulled common-cover trace to principal level is exactly the
fibre cardinality multiple of the rational principal Hecke trace. -/
theorem rationalPulledCommonCoverGLTrace_then_principal_eq_card_smul
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) {lam : ℝ}
    (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) :
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex
        (principalCongruenceGL N) := rationalConjugateGroup_isFiniteRelIndex N g
    maassTraceFunction (H := principalCongruenceGL N)
      (rationalPulledCommonCoverGLTrace N g f) =
      (Nat.card ((rationalConjugateGroup N g) ⧸
        ((principalCongruenceGL N ⊓ rationalConjugateGroup N g).subgroupOf
          (rationalConjugateGroup N g))) : ℂ) •
        rationalPrincipalTraceFunction N g hg lam f := by
  letI : (principalCongruenceGL N ⊓ rationalConjugateGroup N g).IsFiniteRelIndex
      (rationalConjugateGroup N g) := rationalCommonCoverGL_isFiniteRelIndex N g
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex
      (principalCongruenceGL N) := rationalConjugateGroup_isFiniteRelIndex N g
  have hpulled : rationalPulledCommonCoverGLTrace N g f =
      (Nat.card ((rationalConjugateGroup N g) ⧸
        ((principalCongruenceGL N ⊓ rationalConjugateGroup N g).subgroupOf
          (rationalConjugateGroup N g))) : ℂ) •
        rationalMaassPullbackInvariant N g f := by
    apply Subtype.ext
    exact rationalPulledCommonCoverGLTrace_eq_card_smul_pullback N g f
  rw [hpulled, maassTraceFunction_smul]
  rfl

/-- The preceding correspondence begins at the original principal Maass source,
not merely an abstract `GL₂` vector. -/
theorem rationalPulledCommonCoverGLTrace_source_then_principal_eq_card_smul
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex
        (principalCongruenceGL N) := rationalConjugateGroup_isFiniteRelIndex N g
    maassTraceFunction (H := principalCongruenceGL N)
      (rationalPulledCommonCoverGLTrace N g
        (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f)) =
      (Nat.card ((rationalConjugateGroup N g) ⧸
        ((principalCongruenceGL N ⊓ rationalConjugateGroup N g).subgroupOf
          (rationalConjugateGroup N g))) : ℂ) •
        rationalPrincipalTraceFunction N g hg lam
          (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f) := by
  simpa using rationalPulledCommonCoverGLTrace_then_principal_eq_card_smul N g hg
    (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f)

/-- Relative cosets on the actual rational common cover agree directly with
the cosets used by the common-cover `GL₂` trace. -/
noncomputable def rationalHeckeCommonCoverGLTraceCosetEquiv (N : ℕ) (g : GL (Fin 2) ℚ) :
    (rationalConjugateSL2Group N g) ⧸
      ((rationalHeckeCommonCoverReal N g).subgroupOf
        (rationalConjugateSL2Group N g)) ≃
      (rationalConjugateGroup N g) ⧸
        ((principalCongruenceGL N ⊓ rationalConjugateGroup N g).subgroupOf
          (rationalConjugateGroup N g)) := by
  let e := rationalConjugateSL2ToGLEquiv N g
  let Psl := realImage (CongruenceSubgroup.Gamma (N + 1))
  let Rsl := rationalConjugateSL2Group N g
  let Pgl := principalCongruenceGL N
  let Rgl := rationalConjugateGroup N g
  have hK : (rationalHeckeCommonCoverReal N g).subgroupOf Rsl = Psl.subgroupOf Rsl :=
    rationalHeckeCommonCover_subgroupOf_eq_principal N g
  have hsub : Subgroup.map e.toMonoidHom (Psl.subgroupOf Rsl) =
      Pgl.subgroupOf Rgl :=
    rationalConjugateSL2_principalIntersection_map_eq N g
  exact Quotient.congr e.toEquiv (by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    have hmem (x : Rsl) : x ∈ Psl.subgroupOf Rsl ↔ e x ∈ Pgl.subgroupOf Rgl := by
      rw [← hsub]
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hey⟩
        exact e.injective hey.symm ▸ hy
    dsimp only [Psl, Rsl, Pgl, Rgl] at hmem
    change a⁻¹ * b ∈ (rationalHeckeCommonCoverReal N g).subgroupOf
        (rationalConjugateSL2Group N g) ↔
      (e a)⁻¹ * e b ∈ (principalCongruenceGL N ⊓ rationalConjugateGroup N g).subgroupOf
        (rationalConjugateGroup N g)
    rw [show (e a)⁻¹ * e b = e (a⁻¹ * b) by
      simp only [e.map_inv, e.map_mul]]
    constructor
    · intro hx
      have hx' : e (a⁻¹ * b) ∈ (principalCongruenceGL N).subgroupOf
          (rationalConjugateGroup N g) := hmem (a⁻¹ * b) |>.mp (hK ▸ hx)
      exact ⟨hx', (e (a⁻¹ * b)).property⟩
    · intro hx
      exact hK.symm ▸ (hmem (a⁻¹ * b) |>.mpr hx.1))

 /-- The direct common-cover coset equivalence sends a literal determinant-one
representative to its `GL₂` realization. -/
@[simp] theorem rationalHeckeCommonCoverGLTraceCosetEquiv_mk (N : ℕ) (g : GL (Fin 2) ℚ)
    (c : rationalConjugateSL2Group N g) :
    rationalHeckeCommonCoverGLTraceCosetEquiv N g (QuotientGroup.mk c) =
      QuotientGroup.mk (rationalConjugateSL2ToGLEquiv N g c) := by
  rfl

/-- Evaluating the common-cover source on a fibre representative gives the
original Maass function at that representative's inverse translate. -/
theorem rationalHeckeIntegralCoverSourceFunction_fiber_summand (N : ℕ)
    (g : GL (Fin 2) ℚ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (z : ℍ) (c : (rationalConjugateSL2Group N g) ⧸
      ((rationalHeckeCommonCoverReal N g).subgroupOf
        (rationalConjugateSL2Group N g))) :
    rationalHeckeIntegralCoverSourceFunction N g f
      (QuotientGroup.mk ((UpperHalfPlane.toSL2R z)⁻¹ * c.out.val) :
        SL2R ⧸ rationalHeckeCommonCoverReal N g) =
      f.1.1 (c.out.val⁻¹ • z) := by
  unfold rationalHeckeIntegralCoverSourceFunction
  rw [maassInvariantQuotientLift_mk]
  simp only [_root_.mul_inv_rev, inv_inv, mul_smul, UpperHalfPlane.toSL2R_smul_I]
  rfl

/-- The common-cover source at any literal fibre representative is the
corresponding inverse translate of the original Maass function. -/
theorem rationalHeckeIntegralCoverSourceFunction_fiber_summand_apply (N : ℕ)
    (g : GL (Fin 2) ℚ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (a : SL2R) (c : (rationalConjugateSL2Group N g) ⧸
      ((rationalHeckeCommonCoverReal N g).subgroupOf
        (rationalConjugateSL2Group N g))) :
    rationalHeckeIntegralCoverSourceFunction N g f
      (QuotientGroup.mk (a * c.out.val) : SL2R ⧸ rationalHeckeCommonCoverReal N g) =
      f.1.1 (c.out.val⁻¹ • (a⁻¹ • UpperHalfPlane.I)) := by
  unfold rationalHeckeIntegralCoverSourceFunction
  rw [maassInvariantQuotientLift_mk]
  simp only [_root_.mul_inv_rev, mul_smul]
  rfl

/-- A `GL₂` common-cover trace summand is the same inverse translate of the
original Maass function as its determinant-one counterpart. -/
theorem rationalCommonCoverGLInvariant_trace_summand (N : ℕ) (g : GL (Fin 2) ℚ)
    {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (c : rationalConjugateSL2Group N g) (z : ℍ) :
    (rationalCommonCoverGLInvariant N g f).1
      (((rationalConjugateSL2ToGLEquiv N g c : rationalConjugateGroup N g).val)⁻¹ • z) =
      f.1.1 (c.val⁻¹ • z) := by
  change f.1.1 (((rationalConjugateSL2ToGLEquiv N g c)⁻¹).val • z) =
    f.1.1 ((c⁻¹).val • z)
  exact congrArg f.1.1 (rationalConjugateSL2ToGLEquiv_smul N g c⁻¹ z)

/-- The finite trace on the `GL₂` common cover is pointwise the raw bounded
fibre trace of the original Maass source. -/
theorem rationalCommonCoverGLTrace_apply_eq_rationalHeckeConjugateFiberTrace_mk
    (N : ℕ) (g : GL (Fin 2) ℚ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (a : SL2R) :
    (rationalCommonCoverGLTrace N g f).1 (a⁻¹ • UpperHalfPlane.I) =
      rationalHeckeConjugateFiberTrace N g
        (rationalHeckeIntegralCoverSourceFunction N g f)
        (QuotientGroup.mk a) := by
  letI : (principalCongruenceGL N ⊓ rationalConjugateGroup N g).IsFiniteRelIndex
      (rationalConjugateGroup N g) := rationalCommonCoverGL_isFiniteRelIndex N g
  letI : Fintype ((rationalConjugateGroup N g) ⧸
      ((principalCongruenceGL N ⊓ rationalConjugateGroup N g).subgroupOf
        (rationalConjugateGroup N g))) := Fintype.ofFinite _
  change maassTraceFunction
      (G := principalCongruenceGL N ⊓ rationalConjugateGroup N g)
      (H := rationalConjugateGroup N g) (rationalCommonCoverGLInvariant N g f)
        (a⁻¹ • UpperHalfPlane.I) = _
  rw [rationalHeckeConjugateFiberTrace_mk]
  unfold maassTraceFunction
  let e := rationalHeckeCommonCoverGLTraceCosetEquiv N g
  calc
    ∑ q : (rationalConjugateGroup N g) ⧸
        ((principalCongruenceGL N ⊓ rationalConjugateGroup N g).subgroupOf
          (rationalConjugateGroup N g)),
        maassTraceQuotientFunc (rationalCommonCoverGLInvariant N g f) q
          (a⁻¹ • UpperHalfPlane.I) =
      ∑ c : (rationalConjugateSL2Group N g) ⧸
          ((rationalHeckeCommonCoverReal N g).subgroupOf
            (rationalConjugateSL2Group N g)),
          f.1.1 (c.out.val⁻¹ • (a⁻¹ • UpperHalfPlane.I)) := by
        symm
        apply Fintype.sum_equiv e
        intro c
        have hc : (QuotientGroup.mk c.out : (rationalConjugateSL2Group N g) ⧸
            (rationalHeckeCommonCoverReal N g).subgroupOf
              (rationalConjugateSL2Group N g)) = c := Quotient.out_eq c
        have he : e c = QuotientGroup.mk (rationalConjugateSL2ToGLEquiv N g c.out) := by
          change rationalHeckeCommonCoverGLTraceCosetEquiv N g c = _
          exact (congrArg (rationalHeckeCommonCoverGLTraceCosetEquiv N g) hc.symm).trans
            (rationalHeckeCommonCoverGLTraceCosetEquiv_mk N g c.out)
        rw [he,
          maassTraceQuotientFunc_mk]
        exact (rationalCommonCoverGLInvariant_trace_summand N g f c.out
          (a⁻¹ • UpperHalfPlane.I)).symm
    _ = ∑ c : (rationalConjugateSL2Group N g) ⧸
          ((rationalHeckeCommonCoverReal N g).subgroupOf
            (rationalConjugateSL2Group N g)),
          rationalHeckeIntegralCoverSourceFunction N g f
            (RHTower.deningerFiberMap
              (H := rationalHeckeCommonCoverReal N g)
              a c) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [rationalHeckeConjugateFiberCoordinate_eq_mk_out]
        exact (rationalHeckeIntegralCoverSourceFunction_fiber_summand_apply N g f a c).symm

/-- Restricting the rational-conjugate `GL₂` trace to determinant one gives an
invariant upper-half-plane function on the rational-conjugate `SL₂` group. -/
noncomputable def rationalCommonCoverGLTraceSLInvariant (N : ℕ) (g : GL (Fin 2) ℚ)
    {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    upperHalfPlaneInvariantFunctions (rationalConjugateSL2Group N g) :=
  ⟨(rationalCommonCoverGLTrace N g f).1, by
    intro c z
    rw [← rationalConjugateSL2ToGLEquiv_smul N g c z]
    exact (rationalCommonCoverGLTrace N g f).2
      (rationalConjugateSL2ToGLEquiv N g c) z⟩

/-- Actual Maass-to-model intertwiner: the raw rational finite-fibre trace is
exactly the quotient lift of the rational-conjugate automorphic trace. -/
theorem rationalHeckeConjugateFiberTrace_source_eq_glTraceQuotientLift
    (N : ℕ) (g : GL (Fin 2) ℚ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    rationalHeckeConjugateFiberTrace N g
      (rationalHeckeIntegralCoverSourceFunction N g f) =
      maassInvariantQuotientLift (rationalConjugateSL2Group N g)
        (rationalCommonCoverGLTraceSLInvariant N g f) := by
  funext q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  rw [maassInvariantQuotientLift_mk]
  change rationalHeckeConjugateFiberTrace N g
      (rationalHeckeIntegralCoverSourceFunction N g f) (QuotientGroup.mk a) =
    (rationalCommonCoverGLTrace N g f).1 (a⁻¹ • UpperHalfPlane.I)
  exact (rationalCommonCoverGLTrace_apply_eq_rationalHeckeConjugateFiberTrace_mk N g f a).symm

/-- The bounded quotient `L²` trace of a Maass source has the rational-
conjugate automorphic trace as its literal almost-everywhere representative. -/
theorem coe_rationalHeckeConjugateFiberTraceSourceLp_eq_glTraceQuotientLift
    (N : ℕ) (g : GL (Fin 2) ℚ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    rationalHeckeConjugateFiberTraceSourceLp N g f =ᵐ[
      rationalConjugateSL2QuotientMeasure N g]
      maassInvariantQuotientLift (rationalConjugateSL2Group N g)
        (rationalCommonCoverGLTraceSLInvariant N g f) :=
  (coe_rationalHeckeConjugateFiberTraceSourceLp N g f).trans
    (Filter.Eventually.of_forall fun q =>
      congrFun (rationalHeckeConjugateFiberTrace_source_eq_glTraceQuotientLift N g f) q)

/-- The common-cover `GL₂` trace and raw finite fibre trace agree on the
upper-half-plane section. -/
theorem rationalCommonCoverGLTrace_apply_eq_rationalHeckeConjugateFiberTrace
    (N : ℕ) (g : GL (Fin 2) ℚ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (z : ℍ) :
    (rationalCommonCoverGLTrace N g f).1 z =
      rationalHeckeConjugateFiberTrace N g
        (rationalHeckeIntegralCoverSourceFunction N g f)
        (QuotientGroup.mk (UpperHalfPlane.toSL2R z)⁻¹) := by
  simpa only [inv_inv, UpperHalfPlane.toSL2R_smul_I] using
    rationalCommonCoverGLTrace_apply_eq_rationalHeckeConjugateFiberTrace_mk N g f
      (UpperHalfPlane.toSL2R z)⁻¹

/-- The common-cover trace has the Maass eigen-equation and integral-cusp
decay in its rational-conjugate `GL₂` target. -/
noncomputable def rationalCommonCoverGLTraceData (N : ℕ) (g : GL (Fin 2) ℚ)
    {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    {F : glUpperHalfPlaneInvariantFunctions (rationalConjugateGroup N g) //
      IsMaassEigenfunction lam F.1 ∧ IsCuspidalAtIntegralCusps F.1} := by
  letI : (principalCongruenceGL N ⊓ rationalConjugateGroup N g).IsFiniteRelIndex
      (rationalConjugateGroup N g) := rationalCommonCoverGL_isFiniteRelIndex N g
  exact rationalConjugateMaassTraceData_of_data N g lam
    (rationalCommonCoverGLInvariant N g f) f.2.2.1 f.2.2.2

/-- The trace-data carrier is the literal common-cover `GL₂` trace. -/
theorem coe_rationalCommonCoverGLTraceData (N : ℕ) (g : GL (Fin 2) ℚ)
    {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    (rationalCommonCoverGLTraceData N g f).1 = rationalCommonCoverGLTrace N g f := by
  rfl

/-- On the rational quotient section, the raw finite fibre trace satisfies the
same Maass eigen-equation as the common-cover `GL₂` trace. -/
theorem rationalHeckeConjugateFiberTrace_source_section_eigen (N : ℕ)
    (g : GL (Fin 2) ℚ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (z : ℍ) :
    positiveHyperbolicLaplacian (fun w =>
      rationalHeckeConjugateFiberTrace N g
        (rationalHeckeIntegralCoverSourceFunction N g f)
        (QuotientGroup.mk (UpperHalfPlane.toSL2R w)⁻¹)) z =
      (lam : ℂ) * rationalHeckeConjugateFiberTrace N g
        (rationalHeckeIntegralCoverSourceFunction N g f)
        (QuotientGroup.mk (UpperHalfPlane.toSL2R z)⁻¹) := by
  have hsection : (fun w =>
      rationalHeckeConjugateFiberTrace N g
        (rationalHeckeIntegralCoverSourceFunction N g f)
        (QuotientGroup.mk (UpperHalfPlane.toSL2R w)⁻¹)) =
      (rationalCommonCoverGLTrace N g f).1 := by
    funext w
    exact (rationalCommonCoverGLTrace_apply_eq_rationalHeckeConjugateFiberTrace N g f w).symm
  have htrace := (rationalCommonCoverGLTraceData N g f).2.1.2 z
  rw [coe_rationalCommonCoverGLTraceData, ← hsection] at htrace
  exact htrace

/-- On the rational quotient section, the raw finite fibre trace retains
integral-cusp decay. -/
theorem rationalHeckeConjugateFiberTrace_source_section_cuspidal (N : ℕ)
    (g : GL (Fin 2) ℚ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    IsCuspidalAtIntegralCusps (fun w =>
      rationalHeckeConjugateFiberTrace N g
        (rationalHeckeIntegralCoverSourceFunction N g f)
        (QuotientGroup.mk (UpperHalfPlane.toSL2R w)⁻¹)) := by
  have hsection : (fun w =>
      rationalHeckeConjugateFiberTrace N g
        (rationalHeckeIntegralCoverSourceFunction N g f)
        (QuotientGroup.mk (UpperHalfPlane.toSL2R w)⁻¹)) =
      (rationalCommonCoverGLTrace N g f).1 := by
    funext w
    exact (rationalCommonCoverGLTrace_apply_eq_rationalHeckeConjugateFiberTrace N g f w).symm
  have htrace := (rationalCommonCoverGLTraceData N g f).2.2
  rw [coe_rationalCommonCoverGLTraceData, ← hsection] at htrace
  exact htrace

/-- The generic quotient `L²` trace is additive. -/
theorem rationalHeckeConjugateFiberTraceLp_map_add (N : ℕ) (g : GL (Fin 2) ℚ)
    (f h : Lp ℂ 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))) :
    rationalHeckeConjugateFiberTraceLp N g (f + h) =
      rationalHeckeConjugateFiberTraceLp N g f +
        rationalHeckeConjugateFiberTraceLp N g h := by
  let f₀ := AEStronglyMeasurable.mk f (Lp.aestronglyMeasurable f)
  let h₀ := AEStronglyMeasurable.mk h (Lp.aestronglyMeasurable h)
  let fh₀ := AEStronglyMeasurable.mk (f + h) (Lp.aestronglyMeasurable (f + h))
  have hf₀ : StronglyMeasurable f₀ := (Lp.aestronglyMeasurable f).stronglyMeasurable_mk
  have hh₀ : StronglyMeasurable h₀ := (Lp.aestronglyMeasurable h).stronglyMeasurable_mk
  have hfh₀ : StronglyMeasurable fh₀ :=
    (Lp.aestronglyMeasurable (f + h)).stronglyMeasurable_mk
  have hcanon : fh₀ =ᵐ[integralSubgroupQuotientMeasure
      (rationalHeckeIntegralIntersection N g)] f₀ + h₀ :=
    (Lp.aestronglyMeasurable (f + h)).ae_eq_mk.symm.trans
      ((Lp.coeFn_add f h).trans ((Lp.aestronglyMeasurable f).ae_eq_mk.add
        (Lp.aestronglyMeasurable h).ae_eq_mk))
  have htraceCongr : rationalHeckeConjugateFiberTrace N g fh₀ =ᵐ[
      rationalConjugateSL2QuotientMeasure N g]
      rationalHeckeConjugateFiberTrace N g (f₀ + h₀) :=
    rationalHeckeConjugateFiberTrace_congr_ae_of_stronglyMeasurable N g fh₀ (f₀ + h₀)
      hfh₀ (hf₀.add hh₀) hcanon
  have htraceAdd : rationalHeckeConjugateFiberTrace N g (f₀ + h₀) =
      rationalHeckeConjugateFiberTrace N g f₀ + rationalHeckeConjugateFiberTrace N g h₀ := by
    exact (rationalHeckeConjugateFiberTraceLinear N g).map_add f₀ h₀
  have htraceEq : rationalHeckeConjugateFiberTrace N g fh₀ =ᵐ[
      rationalConjugateSL2QuotientMeasure N g]
      rationalHeckeConjugateFiberTrace N g f₀ + rationalHeckeConjugateFiberTrace N g h₀ :=
    htraceCongr.trans (Filter.EventuallyEq.of_eq htraceAdd)
  apply Lp.ext
  exact (coe_rationalHeckeConjugateFiberTraceLp N g (f + h)).trans
    (htraceEq.trans
      (((coe_rationalHeckeConjugateFiberTraceLp N g f).symm.add
        (coe_rationalHeckeConjugateFiberTraceLp N g h).symm).trans
        (Lp.coeFn_add _ _).symm))

/-- The generic quotient `L²` trace commutes with complex scalar multiplication. -/
theorem rationalHeckeConjugateFiberTraceLp_map_smul (N : ℕ) (g : GL (Fin 2) ℚ)
    (c : ℂ) (f : Lp ℂ 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))) :
    rationalHeckeConjugateFiberTraceLp N g (c • f) =
      c • rationalHeckeConjugateFiberTraceLp N g f := by
  let f₀ := AEStronglyMeasurable.mk f (Lp.aestronglyMeasurable f)
  let cf₀ := AEStronglyMeasurable.mk (c • f) (Lp.aestronglyMeasurable (c • f))
  have hf₀ : StronglyMeasurable f₀ := (Lp.aestronglyMeasurable f).stronglyMeasurable_mk
  have hcf₀ : StronglyMeasurable cf₀ :=
    (Lp.aestronglyMeasurable (c • f)).stronglyMeasurable_mk
  have hcanon : cf₀ =ᵐ[integralSubgroupQuotientMeasure
      (rationalHeckeIntegralIntersection N g)] c • f₀ :=
    (Lp.aestronglyMeasurable (c • f)).ae_eq_mk.symm.trans
      ((Lp.coeFn_smul c f).trans ((Lp.aestronglyMeasurable f).ae_eq_mk.const_smul c))
  have htraceCongr : rationalHeckeConjugateFiberTrace N g cf₀ =ᵐ[
      rationalConjugateSL2QuotientMeasure N g]
      rationalHeckeConjugateFiberTrace N g (c • f₀) :=
    rationalHeckeConjugateFiberTrace_congr_ae_of_stronglyMeasurable N g cf₀ (c • f₀)
      hcf₀ (hf₀.const_smul c) hcanon
  have htraceSmul : rationalHeckeConjugateFiberTrace N g (c • f₀) =
      c • rationalHeckeConjugateFiberTrace N g f₀ := by
    exact (rationalHeckeConjugateFiberTraceLinear N g).map_smul c f₀
  have htraceEq : rationalHeckeConjugateFiberTrace N g cf₀ =ᵐ[
      rationalConjugateSL2QuotientMeasure N g]
      c • rationalHeckeConjugateFiberTrace N g f₀ :=
    htraceCongr.trans (Filter.EventuallyEq.of_eq htraceSmul)
  have hcoe : rationalHeckeConjugateFiberTraceLp N g f =ᵐ[
      rationalConjugateSL2QuotientMeasure N g]
      rationalHeckeConjugateFiberTrace N g f₀ :=
    coe_rationalHeckeConjugateFiberTraceLp N g f
  have hscaled : c • rationalHeckeConjugateFiberTrace N g f₀ =ᵐ[
      rationalConjugateSL2QuotientMeasure N g]
      c • rationalHeckeConjugateFiberTraceLp N g f :=
    hcoe.symm.const_smul c
  apply Lp.ext
  exact (coe_rationalHeckeConjugateFiberTraceLp N g (c • f)).trans
    (htraceEq.trans (hscaled.trans (Lp.coeFn_smul _ _).symm))

/-- The rational finite-fibre correspondence as a genuine complex-linear map on
the two quotient `L²` spaces. -/
noncomputable def rationalHeckeConjugateFiberTraceLpLinear (N : ℕ) (g : GL (Fin 2) ℚ) :
    Lp ℂ 2 (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) →ₗ[ℂ]
      Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g) where
  toFun := rationalHeckeConjugateFiberTraceLp N g
  map_add' := rationalHeckeConjugateFiberTraceLp_map_add N g
  map_smul' := rationalHeckeConjugateFiberTraceLp_map_smul N g

/-- The quotient `L²` trace norm is bounded by its finite fibre cardinality.
The sharper square-energy bound is proved above; this linear bound packages it
in the form needed to construct a continuous operator. -/
theorem rationalHeckeConjugateFiberTraceLp_norm_le_card_mul (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : Lp ℂ 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))) :
    ‖rationalHeckeConjugateFiberTraceLp N g f‖ ≤
      (Fintype.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) : ℝ) * ‖f‖ := by
  let K := rationalHeckeCommonCoverReal N g
  let R := rationalConjugateSL2Group N g
  let D := R ⧸ K.subgroupOf R
  letI : Fintype D := Fintype.ofFinite _
  let f₀ := AEStronglyMeasurable.mk f (Lp.aestronglyMeasurable f)
  have hf₀ : StronglyMeasurable f₀ :=
    (Lp.aestronglyMeasurable f).stronglyMeasurable_mk
  have hmemf₀ : MemLp f₀ 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) :=
    (memLp_congr_ae (Lp.aestronglyMeasurable f).ae_eq_mk).mp (Lp.memLp f)
  have henergy :=
    rationalHeckeConjugateFiberTrace_integral_norm_sq_le_of_stronglyMeasurable
      N g f₀ hf₀ hmemf₀
  have htargetEnergy : ‖rationalHeckeConjugateFiberTraceLp N g f‖ ^ 2 =
      ∫ y, ‖rationalHeckeConjugateFiberTrace N g f₀ y‖ ^ 2
        ∂rationalConjugateSL2QuotientMeasure N g := by
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [coe_rationalHeckeConjugateFiberTraceLp N g f] with y hy
    rw [hy]
  have hsourceEnergy : ‖f‖ ^ 2 = ∫ y, ‖f₀ y‖ ^ 2
      ∂integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g) := by
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [(Lp.aestronglyMeasurable f).ae_eq_mk] with y hy
    rw [hy]
  have hsq : ‖rationalHeckeConjugateFiberTraceLp N g f‖ ^ 2 ≤
      (Fintype.card D : ℝ) * ‖f‖ ^ 2 := by
    rw [htargetEnergy, hsourceEnergy]
    simpa only [D, R, K] using henergy
  letI : Nonempty D := ⟨QuotientGroup.mk 1⟩
  have hcard : (1 : ℝ) ≤ Fintype.card D := by
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α := D))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (le_trans zero_le_one hcard) (norm_nonneg _))).mp
  calc
    ‖rationalHeckeConjugateFiberTraceLp N g f‖ ^ 2 ≤
        (Fintype.card D : ℝ) * ‖f‖ ^ 2 := hsq
    _ ≤ ((Fintype.card D : ℝ) * (Fintype.card D : ℝ)) * ‖f‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right (le_trans zero_le_one hcard) hcard) (sq_nonneg ‖f‖)
    _ = ((Fintype.card D : ℝ) * ‖f‖) ^ 2 := by ring

/-- The finite-fibre rational correspondence is a continuous complex-linear
operator on the two quotient `L²` spaces. -/
noncomputable def rationalHeckeConjugateFiberTraceLpContinuousLinear (N : ℕ)
    (g : GL (Fin 2) ℚ) :
    Lp ℂ 2 (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) →L[ℂ]
      Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g) :=
  LinearMap.mkContinuous (rationalHeckeConjugateFiberTraceLpLinear N g)
    (Fintype.card ((rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) : ℝ)
    (rationalHeckeConjugateFiberTraceLp_norm_le_card_mul N g)

end

end GaloisForLFunctions.RHTower
