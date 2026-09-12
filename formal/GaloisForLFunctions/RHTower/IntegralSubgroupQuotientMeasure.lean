import GaloisForLFunctions.RHTower.RealSL2Haar
import GaloisForLFunctions.RHTower.CongruenceMaassCorrespondence
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Actual integral-subgroup quotient measure

Discreteness supplies a countable cover by orbit-injective open patches. Keeping
points whose orbit misses all earlier patches gives a measurable strict selector.
This constructs, rather than assumes, a fundamental domain for every integral
subgroup, hence every principal congruence subgroup. Haar unimodularity then gives
an invariant nonzero, sigma-finite, locally finite, regular quotient measure.

The quotient is G/Gamma. Inversion relates it to the Gamma\G convention for
Maass lifts. Finite covolume and the Iwasawa comparison with the hyperbolic-cell
norm are further obligations; neither is asserted here.
-/

open Set MeasureTheory Topology TopologicalSpace
open scoped Pointwise
namespace GaloisForLFunctions.RHTower

private theorem strictDomain_of_countable_cover
    {G X : Type*} [Group G] [MulAction G X] [Countable G]
    [MeasurableSpace X] [MeasurableConstSMul G X]
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (hcover : ∀ x, ∃ n, x ∈ U n)
    (huniq : ∀ n x (g : G), x ∈ U n → g • x ∈ U n → g = 1) :
    ∃ s : Set X, MeasurableSet s ∧ ∀ x, ∃! g : G, g • x ∈ s := by
  classical
  let V : ℕ → Set X := fun n => {x | x ∈ U n ∧ ∀ m, m < n → ∀ g : G, g • x ∉ U m}
  have hV : ∀ n, MeasurableSet (V n) := by
    intro n
    have hv : V n = U n ∩ ⋂ m, ⋂ (_ : m < n), ⋂ g : G,
        ((fun x => g • x) ⁻¹' U m)ᶜ := by ext; simp [V]
    rw [hv]
    exact (hU n).inter (MeasurableSet.iInter fun m =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun g =>
        ((hU m).preimage (measurable_const_smul g)).compl)
  refine ⟨⋃ n, V n, MeasurableSet.iUnion hV, fun x => ?_⟩
  have hex : ∃ n, ∃ g : G, g • x ∈ U n := by
    obtain ⟨n, hn⟩ := hcover x
    exact ⟨n, 1, by simpa using hn⟩
  obtain ⟨g, hg⟩ := Nat.find_spec hex
  have hgV : g • x ∈ V (Nat.find hex) := by
    refine ⟨hg, fun m hm a ha => ?_⟩
    exact Nat.find_min hex hm ⟨a * g, by simpa [mul_smul] using ha⟩
  refine ⟨g, mem_iUnion.mpr ⟨_, hgV⟩, ?_⟩
  intro a ha
  obtain ⟨m, ham, hamin⟩ := mem_iUnion.mp ha
  have hm : m = Nat.find hex := by
    apply le_antisymm
    · by_contra h
      exact hamin _ (Nat.lt_of_not_ge h) (g * a⁻¹) (by simpa [mul_smul] using hg)
    · exact Nat.find_min' hex ⟨a, ham⟩
  have heq := huniq m (g • x) (a * g⁻¹) (hm ▸ hg) (by simpa [mul_smul] using ham)
  exact mul_inv_eq_one.mp heq

private theorem strictDomain_of_discrete_subgroup
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup H) [Countable Γ] [DiscreteTopology Γ] :
    ∃ s : Set H, MeasurableSet s ∧ ∀ x, ∃! g : Γ.op, g • x ∈ s := by
  classical
  have hΓ : IsDiscrete (Γ : Set H) := SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  obtain ⟨U, hU, -, hsep⟩ :=
    hΓ.exists_nhds_eq_one_of_image_mulRight_inter_nonempty
  let W : H → Set H := fun z => (z * ·) '' interior U
  have hopen : ∀ z, IsOpen (W z) := fun z => isOpenMap_mul_left z _ isOpen_interior
  have hone : (1 : H) ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  have hself : ∀ x, x ∈ W x := fun x => ⟨1, hone, mul_one x⟩
  have huniq : ∀ z x (g : Γ.op), x ∈ W z → g • x ∈ W z → g = 1 := by
    intro z x g hx hgx
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, heq⟩ := hgx
    have huv : u * g.1.unop = v := by
      apply mul_left_cancel (a := z)
      exact (mul_assoc z u g.1.unop).symm.trans heq.symm
    have hg1 : g.1.unop = 1 := hsep _ g.2
      ⟨v, ⟨u, interior_subset hu, huv⟩, interior_subset hv⟩
    apply Subtype.ext
    exact MulOpposite.unop_injective hg1
  obtain ⟨T, hT, hTW⟩ := isOpen_iUnion_countable W hopen
  have hcoverT : ∀ x, ∃ z : T, x ∈ W z := by
    intro x
    have hx : x ∈ ⋃ z ∈ T, W z := by
      rw [hTW]
      exact mem_iUnion.mpr ⟨x, hself x⟩
    simpa only [mem_iUnion, Subtype.exists, exists_prop] using hx
  haveI : Countable T := hT.to_subtype
  haveI : Nonempty T := ⟨(hcoverT 1).choose⟩
  obtain ⟨a, ha⟩ := exists_surjective_nat T
  apply strictDomain_of_countable_cover (fun n => W (a n))
    (fun n => (hopen _).measurableSet)
  · intro x
    obtain ⟨z, hz⟩ := hcoverT x
    obtain ⟨n, rfl⟩ := ha z
    exact ⟨n, hz⟩
  · intro n
    exact huniq (a n)

instance realImage_countable (Γ : Subgroup SL2Z) : Countable (realImage Γ) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL2Z := inferInstanceAs (Countable (Subtype _))
  exact ((Set.to_countable (Γ : Set SL2Z)).image integralSL2ToReal).to_subtype

instance realImage_discreteTopology (Γ : Subgroup SL2Z) : DiscreteTopology (realImage Γ) := by
  apply SetLike.isDiscrete_iff_discreteTopology.mp
  have hr : IsDiscrete ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
      (n := Fin 2)).range : Set SL2R) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  apply hr.mono
  rintro _ ⟨γ, -, rfl⟩
  exact ⟨γ, rfl⟩

/-- A measurable selector for orbits of right multiplication by the integral subgroup. -/
noncomputable def integralSubgroupFundamentalSet (Γ : Subgroup SL2Z) : Set SL2R :=
  (strictDomain_of_discrete_subgroup (realImage Γ)).choose

/-- The chosen selector is Borel measurable. -/
theorem integralSubgroupFundamentalSet_measurable (Γ : Subgroup SL2Z) :
    MeasurableSet (integralSubgroupFundamentalSet Γ) :=
  (strictDomain_of_discrete_subgroup (realImage Γ)).choose_spec.1

/-- Every orbit meets the chosen selector exactly once. -/
theorem integralSubgroupFundamentalSet_unique (Γ : Subgroup SL2Z) (x : SL2R) :
    ∃! g : (realImage Γ).op, g • x ∈ integralSubgroupFundamentalSet Γ :=
  (strictDomain_of_discrete_subgroup (realImage Γ)).choose_spec.2 x

/-- The actual selector is a Haar fundamental domain. -/
theorem integralSubgroupFundamentalSet_isFundamentalDomain (Γ : Subgroup SL2Z) :
    IsFundamentalDomain (realImage Γ).op (integralSubgroupFundamentalSet Γ) realSL2Haar :=
  IsFundamentalDomain.mk' (integralSubgroupFundamentalSet_measurable Γ).nullMeasurableSet
    (integralSubgroupFundamentalSet_unique Γ)

instance integralSubgroup_hasFundamentalDomain (Γ : Subgroup SL2Z) :
    HasFundamentalDomain (realImage Γ).op SL2R realSL2Haar :=
  (integralSubgroupFundamentalSet_isFundamentalDomain Γ).hasFundamentalDomain realSL2Haar

/-- Haar quotient measure on actual left cosets; the subgroup need not be normal. -/
noncomputable def integralSubgroupQuotientMeasure (Γ : Subgroup SL2Z) :
    Measure (SL2R ⧸ realImage Γ) :=
  (realSL2Haar.restrict (integralSubgroupFundamentalSet Γ)).map QuotientGroup.mk

instance integralSubgroupQuotientMeasure_projection (Γ : Subgroup SL2Z) :
    QuotientMeasureEqMeasurePreimage realSL2Haar (integralSubgroupQuotientMeasure Γ) :=
  (integralSubgroupFundamentalSet_isFundamentalDomain Γ).quotientMeasureEqMeasurePreimage_quotientMeasure

instance integralSubgroupQuotientMeasure_invariant (Γ : Subgroup SL2Z) :
    SMulInvariantMeasure SL2R (SL2R ⧸ realImage Γ) (integralSubgroupQuotientMeasure Γ) :=
  QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient realSL2Haar

instance integralSubgroupQuotientMeasure_sigmaFinite (Γ : Subgroup SL2Z) :
    SigmaFinite (integralSubgroupQuotientMeasure Γ) :=
  QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient (ν := realSL2Haar)
    (integralSubgroupQuotientMeasure Γ)

/-- Actual group translation preserves quotient measure. -/
theorem integralSubgroupQuotientMeasure_translation (Γ : Subgroup SL2Z) (g : SL2R) :
    MeasurePreserving (fun q : SL2R ⧸ realImage Γ => g • q)
      (integralSubgroupQuotientMeasure Γ) (integralSubgroupQuotientMeasure Γ) :=
  measurePreserving_smul g (integralSubgroupQuotientMeasure Γ)
/-- Folding a measurable set to the quotient cannot increase its mass. -/
theorem integralSubgroupQuotientMeasure_image_le (Γ : Subgroup SL2Z)
    {A : Set SL2R} (hA : MeasurableSet A) :
    integralSubgroupQuotientMeasure Γ (QuotientGroup.mk '' A) ≤ realSL2Haar A := by
  let π : SL2R → SL2R ⧸ realImage Γ := QuotientGroup.mk
  have hpre : π ⁻¹' π '' A = ⋃ g : (realImage Γ).op, g • A :=
    MulAction.quotient_preimage_image_eq_union_mul A (G := (realImage Γ).op)
  have hmeas : MeasurableSet (π '' A) := by
    rw [measurableSet_quotient, hpre]
    exact MeasurableSet.iUnion fun g => hA.const_smul g
  rw [(integralSubgroupFundamentalSet_isFundamentalDomain Γ).projection_respects_measure_apply
    (μ := integralSubgroupQuotientMeasure Γ) hmeas]
  change realSL2Haar (π ⁻¹' π '' A ∩ integralSubgroupFundamentalSet Γ) ≤ _
  rw [hpre, iUnion_inter,
    (integralSubgroupFundamentalSet_isFundamentalDomain Γ).measure_eq_tsum A]
  exact measure_iUnion_le _

instance integralSubgroupQuotientMeasure_locallyFinite (Γ : Subgroup SL2Z) :
    IsLocallyFiniteMeasure (integralSubgroupQuotientMeasure Γ) where
  finiteAtNhds q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨U, hx, hU, hfin⟩ := realSL2Haar.exists_isOpen_measure_lt_top x
    refine ⟨QuotientGroup.mk '' U, ?_,
      (integralSubgroupQuotientMeasure_image_le Γ hU.measurableSet).trans_lt hfin⟩
    exact (QuotientGroup.isOpenMap_coe (N := realImage Γ) U hU).mem_nhds ⟨x, hx, rfl⟩
/-- The constructed quotient measure is nonzero. -/
theorem integralSubgroupQuotientMeasure_ne_zero (Γ : Subgroup SL2Z) :
    integralSubgroupQuotientMeasure Γ ≠ 0 := by
  have hpos := (integralSubgroupFundamentalSet_isFundamentalDomain Γ).measure_ne_zero
    (NeZero.ne realSL2Haar)
  intro hzero
  have hu := (integralSubgroupFundamentalSet_isFundamentalDomain Γ).projection_respects_measure_apply
    (μ := integralSubgroupQuotientMeasure Γ) MeasurableSet.univ
  rw [hzero] at hu
  exact hpos (by simpa using hu.symm)
/-- The actual quotient measure is regular; no finite-covolume premise is used. -/
instance integralSubgroupQuotientMeasure_regular (Γ : Subgroup SL2Z) :
    (integralSubgroupQuotientMeasure Γ).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

end GaloisForLFunctions.RHTower
