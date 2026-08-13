import GaloisForLFunctions.HTGeometry.TripticKummerRootClassification
import GaloisForLFunctions.HTGeometry.SourceDivisorSurjectivity

/-!
# The multiplicative triptic class as a group, and its effective quotient `M/M_DA ≅ ℤ[ℂ/H₃]`

As functions, class members fail to be invertible at their zeros; as germs along the codiscrete
filter they form a group.  The units of the codiscrete-germ ring represented by class members form
a subgroup `M`; the integral orbit divisor of a representative depends only on the germ, so it
defines an additive homomorphism `D : M →+ ℤ[ℂ/H₃]`.  Every single class `[g]` is realized by a
translated elliptic gamma unit, so `D` is surjective and the abstract Kummer classification
applies verbatim: the effective quotient `M/ker D ≅ ℤ[ℂ/H₃]`, the root criterion by content
divisibility, and the identification of `ker D` with the differentially algebraic members.

* `tripticSourceUnitClass`, `tripticSourceUnit`;
* `tripticDivisorHom`, `tripticDivisorHom_single`;
* `tripticSourceQuotientEquiv`, `tripticSource_hasSourceRootModuloKernel_iff_content_dvd`;
* `mem_ker_tripticDivisorHom_iff`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {τ σ : ℂ} {Y : ℂ → ℂ} {Cst : ℂ}

/-! ### The codiscrete germ carrier -/

/-- A set belongs to the codiscrete filter of the plane exactly when it is a punctured
neighbourhood of every point. -/
theorem mem_codiscreteWithin_univ_iff {S : Set ℂ} :
    S ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) ↔ ∀ x : ℂ, S ∈ 𝓝[≠] x := by
  rw [mem_codiscreteWithin]
  refine ⟨fun h x ↦ ?_, fun h x _ ↦ ?_⟩
  · have hx := h x (Set.mem_univ x)
    rw [Filter.disjoint_principal_right] at hx
    have hcompl : (Set.univ \ S)ᶜ = S := by
      rw [Set.univ_diff, compl_compl]
    rwa [hcompl] at hx
  · rw [Filter.disjoint_principal_right]
    have hcompl : (Set.univ \ S)ᶜ = S := by
      rw [Set.univ_diff, compl_compl]
    rwa [hcompl]

/-- Germ equality along the codiscrete filter is punctured-local equality at every point. -/
theorem eventuallyEq_nhdsNE_of_codiscrete {Y₁ Y₂ : ℂ → ℂ}
    (h : Y₁ =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)] Y₂) (z : ℂ) :
    Y₁ =ᶠ[𝓝[≠] z] Y₂ :=
  mem_codiscreteWithin_univ_iff.mp h z

/-- **The orbital charge depends only on the codiscrete germ.** -/
theorem tripticOrbitCharge_congr {Y₁ Y₂ : ℂ → ℂ}
    (h : Y₁ =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)] Y₂) (σ p : ℂ) :
    tripticOrbitCharge Y₁ σ p = tripticOrbitCharge Y₂ σ p := by
  rw [tripticOrbitCharge, tripticOrbitCharge]
  refine finsum_congr fun m ↦ ?_
  rw [shiftOrder, shiftOrder,
    meromorphicOrderAt_congr (eventuallyEq_nhdsNE_of_codiscrete h _),
    meromorphicOrderAt_congr (eventuallyEq_nhdsNE_of_codiscrete h _)]

/-- **The divisor depends only on the codiscrete germ.** -/
theorem tripticDivisor_congr {Y₁ Y₂ : ℂ → ℂ}
    (h : Y₁ =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)] Y₂)
    (hfin₁ : (Function.support (tripticChargeClass Y₁ τ σ)).Finite)
    (hfin₂ : (Function.support (tripticChargeClass Y₂ τ σ)).Finite) :
    tripticDivisor Y₁ τ σ hfin₁ = tripticDivisor Y₂ τ σ hfin₂ := by
  ext g
  exact tripticOrbitCharge_congr h σ (Quotient.out g)

/-- **The divisor of a product of class members is the sum of the divisors.** -/
theorem tripticDivisor_mul {Y₁ Y₂ : ℂ → ℂ} {C₁ C₂ : ℂ}
    (h₁ : TripticMultiplicativeSource τ σ Y₁ C₁)
    (h₂ : TripticMultiplicativeSource τ σ Y₂ C₂)
    (hτ : 0 < τ.im) (hindep : IndepPeriods τ σ)
    (hfin₁ : (Function.support (tripticChargeClass Y₁ τ σ)).Finite)
    (hfin₂ : (Function.support (tripticChargeClass Y₂ τ σ)).Finite)
    (hfin₁₂ : (Function.support (tripticChargeClass (fun z ↦ Y₁ z * Y₂ z) τ σ)).Finite) :
    tripticDivisor (fun z ↦ Y₁ z * Y₂ z) τ σ hfin₁₂
      = tripticDivisor Y₁ τ σ hfin₁ + tripticDivisor Y₂ τ σ hfin₂ := by
  ext g
  rw [Finsupp.add_apply]
  exact tripticOrbitCharge_mul h₁.mero h₂.mero h₁.finOrd h₂.finOrd
    (finiteShiftSupport_of_source h₁ hτ hindep (Quotient.out g))
    (finiteShiftSupport_of_source h₂ hτ hindep (Quotient.out g))

/-! ### Class members as units of the codiscrete germ ring -/

/-- A class member is eventually nonvanishing along the codiscrete filter. -/
theorem codiscrete_ne_zero_of_source (hY : TripticMultiplicativeSource τ σ Y Cst) :
    {z : ℂ | Y z ≠ 0} ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) := by
  rw [mem_codiscreteWithin_univ_iff]
  intro x
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (hY.mero x (Set.mem_univ x))).mp (hY.finOrd x)

/-- **A class member is a unit of the codiscrete germ ring**, with the pointwise reciprocal as
inverse. -/
def tripticSourceUnit (hY : TripticMultiplicativeSource τ σ Y Cst) :
    ((Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)ˣ where
  val := (Y : (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)
  inv := ((fun z ↦ 1 / Y z : ℂ → ℂ) : (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)
  val_inv := by
    rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
    filter_upwards [codiscrete_ne_zero_of_source hY] with z hz
    exact mul_one_div_cancel hz
  inv_val := by
    rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
    filter_upwards [codiscrete_ne_zero_of_source hY] with z hz
    exact one_div_mul_cancel hz

@[simp] theorem tripticSourceUnit_val (hY : TripticMultiplicativeSource τ σ Y Cst) :
    (tripticSourceUnit hY : (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)
      = (Y : (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ) := rfl

/-- **The multiplicative triptic class as a subgroup of the units of the codiscrete germ ring**:
units represented by class members. -/
def tripticSourceUnitClass (τ σ : ℂ) :
    Subgroup ((Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)ˣ where
  carrier := {x | ∃ (Y : ℂ → ℂ) (Cst : ℂ), TripticMultiplicativeSource τ σ Y Cst ∧
    (x : (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ) = ↑Y}
  one_mem' := ⟨fun _ ↦ (1 : ℂ), 0, tripticMultiplicativeSource_one τ σ, by
    rw [Units.val_one, ← Filter.Germ.coe_one]
    rfl⟩
  mul_mem' := by
    rintro x y ⟨Y₁, C₁, h₁, hx⟩ ⟨Y₂, C₂, h₂, hy⟩
    refine ⟨fun z ↦ Y₁ z * Y₂ z, C₁ + C₂, h₁.mul h₂, ?_⟩
    rw [Units.val_mul, hx, hy, ← Filter.Germ.coe_mul]
    rfl
  inv_mem' := by
    rintro x ⟨Y, C, h, hx⟩
    refine ⟨fun z ↦ 1 / Y z, 0 - C, (tripticMultiplicativeSource_one τ σ).div h, ?_⟩
    have hunit : (x : (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)
        * ((fun z ↦ 1 / Y z : ℂ → ℂ) : (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)
        = 1 := by
      rw [hx, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
      filter_upwards [codiscrete_ne_zero_of_source h] with z hz
      exact mul_one_div_cancel hz
    calc (↑x⁻¹ : (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)
        = ↑x⁻¹ * ((x : (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)
            * ((fun z ↦ 1 / Y z : ℂ → ℂ) :
              (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)) := by
          rw [hunit, mul_one]
      _ = (↑x⁻¹ * ↑x)
            * ((fun z ↦ 1 / Y z : ℂ → ℂ) :
              (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ) := by
          rw [mul_assoc]
      _ = ((fun z ↦ 1 / Y z : ℂ → ℂ) :
              (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ) := by
          rw [Units.inv_mul, one_mul]

/-- The chosen class representative of a member of the germ subgroup. -/
def tripticGermRep (x : ↥(tripticSourceUnitClass τ σ)) : ℂ → ℂ := x.2.choose

/-- The mixed constant of the chosen representative. -/
def tripticGermRepCst (x : ↥(tripticSourceUnitClass τ σ)) : ℂ := x.2.choose_spec.choose

theorem tripticGermRep_source (x : ↥(tripticSourceUnitClass τ σ)) :
    TripticMultiplicativeSource τ σ (tripticGermRep x) (tripticGermRepCst x) :=
  x.2.choose_spec.choose_spec.1

theorem tripticGermRep_coe (x : ↥(tripticSourceUnitClass τ σ)) :
    ((x : ((Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)ˣ) :
      (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ) = ↑(tripticGermRep x) :=
  x.2.choose_spec.choose_spec.2

/-- Any class representative of a germ-subgroup member has the divisor of the chosen one. -/
theorem tripticDivisor_rep_congr (x : ↥(tripticSourceUnitClass τ σ))
    {Z : ℂ → ℂ} {CZ : ℂ} (hZ : TripticMultiplicativeSource τ σ Z CZ)
    (hcoe : ((x : ((Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)ˣ) :
      (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ) = ↑Z)
    (hfinx : (Function.support (tripticChargeClass (tripticGermRep x) τ σ)).Finite)
    (hfinZ : (Function.support (tripticChargeClass Z τ σ)).Finite) :
    tripticDivisor (tripticGermRep x) τ σ hfinx = tripticDivisor Z τ σ hfinZ := by
  refine tripticDivisor_congr ?_ hfinx hfinZ
  rw [← Filter.Germ.coe_eq, ← tripticGermRep_coe x, hcoe]

/-! ### The divisor homomorphism -/

/-- The integral orbit divisor of a germ-subgroup member. -/
def tripticGermDivisor (hτ : 0 < τ.im) (x : ↥(tripticSourceUnitClass τ σ)) :
    (ℂ ⧸ tripticPeriodGroup τ σ) →₀ ℤ :=
  tripticDivisor (tripticGermRep x) τ σ
    (finite_support_tripticChargeClass (tripticGermRep_source x) hτ)

/-- **The divisor homomorphism `D : M →+ ℤ[ℂ/H₃]`** on the additive form of the germ
subgroup. -/
def tripticDivisorHom (hτ : 0 < τ.im) (hindep : IndepPeriods τ σ) :
    Additive ↥(tripticSourceUnitClass τ σ) →+ ((ℂ ⧸ tripticPeriodGroup τ σ) →₀ ℤ) where
  toFun x := tripticGermDivisor hτ (Additive.toMul x)
  map_zero' := by
    have hone : TripticMultiplicativeSource τ σ (fun _ : ℂ ↦ (1 : ℂ)) 0 :=
      tripticMultiplicativeSource_one τ σ
    have hcoe : ((((1 : ↥(tripticSourceUnitClass τ σ)) :
        ((Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)ˣ)) :
        (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ) = ↑(fun _ : ℂ ↦ (1 : ℂ)) := by
      rw [Subgroup.coe_one, Units.val_one, ← Filter.Germ.coe_one]
      rfl
    have hfin1 : (Function.support (tripticChargeClass (fun _ : ℂ ↦ (1 : ℂ)) τ σ)).Finite :=
      finite_support_tripticChargeClass hone hτ
    have h := tripticDivisor_rep_congr (τ := τ) (σ := σ) 1 hone hcoe
      (finite_support_tripticChargeClass (tripticGermRep_source 1) hτ) hfin1
    have hzero : tripticDivisor (fun _ : ℂ ↦ (1 : ℂ)) τ σ hfin1 = 0 := by
      ext g
      exact tripticOrbitCharge_one σ (Quotient.out g)
    exact h.trans hzero
  map_add' := by
    intro x y
    set x' := Additive.toMul x
    set y' := Additive.toMul y
    have hx := tripticGermRep_source (τ := τ) (σ := σ) x'
    have hy := tripticGermRep_source (τ := τ) (σ := σ) y'
    have hmul : TripticMultiplicativeSource τ σ
        (fun z ↦ tripticGermRep x' z * tripticGermRep y' z)
        (tripticGermRepCst x' + tripticGermRepCst y') := hx.mul hy
    have hcoe : (((x' * y' : ↥(tripticSourceUnitClass τ σ)) :
        ((Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)ˣ) :
        (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)
        = ↑(fun z ↦ tripticGermRep x' z * tripticGermRep y' z) := by
      rw [Subgroup.coe_mul, Units.val_mul, tripticGermRep_coe x', tripticGermRep_coe y',
        ← Filter.Germ.coe_mul]
      rfl
    have hfinmul : (Function.support (tripticChargeClass
        (fun z ↦ tripticGermRep x' z * tripticGermRep y' z) τ σ)).Finite :=
      finite_support_tripticChargeClass hmul hτ
    have h := tripticDivisor_rep_congr (τ := τ) (σ := σ) (x' * y') hmul hcoe
      (finite_support_tripticChargeClass (tripticGermRep_source (x' * y')) hτ) hfinmul
    have hadd := tripticDivisor_mul hx hy hτ hindep
      (finite_support_tripticChargeClass hx hτ)
      (finite_support_tripticChargeClass hy hτ) hfinmul
    have hxy : Additive.toMul (x + y) = x' * y' := rfl
    show tripticGermDivisor hτ (Additive.toMul (x + y))
      = tripticGermDivisor hτ x' + tripticGermDivisor hτ y'
    rw [hxy]
    exact h.trans hadd

/-- **Every single class is realized**: the translated elliptic gamma unit has divisor
`[g]`. -/
theorem tripticDivisorHom_single (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
    (g : ℂ ⧸ tripticPeriodGroup τ σ) :
    ∃ x : Additive ↥(tripticSourceUnitClass τ σ),
      tripticDivisorHom hτ hindep x = Finsupp.single g 1 := by
  have hmem := tripticMultiplicativeSource_ellipticGammaConeTranslate
    (τ := τ) (σ := σ) hτ hσ (Quotient.out g)
  refine ⟨Additive.ofMul ⟨tripticSourceUnit hmem,
    ⟨ellipticGammaConeTranslate τ σ (Quotient.out g), -(2 * (Real.pi : ℂ) * Complex.I),
      hmem, rfl⟩⟩, ?_⟩
  have hcoe : ((((⟨tripticSourceUnit hmem, _⟩ : ↥(tripticSourceUnitClass τ σ))) :
      ((Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)ˣ) :
      (Filter.codiscreteWithin (Set.univ : Set ℂ)).Germ ℂ)
      = ↑(ellipticGammaConeTranslate τ σ (Quotient.out g)) := rfl
  have hfinΓ : (Function.support
      (tripticChargeClass (ellipticGammaConeTranslate τ σ (Quotient.out g)) τ σ)).Finite :=
    finite_support_tripticChargeClass hmem hτ
  have h := tripticDivisor_rep_congr (τ := τ) (σ := σ) _ hmem hcoe
    (finite_support_tripticChargeClass (tripticGermRep_source _) hτ) hfinΓ
  refine h.trans ?_
  ext c
  rw [Finsupp.single_apply]
  have happ : tripticDivisor (ellipticGammaConeTranslate τ σ (Quotient.out g)) τ σ hfinΓ c
      = tripticOrbitCharge (ellipticGammaConeTranslate τ σ (Quotient.out g)) σ
        (Quotient.out c) := rfl
  rw [happ]
  by_cases hgc : g = c
  · rw [if_pos hgc]
    refine tripticOrbitCharge_ellipticGammaConeTranslate_of_mem hτ hσ hindep ?_
    have hclass : (QuotientAddGroup.mk (Quotient.out c) : ℂ ⧸ tripticPeriodGroup τ σ) = g := by
      rw [QuotientAddGroup.out_eq' c, hgc]
    exact (periodGroupMem_sub_out_iff (Quotient.out c) g).mpr hclass
  · rw [if_neg hgc]
    refine tripticOrbitCharge_ellipticGammaConeTranslate_of_notMem hτ hσ ?_
    intro hmem'
    have hclass := (periodGroupMem_sub_out_iff (Quotient.out c) g).mp hmem'
    rw [QuotientAddGroup.out_eq' c] at hclass
    exact hgc hclass.symm

/-! ### The effective quotient and the verbatim Kummer classification -/

/-- **The effective quotient `M/M_DA ≅ ℤ[ℂ/H₃]`**: the divisor homomorphism induces an
isomorphism of the germ class group modulo its kernel onto the free abelian group on the orbit
space. -/
def tripticSourceQuotientEquiv (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ) :
    (Additive ↥(tripticSourceUnitClass τ σ) ⧸ (tripticDivisorHom hτ hindep).ker)
      ≃+ ((ℂ ⧸ tripticPeriodGroup τ σ) →₀ ℤ) :=
  sourceQuotientEquiv (tripticDivisorHom hτ hindep) (tripticDivisorHom_single hτ hσ hindep)

/-- **The Kummer root criterion on the germ class group, verbatim from the abstract
classification**: a germ class member has an `m`-th root modulo the kernel of the divisor map
exactly when `m` divides the content of its divisor. -/
theorem tripticSource_hasSourceRootModuloKernel_iff_content_dvd
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ) (m : ℕ)
    (x : Additive ↥(tripticSourceUnitClass τ σ)) :
    HasSourceRootModuloKernel (tripticDivisorHom hτ hindep) m x
      ↔ m ∣ integralOrbitDivisorContent (tripticDivisorHom hτ hindep x) :=
  hasSourceRootModuloKernel_iff_content_dvd_of_single (tripticDivisorHom hτ hindep)
    (tripticDivisorHom_single hτ hσ hindep) m x

/-- **Uniqueness of roots modulo the kernel**, verbatim from the abstract classification. -/
theorem tripticSource_root_unique_mod_kernel
    (hτ : 0 < τ.im) (hindep : IndepPeriods τ σ) {m : ℕ} (hm : m ≠ 0)
    {x z₁ z₂ : Additive ↥(tripticSourceUnitClass τ σ)}
    (h₁ : x - m • z₁ ∈ (tripticDivisorHom hτ hindep).ker)
    (h₂ : x - m • z₂ ∈ (tripticDivisorHom hτ hindep).ker) :
    z₁ - z₂ ∈ (tripticDivisorHom hτ hindep).ker :=
  sourceRoot_unique_mod_kernel (tripticDivisorHom hτ hindep) hm h₁ h₂

/-! ### The kernel is the differentially algebraic part -/

/-- **The kernel of the divisor homomorphism is exactly the differentially algebraic part of the
class**: a germ class member maps to zero exactly when the logarithmic derivative of its
representative is differentially algebraic. -/
theorem mem_ker_tripticDivisorHom_iff
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ))
    (x : Additive ↥(tripticSourceUnitClass τ σ)) :
    x ∈ (tripticDivisorHom hτ hindep).ker
      ↔ DifferentiallyAlgebraic
        (toMeromorphicNFOn (logDeriv (tripticGermRep (Additive.toMul x)))
          (Set.univ : Set ℂ)) := by
  set x' := Additive.toMul x
  have hx := tripticGermRep_source (τ := τ) (σ := σ) x'
  have hfin := finite_support_tripticChargeClass hx hτ
  have hker : x ∈ (tripticDivisorHom hτ hindep).ker
      ↔ ∀ p : ℂ, tripticOrbitCharge (tripticGermRep x') σ p = 0 := by
    constructor
    · intro h p
      have happ : tripticDivisorHom hτ hindep x (QuotientAddGroup.mk p)
          = tripticOrbitCharge (tripticGermRep x') σ p :=
        tripticDivisor_mk hx hfin p
      rw [AddMonoidHom.mem_ker] at h
      rw [← happ, h]
      rfl
    · intro h
      rw [AddMonoidHom.mem_ker]
      ext g
      exact h (Quotient.out g)
  rw [hker]
  constructor
  · intro hcharge
    exact (differentiallyAlgebraic_logDeriv_of_vanishing_orbitCharge_source hx
      hτ hσ hindep hindepτ hindepσ hcharge).2
  · intro hDA p
    exact tripticOrbitCharge_eq_zero_of_differentiallyAlgebraic_source hx
      hτ hσ hindep hindepτ hindepσ hperiods hDA p

end

end GaloisForLFunctions.HTGeometry
