/-
# Decomposition order and transitivity for a valuation subring

mathlib's ramification-group file defines the decomposition and inertia subgroups of a valuation
subring and stops there; its Hilbert theory is ideal-theoretic.  Through the centre dictionary the
two remaining structural facts transport.

```text
exists_smul_valuationSubring_eq
    ** the Galois group acts transitively on the valuation subrings over one place of the base **
smul_valuationSubring_eq_iff_smul_centerPrime_eq
    a Galois element stabilises the subring exactly when it stabilises its centre
natCard_decompositionSubgroup_eq_natCard_inertiaSubgroup_mul_inertiaDegIn
    ** |D| = |I| · f **
```

The stabiliser identity is the only new argument: a Galois element carrying `W` to itself carries
its nonunits to its nonunits, because an inverse produced inside `W` after transport comes back
inside `W`.  Everything else is `Ideal.exists_smul_eq_of_isGaloisGroup` and
`Ideal.card_stabilizer_eq_card_inertia_mul_finrank` read through
`ValuationSubringInertiaDictionary` and `ValuationSubringGaloisTransport`.

The base field `F` is arbitrary among those over which `L` is Galois, so both statements apply at
every intermediate field of a tower, not only at the bottom.
-/
import GaloisForLFunctions.HTGeometry.ValuationSubringGaloisTransport
import GaloisForLFunctions.HTGeometry.ValuationInertiaRamificationIndex

namespace GaloisForLFunctions.HTGeometry
namespace ValuationInertia

noncomputable section

open IsLocalRing IsDedekindDomain
open scoped Pointwise

section Stabilizer

variable {S L : Type*} [CommRing S] [IsDedekindDomain S]
variable [Field L] [Algebra S L] [IsFractionRing S L]
variable {F : Type*} [Field F] [Algebra F L]
variable [MulSemiringAction (L ≃ₐ[F] L) S]
variable (hact : ∀ (g : L ≃ₐ[F] L) (x : S), algebraMap S L (g • x) = g • algebraMap S L x)

include hact

/-- A Galois element stabilising the valuation subring stabilises its centre. -/
theorem smul_centerPrime_le_of_smul_valuationSubring_eq
    {W : ValuationSubring L} (hSW : ∀ x : S, algebraMap S L x ∈ W)
    {g : L ≃ₐ[F] L} (hg : g • W = W) {x : S} (hx : x ∈ centerPrime W hSW) :
    g • x ∈ centerPrime W hSW := by
  rw [mem_centerPrime_iff, IsLocalRing.mem_maximalIdeal] at hx ⊢
  intro hunit
  refine hx ?_
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hunit
  have hyL : ((y : L)) ∈ W := y.property
  have hyval : algebraMap S L (g • x) * (y : L) = 1 := congrArg Subtype.val hy
  have hgx : algebraMap S L (g • x) = g • algebraMap S L x := hact g x
  rw [hgx] at hyval
  have hinvW : (g⁻¹ • (y : L)) ∈ W := by
    have hmem : (y : L) ∈ g • W := by
      rw [hg]
      exact hyL
    rw [ValuationSubring.mem_smul_pointwise_iff_exists] at hmem
    obtain ⟨a, ha, hay⟩ := hmem
    have heq : g⁻¹ • (y : L) = a := by
      rw [← hay, inv_smul_smul]
    rw [heq]
    exact ha
  refine isUnit_iff_exists_inv.mpr ⟨⟨g⁻¹ • (y : L), hinvW⟩, ?_⟩
  apply Subtype.ext
  show algebraMap S L x * (g⁻¹ • (y : L)) = 1
  have : g⁻¹ • (g • algebraMap S L x * (y : L)) = g⁻¹ • (1 : L) := by rw [hyval]
  rw [smul_mul', inv_smul_smul] at this
  simpa using this

/-- **A Galois element stabilises the valuation subring exactly when it stabilises its centre.** -/
theorem smul_valuationSubring_eq_iff_smul_centerPrime_eq
    {W : ValuationSubring L} (hSW : ∀ x : S, algebraMap S L x ∈ W) (hW : W ≠ ⊤)
    (g : L ≃ₐ[F] L) :
    g • W = W ↔ g • centerPrime W hSW = centerPrime W hSW := by
  constructor
  · intro hg
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hx
      have := smul_centerPrime_le_of_smul_valuationSubring_eq hact hSW hg hx
      rwa [smul_inv_smul] at this
    · intro x hx
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      have hginv : g⁻¹ • W = W := by
        conv_lhs => rw [← hg]
        rw [inv_smul_smul]
      exact smul_centerPrime_le_of_smul_valuationSubring_eq hact hSW hginv hx
  · intro hg
    exact smul_valuationSubring_eq_of_smul_centerPrime hact hSW hSW hW hW hg

end Stabilizer

section Fundamental

/-- **`|D| = |I| · f` for a valuation subring**, over any base field of the normal extension.
mathlib's `Ideal.card_stabilizer_eq_card_inertia_mul_finrank` is ideal-theoretic; the decomposition
subgroup of a valuation subring is the stabiliser of its centre, and the two inertia groups agree. -/
theorem natCard_decompositionSubgroup_eq_natCard_inertiaSubgroup_mul_inertiaDegIn
    {R T L : Type*} [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
    [FiniteDimensional F L] [IsGalois F L]
    [CommRing T] [IsDomain T] [Algebra R T] [Algebra T L] [IsScalarTower R T L]
    [IsIntegralClosure T R L]
    (p : Ideal R) [p.IsMaximal] [PerfectField p.ResidueField]
    (W : ValuationSubring L) (hW : W ≠ ⊤) (hRW : ∀ r : R, algebraMap R L r ∈ W)
    (hcent : ∀ r : R, (¬ IsUnit (⟨algebraMap R L r, hRW r⟩ : W)) ↔ r ∈ p) :
    Nat.card (W.decompositionSubgroup F)
      = Nat.card (W.inertiaSubgroup F) * Ideal.inertiaDegIn p T := by
  classical
  haveI : IsDedekindDomain T := IsIntegralClosure.isDedekindDomain R F L T
  haveI : Module.Finite R T := IsIntegralClosure.finite R F L T
  haveI : IsFractionRing T L := IsIntegralClosure.isFractionRing_of_finite_extension R F L T
  letI : MulSemiringAction (L ≃ₐ[F] L) T := IsIntegralClosure.MulSemiringAction R F L T
  have hSW : ∀ x : T, algebraMap T L x ∈ W := fun x =>
    mem_of_isIntegral W hRW
      ((IsIntegralClosure.isIntegral R L x).map (IsScalarTower.toAlgHom R T L))
  have hact : ∀ (g : L ≃ₐ[F] L) (x : T),
      algebraMap T L (g • x) = g • algebraMap T L x := fun g x =>
    algebraMap_galRestrict_apply R g x
  haveI : IsGaloisGroup (L ≃ₐ[F] L) R T := IsGaloisGroup.of_isFractionRing _ _ _ F L
  haveI : Finite (L ≃ₐ[F] L) := inferInstance
  have hinjRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective R F)
  have hinjRS : Function.Injective (algebraMap R T) := by
    intro x y hxy
    have := congrArg (algebraMap T L) hxy
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact hinjRL this
  haveI : Module.IsTorsionFree R T := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinjRS
  haveI : Module.Flat R T := inferInstance
  haveI : (centerPrime W hSW).LiesOver p := liesOver_centerPrime p W hRW hSW hcent
  have hstab : W.decompositionSubgroup F
      = MulAction.stabilizer (L ≃ₐ[F] L) (centerPrime W hSW) := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    exact smul_valuationSubring_eq_iff_smul_centerPrime_eq hact hSW hW g
  have hcard : Nat.card (W.decompositionSubgroup F)
      = Nat.card (MulAction.stabilizer (L ≃ₐ[F] L) (centerPrime W hSW)) := by
    rw [hstab]
  rw [hcard, Ideal.card_stabilizer_eq_card_inertia_mul_finrank p (centerPrime W hSW),
    natCard_inertia_eq_natCard_inertiaSubgroup W hSW hact hW,
    Ideal.inertiaDegIn_eq_inertiaDeg p (centerPrime W hSW) (L ≃ₐ[F] L)]

end Fundamental


/-- **Transitivity of the Galois action on the valuation subrings over one place of the base.**
mathlib's ramification-group file defines the decomposition and inertia subgroups of a valuation
subring but proves no transitivity; its ideal-theoretic transitivity
`Ideal.exists_smul_eq_of_isGaloisGroup` transports through the centre. -/
theorem exists_smul_valuationSubring_eq
    {R T L : Type*} [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
    [FiniteDimensional F L] [IsGalois F L]
    [CommRing T] [IsDomain T] [Algebra R T] [Algebra T L] [IsScalarTower R T L]
    [IsIntegralClosure T R L]
    (p : Ideal R) [p.IsMaximal]
    {W₁ W₂ : ValuationSubring L} (hW₁ : W₁ ≠ ⊤) (hW₂ : W₂ ≠ ⊤)
    (hRW₁ : ∀ r : R, algebraMap R L r ∈ W₁) (hRW₂ : ∀ r : R, algebraMap R L r ∈ W₂)
    (hcent₁ : ∀ r : R, (¬ IsUnit (⟨algebraMap R L r, hRW₁ r⟩ : W₁)) ↔ r ∈ p)
    (hcent₂ : ∀ r : R, (¬ IsUnit (⟨algebraMap R L r, hRW₂ r⟩ : W₂)) ↔ r ∈ p) :
    ∃ g : L ≃ₐ[F] L, g • W₁ = W₂ := by
  classical
  haveI : IsDedekindDomain T := IsIntegralClosure.isDedekindDomain R F L T
  haveI : Module.Finite R T := IsIntegralClosure.finite R F L T
  haveI : IsFractionRing T L := IsIntegralClosure.isFractionRing_of_finite_extension R F L T
  letI : MulSemiringAction (L ≃ₐ[F] L) T := IsIntegralClosure.MulSemiringAction R F L T
  have hSW₁ : ∀ x : T, algebraMap T L x ∈ W₁ := fun x =>
    mem_of_isIntegral W₁ hRW₁
      ((IsIntegralClosure.isIntegral R L x).map (IsScalarTower.toAlgHom R T L))
  have hSW₂ : ∀ x : T, algebraMap T L x ∈ W₂ := fun x =>
    mem_of_isIntegral W₂ hRW₂
      ((IsIntegralClosure.isIntegral R L x).map (IsScalarTower.toAlgHom R T L))
  have hact : ∀ (g : L ≃ₐ[F] L) (x : T),
      algebraMap T L (g • x) = g • algebraMap T L x := fun g x =>
    algebraMap_galRestrict_apply R g x
  haveI : IsGaloisGroup (L ≃ₐ[F] L) R T := IsGaloisGroup.of_isFractionRing _ _ _ F L
  haveI : Finite (L ≃ₐ[F] L) := inferInstance
  haveI h1 : (centerPrime W₁ hSW₁).LiesOver p := liesOver_centerPrime p W₁ hRW₁ hSW₁ hcent₁
  haveI h2 : (centerPrime W₂ hSW₂).LiesOver p := liesOver_centerPrime p W₂ hRW₂ hSW₂ hcent₂
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p (centerPrime W₁ hSW₁)
    (centerPrime W₂ hSW₂) (L ≃ₐ[F] L)
  exact ⟨g, smul_valuationSubring_eq_of_smul_centerPrime hact hSW₁ hSW₂ hW₁ hW₂ hg⟩


end

end ValuationInertia

end GaloisForLFunctions.HTGeometry
