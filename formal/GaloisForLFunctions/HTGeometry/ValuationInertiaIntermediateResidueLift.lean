import GaloisForLFunctions.HTGeometry.ValuationInertiaIntermediateBase
import GaloisForLFunctions.HTGeometry.ValuationSubringDecompositionOrder

/-!
# The label of a place lifts a Galois element into inertia

Let `L/F` be Galois with a Dedekind base `A` of `F`, let `W` be a valuation subring of `L` over `A`,
and let `M` be an intermediate field.  A Galois element that stabilises `W` and acts trivially on
the residues of the integral closure of `A` in `M` is, *on `M` itself*, indistinguishable from an
element of the inertia group:

```text
exists_mem_inertia_eq_on_intermediateField
    g • W = W  and  g fixes the residues of the intermediate base
      ⟹  ∃ i ∈ inertia, ∀ x : M, g x = i x
```

The mechanism is that the decomposition group of `W` over `M` already realises every automorphism of
the residue field of `W` over the residue field of the intermediate centre — mathlib's
`Ideal.Quotient.stabilizerHom_surjective` — so the correcting factor can be chosen inside
`Gal(L/M)`, which acts as the identity on `M`.

The consequence used by a covering is a *count*: the fibre of the reduced label through a point is
contained in one inertia orbit, so it has at most `|I|` elements.  No residue-degree computation is
needed; the residue degree cancels between the two levels.

## Main results

* `smulCommClass_intermediate`, `liesOverCentre` — the intermediate Galois action and its centre.
* `exists_mem_inertia_eq_on_intermediateField` — **the lift.**
* `exists_mem_inertiaSubgroup_eq_on_intermediateField` — the same in valuation-subgroup form.
-/

namespace GaloisForLFunctions.HTGeometry
namespace ValuationInertia

open IsLocalRing IsDedekindDomain
open scoped Pointwise
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

variable {A L : Type*} [CommRing A] [IsDedekindDomain A]
variable {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
variable [Field L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
variable [FiniteDimensional F L] [IsGalois F L]

theorem integralClosureTop_mem (W : ValuationSubring L) (hAW : ∀ a : A, algebraMap A L a ∈ W)
    (x : integralClosure A L) : algebraMap (integralClosure A L) L x ∈ W :=
  mem_of_isIntegral W hAW x.property

variable (M : IntermediateField F L)

theorem smulCommClass_intermediate :
    SMulCommClass (L ≃ₐ[M] L) (integralClosure A M) (integralClosure A L) := by
  refine ⟨fun g b x => ?_⟩
  apply Subtype.ext
  have hbL : algebraMap (integralClosure A M) L b = algebraMap (M : Type _) L (b : M) := rfl
  have hb : g (algebraMap (integralClosure A M) L b) = algebraMap (integralClosure A M) L b := by
    rw [hbL]; exact g.commutes _
  have hsmul : ∀ y : integralClosure A L,
      ((b • y : integralClosure A L) : L)
        = algebraMap (integralClosure A M) L b * (y : L) := by
    intro y
    rw [Algebra.smul_def]
    rfl
  show ((g • (b • x) : integralClosure A L) : L) = ((b • (g • x) : integralClosure A L) : L)
  rw [integralClosure.coe_smul, hsmul, hsmul, integralClosure.coe_smul]
  show g (algebraMap (integralClosure A M) L b * (x : L)) = _
  rw [map_mul, hb]
  rfl

variable (W : ValuationSubring L) (hAW : ∀ a : A, algebraMap A L a ∈ W)

theorem comap_centerPrime_eq_intermediateCentre :
    (centerPrime W (integralClosureTop_mem W hAW)).comap
        (algebraMap (integralClosure A M) (integralClosure A L))
      = intermediateCentre M W hAW := by
  rw [centerPrime, intermediateCentre, Ideal.comap_comap]
  congr 1

instance liesOverCentre :
    (centerPrime W (integralClosureTop_mem W hAW)).LiesOver (intermediateCentre M W hAW) :=
  ⟨(comap_centerPrime_eq_intermediateCentre M W hAW).symm⟩

/-- **A Galois element that is trivial on the residues of an intermediate base agrees, on that
intermediate field, with an inertia element.** -/
theorem exists_mem_inertia_eq_on_intermediateField (hW : W ≠ ⊤)
    {g : L ≃ₐ[F] L} (hgW : g • W = W)
    (hres : ∀ b : integralClosure A M,
      g • (algebraMap (integralClosure A M) (integralClosure A L) b)
          - algebraMap (integralClosure A M) (integralClosure A L) b
        ∈ centerPrime W (integralClosureTop_mem W hAW)) :
    ∃ i : L ≃ₐ[F] L,
      i ∈ (centerPrime W (integralClosureTop_mem W hAW)).inertia (L ≃ₐ[F] L) ∧
      ∀ x : M, g (x : L) = i (x : L) := by
  classical
  haveI : IsDedekindDomain (integralClosure A M) :=
    IsIntegralClosure.isDedekindDomain A F M (integralClosure A M)
  haveI : IsDedekindDomain (integralClosure A L) :=
    IsIntegralClosure.isDedekindDomain A F L (integralClosure A L)
  haveI : IsFractionRing (integralClosure A M) M :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F M (integralClosure A M)
  haveI : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F L (integralClosure A L)
  haveI : Algebra.IsIntegral (integralClosure A M) (integralClosure A L) :=
    IsIntegralClosure.isIntegral_algebra (integralClosure A M) L
  haveI := smulCommClass_intermediate (A := A) M
  haveI : IsGaloisGroup (L ≃ₐ[M] L) (integralClosure A M) (integralClosure A L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ (M : Type _) L
  haveI : Algebra.IsInvariant (integralClosure A M) (integralClosure A L) (L ≃ₐ[M] L) :=
    inferInstance
  have hSW := integralClosureTop_mem (A := A) W hAW
  have hact : ∀ (u : L ≃ₐ[F] L) (x : integralClosure A L),
      algebraMap (integralClosure A L) L (u • x)
        = u • algebraMap (integralClosure A L) L x := fun _ _ => rfl
  have hgQ : g • centerPrime W hSW = centerPrime W hSW :=
    (smul_valuationSubring_eq_iff_smul_centerPrime_eq hact hSW hW g).mp hgW
  -- the quotient automorphism attached to `g`
  have hmap : centerPrime W hSW
      = Ideal.map ((MulSemiringAction.toRingEquiv (L ≃ₐ[F] L) (integralClosure A L) g :
          integralClosure A L ≃+* integralClosure A L) :
          integralClosure A L →+* integralClosure A L) (centerPrime W hSW) := by
    conv_lhs => rw [← hgQ]
    rw [Ideal.pointwise_smul_def]
    rfl
  set φ := Ideal.quotientEquiv (centerPrime W hSW) (centerPrime W hSW)
      (MulSemiringAction.toRingEquiv (L ≃ₐ[F] L) (integralClosure A L) g) hmap with hφ
  have hφmk : ∀ x : integralClosure A L,
      φ (Ideal.Quotient.mk (centerPrime W hSW) x)
        = Ideal.Quotient.mk (centerPrime W hSW) (g • x) := by
    intro x
    rw [hφ, Ideal.quotientEquiv_mk]
    rfl
  let ψ : (integralClosure A L ⧸ centerPrime W hSW)
      ≃ₐ[integralClosure A M ⧸ intermediateCentre M W hAW]
      (integralClosure A L ⧸ centerPrime W hSW) :=
    { φ with
      commutes' := by
        intro r
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
        show φ (algebraMap (integralClosure A M ⧸ intermediateCentre M W hAW)
            (integralClosure A L ⧸ centerPrime W hSW) (Ideal.Quotient.mk _ b))
          = algebraMap (integralClosure A M ⧸ intermediateCentre M W hAW)
            (integralClosure A L ⧸ centerPrime W hSW) (Ideal.Quotient.mk _ b)
        rw [Ideal.Quotient.algebraMap_mk_of_liesOver, hφmk]
        exact Ideal.Quotient.eq.mpr (hres b) }
  obtain ⟨h, hh⟩ := Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[M] L)
    (intermediateCentre M W hAW) (centerPrime W hSW) ψ
  have hmk : ∀ b : integralClosure A L,
      Ideal.Quotient.mk (centerPrime W hSW) ((h : L ≃ₐ[M] L) • b)
        = Ideal.Quotient.mk (centerPrime W hSW) (g • b) := by
    intro b
    have h1 : Ideal.Quotient.stabilizerHom (centerPrime W hSW) (intermediateCentre M W hAW)
        (L ≃ₐ[M] L) h (Ideal.Quotient.mk _ b) = ψ (Ideal.Quotient.mk _ b) := by rw [hh]
    rw [Ideal.Quotient.stabilizerHom_apply] at h1
    have h2 : Ideal.Quotient.mk (centerPrime W hSW) ((h : L ≃ₐ[M] L) • b)
        = Ideal.Quotient.mk (centerPrime W hSW) ((h : MulAction.stabilizer (L ≃ₐ[M] L)
            (centerPrime W hSW)) • b) := rfl
    rw [h2, h1]
    show φ _ = _
    rw [hφmk]
  set u : L ≃ₐ[F] L := AlgEquiv.restrictScalars F ((h : L ≃ₐ[M] L)⁻¹) with hu
  have hu_apply : ∀ y : L, u y = ((h : L ≃ₐ[M] L).symm) y := fun _ => rfl
  refine ⟨g * u, ?_, ?_⟩
  · intro x
    have hcancel : (h : L ≃ₐ[M] L) • (u • x) = x := by
      apply Subtype.ext
      rw [integralClosure.coe_smul, integralClosure.coe_smul]
      show (h : L ≃ₐ[M] L) (u (x : L)) = (x : L)
      rw [hu_apply]
      exact AlgEquiv.apply_symm_apply _ _
    have hgu : (g * u) • x = g • (u • x) := mul_smul _ _ _
    have hmem : g • (u • x) - x ∈ centerPrime W hSW := by
      rw [← Ideal.Quotient.eq, ← hmk, hcancel]
    rw [hgu]
    exact hmem
  · intro x
    have hfix : ((h : L ≃ₐ[M] L).symm) ((x : M) : L) = ((x : M) : L) :=
      (h : L ≃ₐ[M] L).symm.commutes x
    rw [AlgEquiv.mul_apply, hu_apply, hfix]

/-- **The lift in valuation-subgroup form.**  The correcting element can be taken in the
valuation-theoretic inertia subgroup of `W` over `F`. -/
theorem exists_mem_inertiaSubgroup_eq_on_intermediateField (hW : W ≠ ⊤)
    {g : L ≃ₐ[F] L} (hgW : g • W = W)
    (hres : ∀ b : integralClosure A M,
      g • (algebraMap (integralClosure A M) (integralClosure A L)) b
          - (algebraMap (integralClosure A M) (integralClosure A L)) b
        ∈ centerPrime W (integralClosureTop_mem W hAW)) :
    ∃ i : W.decompositionSubgroup F, i ∈ W.inertiaSubgroup F ∧
      ∀ x : M, g ((x : M) : L) = ((i : L ≃ₐ[F] L)) ((x : M) : L) := by
  haveI : IsDedekindDomain (integralClosure A L) :=
    IsIntegralClosure.isDedekindDomain A F L (integralClosure A L)
  haveI : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F L (integralClosure A L)
  have hSW := integralClosureTop_mem (A := A) W hAW
  have hact : ∀ (u : L ≃ₐ[F] L) (x : integralClosure A L),
      algebraMap (integralClosure A L) L (u • x)
        = u • algebraMap (integralClosure A L) L x := fun _ _ => rfl
  obtain ⟨i, hi, hiM⟩ := exists_mem_inertia_eq_on_intermediateField M W hAW hW hgW hres
  exact ⟨toDecomposition W hSW hact hW hi,
    toDecomposition_mem_inertiaSubgroup W hSW hact hW hi, hiM⟩

end ValuationInertia
end GaloisForLFunctions.HTGeometry
