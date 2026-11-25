import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.SingletonLocalizationEquiv
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Flat.Localization

/-! Flatness of a dehomogenized chart gives flatness on every smaller coordinate intersection. -/

open DirectSum MvPolynomial TensorProduct

namespace GlobalTheory

private theorem isLocalizedModule_restrict {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    {f g c : A} (h : f ∣ g) (hg : g = c * f) :
    IsLocalizedModule.Away c (ModuleFraction.restrict (M := M) h) := by
  have hd : c ∣ g := hg.symm ▸ dvd_mul_right c f
  refine IsLocalizedModule.Away.mk_of_addCommGroup
    (ModuleFraction.isUnit_smul_of_dvd hd) (fun z => ?_) (fun z hz => ?_)
  · obtain ⟨k, m, rfl⟩ := ModuleFraction.exists_frac z
    exact ⟨k, ModuleFraction.frac f k m, by rw [ModuleFraction.restrict_frac h hg, map_smul]⟩
  · obtain ⟨k, m, rfl⟩ := ModuleFraction.exists_frac z
    rw [ModuleFraction.restrict_frac h hg, ModuleFraction.frac_eq_zero_iff] at hz
    obtain ⟨l, hl⟩ := hz
    refine ⟨l + k, ?_⟩
    rw [← map_smul, ModuleFraction.frac_eq_zero_iff]
    refine ⟨l, ?_⟩
    have hpow : f ^ l * c ^ (l + k) = g ^ l * c ^ k := by
      rw [hg, pow_add, mul_pow]
      ring
    rwa [← mul_smul, hpow, mul_smul]

private theorem flat_of_flat_localizedModule {R A M N : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A M] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (S : Submonoid A) (f : M →ₗ[A] N) [IsLocalizedModule S f] (h : Module.Flat R M) :
    Module.Flat R N := by
  rw [Module.Flat.iff_lTensor_injectiveₛ] at h ⊢
  intro P _ _ Q
  have hinj := IsLocalizedModule.map_injective S (AlgebraTensorModule.rTensor R Q f)
    (AlgebraTensorModule.rTensor R P f) (AlgebraTensorModule.lTensor A M Q.subtype) (h Q)
  rwa [IsLocalizedModule.map_lTensor] at hinj

private theorem flat_iff_flat_pieces {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (D : ℤ → Submodule R M) [Decomposition D] :
    Module.Flat R M ↔ ∀ n, Module.Flat R (D n) :=
  (Module.Flat.equiv_iff (decomposeLinearEquiv D)).trans Module.Flat.directSum_iff

theorem flat_homLoc_of_flat_specialization {ι R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
    (D : ℤ → Submodule R M) [PolyGradedSMul ι D] [Decomposition D]
    {i : ι} {s : Finset ι} (hi : i ∈ s) (n : ℤ)
    (hflat : Module.Flat R (QuotSMulTop (X i - 1 : MvPolynomial ι R) M)) :
    Module.Flat R (homLoc D s n) := by
  classical
  have h₁ : Module.Flat R (LocalizedModule.Away (xProd R {i}) M) := by
    apply (flat_iff_flat_pieces (homLoc D {i})).2
    intro j
    obtain ⟨e⟩ := nonempty_singletonHomLocEquiv_quotSMulTop D i j
    letI := hflat
    exact Module.Flat.of_linearEquiv e
  have hsub : ({i} : Finset ι) ⊆ s := Finset.singleton_subset_iff.2 hi
  have hc : xProd R s = xProd R (s \ {i}) * xProd R {i} := (Finset.prod_sdiff hsub).symm
  let ρ := ModuleFraction.restrict (M := M) (xProd_dvd R hsub)
  letI := isLocalizedModule_restrict (M := M) (xProd_dvd R hsub) hc
  have h₂ : Module.Flat R (LocalizedModule.Away (xProd R s) M) :=
    flat_of_flat_localizedModule (Submonoid.powers (xProd R (s \ {i}))) ρ h₁
  exact (flat_iff_flat_pieces (homLoc D s)).1 h₂ n

theorem flat_gradedCech_of_flat_specializations {ι R M : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [CommRing R] [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    (D : ℤ → Submodule R M) [PolyGradedSMul ι D] [Decomposition D]
    (hflat : ∀ i : ι, Module.Flat R (QuotSMulTop (X i - 1 : MvPolynomial ι R) M))
    (n : ℤ) (q : ℕ) : Module.Flat R ((gradedCech (ι := ι) D n).X q) :=
  (homLocDatum (ι := ι) D n).linearComplex_X_flat (fun h => homLocDatum_res_smul D h n) q
    fun _ ⟨i, hi⟩ => flat_homLoc_of_flat_specialization D hi n (hflat i)

end GlobalTheory
