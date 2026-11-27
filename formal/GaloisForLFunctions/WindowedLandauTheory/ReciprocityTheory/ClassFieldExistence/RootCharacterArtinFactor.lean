import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.KummerOpenClassField

/-! A continuous character of exponent dividing n factors injectively
through a finite Artin quotient when the base contains the n-th roots of unity. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField

namespace GlobalTheory.Kummer

open GlobalTheory.Reciprocity

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {A : Type*} [Group A] [TopologicalSpace A] [DiscreteTopology A]

theorem exists_artin_factor_of_roots (χ : CompactIdeleClassQuotient K →* A) (hc : Continuous χ)
    (hexp : ∀ x, χ x ^ n = 1) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (L : IntermediateField K (sUnitRadicalExtension K S n))
      (hL : IsAbelianGalois K L), letI := hL
      ∃ (f : IdeleGroup K →* Gal(L/K)) (g : Gal(L/K) →* A),
        Continuous f ∧ Function.Surjective f ∧ IsFiniteIdelicArtin f ∧
        Function.Injective g ∧ g.comp f = χ.comp (toCompactIdeleClassQuotient K) := by
  have ho : IsOpen (χ.ker : Set (CompactIdeleClassQuotient K)) :=
    (isOpen_discrete ({1} : Set A)).preimage hc
  have hpow (x : CompactIdeleClassQuotient K) : x ^ n ∈ χ.ker :=
    MonoidHom.mem_ker.mpr ((map_pow χ x n).trans (hexp x))
  obtain ⟨S, L, hL, f, hf, hs, hk, ha⟩ :=
    exists_finite_idelic_artin_of_open_of_roots n χ.ker ho hpow
  let θ := χ.comp (toCompactIdeleClassQuotient K)
  have he : f.ker = θ.ker := hk.trans (MonoidHom.comap_ker χ _)
  let g := f.liftOfSurjective hs ⟨θ, he.le⟩
  have hgf : g.comp f = θ :=
    f.liftOfRightInverse_comp _ (Function.rightInverse_surjInv hs) ⟨θ, he.le⟩
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨x, rfl⟩ := hs y
    change (g.comp f) x = 1 at hy
    rw [hgf] at hy
    exact MonoidHom.mem_ker.mp (he.symm ▸ MonoidHom.mem_ker.mpr hy)
  exact ⟨S, L, hL, f, g, hf, hs, ha, hinj, hgf⟩

end GlobalTheory.Kummer
