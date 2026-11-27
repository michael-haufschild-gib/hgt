import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RadicalArtinKernel
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.FixedFieldIdelicKernel
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.OpenIdelicCongruences

/-! For an open idelic congruence subgroup of exponent dividing n, the
S-unit radical field contains its class field when the n-th roots of
unity lie in the number field. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions

namespace GlobalTheory.Kummer

open GlobalTheory.Reciprocity GlobalTheory.Reciprocity.IdeleGroup GlobalTheory.Reciprocity.IdeleRay

variable {K : Type} [Field K] [NumberField K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]

theorem exists_finite_idelic_artin_of_open_of_roots
    (N : Subgroup (CompactIdeleClassQuotient K)) (hN : IsOpen (N : Set (CompactIdeleClassQuotient K)))
    (hpow : ∀ x : CompactIdeleClassQuotient K, x ^ n ∈ N) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (L : IntermediateField K (sUnitRadicalExtension K S n))
      (hL : IsAbelianGalois K L),
      letI := hL
      ∃ ψ : IdeleGroup K →* Gal(L/K),
        Continuous ψ ∧ Function.Surjective ψ ∧ ψ.ker = N.comap (toCompactIdeleClassQuotient K) ∧
        IsFiniteIdelicArtin ψ := by
  classical
  obtain ⟨S₀, hS₀⟩ := exists_sup_supportedIdeles_eq_top (K := K)
  have hn : Ideal.span {(n : 𝓞 K)} ≠ ⊥ :=
    fun h => (Nat.cast_ne_zero.mpr (NeZero.ne n)) (Ideal.span_singleton_eq_bot.mp h)
  let m : Modulus K := ⟨Ideal.span {(n : 𝓞 K)}, hn, ∅⟩
  let P := (finite_primes_dvd m).toFinset
  obtain ⟨S, hS, hPS⟩ := exists_powerCongruence_map_le_open N hN hpow (S₀ ∪ P)
  have hfin (v : HeightOneSpectrum (𝓞 K)) (hv : (n : 𝓞 K) ∈ v.asIdeal) : v ∈ S :=
    hS (Finset.mem_union_right _ ((finite_primes_dvd m).mem_toFinset.mpr (Ideal.dvd_span_singleton.mpr hv)))
  have hJ : (diagonal K).range ⊔ supportedIdeles (K := K) (S : Set _) = ⊤ := by
    rw [eq_top_iff, ← hS₀]
    exact sup_le_sup_left (supportedIdeles_mono fun _ hv => hS (Finset.mem_union_left _ hv)) _
  let C := N.comap (toCompactIdeleClassQuotient K)
  have hle : (diagonal K).range ⊔ powerCongruence n S ≤ C := by
    apply sup_le
    · rintro _ ⟨a, rfl⟩
      exact Subgroup.mem_comap.mpr ((toCompactIdeleClassQuotient_diagonal K a).symm ▸ N.one_mem)
    · exact Subgroup.map_le_iff_le_comap.mp hPS
  let M := sUnitRadicalExtension K S n
  letI : NumberField M := NumberField.of_module_finite K M
  letI : Fintype Gal(M/K) := Fintype.ofFinite _
  obtain ⟨q, φ, -, -, hφ, hr, hq⟩ := exists_sUnitRadical_artin_exact S n hfin hJ
  obtain ⟨L, hL, ψ, hψc, hψs, hψ, hArt⟩ := exists_finite_idelic_artin_of_kernel_le (M := M) q φ
    (fun a => MonoidHom.mem_ker.mp (hφ.symm ▸ Subgroup.mem_sup_left ⟨a, rfl⟩))
    (fun v hv => not_not.mp fun h => hv ((hr v).mpr h)) hq C (hφ.symm ▸ hle)
  exact ⟨S, L, hL, ψ, hψc, hψs, hψ, hArt⟩

end GlobalTheory.Kummer
