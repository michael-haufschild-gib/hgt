import GaloisForLFunctions.ArtinMertens.ThePrimeIdealsSatisfyChebyshevBounds
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! Multiplying the norms of the prime-power factors of a nonzero
rational integer gives its absolute field norm. -/

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.Reciprocity

variable {K : Type*} [Field K] [NumberField K]

theorem prod_ideal_norm_pow_multiplicity_natCast {n : ℕ} (hn : n ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ v : HeightOneSpectrum (𝓞 K),
      (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∏ v ∈ S, v.asIdeal.absNorm ^
      multiplicity v.asIdeal (Ideal.span {(n : 𝓞 K)}) = n ^ Module.finrank ℚ K := by
  let I : Ideal (𝓞 K) := Ideal.span {(n : 𝓞 K)}
  have hI : I ≠ ⊥ := by
    change Ideal.span {(n : 𝓞 K)} ≠ ⊥
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hn
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      v.asIdeal ^ multiplicity v.asIdeal I) ⊆ (S : Set _) := by
    intro v hv
    apply hS
    apply Ideal.dvd_span_singleton.mp
    by_contra h
    change ¬ v.asIdeal ∣ I at h
    apply hv
    change v.asIdeal ^ multiplicity v.asIdeal I = 1
    rw [multiplicity_eq_zero.mpr h, pow_zero]
  have hp : ∏ v ∈ S, v.asIdeal ^ multiplicity v.asIdeal I = I := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hf, Ideal.finprod_heightOneSpectrum_pow_multiplicity hI]
  have h := congrArg Ideal.absNorm hp
  simp only [map_prod, map_pow, I, GaloisForLFunctions.ArtinMertens.absNorm_span_natCast,
    RingOfIntegers.rank] at h
  exact h

end GlobalTheory.Reciprocity
