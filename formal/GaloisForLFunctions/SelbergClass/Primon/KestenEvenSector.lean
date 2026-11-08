import GaloisForLFunctions.SelbergClass.Primon.KestenTailCyclicity
import GaloisForLFunctions.SelbergClass.Primon.SemicircleCharacterBasis
import GaloisForLFunctions.SelbergClass.Primon.SpectralReflection

/-!
# The likelihood Hilbert space is the even spectral sector

Completeness of the character basis identifies the closed prime-likelihood
span by vanishing odd coordinates. Actual spectral reflection then identifies
this space with the almost-everywhere even observables.
-/

open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- A semicircle observable belongs to the likelihood space exactly when all odd coordinates vanish. -/
theorem mem_likelihoodHilbert_iff_oddCoefficients (f : SemicircleL2) :
    f ∈ KestenLikelihoodHilbert ↔
      ∀ n : ℕ, inner ℝ (spectralCharacterVector (2 * n + 1)) f = 0 := by
  constructor
  · intro hf
    change f ∈ closure (kestenLikelihoodMap.range : Set SemicircleL2) at hf
    rw [← range_hardyLikelihoodEmbedding] at hf
    obtain ⟨x, rfl⟩ := hf
    intro n
    rw [real_inner_comm, inner_hardyLikelihoodEmbedding_oddCharacter]
  · intro hodd
    apply isClosed_closure.mem_of_tendsto (hasSum_spectralCharacters f)
    apply Filter.Eventually.of_forall
    intro s
    change (∑ n ∈ s, inner ℝ (spectralCharacterVector n) f • spectralCharacterVector n) ∈
      KestenLikelihoodHilbert
    apply KestenLikelihoodHilbert.sum_mem
    intro n _
    by_cases hn : n % 2 = 0
    · have he : n = 2 * (n / 2) := by omega
      rw [he]
      exact KestenLikelihoodHilbert.smul_mem _ (evenCharacter_mem_likelihoodHilbert _)
    · have he : n = 2 * (n / 2) + 1 := by omega
      rw [he, hodd, zero_smul]
      exact KestenLikelihoodHilbert.zero_mem


/-- Reflection multiplies the degree-`n` Fourier coordinate by its parity sign. -/
theorem inner_character_reflection (f : SemicircleL2) (n : ℕ) :
    inner ℝ (spectralCharacterVector n) (semicircleReflection f) =
      (-1 : ℝ) ^ n * inner ℝ (spectralCharacterVector n) f := by
  rw [← inner_semicircleReflection, semicircleReflection_character,
    inner_smul_left, conj_trivial]

/-- The prime-likelihood Hilbert space is the fixed subspace of actual spectral reflection. -/
theorem mem_likelihoodHilbert_iff_reflection_fixed (f : SemicircleL2) :
    f ∈ KestenLikelihoodHilbert ↔ semicircleReflection f = f := by
  constructor
  · intro hf
    have hodd := (mem_likelihoodHilbert_iff_oddCoefficients f).1 hf
    apply semicircleCharacterBasis.repr.injective
    ext n
    simp only [semicircleCharacterBasis_repr]
    rw [inner_character_reflection]
    by_cases hn : n % 2 = 0
    · have he : n = 2 * (n / 2) := by omega
      rw [he]
      simp [pow_mul]
    · have he : n = 2 * (n / 2) + 1 := by omega
      rw [he, hodd, mul_zero]
  · intro hf
    apply (mem_likelihoodHilbert_iff_oddCoefficients f).2
    intro n
    have h := inner_semicircleReflection (spectralCharacterVector (2 * n + 1)) f
    rw [semicircleReflection_oddCharacter, hf, inner_neg_left] at h
    linarith only [h]

/-- The closed likelihood span consists of all almost-everywhere even semicircle observables. -/
theorem mem_likelihoodHilbert_iff_even (f : SemicircleL2) :
    f ∈ KestenLikelihoodHilbert ↔
      (fun x => f (-x)) =ᵐ[(semicircleSpectralLaw : Measure ℝ)] f := by
  rw [mem_likelihoodHilbert_iff_reflection_fixed, semicircleReflection_fixed_iff]

/-- Every one-prime tail family is complete in the actual almost-everywhere even sector. -/
theorem mem_kestenTailClosure_iff_even (p : Nat.Primes) (f : SemicircleL2) :
    f ∈ (kestenTailSpan p).topologicalClosure ↔
      (fun x => f (-x)) =ᵐ[(semicircleSpectralLaw : Measure ℝ)] f := by
  rw [kestenTailSpan_closure, mem_likelihoodHilbert_iff_even]

/-- The Hardy realization fills every almost-everywhere even semicircle observable. -/
theorem range_hardyLikelihoodEmbedding_eq_even :
    Set.range hardyLikelihoodEmbedding =
      {f : SemicircleL2 | (fun x => f (-x)) =ᵐ[(semicircleSpectralLaw : Measure ℝ)] f} := by
  ext f
  rw [range_hardyLikelihoodEmbedding]
  exact mem_likelihoodHilbert_iff_even f

/-- The orthogonal complement of prime likelihoods is the negative reflection eigenspace. -/
theorem mem_orthogonal_likelihood_iff_reflection_neg (f : SemicircleL2) :
    f ∈ KestenLikelihoodHilbertᗮ ↔ semicircleReflection f = -f := by
  constructor
  · intro hf
    have heven (n : ℕ) : inner ℝ (spectralCharacterVector (2 * n)) f = 0 :=
      hf _ (evenCharacter_mem_likelihoodHilbert n)
    apply semicircleCharacterBasis.repr.injective
    ext n
    simp only [semicircleCharacterBasis_repr, inner_neg_right]
    rw [inner_character_reflection]
    by_cases hn : n % 2 = 0
    · have he : n = 2 * (n / 2) := by omega
      rw [he, heven, mul_zero, neg_zero]
    · have he : n = 2 * (n / 2) + 1 := by omega
      rw [he]
      simp [pow_add, pow_mul]
  · intro hf
    intro g hg
    have hgfix := (mem_likelihoodHilbert_iff_reflection_fixed g).1 hg
    have h := inner_semicircleReflection g f
    rw [hgfix, hf, inner_neg_right] at h
    linarith only [h]

/-- The orthogonal complement consists exactly of almost-everywhere odd observables. -/
theorem mem_orthogonal_likelihood_iff_odd (f : SemicircleL2) :
    f ∈ KestenLikelihoodHilbertᗮ ↔
      (fun x => f (-x)) =ᵐ[(semicircleSpectralLaw : Measure ℝ)] fun x => -f x := by
  rw [mem_orthogonal_likelihood_iff_reflection_neg]
  constructor
  · intro hf
    have h := semicircleReflection_ae f
    rw [hf] at h
    exact h.symm.trans (Lp.coeFn_neg f)
  · intro hf
    exact Lp.ext ((semicircleReflection_ae f).trans (hf.trans (Lp.coeFn_neg f).symm))

end
end GaloisForLFunctions.SelbergClass.Primon

