import GaloisForLFunctions.HTGeometry.SignedGammaFactorScale
import GaloisForLFunctions.RHTower.GammaDigammaZetaXiArbitraryWindowEscapeUniversalityLaw

/-!
# Affine Gamma–digamma–zeta–Xi arbitrary-window escape universality

The synchronized four-source escape theorem uses only constant-coefficient differential
transcendence of its source family.  Arbitrary nonzero affine rescalings and nonzero amplitudes of
Gamma and digamma retain hypertranscendence, so the same common-order escape holds uniformly over
independently chosen affine orbits of both archimedean sources.
-/

namespace GaloisForLFunctions

noncomputable section

/-- **Affine Gamma–digamma–zeta–Xi arbitrary-window escape universality law.**  Every derivative
window larger than the combined four-source dictionary capacity contains one order missed
simultaneously by independently affine-scaled Gamma and digamma, zeta, and completed Xi. -/
theorem exists_synchronized_affine_gamma_digamma_zeta_xi_jet_escape_in_finset
    {aGamma cGamma dGamma aDigamma cDigamma dDigamma : ℂ}
    (haGamma : aGamma ≠ 0) (hcGamma : cGamma ≠ 0)
    (haDigamma : aDigamma ≠ 0) (hcDigamma : cDigamma ≠ 0)
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (s : Finset ℕ) (hcard : 4 * Module.finrank ℂ V < s.card) :
    ∃ n ∈ s,
      iteratedDeriv n
          (fun z => aGamma * Complex.Gamma (cGamma * z + dGamma)) ∉ V ∧
      iteratedDeriv n
          (fun z => aDigamma * Complex.digamma (cDigamma * z + dDigamma)) ∉ V ∧
      iteratedDeriv n riemannZeta ∉ V ∧
      iteratedDeriv n RHTower.xi ∉ V := by
  let sources : Fin 4 → (ℂ → ℂ) :=
    ![fun z => aGamma * Complex.Gamma (cGamma * z + dGamma),
      fun z => aDigamma * Complex.digamma (cDigamma * z + dDigamma),
      riemannZeta,
      RHTower.xi]
  have hsources : ∀ i,
      HTGeometry.ConstantCoefficientDifferentiallyTranscendental (sources i) := by
    intro i
    fin_cases i
    · exact
        HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
          (hypertranscendental_smul_gamma_affine haGamma hcGamma)
    · exact
        HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
          (hypertranscendental_smul_digamma_affine haDigamma hcDigamma)
    · exact
        HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
          hypertranscendental_riemannZeta
    · exact
        HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
          RHTower.xi_hypertranscendental
  obtain ⟨n, hn, hescape⟩ :=
    HTGeometry.exists_common_iteratedDeriv_not_mem_of_card_mul_finrank_lt
      sources hsources V s (by simpa using hcard)
  refine ⟨n, hn, ?_, ?_, ?_, ?_⟩
  · simpa [sources] using hescape (0 : Fin 4)
  · simpa [sources] using hescape (1 : Fin 4)
  · simpa [sources] using hescape (2 : Fin 4)
  · simpa [sources] using hescape (3 : Fin 4)

end

end GaloisForLFunctions
