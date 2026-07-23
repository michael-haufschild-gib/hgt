import GaloisForLFunctions.HTGeometry.FiniteFamilySynchronizedJetEscapeLaw
import GaloisForLFunctions.RHTower.GammaDigammaZetaXiSynchronizedJetEscapeLaw

/-!
# Gamma--digamma--zeta--Xi arbitrary-window escape universality

The four classical sources are individually constant-coefficient differentially transcendental.
The generic finite-family capacity theorem therefore applies not only to an initial derivative
segment but to every finite set of derivative orders.  Any window containing more than four times
the dictionary dimension contains one order missed simultaneously by all four sources.
-/

namespace GaloisForLFunctions

noncomputable section

/-- **Gamma--digamma--zeta--Xi arbitrary-window escape universality law.**  Every finite set of
orders whose cardinality exceeds the combined four-source dictionary capacity contains a single
order at which all four derivative towers escape the dictionary. -/
theorem exists_synchronized_gamma_digamma_zeta_xi_jet_escape_in_finset
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (s : Finset ℕ) (hcard : 4 * Module.finrank ℂ V < s.card) :
    ∃ n ∈ s,
      iteratedDeriv n Complex.Gamma ∉ V ∧
      iteratedDeriv n Complex.digamma ∉ V ∧
      iteratedDeriv n riemannZeta ∉ V ∧
      iteratedDeriv n RHTower.xi ∉ V := by
  let sources : Fin 4 → (ℂ → ℂ) :=
    ![Complex.Gamma, Complex.digamma, riemannZeta, RHTower.xi]
  have hsources : ∀ i,
      HTGeometry.ConstantCoefficientDifferentiallyTranscendental (sources i) := by
    intro i
    fin_cases i
    · exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
        hypertranscendental_gamma
    · exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
        hypertranscendental_digamma
    · exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
        hypertranscendental_riemannZeta
    · exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
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
