import GaloisForLFunctions.RHTower.JointAncestrySparseChainExclusion
import GaloisForLFunctions.RHTower.JointAncestryConstantVectorDyadicShellDetection

/-!
# The sparsest JAS form of RH: doubly exponential windows and infinitely many dyadic shells

Under quasi-RH the level-one log-weight window tests on the doubly exponential windows
`(2^{2^k}, 2^{2^{k+1}}]` exclude an off-line chain, and without a chain a maximal off-line zero
makes the constant-vector test negative on every large dyadic shell `(N, 2N]`.  Hence:

* RH ⟺ quasi-RH ∧ window positivity on the doubly exponential windows ∧ constant-vector
  positivity on infinitely many dyadic shells
  (`riemannHypothesis_iff_quasi_and_doubleExpWindows_and_frequently_shells`);
* the same with single-prime positivity at some level `σ < ½` in place of quasi-RH
  (`riemannHypothesis_iff_singlePrime_and_doubleExpWindows_and_frequently_shells`).

The second conjunct is a doubly exponentially sparse family of windows and the third an arbitrary
infinite sequence of fixed-ratio shells; each test carries one complex parameter.
-/

open Filter

namespace RHTower

/-- **RH ⟺ quasi-RH ∧ doubly exponential window positivity ∧ shell positivity infinitely often.** -/
theorem riemannHypothesis_iff_quasi_and_doubleExpWindows_and_frequently_shells :
    RiemannHypothesis ↔
      (∃ alpha : ℝ, 0 ≤ alpha ∧ alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha) ∧
        JasWindowPositivityOn 1 doubleExpIndices ∧
        ∃ᶠ N : ℕ in atTop, JasConstProductPositiveOn (jasPrimeWindow N (2 * N)) 1 := by
  constructor
  · intro hRH
    obtain ⟨hq, hW, -⟩ := riemannHypothesis_iff_quasi_and_doubleExpWindows_and_dyadicScales.mp hRH
    exact ⟨hq, hW, frequently_jasConstProductPositiveOn_shell_of_riemannHypothesis hRH⟩
  · rintro ⟨⟨alpha, h0, h1, hXi⟩, hW, hfr⟩
    exact riemannHypothesis_iff_not_jasOffLineChain_and_frequently_jasConstProductPositiveOn_shell.mpr
      ⟨not_jasOffLineChain_of_quasi_of_jasWindowPositivityOn h0 h1 hXi hW
        chainRichWindows_doubleExp, hfr⟩

/-- **RH ⟺ single-prime positivity below level `½` ∧ doubly exponential window positivity ∧ shell
positivity infinitely often.** -/
theorem riemannHypothesis_iff_singlePrime_and_doubleExpWindows_and_frequently_shells :
    RiemannHypothesis ↔
      (∃ (X : ℕ) (σ : ℝ), 0 ≤ σ ∧ σ < 1 / 2 ∧ JasSinglePrimePositiveAbove X σ) ∧
        JasWindowPositivityOn 1 doubleExpIndices ∧
        ∃ᶠ N : ℕ in atTop, JasConstProductPositiveOn (jasPrimeWindow N (2 * N)) 1 := by
  constructor
  · intro hRH
    obtain ⟨hS, hW, -⟩ :=
      riemannHypothesis_iff_singlePrime_and_doubleExpWindows_and_dyadicScales.mp hRH
    exact ⟨hS, hW, frequently_jasConstProductPositiveOn_shell_of_riemannHypothesis hRH⟩
  · rintro ⟨⟨X, σ, hσ0, hσ, hS⟩, hW, hfr⟩
    exact riemannHypothesis_iff_quasi_and_doubleExpWindows_and_frequently_shells.mpr
      ⟨⟨max σ (1 / 4), le_trans hσ0 (le_max_left _ _), max_lt hσ (by norm_num),
        xiZeroHalfPlaneBound_of_jasSinglePrimePositiveAbove hσ0 hσ hS⟩, hW, hfr⟩

end RHTower
