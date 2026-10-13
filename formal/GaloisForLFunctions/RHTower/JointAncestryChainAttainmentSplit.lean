import GaloisForLFunctions.RHTower.WeilLagFunctionDensityZeroExcursion
import GaloisForLFunctions.RHTower.JointAncestryQuasiRHChainExclusion

/-!
# Route JAS: chains and attained tops are excluded by different tests

If RH fails, the off-line zeros either have a farthest member (an attained top) or form a chain.
Under quasi-RH (`Re ρ ≤ ½ + α` with `α < ½`) the two cases are excluded by two different families of
level-one JAS tests:
* the log-weight Bernoulli window tests on the windows `(n, n²]`, `n ≥ N₀`, exclude a chain
  (`not_jasOffLineChain_of_quasi_of_jasWindowPositivity_one`, from
  `one_add_sSup_le_of_jasWindowPositivity_of_chain`);
* the constant-vector interval tests exclude an attained top, and they are needed only at the
  log-scales outside a set of lower density zero
  (`riemannHypothesis_of_attainedTop_of_jasIntervalProductPositiveExcept_lowerAbel`).

**Theorem** (`riemannHypothesis_iff_quasi_and_jasWindowPositivity_and_jasPositiveExcept`). RH holds
iff quasi-RH holds, the window tests are positive at level one beyond some `N₀`, and the
constant-vector interval tests are positive at level one at every scale whose logarithm lies outside
a set of lower density zero.
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

open OneSidedConfiguration

/-- **Window positivity at level one excludes an off-line chain under quasi-RH.** -/
theorem not_jasOffLineChain_of_quasi_of_jasWindowPositivity_one {alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha) {N₀ : ℕ}
    (hW : JasWindowPositivity 1 N₀) : ¬ JasOffLineChain := by
  intro hch
  have h := one_add_sSup_le_of_jasWindowPositivity_of_chain halpha0 halpha hXi hW hch
  obtain ⟨q₁, hq₁⟩ := hch.1
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨alpha, by rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q⟩
  have h1 := le_csSup hbdd ⟨q₁, rfl⟩
  have h2 : 0 < |(q₁.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hq₁)
  simp only at h1
  linarith

/-- **Division of labour.** RH ⟺ quasi-RH ∧ level-one window positivity beyond some `N₀` ∧
level-one constant-vector interval positivity off a set of log-scales of lower density zero. -/
theorem riemannHypothesis_iff_quasi_and_jasWindowPositivity_and_jasPositiveExcept :
    RiemannHypothesis ↔
      (∃ alpha : ℝ, 0 ≤ alpha ∧ alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha) ∧
        (∃ N₀ : ℕ, JasWindowPositivity 1 N₀) ∧
        ∃ (X : ℕ) (S : Set ℝ), MeasurableSet S ∧ LowerDensityZero S ∧
          JasIntervalProductPositiveExcept X 1 S := by
  constructor
  · intro hRH
    obtain ⟨hPSD, hq⟩ := riemannHypothesis_iff_jasDressedPSD_one_and_quasi.mp hRH
    obtain ⟨-, hrest⟩ :=
      riemannHypothesis_iff_not_jasOffLineChain_and_jasPositiveExcept_lowerDensityZero.mp hRH
    exact ⟨hq, ⟨0, jasWindowPositivity_of_jasDressedPSD hPSD⟩, hrest⟩
  · rintro ⟨⟨alpha, h0, h1, hXi⟩, ⟨N₀, hW⟩, hrest⟩
    exact riemannHypothesis_iff_not_jasOffLineChain_and_jasPositiveExcept_lowerDensityZero.mpr
      ⟨not_jasOffLineChain_of_quasi_of_jasWindowPositivity_one h0 h1 hXi hW, hrest⟩

end

end RHTower
