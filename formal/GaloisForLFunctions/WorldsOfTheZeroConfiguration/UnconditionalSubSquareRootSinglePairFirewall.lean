import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheSignedGroupedEditCountsBelowTheSquareRoot
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheWorldOneScenarioTable
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# Unconditional Sub-Square-Root Single-Pair Firewall and RH `{0, 1, 2}`-Edit Realization

Combining the unconditional zero-free half-plane `zetaZeroAbscissa ≤ 20999 / 24000` with the
signed grouped prime edits (`sEdit`) and the World-I scenario table yields three unconditional
theorems clarifying the arithmetic firewall around a single off-line pair:

1. **Unconditional `(1/2, 27001/48000)` sub-square-root single-pair dichotomy**
   (`unconditional_subSqrt_singlePair_dichotomy`):
   For every `β ∈ (1/2, 27001 / 48000)` (`= (1/2, 9/16 + 1/48000)`) and every `γ ∈ ℝ`, either
   `ζ(β + iγ) = 0` (so `¬ RiemannHypothesis` holds outright), or there exists a `{0, 1, 2}`-prime
   Beurling edit `sEdit α β γ k₀` with sub-square-root integer norm count `c < 1/2` whose
   pole-cleared zeta function continues holomorphically below `Re s = 1/2` (`σ₁ < 1/2`) with zeros
   equal to those of `(s - 1) ζ(s)` plus `{β + iγ, β - iγ}`.

2. **Full `(1/2, 2/3)` single-pair realization under `RiemannHypothesis` and FE defect barrier**
   (`rh_subSqrt_singlePair_realization_and_defect_barrier`):
   Under `RiemannHypothesis`, for **every** `β ∈ (1/2, 2/3)` and **every** `γ ≠ 0`, there exists a
   `{0, 1, 2}`-multiplicity rational-prime edit `sEdit α β γ k₀` with sub-square-root integer norm
   count `c < 1/2` and holomorphic continuation across `Re s = 1/2` whose **exact** zero set in
   `{Re s > 1/2}` is the single conjugate pair `{β + iγ, β - iγ}`, while every Hamburger strip
   defect of `ζ_B` is unbounded, non-decaying, and not Abel-sublinear. Thus no sieve, `{0, 1, 2}`
   prime-multiplicity, `O(x^c)` (`c < 1/2`) norm-counting, or half-plane continuation argument can
   exclude a single off-line pair in `(1/2, 2/3)` without invoking the functional equation.

3. **Unconditional `(1/2, 15001/24000)` subpolynomial-defect dichotomy**
   (`unconditional_subpolynomialDefect_dichotomy_below_five_eighths`):
   For every `β₀ ∈ (1/2, 15001 / 24000)` (`= (1/2, 5/8 + 1/24000)`), `γ₀ ∈ ℝ`, `β_c ∈ (β₀, 1)`, and
   `P ∈ ℕ`, either `ζ(β₀ + iγ₀) = 0` (`¬ RiemannHypothesis`), or integer-norm fake edits carrying
   `β₀ + iγ₀` exist both with critical-line `L²` defect below every power lower bound and with
   least deleted prime exceeding `P`.
-/

noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate
open RHTower RHTower.HamburgerStability
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.FEDefect
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.WorldOne
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open GaloisForLFunctions.EulerFETransportTheory

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration

private theorem not_riemannHypothesis_of_zeroPt_eq_zero {β γ : ℝ} (hlo : 1 / 2 < β)
    (hhi : β < 1) (hζ : riemannZeta (zeroPt β γ) = 0) : ¬ RiemannHypothesis := by
  intro hRH
  have hre : (zeroPt β γ).re = β := by simp [zeroPt]
  have hne1 : zeroPt β γ ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hre; linarith
  have hntriv : ¬ ∃ n : ℕ, zeroPt β γ = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hneg : (zeroPt β γ).re = -2 * ((n : ℝ) + 1) := by
      rw [hn]; simp
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hhalf := hRH (zeroPt β γ) hζ hntriv hne1
  linarith

/-- **Unconditional `(1/2, 27001 / 48000)` sub-square-root single-pair dichotomy.**
For every `β ∈ (1/2, 27001 / 48000)` and `γ ∈ ℝ`, either `ζ(β + iγ) = 0` (refuting
`RiemannHypothesis` outright), or a `{0, 1, 2}`-prime edit `sEdit α β γ k₀` realizes `β ± iγ` at
an integer norm-count exponent `c < 1/2` with holomorphic continuation below `Re s = 1/2`. -/
theorem unconditional_subSqrt_singlePair_dichotomy {β γ : ℝ} (hlo : 1 / 2 < β)
    (hhi : β < 27001 / 48000) :
    (riemannZeta (zeroPt β γ) = 0 ∧ ¬ RiemannHypothesis) ∨
      ∃ (α : ℝ) (k₀ : ℕ) (c σ₁ : ℝ),
        c < 1 / 2 ∧ σ₁ < 1 / 2 ∧
        IsIntegerNormFakeAt (editSystem (sEdit α β γ k₀)) c ∧
        (∀ s : ℂ, 1 < s.re →
          editG α β γ k₀ s = (s - 1) * (editSystem (sEdit α β γ k₀)).zetaSeriesC s) ∧
        DifferentiableOn ℂ (editG α β γ k₀) {s : ℂ | σ₁ < s.re} ∧
        (∀ s : ℂ, σ₁ < s.re → (editG α β γ k₀ s = 0 ↔
          zetaResidueUnit s = 0 ∨ s = zeroPt β γ ∨ s = conj (zeroPt β γ))) := by
  by_cases hζ : riemannZeta (zeroPt β γ) = 0
  · exact Or.inl ⟨hζ, not_riemannHypothesis_of_zeroPt_eq_zero hlo (by linarith) hζ⟩
  · right
    have hΘ : zetaZeroAbscissa ≤ 20999 / 24000 :=
      ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths
    have hΘβ : zetaZeroAbscissa + 2 * β < 2 := by linarith
    have hβ23 : β < 2 / 3 := by linarith
    obtain ⟨α, k₀, c, hc, hfake, hGeq, σ₁, hσ₁, hdiff, hzeros⟩ :=
      exists_isIntegerNormFakeAt_sEdit_lt_half hlo hβ23 hΘβ hζ
    exact ⟨α, k₀, c, σ₁, hc, hσ₁, hfake, hGeq, hdiff, hzeros⟩

/-- **Full `(1/2, 2/3)` single-pair realization under `RiemannHypothesis` and FE defect barrier.**
Under `RiemannHypothesis`, every `β ∈ (1/2, 2/3)` and `γ ≠ 0` is realized as the **unique**
right-half-plane (`Re s > 1/2`) conjugate zero pair of a `{0, 1, 2}`-prime Beurling edit with
sub-square-root integer norm count `c < 1/2` and holomorphic continuation below `Re s = 1/2`,
while every Hamburger strip defect of that system has a deleted prime `p₀` and is unbounded,
non-decaying, and not Abel-sublinear. -/
theorem rh_subSqrt_singlePair_realization_and_defect_barrier (hRH : RiemannHypothesis)
    {β γ : ℝ} (hlo : 1 / 2 < β) (hhi : β < 2 / 3) (hγ : γ ≠ 0) :
    ∃ (α : ℝ) (k₀ : ℕ) (c σ₁ : ℝ),
      c < 1 / 2 ∧ σ₁ < 1 / 2 ∧
      zeroPt β γ ≠ conj (zeroPt β γ) ∧
      IsIntegerNormFakeAt (editSystem (sEdit α β γ k₀)) c ∧
      (∀ s : ℂ, 1 < s.re →
        editG α β γ k₀ s = (s - 1) * (editSystem (sEdit α β γ k₀)).zetaSeriesC s) ∧
      DifferentiableOn ℂ (editG α β γ k₀) {s : ℂ | σ₁ < s.re} ∧
      (∀ s : ℂ, 1 / 2 < s.re → (editG α β γ k₀ s = 0 ↔
        s = zeroPt β γ ∨ s = conj (zeroPt β γ))) ∧
      (∀ (β_h : ℂ) (g : ℝ → ℂ),
        HamburgerStripDefect (editSystem (sEdit α β γ k₀)).zetaSeriesC β_h g →
        ∃ p₀ : ℕ, p₀.Prime ∧ sEdit α β γ k₀ p₀ = -1 ∧
          ¬ Tendsto (fun δ => δ * abelMass g δ) (𝓝[>] 0) (𝓝 0) ∧
          (∀ M : ℝ, ¬ ∀ t : ℝ, ‖g t‖ ≤ M)) := by
  have hΘ_eq : zetaZeroAbscissa = 1 / 2 := by
    have hw : SquareRootThreshold.zetaZeroWidth = 0 :=
      SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp hRH
    have hrel := SquareRootThreshold.zetaZeroWidth_eq_zetaZeroAbscissa_sub_half
    linarith
  have hΘβ : zetaZeroAbscissa + 2 * β < 2 := by linarith
  have hζ_ne : riemannZeta (zeroPt β γ) ≠ 0 :=
    fun hζ => not_riemannHypothesis_of_zeroPt_eq_zero hlo (by linarith) hζ hRH
  obtain ⟨α, k₀, c, hc, hfake, hGeq, σ₁, hσ₁, hdiff, hzeros⟩ :=
    exists_isIntegerNormFakeAt_sEdit_lt_half hlo hhi hΘβ hζ_ne
  have hpair_ne : zeroPt β γ ≠ conj (zeroPt β γ) := by
    intro h
    have him := congrArg Complex.im h
    simp [zeroPt] at him
    exact hγ (by linarith)
  have hunit_ne : ∀ s : ℂ, 1 / 2 < s.re → zetaResidueUnit s ≠ 0 := by
    intro s hs
    by_cases hs1 : s = 1
    · rw [hs1, zetaResidueUnit_one]; exact one_ne_zero
    · rw [zetaResidueUnit, Function.update_of_ne hs1]
      refine mul_ne_zero (sub_ne_zero.mpr hs1) fun hζs => ?_
      have hle := re_le_zetaZeroAbscissa hζs
      linarith
  refine ⟨α, k₀, c, σ₁, hc, hσ₁, hpair_ne, hfake, hGeq, hdiff, fun s hs => ?_, ?_⟩
  · rw [hzeros s (lt_trans hσ₁ hs)]
    exact or_iff_right (hunit_ne s hs)
  · intro β_h g hH
    obtain ⟨A, C, _, hcnt⟩ := hfake.2.2.2.1
    obtain ⟨p₀, hp₀, hep₀, habel, -, -, hunb, -⟩ :=
      worldOne_row_one (by linarith : c < 1) hfake hcnt hH
    exact ⟨p₀, hp₀, hep₀, habel, hunb⟩

/-- **Unconditional `(1/2, 15001 / 24000)` subpolynomial-defect and prime-cutoff dichotomy.**
For every `β₀ ∈ (1/2, 15001 / 24000)` (`= (1/2, 5/8 + 1/24000)`), `γ₀ ∈ ℝ`, `β_c ∈ (β₀, 1)`, and
`P ∈ ℕ`, either `ζ(β₀ + iγ₀) = 0` (`¬ RiemannHypothesis`), or integer-norm fake edits carrying
`β₀ + iγ₀` exist both with critical-line `L²` defect violating every power lower bound and with
least deleted prime exceeding `P`. -/
theorem unconditional_subpolynomialDefect_dichotomy_below_five_eighths
    {β₀ γ₀ β_c : ℝ} (hlo : 1 / 2 < β₀) (hhi : β₀ < 15001 / 24000)
    (hβc : β₀ < β_c) (hβc1 : β_c < 1) (P : ℕ) :
    (riemannZeta (zeroPt β₀ γ₀) = 0 ∧ ¬ RiemannHypothesis) ∨
      ((∃ e : ℕ → ℤ, ∃ G : ℂ → ℂ, IsIntegerNormFakeAt (editSystem e) β_c ∧
          HamburgerStripDefect (editSystem e).zetaSeriesC (G 1 / 2) (stripDefect G) ∧
          ∀ α c : ℝ, 0 < α → 0 < c → ∀ T₀ : ℝ, ∃ T, T₀ ≤ T ∧
            (2 * T)⁻¹ * ∫ t in (-T)..T, ‖stripDefect G t‖ ^ 2 < c * T ^ (2 * α)) ∧
        (∃ e : ℕ → ℤ, IsSubpolynomialDefectFake e (zeroPt β₀ γ₀) β_c ∧
          ∃ p₀ : ℕ, p₀.Prime ∧ e p₀ = -1 ∧ P < p₀ ∧
            ∀ q : ℕ, q.Prime → e q = -1 → p₀ ≤ q)) := by
  by_cases hζ : riemannZeta (zeroPt β₀ γ₀) = 0
  · exact Or.inl ⟨hζ, not_riemannHypothesis_of_zeroPt_eq_zero hlo (by linarith) hζ⟩
  · right
    have hΘ : zetaZeroAbscissa ≤ 20999 / 24000 :=
      ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths
    have hβ₀Θ : β₀ < 3 / 2 - zetaZeroAbscissa := by linarith
    exact ⟨worldOne_row_two hlo hβ₀Θ hζ hβc hβc1,
      worldOne_row_three hlo hβ₀Θ hζ hβc hβc1 P⟩

#print axioms unconditional_subSqrt_singlePair_dichotomy
#print axioms rh_subSqrt_singlePair_realization_and_defect_barrier
#print axioms unconditional_subpolynomialDefect_dichotomy_below_five_eighths

end GaloisForLFunctions.WorldsOfTheZeroConfiguration
