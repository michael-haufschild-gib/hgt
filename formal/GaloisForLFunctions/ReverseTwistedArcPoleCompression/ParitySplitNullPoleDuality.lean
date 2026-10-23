import GaloisForLFunctions.ReverseTwistedArcPoleCompression.TwistedArcShiftedGammaPoleProjection
import GaloisForLFunctions.RHTower.WeilPoleDepthRigidity
import GaloisForLFunctions.RHTower.WeilPoleWeightSummableDeviationRigidity

/-!
# Parity-Split Null Duality and Three-Way Decomposition of the `2 × 2` Pole Space

This module formalizes the second leg of **Mechanism 4 (Reverse Twisted-Arc Duality on the
`2 × 2` Pole-Compression Matrix)**:

1. **Exact Parity Decomposition of the Bilinear Pole Form (`pole_of_decayBound_eq_two_mul_cosh_sq_sub_sinh_sq`):**
   For any test `F` satisfying `DecayBound F δ C` (`0 < δ`), the bilinear pole pairing splits into
   the difference of squares of its even (`cosh(u/2)`) and odd (`sinh(u/2)`) pole projections:
   `2 (∫ F e^{-u/2}) (∫ F e^{u/2}) = 2 ((∫ F cosh(u/2))^2 - (∫ F sinh(u/2))^2)`.
   Thus even-pole tests produce positive pole pairings (`+2 (∫ F cosh(u/2))^2 ≥ 0`, locking `β ≥ 1`),
   whereas odd-pole tests produce negative pole pairings (`-2 (∫ F sinh(u/2))^2 ≤ 0`, locking `β ≤ 1`).
2. **Pure Odd-Pole Projection of `oddNullTest = F₁ - (1/4) F₀`:**
   The odd-type null test `oddNullTest` has `∫ oddNullTest(u) cosh(u/2) du = 0` and
   `∫ oddNullTest(u) sinh(u/2) du = 1/8`, with strictly negative pole pairing
   `-2 * (1/8)^2 = -1/32 < 0`.
3. **Polar-Orthogonal Projection of `depthNullTest (1/2)`:**
   At the true pole depth `c = 1/2`, `depthNullTest (1/2)` (whose Fourier transform is
   `Ξ(z)(z^2 + 1/4) = -4 Ξ Q₂ + 6 Ξ Q₁`) is orthogonal to both `cosh(u/2)` and `sinh(u/2)`
   (`∫ depthNullTest(1/2) e^{±u/2} = 0`, `∫ depthNullTest(1/2) cosh(u/2) = 0`,
   `∫ depthNullTest(1/2) sinh(u/2) = 0`), lying inside the polar-constrained kernel of the
   `2 × 2` pole space.
4. **Three-Way `Ξ`-Divisible Pole Basis & Two-Sided Pole Rigidity (`xiDivisible_two_by_two_pole_channel_decomposition`):**
   Combines the three orthogonal channels (`xiShiftedGammaTest 0`, `oddNullTest`,
   `depthNullTest (1/2)`) with the unconditional rigidity of the pole depth `c^2 = 1/4` and
   residue weight `β = 1`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Nat
open Zeta23 RHTower RHTower.WeilSpectral RHTower.WeilPoleWeight

noncomputable section

namespace GaloisForLFunctions.ReverseTwistedArcPoleCompression

/-! ### Exact parity decomposition of the bilinear pole pairing -/

/-- A `DecayBound` test is integrable against both pole weights `e^{±u/2}`. -/
private theorem integrable_mul_exp_half_of_decayBound {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ)
    (hF : DecayBound F δ C) :
    (Integrable fun u => F u * Real.exp (u / 2)) ∧
      Integrable fun u => F u * Real.exp (-u / 2) := by
  refine ⟨(integrable_mul_exp_of_decayBound hδ hF (c := 1 / 2) (by norm_num)).congr
      (Filter.Eventually.of_forall fun u => ?_),
    (integrable_mul_exp_of_decayBound hδ hF (c := -(1 / 2)) (by norm_num)).congr
      (Filter.Eventually.of_forall fun u => ?_)⟩
  · dsimp only
    rw [show (1 / 2 : ℝ) * u = u / 2 by ring]
  · dsimp only
    rw [show -(1 / 2 : ℝ) * u = -u / 2 by ring]

/-- **Even pole projection**: `∫ F cosh(u/2) = (∫ F e^{u/2} + ∫ F e^{-u/2}) / 2` for a
`DecayBound` test, by `cosh = (exp + exp ∘ neg)/2` and linearity of the convergent integrals. -/
theorem integral_mul_cosh_half_of_decayBound {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ)
    (hF : DecayBound F δ C) :
    ∫ u, F u * Real.cosh (u / 2) =
      ((∫ u, F u * Real.exp (u / 2)) + ∫ u, F u * Real.exp (-u / 2)) / 2 := by
  obtain ⟨h1, h2⟩ := integrable_mul_exp_half_of_decayBound hδ hF
  rw [← integral_add h1 h2, ← integral_div]
  congr 1
  ext u
  rw [Real.cosh_eq, show -(u / 2) = -u / 2 by ring]
  ring

/-- **Odd pole projection**: `∫ F sinh(u/2) = (∫ F e^{u/2} - ∫ F e^{-u/2}) / 2` for a
`DecayBound` test. -/
theorem integral_mul_sinh_half_of_decayBound {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ)
    (hF : DecayBound F δ C) :
    ∫ u, F u * Real.sinh (u / 2) =
      ((∫ u, F u * Real.exp (u / 2)) - ∫ u, F u * Real.exp (-u / 2)) / 2 := by
  obtain ⟨h1, h2⟩ := integrable_mul_exp_half_of_decayBound hδ hF
  rw [← integral_sub h1 h2, ← integral_div]
  congr 1
  ext u
  rw [Real.sinh_eq, show -(u / 2) = -u / 2 by ring]
  ring

/-- **Parity-difference-of-squares law for the bilinear pole pairing:**
For any `DecayBound` test `F`, the bilinear pole pairing `2 (∫ F e^{-u/2}) (∫ F e^{u/2})` equals
`2 ((∫ F cosh(u/2))^2 - (∫ F sinh(u/2))^2)`. -/
theorem pole_of_decayBound_eq_two_mul_cosh_sq_sub_sinh_sq {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ)
    (hF : DecayBound F δ C) :
    2 * ((∫ u, F u * Real.exp (-u / 2)) * ∫ u, F u * Real.exp (u / 2)) =
      2 * ((∫ u, F u * Real.cosh (u / 2)) ^ 2 - (∫ u, F u * Real.sinh (u / 2)) ^ 2) := by
  rw [integral_mul_cosh_half_of_decayBound hδ hF, integral_mul_sinh_half_of_decayBound hδ hF]
  ring

/-! ### Pure odd-pole projection of `oddNullTest` -/

/-- The odd-type null test `oddNullTest = F₁ - (1/4) F₀` annihilates the **even** pole mode
`cosh(u/2)`. -/
theorem integral_oddNullTest_cosh_half :
    ∫ u, oddNullTest u * Real.cosh (u / 2) = 0 := by
  obtain ⟨C, hF⟩ := exists_decayBound_oddNullTest
  rw [integral_mul_cosh_half_of_decayBound (by norm_num : (0 : ℝ) < 1 / 4) hF,
    integral_oddNullTest_mul_exp_half, integral_oddNullTest_mul_exp_neg_half]
  norm_num

/-- The odd-type null test `oddNullTest = F₁ - (1/4) F₀` has **odd** pole projection
`∫ oddNullTest(u) sinh(u/2) du = 1/8`. -/
theorem integral_oddNullTest_sinh_half :
    ∫ u, oddNullTest u * Real.sinh (u / 2) = 1 / 8 := by
  obtain ⟨C, hF⟩ := exists_decayBound_oddNullTest
  rw [integral_mul_sinh_half_of_decayBound (by norm_num : (0 : ℝ) < 1 / 4) hF,
    integral_oddNullTest_mul_exp_half, integral_oddNullTest_mul_exp_neg_half]
  norm_num

/-! ### Polar-orthogonal projection of `depthNullTest (1/2)` -/

/-- At the true pole depth `c = 1/2`, `depthNullTest (1/2)` has zero `e^{-u/2}` pole projection. -/
theorem integral_depthNullTest_half_exp_neg_half :
    ∫ u, depthNullTest (1 / 2) u * Real.exp (-u / 2) = 0 := by
  rw [integral_depthNullTest_mul_exp_neg_half]
  norm_num

/-- At the true pole depth `c = 1/2`, `depthNullTest (1/2)` has zero `e^{u/2}` pole projection. -/
theorem integral_depthNullTest_half_exp_half :
    ∫ u, depthNullTest (1 / 2) u * Real.exp (u / 2) = 0 := by
  rw [integral_depthNullTest_mul_exp_half]
  norm_num

/-- At the true pole depth `c = 1/2`, `depthNullTest (1/2)` has zero **even** pole projection
`∫ depthNullTest(1/2)(u) cosh(u/2) du = 0`. -/
theorem integral_depthNullTest_half_cosh_half :
    ∫ u, depthNullTest (1 / 2) u * Real.cosh (u / 2) = 0 := by
  obtain ⟨C, hF⟩ := exists_decayBound_depthNullTest (1 / 2)
  rw [integral_mul_cosh_half_of_decayBound (by norm_num : (0 : ℝ) < 1 / 4) hF,
    integral_depthNullTest_half_exp_half, integral_depthNullTest_half_exp_neg_half]
  norm_num

/-- At the true pole depth `c = 1/2`, `depthNullTest (1/2)` has zero **odd** pole projection
`∫ depthNullTest(1/2)(u) sinh(u/2) du = 0`. -/
theorem integral_depthNullTest_half_sinh_half :
    ∫ u, depthNullTest (1 / 2) u * Real.sinh (u / 2) = 0 := by
  obtain ⟨C, hF⟩ := exists_decayBound_depthNullTest (1 / 2)
  rw [integral_mul_sinh_half_of_decayBound (by norm_num : (0 : ℝ) < 1 / 4) hF,
    integral_depthNullTest_half_exp_half, integral_depthNullTest_half_exp_neg_half]
  norm_num

/-- At the true pole depth `c = 1/2`, `depthNullTest (1/2)` has zero bilinear pole pairing. -/
theorem pole_depthNullTest_half :
    2 * ((∫ u, depthNullTest (1 / 2) u * Real.exp (-u / 2)) *
      ∫ u, depthNullTest (1 / 2) u * Real.exp (u / 2)) = 0 := by
  rw [integral_depthNullTest_half_exp_neg_half, integral_depthNullTest_half_exp_half]
  norm_num

/-! ### Pure even-pole projection of `xiShiftedGammaTest 0` -/

/-- Both pole integrals of `xiShiftedGammaTest 0` are `ξ(0) = ξ(1) = 1/2`. -/
private theorem integral_xiShiftedGammaTest_zero_exp_halves :
    (∫ u, xiShiftedGammaTest 0 u * Real.exp (-u / 2)) = 1 / 2 ∧
      ∫ u, xiShiftedGammaTest 0 u * Real.exp (u / 2) = 1 / 2 := by
  have h1 := integral_xiShiftedGammaTest_mul_exp_neg_half 0
  have h2 := integral_xiShiftedGammaTest_mul_exp_half 0
  simp only [xiShiftedGamma, shiftedGammaPoly, Finset.range_zero, Finset.prod_empty, mul_one,
    RHTower.XiC] at h1 h2
  rw [show (1 / 2 : ℂ) + I / 2 * I = 0 by rw [mul_comm, ← mul_div_assoc, Complex.I_mul_I]; ring,
    xi_zero_eq_half] at h1
  rw [show (1 / 2 : ℂ) + -I / 2 * I = 1 by
    rw [mul_comm, ← mul_div_assoc, mul_neg, Complex.I_mul_I]; ring, xi_one] at h2
  exact ⟨by simpa using congrArg Complex.re h1, by simpa using congrArg Complex.re h2⟩

/-- `xiShiftedGammaTest 0` has even pole projection `∫ · cosh(u/2) = 1/2`. -/
theorem integral_xiShiftedGammaTest_zero_cosh_half :
    ∫ u, xiShiftedGammaTest 0 u * Real.cosh (u / 2) = 1 / 2 := by
  obtain ⟨C, -, hj⟩ := exists_decayBound_xiShiftedGammaTest
  rw [integral_mul_cosh_half_of_decayBound (by norm_num : (0 : ℝ) < 1 / 4) (hj 0),
    integral_xiShiftedGammaTest_zero_exp_halves.1, integral_xiShiftedGammaTest_zero_exp_halves.2]
  norm_num

/-- `xiShiftedGammaTest 0` has vanishing odd pole projection `∫ · sinh(u/2) = 0`. -/
theorem integral_xiShiftedGammaTest_zero_sinh_half :
    ∫ u, xiShiftedGammaTest 0 u * Real.sinh (u / 2) = 0 := by
  obtain ⟨C, -, hj⟩ := exists_decayBound_xiShiftedGammaTest
  rw [integral_mul_sinh_half_of_decayBound (by norm_num : (0 : ℝ) < 1 / 4) (hj 0),
    integral_xiShiftedGammaTest_zero_exp_halves.1, integral_xiShiftedGammaTest_zero_exp_halves.2]
  norm_num

/-! ### Three-way `Ξ`-divisible pole basis and two-sided pole rigidity -/

/-- **Three-Way `Ξ`-Divisible Decomposition of the `2 × 2` Pole Space and Two-Sided Pole Rigidity:**
The first three shifted-Gamma `Ξ`-divisible tests (`xiShiftedGammaTest 0`, `oddNullTest`,
`depthNullTest (1/2)`) diagonalize the `2 × 2` pole space `span(cosh(u/2), sinh(u/2))` into:
1. the pure **even** pole channel `xiShiftedGammaTest 0` (`∫ · cosh(u/2) = 1/2`,
   `∫ · sinh(u/2) = 0`, pole pairing `+1/2 > 0`),
2. the pure **odd** pole channel `oddNullTest` (`∫ · cosh(u/2) = 0`,
   `∫ · sinh(u/2) = 1/8`, pole pairing `-1/32 < 0`),
3. the **polar-orthogonal** channel `depthNullTest (1/2)` (`∫ · cosh(u/2) = 0`,
   `∫ · sinh(u/2) = 0`, pole pairing `0`),
while all three vanish at every nontrivial zero `ρ` of `ζ` (`paperFT · (gammaOf ρ) = 0`), and
together force unconditional rigidity of both the pole depth `c^2 = 1/4` and residue weight
`β = 1`. -/
theorem xiDivisible_two_by_two_pole_channel_decomposition :
    -- 1. Pure even-pole channel: xiShiftedGammaTest 0
    ((∫ u, xiShiftedGammaTest 0 u * Real.cosh (u / 2) = 1 / 2) ∧
     (∫ u, xiShiftedGammaTest 0 u * Real.sinh (u / 2) = 0) ∧
     (2 * ((∫ u, xiShiftedGammaTest 0 u * Real.exp (-u / 2)) *
       ∫ u, xiShiftedGammaTest 0 u * Real.exp (u / 2)) = 1 / 2) ∧
     (∀ ρ : zetaZeroConfig.carrier,
       paperFT (fun u => (xiShiftedGammaTest 0 u : ℂ)) (gammaOf ρ) = 0)) ∧
    -- 2. Pure odd-pole channel: oddNullTest = F₁ - (1/4) F₀
    ((∫ u, oddNullTest u * Real.cosh (u / 2) = 0) ∧
     (∫ u, oddNullTest u * Real.sinh (u / 2) = 1 / 8) ∧
     (2 * ((∫ u, oddNullTest u * Real.exp (-u / 2)) *
       ∫ u, oddNullTest u * Real.exp (u / 2)) = -1 / 32) ∧
     (∀ ρ : zetaZeroConfig.carrier,
       paperFT (fun u => (oddNullTest u : ℂ)) (gammaOf ρ) = 0)) ∧
    -- 3. Polar-orthogonal channel: depthNullTest (1/2)
    ((∫ u, depthNullTest (1 / 2) u * Real.cosh (u / 2) = 0) ∧
     (∫ u, depthNullTest (1 / 2) u * Real.sinh (u / 2) = 0) ∧
     (2 * ((∫ u, depthNullTest (1 / 2) u * Real.exp (-u / 2)) *
       ∫ u, depthNullTest (1 / 2) u * Real.exp (u / 2)) = 0) ∧
     (∀ ρ : zetaZeroConfig.carrier,
       paperFT (fun u => (depthNullTest (1 / 2) u : ℂ)) (gammaOf ρ) = 0)) ∧
    -- 4. Two-sided pole-depth and residue-weight rigidity
    (∀ β c : ℝ, |c| < 3 / 4 →
      (∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
        0 ≤ (weilPoleDepthFunctional β c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re) →
      c ^ 2 = 1 / 4 ∧ β = 1) :=
  ⟨⟨integral_xiShiftedGammaTest_zero_cosh_half,
    integral_xiShiftedGammaTest_zero_sinh_half,
    pole_xiShiftedGammaTest_zero,
    paperFT_xiShiftedGammaTest_gammaOf 0⟩,
   ⟨integral_oddNullTest_cosh_half,
    integral_oddNullTest_sinh_half,
    pole_oddNullTest,
    paperFT_oddNullTest_gammaOf⟩,
   ⟨integral_depthNullTest_half_cosh_half,
    integral_depthNullTest_half_sinh_half,
    pole_depthNullTest_half,
    paperFT_depthNullTest_gammaOf (1 / 2)⟩,
   fun _ _ hc hpos =>
    sq_eq_and_eq_one_of_forall_re_weilPoleDepthFunctional_vonMangoldt_nonneg hc hpos⟩

end GaloisForLFunctions.ReverseTwistedArcPoleCompression
