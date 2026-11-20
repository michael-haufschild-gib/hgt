import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheStepanovBoundSeparatesZetaFromTheOneOff
import GaloisForLFunctions.SignedArithmeticCorrespondences.ControlledDivisibilityPositivityAndTheMacroscopicBarrier
import GaloisForLFunctions.FloorFreeArithmetic.TheZeroConfigurationDoesNotSeeTheEulerProduct
import GaloisForLFunctions.BlackHoleRingdown.CausalIdentitiesCannotForceQuarterRingdown
import GaloisForLFunctions.SquareRootThreshold.TheZeroWidthIsAnUnboundedApertureProperty

/-!
# The twin test suite

A proof of RH must use something that `ζ` has and its twins lack. Each proposed producer target is
evaluated here on the twins that share the structure it uses. A mechanism whose hypotheses hold on
a twin on which the target fails cannot prove the target.

| Target | Twin | Shared with `ζ` | Value on the twin |
|---|---|---|---|
| Stepanov bound `θ(N) ≤ N + C√N log²N` | integer-norm one-off, zeros `3/5 ± i` | Euler product over integer norms, continuation to `Re s > ½` | violated for every `C` (`twin_stepanov_oneOff`) |
| Stepanov bound | real one-off, zero `3/5` | the same | satisfied (`twin_stepanov_realOneOff`) |
| comb positivity, odd-sector Schur complement | Liouville comb `λΛ` | contact sizes `log p`, comb geometry | below `−‖c‖²/2000` at macroscopic cost, every `K` (`twin_comb_liouville`) |
| exclusion of off-line zeros by configuration data | Euler-symmetric finite layers | explicit formula, reflection, conjugation, no real zeros, Euler divisor | a model at every depth below `½` (`twin_eulerSymmetric_floor`) |
| decay of the reflected field, quarter-rate ringdown | prime-2 Schur twin | functional equation, Euler product, Schur passivity, unitarity, pole dictionary | decay fails at every rate `δ > 0` (`twin_primeTwo_schur`) |
| Weil positivity on a fixed aperture | tempered off-line lattice | explicit formula, temperedness | positive at every width (`twin_fixedAperture`) |

The Stepanov bound is one-sided: it fails for the complex one-off and holds for the real one-off,
so it is blind to real zeros, and a proof of it must use the real place.
-/

noncomputable section

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

section Stepanov
open Real Filter

/-- **Stepanov bound on the integer-norm one-off: violated for every constant.** -/
theorem twin_stepanov_oneOff :
    ∃ q : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - Complex.exp (-(s * Real.log (q k))))⁻¹) (F s)) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} ∧
      {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} =
        {(3 / 5 : ℂ) + Complex.I, (3 / 5 : ℂ) - Complex.I} ∧
      ∀ C : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
        (n : ℝ) + C * Real.sqrt n * Real.log n ^ 2 <
          ∑' k, if q k ≤ n then Real.log (q k) else 0 :=
  ArithmeticLefschetzStepanovTheory.one_off_violates_stepanov_bound

/-- **Stepanov bound on the real one-off: satisfied.** -/
theorem twin_stepanov_realOneOff :
    ∃ q : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - Complex.exp (-(s * Real.log (q k))))⁻¹) (F s)) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} ∧
      {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} = {(3 / 5 : ℂ)} ∧
      ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
        (∑' k, if q k ≤ n then Real.log (q k) else 0) ≤
          (n : ℝ) + C * Real.sqrt n * Real.log n ^ 2 :=
  ArithmeticLefschetzStepanovTheory.real_one_off_satisfies_stepanov_bound

end Stepanov

section Comb
open Finset Filter
open GaloisForLFunctions.SignedArithmeticCorrespondences HodgeTheoryOfAFixedPart

/-- **Comb positivity on the Liouville comb: negative at macroscopic cost, at every width.** -/
theorem twin_comb_liouville {K : ℕ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∃ α : ℕ → ℝ,
        let S := Ioc N (N + 3 * K * N)
        let c := fun n => ∑ d ∈ Icc 2 ((1 + 3 * K) * N), α d * centeredMultiple d n
        0 < ∑ n ∈ S, c n ^ 2 ∧
        (∑ d ∈ Icc 2 ((1 + 3 * K) * N), |α d|) ^ 2 ≤ C * (N : ℝ) * ∑ n ∈ S, c n ^ 2 ∧
        combFormW SelectiveArithmetic.liouvilleWeight S c <
          -(1 / 2000) * ∑ n ∈ S, c n ^ 2 ∧
        diagRealBudget S c <
          mixedPrimeDebitW SelectiveArithmetic.liouvilleWeight S c :=
  eventually_exists_liouville_centeredMultiple_neg hK

end Comb

/-- **Configuration data on Euler-symmetric layers: no depth below `½` is excluded.** -/
theorem twin_eulerSymmetric_floor :
    FloorFreeArithmetic.floor FloorFreeArithmetic.EulerSymmetric = 1 / 2 :=
  FloorFreeArithmetic.floor_eulerSymmetric

section Aperture
open Set Zeta23

/-- **Weil positivity on one aperture: satisfied by tempered configurations of every width.** -/
theorem twin_fixedAperture {a : ℝ} (ha : 0 < a) :
    ¬ ∀ Z : ZeroConfig, SquareRootThreshold.TemperedConfig Z →
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re) →
        SquareRootThreshold.configWidth Z = 0 :=
  SquareRootThreshold.not_forall_configWidth_eq_zero_of_weil_nonneg_on_aperture ha

end Aperture

section Schur
open Complex _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

/-- **Causal decay on the prime-2 Schur twin: fails at every prescribed rate.** -/
theorem twin_primeTwo_schur {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 7 / 8 < α ∧ α < 1 ∧
      (∀ τ : ℝ, τ ≤ 0 → deformedEchoKernel α τ = 0) ∧
      (∀ w : ℂ, 1 / 2 < w.re →
        HasProd (fun p : Nat.Primes => deformedPrimeGate α p w)
          (primeTwoScatteringGate α w * (riemannZeta (2 * w) / riemannZeta (2 * w + 1)))) ∧
      (∀ w : ℂ, 0 ≤ w.re → ‖deformedReducedScattering α w‖ ≤ 1 ∧
        0 ≤ ((1 - deformedReducedScattering α w) / (1 + deformedReducedScattering α w)).re) ∧
      (∀ t : ℝ, ‖deformedScatteringPhase α ((t : ℂ) * I)‖ = 1) ∧
      (∀ ρ : ℂ, xi ρ = 0 →
        meromorphicOrderAt (deformedWightmanRL α) (I * (ρ - 1) / 2) < 0) ∧
      (∀ σ : ℝ, 0 < σ → σ < (1 - α) / 2 → ∀ h : CompactPulse, ∃ C : ℝ, 0 ≤ C ∧
        ∀ τ : ℝ, 0 ≤ τ → ‖deformedReflectedField α h τ‖ ≤ C * Real.exp (-σ * τ)) ∧
      (∃ h : CompactPulse, ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖deformedReflectedField α h τ‖ ≤ C * Real.exp (-δ * τ)) :=
  universal_causal_ringdown_infimum_zero hδ

end Schur

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
