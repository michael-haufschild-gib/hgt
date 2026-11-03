import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRowsOfANearPairSum
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheNearAtomsHaveALogarithmicPairing
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanFinitePartIsMinusLogTwoPi

/-!
# The archimedean kernel of near atoms

Two atoms of width `w` at log-distance `wℓ`, `0 ≤ ℓ ≤ 2`, pair through

`Arch(n, j)/(w∫φ²) = (log(1/w) G(ℓ) + K_near(ℓ))/∫φ² + O(w)`
(`abs_atomArchPair_sub_nearKernel_le`),

`K_near(ℓ) = G(ℓ)(κ₀ − log(1 + ℓ)) + ∫_0^{1+ℓ} (2G(ℓ) − G(y − ℓ) − G(y + ℓ))/(2y) dy`,

where `G = φ ⋆ φ` and `κ₀ = 2θ′(0) + c_∞ = −log 2π − γ` (`nearConstant_eq`). The expansion is the
mixed Robin expansion on the common window `w(1 + ℓ)`; the shape term scales with the width and
polarizes into the second difference of `G`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped Real

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis
open _root_.RHTower (gammaHardyPhaseRate)

/-- The archimedean constant of the near pairing, `κ₀ = 2θ′(0) + c_∞`. -/
def nearConstant : ℝ := 2 * gammaHardyPhaseRate 0 + archRobinConstant

/-- `κ₀ = −log 2π − γ`. -/
theorem nearConstant_eq : nearConstant = -Real.log (2 * π) - Real.eulerMascheroniConstant := by
  have h := finitePart_profileRobin_eq (fun _ : ℝ => (0 : ℝ))
  simp only [profileRobin] at h
  rw [nearConstant]
  linarith

/-- The pair shape: `∫_0^{1+ℓ} (2G(ℓ) − G(y − ℓ) − G(y + ℓ))/(2y) dy`. -/
def nearShape (φ : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  ∫ y in Ioc 0 (1 + ℓ),
    (2 * shellAutocorr φ ℓ - shellAutocorr φ (y - ℓ) - shellAutocorr φ (y + ℓ)) / (2 * y)

/-- The near archimedean kernel `K_near(ℓ) = G(ℓ)(κ₀ − log(1 + ℓ)) + shape(ℓ)`. -/
def nearKernel (φ : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  shellAutocorr φ ℓ * (nearConstant - Real.log (1 + ℓ)) + nearShape φ ℓ

/-! ### The shape term in closed form -/

/-- The product of two shifted increments integrates to the second difference of `G`. -/
theorem integral_increment_mul_increment {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (ℓ y : ℝ) :
    ∫ u, (φ u - φ (u + y)) * (φ (u - ℓ) - φ (u - ℓ + y)) =
      2 * shellAutocorr φ ℓ - shellAutocorr φ (y - ℓ) - shellAutocorr φ (y + ℓ) := by
  have hint : ∀ a b : ℝ, Integrable fun u => φ (u + a) * φ (u + b) := fun a b =>
    ((hφ.comp (continuous_id.add continuous_const)).mul
      (hφ.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      ((hφc.comp_homeomorph (Homeomorph.addRight a)).mul_right)
  have hshift : ∀ a b : ℝ, ∫ u, φ (u + a) * φ (u + b) = shellAutocorr φ (b - a) := fun a b => by
    simp only [shellAutocorr, RHTower.ArchimedeanAnomaly.autocorr]
    rw [← integral_add_right_eq_self (fun u => φ u * φ (u + (b - a))) a]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring_nf)
  have e : (fun u => (φ u - φ (u + y)) * (φ (u - ℓ) - φ (u - ℓ + y))) = fun u =>
      φ (u + 0) * φ (u + -ℓ) - φ (u + 0) * φ (u + (y - ℓ)) - φ (u + y) * φ (u + -ℓ) +
        φ (u + y) * φ (u + (y - ℓ)) := by
    funext u; simp only [add_zero, ← sub_eq_add_neg]; ring_nf
  rw [e, integral_add ((hint 0 (-ℓ)).sub (hint 0 (y - ℓ)) |>.sub (hint y (-ℓ))) (hint y (y - ℓ)),
    integral_sub ((hint 0 (-ℓ)).sub (hint 0 (y - ℓ))) (hint y (-ℓ)),
    integral_sub (hint 0 (-ℓ)) (hint 0 (y - ℓ)), hshift, hshift, hshift, hshift]
  have h1 : shellAutocorr φ (-ℓ - 0) = shellAutocorr φ ℓ := by rw [sub_zero, shellAutocorr_neg]
  have h2 : shellAutocorr φ (-ℓ - y) = shellAutocorr φ (y + ℓ) := by
    rw [show -ℓ - y = -(y + ℓ) by ring, shellAutocorr_neg]
  have h3 : shellAutocorr φ (y - ℓ - y) = shellAutocorr φ ℓ := by
    rw [show y - ℓ - y = -ℓ by ring, shellAutocorr_neg]
  rw [h1, h2, h3, sub_zero]
  ring

/-- **Polarization of the shape term.** -/
theorem mixedBumpRobin_eq_integral {f d : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hd : Continuous d) (hdc : HasCompactSupport d) {W : ℝ}
    (hp : IntegrableOn (fun y => (∫ u, ((f u + d u) - (f (u + y) + d (u + y))) ^ 2) / (2 * y))
      (Ioc 0 W))
    (hm : IntegrableOn (fun y => (∫ u, ((-f u + d u) - (-f (u + y) + d (u + y))) ^ 2) / (2 * y))
      (Ioc 0 W)) :
    mixedBumpRobin f d W =
      ∫ y in Ioc 0 W, (∫ u, (f u - f (u + y)) * (d u - d (u + y))) / (2 * y) := by
  rw [mixedBumpRobin, bumpRobin, bumpRobin, ← integral_sub hp hm, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
  have hsq : ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      Integrable fun u => (g u - g (u + y)) ^ 2 := fun g hg hgc =>
    ((hg.sub (hg.comp (continuous_id.add continuous_const))).pow 2).integrable_of_hasCompactSupport
      ((hgc.sub (hgc.comp_homeomorph (Homeomorph.addRight y))).comp_left (by norm_num))
  have hP := hsq (fun u => f u + d u) (hf.add hd) (hfc.add hdc)
  have hM := hsq (fun u => -f u + d u) (hf.neg.add hd) (hfc.neg.add hdc)
  simp only at hP hM
  rw [← sub_div, ← integral_sub hP hM, div_div, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
