import GaloisForLFunctions.RHTower.PaperThetaCutDivisor
import GaloisForLFunctions.RHTower.DeningerMeyerHedenmalmSourceRealization

/-! # Literal Meyer sources in the compact theta current

Every finite Hedenmalm causal source gives the exact factorization of the
movable interior charge. At the full multiplicity, its first surviving jet
is both a literal Meyer Mellin value and an explicit theta-source moment.
The weak-current identity therefore retains the original arithmetic source
through the singular quantile coordinate, including repeated zeros.
-/

noncomputable section
open MeasureTheory Set Complex
open scoped SchwartzMap

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

/-- All causal slots through the full multiplicity factor the actual interior charge. -/
theorem cutCharge_meyer_factorization (rho : XiDivisorSupport)
    (k : Fin (xiSupportMultiplicity rho + 1)) (z : ℂ) (a : ℝ) :
    cutCharge z a =
      (-(I*z)*Complex.exp (-(I*z)*(a : ℂ)) / (thetaSource.k a : ℂ)) *
        (z - xiSpectralPointSupport rho) ^ k.val *
          deningerMeyerCenteredMellin (deningerMeyerHedenmalmSource rho k) z := by
  rw [cutCharge_eq, deningerMeyerHedenmalmSource_transform,
    xiThetaDividedChain_partial_factorization rho (Nat.le_of_lt_succ k.isLt) z]
  ring

/-- The first surviving current jet is the full theta-source moment, with its cut gauge. -/
theorem iteratedDeriv_cutCharge_at_supportMultiplicity (rho : XiDivisorSupport) (a : ℝ) :
    iteratedDeriv (xiSupportMultiplicity rho) (fun z => cutCharge z a)
        (xiSpectralPointSupport rho) =
      (-(I * xiSpectralPointSupport rho) *
        Complex.exp (-(I * xiSpectralPointSupport rho)*(a : ℂ)) /
          (thetaSource.k a : ℂ)) *
        ∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand
          (xiSupportMultiplicity rho) (xiSpectralPointSupport rho) x := by
  let g : ℂ → ℂ := fun z =>
    -(I*z)*Complex.exp (-(I*z)*(a : ℂ)) / (thetaSource.k a : ℂ)
  have he : (fun z => cutCharge z a) = g * XiC := by
    funext z
    rw [cutCharge_eq]
    dsimp [g]
    ring
  rw [he, iteratedDeriv_mul
    (by dsimp [g]; fun_prop)
    ((XiC_differentiable.analyticAt _).contDiffAt.of_le le_top)]
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero,
      one_mul, Nat.sub_zero]
    rw [iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet
      (xiSupportMultiplicity rho)
      (xiSpectralPointSupport_mem_thetaCuspFourierLaplaceStrip rho)]
  · intro i _ hi
    rw [iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho
      (Nat.sub_lt (xiSupportMultiplicity_pos rho) (Nat.pos_of_ne_zero hi))]
    ring
  · simp

/-- No lower current jet survives, and the multiplicity-order jet never vanishes. -/
theorem cutCharge_full_multiplicity_jets (rho : XiDivisorSupport) (a : ℝ) :
    (∀ j < xiSupportMultiplicity rho,
      iteratedDeriv j (fun z => cutCharge z a) (xiSpectralPointSupport rho) = 0) ∧
    iteratedDeriv (xiSupportMultiplicity rho) (fun z => cutCharge z a)
      (xiSpectralPointSupport rho) ≠ 0 := by
  exact (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    ((differentiable_cutCharge a).analyticAt _)).mp
      (analyticOrderAt_cutCharge_support rho a)

/-- The terminal current jet is a value of an actual all-weight Meyer source. -/
theorem cutCharge_terminal_meyer_source (rho : XiDivisorSupport) (a : ℝ) :
    iteratedDeriv (xiSupportMultiplicity rho) (fun z => cutCharge z a)
        (xiSpectralPointSupport rho) =
      (-(I * xiSpectralPointSupport rho) *
        Complex.exp (-(I * xiSpectralPointSupport rho)*(a : ℂ)) /
          (thetaSource.k a : ℂ)) * (xiSupportMultiplicity rho).factorial *
        deningerMeyerCenteredMellin
          (deningerMeyerHedenmalmSource rho ⟨xiSupportMultiplicity rho, Nat.lt_succ_self _⟩)
          (xiSpectralPointSupport rho) := by
  rw [iteratedDeriv_cutCharge_at_supportMultiplicity,
    deningerMeyerHedenmalmSource_transform,
    xiThetaDividedChain_self_eq_integral_thetaCuspFourierLaplaceJet_div_factorial
      (xiSpectralPointSupport_mem_thetaCuspFourierLaplaceStrip rho)]
  have hf : ((xiSupportMultiplicity rho).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (xiSupportMultiplicity rho)
  field_simp

/-- The compact native current carries every literal Meyer causal source factorization. -/
theorem cutQuantileMode_meyer_source_current (rho : XiDivisorSupport)
    (k : Fin (xiSupportMultiplicity rho + 1)) (z : ℂ)
    (c : Ioo (0 : ℝ) 1) (φ : 𝓢(ℝ, ℂ)) :
    (∫ t in (0 : ℝ)..1, cutQuantileMode z c t * deriv φ t) =
      φ 0 - φ 1 - (∫ t in (0 : ℝ)..1, cutSourceDensity z c t * φ t) -
        ((-(I*z)*Complex.exp (-(I*z)*(thetaSource.quantileFun c.val : ℂ)) /
            (thetaSource.k (thetaSource.quantileFun c.val) : ℂ)) *
          (z - xiSpectralPointSupport rho) ^ k.val *
            deningerMeyerCenteredMellin (deningerMeyerHedenmalmSource rho k) z) *
          φ c.val := by
  rw [cutQuantileMode_source_current, cutCharge_meyer_factorization rho k]

end RHTower.PaperThetaEndpoint
