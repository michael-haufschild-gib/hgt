import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEClockLogarithmicMonodromyTransduction
import GaloisForLFunctions.HTGeometry.TanhSubstitution
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPlebanskiAngularPolarizationNoGo

/-!
# Every Xi radial carrier activates a polarized Plebanski source

The local angular no-go leaves a possible loophole: perhaps the actual Xi radial monodromy mode
vanishes on the physical positive-real BM radius, making the traceless-horizon channel vacuous.
This module closes that loophole.

The punctured complex Frobenius limit is pulled back along the real embedding.  Since its limit is
the nonzero Xi monodromy jump, every Xi fibre has a point `z` in the physical interval `(0,1)` at
which the exact radial mode is nonzero.  The corpus theorem
`tanh '' (0,infinity) = (0,1)` then writes `z=tanh(xi)^(2 : ℕ)` with `xi>0`.

Scaling the unit traceless horizon Hessian by that actual mode and applying the complete BM
inverse-Hessian transport gives the exact source

`-sech(xi)^(2 : ℕ) * mode(tanh(xi)^(2 : ℕ))^(2 : ℕ) / 16`.

It is nonzero on the selected rapidity, for every Xi copy and every AdS curvature coefficient.
Thus the remaining angular problem is genuine: a completed Maass-raised/spin-two Eisenstein
projection must be constructed before the negative leg can be attached.  It cannot be bypassed by
radial darkness or by the scalar completed triple-Eisenstein vertex alone.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [ACTUAL XI POLARIZED SOURCE]`
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The positive real ray approaches zero inside the punctured complex plane. -/
private theorem tendsto_ofReal_nhdsGT_zero_nhdsNE_zero :
    Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [mem_compl_iff, mem_singleton_iff]
  exact_mod_cast ne_of_gt hx

/-- The exact Xi monodromy carrier is nonzero somewhere on the physical BM interval `(0,1)`. -/
theorem exists_d4BMXiMixedHorizonExactMonodromyMode_ne_zero_real_unitInterval
    (n k : ℕ) (q : XiZeroCopy) :
    ∃ z : ℝ, 0 < z ∧ z < 1 ∧
      d4BMXiMixedHorizonExactMonodromyMode n k q (z : ℂ) ≠ 0 := by
  have hratio :
      ∀ᶠ z : ℂ in 𝓝[≠] 0,
        d4BMXiMixedHorizonExactMonodromyMode n k q z /
            z ^ (d4BMMixedHorizonFrobeniusOrder n k + 1) ≠ 0 :=
    (tendsto_d4BMXiMixedHorizonExactMonodromyMode_div_pow_zero n k q).eventually_ne
      (d4BMXiMixedHorizonComplexMonodromyJump_ne_zero n k q)
  have hratioReal :
      ∀ᶠ z : ℝ in 𝓝[>] 0,
        d4BMXiMixedHorizonExactMonodromyMode n k q (z : ℂ) /
            (z : ℂ) ^ (d4BMMixedHorizonFrobeniusOrder n k + 1) ≠ 0 :=
    tendsto_ofReal_nhdsGT_zero_nhdsNE_zero.eventually hratio
  have hlt : ∀ᶠ z : ℝ in 𝓝[>] 0, z < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ z : ℝ in 𝓝[>] 0, 0 < z := self_mem_nhdsWithin
  rcases (hpos.and (hlt.and hratioReal)).exists with ⟨z, hz0, hz1, hratioz⟩
  refine ⟨z, hz0, hz1, ?_⟩
  intro hzero
  apply hratioz
  rw [hzero]
  simp

/-- Every Xi monodromy carrier is nonzero at some positive physical rapidity. -/
theorem exists_d4BMXiMixedHorizonExactMonodromyMode_ne_zero_positiveRapidity
    (n k : ℕ) (q : XiZeroCopy) :
    ∃ xi : ℝ, 0 < xi ∧
      d4BMXiMixedHorizonExactMonodromyMode n k q
          ((Real.tanh xi ^ (2 : ℕ) : ℝ) : ℂ) ≠ 0 := by
  rcases exists_d4BMXiMixedHorizonExactMonodromyMode_ne_zero_real_unitInterval n k q with
    ⟨z, hz0, hz1, hmode⟩
  have hsqrt : Real.sqrt z ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hz0
    · exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2 (by simpa using hz1)
  have himage : Real.sqrt z ∈ Real.tanh '' Set.Ioi (0 : ℝ) := by
    rw [HTGeometry.tanh_image_Ioi_zero]
    exact hsqrt
  rcases himage with ⟨xi, hxi, htanh⟩
  refine ⟨xi, hxi, ?_⟩
  rw [htanh, Real.sq_sqrt (le_of_lt hz0)]
  exact hmode

/-- Traceless angular Hessian scaled by a physical radial amplitude. -/
def d4BMScaledTracelessHorizonHessianSecondJet (amplitude : ℂ) :
    D4BMFullSecondJet :=
  { first := { value := 0, tau := 0, horizonX := 0, sigma := 0, xi := 0 }
    tauTau := 0
    tauHorizonX := 0
    tauSigma := 0
    tauXi := 0
    horizonXHorizonX := -amplitude
    horizonXSigma := 0
    horizonXXi := 0
    sigmaSigma := amplitude
    sigmaXi := 0
    xiXi := 0 }

/-- Exact source coefficient for an arbitrary scaled traceless angular Hessian at positive
rapidity.  The curvature term drops because the complete first jet vanishes. -/
theorem ads4PlebanskiJacobiDoubleBracket_scaledTracelessHorizonWitness_eq
    (inverseUV amplitude : ℂ) (xi : {x : ℝ // 0 < x}) :
    ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets
        inverseUV
        ((Real.tanh (xi : ℝ) : ℂ)⁻¹)
        ((d4BMRindlerRapiditySech (xi : ℝ) : ℂ)⁻¹)
        0 (xi : ℝ) 1
        (d4BMScaledTracelessHorizonHessianSecondJet amplitude)
        (d4BMScaledTracelessHorizonHessianSecondJet amplitude) =
      -(d4BMRindlerRapiditySech (xi : ℝ) : ℂ) ^ (2 : ℕ) * amplitude ^ (2 : ℕ) / 16 := by
  have haR : Real.tanh (xi : ℝ) ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero (Real.sinh_ne_zero.mpr (ne_of_gt xi.property))
      (ne_of_gt (Real.cosh_pos xi))
  have ha : (Real.tanh (xi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast haR
  have hbR : d4BMRindlerRapiditySech (xi : ℝ) ≠ 0 := by
    exact inv_ne_zero (ne_of_gt (Real.cosh_pos xi))
  have hb : (d4BMRindlerRapiditySech (xi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hbR
  have haComplex : Complex.tanh ((xi : ℝ) : ℂ) ≠ 0 := by
    simpa using ha
  have haCancel :
      (Complex.tanh ((xi : ℝ) : ℂ))⁻¹ * Complex.tanh ((xi : ℝ) : ℂ) ^ (2 : ℕ) =
        Complex.tanh ((xi : ℝ) : ℂ) := by
    field_simp [haComplex]
  have hbCancel :
      (d4BMRindlerRapiditySech (xi : ℝ) : ℂ)⁻¹ *
          (d4BMRindlerRapiditySech (xi : ℝ) : ℂ) ^ (2 : ℕ) =
        (d4BMRindlerRapiditySech (xi : ℝ) : ℂ) := by
    field_simp [hb]
  simp [ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets,
    d4PlebanskiLightConeTwoJetOfBMFormalInv,
    d4PoincareLightConeUVectorFieldFirstJetOnBMFormalInv,
    d4PoincareLightConeWVectorFieldFirstJetOnBMFormalInv,
    d4BMVectorFieldFirstJetLinearCombination,
    d4BMFullFirstJetLinearCombination,
    d4BMDirectionalDerivativeOnFullFirstJet,
    d4BMOrderedSecondDirectionalDerivative,
    d4PoincareTimeVectorFieldFirstJetOnBMFormalInv,
    d4PoincareHorizonYVectorFieldFirstJetOnBMFormalInv,
    d4PoincareRadialVectorFieldFirstJetOnBMFormalInv,
    d4PoincareHorizonXVectorFieldFirstJetOnBM,
    d4BMScaledTracelessHorizonHessianSecondJet,
    ads4PlebanskiJacobiDoubleBracketOnTwoJets]
  rw [haCancel, hbCancel]
  ring

/-- On every actual Xi fibre, the missing spin-two angular polarization produces a nonzero local
Plebanski source at some positive real rapidity. -/
theorem exists_d4BMXiPulledPlebanskiTracelessHorizonSource_ne_zero
    (n k : ℕ) (q : XiZeroCopy) (inverseUV : ℂ) :
    ∃ xi : {x : ℝ // 0 < x},
      ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets
          inverseUV
          ((Real.tanh (xi : ℝ) : ℂ)⁻¹)
          ((d4BMRindlerRapiditySech (xi : ℝ) : ℂ)⁻¹)
          0 (xi : ℝ) 1
          (d4BMScaledTracelessHorizonHessianSecondJet
            (d4BMXiMixedHorizonExactMonodromyMode n k q
              ((Real.tanh (xi : ℝ) ^ (2 : ℕ) : ℝ) : ℂ)))
          (d4BMScaledTracelessHorizonHessianSecondJet
            (d4BMXiMixedHorizonExactMonodromyMode n k q
              ((Real.tanh (xi : ℝ) ^ (2 : ℕ) : ℝ) : ℂ))) ≠ 0 := by
  rcases exists_d4BMXiMixedHorizonExactMonodromyMode_ne_zero_positiveRapidity n k q with
    ⟨xi, hxi, hmode⟩
  let xiPos : {x : ℝ // 0 < x} := ⟨xi, hxi⟩
  refine ⟨xiPos, ?_⟩
  rw [ads4PlebanskiJacobiDoubleBracket_scaledTracelessHorizonWitness_eq]
  have hbR : d4BMRindlerRapiditySech xi ≠ 0 := by
    exact inv_ne_zero (ne_of_gt (Real.cosh_pos xi))
  have hb : (d4BMRindlerRapiditySech xi : ℂ) ≠ 0 := by
    exact_mod_cast hbR
  exact div_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hb)) (pow_ne_zero 2 hmode))
    (by norm_num)

end

end RHTower
