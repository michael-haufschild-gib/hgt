import GaloisForLFunctions.RHTower.SourceGammaReflectionRadialGhostRigidity

/-!
# Finite physical half-density tensor powers cannot produce Gamma Ward selectivity

The exact radial survivor from the preceding source--Gamma classifications requires

`‖u₂‖ / ‖u₃‖ = (3/2)^(2*t)`.

The corpus already identifies the literal physical half-density character.  Its `n`-fold ordinary
tensor-power norm ratio is computed here exactly as

`(3/2)^(n*t/2)`, where `t = 2 Re(rho) - 1`.

Strict monotonicity gives a sharp dichotomy: compatibility with two-prime Gamma Ward is equivalent
to `n = 4` or `t = 0`.  Every degree other than four is therefore only another critical-wall/RH
receiver.  Degree four is worse as a producer: it has exactly the fitted Ward exponent and hence
admits a ghost at every grade, including every hypothetical off-wall Xi divisor.

Thus the complete finite tensor-power radial route is nonselective.  The positive survivor is no
longer an exponent: it must be a source-natural phase, sign, or cohomological compatibility law
beyond radial norm.

`[NEW] [SHARED-WARD ROUTE-CLASS NO-GO] [SOURCE-PURE] [LEAN-PROVED]`
-/

open Complex Matrix

namespace RHTower

noncomputable section

universe u

/-- Prime-two/prime-three norm ratio of the `n`th ordinary power of the literal physical
half-density character. -/
def ccmRationalAdelicTwoThreePhysicalHalfDensityTensorPowerNormRatio
    (rho : XiDivisorSupport) (n : ℕ) : ℝ :=
  ‖(bilateralHalfDensityCharacter 2 (rho : ℂ)) ^ n‖ /
    ‖(bilateralHalfDensityCharacter 3 (rho : ℂ)) ^ n‖

/-- **Exact tensor-power exponent.**  Degree `n` multiplies the canonical half-density exponent
`t/2` by `n`. -/
theorem ccmRationalAdelicTwoThreePhysicalHalfDensityTensorPowerNormRatio_eq
    (rho : XiDivisorSupport) (n : ℕ) :
    ccmRationalAdelicTwoThreePhysicalHalfDensityTensorPowerNormRatio rho n =
      ((3 : ℝ) / 2) ^ ((n : ℝ) * (2 * (rho : ℂ).re - 1) / 2) := by
  rw [ccmRationalAdelicTwoThreePhysicalHalfDensityTensorPowerNormRatio,
    norm_pow, norm_pow, ← div_pow]
  change ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio rho ^ n = _
  rw [ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio_eq,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  congr 1
  ring

/-- Two-prime Gamma Ward legs whose radial normalization is fixed by the degree-`n` physical
half-density power. -/
def PrimeGammaTwoThreePhysicalHalfDensityTensorPowerModuleGhostWard
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (rho : XiDivisorSupport) (n : ℕ) : Prop :=
  ∃ u₂ u₃ v : V, u₃ ≠ 0 ∧
    ‖u₂‖ / ‖u₃‖ =
      ccmRationalAdelicTwoThreePhysicalHalfDensityTensorPowerNormRatio rho n ∧
    primeGammaCentralModuleGhostWardEquation
      u₂ v (2 * (rho : ℂ).re - 1) deningerCalderonWittPrimeTwo ∧
    primeGammaCentralModuleGhostWardEquation
      u₃ v (2 * (rho : ℂ).re - 1) deningerCalderonWittPrimeThree

/-- **Finite tensor-power classification.**  A physical half-density power fits two-prime Gamma
Ward exactly in degree four; every other degree fits only on the critical line. -/
theorem primeGammaTwoThreePhysicalHalfDensityTensorPowerModuleGhostWard_iff
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V]
    (rho : XiDivisorSupport) (n : ℕ) :
    PrimeGammaTwoThreePhysicalHalfDensityTensorPowerModuleGhostWard V rho n ↔
      n = 4 ∨ (rho : ℂ).re = 1 / 2 := by
  let t : ℝ := 2 * (rho : ℂ).re - 1
  constructor
  · rintro ⟨u₂, u₃, v, hu₃, hratio, htwo, hthree⟩
    have hward := primeGammaTwoThreePrimeDependentGhost_norm_ratio
      hu₃ t htwo hthree
    have hsource :=
      ccmRationalAdelicTwoThreePhysicalHalfDensityTensorPowerNormRatio_eq rho n
    have hpowers : ((3 : ℝ) / 2) ^ (2 * t) =
        ((3 : ℝ) / 2) ^ ((n : ℝ) * t / 2) := by
      calc
        ((3 : ℝ) / 2) ^ (2 * t) = ‖u₂‖ / ‖u₃‖ := hward.symm
        _ = ccmRationalAdelicTwoThreePhysicalHalfDensityTensorPowerNormRatio rho n :=
          hratio
        _ = ((3 : ℝ) / 2) ^ ((n : ℝ) * t / 2) := by simpa [t] using hsource
    have hexponents : 2 * t = (n : ℝ) * t / 2 :=
      (Real.strictMono_rpow_of_base_gt_one
        (by norm_num : (1 : ℝ) < 3 / 2)).injective hpowers
    by_cases hn : n = 4
    · exact Or.inl hn
    · right
      have hncast : (n : ℝ) ≠ 4 := by exact_mod_cast hn
      have hmul : ((4 : ℝ) - n) * t = 0 := by
        nlinarith
      have ht : t = 0 :=
        (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hncast.symm)
      dsimp only [t] at ht
      linarith
  · rintro (hn | hline)
    · subst n
      rcases primeGammaTwoThreeUnconstrainedModuleGhostWard_exists V t with
        ⟨u₂, u₃, v, hu₂, hu₃, htwo, hthree⟩
      refine ⟨u₂, u₃, v, hu₃, ?_, htwo, hthree⟩
      rw [primeGammaTwoThreePrimeDependentGhost_norm_ratio hu₃ t htwo hthree,
        ccmRationalAdelicTwoThreePhysicalHalfDensityTensorPowerNormRatio_eq]
      congr 1
      dsimp only [t]
      ring
    · have ht : t = 0 := by
        dsimp only [t]
        linarith
      obtain ⟨u, hu⟩ := exists_ne (0 : V)
      refine ⟨u, u, u, hu, ?_, ?_, ?_⟩
      · rw [div_self (norm_ne_zero_iff.mpr hu),
          ccmRationalAdelicTwoThreePhysicalHalfDensityTensorPowerNormRatio_eq,
          hline]
        norm_num
      · rw [show 2 * (rho : ℂ).re - 1 = 0 by simpa [t] using ht]
        exact primeGammaCentralModuleGhostWardEquation_of_fitted (by simp)
      · rw [show 2 * (rho : ℂ).re - 1 = 0 by simpa [t] using ht]
        exact primeGammaCentralModuleGhostWardEquation_of_fitted (by simp)

/-- Universal degree-`n` physical tensor-power radial descent over actual Xi support. -/
def EveryFrankensteinPhysicalHalfDensityTensorPowerGammaGhostDescends
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    PrimeGammaTwoThreePhysicalHalfDensityTensorPowerModuleGhostWard V rho n

/-- **Degree-four nonselectivity.**  The exact Ward exponent is source-native but produces fitted
ghosts unconditionally, so it cannot detect the RH wall. -/
theorem everyFrankensteinPhysicalHalfDensityFourthPowerGammaGhostDescends
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] :
    EveryFrankensteinPhysicalHalfDensityTensorPowerGammaGhostDescends V 4 := by
  intro rho
  exact (primeGammaTwoThreePhysicalHalfDensityTensorPowerModuleGhostWard_iff
    V rho 4).2 (Or.inl rfl)

/-- Every non-fourth finite power remains exactly an RH receiver. -/
theorem everyFrankensteinPhysicalHalfDensityTensorPowerGammaGhostDescends_iff_rh
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V]
    (n : ℕ) (hn : n ≠ 4) :
    EveryFrankensteinPhysicalHalfDensityTensorPowerGammaGhostDescends V n ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      ((primeGammaTwoThreePhysicalHalfDensityTensorPowerModuleGhostWard_iff
        V rho n).1 (h rho)).resolve_left hn
  · intro h rho
    exact (primeGammaTwoThreePhysicalHalfDensityTensorPowerModuleGhostWard_iff
      V rho n).2 (Or.inr (xi_divisor_support_re_eq_half_of_rh h rho))

/-- Closed route-class classification over every nontrivial real normed space. -/
def SharedWardFiniteHalfDensityTensorPowerRadialGhostRouteKilled : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V],
    (∀ (rho : XiDivisorSupport) (n : ℕ),
      PrimeGammaTwoThreePhysicalHalfDensityTensorPowerModuleGhostWard V rho n ↔
        n = 4 ∨ (rho : ℂ).re = 1 / 2) ∧
    EveryFrankensteinPhysicalHalfDensityTensorPowerGammaGhostDescends V 4 ∧
    (∀ n : ℕ, n ≠ 4 →
      (EveryFrankensteinPhysicalHalfDensityTensorPowerGammaGhostDescends V n ↔
        RiemannHypothesis))

/-- **[SHARED-WARD ROUTE-CLASS KILL].**  No finite physical half-density tensor power supplies an
independent radial Gamma-ghost producer: non-fourth degrees are RH-equivalent receivers, while the
unique exact degree four is fitted at every grade. -/
theorem sharedWardFiniteHalfDensityTensorPowerRadialGhostRouteKilled :
    SharedWardFiniteHalfDensityTensorPowerRadialGhostRouteKilled := by
  intro V _ _ _
  exact ⟨primeGammaTwoThreePhysicalHalfDensityTensorPowerModuleGhostWard_iff V,
    everyFrankensteinPhysicalHalfDensityFourthPowerGammaGhostDescends V,
    everyFrankensteinPhysicalHalfDensityTensorPowerGammaGhostDescends_iff_rh V⟩

end

end RHTower
