import GaloisForLFunctions.RHTower.SourceGammaEquimodularPrimeDependentGhostRigidity
import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveFisherReflectionCurvature
import GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapRadialPhasePolarization

/-!
# Reflection-radial source--Gamma ghost rigidity

Prime-dependent Gamma ghosts must have the exact cross-prime norm ratio

`‖u₂‖ / ‖u₃‖ = (3/2)^(2*t)`.

This file tests the two strongest source-derived radial laws already present in the corpus.

First, every reflection-even ratio fails off the critical wall.  Applying the Ward ratio law at
`t` and `-t` gives reciprocal powers of `3/2`; equality of the source ratios forces `t = 0`.
This applies in particular to the exact adaptive-Fisher/frozen-Hodge frame distortion, which the
corpus proves is even under functional-equation reflection.

Second, the actual physical half-density is orientation-sensitive and therefore survives the
parity test.  Its prime-two/prime-three ratio is computed here exactly as `(3/2)^(t/2)`, and its
reflected ratio is reciprocal.  But Gamma Ward requires `(3/2)^(2*t)`.  Strict monotonicity exposes
a fourfold exponent mismatch, again forcing `t = 0`.

Thus neither FE-even source work nor the canonical reciprocal physical half-density can provide
an independent radial ghost producer.  Universal existence of either class over the actual Xi
divisor is exactly RH; the physical class is also exactly the shared HB/FZZ-P/PW-B/RBH endpoint.
The sharp survivor must be reflection-reciprocal and must derive the precise exponent `2*t` from
source dynamics rather than the canonical half-density exponent `t/2`.

`[NEW] [SHARED-WARD ROUTE-CLASS NO-GO] [SOURCE-PURE] [LEAN-PROVED]`
-/

open Complex Matrix

namespace RHTower

noncomputable section

universe u

/-- **Reflection-even radial rigidity.**  If the source presents the same prime-two/prime-three
norm ratio at reflected grades `t` and `-t`, simultaneous two-prime Gamma Ward descent forces
neutral grade. -/
theorem primeGammaTwoThreeReflectionEvenRadialGhost_rigidity
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u₂ u₃ v w₂ w₃ z : V}
    (hu₃ : u₃ ≠ 0) (hw₃ : w₃ ≠ 0)
    (hratio : ‖u₂‖ / ‖u₃‖ = ‖w₂‖ / ‖w₃‖) (t : ℝ)
    (htwo : primeGammaCentralModuleGhostWardEquation
      u₂ v t deningerCalderonWittPrimeTwo)
    (hthree : primeGammaCentralModuleGhostWardEquation
      u₃ v t deningerCalderonWittPrimeThree)
    (htwoReflect : primeGammaCentralModuleGhostWardEquation
      w₂ z (-t) deningerCalderonWittPrimeTwo)
    (hthreeReflect : primeGammaCentralModuleGhostWardEquation
      w₃ z (-t) deningerCalderonWittPrimeThree) :
    t = 0 := by
  have hforward := primeGammaTwoThreePrimeDependentGhost_norm_ratio
    hu₃ t htwo hthree
  have hreflected := primeGammaTwoThreePrimeDependentGhost_norm_ratio
    hw₃ (-t) htwoReflect hthreeReflect
  have hpowers : ((3 : ℝ) / 2) ^ (2 * t) =
      ((3 : ℝ) / 2) ^ (2 * (-t)) := by
    calc
      ((3 : ℝ) / 2) ^ (2 * t) = ‖u₂‖ / ‖u₃‖ := hforward.symm
      _ = ‖w₂‖ / ‖w₃‖ := hratio
      _ = ((3 : ℝ) / 2) ^ (2 * (-t)) := hreflected
  have hexponents : 2 * t = 2 * (-t) :=
    (Real.strictMono_rpow_of_base_gt_one
      (by norm_num : (1 : ℝ) < 3 / 2)).injective hpowers
  linarith

/-- Existence of reflected two-prime Ward legs with an FE-even radial norm ratio. -/
def PrimeGammaTwoThreeReflectionEvenRadialModuleGhostWard
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (t : ℝ) : Prop :=
  ∃ u₂ u₃ v w₂ w₃ z : V,
    u₃ ≠ 0 ∧ w₃ ≠ 0 ∧
    ‖u₂‖ / ‖u₃‖ = ‖w₂‖ / ‖w₃‖ ∧
    primeGammaCentralModuleGhostWardEquation
      u₂ v t deningerCalderonWittPrimeTwo ∧
    primeGammaCentralModuleGhostWardEquation
      u₃ v t deningerCalderonWittPrimeThree ∧
    primeGammaCentralModuleGhostWardEquation
      w₂ z (-t) deningerCalderonWittPrimeTwo ∧
    primeGammaCentralModuleGhostWardEquation
      w₃ z (-t) deningerCalderonWittPrimeThree

/-- Reflection-even radial two-prime ghosts exist exactly at neutral grade. -/
theorem primeGammaTwoThreeReflectionEvenRadialModuleGhostWard_iff
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V]
    (t : ℝ) :
    PrimeGammaTwoThreeReflectionEvenRadialModuleGhostWard V t ↔ t = 0 := by
  constructor
  · rintro ⟨u₂, u₃, v, w₂, w₃, z, hu₃, hw₃, hratio,
      htwo, hthree, htwoReflect, hthreeReflect⟩
    exact primeGammaTwoThreeReflectionEvenRadialGhost_rigidity
      hu₃ hw₃ hratio t htwo hthree htwoReflect hthreeReflect
  · rintro rfl
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    refine ⟨u, u, u, u, u, u, hu, hu, rfl, ?_, ?_, ?_, ?_⟩ <;>
      exact primeGammaCentralModuleGhostWardEquation_of_fitted (by simp)

/-- Source-specific specialization: both reflected ratios are the literal frozen/adaptive Fisher
frame distortion at one prime clock. -/
def PrimeGammaTwoThreeFisherFrameRadialModuleGhostWard
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Nat.Primes) (t : ℝ) : Prop :=
  ∃ u₂ u₃ v w₂ w₃ z : V,
    u₃ ≠ 0 ∧ w₃ ≠ 0 ∧
    ‖u₂‖ / ‖u₃‖ = sourceHorizontalPrimeFisherFrameDistortion p t ∧
    ‖w₂‖ / ‖w₃‖ = sourceHorizontalPrimeFisherFrameDistortion p (-t) ∧
    primeGammaCentralModuleGhostWardEquation
      u₂ v t deningerCalderonWittPrimeTwo ∧
    primeGammaCentralModuleGhostWardEquation
      u₃ v t deningerCalderonWittPrimeThree ∧
    primeGammaCentralModuleGhostWardEquation
      w₂ z (-t) deningerCalderonWittPrimeTwo ∧
    primeGammaCentralModuleGhostWardEquation
      w₃ z (-t) deningerCalderonWittPrimeThree

/-- **Fisher-frame radial no-go.**  The actual FE-even Fisher/Hodge distortion can satisfy the
two-prime reflected ghost problem only at neutral grade. -/
theorem primeGammaTwoThreeFisherFrameRadialModuleGhostWard_iff
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V]
    (p : Nat.Primes) (t : ℝ) :
    PrimeGammaTwoThreeFisherFrameRadialModuleGhostWard V p t ↔ t = 0 := by
  constructor
  · rintro ⟨u₂, u₃, v, w₂, w₃, z, hu₃, hw₃, hforward, hreflected,
      htwo, hthree, htwoReflect, hthreeReflect⟩
    apply primeGammaTwoThreeReflectionEvenRadialGhost_rigidity
      hu₃ hw₃ _ t htwo hthree htwoReflect hthreeReflect
    rw [hforward, hreflected, sourceHorizontalPrimeFisherFrameDistortion_even]
  · rintro rfl
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have hdist : sourceHorizontalPrimeFisherFrameDistortion p 0 = 1 :=
      (sourceHorizontalPrimeFisherFrameDistortion_eq_one_iff p 0).2 rfl
    refine ⟨u, u, u, u, u, u, hu, hu, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdist]
      exact div_self (norm_ne_zero_iff.mpr hu)
    · simpa [hdist] using div_self (norm_ne_zero_iff.mpr hu)
    all_goals exact primeGammaCentralModuleGhostWardEquation_of_fitted (by simp)

/-- Canonical prime-two/prime-three norm ratio of the actual physical Xi half-density. -/
def ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio
    (rho : XiDivisorSupport) : ℝ :=
  ‖bilateralHalfDensityCharacter 2 (rho : ℂ)‖ /
    ‖bilateralHalfDensityCharacter 3 (rho : ℂ)‖

/-- **Exact physical exponent.**  The actual half-density carries exponent `t/2`, where
`t = 2 Re(rho) - 1`. -/
theorem ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio_eq
    (rho : XiDivisorSupport) :
    ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio rho =
      ((3 : ℝ) / 2) ^ ((2 * (rho : ℂ).re - 1) / 2) := by
  rw [ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio,
    norm_bilateralHalfDensityCharacter (by norm_num : 0 < 2),
    norm_bilateralHalfDensityCharacter (by norm_num : 0 < 3)]
  change (2 : ℝ) ^ (1 / 2 - (rho : ℂ).re) /
      (3 : ℝ) ^ (1 / 2 - (rho : ℂ).re) = _
  rw [← Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) ≤ 3)]
  have hbase : (2 / 3 : ℝ) = ((3 / 2 : ℝ))⁻¹ := by norm_num
  rw [hbase, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  congr 1
  ring

/-- **Sharp positive survivor.**  Unlike Fisher work, the physical half-density ratio is
reflection-reciprocal rather than reflection-even. -/
theorem ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio_mul_reflection
    (rho : XiDivisorSupport) :
    ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio rho *
        ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio
          (xiZeroReflectEquiv rho) = 1 := by
  rw [ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio_eq,
    ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio_eq]
  have hreflect : 2 * (xiZeroReflectEquiv rho : ℂ).re - 1 =
      -(2 * (rho : ℂ).re - 1) := by
    rw [xiZeroReflectEquiv_apply]
    simp
    ring
  rw [hreflect, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3 / 2)]
  have hexp : (2 * (rho : ℂ).re - 1) / 2 +
      (-(2 * (rho : ℂ).re - 1)) / 2 = 0 := by ring
  rw [hexp, Real.rpow_zero]

/-- **Physical half-density exponent mismatch.**  If forward-leg norms are fixed by the actual
two-prime physical half-density, Gamma Ward requires exponent `2*t` while the source supplies
`t/2`; equality forces the Xi divisor onto the critical line. -/
theorem primeGammaTwoThreePhysicalHalfDensityGhost_rigidity
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u₂ u₃ v : V} (hu₃ : u₃ ≠ 0) (rho : XiDivisorSupport)
    (hratio : ‖u₂‖ / ‖u₃‖ =
      ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio rho)
    (htwo : primeGammaCentralModuleGhostWardEquation
      u₂ v (2 * (rho : ℂ).re - 1) deningerCalderonWittPrimeTwo)
    (hthree : primeGammaCentralModuleGhostWardEquation
      u₃ v (2 * (rho : ℂ).re - 1) deningerCalderonWittPrimeThree) :
    (rho : ℂ).re = 1 / 2 := by
  let t : ℝ := 2 * (rho : ℂ).re - 1
  have hward := primeGammaTwoThreePrimeDependentGhost_norm_ratio
    hu₃ t htwo hthree
  have hpowers : ((3 : ℝ) / 2) ^ (2 * t) =
      ((3 : ℝ) / 2) ^ (t / 2) := by
    calc
      ((3 : ℝ) / 2) ^ (2 * t) = ‖u₂‖ / ‖u₃‖ := hward.symm
      _ = ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio rho := hratio
      _ = ((3 : ℝ) / 2) ^ (t / 2) := by
        simpa [t] using
          ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio_eq rho
  have hexponents : 2 * t = t / 2 :=
    (Real.strictMono_rpow_of_base_gt_one
      (by norm_num : (1 : ℝ) < 3 / 2)).injective hpowers
  dsimp only [t] at hexponents
  linarith

/-- Actual physical half-density norms used as the prime-dependent forward ghost normalization. -/
def PrimeGammaTwoThreePhysicalHalfDensityModuleGhostWard
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (rho : XiDivisorSupport) : Prop :=
  ∃ u₂ u₃ v : V, u₃ ≠ 0 ∧
    ‖u₂‖ / ‖u₃‖ =
      ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio rho ∧
    primeGammaCentralModuleGhostWardEquation
      u₂ v (2 * (rho : ℂ).re - 1) deningerCalderonWittPrimeTwo ∧
    primeGammaCentralModuleGhostWardEquation
      u₃ v (2 * (rho : ℂ).re - 1) deningerCalderonWittPrimeThree

/-- Physical half-density radial ghosts exist exactly on the critical line. -/
theorem primeGammaTwoThreePhysicalHalfDensityModuleGhostWard_iff
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V]
    (rho : XiDivisorSupport) :
    PrimeGammaTwoThreePhysicalHalfDensityModuleGhostWard V rho ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨u₂, u₃, v, hu₃, hratio, htwo, hthree⟩
    exact primeGammaTwoThreePhysicalHalfDensityGhost_rigidity
      hu₃ rho hratio htwo hthree
  · intro hline
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have hratio : ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio rho = 1 := by
      rw [ccmRationalAdelicTwoThreePhysicalHalfDensityNormRatio_eq, hline]
      norm_num
    have ht : 2 * (rho : ℂ).re - 1 = 0 := by linarith
    refine ⟨u, u, u, hu, ?_, ?_, ?_⟩
    · rw [hratio]
      exact div_self (norm_ne_zero_iff.mpr hu)
    · rw [ht]
      exact primeGammaCentralModuleGhostWardEquation_of_fitted (by simp)
    · rw [ht]
      exact primeGammaCentralModuleGhostWardEquation_of_fitted (by simp)

/-- Universal reflection-even radial ghost descent over actual Xi support. -/
def EveryFrankensteinReflectionEvenRadialGammaGhostDescends
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop :=
  ∀ rho : XiDivisorSupport,
    PrimeGammaTwoThreeReflectionEvenRadialModuleGhostWard V
      (2 * (rho : ℂ).re - 1)

/-- Universal Fisher-frame radial ghost descent over actual Xi support. -/
def EveryFrankensteinFisherFrameRadialGammaGhostDescends
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Nat.Primes) : Prop :=
  ∀ rho : XiDivisorSupport,
    PrimeGammaTwoThreeFisherFrameRadialModuleGhostWard V p
      (2 * (rho : ℂ).re - 1)

/-- Universal physical-half-density radial ghost descent over actual Xi support. -/
def EveryFrankensteinPhysicalHalfDensityGammaGhostDescends
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop :=
  ∀ rho : XiDivisorSupport,
    PrimeGammaTwoThreePhysicalHalfDensityModuleGhostWard V rho

theorem everyFrankensteinReflectionEvenRadialGammaGhostDescends_iff_riemannHypothesis
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] :
    EveryFrankensteinReflectionEvenRadialGammaGhostDescends V ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => by
      have ht := (primeGammaTwoThreeReflectionEvenRadialModuleGhostWard_iff V _).mp
        (h rho)
      linarith
  · intro h rho
    apply (primeGammaTwoThreeReflectionEvenRadialModuleGhostWard_iff V _).mpr
    have hr := xi_divisor_support_re_eq_half_of_rh h rho
    linarith

theorem everyFrankensteinFisherFrameRadialGammaGhostDescends_iff_riemannHypothesis
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V]
    (p : Nat.Primes) :
    EveryFrankensteinFisherFrameRadialGammaGhostDescends V p ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => by
      have ht := (primeGammaTwoThreeFisherFrameRadialModuleGhostWard_iff V p _).mp
        (h rho)
      linarith
  · intro h rho
    apply (primeGammaTwoThreeFisherFrameRadialModuleGhostWard_iff V p _).mpr
    have hr := xi_divisor_support_re_eq_half_of_rh h rho
    linarith

theorem everyFrankensteinPhysicalHalfDensityGammaGhostDescends_iff_riemannHypothesis
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] :
    EveryFrankensteinPhysicalHalfDensityGammaGhostDescends V ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (primeGammaTwoThreePhysicalHalfDensityModuleGhostWard_iff V rho).mp (h rho)
  · intro h rho
    apply (primeGammaTwoThreePhysicalHalfDensityModuleGhostWard_iff V rho).mpr
    exact xi_divisor_support_re_eq_half_of_rh h rho

/-- The actual physical-half-density ghost law is exactly the common four-route endpoint. -/
theorem everyFrankensteinPhysicalHalfDensityGammaGhostDescends_iff_sharedFourRouteWardEndpoint
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] :
    EveryFrankensteinPhysicalHalfDensityGammaGhostDescends V ↔
      SharedFourRouteWardEndpoint := by
  have hshared : SharedFourRouteWardEndpoint ↔ RiemannHypothesis :=
    everyFrankensteinChannelResolvedGammaJointNaturality_iff_sharedFourRouteWardEndpoint.symm.trans
      everyFrankensteinChannelResolvedGammaJointNaturality_iff_riemannHypothesis
  exact
    (everyFrankensteinPhysicalHalfDensityGammaGhostDescends_iff_riemannHypothesis V).trans
      hshared.symm

/-- Closed route-class classification over every nontrivial real normed space. -/
def SharedWardReflectionRadialGammaGhostRouteKilled : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V],
    (∀ t : ℝ, PrimeGammaTwoThreeReflectionEvenRadialModuleGhostWard V t ↔ t = 0) ∧
    (∀ (p : Nat.Primes) (t : ℝ),
      PrimeGammaTwoThreeFisherFrameRadialModuleGhostWard V p t ↔ t = 0) ∧
    (∀ rho : XiDivisorSupport,
      PrimeGammaTwoThreePhysicalHalfDensityModuleGhostWard V rho ↔
        (rho : ℂ).re = 1 / 2) ∧
    (EveryFrankensteinReflectionEvenRadialGammaGhostDescends V ↔ RiemannHypothesis) ∧
    (∀ p : Nat.Primes,
      EveryFrankensteinFisherFrameRadialGammaGhostDescends V p ↔ RiemannHypothesis) ∧
    (EveryFrankensteinPhysicalHalfDensityGammaGhostDescends V ↔
      SharedFourRouteWardEndpoint) ∧
    (EveryFrankensteinPhysicalHalfDensityGammaGhostDescends V ↔ RiemannHypothesis)

/-- **[SHARED-WARD ROUTE-CLASS KILL].**  Both FE-even source radial normalizations and the actual
reflection-reciprocal physical half-density fail as independent two-prime Gamma ghost producers.
The former has wrong reflection parity; the latter has the exact but wrong exponent `t/2` instead
of `2*t`.  Their universal laws are only the existing shared four-route/RH wall receiver. -/
theorem sharedWardReflectionRadialGammaGhostRouteKilled :
    SharedWardReflectionRadialGammaGhostRouteKilled := by
  intro V _ _ _
  exact ⟨primeGammaTwoThreeReflectionEvenRadialModuleGhostWard_iff V,
    primeGammaTwoThreeFisherFrameRadialModuleGhostWard_iff V,
    primeGammaTwoThreePhysicalHalfDensityModuleGhostWard_iff V,
    everyFrankensteinReflectionEvenRadialGammaGhostDescends_iff_riemannHypothesis V,
    everyFrankensteinFisherFrameRadialGammaGhostDescends_iff_riemannHypothesis V,
    everyFrankensteinPhysicalHalfDensityGammaGhostDescends_iff_sharedFourRouteWardEndpoint V,
    everyFrankensteinPhysicalHalfDensityGammaGhostDescends_iff_riemannHypothesis V⟩

end

end RHTower
