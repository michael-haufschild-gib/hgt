import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFZZSchwarzschildDressedLogIncidence
import GaloisForLFunctions.RHTower.CCM.CCMShiftedXiCancellation
import GaloisForLFunctions.HTGeometry.MinimalTypeNoArithmeticProgression
import GaloisForLFunctions.HTGeometry.EntireBezout
import GaloisForLFunctions.HTGeometry.ReciprocalGammaPoleBranchTaylor

/-!
# FZZ--Schwarzschild response-order interpolation no-go

Solon's exact Schwarzschild dressed logarithm supplies every positive integer response derivative.
After factorial normalization, its order-`m` value is `ζ(m+2)`, exactly the protected FZZ cigar
delay clock.  This file classifies every entire continuation in the *response-order* variable.

Let

`P(z) = regularizedRiemannZeta(z+2)` and `G(z) = 1 / Gamma(-z)`.

The physical samples are `P(m) = (m+1) ζ(m+2)`.  The generator `G` is entire and has simple zeros
exactly at the nonnegative integers.  Analytic division therefore gives the exact classification

`{entire physical interpolants} = P + G * O(C)`.

Thus the complete perturbative response jet does not select a complex-order FZZ source: the
ambiguity is an infinite-dimensional principal ideal, not a finite normalization freedom.  A
global minimal-exponential-type uniqueness hypothesis cannot repair this, because the canonical
carrier `P` itself has the arithmetic progression of trivial-zeta zeros `-4,-6,...` and hence is
not of minimal exponential type.

This kills the response-jet-only branch of

`Schwarzschild integer jet -> complex-order FZZ source -> orientation law -> Ward equivariance`.

The sharp positive survivor is the principal-ideal classification: a viable selection law must
add off-lattice/nonlocal source data or a genuinely one-sided growth law that admits `P` while
excluding every nonzero Gamma-null deformation.

**[FALSIFIED] [ROUTE KILL] [PAPER-PROVED] [LEAN-PROVED]** Entireness plus all perturbative
response orders uniquely determine the complex-order continuation.

**[NOVELTY AUDIT]** Carlson-type integer interpolation and analytic division are classical.  A
targeted literature audit through 2026-08-30 found no FZZ/Schwarzschild response-order theorem and
no identification of this exact Gamma-null ambiguity module.  Novelty is restricted to the exact
cross-model classification and its RH-route consequence.
-/

open Complex Set

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Canonical entire pole-filled continuation of the factorial-normalized black-hole response
clock in the response-order variable. -/
def blackHolePoleFilledJetInterpolation (z : ℂ) : ℂ :=
  regularizedRiemannZeta (z + 2)

/-- Canonical generator of the entire functions invisible at every natural response order. -/
def naturalJetNullGenerator (z : ℂ) : ℂ :=
  (Complex.Gamma (-z))⁻¹

theorem differentiable_blackHolePoleFilledJetInterpolation :
    Differentiable ℂ blackHolePoleFilledJetInterpolation := by
  exact differentiable_regularizedRiemannZeta.comp (by fun_prop)

theorem differentiable_naturalJetNullGenerator :
    Differentiable ℂ naturalJetNullGenerator := by
  exact Complex.differentiable_one_div_Gamma.comp (by fun_prop)

/-- The canonical continuation reproduces every factorial-normalized physical Schwarzschild/FZZ
response sample, independently of far-zone scale convention. -/
theorem blackHolePoleFilledJetInterpolation_nat
    (scaleLog : ℂ) (m : ℕ) :
    blackHolePoleFilledJetInterpolation (m : ℂ) =
      ((m + 1 : ℕ) : ℂ) *
        (HTGeometry.normalizedBlackHoleFarZoneJet scaleLog m : ℂ) := by
  have hne : ((m : ℂ) + 2) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [blackHolePoleFilledJetInterpolation,
    regularizedRiemannZeta_of_ne_one hne,
    HTGeometry.normalizedBlackHoleFarZoneJet_ofReal_eq_riemannZeta]
  rw [show (m : ℂ) + 2 = ((m + 2 : ℕ) : ℂ) by push_cast; ring]
  congr 1
  push_cast
  ring

theorem naturalJetNullGenerator_nat (m : ℕ) :
    naturalJetNullGenerator (m : ℂ) = 0 := by
  simp [naturalJetNullGenerator, Complex.Gamma_neg_nat_eq_zero]

theorem naturalJetNullGenerator_neg_one :
    naturalJetNullGenerator (-1) = 1 := by
  simp [naturalJetNullGenerator]

/-- Reciprocal Gamma after reflection has exactly the natural response orders as its zero set. -/
theorem naturalJetNullGenerator_eq_zero_iff (z : ℂ) :
    naturalJetNullGenerator z = 0 ↔ ∃ m : ℕ, z = (m : ℂ) := by
  rw [naturalJetNullGenerator, inv_eq_zero, Complex.Gamma_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, neg_inj.mp hm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by ring⟩

/-- Every natural response-order zero of the Gamma-null generator is simple. -/
theorem analyticOrderAt_naturalJetNullGenerator_nat (m : ℕ) :
    analyticOrderAt naturalJetNullGenerator (m : ℂ) = 1 := by
  have hana : AnalyticAt ℂ naturalJetNullGenerator (m : ℂ) :=
    differentiable_naturalJetNullGenerator.differentiableOn.analyticAt
      (s := Set.univ) Filter.univ_mem
  apply hana.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · exact naturalJetNullGenerator_nat m
  · have hinner : HasDerivAt (fun z : ℂ => -z) (-1) (m : ℂ) :=
      (hasDerivAt_id (m : ℂ)).neg
    have hcomp := (hasDerivAt_oneDivGamma_neg_nat m).comp (m : ℂ) hinner
    have hcomp' : HasDerivAt naturalJetNullGenerator
        (((-1 : ℂ) ^ m * (m.factorial : ℂ)) * (-1)) (m : ℂ) := by
      change HasDerivAt ((fun z : ℂ => (Complex.Gamma z)⁻¹) ∘ fun z => -z)
        (((-1 : ℂ) ^ m * (m.factorial : ℂ)) * (-1)) (m : ℂ)
      exact hcomp
    have hderiv : deriv naturalJetNullGenerator (m : ℂ) =
        ((-1 : ℂ) ^ m * (m.factorial : ℂ)) * (-1) := by
      exact hcomp'.deriv
    rw [hderiv]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero m (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero m)) (by norm_num)

/-- Entire continuations carrying precisely the complete physical Schwarzschild response samples. -/
def IsEntireBlackHoleJetInterpolant (scaleLog : ℂ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧
    ∀ m : ℕ, F (m : ℂ) =
      ((m + 1 : ℕ) : ℂ) *
        (HTGeometry.normalizedBlackHoleFarZoneJet scaleLog m : ℂ)

/-- **Exact principal-ideal classification.** Every entire response-order interpolation, and only
such an interpolation, is the canonical pole-filled shifted zeta plus an arbitrary entire
multiple of `1 / Gamma(-z)`. -/
theorem isEntireBlackHoleJetInterpolant_iff_gammaNullDeformation
    (scaleLog : ℂ) (F : ℂ → ℂ) :
    IsEntireBlackHoleJetInterpolant scaleLog F ↔
      ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
        ∀ z : ℂ, F z = blackHolePoleFilledJetInterpolation z +
          H z * naturalJetNullGenerator z := by
  constructor
  · rintro ⟨hF, hsample⟩
    let D : ℂ → ℂ := fun z => F z - blackHolePoleFilledJetInterpolation z
    have hD : Differentiable ℂ D := hF.sub differentiable_blackHolePoleFilledJetInterpolation
    have horder : ∀ z : ℂ,
        analyticOrderAt naturalJetNullGenerator z ≤ analyticOrderAt D z := by
      intro z
      by_cases hz : naturalJetNullGenerator z = 0
      · obtain ⟨m, rfl⟩ := (naturalJetNullGenerator_eq_zero_iff z).mp hz
        rw [analyticOrderAt_naturalJetNullGenerator_nat]
        have hDzero : D (m : ℂ) = 0 := by
          dsimp only [D]
          rw [hsample m, blackHolePoleFilledJetInterpolation_nat scaleLog m]
          exact sub_self _
        have hDA : AnalyticAt ℂ D (m : ℂ) :=
          hD.differentiableOn.analyticAt (s := Set.univ) Filter.univ_mem
        exact Order.one_le_iff_ne_zero.mpr (fun hzero => by
          rw [hDA.analyticOrderAt_eq_zero] at hzero
          exact hzero hDzero)
      · have hzero : analyticOrderAt naturalJetNullGenerator z = 0 :=
          (differentiable_naturalJetNullGenerator.differentiableOn.analyticAt
            (s := Set.univ) Filter.univ_mem).analyticOrderAt_eq_zero.mpr hz
        rw [hzero]
        exact bot_le
    obtain ⟨H, hH, hfactor⟩ := exists_entire_quotient hD
      differentiable_naturalJetNullGenerator
      ⟨-1, by simp [naturalJetNullGenerator_neg_one]⟩ horder
    refine ⟨H, hH, fun z => ?_⟩
    have hz := hfactor z
    dsimp only [D] at hz
    rw [← hz]
    ring
  · rintro ⟨H, hH, hfactor⟩
    constructor
    · have hprod : Differentiable ℂ (fun z => H z * naturalJetNullGenerator z) :=
        hH.mul differentiable_naturalJetNullGenerator
      rw [show F = fun z => blackHolePoleFilledJetInterpolation z +
          H z * naturalJetNullGenerator z from funext hfactor]
      exact differentiable_blackHolePoleFilledJetInterpolation.add hprod
    · intro m
      rw [hfactor, naturalJetNullGenerator_nat, mul_zero, add_zero,
        blackHolePoleFilledJetInterpolation_nat scaleLog m]

/-- One explicit noncanonical entire continuation invisible to every response sample. -/
def blackHoleGammaNullDeformation (z : ℂ) : ℂ :=
  blackHolePoleFilledJetInterpolation z + naturalJetNullGenerator z

theorem blackHoleGammaNullDeformation_isInterpolant (scaleLog : ℂ) :
    IsEntireBlackHoleJetInterpolant scaleLog blackHoleGammaNullDeformation := by
  rw [isEntireBlackHoleJetInterpolant_iff_gammaNullDeformation]
  exact ⟨fun _ => 1, differentiable_const 1, by
    intro z
    simp [blackHoleGammaNullDeformation]⟩

theorem blackHolePoleFilledJetInterpolation_isInterpolant (scaleLog : ℂ) :
    IsEntireBlackHoleJetInterpolant scaleLog blackHolePoleFilledJetInterpolation := by
  exact ⟨differentiable_blackHolePoleFilledJetInterpolation,
    blackHolePoleFilledJetInterpolation_nat scaleLog⟩

theorem blackHoleGammaNullDeformation_ne_canonical :
    blackHoleGammaNullDeformation ≠ blackHolePoleFilledJetInterpolation := by
  intro h
  have hvalue := congrFun h (-1)
  simp [blackHoleGammaNullDeformation, naturalJetNullGenerator_neg_one] at hvalue

/-- Entireness and the complete all-order response jet never select a unique complex-order
continuation, for any far-zone scale convention. -/
theorem not_unique_entire_blackHoleJetInterpolation (scaleLog : ℂ) :
    ¬ ∃! F : ℂ → ℂ, IsEntireBlackHoleJetInterpolant scaleLog F := by
  rintro ⟨F, hF, hunique⟩
  have hcanon := hunique blackHolePoleFilledJetInterpolation
    (blackHolePoleFilledJetInterpolation_isInterpolant scaleLog)
  have hdeform := hunique blackHoleGammaNullDeformation
    (blackHoleGammaNullDeformation_isInterpolant scaleLog)
  exact blackHoleGammaNullDeformation_ne_canonical (hdeform.trans hcanon.symm)

theorem blackHolePoleFilledJetInterpolation_zero_progression (m : ℕ) :
    blackHolePoleFilledJetInterpolation (-4 - 2 * (m : ℂ)) = 0 := by
  have hne : (-4 - 2 * (m : ℂ) + 2 : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [blackHolePoleFilledJetInterpolation,
    regularizedRiemannZeta_of_ne_one hne]
  have harg : (-4 - 2 * (m : ℂ) + 2 : ℂ) = -2 * ((m : ℂ) + 1) := by ring
  rw [harg, riemannZeta_neg_two_mul_nat_add_one, mul_zero]

theorem blackHolePoleFilledJetInterpolation_zero_ne :
    blackHolePoleFilledJetInterpolation 0 ≠ 0 := by
  rw [blackHolePoleFilledJetInterpolation,
    regularizedRiemannZeta_of_ne_one (by norm_num)]
  norm_num
  exact riemannZeta_ne_zero_of_one_le_re (by norm_num)

/-- The canonical physical carrier is excluded by the global minimal-type uniqueness class: its
trivial-zeta zeros form a nonconstant arithmetic progression. -/
theorem blackHolePoleFilledJetInterpolation_not_minimalExponentialType :
    ¬ HasMinimalExponentialType blackHolePoleFilledJetInterpolation := by
  intro hmin
  apply hmin.no_arithmeticProgression_zeros (c := 0) (p := -4) (omega := -2)
    blackHolePoleFilledJetInterpolation_zero_ne (by norm_num : (-2 : ℂ) ≠ 0)
  intro m
  convert blackHolePoleFilledJetInterpolation_zero_progression m using 1
  simp [nsmul_eq_mul]
  ring

/-- **Closed FZZ--Schwarzschild response-jet route kill.** Every scale convention has multiple
entire continuations with the complete physical jet, while the canonical continuation itself lies
outside the global minimal-type class that would force arithmetic-lattice uniqueness. -/
theorem blackHole_responseJetInterpolation_route_noGo :
    (∀ scaleLog : ℂ,
      ¬ ∃! F : ℂ → ℂ, IsEntireBlackHoleJetInterpolant scaleLog F) ∧
      ¬ HasMinimalExponentialType blackHolePoleFilledJetInterpolation :=
  ⟨not_unique_entire_blackHoleJetInterpolation,
    blackHolePoleFilledJetInterpolation_not_minimalExponentialType⟩

end RHTower
