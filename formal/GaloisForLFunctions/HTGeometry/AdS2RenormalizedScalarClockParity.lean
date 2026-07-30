import GaloisForLFunctions.HTGeometry.CommonScaleDigammaOrbitCarrierUniversalityLaw
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.NearHorizonScalaronClockBoundary

/-!
# Renormalized AdS₂ scalar-clock parity boundary

For a neutral scalar with positive integer throat gap `g = 2ν`, the generic finite-temperature
response has a singular normalization at even `g`.  Removing its local polynomial pole leaves,
up to a nonzero local polynomial multiplier and an arbitrary local counterterm, the frequency
carrier

`ψ(z + 1/2 - n) + ψ(z + 1/2 + n)`  when `g = 2n`.

The two digamma terms lie on one integer-shift orbit and have total charge `2`, so this carrier is
hypertranscendental.  This file proves that exact statement and the scheme-independence theorem:
nonzero differentially algebraic multiplication and differentially algebraic counterterms cannot
erase the carrier.

The module also proves the exact even-gap Laurent extraction, exact odd-gap pole cancellation,
and the full odd-DA/even-HT/noninteger-HT meromorphic response law.  It does not declare the
physical identification with a holographic retarded response as an axiom; that map remains an
external physics theorem.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Frequency-independent neutral-scalar denominator argument in the finite-temperature AdS₂
normalization. -/
def ads2NeutralScalarStaticDenominatorArgument (gap : ℂ) : ℂ :=
  (1 - gap) / 2

/-- Odd positive gaps send the static denominator Gamma factor exactly to a pole location. -/
theorem ads2NeutralScalarStaticDenominatorArgument_odd (n : ℕ) :
    ads2NeutralScalarStaticDenominatorArgument (2 * (n : ℂ) + 1) = -(n : ℂ) := by
  unfold ads2NeutralScalarStaticDenominatorArgument
  ring

/-- Even positive gaps never send the static denominator Gamma factor to a pole location. -/
theorem ads2NeutralScalarStaticDenominatorArgument_even_ne_neg_nat (n m : ℕ) :
    ads2NeutralScalarStaticDenominatorArgument (2 * (n : ℂ)) ≠ -(m : ℂ) := by
  unfold ads2NeutralScalarStaticDenominatorArgument
  intro h
  have hc : ((2 * m + 1 : ℕ) : ℂ) = ((2 * n : ℕ) : ℂ) := by
    push_cast
    linear_combination 2 * h
  have hn : 2 * m + 1 = 2 * n := by
    exact_mod_cast hc
  omega

/-- **Static Gamma parity selector.**  The neutral AdS₂ normalization's static denominator is a
Gamma pole on every odd positive gap. -/
theorem Gamma_ads2NeutralScalarStaticDenominatorArgument_odd (n : ℕ) :
    Complex.Gamma
      (ads2NeutralScalarStaticDenominatorArgument (2 * (n : ℂ) + 1)) = 0 := by
  rw [ads2NeutralScalarStaticDenominatorArgument_odd]
  exact Complex.Gamma_neg_nat_eq_zero n

/-- The same static denominator is finite and nonzero on every even positive gap. -/
theorem Gamma_ads2NeutralScalarStaticDenominatorArgument_even_ne_zero (n : ℕ) :
    Complex.Gamma
      (ads2NeutralScalarStaticDenominatorArgument (2 * (n : ℂ))) ≠ 0 :=
  Complex.Gamma_ne_zero
    (ads2NeutralScalarStaticDenominatorArgument_even_ne_neg_nat n)

/-- The Gamma quotient viewed as a function of throat gap at fixed normalized frequency. -/
def ads2ScalarGammaGapQuotient (z gap : ℂ) : ℂ :=
  Complex.Gamma (z + (1 + gap) / 2) /
    Complex.Gamma (z + (1 - gap) / 2)

/-- Exact frequency-independent neutral-scalar AdS₂ Gamma normalization, with the elementary
nonzero temperature power omitted. -/
def ads2NeutralScalarGammaNormalization (gap : ℂ) : ℂ :=
  Complex.Gamma (-gap) * Complex.Gamma ((1 + gap) / 2) /
    (Complex.Gamma gap * Complex.Gamma ((1 - gap) / 2))

/-- Candidate residue of the neutral-scalar normalization at positive even gap `2n`, expressed
without simplifying half-integer Gamma values. -/
def ads2NeutralScalarGammaNormalizationEvenResidue (n : ℕ) : ℂ :=
  (-(1 / (((2 * n).factorial : ℕ) : ℂ))) *
    Complex.Gamma (1 / 2 + (n : ℂ)) /
      (Complex.Gamma (2 * (n : ℂ)) *
        Complex.Gamma (1 / 2 - (n : ℂ)))

private theorem tendsto_neg_evenGap_add_nhdsNE (n : ℕ) :
    Tendsto (fun epsilon : ℂ => -(2 * (n : ℂ) + epsilon))
      (𝓝[≠] (0 : ℂ)) (𝓝[≠] (-(((2 * n : ℕ) : ℂ)))) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc :
        Tendsto (fun epsilon : ℂ => -(2 * (n : ℂ) + epsilon))
          (𝓝 (0 : ℂ)) (𝓝 (-(2 * (n : ℂ)))) := by
        convert (by fun_prop :
          ContinuousAt (fun epsilon : ℂ => -(2 * (n : ℂ) + epsilon)) 0).tendsto using 1 <;>
          ring
    convert hc.mono_left nhdsWithin_le_nhds using 1 <;> push_cast <;> ring
  · filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    simp only [mem_compl_iff, mem_singleton_iff] at hepsilon ⊢
    intro h
    apply hepsilon
    push_cast at h
    linear_combination -h

/-- The even-gap normalization residue is never zero at a positive even gap. -/
theorem ads2NeutralScalarGammaNormalizationEvenResidue_ne_zero
    (n : ℕ) (hn : 0 < n) :
    ads2NeutralScalarGammaNormalizationEvenResidue n ≠ 0 := by
  have hfactorial : ((((2 * n).factorial : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have hupper : ∀ m : ℕ, (1 / 2 + (n : ℂ)) ≠ -(m : ℂ) := by
    intro m h
    have hc : (((2 * n + 2 * m + 1 : ℕ) : ℂ)) = 0 := by
      push_cast
      linear_combination 2 * h
    have hnat : 2 * n + 2 * m + 1 = 0 := by
      exact_mod_cast hc
    omega
  have hgap : ∀ m : ℕ, (2 * (n : ℂ)) ≠ -(m : ℂ) := by
    intro m h
    have hc : (((2 * n + m : ℕ) : ℂ)) = 0 := by
      push_cast
      linear_combination h
    have hnat : 2 * n + m = 0 := by
      exact_mod_cast hc
    omega
  have hlower : ∀ m : ℕ, (1 / 2 - (n : ℂ)) ≠ -(m : ℂ) := by
    intro m
    convert ads2NeutralScalarStaticDenominatorArgument_even_ne_neg_nat n m using 1 <;>
      unfold ads2NeutralScalarStaticDenominatorArgument <;> ring
  unfold ads2NeutralScalarGammaNormalizationEvenResidue
  exact div_ne_zero
    (mul_ne_zero
      (neg_ne_zero.mpr (div_ne_zero one_ne_zero hfactorial))
      (Complex.Gamma_ne_zero hupper))
    (mul_ne_zero (Complex.Gamma_ne_zero hgap)
      (Complex.Gamma_ne_zero hlower))

/-- The declared coefficient is the actual simple-pole residue of the neutral-scalar
normalization at every positive even gap. -/
theorem tendsto_ads2NeutralScalarGammaNormalization_even_residue
    (n : ℕ) (hn : 0 < n) :
    Tendsto
      (fun epsilon =>
        epsilon *
          ads2NeutralScalarGammaNormalization (2 * (n : ℂ) + epsilon))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (ads2NeutralScalarGammaNormalizationEvenResidue n)) := by
  have hmap := tendsto_neg_evenGap_add_nhdsNE n
  have hpoleRaw := (gamma_residue (2 * n)).comp hmap
  have hpole :
      Tendsto
        (fun epsilon : ℂ =>
          epsilon * Complex.Gamma (-(2 * (n : ℂ) + epsilon)))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-(1 / ((((2 * n).factorial : ℕ)) : ℂ)))) := by
    have hminusOne :
        Tendsto (fun _ : ℂ => (-1 : ℂ)) (𝓝[≠] (0 : ℂ)) (𝓝 (-1 : ℂ)) :=
      tendsto_const_nhds
    have hneg := hminusOne.mul hpoleRaw
    simp only [Function.comp_apply] at hneg
    have heqPole :
        (fun epsilon : ℂ =>
          (-1 : ℂ) *
            ((-(2 * (n : ℂ) + epsilon) + (((2 * n : ℕ) : ℂ))) *
              Complex.Gamma (-(2 * (n : ℂ) + epsilon)))) =ᶠ[𝓝[≠] (0 : ℂ)]
          (fun epsilon : ℂ =>
            epsilon * Complex.Gamma (-(2 * (n : ℂ) + epsilon))) :=
      Filter.Eventually.of_forall (fun epsilon : ℂ => by
        simp only [Function.comp_apply]
        push_cast
        ring)
    have hneg' := hneg.congr' heqPole
    simpa only [one_div, neg_mul, neg_neg, one_mul, neg_inj,
      pow_mul, neg_one_sq, one_pow] using hneg'
  have hupperPole : ∀ m : ℕ, (1 / 2 + (n : ℂ)) ≠ -(m : ℂ) := by
    intro m h
    have hc : (((2 * n + 2 * m + 1 : ℕ) : ℂ)) = 0 := by
      push_cast
      linear_combination 2 * h
    have hnat : 2 * n + 2 * m + 1 = 0 := by
      exact_mod_cast hc
    omega
  have hgapPole : ∀ m : ℕ, (2 * (n : ℂ)) ≠ -(m : ℂ) := by
    intro m h
    have hc : (((2 * n + m : ℕ) : ℂ)) = 0 := by
      push_cast
      linear_combination h
    have hnat : 2 * n + m = 0 := by
      exact_mod_cast hc
    omega
  have hlowerPole : ∀ m : ℕ, (1 / 2 - (n : ℂ)) ≠ -(m : ℂ) := by
    intro m
    convert ads2NeutralScalarStaticDenominatorArgument_even_ne_neg_nat n m using 1 <;>
      unfold ads2NeutralScalarStaticDenominatorArgument <;> ring
  have hupperArg :
      Tendsto (fun epsilon : ℂ => (1 + (2 * (n : ℂ) + epsilon)) / 2)
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 / 2 + (n : ℂ))) := by
    have hc := (by fun_prop :
      ContinuousAt (fun epsilon : ℂ => (1 + (2 * (n : ℂ) + epsilon)) / 2) 0)
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> ring
  have hgapArg :
      Tendsto (fun epsilon : ℂ => 2 * (n : ℂ) + epsilon)
        (𝓝[≠] (0 : ℂ)) (𝓝 (2 * (n : ℂ))) := by
    have hc := (by fun_prop :
      ContinuousAt (fun epsilon : ℂ => 2 * (n : ℂ) + epsilon) 0)
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> ring
  have hlowerArg :
      Tendsto (fun epsilon : ℂ => (1 - (2 * (n : ℂ) + epsilon)) / 2)
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 / 2 - (n : ℂ))) := by
    have hc := (by fun_prop :
      ContinuousAt (fun epsilon : ℂ => (1 - (2 * (n : ℂ) + epsilon)) / 2) 0)
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> ring
  have hupperGamma :=
    (Complex.continuousAt_Gamma (1 / 2 + (n : ℂ)) hupperPole).tendsto.comp hupperArg
  have hgapGamma :=
    (Complex.continuousAt_Gamma (2 * (n : ℂ)) hgapPole).tendsto.comp hgapArg
  have hlowerGamma :=
    (Complex.continuousAt_Gamma (1 / 2 - (n : ℂ)) hlowerPole).tendsto.comp hlowerArg
  have hdenominator :
      Complex.Gamma (2 * (n : ℂ)) *
        Complex.Gamma (1 / 2 - (n : ℂ)) ≠ 0 :=
    mul_ne_zero (Complex.Gamma_ne_zero hgapPole)
      (Complex.Gamma_ne_zero hlowerPole)
  have hlimit :=
    (hpole.mul hupperGamma).div (hgapGamma.mul hlowerGamma) hdenominator
  simp only [Function.comp_apply] at hlimit
  have heqLimit :
      (fun epsilon : ℂ =>
        (epsilon * Complex.Gamma (-(2 * (n : ℂ) + epsilon)) *
            Complex.Gamma ((1 + (2 * (n : ℂ) + epsilon)) / 2)) /
          (Complex.Gamma (2 * (n : ℂ) + epsilon) *
            Complex.Gamma ((1 - (2 * (n : ℂ) + epsilon)) / 2))) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun epsilon =>
          epsilon *
            ads2NeutralScalarGammaNormalization (2 * (n : ℂ) + epsilon)) :=
    Filter.Eventually.of_forall (fun epsilon : ℂ => by
      unfold ads2NeutralScalarGammaNormalization
      ring)
  have hlimit' := hlimit.congr' heqLimit
  simpa only [ads2NeutralScalarGammaNormalizationEvenResidue] using hlimit'

/-- Analytic extension of `epsilon * normalization (2n + epsilon)` through an even-gap pole. -/
def ads2NeutralScalarGammaNormalizationEvenExtension (n : ℕ) (epsilon : ℂ) : ℂ :=
  (-gammaExtension (2 * n) (-(2 * (n : ℂ) + epsilon))) *
    Complex.Gamma ((1 + (2 * (n : ℂ) + epsilon)) / 2) /
      (Complex.Gamma (2 * (n : ℂ) + epsilon) *
        Complex.Gamma ((1 - (2 * (n : ℂ) + epsilon)) / 2))

/-- The analytic extension takes the residue value at the even-gap pole. -/
theorem ads2NeutralScalarGammaNormalizationEvenExtension_zero (n : ℕ) :
    ads2NeutralScalarGammaNormalizationEvenExtension n 0 =
      ads2NeutralScalarGammaNormalizationEvenResidue n := by
  unfold ads2NeutralScalarGammaNormalizationEvenExtension
    ads2NeutralScalarGammaNormalizationEvenResidue
  have harg :
      -(2 * (n : ℂ) + 0) = -(((2 * n : ℕ) : ℂ)) := by
    push_cast
    ring
  rw [harg, gammaExtension_apply_neg]
  simp only [pow_mul, neg_one_sq, one_pow]
  congr 1 <;> push_cast <;> ring

/-- The pole-removed even-gap normalization is differentiable through the resonance. -/
theorem differentiableAt_ads2NeutralScalarGammaNormalizationEvenExtension
    (n : ℕ) (hn : 0 < n) :
    DifferentiableAt ℂ (ads2NeutralScalarGammaNormalizationEvenExtension n) 0 := by
  have hcenter :
      -(2 * (n : ℂ) + (0 : ℂ)) = -(((2 * n : ℕ) : ℂ)) := by
    push_cast
    ring
  have hextBase :
      DifferentiableAt ℂ (gammaExtension (2 * n))
        (-(((2 * n : ℕ) : ℂ))) :=
    (contDiffAt_gammaExtension (2 * n) 1).differentiableAt (by norm_num)
  have hext :
      DifferentiableAt ℂ
        (fun epsilon : ℂ =>
          gammaExtension (2 * n) (-(2 * (n : ℂ) + epsilon))) 0 := by
    have hbase :
        DifferentiableAt ℂ (gammaExtension (2 * n))
          (-(2 * (n : ℂ) + (0 : ℂ))) := by
      simpa only [hcenter] using hextBase
    have hinner :
        DifferentiableAt ℂ (fun epsilon : ℂ => -(2 * (n : ℂ) + epsilon)) 0 := by
      fun_prop
    exact hbase.comp 0 hinner
  have hupperPole :
      ∀ m : ℕ, (1 + (2 * (n : ℂ) + (0 : ℂ))) / 2 ≠ -(m : ℂ) := by
    intro m h
    have hc : (((2 * n + 2 * m + 1 : ℕ) : ℂ)) = 0 := by
      push_cast
      linear_combination 2 * h
    have hnat : 2 * n + 2 * m + 1 = 0 := by
      exact_mod_cast hc
    omega
  have hgapPole :
      ∀ m : ℕ, 2 * (n : ℂ) + (0 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have hc : (((2 * n + m : ℕ) : ℂ)) = 0 := by
      push_cast
      linear_combination h
    have hnat : 2 * n + m = 0 := by
      exact_mod_cast hc
    omega
  have hlowerPole :
      ∀ m : ℕ, (1 - (2 * (n : ℂ) + (0 : ℂ))) / 2 ≠ -(m : ℂ) := by
    intro m
    convert ads2NeutralScalarStaticDenominatorArgument_even_ne_neg_nat n m using 1 <;>
      unfold ads2NeutralScalarStaticDenominatorArgument <;> ring
  have hupper :
      DifferentiableAt ℂ
        (fun epsilon : ℂ =>
          Complex.Gamma ((1 + (2 * (n : ℂ) + epsilon)) / 2)) 0 :=
    (Complex.differentiableAt_Gamma
      ((1 + (2 * (n : ℂ) + (0 : ℂ))) / 2) hupperPole).comp 0 (by fun_prop)
  have hgap :
      DifferentiableAt ℂ
        (fun epsilon : ℂ => Complex.Gamma (2 * (n : ℂ) + epsilon)) 0 :=
    (Complex.differentiableAt_Gamma
      (2 * (n : ℂ) + (0 : ℂ)) hgapPole).comp 0 (by fun_prop)
  have hlower :
      DifferentiableAt ℂ
        (fun epsilon : ℂ =>
          Complex.Gamma ((1 - (2 * (n : ℂ) + epsilon)) / 2)) 0 :=
    (Complex.differentiableAt_Gamma
      ((1 - (2 * (n : ℂ) + (0 : ℂ))) / 2) hlowerPole).comp 0 (by fun_prop)
  have hdenominator :
      Complex.Gamma (2 * (n : ℂ) + (0 : ℂ)) *
        Complex.Gamma ((1 - (2 * (n : ℂ) + (0 : ℂ))) / 2) ≠ 0 :=
    mul_ne_zero (Complex.Gamma_ne_zero hgapPole)
      (Complex.Gamma_ne_zero hlowerPole)
  unfold ads2NeutralScalarGammaNormalizationEvenExtension
  exact (hext.neg.mul hupper).div (hgap.mul hlower) hdenominator

/-- Off the resonance, the analytic extension agrees with `epsilon` times the singular
normalization. -/
theorem ads2NeutralScalarGammaNormalizationEvenExtension_eventuallyEq
    (n : ℕ) :
    (fun epsilon =>
      epsilon * ads2NeutralScalarGammaNormalization (2 * (n : ℂ) + epsilon)) =ᶠ[
        𝓝[≠] (0 : ℂ)]
      ads2NeutralScalarGammaNormalizationEvenExtension n := by
  have hfactor :=
    (gamma_factor_near_pole (2 * n)).comp_tendsto
      (tendsto_neg_evenGap_add_nhdsNE n)
  filter_upwards [hfactor, self_mem_nhdsWithin] with epsilon hfactor hepsilon
  simp only [Function.comp_apply] at hfactor
  change
    Complex.Gamma (-(2 * (n : ℂ) + epsilon)) =
      gammaExtension (2 * n) (-(2 * (n : ℂ) + epsilon)) *
        (-(2 * (n : ℂ) + epsilon) + (((2 * n : ℕ) : ℂ)))⁻¹ at hfactor
  simp only [mem_compl_iff, mem_singleton_iff] at hepsilon
  unfold ads2NeutralScalarGammaNormalization
    ads2NeutralScalarGammaNormalizationEvenExtension
  rw [hfactor]
  have hshift :
      -(2 * (n : ℂ) + epsilon) + (((2 * n : ℕ) : ℂ)) = -epsilon := by
    push_cast
    ring
  rw [hshift]
  field_simp [hepsilon]

/-- The exact neutral-scalar normalization has a genuine regular Laurent coefficient at every
positive even gap. -/
theorem exists_ads2NeutralScalarGammaNormalization_even_regularPart
    (n : ℕ) (hn : 0 < n) :
    ∃ regular : ℂ,
      Tendsto
        (fun epsilon =>
          ads2NeutralScalarGammaNormalization (2 * (n : ℂ) + epsilon) -
            ads2NeutralScalarGammaNormalizationEvenResidue n / epsilon)
        (𝓝[≠] (0 : ℂ)) (𝓝 regular) := by
  let extension : ℂ → ℂ :=
    ads2NeutralScalarGammaNormalizationEvenExtension n
  have hdifferentiable : DifferentiableAt ℂ extension 0 := by
    simpa only [extension] using
      differentiableAt_ads2NeutralScalarGammaNormalizationEvenExtension n hn
  let regular : ℂ := deriv extension 0
  refine ⟨regular, ?_⟩
  have hslope :
      Tendsto (fun epsilon => (extension epsilon - extension 0) / epsilon)
        (𝓝[≠] (0 : ℂ)) (𝓝 regular) := by
    simpa only [regular, zero_add, div_eq_inv_mul, mul_comm, inv_smul_smul₀, one_smul] using!
      hdifferentiable.hasDerivAt.tendsto_slope_zero
  have hextension :=
    ads2NeutralScalarGammaNormalizationEvenExtension_eventuallyEq n
  have hzero := ads2NeutralScalarGammaNormalizationEvenExtension_zero n
  refine hslope.congr' ?_
  filter_upwards [hextension, self_mem_nhdsWithin] with epsilon hextension hepsilon
  simp only [mem_compl_iff, mem_singleton_iff] at hepsilon
  change
    (ads2NeutralScalarGammaNormalizationEvenExtension n epsilon -
        ads2NeutralScalarGammaNormalizationEvenExtension n 0) / epsilon =
      ads2NeutralScalarGammaNormalization (2 * (n : ℂ) + epsilon) -
        ads2NeutralScalarGammaNormalizationEvenResidue n / epsilon
  rw [hzero]
  field_simp [hepsilon]
  rw [hextension]

/-- **Gap-derivative clock identity.**  Away from its pole orbits, differentiating the scalar
Gamma quotient with respect to the gravitational gap exposes the sum of its two endpoint
digammas. -/
theorem hasDerivAt_ads2ScalarGammaGapQuotient
    (z gap : ℂ)
    (hupper : ∀ m : ℕ, z + (1 + gap) / 2 ≠ -(m : ℂ))
    (hlower : ∀ m : ℕ, z + (1 - gap) / 2 ≠ -(m : ℂ)) :
    HasDerivAt (ads2ScalarGammaGapQuotient z)
      (ads2ScalarGammaGapQuotient z gap *
        (Complex.digamma (z + (1 + gap) / 2) +
          Complex.digamma (z + (1 - gap) / 2)) / 2) gap := by
  have hupperArg :
      HasDerivAt (fun g : ℂ => z + (1 + g) / 2) (1 / 2) gap := by
    convert! (hasDerivAt_const gap z).add
      (((hasDerivAt_const gap (1 : ℂ)).add (hasDerivAt_id gap)).div_const 2) using 1
    ring
  have hlowerArg :
      HasDerivAt (fun g : ℂ => z + (1 - g) / 2) (-1 / 2) gap := by
    convert! (hasDerivAt_const gap z).add
      (((hasDerivAt_const gap (1 : ℂ)).sub (hasDerivAt_id gap)).div_const 2) using 1
    ring
  have hnum :=
    (Complex.differentiableAt_Gamma (z + (1 + gap) / 2) hupper).hasDerivAt.comp
      gap hupperArg
  have hden :=
    (Complex.differentiableAt_Gamma (z + (1 - gap) / 2) hlower).hasDerivAt.comp
      gap hlowerArg
  have hupper0 : Complex.Gamma (z + (1 + gap) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero hupper
  have hlower0 : Complex.Gamma (z + (1 - gap) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero hlower
  have hlower0' :
      Complex.Gamma (1 / 2 + z + gap * (-1 / 2)) ≠ 0 := by
    convert hlower0 using 1 <;> ring
  have hdu :
      deriv Complex.Gamma (z + (1 + gap) / 2) =
        Complex.digamma (z + (1 + gap) / 2) *
          Complex.Gamma (z + (1 + gap) / 2) := by
    rw [Complex.digamma_def, logDeriv_apply, div_mul_cancel₀ _ hupper0]
  have hdl :
      deriv Complex.Gamma (z + (1 - gap) / 2) =
        Complex.digamma (z + (1 - gap) / 2) *
          Complex.Gamma (z + (1 - gap) / 2) := by
    rw [Complex.digamma_def, logDeriv_apply, div_mul_cancel₀ _ hlower0]
  convert! hnum.div hden hlower0 using 1
  rw [hdu, hdl]
  unfold ads2ScalarGammaGapQuotient
  simp only [Function.comp_apply]
  field_simp [hlower0']
  ring

/-- **Simple-pole finite-part product law.**  If `normalization` has residue `residue` and finite
part `regular`, while `response` has derivative `responseDerivative` at the resonance, then
subtracting the product's local principal part leaves

`residue * responseDerivative + regular * response 0`.

This is the exact analytic mechanism by which gap differentiation enters a renormalized AdS₂
response. -/
theorem tendsto_simplePoleProduct_sub_principalPart
    (normalization response : ℂ → ℂ) (residue regular responseDerivative : ℂ)
    (hresidue :
      Tendsto (fun epsilon => epsilon * normalization epsilon)
        (𝓝[≠] (0 : ℂ)) (𝓝 residue))
    (hregular :
      Tendsto (fun epsilon => normalization epsilon - residue / epsilon)
        (𝓝[≠] (0 : ℂ)) (𝓝 regular))
    (hresponse : HasDerivAt response responseDerivative 0) :
    Tendsto
      (fun epsilon =>
        normalization epsilon * response epsilon -
          residue * response 0 / epsilon)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (residue * responseDerivative + regular * response 0)) := by
  have hslope :
      Tendsto (fun epsilon => (response epsilon - response 0) / epsilon)
        (𝓝[≠] (0 : ℂ)) (𝓝 responseDerivative) := by
    simpa only [zero_add, inv_smul_smul₀, one_smul, div_eq_inv_mul, mul_comm] using!
      hresponse.tendsto_slope_zero
  have hlimit :=
    (hresidue.mul hslope).add (hregular.mul_const (response 0))
  refine hlimit.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  have hepsilon0 : epsilon ≠ 0 := by
    simpa using hepsilon
  field_simp [hepsilon0]
  ring

/-- Digamma carrier exposed by the renormalized finite part at positive even gap `g = 2n`. -/
def evenResonantAdS2DigammaClockCore (n : ℕ) (z : ℂ) : ℂ :=
  Complex.digamma (z + (1 / 2 - (n : ℂ))) +
    Complex.digamma (z + (1 / 2 + (n : ℂ)))

/-- At even gap `2n`, the exact gap derivative exposes one half of the even-resonance digamma
clock, multiplied by the integer-gap Gamma quotient. -/
theorem hasDerivAt_ads2ScalarGammaGapQuotient_even
    (n : ℕ) (z : ℂ)
    (hupper : ∀ m : ℕ, z + (1 + 2 * (n : ℂ)) / 2 ≠ -(m : ℂ))
    (hlower : ∀ m : ℕ, z + (1 - 2 * (n : ℂ)) / 2 ≠ -(m : ℂ)) :
    HasDerivAt (ads2ScalarGammaGapQuotient z)
      (ads2ScalarGammaGapQuotient z (2 * (n : ℂ)) *
        evenResonantAdS2DigammaClockCore n z / 2)
      (2 * (n : ℂ)) := by
  have hu :
      z + (1 + 2 * (n : ℂ)) / 2 =
        z + (1 / 2 + (n : ℂ)) := by
    ring
  have hl :
      z + (1 - 2 * (n : ℂ)) / 2 =
        z + (1 / 2 - (n : ℂ)) := by
    ring
  simpa only [evenResonantAdS2DigammaClockCore, hu, hl, add_comm] using
    hasDerivAt_ads2ScalarGammaGapQuotient z (2 * (n : ℂ)) hupper hlower

/-- **Even-resonance memory theorem.**  Every nonnegative integer `n` gives an
hypertranscendental two-ended digamma clock.  The two ends are separated by the integer shift
`2n`, but their charges add rather than cancel. -/
theorem hypertranscendental_evenResonantAdS2DigammaClockCore (n : ℕ) :
    Hypertranscendental (evenResonantAdS2DigammaClockCore n) := by
  let charge : Fin 2 → ℂ := ![1, 1]
  let shift : Fin 2 → ℕ := ![0, 2 * n]
  have hcharge : ∑ k, charge k ≠ 0 := by
    simp [charge, Fin.sum_univ_two]
  have h :=
    hypertranscendental_commonScale_digamma_orbit_charge
      charge shift (c := (1 : ℂ)) (by norm_num)
        ((1 : ℂ) / 2 - (n : ℂ)) hcharge
  have heq :
      (fun s => ∑ k, charge k *
        Complex.digamma ((1 : ℂ) * s + ((1 : ℂ) / 2 - (n : ℂ)) + (shift k : ℂ))) =
        evenResonantAdS2DigammaClockCore n := by
    funext s
    simp only [charge, shift, evenResonantAdS2DigammaClockCore, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, Nat.cast_zero, add_zero]
    congr 1
    push_cast
    ring
  rw [heq] at h
  exact h

/-- **Exact even-gap renormalized response law.**  One normalization-dependent constant
`regular` works for every frequency away from the endpoint pole orbits.  After subtracting the
local principal part, the finite response is the nonzero normalization residue times the exact
gap derivative (hence the even-resonance digamma clock), plus the regular normalization times the
integer-gap response. -/
theorem exists_tendsto_ads2EvenRenormalizedScalarResponse_finitePart
    (n : ℕ) (hn : 0 < n) :
    ∃ regular : ℂ, ∀ z : ℂ,
      (∀ m : ℕ, z + (1 + 2 * (n : ℂ)) / 2 ≠ -(m : ℂ)) →
      (∀ m : ℕ, z + (1 - 2 * (n : ℂ)) / 2 ≠ -(m : ℂ)) →
      Tendsto
        (fun epsilon =>
          ads2NeutralScalarGammaNormalization (2 * (n : ℂ) + epsilon) *
              ads2ScalarGammaGapQuotient z (2 * (n : ℂ) + epsilon) -
            ads2NeutralScalarGammaNormalizationEvenResidue n *
              ads2ScalarGammaGapQuotient z (2 * (n : ℂ)) / epsilon)
        (𝓝[≠] (0 : ℂ))
        (𝓝
          (ads2NeutralScalarGammaNormalizationEvenResidue n *
              (ads2ScalarGammaGapQuotient z (2 * (n : ℂ)) *
                evenResonantAdS2DigammaClockCore n z / 2) +
            regular * ads2ScalarGammaGapQuotient z (2 * (n : ℂ)))) := by
  obtain ⟨regular, hregular⟩ :=
    exists_ads2NeutralScalarGammaNormalization_even_regularPart n hn
  refine ⟨regular, fun z hupper hlower => ?_⟩
  have hgapDerivative :=
    hasDerivAt_ads2ScalarGammaGapQuotient_even n z hupper hlower
  have hgapDerivative' :
      HasDerivAt (ads2ScalarGammaGapQuotient z)
        (ads2ScalarGammaGapQuotient z (2 * (n : ℂ)) *
          evenResonantAdS2DigammaClockCore n z / 2)
        (2 * (n : ℂ) + 0) := by
    simpa only [add_zero] using hgapDerivative
  have hshift :
      HasDerivAt
        (fun epsilon =>
          ads2ScalarGammaGapQuotient z (2 * (n : ℂ) + epsilon))
        (ads2ScalarGammaGapQuotient z (2 * (n : ℂ)) *
          evenResonantAdS2DigammaClockCore n z / 2) 0 := by
    have hinner :
        HasDerivAt (fun epsilon : ℂ => 2 * (n : ℂ) + epsilon) 1 0 := by
      convert! (hasDerivAt_const (0 : ℂ) (2 * (n : ℂ))).add
        (hasDerivAt_id (0 : ℂ)) using 1
      ring
    simpa only [add_zero, mul_one] using! hgapDerivative'.comp 0 hinner
  simpa only [add_zero] using
    (tendsto_simplePoleProduct_sub_principalPart
      (fun epsilon =>
        ads2NeutralScalarGammaNormalization (2 * (n : ℂ) + epsilon))
      (fun epsilon =>
        ads2ScalarGammaGapQuotient z (2 * (n : ℂ) + epsilon))
      (ads2NeutralScalarGammaNormalizationEvenResidue n) regular
      (ads2ScalarGammaGapQuotient z (2 * (n : ℂ)) *
        evenResonantAdS2DigammaClockCore n z / 2)
      (tendsto_ads2NeutralScalarGammaNormalization_even_residue n hn)
      hregular hshift)

/-- **Local-renormalization invariance.**  Multiplying an HT carrier by any nonzero DA residue and
adding any DA local counterterm preserves hypertranscendence.  This is the exact algebraic
scheme-independence principle needed for a renormalized response modulo local contact terms. -/
theorem hypertranscendentalOver_nonzeroDA_mul_add_local_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {carrier residue counterterm : E}
    (hresidue : DifferentialAlgebraicOver F residue) (hresidue0 : residue ≠ 0)
    (hcounterterm : DifferentialAlgebraicOver F counterterm) :
    HypertranscendentalOver F (residue * carrier + counterterm) ↔
      HypertranscendentalOver F carrier := by
  rw [mul_comm residue carrier,
    HTGeometry.hypertranscendentalOver_add_differentialAlgebraic_iff hcounterterm,
    HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
      hresidue hresidue0]

/-- Any renormalized representative satisfying the local finite-part form remains HT. -/
theorem hypertranscendentalOver_nonzeroDA_mul_add_local
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {carrier residue counterterm : E}
    (hcarrier : HypertranscendentalOver F carrier)
    (hresidue : DifferentialAlgebraicOver F residue) (hresidue0 : residue ≠ 0)
    (hcounterterm : DifferentialAlgebraicOver F counterterm) :
    HypertranscendentalOver F (residue * carrier + counterterm) :=
  (hypertranscendentalOver_nonzeroDA_mul_add_local_iff
    hresidue hresidue0 hcounterterm).2 hcarrier

/-- Genuine meromorphic realization of the two-ended even-resonance clock. -/
def evenResonantAdS2DigammaClockCoreMero (n : ℕ) : meroField Set.univ :=
  digammaShiftMero (1 / 2 - (n : ℂ)) +
    digammaShiftMero (1 / 2 + (n : ℂ))

/-- The normalized scalaron throat response never vanishes as a meromorphic-field element. -/
theorem scalaronThroatGammaResponseMero_ne_zero (gap : ℂ) :
    scalaronThroatGammaResponseMero gap ≠ 0 := by
  rw [scalaronThroatGammaResponseMero_eq_gammaRatio]
  exact div_ne_zero
    (gammaShiftMero_ne_zero ((1 + gap) / 2))
    (gammaShiftMero_ne_zero ((1 - gap) / 2))

/-- **Meromorphic even-resonance memory theorem.**  The exact two-ended clock at every
nonnegative even gap is hypertranscendental over the rational frequency field.  Integer
separation makes the endpoint *difference* DA, but the endpoint *sum* retains twice one
uncancelled digamma orbit. -/
theorem hypertranscendentalOver_evenResonantAdS2DigammaClockCoreMero
    (n : ℕ) :
    HypertranscendentalOver (RatFunc ℂ)
      (evenResonantAdS2DigammaClockCoreMero n) := by
  let b : Fin 1 → ℂ := fun _ => 1 / 2 - (n : ℂ)
  let charge : Fin 1 → ℂ := fun _ => 1
  have hlower :
      HypertranscendentalOver (RatFunc ℂ)
        (digammaShiftMero (1 / 2 - (n : ℂ))) := by
    have h := hypertranscendentalOver_gammaOrbitDigammaMero b charge 0
      (by simp [charge])
      (by
        intro c hc
        exact (hc (Subsingleton.elim c 0)).elim)
    simpa [b, charge, gammaOrbitDigammaMero] using h
  have hresponseDA :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (kerrNewmanChargedScalarGammaResponseMero (2 * (n : ℂ))) := by
    change DifferentialAlgebraicOver (RatFunc ℂ)
      (scalaronThroatGammaResponseMero (2 * (n : ℂ)))
    apply
      (differentialAlgebraicOver_scalaronThroatGammaResponseMero_iff_integerGap
        (2 * (n : ℂ))).2
    refine ⟨Int.ofNat (2 * n), ?_⟩
    norm_num [Int.cast_ofNat]
  have hclockDA :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (kerrNewmanChargedScalarLogResponseClockMero (2 * (n : ℂ))) := by
    by_contra hclockHT
    have hresponseHT :=
      (HTGeometry.hypertranscendentalOver_wignerSmithLogClock_iff
        (kerrNewmanChargedScalarGammaResponseMero (2 * (n : ℂ)))).1 hclockHT
    exact hresponseHT hresponseDA
  have hdiffDA :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (digammaShiftMero (1 / 2 + (n : ℂ)) -
          digammaShiftMero (1 / 2 - (n : ℂ))) := by
    rw [kerrNewmanChargedScalarLogResponseClockMero_eq_digammaDifference] at hclockDA
    convert hclockDA using 1 <;> ring
  have htwoDA :
      DifferentialAlgebraicOver (RatFunc ℂ) (2 : meroField Set.univ) := by
    simpa only [map_ofNat] using
      HTGeometry.differentialAlgebraicOver_algebraMap
        (F := RatFunc ℂ) (E := meroField Set.univ) (2 : RatFunc ℂ)
  have hsum :=
    hypertranscendentalOver_nonzeroDA_mul_add_local
      hlower htwoDA (by norm_num) hdiffDA
  convert! hsum using 1
  unfold evenResonantAdS2DigammaClockCoreMero
  ring

/-- Meromorphic frequency function equal to the exact even-gap finite part: physical residue
times the integer-gap response times the two-ended clock, plus an arbitrary regular local
counterterm proportional to the integer-gap response. -/
def ads2EvenRenormalizedScalarResponseMero
    (n : ℕ) (residue regular : ℂ) : meroField Set.univ :=
  (algebraMap ℂ (meroField Set.univ) residue *
      scalaronThroatGammaResponseMero (2 * (n : ℂ)) / 2) *
      evenResonantAdS2DigammaClockCoreMero n +
    algebraMap ℂ (meroField Set.univ) regular *
      scalaronThroatGammaResponseMero (2 * (n : ℂ))

private theorem differentialAlgebraicOver_complexConstantMero (c : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (algebraMap ℂ (meroField Set.univ) c) := by
  rw [← ratFuncC_toMero_eq_complex_natScale]
  exact HTGeometry.differentialAlgebraicOver_algebraMap _

/-- **Scheme-independent even-gap HT response.**  Every nonzero complex residue and every
complex regular subtraction constant give an HT renormalized response.  Thus no frequency-local
choice of finite counterterm can turn an even-resonance black-hole clock into a finite
differential law. -/
theorem hypertranscendentalOver_ads2EvenRenormalizedScalarResponseMero
    (n : ℕ) (residue regular : ℂ) (hresidue : residue ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ)
      (ads2EvenRenormalizedScalarResponseMero n residue regular) := by
  have hresponseDA :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (scalaronThroatGammaResponseMero (2 * (n : ℂ))) := by
    apply
      (differentialAlgebraicOver_scalaronThroatGammaResponseMero_iff_integerGap
        (2 * (n : ℂ))).2
    refine ⟨Int.ofNat (2 * n), ?_⟩
    norm_num [Int.cast_ofNat]
  have hresponse0 :
      scalaronThroatGammaResponseMero (2 * (n : ℂ)) ≠ 0 :=
    scalaronThroatGammaResponseMero_ne_zero _
  have htwoDA :
      DifferentialAlgebraicOver (RatFunc ℂ) (2 : meroField Set.univ) := by
    simpa only [map_ofNat] using
      HTGeometry.differentialAlgebraicOver_algebraMap
        (F := RatFunc ℂ) (E := meroField Set.univ) (2 : RatFunc ℂ)
  have hresidueDA :=
    differentialAlgebraicOver_complexConstantMero residue
  have hregularDA :=
    differentialAlgebraicOver_complexConstantMero regular
  have hmultiplierDA :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (algebraMap ℂ (meroField Set.univ) residue *
          scalaronThroatGammaResponseMero (2 * (n : ℂ)) / 2) :=
    HTGeometry.differentialAlgebraicOver_div
      (HTGeometry.differentialAlgebraicOver_mul hresidueDA hresponseDA)
      htwoDA
  have hmultiplier0 :
      algebraMap ℂ (meroField Set.univ) residue *
          scalaronThroatGammaResponseMero (2 * (n : ℂ)) / 2 ≠ 0 :=
    div_ne_zero
      (mul_ne_zero
        (by
          intro hzero
          apply hresidue
          exact (algebraMap ℂ (meroField Set.univ)).injective
            (by simpa using hzero))
        hresponse0)
      (by norm_num)
  have hcountertermDA :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (algebraMap ℂ (meroField Set.univ) regular *
          scalaronThroatGammaResponseMero (2 * (n : ℂ))) :=
    HTGeometry.differentialAlgebraicOver_mul hregularDA hresponseDA
  exact
    hypertranscendentalOver_nonzeroDA_mul_add_local
      (hypertranscendentalOver_evenResonantAdS2DigammaClockCoreMero n)
      hmultiplierDA hmultiplier0 hcountertermDA

/-- **Physical even-gap theorem.**  Substituting the exact neutral-scalar AdS₂ normalization
residue gives an HT renormalized black-hole clock at every positive even gap, for every finite
regular subtraction constant. -/
theorem hypertranscendentalOver_ads2EvenPhysicalRenormalizedScalarResponseMero
    (n : ℕ) (hn : 0 < n) (regular : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
      (ads2EvenRenormalizedScalarResponseMero n
        (ads2NeutralScalarGammaNormalizationEvenResidue n) regular) :=
  hypertranscendentalOver_ads2EvenRenormalizedScalarResponseMero
    n (ads2NeutralScalarGammaNormalizationEvenResidue n) regular
      (ads2NeutralScalarGammaNormalizationEvenResidue_ne_zero n hn)

/-- Finite coefficient produced when the two Gamma poles cancel at positive odd gap `2n+1`.
The unsimplified residue-ratio form records exactly which two pole scales cancel. -/
def ads2NeutralScalarGammaNormalizationOddLimit (n : ℕ) : ℂ :=
  (-((-1 : ℂ) ^ (2 * n + 1) /
      (((2 * n + 1).factorial : ℕ) : ℂ))) /
      (-2 * ((-1 : ℂ) ^ n / ((n.factorial : ℕ) : ℂ))) *
    (Complex.Gamma ((n : ℂ) + 1) /
      Complex.Gamma ((2 * n + 1 : ℕ) : ℂ))

private theorem tendsto_neg_oddGap_add_nhdsNE (n : ℕ) :
    Tendsto (fun epsilon : ℂ => -(2 * (n : ℂ) + 1 + epsilon))
      (𝓝[≠] (0 : ℂ)) (𝓝[≠] (-(((2 * n + 1 : ℕ) : ℂ)))) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc :
        Tendsto (fun epsilon : ℂ => -(2 * (n : ℂ) + 1 + epsilon))
          (𝓝 (0 : ℂ)) (𝓝 (-(2 * (n : ℂ) + 1))) := by
        convert (by fun_prop :
          ContinuousAt (fun epsilon : ℂ => -(2 * (n : ℂ) + 1 + epsilon)) 0).tendsto
          using 1 <;> ring
    convert hc.mono_left nhdsWithin_le_nhds using 1 <;> push_cast <;> ring
  · filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    simp only [mem_compl_iff, mem_singleton_iff] at hepsilon ⊢
    intro h
    apply hepsilon
    push_cast at h
    linear_combination -h

private theorem tendsto_oddStaticDenominator_add_nhdsNE (n : ℕ) :
    Tendsto
      (fun epsilon : ℂ =>
        (1 - (2 * (n : ℂ) + 1 + epsilon)) / 2)
      (𝓝[≠] (0 : ℂ)) (𝓝[≠] (-(n : ℂ))) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc :
        Tendsto
          (fun epsilon : ℂ =>
            (1 - (2 * (n : ℂ) + 1 + epsilon)) / 2)
          (𝓝 (0 : ℂ)) (𝓝 (-(n : ℂ))) := by
        convert (by fun_prop :
          ContinuousAt
            (fun epsilon : ℂ =>
              (1 - (2 * (n : ℂ) + 1 + epsilon)) / 2) 0).tendsto
          using 1 <;> ring
    exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    simp only [mem_compl_iff, mem_singleton_iff] at hepsilon ⊢
    intro h
    apply hepsilon
    linear_combination -2 * h

/-- **Odd-resonance pole-cancellation theorem.**  The apparent `0/0` normalization at every
positive odd gap has the declared finite limit. -/
theorem tendsto_ads2NeutralScalarGammaNormalization_odd_limit (n : ℕ) :
    Tendsto
      (fun epsilon =>
        ads2NeutralScalarGammaNormalization
          (2 * (n : ℂ) + 1 + epsilon))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (ads2NeutralScalarGammaNormalizationOddLimit n)) := by
  have hnegMap := tendsto_neg_oddGap_add_nhdsNE n
  have hnegativeRaw := (gamma_residue (2 * n + 1)).comp hnegMap
  have hnegative :
      Tendsto
        (fun epsilon : ℂ =>
          epsilon *
            Complex.Gamma (-(2 * (n : ℂ) + 1 + epsilon)))
        (𝓝[≠] (0 : ℂ))
        (𝓝
          (-((-1 : ℂ) ^ (2 * n + 1) /
            (((2 * n + 1).factorial : ℕ) : ℂ)))) := by
    have hscaled :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℂ => (-1 : ℂ)) (𝓝[≠] (0 : ℂ)) (𝓝 (-1 : ℂ))).mul
        hnegativeRaw
    have heq :
        (fun epsilon : ℂ =>
          (-1 : ℂ) *
            (((-(2 * (n : ℂ) + 1 + epsilon)) +
                (((2 * n + 1 : ℕ) : ℂ))) *
              Complex.Gamma (-(2 * (n : ℂ) + 1 + epsilon)))) =ᶠ[
            𝓝[≠] (0 : ℂ)]
          (fun epsilon : ℂ =>
            epsilon * Complex.Gamma (-(2 * (n : ℂ) + 1 + epsilon))) :=
      Filter.Eventually.of_forall (fun epsilon : ℂ => by
        have harg :
            -(2 * (n : ℂ) + 1 + epsilon) +
                (((2 * n + 1 : ℕ) : ℂ)) = -epsilon := by
          push_cast
          ring
        change
          (-1 : ℂ) *
              ((-(2 * (n : ℂ) + 1 + epsilon) +
                  (((2 * n + 1 : ℕ) : ℂ))) *
                Complex.Gamma (-(2 * (n : ℂ) + 1 + epsilon))) =
            epsilon * Complex.Gamma (-(2 * (n : ℂ) + 1 + epsilon))
        rw [harg]
        ring)
    have hscaled' := hscaled.congr' heq
    convert hscaled' using 1 <;> ring
  have hlowerMap := tendsto_oddStaticDenominator_add_nhdsNE n
  have hlowerRaw := (gamma_residue n).comp hlowerMap
  have hlower :
      Tendsto
        (fun epsilon : ℂ =>
          epsilon *
            Complex.Gamma
              ((1 - (2 * (n : ℂ) + 1 + epsilon)) / 2))
        (𝓝[≠] (0 : ℂ))
        (𝓝
          (-2 * ((-1 : ℂ) ^ n / ((n.factorial : ℕ) : ℂ)))) := by
    have hscaled :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℂ => (-2 : ℂ)) (𝓝[≠] (0 : ℂ)) (𝓝 (-2 : ℂ))).mul
        hlowerRaw
    have heq :
        (fun epsilon : ℂ =>
          (-2 : ℂ) *
            (((1 - (2 * (n : ℂ) + 1 + epsilon)) / 2 + (n : ℂ)) *
              Complex.Gamma
                ((1 - (2 * (n : ℂ) + 1 + epsilon)) / 2))) =ᶠ[
            𝓝[≠] (0 : ℂ)]
          (fun epsilon : ℂ =>
            epsilon *
              Complex.Gamma
                ((1 - (2 * (n : ℂ) + 1 + epsilon)) / 2)) :=
      Filter.Eventually.of_forall (fun epsilon : ℂ => by
        have harg :
            (1 - (2 * (n : ℂ) + 1 + epsilon)) / 2 + (n : ℂ) =
              -epsilon / 2 := by
          ring
        change
          (-2 : ℂ) *
              (((1 - (2 * (n : ℂ) + 1 + epsilon)) / 2 + (n : ℂ)) *
                Complex.Gamma
                  ((1 - (2 * (n : ℂ) + 1 + epsilon)) / 2)) =
            epsilon *
              Complex.Gamma
                ((1 - (2 * (n : ℂ) + 1 + epsilon)) / 2)
        rw [harg]
        ring)
    exact hscaled.congr' heq
  have hlowerLimit0 :
      -2 * ((-1 : ℂ) ^ n / ((n.factorial : ℕ) : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (div_ne_zero (pow_ne_zero n (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n))
  have hratio := hnegative.div hlower hlowerLimit0
  have hupperPole :
      ∀ m : ℕ, (n : ℂ) + 1 ≠ -(m : ℂ) := by
    intro m h
    have hc : (((n + m + 1 : ℕ) : ℂ)) = 0 := by
      push_cast
      linear_combination h
    have hnat : n + m + 1 = 0 := by
      exact_mod_cast hc
    omega
  have hgapPole :
      ∀ m : ℕ, (((2 * n + 1 : ℕ) : ℂ)) ≠ -(m : ℂ) := by
    intro m h
    have hc : (((2 * n + 1 + m : ℕ) : ℂ)) = 0 := by
      push_cast
      push_cast at h
      linear_combination h
    have hnat : 2 * n + 1 + m = 0 := by
      exact_mod_cast hc
    omega
  have hupperArg :
      Tendsto
        (fun epsilon : ℂ =>
          (1 + (2 * (n : ℂ) + 1 + epsilon)) / 2)
        (𝓝[≠] (0 : ℂ)) (𝓝 ((n : ℂ) + 1)) := by
    have hc := (by fun_prop :
      ContinuousAt
        (fun epsilon : ℂ =>
          (1 + (2 * (n : ℂ) + 1 + epsilon)) / 2) 0)
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> ring
  have hgapArg :
      Tendsto
        (fun epsilon : ℂ => 2 * (n : ℂ) + 1 + epsilon)
        (𝓝[≠] (0 : ℂ)) (𝓝 (((2 * n + 1 : ℕ) : ℂ))) := by
    have hc := (by fun_prop :
      ContinuousAt (fun epsilon : ℂ => 2 * (n : ℂ) + 1 + epsilon) 0)
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> push_cast <;> ring
  have hupperGamma :=
    (Complex.continuousAt_Gamma ((n : ℂ) + 1) hupperPole).tendsto.comp hupperArg
  have hgapGamma :=
    (Complex.continuousAt_Gamma (((2 * n + 1 : ℕ) : ℂ)) hgapPole).tendsto.comp
      hgapArg
  have hgap0 : Complex.Gamma (((2 * n + 1 : ℕ) : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero hgapPole
  have hlimit := hratio.mul (hupperGamma.div hgapGamma hgap0)
  refine hlimit.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  have hepsilon0 : epsilon ≠ 0 := by
    simpa using hepsilon
  change
    (epsilon * Complex.Gamma (-(2 * (n : ℂ) + 1 + epsilon)) /
          (epsilon *
            Complex.Gamma
              ((1 - (2 * (n : ℂ) + 1 + epsilon)) / 2))) *
        (Complex.Gamma
            ((1 + (2 * (n : ℂ) + 1 + epsilon)) / 2) /
          Complex.Gamma (2 * (n : ℂ) + 1 + epsilon)) =
      Complex.Gamma (-(2 * (n : ℂ) + 1 + epsilon)) *
          Complex.Gamma
            ((1 + (2 * (n : ℂ) + 1 + epsilon)) / 2) /
        (Complex.Gamma (2 * (n : ℂ) + 1 + epsilon) *
          Complex.Gamma
            ((1 - (2 * (n : ℂ) + 1 + epsilon)) / 2))
  rw [mul_div_mul_left _ _ hepsilon0]
  rw [div_mul_div_comm]
  congr 1 <;> ring

/-- The odd-resonance cancellation coefficient is finite and nonzero. -/
theorem ads2NeutralScalarGammaNormalizationOddLimit_ne_zero (n : ℕ) :
    ads2NeutralScalarGammaNormalizationOddLimit n ≠ 0 := by
  have hupperPole :
      ∀ m : ℕ, (n : ℂ) + 1 ≠ -(m : ℂ) := by
    intro m h
    have hc : (((n + m + 1 : ℕ) : ℂ)) = 0 := by
      push_cast
      linear_combination h
    have hnat : n + m + 1 = 0 := by
      exact_mod_cast hc
    omega
  have hgapPole :
      ∀ m : ℕ, (((2 * n + 1 : ℕ) : ℂ)) ≠ -(m : ℂ) := by
    intro m h
    have hc : (((2 * n + 1 + m : ℕ) : ℂ)) = 0 := by
      push_cast
      push_cast at h
      linear_combination h
    have hnat : 2 * n + 1 + m = 0 := by
      exact_mod_cast hc
    omega
  unfold ads2NeutralScalarGammaNormalizationOddLimit
  exact mul_ne_zero
    (div_ne_zero
      (neg_ne_zero.mpr
        (div_ne_zero (pow_ne_zero _ (by norm_num))
          (by exact_mod_cast Nat.factorial_ne_zero (2 * n + 1))))
      (mul_ne_zero (by norm_num)
        (div_ne_zero (pow_ne_zero _ (by norm_num))
          (by exact_mod_cast Nat.factorial_ne_zero n))))
    (div_ne_zero (Complex.Gamma_ne_zero hupperPole)
      (Complex.Gamma_ne_zero hgapPole))

/-- Pole-cancelled physical response at positive odd gap. -/
def ads2OddRenormalizedScalarResponseMero (n : ℕ) :
    meroField Set.univ :=
  algebraMap ℂ (meroField Set.univ)
      (ads2NeutralScalarGammaNormalizationOddLimit n) *
    scalaronThroatGammaResponseMero (2 * (n : ℂ) + 1)

/-- **Odd-resonance finite-law theorem.**  Every pole-cancelled positive odd response is
differentially algebraic over the rational frequency field. -/
theorem differentialAlgebraicOver_ads2OddRenormalizedScalarResponseMero
    (n : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (ads2OddRenormalizedScalarResponseMero n) := by
  unfold ads2OddRenormalizedScalarResponseMero
  apply HTGeometry.differentialAlgebraicOver_mul
    (differentialAlgebraicOver_complexConstantMero _)
  change DifferentialAlgebraicOver (RatFunc ℂ)
    (kerrNewmanChargedScalarGammaResponseMero (2 * (n : ℂ) + 1))
  exact differentialAlgebraicOver_kerrNewmanNeutralScalarGammaResponseMero n

/-- The pole-cancelled positive odd response is nonzero. -/
theorem ads2OddRenormalizedScalarResponseMero_ne_zero (n : ℕ) :
    ads2OddRenormalizedScalarResponseMero n ≠ 0 := by
  unfold ads2OddRenormalizedScalarResponseMero
  apply mul_ne_zero
  · intro hzero
    apply ads2NeutralScalarGammaNormalizationOddLimit_ne_zero n
    exact (algebraMap ℂ (meroField Set.univ)).injective (by simpa using hzero)
  · exact scalaronThroatGammaResponseMero_ne_zero _

/-- Exact nonresonant physical response before any integer-gap limiting prescription. -/
def ads2NonresonantPhysicalScalarResponseMero (gap : ℂ) :
    meroField Set.univ :=
  algebraMap ℂ (meroField Set.univ)
      (ads2NeutralScalarGammaNormalization gap) *
    scalaronThroatGammaResponseMero gap

/-- Away from the integer gap lattice, the exact neutral-scalar normalization is nonzero. -/
theorem ads2NeutralScalarGammaNormalization_ne_zero_of_noninteger
    (gap : ℂ) (hnoninteger : ∀ k : ℤ, gap ≠ (k : ℂ)) :
    ads2NeutralScalarGammaNormalization gap ≠ 0 := by
  have hnegative : ∀ m : ℕ, -gap ≠ -(m : ℂ) := by
    intro m h
    apply hnoninteger (Int.ofNat m)
    norm_num [Int.cast_ofNat]
    linear_combination -h
  have hupper : ∀ m : ℕ, (1 + gap) / 2 ≠ -(m : ℂ) := by
    intro m h
    apply hnoninteger (-Int.ofNat (2 * m + 1))
    norm_num [Int.cast_ofNat]
    push_cast
    linear_combination 2 * h
  have hgap : ∀ m : ℕ, gap ≠ -(m : ℂ) := by
    intro m h
    apply hnoninteger (-Int.ofNat m)
    norm_num [Int.cast_ofNat]
    exact h
  have hlower : ∀ m : ℕ, (1 - gap) / 2 ≠ -(m : ℂ) := by
    intro m h
    apply hnoninteger (Int.ofNat (2 * m + 1))
    norm_num [Int.cast_ofNat]
    push_cast
    linear_combination -2 * h
  unfold ads2NeutralScalarGammaNormalization
  exact div_ne_zero
    (mul_ne_zero (Complex.Gamma_ne_zero hnegative)
      (Complex.Gamma_ne_zero hupper))
    (mul_ne_zero (Complex.Gamma_ne_zero hgap)
      (Complex.Gamma_ne_zero hlower))

/-- **Nonresonant infinite-law theorem.**  At every noninteger complex gap, restoring the exact
nonzero physical normalization preserves hypertranscendence of the scalar response. -/
theorem hypertranscendentalOver_ads2NonresonantPhysicalScalarResponseMero
    (gap : ℂ) (hnoninteger : ∀ k : ℤ, gap ≠ (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (ads2NonresonantPhysicalScalarResponseMero gap) := by
  have hnormalizationDA :=
    differentialAlgebraicOver_complexConstantMero
      (ads2NeutralScalarGammaNormalization gap)
  have hnormalization0 :
      algebraMap ℂ (meroField Set.univ)
          (ads2NeutralScalarGammaNormalization gap) ≠ 0 := by
    intro hzero
    apply ads2NeutralScalarGammaNormalization_ne_zero_of_noninteger
      gap hnoninteger
    exact (algebraMap ℂ (meroField Set.univ)).injective (by simpa using hzero)
  have hcore :=
    (hypertranscendentalOver_scalaronThroatGammaResponseMero_iff_nonintegerGap
      gap).2 hnoninteger
  unfold ads2NonresonantPhysicalScalarResponseMero
  rw [mul_comm]
  exact
    (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
      hnormalizationDA hnormalization0).2 hcore

/-- **AdS₂ gravitational clock species law.**  The exact physical response has three
dependency-closed branches: positive odd resonances are finite-law (DA), positive even resonances
are infinite-law (HT) after every finite local subtraction, and every noninteger gap is HT. -/
theorem ads2GravitationalClockSpeciesLaw :
    (∀ n : ℕ,
      DifferentialAlgebraicOver (RatFunc ℂ)
        (ads2OddRenormalizedScalarResponseMero n)) ∧
    (∀ n : ℕ, 0 < n → ∀ regular : ℂ,
      HypertranscendentalOver (RatFunc ℂ)
        (ads2EvenRenormalizedScalarResponseMero n
          (ads2NeutralScalarGammaNormalizationEvenResidue n) regular)) ∧
    (∀ gap : ℂ, (∀ k : ℤ, gap ≠ (k : ℂ)) →
      HypertranscendentalOver (RatFunc ℂ)
        (ads2NonresonantPhysicalScalarResponseMero gap)) := by
  exact
    ⟨differentialAlgebraicOver_ads2OddRenormalizedScalarResponseMero,
      fun n hn regular =>
        hypertranscendentalOver_ads2EvenPhysicalRenormalizedScalarResponseMero
          n hn regular,
      hypertranscendentalOver_ads2NonresonantPhysicalScalarResponseMero⟩

end

end GaloisForLFunctions
