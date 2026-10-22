import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingPreDivisorFiniteSchwarzPolarizedInfiniteRankNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedSquaredSignedLaplaceNoGo

/-!
# HB pre-divisor causal Laplace factorization no-go

The exact HB pre-divisor susceptibility cannot be the causal Laplace transform of an
exponentially finite-variation signed spectral measure, even locally on a physical tail interval.
This includes infinite-total-variation spectra whenever exponential tilting at one positive
physical anchor produces finite variation.

After anchoring at `a`, write the signed transform as the difference `L` of two finite positive
half-line Laplace transforms.  It is holomorphic on `Re z > 0`.  Equality with the physical
susceptibility on `a < x < 1/2` forces the pole-cleared identity

`D(z+a) L(z) = N(z+a)`

throughout the right half-plane.  But the exact continuation has `D(1)=0` and `N(1)=864`.
Evaluation at `z=1-a` is therefore impossible.

This kills the causal spectral proof chain

`Laplace two-leg factorization -> radiative ++ compensation -> causal-cut extinction -> RH`.

The positive survivor is sharp: any remaining spectral realization must fail finite exponential
variation at every physical anchor, use negative/growing rates, change support or sheet, or leave
scalar Laplace/distribution pairing.

`[NEW] [HB] [PRE-DIVISOR] [CAUSAL LAPLACE] [ROUTE KILL] [LEAN-PROVED]`
-/

open Complex Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-- The pole-cleared susceptibility numerator remains nonzero at the first positive continuation
pole. -/
@[simp] theorem d4PreDivisorOpticalCancellationReducedNumerator_one :
    d4PreDivisorOpticalCancellationReducedNumerator 1 = 864 := by
  norm_num [d4PreDivisorOpticalCancellationReducedNumerator,
    d4EventHorizonThirdMassParityCrossNumeratorHolomorphic,
    d4PreDivisorHorizonAngularShiftHolomorphic,
    d4PreDivisorReflectedHorizonAngularShiftHolomorphic]

/-- The pole-clearing denominator vanishes at the first positive continuation pole. -/
@[simp] theorem d4PreDivisorOpticalCancellationReducedDenominator_one :
    d4PreDivisorOpticalCancellationReducedDenominator 1 = 0 := by
  norm_num [d4PreDivisorOpticalCancellationReducedDenominator,
    d4PreDivisorHorizonAngularShiftHolomorphic,
    d4PreDivisorReflectedHorizonAngularShiftHolomorphic]

/-- No difference of finite nonnegative-rate Laplace spectra realizes the exact HB susceptibility
on any anchored physical tail.  Exponential tilting converts every signed spectrum with finite
exponential variation at `a` into precisely this form. -/
theorem not_exists_finiteVariationCausalLaplaceRepresentation_d4PreDivisorSusceptibility
    (a : ℝ) (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (mu nu : Measure ℝ) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : mu (Ici (0 : ℝ))ᶜ = 0) (hnu : nu (Ici (0 : ℝ))ᶜ = 0) :
    ¬ (∀ x ∈ Ioo a (1 / 2),
      (d4PreDivisorOpticalCancellationSusceptibility x : ℂ) =
        finiteComplexLaplace mu ((x - a : ℝ) : ℂ) -
          finiteComplexLaplace nu ((x - a : ℝ) : ℂ)) := by
  intro hrep
  let L : ℂ → ℂ := fun z =>
    finiteComplexLaplace mu z - finiteComplexLaplace nu z
  let H : ℂ → ℂ := fun z =>
    d4PreDivisorOpticalCancellationReducedDenominator (z + (a : ℂ)) * L z -
      d4PreDivisorOpticalCancellationReducedNumerator (z + (a : ℂ))
  let U : Set ℂ := {z | 0 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hLdiff : DifferentiableOn ℂ L U := by
    exact (differentiableOn_finiteComplexLaplace_openRightHalfPlane mu hmu).sub
      (differentiableOn_finiteComplexLaplace_openRightHalfPlane nu hnu)
  have hDdiff : Differentiable ℂ
      (fun z : ℂ =>
        d4PreDivisorOpticalCancellationReducedDenominator (z + (a : ℂ))) := by
    unfold d4PreDivisorOpticalCancellationReducedDenominator
      d4PreDivisorHorizonAngularShiftHolomorphic
      d4PreDivisorReflectedHorizonAngularShiftHolomorphic
    fun_prop
  have hNdiff : Differentiable ℂ
      (fun z : ℂ =>
        d4PreDivisorOpticalCancellationReducedNumerator (z + (a : ℂ))) := by
    unfold d4PreDivisorOpticalCancellationReducedNumerator
      d4EventHorizonThirdMassParityCrossNumeratorHolomorphic
      d4PreDivisorHorizonAngularShiftHolomorphic
      d4PreDivisorReflectedHorizonAngularShiftHolomorphic
    fun_prop
  have hHdiff : DifferentiableOn ℂ H U := by
    exact (hDdiff.differentiableOn.mul hLdiff).sub hNdiff.differentiableOn
  have hHan : AnalyticOnNhd ℂ H U := hHdiff.analyticOnNhd hUopen
  have hHreal : ∀ t : ℝ, 0 < t → t < 1 / 2 - a → H (t : ℂ) = 0 := by
    intro t ht0 ht
    have hx0 : 0 < a + t := lt_of_le_of_lt ha0 (by linarith)
    have hxhalf : a + t < 1 / 2 := by linarith
    have hA : d4PreDivisorHorizonAngularShiftHolomorphic ((a + t : ℝ) : ℂ) ≠ 0 := by
      unfold d4PreDivisorHorizonAngularShiftHolomorphic
      apply mul_ne_zero
      · exact_mod_cast (by linarith : (a + t : ℝ) ≠ 0)
      · exact_mod_cast (by linarith : (3 - (a + t) : ℝ) ≠ 0)
    have hB : d4PreDivisorReflectedHorizonAngularShiftHolomorphic
        ((a + t : ℝ) : ℂ) ≠ 0 := by
      unfold d4PreDivisorReflectedHorizonAngularShiftHolomorphic
      apply mul_ne_zero
      · exact_mod_cast (by linarith : (1 - (a + t) : ℝ) ≠ 0)
      · exact_mod_cast (by linarith : (2 + (a + t) : ℝ) ≠ 0)
    have hrat := d4PreDivisorOpticalCancellationHolomorphicContinuation_eq_reduced
      (((a + t : ℝ) : ℂ)) hA hB
    have hreal := d4PreDivisorOpticalCancellationHolomorphicContinuation_ofReal (a + t)
    have hden : d4PreDivisorOpticalCancellationReducedDenominator
        (((a + t : ℝ) : ℂ)) ≠ 0 := by
      unfold d4PreDivisorOpticalCancellationReducedDenominator
      exact mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB)
    have hsource :
        d4PreDivisorOpticalCancellationReducedDenominator (((a + t : ℝ) : ℂ)) *
            (d4PreDivisorOpticalCancellationSusceptibility (a + t) : ℂ) =
          d4PreDivisorOpticalCancellationReducedNumerator (((a + t : ℝ) : ℂ)) := by
      have hratio :
          (d4PreDivisorOpticalCancellationSusceptibility (a + t) : ℂ) =
            d4PreDivisorOpticalCancellationReducedNumerator (((a + t : ℝ) : ℂ)) /
              d4PreDivisorOpticalCancellationReducedDenominator
                (((a + t : ℝ) : ℂ)) := hreal.symm.trans hrat
      rw [hratio]
      field_simp [hden]
    have hrep' := hrep (a + t) ⟨by linarith, hxhalf⟩
    have hL : L (t : ℂ) =
        (d4PreDivisorOpticalCancellationSusceptibility (a + t) : ℂ) := by
      dsimp [L]
      simpa using hrep'.symm
    change d4PreDivisorOpticalCancellationReducedDenominator
        ((t : ℂ) + (a : ℂ)) * L (t : ℂ) -
          d4PreDivisorOpticalCancellationReducedNumerator
            ((t : ℂ) + (a : ℂ)) = 0
    rw [hL]
    rw [Complex.ofReal_add] at hsource
    simpa only [add_comm] using sub_eq_zero.mpr hsource
  let d : ℝ := (1 / 2 - a) / 3
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hdlt : d < 1 / 2 - a := by dsimp [d]; linarith
  have htwodlt : 2 * d < 1 / 2 - a := by dsimp [d]; linarith
  have hdU : ((d : ℝ) : ℂ) ∈ U := by simpa [U] using hd0
  let u : ℕ → ℂ := fun m => (d + d / (m + 1) : ℝ)
  have hutend : Tendsto u atTop (nhds (d : ℂ)) := by
    have hzero : Tendsto (fun m : ℕ => (d / (m + 1) : ℝ)) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero, one_mul] using
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul d)
    exact (Complex.continuous_ofReal.tendsto d).comp
      (by simpa [u] using hzero.const_add d)
  have hune : ∀ m : ℕ, u m ≠ (d : ℂ) := by
    intro m hm
    have hm' : d + d / (m + 1 : ℝ) = d := Complex.ofReal_injective hm
    have hzero : d / (m + 1 : ℝ) = 0 := by linarith
    exact (div_ne_zero (ne_of_gt hd0) (by positivity)) hzero
  have huzero : ∀ m : ℕ, H (u m) = 0 := by
    intro m
    apply hHreal
    · have hdenpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hqpos : 0 < d / ((m : ℝ) + 1) := div_pos hd0 hdenpos
      linarith
    · have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
      have hdenpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hfrac : d / ((m : ℝ) + 1) ≤ d := by
        rw [div_le_iff₀ hdenpos]
        nlinarith [hd0.le]
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] ((d : ℝ) : ℂ), H z = 0 := by
    have htendWithin : Tendsto u atTop (nhdsWithin (d : ℂ) {((d : ℝ) : ℂ)}ᶜ) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hutend
        (Eventually.of_forall hune)
    exact htendWithin.frequently (Frequently.of_forall huzero)
  have hzero := hHan.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt 0).isPreconnected hdU hfreq
  have htargetU : (1 - (a : ℂ)) ∈ U := by
    change 0 < (1 - (a : ℂ)).re
    simp
    linarith
  have htarget := hzero htargetU
  norm_num [H, L] at htarget

/-- Closed route class: no signed nonnegative-rate causal spectrum with finite exponential
variation at one physical anchor can realize the exact HB pre-divisor compensation law. -/
def D4HBPreDivisorExponentiallyFiniteVariationCausalLaplaceRouteKilled : Prop :=
  ∀ (a : ℝ), 0 ≤ a → a < 1 / 2 →
    ∀ (mu nu : Measure ℝ), IsFiniteMeasure mu → IsFiniteMeasure nu →
      mu (Ici (0 : ℝ))ᶜ = 0 → nu (Ici (0 : ℝ))ᶜ = 0 →
        ¬ (∀ x ∈ Ioo a (1 / 2),
          (d4PreDivisorOpticalCancellationSusceptibility x : ℂ) =
            finiteComplexLaplace mu ((x - a : ℝ) : ℂ) -
              finiteComplexLaplace nu ((x - a : ℝ) : ℂ))

/-- Premise-free Lean certificate killing exponentially finite-variation causal Laplace
factorization as the missing HB radiative `++` producer. -/
theorem d4HBPreDivisorExponentiallyFiniteVariationCausalLaplaceRouteKilled :
    D4HBPreDivisorExponentiallyFiniteVariationCausalLaplaceRouteKilled := by
  intro a ha0 ha mu nu hmuFin hnuFin hmu hnu
  letI : IsFiniteMeasure mu := hmuFin
  letI : IsFiniteMeasure nu := hnuFin
  exact not_exists_finiteVariationCausalLaplaceRepresentation_d4PreDivisorSusceptibility
    a ha0 ha mu nu hmu hnu

end

end RHTower
