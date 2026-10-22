import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaPolarAction
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPrimePolarArithmeticAction
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilCanonicalHeadCompletedErrorControl

/-!
# Exact prime–Gamma cancellation in the Weil pole source

The actual positive pole lies in the unrestricted Friedrichs domain. Its
Gamma boundary formula, literal prime-power action, and exact rank-two Gram
entries combine before any estimate: the linear radius and exponential main
terms cancel. On the complete two-moment constrained space the remaining
pairing is precisely the logarithmic boundary kernel minus the Chebyshev and
reciprocal-Mangoldt errors. No sign of this pairing is asserted.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct
noncomputable section
namespace RHTower

/-- Opposite exponential slopes have the exact aperture-length cross pairing. -/
theorem inner_ccmPolarApertureVector_opposite (a : SuzukiPositiveAperture) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a (-s)) (ccmPolarApertureVector a s) = (2*a.1 : ℝ) := by
  change inner ℂ (ccmPolarL2Vector a (-s)) (ccmPolarL2Vector a s) = _
  rw [L2.inner_def]
  calc
    _ = ∫ x : ℝ, (centralInterval a.1).indicator (fun _ => (1:ℂ)) x := by
      apply integral_congr_ae
      filter_upwards [ccmPolarL2Vector_coeFn a (-s), ccmPolarL2Vector_coeFn a s] with x hm hp
      rw [hm,hp]
      by_cases hx : x ∈ centralInterval a.1
      · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
        simp only [ccmPolarProfile, RCLike.inner_apply, Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, ← Real.exp_add]
        simp
      · simp [indicator_of_notMem hx]
    _ = _ := by
      rw [integral_indicator (measurableSet_centralInterval a.1)]
      simp only [setIntegral_const]
      rw [measureReal_def, centralInterval, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [a.property]), Complex.real_smul, mul_one]
      push_cast
      ring

/-- Exact rank-two pole action, retaining both diagonal and off-diagonal Gram entries. -/
theorem ccmPolarOperator_polarPlus_apply (a : SuzukiPositiveAperture) :
    ccmPolarOperator a (ccmPolarApertureVector a (1/2)) =
      ((2*a.1 : ℝ) : ℂ) • ccmPolarApertureVector a (1/2) +
        ((2*Real.sinh a.1 : ℝ) : ℂ) • ccmPolarApertureVector a (-1/2) := by
  have hn : inner ℂ (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (1/2)) =
      ((2*Real.sinh a.1 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ccmPolarApertureVector a (1/2))]
    convert congrArg (fun r : ℝ => (r : ℂ)) (norm_sq_ccmPolarApertureVector_half a) using 1
    simp only [Complex.ofReal_pow]
    rfl
  rw [ccmPolarOperator, add_apply, InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply,
    show (-1/2:ℝ)=-(1/2) from by ring, inner_ccmPolarApertureVector_opposite, hn]

/-- The surviving boundary–arithmetic part of the positive-pole Weil action, before constraint pairing. -/
def ccmPolarBoundaryArithmeticProfile (a : SuzukiPositiveAperture) (x : ℝ) : ℂ :=
  (Real.exp (x/2) * (ccmGammaPolarBoundary (a.1-x) (a.1+x) -
    (Chebyshev.psi (Real.exp (a.1-x)) - Real.exp (a.1-x)) - ccmReciprocalMangoldtError (a.1+x)) : ℝ)

/-- Full actual Weil action on the positive pole: the radius and exponential main terms cancel exactly. -/
theorem ccmRestrictedWeilOperator_polarPlus_coeFn (a : SuzukiPositiveAperture) :
    ((ccmRestrictedWeilOperator a
      ⟨ccmPolarApertureVector a (1/2), ccmPolarApertureVector_mem_weilOperator_domain a (1/2)⟩ : SoninL2) :
        ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x =>
        ccmPolarBoundaryArithmeticProfile a x +
          ((-Real.eulerMascheroniConstant - Real.log (2*Real.pi)) * Real.exp (x/2) -
            Real.exp (-a.1)*Real.exp (-(x/2)) : ℝ)) := by
  let p := ccmPolarApertureVector a (1/2)
  let m := ccmPolarApertureVector a (-1/2)
  have hid : ccmRestrictedWeilOperator a
      ⟨p,ccmPolarApertureVector_mem_weilOperator_domain a (1/2)⟩ =
      (ccmPolarGammaImage a + ((2*a.1:ℝ):ℂ) • p) +
        ((2*Real.sinh a.1:ℝ):ℂ) • m - ccmFinitePrimeOperator a p := by
    rw [ccmRestrictedWeilOperator_polarHalf_eq_gamma_polar_prime, ccmPolarOperator_polarPlus_apply]
    module
  rw [hid]
  change (((ccmPolarGammaImage a : SoninL2) + ((2*a.1:ℝ):ℂ) • p.1 +
    ((2*Real.sinh a.1:ℝ):ℂ) • m.1 - (ccmFinitePrimeOperator a p : SoninL2) : SoninL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub
      ((ccmPolarGammaImage a : SoninL2) + ((2*a.1:ℝ):ℂ) • p.1 + ((2*Real.sinh a.1:ℝ):ℂ) • m.1)
      (ccmFinitePrimeOperator a p : SoninL2),
    Lp.coeFn_add ((ccmPolarGammaImage a : SoninL2) + ((2*a.1:ℝ):ℂ) • p.1)
      (((2*Real.sinh a.1:ℝ):ℂ) • m.1),
    Lp.coeFn_add (ccmPolarGammaImage a : SoninL2) (((2*a.1:ℝ):ℂ) • p.1),
    Lp.coeFn_smul ((2*a.1:ℝ):ℂ) p.1,
    Lp.coeFn_smul ((2*Real.sinh a.1:ℝ):ℂ) m.1,
    ccmPolarGammaImage_coeFn a, ccmPolarL2Vector_coeFn a (1/2),
    ccmPolarL2Vector_coeFn a (-1/2), ccmFinitePrimeOperator_polarPlus_coeFn a] with x hsub ha hb hs ht hg hp hm hprime
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at hsub ha hb hs ht
  rw [hsub, ha, hb, hs, ht, hg]
  change ccmPolarL2Vector a (1/2) x = _ at hp
  change ccmPolarL2Vector a (-1/2) x = _ at hm
  change _ + ((2*a.1:ℝ):ℂ) • ccmPolarL2Vector a (1/2) x +
    ((2*Real.sinh a.1:ℝ):ℂ) • ccmPolarL2Vector a (-1/2) x -
      (ccmFinitePrimeOperator a (ccmPolarApertureVector a (1/2)) : SoninL2) x = _
  rw [hp,hm,hprime]
  by_cases hx : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hx, ccmPolarProfile, smul_eq_mul,
      show (1/2:ℝ)*x=x/2 from by ring, show (-1/2:ℝ)*x=-(x/2) from by ring]
    unfold ccmPolarBoundaryArithmeticProfile
    have hexp : Real.exp (x/2) * Real.exp (a.1-x) =
        Real.exp a.1 * Real.exp (-(x/2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hreal : Real.exp (x/2) * (-(a.1-x) - Real.eulerMascheroniConstant - Real.log (2*Real.pi) +
        ccmGammaPolarBoundary (a.1-x) (a.1+x)) + (2*a.1)*Real.exp (x/2) +
        (2*Real.sinh a.1)*Real.exp (-(x/2)) - Real.exp (x/2)*
          (Chebyshev.psi (Real.exp (a.1-x)) + ccmReciprocalMangoldtCumulative (Real.exp (a.1+x))) =
      Real.exp (x/2) * (ccmGammaPolarBoundary (a.1-x) (a.1+x) -
        (Chebyshev.psi (Real.exp (a.1-x))-Real.exp (a.1-x)) - ccmReciprocalMangoldtError (a.1+x)) +
        ((-Real.eulerMascheroniConstant - Real.log (2*Real.pi))*Real.exp (x/2) -
          Real.exp (-a.1)*Real.exp (-(x/2))) := by
      rw [Real.sinh_eq, ccmReciprocalMangoldtError]
      nlinarith [hexp]
    exact_mod_cast hreal
  · simp only [indicator_of_notMem hx, smul_zero, add_zero, sub_zero]

/-- The actual positive-pole Weil image with the two constraint-invisible profiles removed. -/
def ccmPolarWeilBoundaryDefect (a : SuzukiPositiveAperture) : suzukiApertureHilbert a :=
  ccmPolarWeilRepresentative a (1/2) -
    ((-Real.eulerMascheroniConstant - Real.log (2*Real.pi) : ℝ) : ℂ) • ccmPolarApertureVector a (1/2) +
      (Real.exp (-a.1) : ℂ) • ccmPolarApertureVector a (-1/2)

/-- The completed operator defect is exactly the boundary kernel minus the two arithmetic errors. -/
theorem ccmPolarWeilBoundaryDefect_coeFn (a : SuzukiPositiveAperture) :
    ((ccmPolarWeilBoundaryDefect a : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (ccmPolarBoundaryArithmeticProfile a) := by
  let k : ℂ := ((-Real.eulerMascheroniConstant - Real.log (2*Real.pi) : ℝ) : ℂ)
  have hfull := ccmRestrictedWeilOperator_polarPlus_coeFn a
  rw [ccmRestrictedWeilOperator_polar_apply] at hfull
  change (((ccmPolarWeilRepresentative a (1/2) : SoninL2) - k • ccmPolarL2Vector a (1/2) +
    (Real.exp (-a.1) : ℂ) • ccmPolarL2Vector a (-1/2) : SoninL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add
      ((ccmPolarWeilRepresentative a (1/2) : SoninL2) - k • ccmPolarL2Vector a (1/2))
      ((Real.exp (-a.1) : ℂ) • ccmPolarL2Vector a (-1/2)),
    Lp.coeFn_sub (ccmPolarWeilRepresentative a (1/2) : SoninL2) (k • ccmPolarL2Vector a (1/2)),
    Lp.coeFn_smul k (ccmPolarL2Vector a (1/2)),
    Lp.coeFn_smul (Real.exp (-a.1) : ℂ) (ccmPolarL2Vector a (-1/2)), hfull,
    ccmPolarL2Vector_coeFn a (1/2), ccmPolarL2Vector_coeFn a (-1/2)] with x ha hs ht hu hf hp hm
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at ha hs ht hu
  rw [ha, hs, ht, hu, hf, hp, hm]
  by_cases hx : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hx, ccmPolarProfile, smul_eq_mul, k,
      show (1/2:ℝ)*x=x/2 from by ring, show (-1/2:ℝ)*x=-(x/2) from by ring]
    push_cast
    ring!
  · simp [indicator_of_notMem hx]

/-- Exact full-source pole pairing on the completed constrained space. No Gamma or prime main term is estimated. -/
theorem inner_polarWeil_on_constrained_eq_boundaryArithmetic_integral
    (a : SuzukiPositiveAperture) (u : ccmPolarConstraintSubmodule a) :
    inner ℂ (ccmRestrictedWeilOperator a
      ⟨ccmPolarApertureVector a (1/2), ccmPolarApertureVector_mem_weilOperator_domain a (1/2)⟩)
        (ccmArchimedeanFormToAperture a u.1) =
      ∫ x : ℝ, (centralInterval a.1).indicator (ccmPolarBoundaryArithmeticProfile a) x *
        (ccmArchimedeanFormToAperture a u.1 : SoninL2) x := by
  have hu : IsPolarConstrained a u.1 := u.2
  rw [ccmRestrictedWeilOperator_polar_apply]
  have heq : inner ℂ (ccmPolarWeilRepresentative a (1/2)) (ccmArchimedeanFormToAperture a u.1) =
      inner ℂ (ccmPolarWeilBoundaryDefect a) (ccmArchimedeanFormToAperture a u.1) := by
    rw [ccmPolarWeilBoundaryDefect, inner_add_left, inner_sub_left]
    rw [inner_smul_left (ccmPolarApertureVector a (1/2)) (ccmArchimedeanFormToAperture a u.1)
      ((-Real.eulerMascheroniConstant - Real.log (2*Real.pi) : ℝ) : ℂ),
      inner_smul_left (ccmPolarApertureVector a (-1/2)) (ccmArchimedeanFormToAperture a u.1)
      (Real.exp (-a.1) : ℂ), hu.1, hu.2]
    simp
  rw [heq]
  change inner ℂ (ccmPolarWeilBoundaryDefect a : SoninL2)
    (ccmArchimedeanFormToAperture a u.1 : SoninL2) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmPolarWeilBoundaryDefect_coeFn a] with x hx
  rw [hx]
  by_cases hmem : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hmem, RCLike.inner_apply,
      ccmPolarBoundaryArithmeticProfile, Complex.conj_ofReal]
    ring!
  · simp [indicator_of_notMem hmem]
end RHTower
