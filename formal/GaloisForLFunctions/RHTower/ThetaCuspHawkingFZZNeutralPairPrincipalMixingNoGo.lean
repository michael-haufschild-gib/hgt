import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZNeutralScreeningRecoilEndpoint
import GaloisForLFunctions.RHTower.BurnolCoPoissonTopConormalPluckerHolonomyLanding

/-!
# FZZ neutral-pair coupling and unconditional principal mixing

The genus-one fractional-winding area tangent is not single-valued by itself.  FZZ torus
monodromy permits only charge-neutral products with equal numbers of `W⁺` and `W⁻` screenings.
Consequently the bare condensate coupling `μ` enters the physical vacuum series only through the
canonically de-ramified neutral-pair coupling

`lambda = μ²`.

This file proves the exact coefficient rewrite

`μ^(2n)/(n!)² = lambda^n/(n!)²`,

its first-depth identity, and its screening recurrence.  It then applies the existing
FZZ/Parikh--Wilczek same-depth weld.  At neutral depth one the response is exactly

`lambda * schwarzschildParikhWilczekMellinJet 1 s`.

The coefficient of `lambda` is nonzero throughout the open critical strip.  Hence every actual
Xi divisor copy, on or off the critical line, is dark at depth zero and bright at the first
neutral-pair depth.  In the physically forced pair coordinate, the response has an unconditional
nonzero principal jet and mixes at every nonzero coupling.

This is a sharp no-go for using coupling onset or mere nonvanishing as the RH selector: the
source-faithful neutral-pair response already has unit onset on every Xi sector.  Its positive
survivor is equally sharp.  Any remaining RH producer must use the phase/sign of the one-pair
correlator or prove that it equals the canonical theta backreaction edge; it cannot ask only
whether the first pair couples.

`[PHYSICAL STATUS]` The Lean statements are unconditional identities for the exact objects already
defined in the corpus.  As recorded in the imported endpoint, identifying FZZ neutral screening
depth with four-dimensional Parikh--Wilczek recoil depth is still a conjectural cross-regime
bridge.  Nothing here identifies this response with target-space canonical energy or with the
Schur/Cayley completion of the negative theta cubic.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.FZZCigar

/-- Torus neutrality canonically packages two opposite bare winding insertions into one physical
neutral-pair coupling. -/
def fzzTorusNeutralPairCoupling (μ : ℂ) : ℂ :=
  μ ^ 2

/-- Coefficient of neutral screening depth `n` in the de-ramified pair coordinate. -/
def fzzTorusNeutralPairCoefficient (lambda : ℂ) (n : ℕ) : ℂ :=
  lambda ^ n / ((n.factorial : ℂ) ^ 2)

/-- Exact de-ramification of the full neutral FZZ screening weight. -/
theorem neutralScreeningCoefficient_eq_fzzTorusNeutralPairCoefficient
    (μ : ℂ) (n : ℕ) :
    neutralScreeningCoefficient μ n =
      fzzTorusNeutralPairCoefficient (fzzTorusNeutralPairCoupling μ) n := by
  simp only [neutralScreeningCoefficient, fzzTorusNeutralPairCoefficient,
    fzzTorusNeutralPairCoupling]
  rw [← pow_mul]

theorem fzzTorusNeutralPairCoefficient_zero (lambda : ℂ) :
    fzzTorusNeutralPairCoefficient lambda 0 = 1 := by
  simp [fzzTorusNeutralPairCoefficient]

/-- First admissible neutral screening weight is exactly linear in the physical pair coupling. -/
theorem fzzTorusNeutralPairCoefficient_one (lambda : ℂ) :
    fzzTorusNeutralPairCoefficient lambda 1 = lambda := by
  simp [fzzTorusNeutralPairCoefficient]

/-- No combinatorial screening coefficient vanishes away from zero pair coupling. -/
theorem fzzTorusNeutralPairCoefficient_ne_zero
    {lambda : ℂ} (hlambda : lambda ≠ 0) (n : ℕ) :
    fzzTorusNeutralPairCoefficient lambda n ≠ 0 := by
  apply div_ne_zero
  · exact pow_ne_zero n hlambda
  · exact pow_ne_zero 2 (by exact_mod_cast Nat.factorial_ne_zero n)

/-- Exact adjacent-depth recurrence of the neutral screening tower. -/
theorem fzzTorusNeutralPairCoefficient_succ
    (lambda : ℂ) (n : ℕ) :
    (((n + 1 : ℕ) : ℂ) ^ 2) *
        fzzTorusNeutralPairCoefficient lambda (n + 1) =
      lambda * fzzTorusNeutralPairCoefficient lambda n := by
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  simp only [fzzTorusNeutralPairCoefficient, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp [hfac]

/-- Depth-one FZZ/Parikh--Wilczek response in the canonical neutral-pair coordinate. -/
def thetaCuspHawkingFZZNeutralPairResponse (lambda s : ℂ) : ℂ :=
  lambda * schwarzschildParikhWilczekMellinJet 1 s

/-- The response has an exact first-order coupling jet before any Xi specialization. -/
theorem hasDerivAt_thetaCuspHawkingFZZNeutralPairResponse
    (lambda s : ℂ) :
    HasDerivAt (fun z : ℂ => thetaCuspHawkingFZZNeutralPairResponse z s)
      (schwarzschildParikhWilczekMellinJet 1 s) lambda := by
  simpa [thetaCuspHawkingFZZNeutralPairResponse] using
    (hasDerivAt_id lambda).mul_const (schwarzschildParikhWilczekMellinJet 1 s)

/-- The original depth-one coefficient is exactly the pair-coordinate response at `lambda=μ²`. -/
theorem fzzParikhWilczekNeutralRecoilCoefficient_one_eq_pairResponse
    (μ s : ℂ) :
    fzzParikhWilczekNeutralRecoilCoefficient μ 1 s =
      thetaCuspHawkingFZZNeutralPairResponse
        (fzzTorusNeutralPairCoupling μ) s := by
  simp [fzzParikhWilczekNeutralRecoilCoefficient, neutralScreeningCoefficient,
    thetaCuspHawkingFZZNeutralPairResponse, fzzTorusNeutralPairCoupling]

/-- Every nonzero pair coupling activates the explicit depth-one response in the open strip. -/
theorem thetaCuspHawkingFZZNeutralPairResponse_ne_zero
    {lambda s : ℂ} (hlambda : lambda ≠ 0) (hs : 0 < s.re) :
    thetaCuspHawkingFZZNeutralPairResponse lambda s ≠ 0 := by
  exact mul_ne_zero hlambda
    (schwarzschildParikhWilczekMellinJet_ne_zero (by norm_num) hs)

/-- Every actual Xi divisor copy has a nonzero principal neutral-pair response. -/
theorem xiZeroCopy_thetaCuspHawkingFZZNeutralPairResponse_ne_zero
    (q : XiZeroCopy) {lambda : ℂ} (hlambda : lambda ≠ 0) :
    thetaCuspHawkingFZZNeutralPairResponse lambda (q.1 : ℂ) ≠ 0 := by
  exact thetaCuspHawkingFZZNeutralPairResponse_ne_zero hlambda
    (xi_divisor_support_re_mem_open_unit q.1).1

/-- Coefficient-level form: the principal pair derivative is nonzero at every Xi divisor. -/
theorem xiZeroCopy_thetaCuspHawkingFZZNeutralPairResponse_principalJet
    (q : XiZeroCopy) :
    HasDerivAt
        (fun lambda : ℂ =>
          thetaCuspHawkingFZZNeutralPairResponse lambda (q.1 : ℂ))
        (schwarzschildParikhWilczekMellinJet 1 (q.1 : ℂ)) 0 ∧
      schwarzschildParikhWilczekMellinJet 1 (q.1 : ℂ) ≠ 0 := by
  refine ⟨hasDerivAt_thetaCuspHawkingFZZNeutralPairResponse 0 (q.1 : ℂ), ?_⟩
  exact schwarzschildParikhWilczekMellinJet_ne_zero (by norm_num)
    (xi_divisor_support_re_mem_open_unit q.1).1

/-- Exact dark-to-bright transition: an Xi divisor is dark before recoil and bright after one
neutral FZZ pair. -/
theorem xiZeroCopy_fzzNeutralDepth_zero_dark_firstPair_bright
    (q : XiZeroCopy) {μ : ℂ} (hμ : μ ≠ 0) :
    fzzParikhWilczekNeutralRecoilCoefficient μ 0 (q.1 : ℂ) = 0 ∧
      thetaCuspHawkingFZZNeutralPairResponse
        (fzzTorusNeutralPairCoupling μ) (q.1 : ℂ) ≠ 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hmix := thetaXi_fzzParikhWilczekNeutralRecoil_all_positive_depths_ne_zero
    hμ hstrip.1 hstrip.2 (xi_eq_zero_of_mem_divisor_support q.1)
  refine ⟨hmix.1, ?_⟩
  rw [← fzzParikhWilczekNeutralRecoilCoefficient_one_eq_pairResponse]
  exact hmix.2 1 (by norm_num)

/-- Closed all-sector statement for the explicit source-faithful pair response. -/
def ThetaCuspHawkingFZZNeutralPairPrincipalMixing : Prop :=
  ∀ (q : XiZeroCopy) (lambda : ℂ), lambda ≠ 0 →
    thetaCuspHawkingFZZNeutralPairResponse lambda (q.1 : ℂ) ≠ 0

/-- **Unconditional principal-mixing no-go.** The FZZ/Parikh--Wilczek neutral-pair response mixes
every Xi sector at every nonzero physical pair coupling, independent of critical-line location. -/
theorem thetaCuspHawking_fzzNeutralPairPrincipalMixing :
    ThetaCuspHawkingFZZNeutralPairPrincipalMixing := by
  intro q lambda hlambda
  exact xiZeroCopy_thetaCuspHawkingFZZNeutralPairResponse_ne_zero q hlambda

end

end RHTower
