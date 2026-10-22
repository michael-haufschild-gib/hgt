import GaloisForLFunctions.RHTower.Suzuki.SuzukiLargeNegativeShiftCentralFlux

/-!
# Negative-Stieltjes mechanism for Suzuki's central Carleman flux

The corrected one-sided phase reduces Suzuki's central Herglotz obstruction to a real affine
chord of the normalized Euler--Gamma triangle jet.  This file isolates an exact source mechanism
which forces the required sign.

For two form shifts `alpha,beta`, one negative Stieltjes atom at spectral point `t` contributes
the chord kernel

`K(t;alpha,beta) = (t-alpha-beta) / ((t-alpha)*(t-beta))`.

If `beta<0` and both shifts lie below `t`, this kernel is strictly positive.  Consequently every
jet of form

`q(lambda)=kappa+slope*lambda-sum_i weight_i/(node_i-lambda)`

with nonnegative weights has affine intercept at most its asymptotic constant.  The affine
term—including the direct Neumann channel—cancels exactly.  Final theorems connect this finite
positive spectral colligation to the actual one-sided Xi-real central flux.

The corpus's large-negative-shift theorem forbids identifying the asymptotic constant with Xi
curvature uniformly: it is the initial screw average and can lie strictly above Xi curvature.
The exact source-selection condition is instead that chord-weighted spectral mass fill this
explicit gap.  This file proves that equivalence.  The unresolved source theorem is to construct
the prime--Gamma shift-variable measure and prove its gap condition for one intrinsic nonescaping
pair.  No representation, RH premise, estimate, or numerical computation is assumed here.

There is also a representation-free asymmetric selector.  If `q(lambda)` has a finite limit at
`-infinity`, the affine intercept through one escaping shift `-L` and one fixed shift `beta`
converges to `q(beta)`, not to the escape limit.  Thus one fixed source inequality below Xi
curvature already produces central-admissible two-shift pairs.
-/

open Complex Filter Topology GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Asymmetric escape retains one fixed source value -/

/-- In contrast to the dyadic pair where both shifts escape, the affine zero-intercept through
`-L` and one fixed shift converges to the value at that fixed shift. -/
theorem tendsto_suzukiRealAffineZeroIntercept_neg_atTop_fixed
    {q : ℝ → ℝ} {edge beta : ℝ}
    (hq : Tendsto q atBot (nhds edge)) :
    Tendsto (fun L : ℝ => suzukiRealAffineZeroIntercept q (-L) beta)
      atTop (nhds (q beta)) := by
  have hqneg : Tendsto (fun L : ℝ => q (-L)) atTop (nhds edge) :=
    hq.comp tendsto_neg_atTop_atBot
  have hnum : Tendsto (fun L : ℝ => beta * (q (-L) - q beta)) atTop
      (nhds (beta * (edge - q beta))) :=
    tendsto_const_nhds.mul (hqneg.sub tendsto_const_nhds)
  have hden : Tendsto (fun L : ℝ => beta + L) atTop atTop :=
    (tendsto_atTop_add_const_right _ beta tendsto_id).congr'
      (Eventually.of_forall fun L => by simp [add_comm])
  have hcorr : Tendsto
      (fun L : ℝ => beta * (q (-L) - q beta) / (beta + L))
      atTop (nhds 0) := hnum.div_atTop hden
  have hlim : Tendsto
      (fun L : ℝ => q beta + beta * (q (-L) - q beta) / (beta + L))
      atTop (nhds (q beta)) := by
    simpa using (tendsto_const_nhds (x := q beta)).add hcorr
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (-beta)] with L hL
  simp only [suzukiRealAffineZeroIntercept]
  have hden0 : beta + L ≠ 0 := by linarith
  field_simp [hden0]
  ring

/-- Any strict one-source margin below a target eventually yields a two-shift affine intercept
below the same target, by sending only the other shift to `-infinity`. -/
theorem eventually_suzukiRealAffineZeroIntercept_lt_of_fixed_lt
    {q : ℝ → ℝ} {edge beta target : ℝ}
    (hq : Tendsto q atBot (nhds edge)) (hfixed : q beta < target) :
    ∀ᶠ L in atTop,
      suzukiRealAffineZeroIntercept q (-L) beta < target := by
  have ht := tendsto_suzukiRealAffineZeroIntercept_neg_atTop_fixed
    (beta := beta) hq
  exact (tendsto_order.1 ht).2 target hfixed

/-- **Representation-free central selector.** To satisfy the exact Xi-curvature threshold it is
enough to find one fixed admissible source shift whose normalized Euler--Gamma edge jet lies
strictly below Xi curvature; pairing it with one sufficiently negative shift preserves the sign. -/
theorem eventually_suzukiRealAffineZeroIntercept_lt_XiC_curvature_of_fixed_lt
    {q : ℝ → ℝ} {edge beta : ℝ}
    (hq : Tendsto q atBot (nhds edge))
    (hfixed : q beta < (deriv (deriv XiC) 0 / XiC 0).re) :
    ∀ᶠ L in atTop,
      suzukiRealAffineZeroIntercept q (-L) beta <
        (deriv (deriv XiC) 0 / XiC 0).re :=
  eventually_suzukiRealAffineZeroIntercept_lt_of_fixed_lt hq hfixed

/-! ## Exact chord kernel -/

/-- Resolvent kernel left after taking the affine intercept at target shift zero. -/
def suzukiStieltjesChordKernel (t alpha beta : ℝ) : ℝ :=
  (t - alpha - beta) / ((t - alpha) * (t - beta))

/-- Exact common-denominator identity behind the Stieltjes central-flux mechanism. -/
theorem suzukiStieltjesChordKernel_eq_resolvent_affine_intercept
    {t alpha beta : ℝ} (hab : alpha ≠ beta) (hat : alpha ≠ t) (hbt : beta ≠ t) :
    (beta * (1 / (t - alpha)) - alpha * (1 / (t - beta))) /
        (beta - alpha) =
      suzukiStieltjesChordKernel t alpha beta := by
  simp only [suzukiStieltjesChordKernel]
  field_simp [hab, hat, hbt]
  ring

/-- A spectral atom to the right of both shifts has positive chord kernel as soon as the second
shift is negative.  In the source application both shifts are chosen negative. -/
theorem suzukiStieltjesChordKernel_pos
    {t alpha beta : ℝ} (hbeta : beta < 0)
    (hat : alpha < t) (hbt : beta < t) :
    0 < suzukiStieltjesChordKernel t alpha beta := by
  apply div_pos
  · linarith
  · exact mul_pos (sub_pos.mpr hat) (sub_pos.mpr hbt)

/-! ## One atom and finite positive colligations -/

/-- A single negative Stieltjes atom changes the affine intercept by exactly `-weight*K`;
the common linear channel disappears. -/
theorem suzukiNegativeStieltjesAtom_affine_intercept
    {t alpha beta kappa slope weight : ℝ}
    (hab : alpha ≠ beta) (hat : alpha ≠ t) (hbt : beta ≠ t) :
    (beta * (kappa + slope * alpha - weight / (t - alpha)) -
        alpha * (kappa + slope * beta - weight / (t - beta))) /
        (beta - alpha) =
      kappa - weight * suzukiStieltjesChordKernel t alpha beta := by
  rw [show weight / (t - alpha) = weight * (1 / (t - alpha)) by ring,
    show weight / (t - beta) = weight * (1 / (t - beta)) by ring]
  rw [show
      (beta * (kappa + slope * alpha - weight * (1 / (t - alpha))) -
        alpha * (kappa + slope * beta - weight * (1 / (t - beta)))) /
          (beta - alpha) =
        kappa - weight *
          ((beta * (1 / (t - alpha)) - alpha * (1 / (t - beta))) /
            (beta - alpha)) by
      field_simp [hab]
      ring]
  rw [suzukiStieltjesChordKernel_eq_resolvent_affine_intercept hab hat hbt]

/-- One nonnegative negative-Stieltjes atom can only lower the central affine intercept. -/
theorem suzukiNegativeStieltjesAtom_affine_intercept_le
    {t alpha beta kappa slope weight : ℝ}
    (hab : alpha ≠ beta) (hbeta : beta < 0)
    (hat : alpha < t) (hbt : beta < t) (hweight : 0 ≤ weight) :
    (beta * (kappa + slope * alpha - weight / (t - alpha)) -
        alpha * (kappa + slope * beta - weight / (t - beta))) /
        (beta - alpha) ≤ kappa := by
  rw [suzukiNegativeStieltjesAtom_affine_intercept hab (ne_of_lt hat) (ne_of_lt hbt)]
  exact sub_le_self kappa (mul_nonneg hweight
    (suzukiStieltjesChordKernel_pos hbeta hat hbt).le)

/-- Finite negative-Stieltjes jet with an arbitrary affine channel. -/
def suzukiFiniteNegativeStieltjesJet
    {ι : Type*} (s : Finset ι) (node weight : ι → ℝ)
    (kappa slope lambda : ℝ) : ℝ :=
  kappa + slope * lambda - ∑ i ∈ s, weight i / (node i - lambda)

/-- Exact spectral decomposition of the affine intercept of a finite negative-Stieltjes jet. -/
theorem suzukiFiniteNegativeStieltjesJet_affine_intercept
    {ι : Type*} {s : Finset ι} {node weight : ι → ℝ}
    {alpha beta kappa slope : ℝ}
    (hab : alpha ≠ beta)
    (hnodeAlpha : ∀ i ∈ s, alpha ≠ node i)
    (hnodeBeta : ∀ i ∈ s, beta ≠ node i) :
    (beta * suzukiFiniteNegativeStieltjesJet s node weight kappa slope alpha -
        alpha * suzukiFiniteNegativeStieltjesJet s node weight kappa slope beta) /
        (beta - alpha) =
      kappa - ∑ i ∈ s,
        weight i * suzukiStieltjesChordKernel (node i) alpha beta := by
  simp only [suzukiFiniteNegativeStieltjesJet]
  have hsum :
      (beta * (∑ i ∈ s, weight i / (node i - alpha)) -
          alpha * (∑ i ∈ s, weight i / (node i - beta))) / (beta - alpha) =
        ∑ i ∈ s, weight i *
          ((beta * (1 / (node i - alpha)) -
            alpha * (1 / (node i - beta))) / (beta - alpha)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [show
      (beta * (kappa + slope * alpha - ∑ i ∈ s, weight i / (node i - alpha)) -
        alpha * (kappa + slope * beta - ∑ i ∈ s, weight i / (node i - beta))) /
          (beta - alpha) =
        kappa -
          (beta * (∑ i ∈ s, weight i / (node i - alpha)) -
            alpha * (∑ i ∈ s, weight i / (node i - beta))) / (beta - alpha) by
    field_simp [hab]
    ring]
  rw [hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [suzukiStieltjesChordKernel_eq_resolvent_affine_intercept hab
    (hnodeAlpha i hi) (hnodeBeta i hi)]

/-- Finite positive spectral mass forces the exact central inequality `intercept ≤ kappa`. -/
theorem suzukiFiniteNegativeStieltjesJet_affine_intercept_le
    {ι : Type*} {s : Finset ι} {node weight : ι → ℝ}
    {alpha beta kappa slope : ℝ}
    (hab : alpha ≠ beta) (hbeta : beta < 0)
    (hnodeAlpha : ∀ i ∈ s, alpha < node i)
    (hnodeBeta : ∀ i ∈ s, beta < node i)
    (hweight : ∀ i ∈ s, 0 ≤ weight i) :
    (beta * suzukiFiniteNegativeStieltjesJet s node weight kappa slope alpha -
        alpha * suzukiFiniteNegativeStieltjesJet s node weight kappa slope beta) /
        (beta - alpha) ≤ kappa := by
  rw [suzukiFiniteNegativeStieltjesJet_affine_intercept hab
    (fun i hi => ne_of_lt (hnodeAlpha i hi))
    (fun i hi => ne_of_lt (hnodeBeta i hi))]
  exact sub_le_self kappa (Finset.sum_nonneg fun i hi =>
    mul_nonneg (hweight i hi)
      (suzukiStieltjesChordKernel_pos hbeta
        (hnodeAlpha i hi) (hnodeBeta i hi)).le)

/-! ## Connector to Suzuki's exact one-sided central flux -/

/-- If normalized triangle values factor as `q_lambda` times characteristic first jet, the
one-sided complex central source flux is exactly the real affine intercept of `q`. -/
theorem suzukiWeylNormalizedCentralSourceFlux_eq_real_affine_intercept
    {alpha beta qAlpha qBeta : ℝ} {a b : ℂ}
    (hab : alpha ≠ beta) (ha : a ≠ 0) (hb : b ≠ 0) :
    suzukiAffineSewnCentralSourceFlux
        (suzukiOneSidedCenteredShiftParameter alpha)
        (suzukiOneSidedCenteredShiftParameter beta)
        a b ((qAlpha : ℂ) * a) ((qBeta : ℂ) * b) =
      (((beta * qAlpha - alpha * qBeta) / (beta - alpha) : ℝ) : ℂ) := by
  simp only [suzukiAffineSewnCentralSourceFlux,
    suzukiOneSidedCenteredShiftParameter]
  push_cast
  have habc : (beta : ℂ) ≠ (alpha : ℂ) := by exact_mod_cast hab.symm
  have hba0 : (beta : ℂ) - alpha ≠ 0 := sub_ne_zero.mpr habc
  have hab0 : (alpha : ℂ) - beta ≠ 0 := sub_ne_zero.mpr habc.symm
  field_simp [hba0, hab0, ha, hb]
  rw [show -((beta : ℂ) * qAlpha) - -((alpha : ℂ) * qBeta) =
      -((beta : ℂ) * qAlpha - (alpha : ℂ) * qBeta) by ring]
  rw [show -(beta : ℂ) - -(alpha : ℂ) =
      -((beta : ℂ) - alpha) by ring]
  simp
  field_simp [hba0, hab0]
  ring

/-- Exact finite spectral formula for Suzuki's one-sided Weyl-normalized central flux. -/
theorem suzukiWeylNormalizedCentralSourceFlux_finiteNegativeStieltjes_eq
    {ι : Type*} {s : Finset ι} {node weight : ι → ℝ}
    {alpha beta kappa slope : ℝ} {a b : ℂ}
    (hab : alpha ≠ beta) (ha : a ≠ 0) (hb : b ≠ 0)
    (hnodeAlpha : ∀ i ∈ s, alpha ≠ node i)
    (hnodeBeta : ∀ i ∈ s, beta ≠ node i) :
    suzukiAffineSewnCentralSourceFlux
        (suzukiOneSidedCenteredShiftParameter alpha)
        (suzukiOneSidedCenteredShiftParameter beta) a b
        ((suzukiFiniteNegativeStieltjesJet s node weight kappa slope alpha : ℂ) * a)
        ((suzukiFiniteNegativeStieltjesJet s node weight kappa slope beta : ℂ) * b) =
      ((kappa - ∑ i ∈ s,
        weight i * suzukiStieltjesChordKernel (node i) alpha beta : ℝ) : ℂ) := by
  rw [suzukiWeylNormalizedCentralSourceFlux_eq_real_affine_intercept hab ha hb]
  rw [suzukiFiniteNegativeStieltjesJet_affine_intercept hab hnodeAlpha hnodeBeta]

/-- **Central source threshold from finite positive spectral mass.** A finite negative-Stieltjes
realization of the normalized triangle jet forces the exact upper bound required by the local
Herglotz residue obstruction. -/
theorem suzukiWeylNormalizedCentralSourceFlux_finiteNegativeStieltjes_re_le
    {ι : Type*} {s : Finset ι} {node weight : ι → ℝ}
    {alpha beta kappa slope : ℝ} {a b : ℂ}
    (hab : alpha ≠ beta) (ha : a ≠ 0) (hb : b ≠ 0)
    (hbeta : beta < 0)
    (hnodeAlpha : ∀ i ∈ s, alpha < node i)
    (hnodeBeta : ∀ i ∈ s, beta < node i)
    (hweight : ∀ i ∈ s, 0 ≤ weight i) :
    (suzukiAffineSewnCentralSourceFlux
        (suzukiOneSidedCenteredShiftParameter alpha)
        (suzukiOneSidedCenteredShiftParameter beta) a b
        ((suzukiFiniteNegativeStieltjesJet s node weight kappa slope alpha : ℂ) * a)
        ((suzukiFiniteNegativeStieltjesJet s node weight kappa slope beta : ℂ) * b)).re ≤
      kappa := by
  rw [suzukiWeylNormalizedCentralSourceFlux_eq_real_affine_intercept hab ha hb]
  simp only [ofReal_re]
  exact suzukiFiniteNegativeStieltjesJet_affine_intercept_le hab hbeta
    hnodeAlpha hnodeBeta hweight

/-- **Exact spectral-mass selector.** For a finite negative-Stieltjes triangle jet with arbitrary
asymptotic constant `edge`, meeting any target central bound is equivalent to filling the exact
gap `edge-target` with chord-weighted spectral mass.  This is the form compatible with the
large-negative-shift obstruction. -/
theorem suzukiWeylNormalizedCentralSourceFlux_re_le_iff_spectralMass_gap
    {ι : Type*} {s : Finset ι} {node weight : ι → ℝ}
    {alpha beta edge slope target : ℝ} {a b : ℂ}
    (hab : alpha ≠ beta) (ha : a ≠ 0) (hb : b ≠ 0)
    (hnodeAlpha : ∀ i ∈ s, alpha ≠ node i)
    (hnodeBeta : ∀ i ∈ s, beta ≠ node i) :
    (suzukiAffineSewnCentralSourceFlux
        (suzukiOneSidedCenteredShiftParameter alpha)
        (suzukiOneSidedCenteredShiftParameter beta) a b
        ((suzukiFiniteNegativeStieltjesJet s node weight edge slope alpha : ℂ) * a)
        ((suzukiFiniteNegativeStieltjesJet s node weight edge slope beta : ℂ) * b)).re ≤
      target ↔
        edge - target ≤ ∑ i ∈ s,
          weight i * suzukiStieltjesChordKernel (node i) alpha beta := by
  rw [suzukiWeylNormalizedCentralSourceFlux_finiteNegativeStieltjes_eq
    hab ha hb hnodeAlpha hnodeBeta]
  simp only [ofReal_re]
  constructor <;> intro h <;> linarith

/-- Source-ready specialization: the local Herglotz residue threshold is exactly a lower bound on
the prime--Gamma chord mass, with the already-proved Xi curvature as target. -/
theorem suzukiWeylNormalizedCentralSourceFlux_re_le_XiC_curvature_iff_spectralMass_gap
    {ι : Type*} {s : Finset ι} {node weight : ι → ℝ}
    {alpha beta edge slope : ℝ} {a b : ℂ}
    (hab : alpha ≠ beta) (ha : a ≠ 0) (hb : b ≠ 0)
    (hnodeAlpha : ∀ i ∈ s, alpha ≠ node i)
    (hnodeBeta : ∀ i ∈ s, beta ≠ node i) :
    (suzukiAffineSewnCentralSourceFlux
        (suzukiOneSidedCenteredShiftParameter alpha)
        (suzukiOneSidedCenteredShiftParameter beta) a b
        ((suzukiFiniteNegativeStieltjesJet s node weight edge slope alpha : ℂ) * a)
        ((suzukiFiniteNegativeStieltjesJet s node weight edge slope beta : ℂ) * b)).re ≤
      (deriv (deriv XiC) 0 / XiC 0).re ↔
        edge - (deriv (deriv XiC) 0 / XiC 0).re ≤
          ∑ i ∈ s, weight i * suzukiStieltjesChordKernel (node i) alpha beta :=
  suzukiWeylNormalizedCentralSourceFlux_re_le_iff_spectralMass_gap
    hab ha hb hnodeAlpha hnodeBeta

end

end RHTower
