import GaloisForLFunctions.RHTower.ThetaCuspHawkingEKGCompletedEisensteinOpticalIncidence
import GaloisForLFunctions.HTGeometry.ReciprocalGammaPoleBranchTaylor

/-!
# Hypergeometric radial Jost incidence for the theta topological black hole

This module constructs the radial object missing from the preceding angular optical calculation.
It uses the exact Klein--Gordon scattering problem on the four-dimensional massless topological
AdS black hole, not a thermal analogy.

For the conformally coupled massless scalar, the ingoing radial solution has hypergeometric
parameters

`a = 3/4 - I*(omega-xi)/2`,
`b = 3/4 - I*(omega+xi)/2`,
`c = 1-I*omega`.

The coefficient of the forbidden asymptotic AdS branch is

`B(omega,xi) = Gamma(c) Gamma(1/2) / (Gamma(a) Gamma(b))`.

This is Eq. (2.11), specialized to `beta_+=1`, in Aros--Martinez--Troncoso--Zanelli,
*Quasinormal modes for massless topological black holes*, arXiv:hep-th/0211024.  Vanishing
of this coefficient is exactly their zero-flux boundary condition.  We therefore define both
the normalized Evans/Jost determinant `1/(Gamma(a)Gamma(b))` and the literal physical boundary
coefficient `B`.

For the theta cusp, `xi=z/2+I/4` is the analytically continued horizon angular momentum.
The continuation is explicit: physical L2 hyperbolic harmonics have real `xi`; theta scattering
divisors lie on the resonance continuation.  At every actual Xi divisor, imaginary-axis
nonvanishing of centered Xi rules out accidental Gamma-pole collisions.  Consequently:

* each exact QNM branch is a simple zero of the full physical boundary Jost coefficient;
* each is a simple pole of its retarded Green reciprocal;
* the scalar Jost product is shadow invariant;
* the branch-resolved chiral quotient is inverted by the shadow;
* completed Eisenstein EKG angular vertices are bright on both sheets.

Thus divisor points are not poles of the Jost function: they label angular resonances whose two
radial QNM descendants are Jost zeros and Green poles.  This proves a sharp scalar no-go.  Exact
Klein--Gordon dynamics forces both shadow-related radial sectors and cannot select the canonical
theta split.

Birmingham--Mokhtari, arXiv:hep-th/0609028, reduce exact gravitational topological-black-hole
perturbations to analogous hypergeometric equations.  That motivates, but does not prove, the
remaining route: a genuinely chiral Teukolsky/helicity return determinant whose nonlinear
Einstein backreaction and Hawking horizon condition select one orientation.  Ordinary scalar
KMS/passivity and the shadow-even determinant cannot supply that step.

**[LITERATURE-FORMALIZED] [PAPER-PROVED] [LEAN-PROVED]** All definitions and zero/pole,
collision-exclusion, shadow, and bright-incidence statements below are unconditional.

**[OPEN CORE]** Derive the chiral return determinant and its phase-sensitive optical identity from
nonlinear Einstein--Klein--Gordon/Teukolsky evolution.  No such dynamical selector is assumed here.
-/


open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

def thetaCuspHawkingHypergeometricRadialA (omega z : ℂ) : ℂ :=
  3 / 4 - Complex.I *
    (omega - thetaCuspHawkingTopologicalBlackHoleAngularMomentum z) / 2

def thetaCuspHawkingHypergeometricRadialB (omega z : ℂ) : ℂ :=
  3 / 4 - Complex.I *
    (omega + thetaCuspHawkingTopologicalBlackHoleAngularMomentum z) / 2

def thetaCuspHawkingHypergeometricJostPlus (omega z : ℂ) : ℂ :=
  GaloisForLFunctions.reciprocalGammaEntire (thetaCuspHawkingHypergeometricRadialA omega z)

def thetaCuspHawkingHypergeometricJostMinus (omega z : ℂ) : ℂ :=
  GaloisForLFunctions.reciprocalGammaEntire (thetaCuspHawkingHypergeometricRadialB omega z)

def thetaCuspHawkingHypergeometricJost (omega z : ℂ) : ℂ :=
  thetaCuspHawkingHypergeometricJostPlus omega z * thetaCuspHawkingHypergeometricJostMinus omega z

def thetaCuspHawkingHypergeometricRadialC (omega : ℂ) : ℂ := 1 - Complex.I * omega

def thetaCuspHawkingHypergeometricPhysicalBoundaryJost (omega z : ℂ) : ℂ :=
  Complex.Gamma (thetaCuspHawkingHypergeometricRadialC omega) * Complex.Gamma (1 / 2 : ℂ) *
    thetaCuspHawkingHypergeometricJost omega z

def thetaCuspHawkingHypergeometricChiralJost (omega z : ℂ) : ℂ :=
  thetaCuspHawkingHypergeometricJostPlus omega z / thetaCuspHawkingHypergeometricJostMinus omega z

def thetaCuspHawkingHypergeometricGreenPlus (omega z : ℂ) : ℂ := (thetaCuspHawkingHypergeometricJostPlus omega z)⁻¹

def thetaCuspHawkingHypergeometricGreenMinus (omega z : ℂ) : ℂ := (thetaCuspHawkingHypergeometricJostMinus omega z)⁻¹

def thetaCuspHawkingHypergeometricGreen (omega z : ℂ) : ℂ := (thetaCuspHawkingHypergeometricJost omega z)⁻¹

def thetaCuspHawkingHypergeometricPhysicalBoundaryGreen (omega z : ℂ) : ℂ :=
  (thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega z)⁻¹

lemma thetaCuspHawkingHypergeometricRadialA_qnmPlus (n : ℕ) (z : ℂ) :
    thetaCuspHawkingHypergeometricRadialA (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z) z =
      -(n : ℂ) := by
  unfold thetaCuspHawkingHypergeometricRadialA thetaCuspHawkingTopologicalBlackHoleQNMPlus
  have hInegI : Complex.I * (-Complex.I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I]
    simp
  rw [show thetaCuspHawkingTopologicalBlackHoleAngularMomentum z -
      Complex.I * (thetaCuspHawkingTopologicalBlackHoleConformalDecay n : ℂ) -
      thetaCuspHawkingTopologicalBlackHoleAngularMomentum z =
        (-Complex.I) *
          (thetaCuspHawkingTopologicalBlackHoleConformalDecay n : ℂ) by ring]
  rw [← mul_assoc, hInegI, one_mul]
  unfold thetaCuspHawkingTopologicalBlackHoleConformalDecay
  push_cast
  ring

lemma thetaCuspHawkingHypergeometricRadialB_qnmMinus (n : ℕ) (z : ℂ) :
    thetaCuspHawkingHypergeometricRadialB (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z) z =
      -(n : ℂ) := by
  unfold thetaCuspHawkingHypergeometricRadialB thetaCuspHawkingTopologicalBlackHoleQNMMinus
  have hInegI : Complex.I * (-Complex.I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I]
    simp
  rw [show -thetaCuspHawkingTopologicalBlackHoleAngularMomentum z -
      Complex.I * (thetaCuspHawkingTopologicalBlackHoleConformalDecay n : ℂ) +
      thetaCuspHawkingTopologicalBlackHoleAngularMomentum z =
        (-Complex.I) *
          (thetaCuspHawkingTopologicalBlackHoleConformalDecay n : ℂ) by ring]
  rw [← mul_assoc, hInegI, one_mul]
  unfold thetaCuspHawkingTopologicalBlackHoleConformalDecay
  push_cast
  ring

lemma thetaCuspHawkingHypergeometricHasDerivAt_radialA (omega z : ℂ) :
    HasDerivAt (fun w : ℂ => thetaCuspHawkingHypergeometricRadialA w z) (-(Complex.I / 2)) omega := by
  unfold thetaCuspHawkingHypergeometricRadialA
  have hinner := (hasDerivAt_id omega).sub_const
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum z)
  have hmul := hinner.const_mul Complex.I
  have hdiv := hmul.div_const (2 : ℂ)
  simpa using HasDerivAt.const_sub (3 / 4 : ℂ) hdiv

lemma thetaCuspHawkingHypergeometricHasDerivAt_radialB (omega z : ℂ) :
    HasDerivAt (fun w : ℂ => thetaCuspHawkingHypergeometricRadialB w z) (-(Complex.I / 2)) omega := by
  unfold thetaCuspHawkingHypergeometricRadialB
  have hinner := (hasDerivAt_id omega).add_const
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum z)
  have hmul := hinner.const_mul Complex.I
  have hdiv := hmul.div_const (2 : ℂ)
  simpa using HasDerivAt.const_sub (3 / 4 : ℂ) hdiv

lemma thetaCuspHawkingHypergeometricHasDerivAt_jostPlus_qnm (n : ℕ) (z : ℂ) :
    HasDerivAt (fun omega : ℂ => thetaCuspHawkingHypergeometricJostPlus omega z)
      (((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (-(Complex.I / 2)))
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z) := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMPlus n z
  have hout : HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹)
      ((-1 : ℂ) ^ n * (n.factorial : ℂ)) (thetaCuspHawkingHypergeometricRadialA omega z) := by
    simpa [omega, thetaCuspHawkingHypergeometricRadialA_qnmPlus] using
      (GaloisForLFunctions.hasDerivAt_oneDivGamma_neg_nat n)
  change HasDerivAt
    ((fun w : ℂ => (Complex.Gamma w)⁻¹) ∘ fun w => thetaCuspHawkingHypergeometricRadialA w z)
      _ omega
  exact hout.comp omega (thetaCuspHawkingHypergeometricHasDerivAt_radialA omega z)

lemma thetaCuspHawkingHypergeometricHasDerivAt_jostMinus_qnm (n : ℕ) (z : ℂ) :
    HasDerivAt (fun omega : ℂ => thetaCuspHawkingHypergeometricJostMinus omega z)
      (((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (-(Complex.I / 2)))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z) := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMMinus n z
  have hout : HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹)
      ((-1 : ℂ) ^ n * (n.factorial : ℂ)) (thetaCuspHawkingHypergeometricRadialB omega z) := by
    simpa [omega, thetaCuspHawkingHypergeometricRadialB_qnmMinus] using
      (GaloisForLFunctions.hasDerivAt_oneDivGamma_neg_nat n)
  change HasDerivAt
    ((fun w : ℂ => (Complex.Gamma w)⁻¹) ∘ fun w => thetaCuspHawkingHypergeometricRadialB w z)
      _ omega
  exact hout.comp omega (thetaCuspHawkingHypergeometricHasDerivAt_radialB omega z)

lemma thetaCuspHawkingHypergeometricJostDerivative_ne_zero (n : ℕ) :
    (((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (-(Complex.I / 2))) ≠ 0 := by
  have hfac : (n.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero n (by norm_num)) hfac)
    (neg_ne_zero.mpr (div_ne_zero Complex.I_ne_zero (by norm_num)))

lemma thetaCuspHawkingHypergeometricJostPlus_qnm_zero (n : ℕ) (z : ℂ) :
    thetaCuspHawkingHypergeometricJostPlus (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z) z = 0 := by
  unfold thetaCuspHawkingHypergeometricJostPlus GaloisForLFunctions.reciprocalGammaEntire
  rw [thetaCuspHawkingHypergeometricRadialA_qnmPlus, Complex.Gamma_neg_nat_eq_zero]
  simp

lemma thetaCuspHawkingHypergeometricJostMinus_qnm_zero (n : ℕ) (z : ℂ) :
    thetaCuspHawkingHypergeometricJostMinus (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z) z = 0 := by
  unfold thetaCuspHawkingHypergeometricJostMinus GaloisForLFunctions.reciprocalGammaEntire
  rw [thetaCuspHawkingHypergeometricRadialB_qnmMinus, Complex.Gamma_neg_nat_eq_zero]
  simp

lemma thetaCuspHawkingHypergeometricRadialB_qnmPlus (n : ℕ) (z : ℂ) :
    thetaCuspHawkingHypergeometricRadialB (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z) z =
      -(n : ℂ) - Complex.I *
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum z := by
  unfold thetaCuspHawkingHypergeometricRadialB thetaCuspHawkingTopologicalBlackHoleQNMPlus
  have hInegI : Complex.I * (-Complex.I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I]
    simp
  rw [show thetaCuspHawkingTopologicalBlackHoleAngularMomentum z -
      Complex.I * (thetaCuspHawkingTopologicalBlackHoleConformalDecay n : ℂ) +
      thetaCuspHawkingTopologicalBlackHoleAngularMomentum z =
        2 * thetaCuspHawkingTopologicalBlackHoleAngularMomentum z +
          (-Complex.I) *
            (thetaCuspHawkingTopologicalBlackHoleConformalDecay n : ℂ) by ring]
  rw [mul_add, ← mul_assoc Complex.I (-Complex.I)
      (thetaCuspHawkingTopologicalBlackHoleConformalDecay n : ℂ),
    hInegI, one_mul]
  unfold thetaCuspHawkingTopologicalBlackHoleConformalDecay
  push_cast
  ring

lemma thetaCuspHawkingHypergeometricRadialA_qnmMinus (n : ℕ) (z : ℂ) :
    thetaCuspHawkingHypergeometricRadialA (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z) z =
      -(n : ℂ) + Complex.I *
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum z := by
  unfold thetaCuspHawkingHypergeometricRadialA thetaCuspHawkingTopologicalBlackHoleQNMMinus
  have hInegI : Complex.I * (-Complex.I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I]
    simp
  rw [show -thetaCuspHawkingTopologicalBlackHoleAngularMomentum z -
      Complex.I * (thetaCuspHawkingTopologicalBlackHoleConformalDecay n : ℂ) -
      thetaCuspHawkingTopologicalBlackHoleAngularMomentum z =
        -2 * thetaCuspHawkingTopologicalBlackHoleAngularMomentum z +
          (-Complex.I) *
            (thetaCuspHawkingTopologicalBlackHoleConformalDecay n : ℂ) by ring]
  rw [mul_add, ← mul_assoc Complex.I (-Complex.I)
      (thetaCuspHawkingTopologicalBlackHoleConformalDecay n : ℂ),
    hInegI, one_mul]
  unfold thetaCuspHawkingTopologicalBlackHoleConformalDecay
  push_cast
  ring

lemma thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero (q : XiZeroCopy) :
    (xiSpectralPoint q).re ≠ 0 := by
  intro hre
  have hz : xiSpectralPoint q =
      (((xiSpectralPoint q).im : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp [hre]
    · simp
  apply XiC_ne_zero_of_imaginary (xiSpectralPoint q).im
  rw [← hz]
  exact XiC_xiSpectralPoint_eq_zero q

lemma thetaCuspHawkingHypergeometricRadialB_qnmPlus_ne_neg_nat (n m : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingHypergeometricRadialB
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (xiSpectralPoint q) ≠ -(m : ℂ) := by
  rw [thetaCuspHawkingHypergeometricRadialB_qnmPlus]
  intro h
  have him := congrArg Complex.im h
  simp [thetaCuspHawkingTopologicalBlackHoleAngularMomentum] at him
  exact thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q (by linarith)

lemma thetaCuspHawkingHypergeometricRadialA_qnmMinus_ne_neg_nat (n m : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingHypergeometricRadialA
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q))
        (xiSpectralPoint q) ≠ -(m : ℂ) := by
  rw [thetaCuspHawkingHypergeometricRadialA_qnmMinus]
  intro h
  have him := congrArg Complex.im h
  simp [thetaCuspHawkingTopologicalBlackHoleAngularMomentum] at him
  exact thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q (by linarith)

lemma thetaCuspHawkingHypergeometricJostMinus_qnmPlus_ne_zero (n : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingHypergeometricJostMinus
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
      (xiSpectralPoint q) ≠ 0 := by
  unfold thetaCuspHawkingHypergeometricJostMinus GaloisForLFunctions.reciprocalGammaEntire
  exact inv_ne_zero (Complex.Gamma_ne_zero fun m =>
    thetaCuspHawkingHypergeometricRadialB_qnmPlus_ne_neg_nat n m q)

lemma thetaCuspHawkingHypergeometricJostPlus_qnmMinus_ne_zero (n : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingHypergeometricJostPlus
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q))
      (xiSpectralPoint q) ≠ 0 := by
  unfold thetaCuspHawkingHypergeometricJostPlus GaloisForLFunctions.reciprocalGammaEntire
  exact inv_ne_zero (Complex.Gamma_ne_zero fun m =>
    thetaCuspHawkingHypergeometricRadialA_qnmMinus_ne_neg_nat n m q)

lemma thetaCuspHawkingHypergeometricAnalyticAt_jostPlus (omega z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => thetaCuspHawkingHypergeometricJostPlus w z) omega := by
  have hGamma : AnalyticOnNhd ℂ GaloisForLFunctions.reciprocalGammaEntire Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact GaloisForLFunctions.contDiff_reciprocalGammaEntire.differentiable (by simp)
  unfold thetaCuspHawkingHypergeometricJostPlus
  exact (hGamma _ (Set.mem_univ _)).comp
    (by unfold thetaCuspHawkingHypergeometricRadialA; fun_prop :
      AnalyticAt ℂ (fun w : ℂ => thetaCuspHawkingHypergeometricRadialA w z) omega)

lemma thetaCuspHawkingHypergeometricAnalyticAt_jostMinus (omega z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => thetaCuspHawkingHypergeometricJostMinus w z) omega := by
  have hGamma : AnalyticOnNhd ℂ GaloisForLFunctions.reciprocalGammaEntire Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact GaloisForLFunctions.contDiff_reciprocalGammaEntire.differentiable (by simp)
  unfold thetaCuspHawkingHypergeometricJostMinus
  exact (hGamma _ (Set.mem_univ _)).comp
    (by unfold thetaCuspHawkingHypergeometricRadialB; fun_prop :
      AnalyticAt ℂ (fun w : ℂ => thetaCuspHawkingHypergeometricRadialB w z) omega)

theorem thetaCuspHawkingHypergeometricOrder_jostPlus_qnm (n : ℕ) (z : ℂ) :
    meromorphicOrderAt (fun omega : ℂ => thetaCuspHawkingHypergeometricJostPlus omega z)
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z) = (1 : ℤ) := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMPlus n z
  have hd := thetaCuspHawkingHypergeometricHasDerivAt_jostPlus_qnm n z
  have han := thetaCuspHawkingHypergeometricAnalyticAt_jostPlus omega z
  have hz : thetaCuspHawkingHypergeometricJostPlus omega z = 0 := by
    simpa [omega] using thetaCuspHawkingHypergeometricJostPlus_qnm_zero n z
  have hdn : deriv (fun w : ℂ => thetaCuspHawkingHypergeometricJostPlus w z) omega ≠ 0 := by
    rw [hd.deriv]
    exact thetaCuspHawkingHypergeometricJostDerivative_ne_zero n
  have ho : analyticOrderAt (fun w : ℂ => thetaCuspHawkingHypergeometricJostPlus w z) omega = 1 :=
    han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hdn
  rw [han.meromorphicOrderAt_eq, ho]
  rfl

theorem thetaCuspHawkingHypergeometricOrder_greenPlus_qnm (n : ℕ) (z : ℂ) :
    meromorphicOrderAt (fun omega : ℂ => thetaCuspHawkingHypergeometricGreenPlus omega z)
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z) = ((-1 : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt
    ((fun omega : ℂ => thetaCuspHawkingHypergeometricJostPlus omega z)⁻¹)
    (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z) = _
  rw [meromorphicOrderAt_inv, thetaCuspHawkingHypergeometricOrder_jostPlus_qnm]
  rfl

theorem thetaCuspHawkingHypergeometricOrder_jostMinus_qnm (n : ℕ) (z : ℂ) :
    meromorphicOrderAt (fun omega : ℂ => thetaCuspHawkingHypergeometricJostMinus omega z)
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z) = (1 : ℤ) := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMMinus n z
  have hd := thetaCuspHawkingHypergeometricHasDerivAt_jostMinus_qnm n z
  have han := thetaCuspHawkingHypergeometricAnalyticAt_jostMinus omega z
  have hz : thetaCuspHawkingHypergeometricJostMinus omega z = 0 := by
    simpa [omega] using thetaCuspHawkingHypergeometricJostMinus_qnm_zero n z
  have hdn : deriv (fun w : ℂ => thetaCuspHawkingHypergeometricJostMinus w z) omega ≠ 0 := by
    rw [hd.deriv]
    exact thetaCuspHawkingHypergeometricJostDerivative_ne_zero n
  have ho : analyticOrderAt (fun w : ℂ => thetaCuspHawkingHypergeometricJostMinus w z) omega = 1 :=
    han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hdn
  rw [han.meromorphicOrderAt_eq, ho]
  rfl

theorem thetaCuspHawkingHypergeometricOrder_greenMinus_qnm (n : ℕ) (z : ℂ) :
    meromorphicOrderAt (fun omega : ℂ => thetaCuspHawkingHypergeometricGreenMinus omega z)
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z) = ((-1 : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt
    ((fun omega : ℂ => thetaCuspHawkingHypergeometricJostMinus omega z)⁻¹)
    (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z) = _
  rw [meromorphicOrderAt_inv, thetaCuspHawkingHypergeometricOrder_jostMinus_qnm]
  rfl

lemma thetaCuspHawkingHypergeometricOrder_jostMinus_qnmPlus_xi (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt (fun omega : ℂ => thetaCuspHawkingHypergeometricJostMinus omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) = 0 := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)
  have han := thetaCuspHawkingHypergeometricAnalyticAt_jostMinus omega (xiSpectralPoint q)
  have hne : thetaCuspHawkingHypergeometricJostMinus omega (xiSpectralPoint q) ≠ 0 := by
    simpa [omega] using thetaCuspHawkingHypergeometricJostMinus_qnmPlus_ne_zero n q
  rw [han.meromorphicOrderAt_eq, (han.analyticOrderAt_eq_zero).mpr hne]
  rfl

lemma thetaCuspHawkingHypergeometricOrder_jostPlus_qnmMinus_xi (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt (fun omega : ℂ => thetaCuspHawkingHypergeometricJostPlus omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) = 0 := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)
  have han := thetaCuspHawkingHypergeometricAnalyticAt_jostPlus omega (xiSpectralPoint q)
  have hne : thetaCuspHawkingHypergeometricJostPlus omega (xiSpectralPoint q) ≠ 0 := by
    simpa [omega] using thetaCuspHawkingHypergeometricJostPlus_qnmMinus_ne_zero n q
  rw [han.meromorphicOrderAt_eq, (han.analyticOrderAt_eq_zero).mpr hne]
  rfl

theorem thetaCuspHawkingHypergeometricOrder_fullJost_qnmPlus_xi (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt (fun omega : ℂ => thetaCuspHawkingHypergeometricJost omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) = (1 : ℤ) := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)
  have hp := (thetaCuspHawkingHypergeometricAnalyticAt_jostPlus omega (xiSpectralPoint q)).meromorphicAt
  have hm := (thetaCuspHawkingHypergeometricAnalyticAt_jostMinus omega (xiSpectralPoint q)).meromorphicAt
  change meromorphicOrderAt
    ((fun w : ℂ => thetaCuspHawkingHypergeometricJostPlus w (xiSpectralPoint q)) *
      (fun w : ℂ => thetaCuspHawkingHypergeometricJostMinus w (xiSpectralPoint q))) omega = _
  rw [meromorphicOrderAt_mul hp hm, thetaCuspHawkingHypergeometricOrder_jostPlus_qnm,
    thetaCuspHawkingHypergeometricOrder_jostMinus_qnmPlus_xi]
  rfl

theorem thetaCuspHawkingHypergeometricOrder_fullGreen_qnmPlus_xi (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt (fun omega : ℂ => thetaCuspHawkingHypergeometricGreen omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) =
        ((-1 : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt
    ((fun omega : ℂ => thetaCuspHawkingHypergeometricJost omega (xiSpectralPoint q))⁻¹) _ = _
  rw [meromorphicOrderAt_inv, thetaCuspHawkingHypergeometricOrder_fullJost_qnmPlus_xi]
  rfl

theorem thetaCuspHawkingHypergeometricOrder_fullJost_qnmMinus_xi (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt (fun omega : ℂ => thetaCuspHawkingHypergeometricJost omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) = (1 : ℤ) := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)
  have hp := (thetaCuspHawkingHypergeometricAnalyticAt_jostPlus omega (xiSpectralPoint q)).meromorphicAt
  have hm := (thetaCuspHawkingHypergeometricAnalyticAt_jostMinus omega (xiSpectralPoint q)).meromorphicAt
  change meromorphicOrderAt
    ((fun w : ℂ => thetaCuspHawkingHypergeometricJostPlus w (xiSpectralPoint q)) *
      (fun w : ℂ => thetaCuspHawkingHypergeometricJostMinus w (xiSpectralPoint q))) omega = _
  rw [meromorphicOrderAt_mul hp hm, thetaCuspHawkingHypergeometricOrder_jostPlus_qnmMinus_xi,
    thetaCuspHawkingHypergeometricOrder_jostMinus_qnm]
  rfl

theorem thetaCuspHawkingHypergeometricOrder_fullGreen_qnmMinus_xi (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt (fun omega : ℂ => thetaCuspHawkingHypergeometricGreen omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) =
        ((-1 : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt
    ((fun omega : ℂ => thetaCuspHawkingHypergeometricJost omega (xiSpectralPoint q))⁻¹) _ = _
  rw [meromorphicOrderAt_inv, thetaCuspHawkingHypergeometricOrder_fullJost_qnmMinus_xi]
  rfl

lemma thetaCuspHawkingHypergeometricRadialC_qnmPlus_ne_neg_nat (n m : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingHypergeometricRadialC
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) ≠
      -(m : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp [thetaCuspHawkingHypergeometricRadialC, thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum] at him
  exact thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q (by linarith)

lemma thetaCuspHawkingHypergeometricRadialC_qnmMinus_ne_neg_nat (n m : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingHypergeometricRadialC
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) ≠
      -(m : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp [thetaCuspHawkingHypergeometricRadialC, thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum] at him
  exact thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q (by linarith)

lemma thetaCuspHawkingHypergeometricAnalyticAt_gammaRadialC_of_ne_neg_nat (omega : ℂ)
    (hnot : ∀ m : ℕ, thetaCuspHawkingHypergeometricRadialC omega ≠ -(m : ℂ)) :
    AnalyticAt ℂ (fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w)) omega := by
  have hmer : MeromorphicAt (fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w)) omega := by
    simpa only [Function.comp_def] using
      (Meromorphic.Gamma (thetaCuspHawkingHypergeometricRadialC omega)).comp_analyticAt
        (x := omega) (g := thetaCuspHawkingHypergeometricRadialC)
        (by unfold thetaCuspHawkingHypergeometricRadialC; fun_prop)
  have hcont : ContinuousAt (fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w)) omega := by
    have hinner : ContinuousAt thetaCuspHawkingHypergeometricRadialC omega := by
      unfold thetaCuspHawkingHypergeometricRadialC
      fun_prop
    simpa only [Function.comp_def] using
      ContinuousAt.comp (g := Complex.Gamma) (f := thetaCuspHawkingHypergeometricRadialC) (x := omega)
        (continuousAt_Gamma _ hnot) hinner
  exact hmer.analyticAt hcont

lemma thetaCuspHawkingHypergeometricGamma_half_ne_zero : Complex.Gamma (1 / 2 : ℂ) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

lemma thetaCuspHawkingHypergeometricPhysicalGammaPrefactor_order_qnmPlus_xi (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC omega) *
        Complex.Gamma (1 / 2 : ℂ))
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) = 0 := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)
  have hanC := thetaCuspHawkingHypergeometricAnalyticAt_gammaRadialC_of_ne_neg_nat omega
    (thetaCuspHawkingHypergeometricRadialC_qnmPlus_ne_neg_nat n · q)
  have han : AnalyticAt ℂ
      (fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) * Complex.Gamma (1 / 2 : ℂ))
      omega := hanC.mul analyticAt_const
  have hne : Complex.Gamma (thetaCuspHawkingHypergeometricRadialC omega) * Complex.Gamma (1 / 2 : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.Gamma_ne_zero (thetaCuspHawkingHypergeometricRadialC_qnmPlus_ne_neg_nat n · q))
      thetaCuspHawkingHypergeometricGamma_half_ne_zero
  rw [han.meromorphicOrderAt_eq, (han.analyticOrderAt_eq_zero).mpr hne]
  rfl

lemma thetaCuspHawkingHypergeometricPhysicalGammaPrefactor_order_qnmMinus_xi (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC omega) *
        Complex.Gamma (1 / 2 : ℂ))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) = 0 := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)
  have hanC := thetaCuspHawkingHypergeometricAnalyticAt_gammaRadialC_of_ne_neg_nat omega
    (thetaCuspHawkingHypergeometricRadialC_qnmMinus_ne_neg_nat n · q)
  have han : AnalyticAt ℂ
      (fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) * Complex.Gamma (1 / 2 : ℂ))
      omega := hanC.mul analyticAt_const
  have hne : Complex.Gamma (thetaCuspHawkingHypergeometricRadialC omega) * Complex.Gamma (1 / 2 : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.Gamma_ne_zero (thetaCuspHawkingHypergeometricRadialC_qnmMinus_ne_neg_nat n · q))
      thetaCuspHawkingHypergeometricGamma_half_ne_zero
  rw [han.meromorphicOrderAt_eq, (han.analyticOrderAt_eq_zero).mpr hne]
  rfl

theorem thetaCuspHawkingHypergeometricPhysicalBoundaryJost_order_qnmPlus_xi (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) = (1 : ℤ) := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)
  have hpref : MeromorphicAt
      (fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) * Complex.Gamma (1 / 2 : ℂ))
      omega := (thetaCuspHawkingHypergeometricAnalyticAt_gammaRadialC_of_ne_neg_nat omega
        (thetaCuspHawkingHypergeometricRadialC_qnmPlus_ne_neg_nat n · q) |>.mul analyticAt_const).meromorphicAt
  have hJost : MeromorphicAt (fun w : ℂ => thetaCuspHawkingHypergeometricJost w (xiSpectralPoint q)) omega :=
    ((thetaCuspHawkingHypergeometricAnalyticAt_jostPlus omega (xiSpectralPoint q)).mul
      (thetaCuspHawkingHypergeometricAnalyticAt_jostMinus omega (xiSpectralPoint q))).meromorphicAt
  change meromorphicOrderAt
    ((fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) * Complex.Gamma (1 / 2 : ℂ)) *
      (fun w : ℂ => thetaCuspHawkingHypergeometricJost w (xiSpectralPoint q))) omega = _
  rw [meromorphicOrderAt_mul hpref hJost,
    thetaCuspHawkingHypergeometricPhysicalGammaPrefactor_order_qnmPlus_xi,
    thetaCuspHawkingHypergeometricOrder_fullJost_qnmPlus_xi]
  rfl

theorem thetaCuspHawkingHypergeometricPhysicalBoundaryGreen_order_qnmPlus_xi (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryGreen omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) =
        ((-1 : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt
    ((fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega (xiSpectralPoint q))⁻¹) _ = _
  rw [meromorphicOrderAt_inv, thetaCuspHawkingHypergeometricPhysicalBoundaryJost_order_qnmPlus_xi]
  rfl

theorem thetaCuspHawkingHypergeometricPhysicalBoundaryJost_order_qnmMinus_xi (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) = (1 : ℤ) := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)
  have hpref : MeromorphicAt
      (fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) * Complex.Gamma (1 / 2 : ℂ))
      omega := (thetaCuspHawkingHypergeometricAnalyticAt_gammaRadialC_of_ne_neg_nat omega
        (thetaCuspHawkingHypergeometricRadialC_qnmMinus_ne_neg_nat n · q) |>.mul analyticAt_const).meromorphicAt
  have hJost : MeromorphicAt (fun w : ℂ => thetaCuspHawkingHypergeometricJost w (xiSpectralPoint q)) omega :=
    ((thetaCuspHawkingHypergeometricAnalyticAt_jostPlus omega (xiSpectralPoint q)).mul
      (thetaCuspHawkingHypergeometricAnalyticAt_jostMinus omega (xiSpectralPoint q))).meromorphicAt
  change meromorphicOrderAt
    ((fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) * Complex.Gamma (1 / 2 : ℂ)) *
      (fun w : ℂ => thetaCuspHawkingHypergeometricJost w (xiSpectralPoint q))) omega = _
  rw [meromorphicOrderAt_mul hpref hJost,
    thetaCuspHawkingHypergeometricPhysicalGammaPrefactor_order_qnmMinus_xi,
    thetaCuspHawkingHypergeometricOrder_fullJost_qnmMinus_xi]
  rfl

theorem thetaCuspHawkingHypergeometricPhysicalBoundaryGreen_order_qnmMinus_xi (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryGreen omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) =
        ((-1 : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt
    ((fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega (xiSpectralPoint q))⁻¹) _ = _
  rw [meromorphicOrderAt_inv, thetaCuspHawkingHypergeometricPhysicalBoundaryJost_order_qnmMinus_xi]
  rfl

lemma thetaCuspHawkingHypergeometricRadialA_shadow (omega z : ℂ) :
    thetaCuspHawkingHypergeometricRadialA omega (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingHypergeometricRadialB omega z := by
  unfold thetaCuspHawkingHypergeometricRadialA thetaCuspHawkingHypergeometricRadialB
  rw [thetaCuspHawkingTopologicalBlackHoleAngularMomentum_shadow]
  ring

lemma thetaCuspHawkingHypergeometricRadialB_shadow (omega z : ℂ) :
    thetaCuspHawkingHypergeometricRadialB omega (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingHypergeometricRadialA omega z := by
  unfold thetaCuspHawkingHypergeometricRadialA thetaCuspHawkingHypergeometricRadialB
  rw [thetaCuspHawkingTopologicalBlackHoleAngularMomentum_shadow]
  ring

lemma thetaCuspHawkingHypergeometricJostPlus_shadow (omega z : ℂ) :
    thetaCuspHawkingHypergeometricJostPlus omega (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingHypergeometricJostMinus omega z := by
  simp [thetaCuspHawkingHypergeometricJostPlus, thetaCuspHawkingHypergeometricJostMinus, thetaCuspHawkingHypergeometricRadialA_shadow]

lemma thetaCuspHawkingHypergeometricJostMinus_shadow (omega z : ℂ) :
    thetaCuspHawkingHypergeometricJostMinus omega (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingHypergeometricJostPlus omega z := by
  simp [thetaCuspHawkingHypergeometricJostPlus, thetaCuspHawkingHypergeometricJostMinus, thetaCuspHawkingHypergeometricRadialB_shadow]

theorem thetaCuspHawkingHypergeometricJost_shadow (omega z : ℂ) :
    thetaCuspHawkingHypergeometricJost omega (thetaCuspHawkingOpticalCuspShadow z) = thetaCuspHawkingHypergeometricJost omega z := by
  rw [thetaCuspHawkingHypergeometricJost, thetaCuspHawkingHypergeometricJost, thetaCuspHawkingHypergeometricJostPlus_shadow, thetaCuspHawkingHypergeometricJostMinus_shadow, mul_comm]

theorem thetaCuspHawkingHypergeometricPhysicalBoundaryJost_shadow (omega z : ℂ) :
    thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega z := by
  rw [thetaCuspHawkingHypergeometricPhysicalBoundaryJost, thetaCuspHawkingHypergeometricPhysicalBoundaryJost, thetaCuspHawkingHypergeometricJost_shadow]

theorem thetaCuspHawkingHypergeometricChiralJost_shadow (omega z : ℂ) :
    thetaCuspHawkingHypergeometricChiralJost omega (thetaCuspHawkingOpticalCuspShadow z) =
      (thetaCuspHawkingHypergeometricChiralJost omega z)⁻¹ := by
  rw [thetaCuspHawkingHypergeometricChiralJost, thetaCuspHawkingHypergeometricChiralJost, thetaCuspHawkingHypergeometricJostPlus_shadow, thetaCuspHawkingHypergeometricJostMinus_shadow,
    inv_div]

theorem thetaCuspHawkingHypergeometricXiDivisor_physicalJost_pole_bright_incidence
    (n : ℕ) (q : XiZeroCopy) (t : ℝ) :
    meromorphicOrderAt
        (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega (xiSpectralPoint q))
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) = (1 : ℤ) ∧
      meromorphicOrderAt
        (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryGreen omega (xiSpectralPoint q))
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) =
          ((-1 : ℤ) : WithTop ℤ) ∧
      meromorphicOrderAt
        (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega (xiSpectralPoint q))
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) = (1 : ℤ) ∧
      meromorphicOrderAt
        (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryGreen omega (xiSpectralPoint q))
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) =
          ((-1 : ℤ) : WithTop ℤ) ∧
      (∀ omega : ℂ,
        thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega
            (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) =
          thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega (xiSpectralPoint q)) ∧
      (∀ omega : ℂ,
        thetaCuspHawkingHypergeometricChiralJost omega
            (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) =
          (thetaCuspHawkingHypergeometricChiralJost omega (xiSpectralPoint q))⁻¹) ∧
      ∃ r : ℝ,
        thetaCuspHawkingCompletedEisensteinPhysicalVertex (xiSpectralPoint q) r t ≠ 0 ∧
        thetaCuspHawkingCompletedEisensteinPhysicalVertex
          (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) r t ≠ 0 := by
  refine ⟨thetaCuspHawkingHypergeometricPhysicalBoundaryJost_order_qnmPlus_xi n q,
    thetaCuspHawkingHypergeometricPhysicalBoundaryGreen_order_qnmPlus_xi n q,
    thetaCuspHawkingHypergeometricPhysicalBoundaryJost_order_qnmMinus_xi n q,
    thetaCuspHawkingHypergeometricPhysicalBoundaryGreen_order_qnmMinus_xi n q,
    (fun omega => thetaCuspHawkingHypergeometricPhysicalBoundaryJost_shadow omega (xiSpectralPoint q)),
    (fun omega => thetaCuspHawkingHypergeometricChiralJost_shadow omega (xiSpectralPoint q)), ?_⟩
  exact (thetaCuspHawkingXiDivisor_pole_shadowZero_brightCompletedEisensteinVertex q t).2.2

end

end RHTower

