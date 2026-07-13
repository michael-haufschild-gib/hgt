import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.XiHedenmalmValueConstraint
import GaloisForLFunctions.RHTower.XiHurwitzOrientationCauchyClosure

/-!
# The first RH ladder collides with Hedenmalm simplicity

Every positive RH-ladder rung forces the analytic order of each right-half Xi zero to be even.
The Hedenmalm value and density interfaces independently force every centered Xi zero to be
simple.  The affine centered-coordinate change preserves analytic order, so the two constraints
cannot coexist at a right-half zero.

This gives a short top-down chain from either of the existing Hedenmalm simplicity interfaces and
one positive ladder rung to RH.  No Hermite--Biehler sign, zero-free Hedenmalm function, or common
Kummer root is required.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- **Ladder--simplicity collision.**  Any positive RH-ladder rung together with simplicity of
the centered Xi divisor excludes every right-half Xi zero and forces RH. -/
theorem riemannHypothesis_of_rhLadder_of_xiZerosSimple
    {k : ℕ} (hk : 1 ≤ k) (hladder : RHLadder k)
    (hsimple : XiZerosSimple) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hfirst : RHLadder 1 := rhLadder_imp_one hk hladder
  have heven : Even (analyticOrderAt xi rho).toNat :=
    rhLadder_one_iff_even_order.mp hfirst rho hrho hzero
  let z : ℂ := (rho - 1 / 2) * (-I)
  let g : ℂ → ℂ := fun w => 1 / 2 + w * I
  have hgz : g z = rho := by
    dsimp only [g, z]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have hXiZero : XiC z = 0 := by
    change xi (g z) = 0
    rw [hgz]
    exact hzero
  have hXiOrder : analyticOrderAt XiC z = (1 : ℕ) :=
    (XiC_analytic z (Set.mem_univ z)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      hXiZero (hsimple hXiZero)
  have hg_an : AnalyticAt ℂ g z := by
    dsimp only [g]
    fun_prop
  have hg_deriv : deriv g z ≠ 0 := by
    have hg' : HasDerivAt g I z := by
      dsimp only [g]
      convert (hasDerivAt_const (x := z) (c := (1 / 2 : ℂ))).add
        ((hasDerivAt_id z).mul_const I) using 1
      ring
    rw [hg'.deriv]
    exact I_ne_zero
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := xi) hg_an hg_deriv
  have horder : analyticOrderAt xi rho = (1 : ℕ) := by
    rw [← hgz, ← hcomp]
    exact hXiOrder
  have htoNat : (analyticOrderAt xi rho).toNat = 1 := by
    rw [horder]
    rfl
  rw [htoNat] at heven
  obtain ⟨n, hn⟩ := heven
  omega

/-- The first ladder rung and Xi simplicity are already sufficient; the cofinal ladder is not
needed. -/
theorem riemannHypothesis_of_rhLadder_one_of_xiZerosSimple
    (hladder : RHLadder 1) (hsimple : XiZerosSimple) :
    RiemannHypothesis :=
  riemannHypothesis_of_rhLadder_of_xiZerosSimple (k := 1) le_rfl hladder hsimple

/-- **Static Hedenmalm-value chain to RH.**  Nonvanishing of the first removable Hedenmalm
quotient at every Xi divisor point supplies simplicity; one positive ladder rung then forces RH. -/
theorem riemannHypothesis_of_rhLadder_of_xiThetaFirstQuotientValueConstraint
    {k : ℕ} (hk : 1 ≤ k) (hladder : RHLadder k)
    (hvalue : XiThetaFirstQuotientValueConstraint) :
    RiemannHypothesis :=
  riemannHypothesis_of_rhLadder_of_xiZerosSimple hk hladder
    (xiThetaFirstQuotientValueConstraint_iff_simple.mp hvalue)

/-- **Hedenmalm-density chain to RH.**  Density of the theta evaluation span supplies simplicity;
one positive ladder rung then forces RH. -/
theorem riemannHypothesis_of_rhLadder_of_xiThetaEigenAlgebraicSubspace_dense
    {k : ℕ} (hk : 1 ≤ k) (hladder : RHLadder k)
    (hdense : Dense (xiThetaEigenAlgebraicSubspace :
      Set (lp (fun _ : XiZeroCopy => ℂ) 2))) :
    RiemannHypothesis :=
  riemannHypothesis_of_rhLadder_of_xiZerosSimple hk hladder
    (xiThetaEigenAlgebraicSubspace_dense_iff_simple.mp hdense)

/-! ## A source-to-source closure relation -/

/-- Every vector reconstructed by the analytically continued prime--Gamma Cauchy source core also
lies in the Hilbert closure of the Hedenmalm theta evaluation span. -/
def XiContinuedCauchyToHedenmalmClosure : Prop :=
  xiWeilContinuedCauchyHilbertSubspace ≤
    xiThetaEigenAlgebraicSubspace.topologicalClosure

/-- The Cauchy-to-Hedenmalm closure inclusion is exactly the missing multiplicity interface.  The
continued Cauchy core unconditionally contains the indicator of every complete Xi multiplicity
fiber.  At a multiple zero the entire Hedenmalm span lies in the coordinate hyperplane killing
that fiber, so the inclusion is impossible.  Conversely simplicity makes the Hedenmalm closure
the whole carrier. -/
theorem xiContinuedCauchyToHedenmalmClosure_iff_simple :
    XiContinuedCauchyToHedenmalmClosure ↔ XiZerosSimple := by
  constructor
  · intro hbridge alpha halpha
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy alpha).mp halpha
    intro hderiv
    have hderivq : deriv XiC (xiSpectralPoint q) = 0 := by
      simpa only [hq] using hderiv
    have hthetaLe :=
      xiThetaEigenAlgebraicSubspace_le_coordinateZero_of_deriv_eq_zero q hderivq
    have hthetaClosureLe : xiThetaEigenAlgebraicSubspace.topologicalClosure ≤
        xiCoordinateZeroSubspace q :=
      xiThetaEigenAlgebraicSubspace.topologicalClosure_minimal hthetaLe
        (xiCoordinateZeroSubspace_isClosed q)
    have hfiberCauchy : xiWeilFiberIndicatorLp (xiSpectralPoint q) ∈
        xiWeilContinuedCauchyHilbertSubspace :=
      xiWeilFiberIndicatorLp_mem_continuedCauchyHilbertSubspace q
    have hfiberTheta : xiWeilFiberIndicatorLp (xiSpectralPoint q) ∈
        xiThetaEigenAlgebraicSubspace.topologicalClosure := hbridge hfiberCauchy
    have hcoord := hthetaClosureLe hfiberTheta
    change xiWeilFiberIndicatorLp (xiSpectralPoint q) q = 0 at hcoord
    simp at hcoord
  · intro hsimple _ _
    rw [xiThetaEigenHilbertClosure_eq_top_of_simple hsimple]
    exact Submodule.mem_top

/-- **Cauchy--Hedenmalm value-relation chain to RH.**  A source-to-source closure inclusion plus
one positive RH-ladder rung forces RH. -/
theorem riemannHypothesis_of_rhLadder_of_xiContinuedCauchyToHedenmalmClosure
    {k : ℕ} (hk : 1 ≤ k) (hladder : RHLadder k)
    (hbridge : XiContinuedCauchyToHedenmalmClosure) :
    RiemannHypothesis :=
  riemannHypothesis_of_rhLadder_of_xiZerosSimple hk hladder
    (xiContinuedCauchyToHedenmalmClosure_iff_simple.mp hbridge)

end

end RHTower
