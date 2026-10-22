import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAnalyticBackreactionDoubletStability
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAllOrderTriangularQNMClockRenormalizationNoGo
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch
import GaloisForLFunctions.HTGeometry.ProductSliceSpecialization

/-!
# Analytic nontriangular BM resonance-collision no-go

The all-order triangular QNM hierarchy can absorb the literal mixed-Casimir source by moving its
simple QNM clock.  Its sharp survivor was a genuinely nontriangular resonance collision.  This
module closes that escape in the analytic weak-coupling germ of the actual Birmingham--Mokhtari
boundary problem.

For an arbitrary analytic quadratic-and-higher backreaction, the exact returned Jost relation has
nonzero spectral derivative at zero coupling because its zeroth-order term is the physical BM
Jost function and every Xi descendant is a simple zero.  Holomorphic implicit-function uniqueness
then proves more than existence: every merely continuous pole branch through that QNM is the same
germ.  Hence no analytic completion can split the QNM into two distinct continuous branches at the
perturbative origin.  Existing doublet stability also keeps the two off-wall FE--Schwarz partners
distinct near zero coupling.

Combined with the all-order triangular no-go, this kills every analytic perturbative realization
of the proposed nontriangular pole-collision escape.  A survivor must be nonanalytic at zero
coupling, occur outside the weak-coupling germ, or supply the independent physical Ward sign.

`[NEW] [HB ROUTE KILL] [ANALYTIC BACKREACTION] [POLE-GERM UNIQUENESS] [LEAN-PROVED]`
-/

open Complex Set Filter Topology Function

namespace RHTower

noncomputable section

/-- A continuous root germ of the exact all-order returned BM Jost relation through its specified
Xi QNM at zero coupling. -/
def D4BMXiGaugeFixedTotalPeriodAllOrderContinuousPoleGermMinus
    (higher : ℂ × ℂ → ℂ)
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy)
    (pole : ℂ → ℂ) : Prop :=
  ContinuousAt pole 0 ∧
    pole 0 =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q) ∧
    ∀ᶠ coupling : ℂ in 𝓝 0,
      d4BMXiGaugeFixedTotalPeriodAllOrderReturnedJostMinus higher
        n k conservativeFinitePart amplitude orthogonalMixing q
        coupling (pole coupling) = 0

/-- A nontrivial pole-germ collision would be two distinct continuous branches through the same
BM QNM and solving the same analytic all-order returned Jost relation. -/
def D4BMXiGaugeFixedTotalPeriodAllOrderNontrivialPoleGermCollisionMinus
    (higher : ℂ × ℂ → ℂ)
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) : Prop :=
  ∃ pole₁ pole₂ : ℂ → ℂ,
    D4BMXiGaugeFixedTotalPeriodAllOrderContinuousPoleGermMinus higher
      n k N conservativeFinitePart amplitude orthogonalMixing q pole₁ ∧
    D4BMXiGaugeFixedTotalPeriodAllOrderContinuousPoleGermMinus higher
      n k N conservativeFinitePart amplitude orthogonalMixing q pole₂ ∧
    ¬ (pole₁ =ᶠ[𝓝 0] pole₂)

private theorem d4HBExistsUniqueAnalyticPoleBranch
    {F : ℂ × ℂ → ℂ} {target d : ℂ}
    (hF : AnalyticAt ℂ F (0, target))
    (hF0 : F (0, target) = 0)
    (hpartial : HasDerivAt (fun omega => F (0, omega)) d target)
    (hd : d ≠ 0) :
    ∃ pole : ℂ → ℂ,
      AnalyticAt ℂ pole 0 ∧ pole 0 = target ∧
      (∀ᶠ coupling : ℂ in 𝓝 0, F (coupling, pole coupling) = 0) ∧
      ∀ candidate : ℂ → ℂ, ContinuousAt candidate 0 → candidate 0 = target →
        (∀ᶠ coupling : ℂ in 𝓝 0, F (coupling, candidate coupling) = 0) →
        pole =ᶠ[𝓝 0] candidate := by
  have hdir := GaloisForLFunctions.HTGeometry.dirFderiv_slice
    (E := ℂ) (F := ℂ) (f := F) (z₁ := (0 : ℂ)) (w := target) (1 : ℂ)
      hF.differentiableAt
  have hleft :
      GaloisForLFunctions.HTGeometry.dirFderiv (1 : ℂ)
          (fun omega : ℂ => F (0, omega)) target = d := by
    rw [GaloisForLFunctions.HTGeometry.dirFderiv_apply,
      hpartial.hasFDerivAt.fderiv]
    simp
  have hfw : (fderiv ℂ F (0, target)) ((0 : ℂ), (1 : ℂ)) ≠ 0 := by
    rw [← GaloisForLFunctions.HTGeometry.dirFderiv_apply]
    rw [← hdir, hleft]
    exact hd
  exact GaloisForLFunctions.HTGeometry.parametric_holo_implicit_unique
    hF hF0 hfw

/-- The actual all-order returned BM Jost relation has one and only one continuous pole germ
through every Xi QNM.  The canonical germ is analytic; competing germs need only be continuous. -/
theorem exists_unique_d4BMXiGaugeFixedTotalPeriodAllOrderReturnedJostPoleGermMinus
    (higher : ℂ × ℂ → ℂ)
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hhigher : AnalyticAt ℂ higher
      (0, thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q))) :
    ∃ pole : ℂ → ℂ,
      AnalyticAt ℂ pole 0 ∧
      D4BMXiGaugeFixedTotalPeriodAllOrderContinuousPoleGermMinus higher
        n k N conservativeFinitePart amplitude orthogonalMixing q pole ∧
      ∀ candidate : ℂ → ℂ,
        D4BMXiGaugeFixedTotalPeriodAllOrderContinuousPoleGermMinus higher
          n k N conservativeFinitePart amplitude orthogonalMixing q candidate →
        pole =ᶠ[𝓝 0] candidate := by
  let target := thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)
  let source := d4BMCausalPlusPlusMinusFrequency n k
    (d4BMXiMixedHorizonAngularMomentum q)
  let D : ℂ → ℂ := fun omega =>
    d4GravitationalHypergeometricBoundaryJost omega (xiSpectralPoint q)
  let K : ℂ → ℂ := fun omega =>
    d4BMXiGaugeFixedTotalPeriodTargetNumeratorMinus
      n k conservativeFinitePart amplitude orthogonalMixing q omega
  let F : ℂ × ℂ → ℂ := fun p =>
    D p.2 + p.1 * K p.2 + p.1 ^ (2 : ℕ) * higher p
  have htarget : target =
      d4BMCausalQNMMinus N (d4BMXiMixedHorizonAngularMomentum q) := by
    exact (d4BMXiCausalQNMMinus_eq_topologicalBlackHoleQNMMinus N q).symm
  have hfreq : target - source ≠ 0 := by
    rw [htarget]
    exact sub_ne_zero.mpr
      (d4BMCausalPlusPlusMinusFrequency_ne_qnmMinus_of_re_ne_zero n k N _
        (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)).symm
  have hDder : HasDerivAt D
      (d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus
        N (xiSpectralPoint q)) target := by
    simpa [D, target] using
      d4FundamentalQNMCrossBranchBoundaryJost_hasDerivAt_qnmMinus_xi N q
  have hD : AnalyticAt ℂ D target := by
    dsimp [D]
    unfold d4GravitationalHypergeometricBoundaryJost
      thetaCuspHawkingHypergeometricPhysicalBoundaryJost
      thetaCuspHawkingHypergeometricJost
    exact (((thetaCuspHawkingHypergeometricAnalyticAt_gammaRadialC_of_ne_neg_nat
      target (thetaCuspHawkingHypergeometricRadialC_qnmMinus_ne_neg_nat N · q)).mul
        analyticAt_const).mul
      ((thetaCuspHawkingHypergeometricAnalyticAt_jostPlus
        target (xiSpectralPoint q)).mul
        (thetaCuspHawkingHypergeometricAnalyticAt_jostMinus
          target (xiSpectralPoint q))))
  have hK : AnalyticAt ℂ K target := by
    dsimp [K, d4BMXiGaugeFixedTotalPeriodTargetNumeratorMinus]
    exact ((analyticAt_const.div
      (analyticAt_id.sub analyticAt_const) hfreq).mul analyticAt_const)
  have hF : AnalyticAt ℂ F (0, target) := by
    have hfst : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (0, target) := analyticAt_fst
    have hsnd : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (0, target) := analyticAt_snd
    exact (hD.comp (x := (0, target)) hsnd).add
      (hfst.mul (hK.comp (x := (0, target)) hsnd)) |>.add
      ((hfst.pow 2).mul (by simpa [target] using hhigher))
  have hD0 : D target = 0 := by
    simp [D, target, d4GravitationalHypergeometricBoundaryJost,
      thetaCuspHawkingHypergeometricPhysicalBoundaryJost,
      thetaCuspHawkingHypergeometricJost,
      thetaCuspHawkingHypergeometricJostMinus_qnm_zero]
  have hF0 : F (0, target) = 0 := by
    simp [F, hD0]
  have hpartial : HasDerivAt (fun omega => F (0, omega))
      (d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus
        N (xiSpectralPoint q)) target := by
    simpa [F] using hDder
  have hsimple :
      d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus
        N (xiSpectralPoint q) ≠ 0 :=
    d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus_xi_ne_zero N q
  obtain ⟨pole, hpole, hpole0, hroot, hunique⟩ :=
    d4HBExistsUniqueAnalyticPoleBranch hF hF0 hpartial hsimple
  refine ⟨pole, hpole, ?_, ?_⟩
  · refine ⟨hpole.continuousAt, hpole0, ?_⟩
    filter_upwards [hroot] with coupling hcoupling
    simpa [F, D, K, d4BMXiGaugeFixedTotalPeriodAllOrderReturnedJostMinus,
      d4BMXiGaugeFixedTotalPeriodReturnedJostMinus] using hcoupling
  · intro candidate hcandidate
    rcases hcandidate with ⟨hcandidateContinuous, hcandidate0, hcandidateRoot⟩
    apply hunique candidate hcandidateContinuous hcandidate0
    filter_upwards [hcandidateRoot] with coupling hcoupling
    simpa [F, D, K, d4BMXiGaugeFixedTotalPeriodAllOrderReturnedJostMinus,
      d4BMXiGaugeFixedTotalPeriodReturnedJostMinus] using hcoupling

/-- No analytic quadratic-and-higher completion can produce a nontrivial continuous branch split
at the perturbative BM QNM. -/
theorem not_d4BMXiGaugeFixedTotalPeriodAllOrderNontrivialPoleGermCollisionMinus
    (higher : ℂ × ℂ → ℂ)
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hhigher : AnalyticAt ℂ higher
      (0, thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q))) :
    ¬ D4BMXiGaugeFixedTotalPeriodAllOrderNontrivialPoleGermCollisionMinus higher
      n k N conservativeFinitePart amplitude orthogonalMixing q := by
  obtain ⟨canonical, _, _, hunique⟩ :=
    exists_unique_d4BMXiGaugeFixedTotalPeriodAllOrderReturnedJostPoleGermMinus
      higher n k N conservativeFinitePart amplitude orthogonalMixing q hhigher
  rintro ⟨pole₁, pole₂, hpole₁, hpole₂, hdistinct⟩
  exact hdistinct ((hunique pole₁ hpole₁).symm.trans (hunique pole₂ hpole₂))

/-- Closed class-level statement: triangular QNM clock solvability is nonselective, while its only
analytic perturbative nontriangular escape—a pole-germ collision—is impossible for the actual BM
returned Jost relation. -/
def D4HBAnalyticPerturbativeQNMClockAndCollisionRouteKilled : Prop :=
  D4BMMixedCasimirAllOrderTriangularQNMClockRenormalizationNoGo ∧
    ∀ (higher : ℂ × ℂ → ℂ)
      (n k N : ℕ) (conservativeFinitePart : ℝ)
      (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy),
      AnalyticAt ℂ higher
        (0, thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)) →
      ¬ D4BMXiGaugeFixedTotalPeriodAllOrderNontrivialPoleGermCollisionMinus higher
        n k N conservativeFinitePart amplitude orthogonalMixing q

/-- Premise-free Lean certificate killing the full analytic perturbative QNM-clock route class:
triangular towers absorb the source, and nontriangular germ collisions cannot occur. -/
theorem d4HBAnalyticPerturbativeQNMClockAndCollisionRouteKilled :
    D4HBAnalyticPerturbativeQNMClockAndCollisionRouteKilled := by
  exact ⟨d4BMMixedCasimirAllOrderTriangularQNMClockRenormalization_noGo,
    fun higher n k N conservativeFinitePart amplitude orthogonalMixing q hhigher =>
      not_d4BMXiGaugeFixedTotalPeriodAllOrderNontrivialPoleGermCollisionMinus
        higher n k N conservativeFinitePart amplitude orthogonalMixing q hhigher⟩

end

end RHTower
