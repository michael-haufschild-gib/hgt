import GaloisForLFunctions.HTGeometry.AllJetLevelSet
import GaloisForLFunctions.HTGeometry.TranslatedActiveCoeffScaling

/-!
# The stabilizer of a phase observable, for arbitrary scalings

A scaling by an arbitrary point of the polyannulus which fixes a phase
observable on the torus annihilates every active character.  This is the
scaling law together with the fact that the active coefficients are computed on
the torus, where the invariance is assumed.

For a full-rank active lattice the annihilator consists of roots of unity, so
in particular every such scaling has unit modulus in each coordinate.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-- **A scaling fixing the observable on the torus annihilates every active
character.** -/
theorem charPow_eq_one_of_eqOn_unitTorus {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {h : d → ℂ}
    (hh : h ∈ polyannulus ρ)
    (hinv : ∀ z ∈ unitTorus d, F (torusScale h z) = F z) :
    ∀ m ∈ activeSupport F, charPow h m = 1 := by
  have hres : torusRestriction (fun z => F (torusScale h z)) = torusRestriction F := by
    funext x
    exact hinv _ (circleCoords_mem_unitTorus x)
  intro m hm
  have hcoeff : activeCoeff (fun z => F (torusScale h z)) m = activeCoeff F m := by
    rw [activeCoeff, activeCoeff, hres]
  rw [activeCoeff_comp_torusScale_polyannulus hρ hF m h hh] at hcoeff
  have h1 : charPow h m * activeCoeff F m = 1 * activeCoeff F m := by
    rw [hcoeff, one_mul]
  exact mul_right_cancel₀ hm h1

omit [DecidableEq d] in
/-- **The modulus of an annihilated character.**  A scaling annihilating a
character has unit modulus against that character. -/
theorem norm_eq_one_of_charPow_eq_one {h : d → ℂ}
    {m : d → ℤ} (hm : charPow h m = 1) :
    ∏ j, ‖h j‖ ^ (m j) = 1 := by
  have hnorm : ‖charPow h m‖ = ∏ j, ‖h j‖ ^ (m j) := by
    rw [charPow, norm_prod]
    exact Finset.prod_congr rfl fun j _ => norm_zpow (h j) (m j)
  rw [hm, norm_one] at hnorm
  exact hnorm.symm

/-! ### Scaling commutes with the derivation, for arbitrary scalings -/

omit [DecidableEq d] in
theorem analyticOnNhd_comp_torusScale_of_mapsTo {ρ σ : d → ℝ} {h : d → ℂ}
    (hmaps : ∀ z ∈ polyannulus σ, torusScale h z ∈ polyannulus ρ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) :
    AnalyticOnNhd ℂ (fun z => F (torusScale h z)) (polyannulus σ) :=
  hF.comp (analyticOnNhd_torusScale h _) hmaps

theorem coordDeriv_comp_torusScale_of_mapsTo {ρ σ : d → ℝ} {h : d → ℂ}
    (hmaps : ∀ z ∈ polyannulus σ, torusScale h z ∈ polyannulus ρ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (j : d)
    {z : d → ℂ} (hz : z ∈ polyannulus σ) :
    coordDeriv (fun w => F (torusScale h w)) j z
      = h j * coordDeriv F j (torusScale h z) := by
  have hmem : torusScale h z ∈ polyannulus ρ := hmaps z hz
  have hFd : HasFDerivAt F (fderiv ℂ F (torusScale h z)) (torusScale h z) :=
    (hF _ hmem).differentiableAt.hasFDerivAt
  have hSd : HasFDerivAt (torusScale h) (torusScaleL h) z := by
    have hid := (torusScaleL h).hasFDerivAt (x := z)
    refine hid.congr_of_eventuallyEq ?_
    filter_upwards with w
    rw [torusScaleL_apply]
  have hcomp : HasFDerivAt (fun w => F (torusScale h w))
      ((fderiv ℂ F (torusScale h z)).comp (torusScaleL h)) z := hFd.comp z hSd
  rw [coordDeriv, hcomp.fderiv]
  rw [ContinuousLinearMap.coe_comp, Function.comp_apply, torusScaleL_single,
    map_smul, smul_eq_mul, coordDeriv]

theorem torusDerivation_comp_torusScale_of_mapsTo {ρ σ : d → ℝ} (omega : d → ℝ)
    {h : d → ℂ} (hmaps : ∀ z ∈ polyannulus σ, torusScale h z ∈ polyannulus ρ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) :
    ∀ z ∈ polyannulus σ,
      torusDerivation omega (fun w => F (torusScale h w)) z
        = torusDerivation omega F (torusScale h z) := by
  intro z hz
  rw [torusDerivation, torusDerivation]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordDeriv_comp_torusScale_of_mapsTo hmaps hF j hz]
  show Complex.I * (omega j : ℂ) * z j * (h j * coordDeriv F j (torusScale h z))
    = Complex.I * (omega j : ℂ) * (h j * z j) * coordDeriv F j (torusScale h z)
  ring

theorem phaseJet_comp_torusScale_of_mapsTo {ρ σ : d → ℝ} (omega : d → ℝ)
    {h : d → ℂ} (hmaps : ∀ z ∈ polyannulus σ, torusScale h z ∈ polyannulus ρ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (k : ℕ) :
    ∀ z ∈ polyannulus σ,
      phaseJet omega (fun w => F (torusScale h w)) k z
        = phaseJet omega F k (torusScale h z) := by
  induction k with
  | zero =>
      intro z _
      rfl
  | succ k ih =>
      intro z hz
      have hstep : phaseJet omega (fun w => F (torusScale h w)) (k + 1) z
          = torusDerivation omega
              (phaseJet omega (fun w => F (torusScale h w)) k) z := by
        rw [phaseJet, phaseJet, Function.iterate_succ_apply']
      rw [hstep]
      have hcong := torusDerivation_congr (isOpen_polyannulus σ) omega
        (F := phaseJet omega (fun w => F (torusScale h w)) k)
        (G := fun w => phaseJet omega F k (torusScale h w)) ih z hz
      rw [hcong]
      have hjet := torusDerivation_comp_torusScale_of_mapsTo omega hmaps
        (analyticOnNhd_phaseJet omega hF k) z hz
      rw [hjet]
      show torusDerivation omega ((torusDerivation omega)^[k] F) (torusScale h z)
        = (torusDerivation omega)^[k + 1] F (torusScale h z)
      rw [Function.iterate_succ_apply']

end

end GaloisForLFunctions.HTGeometry
