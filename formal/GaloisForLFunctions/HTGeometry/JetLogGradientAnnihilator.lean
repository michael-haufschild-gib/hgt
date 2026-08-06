import GaloisForLFunctions.HTGeometry.ActiveCoeffLinearity
import GaloisForLFunctions.HTGeometry.NonTorusLevelSet
import GaloisForLFunctions.HTGeometry.PolyannulusFunctionDomain

/-!
# The annihilator of the jet logarithmic gradients

A constant covector annihilating the logarithmic gradients of every phase jet
at a single point annihilates the active lattice.

Pairing the covector with the logarithmic gradients produces one observable
whose phase jets are the pairings with the successive jets; if all of them
vanish at a point, the observable vanishes identically, and its active
coefficients are the pairings of the covector with the exponents.
-/

open Complex Set Filter Topology MeasureTheory

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### Linearity of the torus derivation -/

theorem torusDerivation_const_mul {U : Set (d → ℂ)} (omega : d → ℝ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F U) (c : ℂ) {z : d → ℂ}
    (hz : z ∈ U) :
    torusDerivation omega (fun w => c * F w) z
      = c * torusDerivation omega F z := by
  rw [torusDerivation_mul omega (analyticOnNhd_const (E := d → ℂ) (F := ℂ)) hF hz,
    torusDerivation_const, mul_zero, add_zero]

theorem torusDerivation_sum {ι : Type} [Fintype ι] {U : Set (d → ℂ)}
    (omega : d → ℝ) {g : ι → (d → ℂ) → ℂ}
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) U) {z : d → ℂ} (hz : z ∈ U) :
    torusDerivation omega (fun w => ∑ i, g i w) z
      = ∑ i, torusDerivation omega (g i) z := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact torusDerivation_const omega 0 z
  | insert i s hi ih =>
      have hfun : (fun w => ∑ k ∈ insert i s, g k w)
          = fun w => g i w + ∑ k ∈ s, g k w := by
        funext w
        rw [Finset.sum_insert hi]
      rw [hfun, torusDerivation_add omega (hg i)
        (Finset.analyticOnNhd_fun_sum s fun k _ => hg k) hz, ih,
        Finset.sum_insert hi]

/-! ### Pairing a covector with the logarithmic gradients -/

/-- The observable obtained by pairing a covector with the logarithmic
coordinate derivatives. -/
def logGradPairing (c : d → ℂ) (F : (d → ℂ) → ℂ) (z : d → ℂ) : ℂ :=
  ∑ j, c j * logCoordDeriv F j z

theorem analyticOnNhd_logGradPairing {ρ : d → ℝ} (c : d → ℂ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) :
    AnalyticOnNhd ℂ (logGradPairing c F) (polyannulus ρ) :=
  Finset.analyticOnNhd_fun_sum Finset.univ fun j _ =>
    analyticOnNhd_const.mul (analyticOnNhd_logCoordDeriv hF j)

theorem activeCoeff_logGradPairing {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (c : d → ℂ) {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ))
    (m : d → ℤ) :
    activeCoeff (logGradPairing c F) m
      = (∑ j, c j * (m j : ℂ)) * activeCoeff F m := by
  show activeCoeff (fun z => ∑ j, c j * logCoordDeriv F j z) m = _
  rw [activeCoeff_sum hρ
    (fun j => analyticOnNhd_const.mul (analyticOnNhd_logCoordDeriv hF j)) m,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [activeCoeff_const_mul, activeCoeff_logCoordDeriv hρ hF m j]
  ring

/-- **The pairing commutes with the jets.** -/
theorem logGradPairing_phaseJet {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (omega : d → ℝ) (c : d → ℂ) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (k : ℕ) :
    ∀ z ∈ polyannulus ρ,
      logGradPairing c (phaseJet omega F k) z
        = phaseJet omega (logGradPairing c F) k z := by
  induction k with
  | zero =>
      intro z _
      rfl
  | succ k ih =>
      intro z hz
      have hjetAn : AnalyticOnNhd ℂ (phaseJet omega F k) (polyannulus ρ) :=
        analyticOnNhd_phaseJet omega hF k
      have hcomm : logGradPairing c (phaseJet omega F (k + 1)) z
          = ∑ j, c j * torusDerivation omega
              (logCoordDeriv (phaseJet omega F k) j) z := by
        show (∑ j, c j * logCoordDeriv (phaseJet omega F (k + 1)) j z) = _
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        have hstep : phaseJet omega F (k + 1)
            = torusDerivation omega (phaseJet omega F k) := by
          rw [phaseJet, phaseJet, Function.iterate_succ_apply']
        rw [hstep]
        exact logCoordDeriv_torusDerivation hρ hjetAn omega j z hz
      rw [hcomm]
      have hlin : ∑ j, c j * torusDerivation omega
            (logCoordDeriv (phaseJet omega F k) j) z
          = torusDerivation omega (logGradPairing c (phaseJet omega F k)) z := by
        rw [show logGradPairing c (phaseJet omega F k)
              = fun w => ∑ j, c j * logCoordDeriv (phaseJet omega F k) j w from rfl,
          torusDerivation_sum omega
          (fun j => analyticOnNhd_const.mul
            (analyticOnNhd_logCoordDeriv hjetAn j)) hz]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [torusDerivation_const_mul omega (analyticOnNhd_logCoordDeriv hjetAn j)
          (c j) hz]
      rw [hlin]
      have hcong := torusDerivation_congr (isOpen_polyannulus ρ) omega
        (F := logGradPairing c (phaseJet omega F k))
        (G := phaseJet omega (logGradPairing c F) k) ih z hz
      rw [hcong]
      show torusDerivation omega
          ((torusDerivation omega)^[k] (logGradPairing c F)) z
        = (torusDerivation omega)^[k + 1] (logGradPairing c F) z
      rw [Function.iterate_succ_apply']

/-! ### Vanishing jets force a vanishing observable -/

omit [DecidableEq d] in
theorem eventuallyEq_zero_of_eqOn_scaled {σ : d → ℝ} {z₀ : d → ℂ}
    (hz₀ne : ∀ j, z₀ j ≠ 0) (hσ : (fun _ : d => (1 : ℂ)) ∈ polyannulus σ)
    {G : (d → ℂ) → ℂ} (h : ∀ z ∈ polyannulus σ, G (torusScale z₀ z) = 0) :
    G =ᶠ[𝓝 z₀] 0 := by
  have hcont : Continuous fun w : d → ℂ => fun j => w j / z₀ j :=
    continuous_pi fun j => (continuous_apply j).div_const _
  have hopen : IsOpen ((fun w : d → ℂ => fun j => w j / z₀ j) ⁻¹' polyannulus σ) :=
    (isOpen_polyannulus σ).preimage hcont
  have hmem : z₀ ∈ (fun w : d → ℂ => fun j => w j / z₀ j) ⁻¹' polyannulus σ := by
    have hfun : (fun j => z₀ j / z₀ j) = fun _ : d => (1 : ℂ) := by
      funext j
      exact div_self (hz₀ne j)
    show (fun j => z₀ j / z₀ j) ∈ polyannulus σ
    rw [hfun]
    exact hσ
  filter_upwards [hopen.mem_nhds hmem] with w hw
  have hscale : torusScale z₀ (fun j => w j / z₀ j) = w := by
    funext j
    show z₀ j * (w j / z₀ j) = w j
    rw [mul_comm, div_mul_cancel₀ _ (hz₀ne j)]
  have := h _ hw
  rw [hscale] at this
  exact this

/-- **An observable all of whose phase jets vanish at one point vanishes.** -/
theorem eqOn_zero_of_phaseJet_eq_zero {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hindep : RationallyIndependentFrequency omega) {G : (d → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G (polyannulus ρ)) {z₀ : d → ℂ}
    (hz₀ : z₀ ∈ polyannulus ρ) (hjets : ∀ k, phaseJet omega G k z₀ = 0) :
    ∀ z ∈ polyannulus ρ, G z = 0 := by
  classical
  set σ : d → ℝ := shrinkRadii ρ z₀ with hσdef
  have hσpos : ∀ j, 0 < σ j := fun j => shrinkRadii_pos hz₀ j
  have hmaps : ∀ z ∈ polyannulus σ, torusScale z₀ z ∈ polyannulus ρ :=
    torusScale_mem_polyannulus_of_shrink hz₀
  have hGσ : AnalyticOnNhd ℂ (fun z => G (torusScale z₀ z)) (polyannulus σ) :=
    analyticOnNhd_comp_torusScale_of_mapsTo hmaps hG
  have h1σ : (fun _ : d => (1 : ℂ)) ∈ polyannulus σ := one_mem_polyannulus hσpos
  have hjets0 : ∀ k,
      iteratedDeriv k (phaseFunction omega (fun z => G (torusScale z₀ z))) 0
        = iteratedDeriv k (fun _ : ℂ => (0 : ℂ)) 0 := by
    intro k
    rw [iteratedDeriv_phaseFunction hGσ k 0 (zero_mem_phaseStrip hσpos),
      phaseFunction, phasePoint_zero]
    have hcomp := phaseJet_comp_torusScale_of_mapsTo omega hmaps hG k _ h1σ
    rw [torusScale_one] at hcomp
    have hval : (torusDerivation omega)^[k] (fun z => G (torusScale z₀ z))
        (fun _ : d => (1 : ℂ)) = 0 := hcomp.trans (hjets k)
    have hconst : iteratedDeriv k (fun _ : ℂ => (0 : ℂ)) 0 = 0 := by
      cases k with
      | zero => rfl
      | succ k => rw [iteratedDeriv_const_succ]; rfl
    rw [hval, hconst]
  have hstrip := eqOn_of_iteratedDeriv_eq (isPreconnected_phaseStrip σ omega)
    (analyticOnNhd_phaseFunction (omega := omega) hGσ)
    (analyticOnNhd_const (E := ℂ) (F := ℂ))
    (zero_mem_phaseStrip hσpos) hjets0
  have horbit : ∀ t : ℝ, G (torusScale z₀ (torusOrbitPoint omega t)) = 0 := by
    intro t
    have hval := hstrip (ofReal_mem_phaseStrip hσpos t)
    rw [phaseFunction, phasePoint_ofReal] at hval
    exact hval
  have hscaled := eqOn_zero_polyannulus_of_eqOn_zero_orbit hσpos hindep hGσ horbit
  have hz₀ne : ∀ j, z₀ j ≠ 0 := fun j => ne_zero_of_mem_logAnnulus (hz₀ j)
  have hev : G =ᶠ[𝓝 z₀] 0 :=
    eventuallyEq_zero_of_eqOn_scaled hz₀ne h1σ hscaled
  intro z hz
  exact hG.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_polyannulus hρ) hz₀ hev hz

/-! ### The annihilator statement -/

/-- **A covector annihilating every jet logarithmic gradient at one point
annihilates the active support.** -/
theorem sum_mul_eq_zero_of_annihilates_jetLogGradients {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {z₀ : d → ℂ}
    (hz₀ : z₀ ∈ polyannulus ρ) {c : d → ℂ}
    (hc : ∀ k, ∑ j, c j * logCoordDeriv (phaseJet omega F k) j z₀ = 0) :
    ∀ m ∈ activeSupport F, ∑ j, c j * (m j : ℂ) = 0 := by
  have hpair : AnalyticOnNhd ℂ (logGradPairing c F) (polyannulus ρ) :=
    analyticOnNhd_logGradPairing c hF
  have hjets : ∀ k, phaseJet omega (logGradPairing c F) k z₀ = 0 := by
    intro k
    rw [← logGradPairing_phaseJet hρ omega c hF k z₀ hz₀]
    exact hc k
  have hzero := eqOn_zero_of_phaseJet_eq_zero hρ hindep hpair hz₀ hjets
  intro m hm
  have hcoeff : activeCoeff (logGradPairing c F) m = 0 := by
    have hfun : ∀ x : UnitAddTorus d,
        torusRestriction (logGradPairing c F) x = 0 := by
      intro x
      exact hzero _ (unitTorus_subset_polyannulus hρ (circleCoords_mem_unitTorus x))
    rw [activeCoeff]
    have hint : (fun x : UnitAddTorus d =>
        UnitAddTorus.mFourier (-m) x •
          torusRestriction (logGradPairing c F) x) = fun _ => 0 := by
      funext x
      rw [hfun x, smul_zero]
    show (∫ x, UnitAddTorus.mFourier (-m) x •
      torusRestriction (logGradPairing c F) x) = 0
    rw [hint, MeasureTheory.integral_zero]
  rw [activeCoeff_logGradPairing hρ c hF m] at hcoeff
  exact (mul_eq_zero.1 hcoeff).resolve_right hm

end

end GaloisForLFunctions.HTGeometry
