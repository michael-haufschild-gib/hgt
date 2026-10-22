import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFullMirrorGenericCouplingMixingEndpoint
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFullMirrorWeakCouplingOrderEndpoint
import GaloisForLFunctions.RHTower.WindingFull
import GaloisForLFunctions.HTGeometry.EntireZeroFactorization
import GaloisForLFunctions.HTGeometry.SampledSmallSmooth
import GaloisForLFunctions.RHTower.GelfondSchneiderProof.AnalyticPart

/-!
# Coupling-plane winding of the full theta-cusp Hawking mirror

The entire complex-coupling continuation of the exact Davies--Fulling eikonal amplitude has local
zero order equal to the least nonzero physical coupling jet.  Its phase on every sufficiently small
complex-coupling circle therefore winds by exactly that order.  This is a source-faithful local
coupling analogue of the Birman--Krein resonance index, not the previously falsified identification
of the full mirror with a scalar Cayley block.

Consequently RH is equivalent to unit local coupling winding in every noncentral tilted sector.
This bridge does not prove that dynamics selects unit winding: higher-order Fermi-golden-rule
channels show why unitarity and KMS detailed balance alone cannot exclude tangential order jumps.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

theorem iteratedDeriv_thetaCuspHawkingEikonalCouplingEntire_zero_eq_powerMoment
    (a : ℝ) (ha : |a| < 1) (total : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n (thetaCuspHawkingEikonalCouplingEntire a ha total) 0 =
      (-Complex.I) ^ n * thetaCuspTiltedPowerMoment a n total := by
  let F : ℂ → ℂ := thetaCuspHawkingEikonalCouplingEntire a ha total
  have hrestrict : (fun t : ℝ => F (t : ℂ)) =
      fun t : ℝ => thetaCuspHawkingEikonalFourier a t total := by
    funext t
    exact thetaCuspHawkingEikonalCouplingEntire_ofReal a ha total t
  have hcomplex :=
    HTGeometry.iteratedDeriv_comp_ofReal_of_analyticAt
      (T := -1) n
      (H := F)
      (fun t _ht =>
        (thetaCuspHawkingEikonalCouplingEntire_analyticOnNhd a ha total)
          t (Set.mem_univ t))
      0 (by norm_num)
  rw [hrestrict] at hcomplex
  have hreal := iteratedDeriv_thetaCuspHawkingEikonalFourier_zero_eq_powerMoment
    a ha total (n - 1)
  rw [show n - 1 + 1 = n by omega] at hreal
  exact hcomplex.symm.trans hreal

/-- Exact zero multiplicity in complex mirror coupling equals the least nonzero physical
eikonal coupling-jet order. -/
theorem analyticOrderAt_thetaCuspHawkingEikonalCouplingEntire_zero
    (a total : ℝ) (ha : |a| < 1) :
    analyticOrderAt (thetaCuspHawkingEikonalCouplingEntire a ha total) 0 =
      thetaCuspHawkingFullMirrorSectorCouplingOrder a total ha := by
  let m := thetaCuspHawkingFullMirrorSectorCouplingOrder a total ha
  let F : ℂ → ℂ := thetaCuspHawkingEikonalCouplingEntire a ha total
  have hF : AnalyticAt ℂ F 0 :=
    (thetaCuspHawkingEikonalCouplingEntire_analyticOnNhd a ha total)
      0 (Set.mem_univ 0)
  apply (_root_.GaloisForLFunctions.RHTower.GelfondSchneiderProof.analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero m F hF).mp
  constructor
  · intro n hn
    by_cases hnzero : n = 0
    · subst n
      simp [F, thetaCuspHawkingEikonalCouplingEntire_zero]
    · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hnzero
      simp only [F]
      rw [← iteratedDeriv_eq_iterate]
      rw [iteratedDeriv_thetaCuspHawkingEikonalCouplingEntire_zero_eq_powerMoment
        a ha total n hnpos]
      rw [thetaCuspHawkingFullMirrorSectorCouplingOrder_lower_eq_zero
        a total ha n hnpos hn]
      simp
  · have hm := thetaCuspHawkingFullMirrorSectorCouplingOrder_spec a total ha
    simp only [F]
    rw [← iteratedDeriv_eq_iterate]
    rw [iteratedDeriv_thetaCuspHawkingEikonalCouplingEntire_zero_eq_powerMoment
      a ha total m hm.1]
    exact mul_ne_zero (pow_ne_zero _ (by simp)) hm.2

/-- **Local coupling-plane scattering index.**  On every sufficiently small complex-coupling
circle, the exact Davies--Fulling eikonal response winds by precisely its least nonzero coupling
order.  This is the source-faithful coupling analogue of a Birman--Krein resonance index. -/
theorem exists_thetaCuspHawkingEikonalCouplingWinding_eq_order
    (a total : ℝ) (ha : |a| < 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      windingNumber
          (fun θ : ℝ => thetaCuspHawkingEikonalCouplingEntire a ha total
            ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          0 (2 * Real.pi) =
        (thetaCuspHawkingFullMirrorSectorCouplingOrder a total ha : ℤ) := by
  let m := thetaCuspHawkingFullMirrorSectorCouplingOrder a total ha
  let F : ℂ → ℂ := thetaCuspHawkingEikonalCouplingEntire a ha total
  have hdiff : Differentiable ℂ F := fun z =>
    ((thetaCuspHawkingEikonalCouplingEntire_analyticOnNhd a ha total)
      z (Set.mem_univ z)).differentiableAt
  have hord : analyticOrderAt F 0 = (m : ℕ∞) := by
    exact analyticOrderAt_thetaCuspHawkingEikonalCouplingEntire_zero a total ha
  obtain ⟨g, hg, hg0, hfactor⟩ :=
    GaloisForLFunctions.HTGeometry.exists_entire_factor_of_analyticOrder hdiff hord
  have hopen : IsOpen (g ⁻¹' ({0}ᶜ : Set ℂ)) :=
    isOpen_compl_singleton.preimage hg.continuous
  have hzeroMem : (0 : ℂ) ∈ g ⁻¹' ({0}ᶜ : Set ℂ) := by simpa using hg0
  obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp hopen 0 hzeroMem
  refine ⟨R, hR, fun r hr hrR => ?_⟩
  let s : Finset Unit := {()}
  let rho : Unit → ℂ := fun _ => 0
  let mult : Unit → ℕ := fun _ => m
  have hwind := windingNumber_argument_principle s rho mult
    (f := F) (g := g) (c := 0) (r := r) (R := R)
    hrR hr
    (by
      intro i hi
      simp [rho, hr])
    hg.continuous.continuousOn
    (by
      intro z hz
      exact hRsub hz)
    (by
      intro z hz
      simpa [s, rho, mult] using hfactor z)
  simpa [F, s, rho, mult] using hwind

/-- Every noncentral tilted sector has a simple coupling-plane scattering index. -/
def ThetaCuspHawkingFullMirrorUnitCouplingWinding : Prop :=
  ∀ (a total : ℝ) (ha : |a| < 1), a ≠ 0 →
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      windingNumber
          (fun θ : ℝ => thetaCuspHawkingEikonalCouplingEntire a ha total
            ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          0 (2 * Real.pi) = 1

/-- RH is exactly unit local scattering winding in complex mirror coupling for every noncentral
tilted sector.  Full finite-coupling mixing is unconditional; the missing dynamics must force this
local index to be one rather than an arbitrary positive integer. -/
theorem riemannHypothesis_iff_thetaCuspHawkingFullMirrorUnitCouplingWinding :
    RiemannHypothesis ↔ ThetaCuspHawkingFullMirrorUnitCouplingWinding := by
  rw [riemannHypothesis_iff_thetaCuspHawkingFullMirrorNoOrderJump]
  constructor
  · intro h a total ha hane
    obtain ⟨R, hR, hwind⟩ :=
      exists_thetaCuspHawkingEikonalCouplingWinding_eq_order a total ha
    refine ⟨R, hR, fun r hr hrR => ?_⟩
    rw [hwind r hr hrR, h a total ha hane]
    norm_num
  · intro h a total ha hane
    obtain ⟨Runit, hRunit, hunit⟩ := h a total ha hane
    obtain ⟨Rorder, hRorder, horder⟩ :=
      exists_thetaCuspHawkingEikonalCouplingWinding_eq_order a total ha
    let r := min Runit Rorder / 2
    have hr : 0 < r := by
      dsimp [r]
      positivity
    have hrUnit : r < Runit := by
      dsimp [r]
      have hmin : min Runit Rorder ≤ Runit := min_le_left _ _
      linarith [hRunit, hRorder]
    have hrOrder : r < Rorder := by
      dsimp [r]
      have hmin : min Runit Rorder ≤ Rorder := min_le_right _ _
      linarith [hRunit, hRorder]
    have heq := (horder r hr hrOrder).symm.trans (hunit r hr hrUnit)
    exact_mod_cast heq

end RHTower
