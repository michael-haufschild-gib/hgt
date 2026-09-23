import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorDilationChannels
import GaloisForLFunctions.RHTower.CCMCriticalMellinRieszMobiusRenewal
import GaloisForLFunctions.RHTower.CCMUnitRieszCoherentOutgoingChargeHankel

/-!
# Unit-Riesz weld for the completed CCM-FU Möbius--divisor source

The capped square-root tail produced by the exact dilation-channel telescope is not merely similar
to Suzuki's unit-aperture critical profile.  It is exactly that profile after multiplication by
half the aperture.  Consequently the completed prime--polar--Gamma window, the signed CCM-FU
divisor producer, the coherent Route-O Abel action, and the unit-aperture Suzuki reporter carry one
and the same finite source.

No source coefficient is estimated or separated in this module.
-/

open Nat ArithmeticFunction Finset
open scoped BigOperators Moebius
open Filter Topology

namespace RHTower

noncomputable section

/-- The square-root Riesz gap is exactly half-aperture times the critical unit-aperture profile. -/
theorem sqrtGap_eq_half_aperture_mul_unitApertureWeight
    {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k) :
    Real.sqrt M - Real.sqrt k =
      (M : ℝ) / 2 * unitApertureCriticalPrimeWeight M k := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [unitApertureCriticalPrimeWeight_eq_riesz hMR hkR]
  have hsM : Real.sqrt (M : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hMR).ne'
  have hsMSq : Real.sqrt (M : ℝ) ^ (2 : ℕ) = M := Real.sq_sqrt hMR.le
  have hsdiv : Real.sqrt ((k : ℝ) / M) =
      Real.sqrt k / Real.sqrt M := Real.sqrt_div (by positivity) M
  rw [hsdiv]
  field_simp [hsM]
  rw [hsMSq]
  ring

/-- Actual completed prime--polar--Gamma source in Suzuki's critical unit-aperture coordinates. -/
def completedPrimePolarGammaUnitApertureWindow (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (M - 1),
    completedPrimePolarGammaAtom k *
      unitApertureCriticalPrimeWeight M k

/-- **Exact CCM-FU/Suzuki weld.**  The pre-scalar Möbius--divisor producer is half the aperture
times the completed signed unit-aperture window. -/
theorem mobiusMoment_eq_half_aperture_mul_unitApertureWindow
    {M : ℕ} (hM : 1 ≤ M) :
    mobiusDivisorSquareRootAbelMoment M =
      (M : ℝ) / 2 * completedPrimePolarGammaUnitApertureWindow M := by
  rw [completedPrimePolarGammaUnitApertureWindow,
    Finset.mul_sum,
    ← sum_completedPrimePolarGammaAtom_mul_sqrtGap_eq_mobiusMoment M]
  apply Finset.sum_congr rfl
  intro k hkmem
  rw [sqrtGap_eq_half_aperture_mul_unitApertureWeight hM
    (Finset.mem_Icc.mp hkmem).1]
  ring

/-- Uniform signed bound for the literal completed unit-aperture window. -/
def CompletedPrimePolarGammaUnitApertureBounded : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 2 ≤ M →
    |completedPrimePolarGammaUnitApertureWindow M| ≤ B

/-- The Suzuki-coordinate window bound and the Möbius--divisor normalized bound are identical up
to the exact constant factor two. -/
theorem mobiusBounded_iff_unitApertureBounded :
    MobiusDivisorSquareRootAbelBounded ↔
      CompletedPrimePolarGammaUnitApertureBounded := by
  constructor
  · rintro ⟨B, hB, hbound⟩
    refine ⟨2 * B, by positivity, ?_⟩
    intro M hM
    have hrel := mobiusMoment_eq_half_aperture_mul_unitApertureWindow
      (M := M) (by omega : 1 ≤ M)
    have hMR : (0 : ℝ) < M := by positivity
    have hsolve : completedPrimePolarGammaUnitApertureWindow M =
        2 * (mobiusDivisorSquareRootAbelMoment M / M) := by
      rw [hrel]
      field_simp
    rw [hsolve, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (hbound M hM) (by norm_num)
  · rintro ⟨B, hB, hbound⟩
    refine ⟨B / 2, by positivity, ?_⟩
    intro M hM
    have hrel := mobiusMoment_eq_half_aperture_mul_unitApertureWindow
      (M := M) (by omega : 1 ≤ M)
    have hMR : (0 : ℝ) < M := by positivity
    rw [hrel]
    have heq :
        ((M : ℝ) / 2 * completedPrimePolarGammaUnitApertureWindow M) / M =
          completedPrimePolarGammaUnitApertureWindow M / 2 := by
      field_simp
    rw [heq, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
      (hbound M hM)

/-- RH is exactly uniform boundedness of the actual completed signed Suzuki unit-aperture window. -/
theorem riemannHypothesis_iff_completedPrimePolarGammaUnitApertureBounded :
    RiemannHypothesis ↔ CompletedPrimePolarGammaUnitApertureBounded :=
  riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded.trans
    mobiusBounded_iff_unitApertureBounded

/-- **Universal source invariant.**  The literal FU/Suzuki unit-aperture window is the critical
Mellin--Chebyshev resolvent plus one explicit source-free edge: Gamma normalization minus the
square-root polar lattice defect.  Thus Route O, CCM-FU, and Suzuki do not have independent hard
estimates; after boundary transport they share the same signed arithmetic scalar. -/
theorem unitApertureWindow_eq_resolvent_add_sourceFreeEdge
    {M : ℕ} (hM : 2 ≤ M) :
    completedPrimePolarGammaUnitApertureWindow M =
      criticalMellinChebyshevResolventSource (Real.log M) +
        2 * ((2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1) -
          coherentSquareRootPolarLatticeDefect M) / M) := by
  have hMR : (0 : ℝ) < M := by positivity
  have hwindow := mobiusMoment_eq_half_aperture_mul_unitApertureWindow
    (M := M) (by omega : 1 ≤ M)
  have hmoment := mobiusDivisorSquareRootAbelMoment_eq_coherent_add_gammaBoundary
    (M := M) (by omega : 1 ≤ M)
  have hout := coherentCompletedOutgoing_mul_eq_abel_add_latticeDefect
    (M := M) hM
  have hres :=
    GaloisForLFunctions.RHTower.unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hM
  rw [hres] at hout
  field_simp
  linear_combination 2 * hmoment - 2 * hwindow - 2 * hout

/-- The source-free edge in the universal invariant vanishes cofinally.  This is exact boundary
transport between the finite FU/Suzuki source and the continuous critical resolvent. -/
theorem tendsto_unitApertureWindow_sub_resolvent_zero :
    Tendsto (fun N : ℕ =>
      completedPrimePolarGammaUnitApertureWindow (N + 2) -
        criticalMellinChebyshevResolventSource (Real.log (N + 2 : ℕ)))
      atTop (nhds 0) := by
  have hsqrt := tendsto_sqrt_natCast_div_natCast_atTop_zero.comp
    (Filter.tendsto_add_atTop_nat 2)
  have hinv := tendsto_inv_natCast_atTop_zero.comp
    (Filter.tendsto_add_atTop_nat 2)
  have hgamma : Tendsto (fun N : ℕ =>
      (2 * Real.eulerMascheroniConstant * (Real.sqrt (N + 2 : ℕ) - 1)) /
        (N + 2 : ℕ)) atTop (nhds 0) := by
    have h := (hsqrt.sub hinv).const_mul
      (2 * Real.eulerMascheroniConstant)
    have h0 : Tendsto (fun N : ℕ =>
        2 * Real.eulerMascheroniConstant *
          (Real.sqrt (N + 2 : ℕ) / (N + 2 : ℕ) -
            1 / (N + 2 : ℕ))) atTop (nhds 0) := by
      simpa only [Function.comp_apply, mul_zero, sub_zero] using h
    apply h0.congr'
    exact Eventually.of_forall fun N => by ring
  have hlat0 := tendsto_coherentSquareRootPolarLatticeDefect_div_zero.comp
    (Filter.tendsto_add_atTop_nat 1)
  have hlat : Tendsto (fun N : ℕ =>
      coherentSquareRootPolarLatticeDefect (N + 2) / (N + 2 : ℕ))
      atTop (nhds 0) := by
    convert hlat0 using 1
    funext N
    dsimp
  have hcorr := (hgamma.sub hlat).const_mul 2
  have hcorr0 : Tendsto (fun N : ℕ =>
      2 * ((2 * Real.eulerMascheroniConstant * (Real.sqrt (N + 2 : ℕ) - 1) -
        coherentSquareRootPolarLatticeDefect (N + 2)) / (N + 2 : ℕ)))
      atTop (nhds 0) := by
    convert hcorr using 1
    · funext N
      ring
    · simp
  apply hcorr0.congr'
  exact Eventually.of_forall fun N => by
    dsimp
    rw [unitApertureWindow_eq_resolvent_add_sourceFreeEdge
      (M := N + 2) (by omega : 2 ≤ N + 2)]
    ring

end

end RHTower
