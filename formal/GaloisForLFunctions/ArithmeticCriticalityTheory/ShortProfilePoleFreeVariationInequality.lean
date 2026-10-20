import GaloisForLFunctions.ArithmeticCriticalityTheory.MarkovWindowZetaPositivityTransfer
import GaloisForLFunctions.ArithmeticCriticalityTheory.ZeroFormGaugeInvariance
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateAdmissibility

/-!
# The pole-free variation inequality on short profiles

The sharp form of the problem on the ground-state family is the pole-free variation inequality
`D_a(u) ≤ 2S_a(u) + V_a(u)` for even profiles `u`, the zeros being visible only on `μ_a`-mean-zero
profiles, where the pole term vanishes. Its left and right sides are energies of the shifted ground
state `ω_a`; by gauge invariance its defect is the zero form of the odd test `m_a u`
(`poleFreeForm_eq_zeroForm`). On an odd test the zero form is the full zero form, and the Markov
window (`fullZeroForm_ge_of_support_le_sharp`) bounds it below. Hence:

* **Pole-free variation inequality on short profiles**
  (`reflectedDifferenceEnergy_add_le_poleFree_of_support_le`). For every shift `a > 0` and every even
  `u ∈ C²_c` vanishing outside `[−21/200, 21/200]`, mean-zero or not,

      D_a(u) + (1/30) ∫ (m_a u)² ≤ 2 S_a(u) + V_a(u).

* **Remainder dominates defect on short profiles**
  (`collarDefect_add_le_groundRemainder_of_support_le`). The folded ground remainder dominates the
  weighted collar excess with the same margin:
  `4 ∫_{x>0} u² ω_a Φ (C_a − sinh(a/2) sinh(x/2)) + (1/30) ∫ (m_a u)² ≤ R_N(ω_a, u)`.

These are the first positive regions of the two frontier inequalities that are not regions of pole
domination: on short profiles the reflected variation across the fold is paid by the same-side
variation and the variance with a uniform margin, at every shift.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

theorem zeroForm_eq_fullZeroForm_of_odd {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) :
    zeroForm F = fullZeroForm F := by
  unfold zeroForm fullZeroForm
  rw [evenPoleMoment_eq_zero_of_odd hodd]
  ring

section ShortProfile

variable {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
  (heven : ∀ x, u (-x) = u x) (hsupp : ∀ x, 21 / 200 < |x| → u x = 0)

include hu huc heven hsupp in
/-- The odd test `m_a u` of a short profile lies in the Markov window. -/
theorem fullZeroForm_shiftedGroundState_ge (a : ℝ) :
    1 / 30 * ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 ≤
      zeroForm (phiDoobTest (fun y => shiftedGroundState a y * u y)) := by
  set F := phiDoobTest (fun y => shiftedGroundState a y * u y) with hF
  have hFd : ContDiff ℝ 2 F := contDiff_phiDoobTest ((contDiff_shiftedGroundState a).mul hu)
  have hFc : HasCompactSupport F := hasCompactSupport_phiDoobTest huc.mul_left
  have hodd : ∀ x, F (-x) = -F x := fun x => by
    simp only [hF, phiDoobTest]
    rw [riemannKernelReal_neg', shiftedGroundState_neg, heven]
    ring
  have hFs : ∀ x, 21 / 200 < |x| → F x = 0 := fun x hx => by
    simp only [hF, phiDoobTest]
    rw [hsupp x hx, mul_zero, mul_zero]
  rw [zeroForm_eq_fullZeroForm_of_odd hodd]
  exact fullZeroForm_ge_of_support_le_sharp hFd hFc hFs

include ha hu huc heven hsupp in
/-- **The pole-free variation inequality on short profiles**, with a uniform margin. -/
theorem reflectedDifferenceEnergy_add_le_poleFree_of_support_le :
    reflectedDifferenceEnergy (shiftedGroundState a) u +
        1 / 30 * ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  have h := fullZeroForm_shiftedGroundState_ge hu huc heven hsupp a
  rw [← poleFreeForm_eq_zeroForm ha hu huc heven] at h
  linarith

include ha hu huc heven hsupp in
/-- **The remainder dominates the collar defect on short profiles**, with a uniform margin. -/
theorem collarDefect_add_le_groundRemainder_of_support_le :
    4 * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftedGroundState a x * riemannKernelReal x *
        (shiftedCollarMass a x - Real.sinh (a / 2) * Real.sinh (x / 2))) +
        1 / 30 * ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 ≤
      groundRemainder (shiftedGroundState a) u := by
  have h := fullZeroForm_shiftedGroundState_ge hu huc heven hsupp a
  have hQ := markovEnergy_phiDoob_shiftedGroundState_eq_of_contDiff ha hu huc heven
  have hZ : zeroForm (phiDoobTest (fun y => shiftedGroundState a y * u y)) ≤
      markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) := by
    unfold zeroForm
    nlinarith [sq_nonneg (oddPoleMoment (phiDoobTest (fun y => shiftedGroundState a y * u y)))]
  linarith

end ShortProfile

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
