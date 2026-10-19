import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateSuperposition

/-!
# The shifted ground states fail the folded supersolution test at the origin

The reflected collar mass of `ω_a` is bounded below by its prime-`2` term,
`Λ(2) 2^{−1/2} (Φ(log 2 − x − a) − Φ(log 2 − x + a))⁺`, which stays positive as `x → 0⁺`, while the
source `sinh(a/2) sinh(x/2)` vanishes at the origin. Hence every shifted ground state is a strict
folded **subsolution** on a right neighbourhood of `0`: the hypothesis of the folded supersolution
criterion fails there for every `a > 0`. (Near infinity it fails by the prime number theorem; see the
card.) The folded ground-state representation therefore reads, for the Doob tests `Φ(ω_a u)`,

    markovEnergy = groundRemainder − 4 ∫_{x>0} u² ω_a Φ (C_a(x) − sinh(a/2) sinh(x/2)),

so nonnegativity of the Markov energy is the statement that the nonnegative remainder dominates the
weighted positive part of the collar excess: positivity is carried by the remainder, not by the
generator.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

theorem vonMangoldtAtom_two_pos : 0 < vonMangoldtAtom 2 := by
  unfold vonMangoldtAtom
  rw [if_pos le_rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

/-- The prime `2` alone bounds the reflected collar mass from below. -/
theorem shiftedCollarMass_ge_prime_two (a x : ℝ) :
    vonMangoldtAtom 2 * max (shiftDifference a (Real.log 2 - x)) 0 ≤ shiftedCollarMass a x := by
  unfold shiftedCollarMass
  have h1 : 0 ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0 :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le (le_max_right _ _)
  have h2 : vonMangoldtAtom 2 * max (shiftDifference a (Real.log 2 - x)) 0 ≤
      ∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 := by
    have hs := summable_atom_max_shiftDifference a x
    have h := hs.le_tsum 2 fun j _ => mul_nonneg (vonMangoldtAtom_nonneg j) (le_max_right _ _)
    simpa using h
  linarith

/-- **Origin failure.** For every `a > 0` there is `x₀ > 0` such that the shifted ground state is a
strict folded subsolution on `(0, x₀)`. -/
theorem exists_origin_window_foldedGenerator_lt_potential {a : ℝ} (ha : 0 < a) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x, 0 < x → x < x₀ →
      foldedGenerator (shiftedGroundState a) x <
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x := by
  have hFc : Continuous fun x : ℝ => Real.sinh (a / 2) * Real.sinh (x / 2) :=
    continuous_const.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hGc : Continuous fun x : ℝ => vonMangoldtAtom 2 * max (shiftDifference a (Real.log 2 - x)) 0 :=
    continuous_const.mul
      (((continuous_shiftDifference a).comp (continuous_const.sub continuous_id)).max continuous_const)
  have h0 : Real.sinh (a / 2) * Real.sinh ((0 : ℝ) / 2) <
      vonMangoldtAtom 2 * max (shiftDifference a (Real.log 2 - 0)) 0 := by
    rw [zero_div, Real.sinh_zero, mul_zero, sub_zero]
    exact mul_pos vonMangoldtAtom_two_pos
      (lt_max_of_lt_left (shiftDifference_pos ha (Real.log_pos one_lt_two)))
  have hev := ContinuousAt.eventually_lt hFc.continuousAt hGc.continuousAt h0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun x hx hxε => ?_⟩
  have hdist : dist x 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hx]
    exact hxε
  have hlt := hball hdist
  have hC : Real.sinh (a / 2) * Real.sinh (x / 2) < shiftedCollarMass a x :=
    lt_of_lt_of_le hlt (shiftedCollarMass_ge_prime_two a x)
  have hiff := foldedSupersolution_shiftedGroundState_iff ha hx
  by_contra hcon
  rw [not_lt] at hcon
  exact absurd (hiff.mp hcon) (not_le.mpr hC)

theorem contDiff_shiftedGroundState (a : ℝ) : ContDiff ℝ 2 (shiftedGroundState a) := by
  unfold shiftedGroundState shiftDifference
  exact ((contDiff_riemannKernelReal.comp (contDiff_id.sub contDiff_const)).sub
    (contDiff_riemannKernelReal.comp (contDiff_id.add contDiff_const))).div
    contDiff_riemannKernelReal fun x => (riemannKernelReal_pos x).ne'

/-- **Remainder-dominates-defect form of the Markov energy on the shifted ground state.** -/
theorem markovEnergy_phiDoob_shiftedGroundState_eq {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x)
    (hadm : FoldedAdmissible (shiftedGroundState a) u) :
    markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) =
      groundRemainder (shiftedGroundState a) u -
        4 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftedGroundState a x * riemannKernelReal x *
          (shiftedCollarMass a x - Real.sinh (a / 2) * Real.sinh (x / 2)) := by
  rw [markovEnergy_phiDoob_eq_groundRemainder_add_potential (contDiff_shiftedGroundState a)
    (shiftedGroundState_neg a) hu huc heven hadm]
  have h : (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftedGroundState a x *
      (foldedGenerator (shiftedGroundState a) x -
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x)) =
      ∫ x in Ioi (0 : ℝ), (-2) * (u x ^ 2 * shiftedGroundState a x * riemannKernelReal x *
        (shiftedCollarMass a x - Real.sinh (a / 2) * Real.sinh (x / 2))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [foldedGenerator_shiftedGroundState_sub_potential ha (mem_Ioi.mp hx)]
    ring
  rw [h, integral_const_mul]
  ring

/-- Nonnegativity of the Markov energy on `Φ(ω_a u)` is the domination of the weighted collar excess
by the nonnegative remainder. -/
theorem markovEnergy_phiDoob_shiftedGroundState_nonneg_iff {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x)
    (hadm : FoldedAdmissible (shiftedGroundState a) u) :
    0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) ↔
      4 * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftedGroundState a x * riemannKernelReal x *
          (shiftedCollarMass a x - Real.sinh (a / 2) * Real.sinh (x / 2))) ≤
        groundRemainder (shiftedGroundState a) u := by
  rw [markovEnergy_phiDoob_shiftedGroundState_eq ha hu huc heven hadm]
  constructor <;> intro h <;> linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
