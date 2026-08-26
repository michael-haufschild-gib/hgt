import GaloisForLFunctions.HTGeometry.MakarovPoltoratskiWeakPhaseBigO
import GaloisForLFunctions.RHTower.KapustinGammaToeplitzPhase

/-!
# Oriented reciprocal-Gamma Toeplitz phase

The measurable `p = 1` bounded-phase correction retains the right-half-plane orientation and
therefore leaves one, rather than two, copies of the reciprocal-Gamma phase.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Fixed phase left by the oriented `p = 1` collision. -/
def kapustinOneSidedToeplitzPhase (x : ℝ) : ℝ :=
  kapustinReciprocalGammaPhase x - 8 * Real.arctan x

/-- Its exact unimodular symbol. -/
def kapustinOneSidedToeplitzSymbol (x : ℝ) : ℂ :=
  Complex.exp ((kapustinOneSidedToeplitzPhase x : ℂ) * I)

theorem norm_kapustinOneSidedToeplitzSymbol (x : ℝ) :
    ‖kapustinOneSidedToeplitzSymbol x‖ = 1 := by
  simp [kapustinOneSidedToeplitzSymbol]

theorem tendsto_kapustinOneSidedToeplitzPhase_ratio :
    Tendsto (fun x => kapustinOneSidedToeplitzPhase x / (x * Real.log x))
      atTop (nhds 1) := by
  have hden : Tendsto (fun x : ℝ => x * Real.log x) atTop atTop :=
    Filter.Tendsto.atTop_mul_atTop₀ tendsto_id Real.tendsto_log_atTop
  have hatan : Tendsto Real.arctan atTop (nhds (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right inf_le_left
  have hsmall : Tendsto (fun x : ℝ =>
      8 * Real.arctan x / (x * Real.log x)) atTop (nhds 0) :=
    (hatan.const_mul 8).div_atTop hden
  have h := tendsto_kapustinReciprocalGammaPhase_ratio.sub hsmall
  convert h using 1
  · funext x
    simp only [kapustinOneSidedToeplitzPhase]
    ring
  · norm_num

/-- The oriented phase still grows faster than every linear function. -/
theorem tendsto_kapustinOneSidedToeplitzPhase_div_id_atTop :
    Tendsto (fun x => kapustinOneSidedToeplitzPhase x / x) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  have hratio : ∀ᶠ x : ℝ in atTop,
      (1 / 2 : ℝ) ≤ kapustinOneSidedToeplitzPhase x / (x * Real.log x) :=
    tendsto_kapustinOneSidedToeplitzPhase_ratio.eventually
      (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hlog : ∀ᶠ x : ℝ in atTop, max (2 * B) 0 ≤ Real.log x :=
    (tendsto_atTop.1 Real.tendsto_log_atTop) (max (2 * B) 0)
  have hxone : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  filter_upwards [hratio, hlog, hxone] with x hr hl hx
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hlog0 : 0 ≤ Real.log x := (le_max_right (2 * B) 0).trans hl
  have hmul := mul_le_mul_of_nonneg_right hr hlog0
  have hid :
      (kapustinOneSidedToeplitzPhase x / (x * Real.log x)) * Real.log x =
        kapustinOneSidedToeplitzPhase x / x := by
    field_simp [hxpos.ne', hlogpos.ne']
  rw [hid] at hmul
  have hB : B ≤ (1 / 2 : ℝ) * Real.log x := by
    have : 2 * B ≤ Real.log x := (le_max_left (2 * B) 0).trans hl
    linarith
  exact hB.trans (by simpa only [one_div, invOf_eq_inv] using hmul)

/-- Superlinear reciprocal-Gamma growth excludes every monotone-inner/weak-outer big-`O`
decomposition of the oriented phase. -/
theorem noAESmirnovToeplitzWeakPhaseBigOWitness_kapustinOneSidedToeplitzPhase :
    ¬ Nonempty
      (AESmirnovToeplitzWeakPhaseBigOWitness kapustinOneSidedToeplitzPhase) :=
  not_aeSmirnovToeplitzWeakPhaseBigOWitness_of_ratio_tendsto_atTop
    tendsto_kapustinOneSidedToeplitzPhase_div_id_atTop

end RHTower

end
