import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanPrincipalPart

/-!
# The regular half-plane of the averaged Narain transform

Central cancellation removes the apparent pole at zero. Arithmetic
nonvanishing then gives analyticity up to the boundary and isolates the
universal meromorphic main pole.
-/

open Complex RHTower Set Filter Topology
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Cancellation at the centre leaves only the arithmetic denominator and the main pole. -/
theorem analyticAt_narainMellinMean_of_regular (Y Z : Height) {u : ℂ}
    (hregular : (1 + 2 * u) * xi (1 + 2 * u) ≠ 0) (hmain : u ≠ 1 / 2) :
    AnalyticAt ℂ (narainMellinMean Y Z) u := by
  have hA := analyticAt_narainMeanMainPoleNumerator Y Z hregular
  have hden : AnalyticAt ℂ (fun v : ℂ => (v - 1 / 2) ^ 2) u := by fun_prop
  apply (hA.div hden (pow_ne_zero 2 (sub_ne_zero.mpr hmain))).congr
  filter_upwards [isOpen_ne.mem_nhds hmain] with v hv
  have htwo : 2 * v - 1 ≠ 0 := by
    intro h
    apply hv
    linear_combination h / 2
  symm
  apply (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr hv))).mpr
  rw [narainMeanMainPoleNumerator_eq Y Z htwo, mul_comm]

/-- The actual mean is holomorphic on the closed right half-plane away from its main pole. -/
theorem analyticAt_narainMellinMean_of_nonneg_re (Y Z : Height) {u : ℂ}
    (hu : 0 ≤ u.re) (hmain : u ≠ 1 / 2) :
    AnalyticAt ℂ (narainMellinMean Y Z) u := by
  have hD : xi (1 + 2 * u) ≠ 0 :=
    xi_ne_zero_of_one_le_re (by simp; linarith only [hu])
  have hlin : 1 + 2 * u ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith only [hu, h']
  exact analyticAt_narainMellinMean_of_regular Y Z (mul_ne_zero hlin hD) hmain

/-- Continuity on each vertical line that avoids the universal main pole. -/
theorem continuous_narainMellinMean_vertical (Y Z : Height) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≠ 1 / 2) :
    Continuous (fun t : ℝ => narainMellinMean Y Z ((a : ℂ) + t * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hre : ((a : ℂ) + t * I).re = a := by simp
  have hn : (a : ℂ) + t * I ≠ 1 / 2 := by
    intro h
    apply ha'
    have h' := congrArg Complex.re h
    simpa using h'
  exact ContinuousAt.comp (g := narainMellinMean Y Z)
    (f := fun t : ℝ => (a : ℂ) + t * I) (x := t)
    (analyticAt_narainMellinMean_of_nonneg_re Y Z (by simpa using ha) hn).continuousAt
    (by fun_prop)

/-- The only singularity crossed from the Euler line to the boundary is meromorphic. -/
theorem meromorphicAt_narainMellinMean_shift_one (Y Z : Height) :
    MeromorphicAt (fun s : ℂ => narainMellinMean Y Z (s - 1 / 2)) 1 := by
  have hA := analyticAt_narainMeanMainPoleNumerator Y Z (u := 1 / 2)
    (by norm_num [xi_two_ne_zero])
  have hshift : AnalyticAt ℂ (fun s : ℂ => s - 1 / 2) 1 := by fun_prop
  have hAs : AnalyticAt ℂ (fun s : ℂ => narainMeanMainPoleNumerator Y Z (s - 1 / 2)) 1 :=
    AnalyticAt.comp (g := narainMeanMainPoleNumerator Y Z)
      (f := fun s : ℂ => s - 1 / 2) (x := 1)
      (by rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring]; exact hA) hshift
  have hd : AnalyticAt ℂ (fun s : ℂ => (s - 1) ^ 2) 1 := by fun_prop
  apply (hAs.meromorphicAt.div hd.meromorphicAt).congr
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : s ≠ 1 := by simpa using hs
  have htwo : 2 * (s - 1 / 2) - 1 ≠ 0 := by
    intro h
    apply hne
    linear_combination h / 2
  symm
  apply (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr hne))).mpr
  dsimp only
  rw [narainMeanMainPoleNumerator_eq Y Z htwo]
  ring

#print axioms analyticAt_narainMellinMean_of_regular
#print axioms meromorphicAt_narainMellinMean_shift_one
#print axioms analyticAt_narainMellinMean_of_nonneg_re
#print axioms continuous_narainMellinMean_vertical
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
