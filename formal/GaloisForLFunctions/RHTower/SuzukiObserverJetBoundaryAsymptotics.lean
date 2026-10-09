import GaloisForLFunctions.RHTower.SuzukiObserverJetFormation
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Vanishing normalized observer boundary

For any convergent sequence of partial charges, the first moment divided by the
aperture tends to zero: it is the difference between the final partial charge
and its Cesaro mean. Applied to the literal completed source, the mass tends to
zero and the normalized mass--drift boundary vanishes unconditionally.

Thus the normalized Abel moment differs from the normalized signed
curvature-history sum by a quantity tending to zero. No bound for that history
sum is assumed or proved here, and the RH growth estimate remains open.
-/

open Set Filter Topology
open scoped BigOperators
noncomputable section


namespace GaloisForLFunctions.HTGeometry

theorem observerJetDrift_eq_mass_mul_succ_sub_prefixSum (q : ℕ → ℝ) (N : ℕ) :
    observerJetDrift q N = ((N : ℝ) + 1) * observerJetMass q N -
      ∑ k ∈ Finset.range (N + 1), observerJetMass q k := by
  induction N with
  | zero => simp [observerJetDrift, observerJetMass]
  | succ N ih =>
    have hd : observerJetDrift q (N + 1) = observerJetDrift q N +
        ((N : ℝ) + 1) * q (N + 1) := by
      simp [observerJetDrift, Finset.sum_range_succ]
    have hm : observerJetMass q (N + 1) = observerJetMass q N + q (N + 1) := by
      simp [observerJetMass, Finset.sum_range_succ]
    rw [hd, Finset.sum_range_succ, hm, ih]
    push_cast
    ring

theorem tendsto_observerJetDrift_div_succ_zero
    {q : ℕ → ℝ} {s : ℝ}
    (hq : Tendsto (observerJetMass q) atTop (𝓝 s)) :
    Tendsto (fun N : ℕ => observerJetDrift q N / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have hmean := hq.cesaro.comp (tendsto_add_atTop_nat 1)
  have hsub := hq.sub hmean
  simp only [sub_self] at hsub
  apply hsub.congr'
  filter_upwards with N
  rw [observerJetDrift_eq_mass_mul_succ_sub_prefixSum]
  simp only [Function.comp_apply]
  push_cast
  have hn : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower GaloisForLFunctions.HTGeometry

theorem tendsto_completedSourceObserverJetMass_zero :
    Tendsto completedSourceObserverJetMass atTop (𝓝 0) := by
  have hq : Tendsto (observerJetMass completedPrimePolarGammaHarmonicCharge)
      atTop (𝓝 0) := by
    exact tendsto_completedPrimePolarGammaHarmonicPrefix_zero
  apply (tendsto_add_atTop_iff_nat 2).mp
  simpa only [completedSourceObserverJetMass, Nat.add_sub_cancel] using hq

theorem tendsto_completedSourceObserverJetDrift_div_aperture_zero :
    Tendsto (fun M : ℕ => completedSourceObserverJetDrift M / (M : ℝ))
      atTop (𝓝 0) := by
  have hq : Tendsto (observerJetMass completedPrimePolarGammaHarmonicCharge)
      atTop (𝓝 0) := by
    exact tendsto_completedPrimePolarGammaHarmonicPrefix_zero
  have hd := tendsto_observerJetDrift_div_succ_zero hq
  have hn : Tendsto (fun N : ℕ => ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hi : Tendsto (fun N : ℕ => (1 : ℝ) / ((N + 2 : ℕ) : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hn
  have hr : Tendsto (fun N : ℕ => (1 : ℝ) - 1 / ((N + 2 : ℕ) : ℝ))
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hi
  have hp := hd.mul hr
  apply (tendsto_add_atTop_iff_nat 2).mp
  convert hp using 1
  · funext N
    simp only [completedSourceObserverJetDrift, Nat.add_sub_cancel]
    push_cast
    have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : (N : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  · norm_num

theorem tendsto_completedSourceObserverJetBoundary_div_aperture_zero :
    Tendsto (fun M : ℕ =>
      (completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0 +
        completedSourceObserverJetDrift M *
          (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0)) /
        (M : ℝ)) atTop (𝓝 0) := by
  have hm : Tendsto (fun M : ℕ => completedSourceObserverJetMass M / (M : ℝ))
      atTop (𝓝 0) := tendsto_completedSourceObserverJetMass_zero.div_atTop
        tendsto_natCast_atTop_atTop
  have h := (hm.mul_const (completedRieszHarmonicClockRatio 0)).add
    (tendsto_completedSourceObserverJetDrift_div_aperture_zero.mul_const
      (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0))
  convert h using 1
  · funext M
    ring
  · simp

theorem tendsto_mobiusDivisorSquareRootAbel_sub_curvatureHistory_div_zero :
    Tendsto (fun M : ℕ => mobiusDivisorSquareRootAbelMoment M / (M : ℝ) -
      (∑ j ∈ Finset.range (M - 3), completedSourceObserverJetHistory M j *
        observerJetCurvature completedRieszHarmonicClockRatio j) / (M : ℝ))
      atTop (𝓝 0) := by
  apply tendsto_completedSourceObserverJetBoundary_div_aperture_zero.congr'
  filter_upwards [eventually_ge_atTop 3] with M hM
  rw [mobiusDivisorSquareRootAbelMoment_eq_completedSourceObserverJet hM]
  ring

end GaloisForLFunctions.RHTower
