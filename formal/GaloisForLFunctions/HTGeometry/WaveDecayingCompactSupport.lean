import GaloisForLFunctions.HTGeometry.WaveEnergyDecaying
import GaloisForLFunctions.HTGeometry.WaveGreenIdentityIntegrable

/-!
# Compactly supported solutions are decaying solutions

The hypothesis class of the previous file has to be inhabited by something other than the zero
field, or the estimate proved for it says nothing. It is: every smooth solution with spatially
compact support satisfies all of its conditions, each integrand being continuous with compact
support and the dominating function being the supremum on a compact box. So the decaying layer
subsumes the compactly supported one rather than replacing it with an empty class.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Subsumption

variable {d : ℕ} {u V : ℝ × (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)}

theorem hasCompactSupport_slice_dirDeriv (hK : IsCompact K)
    (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0) (v : ℝ × (Fin d → ℝ)) (t : ℝ) :
    HasCompactSupport (slice (waveDirDeriv v u) t) :=
  HasCompactSupport.intro hK fun x hx => waveDirDeriv_zero_of_notMem hK hzero v (t, x) hx

/-- **A smooth solution with spatially compact support is a decaying solution.** -/
theorem decayingSolution_of_hasCompactSupport (hu : ContDiff ℝ ∞ u) (hV : Continuous V)
    (hK : IsCompact K) (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0)
    (hsolve : SolvesWaveEq u V) : DecayingSolution u V := by
  have hEcd : ContDiff ℝ ∞ (energyDensity u) := contDiff_energyDensity hu
  have hslice : ∀ t : ℝ, ContDiff ℝ ∞ (slice u t) := fun t => contDiff_slice hu t
  have hsliceD : ∀ t : ℝ, ContDiff ℝ ∞ (slice (waveDirDeriv (timeDir d) u) t) :=
    fun t => contDiff_slice (contDiff_dirDeriv hu _) t
  have hsuppF : ∀ t : ℝ, HasCompactSupport (slice u t) :=
    fun t => hasCompactSupport_slice hK hzero t
  have hsuppG : ∀ t : ℝ, HasCompactSupport (slice (waveDirDeriv (timeDir d) u) t) :=
    fun t => hasCompactSupport_slice_dirDeriv hK hzero _ t
  refine
    { smooth := hu
      solves := hsolve
      energyInt := fun t => integrable_energyDensity_slice hu hK hzero t
      greenInt₁ := fun t i => ?_
      greenInt₂ := fun t i => ?_
      greenInt₃ := fun t i => ?_
      fluxInt := fun t => ?_
      dominated := fun t => ?_ }
  · refine integrable_of_continuous_compactSupport ?_ ?_
    · exact ((contDiff_coordPartial (contDiff_coordPartial (hslice t) i) i).continuous).mul
        (hsliceD t).continuous
    · exact (hasCompactSupport_coordPartial (hasCompactSupport_coordPartial (hsuppF t) i)
        i).mul_right
  · refine integrable_of_continuous_compactSupport ?_ ?_
    · exact ((contDiff_coordPartial (hslice t) i).continuous).mul
        (contDiff_coordPartial (hsliceD t) i).continuous
    · exact (hasCompactSupport_coordPartial (hsuppF t) i).mul_right
  · refine integrable_of_continuous_compactSupport ?_ ?_
    · exact ((contDiff_coordPartial (hslice t) i).continuous).mul (hsliceD t).continuous
    · exact (hasCompactSupport_coordPartial (hsuppF t) i).mul_right
  · have hmap : Continuous fun x : Fin d → ℝ => ((t, x) : ℝ × (Fin d → ℝ)) := by fun_prop
    have hcont : Continuous fun x : Fin d → ℝ =>
        (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x)) :=
      ((hV.comp hmap).add continuous_const).mul
        ((hu.continuous.comp hmap).mul ((contDiff_dirDeriv hu _).continuous.comp hmap))
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hK fun x hx => ?_
    show (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x)) = 0
    rw [hzero (t, x) hx, zero_mul, mul_zero]
  · -- the dominating function: the supremum on a compact box, supported on `K`
    classical
    have hF'cont : Continuous (waveDirDeriv (timeDir d) (energyDensity u)) :=
      (contDiff_dirDeriv hEcd _).continuous
    have hE0 : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → energyDensity u p = 0 :=
      energyDensity_zero_of_notMem hK hzero
    have hF'0 : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K →
        waveDirDeriv (timeDir d) (energyDensity u) p = 0 :=
      fun p hp => waveDirDeriv_zero_of_notMem hK hE0 _ p hp
    obtain ⟨C, hC⟩ := ((isCompact_Icc (a := t - 1) (b := t + 1)).prod hK).exists_bound_of_continuousOn hF'cont.continuousOn
    refine ⟨Set.indicator K fun _ : Fin d → ℝ => C, ?_, ?_⟩
    · rw [integrable_indicator_iff hK.measurableSet]
      exact integrableOn_const hK.measure_lt_top.ne
    · intro s hs x
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        refine hC (s, x) ⟨?_, hx⟩
        have hsabs : |s - t| < 1 := by
          rw [Metric.mem_ball, Real.dist_eq] at hs
          exact hs
        have hlt := abs_lt.mp hsabs
        exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
      · rw [Set.indicator_of_notMem hx, hF'0 (s, x) hx, norm_zero]

end Subsumption

end GaloisForLFunctions.HTGeometry
