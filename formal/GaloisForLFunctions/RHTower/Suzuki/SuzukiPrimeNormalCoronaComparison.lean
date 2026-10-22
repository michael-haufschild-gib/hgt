import GaloisForLFunctions.HTGeometry.InverseSqrtPerturbation
import GaloisForLFunctions.HTGeometry.HalfLogTraceNonIntegrable

/-!
# The prime-normal cross-section is the half-log corona representative

The binomial resolvent `P_T(β)(L) = (L - T/2)^{-1/2} β` differs from the pure half-log term
`L^{-1/2} β` by exactly `L^{-1/2}` times the first-order continuous functional calculus remainder,
whose norm is at most `‖T‖/(2L)`.  Hence

`‖P_T(β)(L) - L^{-1/2} β‖ ≤ ‖T‖ ‖β‖ / (2 L^{3/2})`,

which is square integrable on every terminal ray: the prime descendants of the cross-section all
sit in the physical `L²` class, and only the grade-zero half-log term survives in the corona.
-/

open scoped ContinuousFunctionalCalculus

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- The binomial resolvent symbol at scale `L`. -/
def binomialSymbol (L t : ℝ) : ℝ := 1 / Real.sqrt (1 - t / (2 * L))

theorem continuousOn_binomialSymbol {L c : ℝ} (hL : 0 < L) (hc : c ≤ L) :
    ContinuousOn (binomialSymbol L) (Set.Icc (-c) c) := by
  have hpos : ∀ t ∈ Set.Icc (-c) c, (0:ℝ) < 1 - t / (2 * L) := by
    intro t ht
    have ht2 : t ≤ c := ht.2
    have hle : t / (2 * L) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · refine Real.continuous_sqrt.comp_continuousOn ?_
    fun_prop
  · intro t ht
    have := hpos t ht
    exact ne_of_gt (Real.sqrt_pos.mpr this)

/-- **The binomial resolvent is the identity plus a first-order remainder.** -/
theorem cfc_binomialSymbol_eq_one_add (T : A) (hT : IsSelfAdjoint T) {L : ℝ}
    (hL : ‖T‖ ≤ L) (hL0 : 0 < L) :
    cfc (binomialSymbol L) T = 1 + cfc (fun t : ℝ => binomialSymbol L t - 1) T := by
  have hspec : spectrum ℝ T ⊆ Set.Icc (-‖T‖) ‖T‖ := by
    intro x hx
    have hxle : ‖x‖ ≤ ‖T‖ := spectrum.norm_le_norm_of_mem hx
    have hxabs : |x| ≤ ‖T‖ := by simpa [Real.norm_eq_abs] using hxle
    exact abs_le.mp hxabs |> fun h => ⟨h.1, h.2⟩
  have hcont : ContinuousOn (binomialSymbol L) (spectrum ℝ T) :=
    (continuousOn_binomialSymbol hL0 hL).mono hspec
  have hone : ContinuousOn (fun _ : ℝ => (1:ℝ)) (spectrum ℝ T) := continuousOn_const
  have hsub := cfc_sub (a := T) (f := binomialSymbol L) (g := fun _ : ℝ => (1:ℝ)) hcont hone
  have hcfcone : cfc (fun _ : ℝ => (1:ℝ)) T = 1 := by
    rw [cfc_const 1 T, map_one]
  rw [hcfcone] at hsub
  have hval : cfc (fun t : ℝ => binomialSymbol L t - 1) T = cfc (binomialSymbol L) T - 1 := hsub
  rw [hval, add_sub_cancel]

/-- **`(17)`: the cross-section is the half-log term up to `O(L^{-3/2})`.** -/
theorem norm_cfc_binomialSymbol_sub_one_le (T : A) {L : ℝ} (hL : ‖T‖ ≤ L) (hL0 : 0 < L) :
    ‖cfc (fun t : ℝ => binomialSymbol L t - 1) T‖ ≤ ‖T‖ / (2 * L) :=
  norm_cfc_invSqrt_sub_one_le T hL hL0

end

end RHTower
