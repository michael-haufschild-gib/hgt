import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.RelativeStabilityOfTheTangentFamily
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheSecondDampingTangentAndConvexity
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ThePronicDilationContractionAndItsThreshold

/-!
# Second-tangent control gives the angle

The autocorrelation's sign is an angle condition: the tangents at two dampings must not differ by
more than the tangent's own size.  The mean value theorem turns that into a comparison between the
*second* tangent and the first.  If on the damping interval the second tangent has a pointwise
majorant `G`, then

`‖E_η − E_ε‖_T ≤ (ε − η) ‖G‖_T`  (`pronicNorm_dampedChebyshevError_sub_le`),

so the angle is non-obtuse as soon as the gap times `‖G‖_T` is at most `‖E_ε‖_T`
(`nonneg_tangentCorrelation_of_second_tangent_majorant`), and the Riemann hypothesis follows from
that comparison alone (`riemannHypothesis_of_second_tangent_majorant`).

This is the local form of the relative-stability criterion: the obstruction is not the size of the
tangent, nor the size of the second tangent, but their *ratio against the gap*.  Short damping steps
cost nothing, so the criterion can be applied on a fine partition of the damping range — which is
exactly what the sign criterion needs, since it is pointwise in the pair of dampings.
-/

open Set Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. Pronic monotonicity and the mean value step -/

theorem pronicNorm_le_of_abs_le {T : ℕ} {u v : ℕ → ℝ}
    (h : ∀ n ∈ Finset.Icc 1 T, |u n| ≤ v n) :
    pronicNorm T u ≤ pronicNorm T v := by
  unfold pronicNorm
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have habs := h n hn
  have hsq : u n ^ 2 ≤ v n ^ 2 := by
    have h1 : |u n| ^ 2 = u n ^ 2 := sq_abs _
    nlinarith [abs_nonneg (u n)]
  exact div_le_div_of_nonneg_right hsq (by positivity)

/-- **The tangent moves at most the gap times the second tangent.** -/
theorem pronicNorm_dampedChebyshevError_sub_le {η ε : ℝ} (hη : 0 < η) (hηε : η ≤ ε) (T : ℕ)
    (G : ℕ → ℝ) (hG : ∀ x ∈ Icc η ε, ∀ n : ℕ, |dampedChebyshevSecond x n| ≤ G n) :
    pronicNorm T (fun n => dampedChebyshevError η n - dampedChebyshevError ε n) ≤
      (ε - η) * pronicNorm T G := by
  have hGnonneg : ∀ n : ℕ, 0 ≤ G n := fun n =>
    le_trans (abs_nonneg _) (hG η (left_mem_Icc.mpr hηε) n)
  have hcell : ∀ n ∈ Finset.Icc 1 T,
      |dampedChebyshevError η n - dampedChebyshevError ε n| ≤ (ε - η) * G n := by
    intro n _
    rcases eq_or_lt_of_le hηε with rfl | hlt
    · simp
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
        (fun x => dampedChebyshevError x n) (fun x => dampedChebyshevSecond x n) hlt
        (fun x hx => ((hasDerivAt_dampedChebyshevError (lt_of_lt_of_le hη hx.1) n
          ).continuousAt).continuousWithinAt)
        (fun x hx => hasDerivAt_dampedChebyshevError (lt_of_lt_of_le hη (le_of_lt hx.1)) n)
      have hcmem : c ∈ Icc η ε := ⟨le_of_lt hc.1, le_of_lt hc.2⟩
      have hbound := hG c hcmem n
      have hgap : (0 : ℝ) < ε - η := by linarith
      have hval : dampedChebyshevError ε n - dampedChebyshevError η n =
          dampedChebyshevSecond c n * (ε - η) := by
        rw [hslope]
        field_simp
      have habs : |dampedChebyshevError η n - dampedChebyshevError ε n| =
          |dampedChebyshevSecond c n| * (ε - η) := by
        rw [abs_sub_comm, hval, abs_mul, abs_of_pos hgap]
      rw [habs, mul_comm]
      exact mul_le_mul_of_nonneg_left hbound hgap.le
  have hnorm := pronicNorm_le_of_abs_le (T := T)
    (u := fun n => dampedChebyshevError η n - dampedChebyshevError ε n)
    (v := fun n => (ε - η) * G n) hcell
  rwa [pronicNorm_const_mul (by linarith : (0 : ℝ) ≤ ε - η)] at hnorm

/-! ## §2. The angle, and the criterion -/

/-- **Second-tangent control gives a non-obtuse angle.** -/
theorem nonneg_tangentCorrelation_of_second_tangent_majorant {η ε : ℝ} (hη : 0 < η) (hηε : η ≤ ε)
    (T : ℕ) (G : ℕ → ℝ) (hG : ∀ x ∈ Icc η ε, ∀ n : ℕ, |dampedChebyshevSecond x n| ≤ G n)
    (hgap : (ε - η) * pronicNorm T G ≤ pronicNorm T (dampedChebyshevError ε)) :
    0 ≤ tangentCorrelation T η ε :=
  nonneg_tangentCorrelation_of_relative_stability T η ε
    ((pronicNorm_dampedChebyshevError_sub_le hη hηε T G hG).trans hgap)

/-- **The second-tangent criterion for the Riemann hypothesis.**  A pointwise majorant of the second
tangent whose pronic norm, times the damping gap, stays below the tangent norm at the outer damping
gives RH: a comparison of two successive tangents, with no constant and no norm bound in absolute
terms. -/
theorem riemannHypothesis_of_second_tangent_majorant
    (h : ∀ (T : ℕ) (η ε : ℝ), 0 < η → η ≤ ε → ε ≤ 1 / 2 → ∃ G : ℕ → ℝ,
      (∀ x ∈ Icc η ε, ∀ n : ℕ, |dampedChebyshevSecond x n| ≤ G n) ∧
        (ε - η) * pronicNorm T G ≤ pronicNorm T (dampedChebyshevError ε)) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonneg_tangentCorrelation fun T η ε hη hηε hε => by
    obtain ⟨G, hG, hgap⟩ := h T η ε hη hηε hε
    exact nonneg_tangentCorrelation_of_second_tangent_majorant hη hηε T G hG hgap

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
