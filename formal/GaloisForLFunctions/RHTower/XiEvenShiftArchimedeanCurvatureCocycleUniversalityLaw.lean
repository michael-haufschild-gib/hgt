import GaloisForLFunctions.HTGeometry.TrigammaShift
import GaloisForLFunctions.RHTower.CompletedZetaTranslationDefect
import GaloisForLFunctions.RHTower.XiEvenShiftPrimeDefectTelescope

/-!
# Xi even-shift archimedean-curvature cocycle universality

The arbitrary-even rational correction in the completed-Xi prime-defect telescope differentiates
to the genuine completed-zeta archimedean curvature defect.  Its response is the finite sum of
translated shift-two responses and obeys the additive translation-cocycle law.
-/

namespace RHTower

open Complex

noncomputable section

/-- Rational archimedean-curvature response accumulated along the first `m` shift-two steps. -/
def xiEvenShiftArchimedeanCurvatureResponse (m : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range m,
    GaloisForLFunctions.RHTower.completedZetaArchimedeanShiftRational
      (s + (2 * j : ℕ))

/-- The all-even archimedean responses form an additive translation cocycle. -/
theorem xiEvenShiftArchimedeanCurvatureResponse_add
    (m n : ℕ) (s : ℂ) :
    xiEvenShiftArchimedeanCurvatureResponse (m + n) s =
      xiEvenShiftArchimedeanCurvatureResponse m s +
        xiEvenShiftArchimedeanCurvatureResponse n (s + (2 * m : ℕ)) := by
  rw [xiEvenShiftArchimedeanCurvatureResponse, Finset.sum_range_add,
    xiEvenShiftArchimedeanCurvatureResponse,
    xiEvenShiftArchimedeanCurvatureResponse]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  push_cast
  ring

/-- The completed-zeta archimedean curvature defect under `s ↦ s+2m` is the accumulated rational
shift-two response. -/
theorem completedZetaArchimedeanCurvature_evenShift_sub
    (m : ℕ) {s : ℂ} (hs : 2 < s.re) :
    GaloisForLFunctions.RHTower.completedZetaArchimedeanCurvature
          (s + (2 * m : ℕ)) -
        GaloisForLFunctions.RHTower.completedZetaArchimedeanCurvature s =
      xiEvenShiftArchimedeanCurvatureResponse m s := by
  calc
    GaloisForLFunctions.RHTower.completedZetaArchimedeanCurvature
          (s + (2 * m : ℕ)) -
        GaloisForLFunctions.RHTower.completedZetaArchimedeanCurvature s =
        ∑ j ∈ Finset.range m,
          (GaloisForLFunctions.RHTower.completedZetaArchimedeanCurvature
              (s + (2 * (j + 1) : ℕ)) -
            GaloisForLFunctions.RHTower.completedZetaArchimedeanCurvature
              (s + (2 * j : ℕ))) := by
      let f : ℕ → ℂ := fun j =>
        GaloisForLFunctions.RHTower.completedZetaArchimedeanCurvature
          (s + (2 * j : ℕ))
      simpa [f] using (Finset.sum_range_sub f m).symm
    _ = xiEvenShiftArchimedeanCurvatureResponse m s := by
      rw [xiEvenShiftArchimedeanCurvatureResponse]
      apply Finset.sum_congr rfl
      intro j _
      have hsj : 2 < (s + (2 * j : ℕ)).re := by
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        norm_num
        linarith
      have hstep :=
        GaloisForLFunctions.RHTower.completedZetaArchimedeanCurvature_add_two_sub
          (s := s + (2 * j : ℕ)) hsj
      convert hstep using 1
      all_goals
        push_cast
        ring_nf

private theorem hasDerivAt_one_div_add_const
    (s a : ℂ) (h : s + a ≠ 0) :
    HasDerivAt (fun z : ℂ => 1 / (z + a)) (-1 / (s + a) ^ (2 : ℕ)) s := by
  have hbase : HasDerivAt (fun z : ℂ => z + a) 1 s :=
    (hasDerivAt_id s).add_const a
  simpa only [one_div, one_mul, neg_div, add_comm] using! hbase.inv h

/-- The derivative of the arbitrary-even Xi prime correction is its accumulated rational
archimedean-curvature response. -/
theorem hasDerivAt_xiEvenShiftPrimeCorrection
    (m : ℕ) {s : ℂ} (hs : 2 < s.re) :
    HasDerivAt (xiEvenShiftPrimeCorrection m)
      (xiEvenShiftArchimedeanCurvatureResponse m s) s := by
  have hterm : ∀ j ∈ Finset.range m,
      HasDerivAt
        (fun z : ℂ =>
          1 / (z + (2 * j : ℕ) + 2) +
              1 / (z + (2 * j : ℕ) + 1) -
            1 / (z + (2 * j : ℕ) - 1))
        (GaloisForLFunctions.RHTower.completedZetaArchimedeanShiftRational
          (s + (2 * j : ℕ))) s := by
    intro j _
    have hp2 : s + (2 * j : ℕ) + 2 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      norm_num at hre
      linarith
    have hp1 : s + (2 * j : ℕ) + 1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      norm_num at hre
      linarith
    have hm1 : s + (2 * j : ℕ) - 1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      norm_num at hre
      linarith
    have hd2 := hasDerivAt_one_div_add_const
      s (((2 * j : ℕ) : ℂ) + 2) (by simpa [add_assoc] using hp2)
    have hd1 := hasDerivAt_one_div_add_const
      s (((2 * j : ℕ) : ℂ) + 1) (by simpa [add_assoc] using hp1)
    have hdm1 := hasDerivAt_one_div_add_const
      s (((2 * j : ℕ) : ℂ) - 1) (by
        simpa [sub_eq_add_neg, add_assoc] using hm1)
    simpa only [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg, add_assoc] using!
      ((hd2.add hd1).sub hdm1).congr_deriv (by
        simp only [
          GaloisForLFunctions.RHTower.completedZetaArchimedeanShiftRational,
          sub_eq_add_neg, add_assoc]
        ring)
  have hsum := HasDerivAt.sum (u := Finset.range m) hterm
  change HasDerivAt
    (fun z : ℂ => ∑ j ∈ Finset.range m,
      (1 / (z + (2 * j : ℕ) + 2) + 1 / (z + (2 * j : ℕ) + 1) -
        1 / (z + (2 * j : ℕ) - 1)))
    (xiEvenShiftArchimedeanCurvatureResponse m s) s
  rw [xiEvenShiftArchimedeanCurvatureResponse]
  simpa only using!
    hsum.congr_of_eventuallyEq (by
      filter_upwards with z
      simp only [Finset.sum_apply])

/-- **Xi even-shift archimedean-curvature cocycle universality law.**  On the right half-plane,
the derivative of the arbitrary-even Xi prime correction is exactly the genuine completed-zeta
archimedean curvature defect across the same shift. -/
theorem xiEvenShiftPrimeCorrection_deriv_eq_archimedeanCurvatureDefect
    (m : ℕ) {s : ℂ} (hs : 2 < s.re) :
    deriv (xiEvenShiftPrimeCorrection m) s =
      GaloisForLFunctions.RHTower.completedZetaArchimedeanCurvature
          (s + (2 * m : ℕ)) -
        GaloisForLFunctions.RHTower.completedZetaArchimedeanCurvature s := by
  calc
    deriv (xiEvenShiftPrimeCorrection m) s =
        xiEvenShiftArchimedeanCurvatureResponse m s :=
      (hasDerivAt_xiEvenShiftPrimeCorrection m hs).deriv
    _ = GaloisForLFunctions.RHTower.completedZetaArchimedeanCurvature
          (s + (2 * m : ℕ)) -
        GaloisForLFunctions.RHTower.completedZetaArchimedeanCurvature s :=
      (completedZetaArchimedeanCurvature_evenShift_sub m hs).symm

end

end RHTower
