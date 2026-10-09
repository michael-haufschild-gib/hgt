import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Thermal.Order

/-! # A genuine Fourier metric for every finite Gibbs law

Strict positivity of the actual Gibbs weights makes the character distance
nondegenerate. Its square is exactly the mean squared distance of the two
characters, so the source triangle inequality yields a genuine metric.
-/

open scoped BigOperators ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Thermal
noncomputable section
variable {M : ℕ}

/-- Full support of a finite Gibbs law separates every nonzero frequency. -/
theorem delta_eq_zero_iff (A : Form M) (s : Grid M) : delta A s = 0 ↔ s = 0 := by
  classical
  constructor
  · intro h
    have he : (label A).Ex (fun y => ‖1-chi s y‖^2) = 0 := by
      have H := Real.sq_sqrt ((label A).Ex_nonneg (fun y => sq_nonneg ‖1-chi s y‖))
      change delta A s ^ 2 = _ at H
      rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at H
      exact H.symm
    have hc (y : Grid M) : chi s y = 1 := by
      have H : label A y * ‖1-chi s y‖^2 ≤ (label A).Ex (fun z => ‖1-chi s z‖^2) :=
        Finset.single_le_sum (f := fun z : Grid M => label A z * ‖1-chi s z‖^2)
          (fun z _ => mul_nonneg (label_pos A z).le (sq_nonneg _)) (Finset.mem_univ y)
      rw [he] at H
      have hp := label_pos A y
      have hz : ‖1-chi s y‖^2 = 0 := by nlinarith [sq_nonneg ‖1-chi s y‖]
      exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm
    by_contra hs
    have H := expU_chi s
    rw [if_neg hs, funext hc, expU_cx] at H
    change (Law.uniform (Grid M)).Cx (fun _ => ((1 : ℝ) : ℂ)) = 0 at H
    rw [Law.Cx_ofReal, Law.Ex_const, Complex.ofReal_one] at H
    exact one_ne_zero H
  · rintro rfl
    exact delta_zero A

/-- Frequency distance is the actual Gibbs mean squared character difference. -/
theorem delta_sub_sq (A : Form M) (x z : Grid M) :
    delta A (x-z)^2 = (label A).Ex (fun y => ‖chi x y - chi z y‖^2) := by
  unfold delta
  rw [Real.sq_sqrt ((label A).Ex_nonneg (fun y => sq_nonneg _))]
  apply congrArg (label A).Ex
  funext y
  have hc : chi (x-z) y = chi x y * conj (chi z y) := by
    rw [chi_comm, chi_sub, chi_comm y x, chi_comm y z]
  rw [norm_phase_sq, Complex.sq_norm, Complex.normSq_sub,
    ← Complex.sq_norm, ← Complex.sq_norm, norm_chi, norm_chi]
  unfold cost wave
  rw [hc]
  ring

theorem delta_sub_self (A : Form M) (x : Grid M) : delta A (x-x) = 0 := by
  rw [sub_self, delta_zero]

theorem delta_sub_comm (A : Form M) (x z : Grid M) : delta A (x-z) = delta A (z-x) := by
  rw [← neg_sub z x, delta_even]

theorem delta_sub_triangle (A : Form M) (x y z : Grid M) :
    delta A (x-z) ≤ delta A (x-y) + delta A (y-z) := by
  simpa only [sub_add_sub_cancel] using delta_triangle A (x-y) (y-z)

/-- The Fourier distance is installed explicitly, avoiding any change to the grid's other metrics. -/
@[implicit_reducible]
def deltaMetric (A : Form M) : MetricSpace (Grid M) where
  dist x z := delta A (x-z)
  dist_self := delta_sub_self A
  dist_comm := delta_sub_comm A
  dist_triangle := delta_sub_triangle A
  eq_of_dist_eq_zero h := sub_eq_zero.mp ((delta_eq_zero_iff A _).mp h)

theorem deltaMetric_dist (A : Form M) (x z : Grid M) :
    @dist (Grid M) (deltaMetric A).toDist x z = delta A (x-z) := rfl

end
end GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Thermal
