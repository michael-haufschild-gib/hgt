import GaloisForLFunctions.RHTower.WeilLogShiftObservableLaw

/-! Exact weighted covariance and Chebyshev positivity for finite probability laws. -/

open GaloisForLFunctions.HTGeometry.FourierLLogL
open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilLaw_covariance_pairwise {ι : Type*} [Fintype ι]
    (P : Law ι) (f g : ι → ℝ) :
    (∑ i, ∑ j, P i * P j * (f i - f j) * (g i - g j)) =
      2 * (P.Ex (fun i => f i * g i) - P.Ex f * P.Ex g) := by
  have hrow (i : ι) :
      (∑ j, P i * P j * (f i - f j) * (g i - g j)) =
        P i * (f i * g i) - (P i * f i) * P.Ex g -
          (P i * g i) * P.Ex f + P i * P.Ex (fun j => f j * g j) := by
    calc
      _ = (P i * (f i * g i)) * (∑ j, P j) -
          (P i * f i) * (∑ j, P j * g j) -
          (P i * g i) * (∑ j, P j * f j) +
          P i * (∑ j, P j * (f j * g j)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by simp only [P.total, mul_one, Law.Ex]
  calc
    _ = ∑ i, (P i * (f i * g i) - (P i * f i) * P.Ex g -
        (P i * g i) * P.Ex f + P i * P.Ex (fun j => f j * g j)) :=
      Finset.sum_congr rfl fun i _ => hrow i
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, P.total, one_mul]
      simp only [Law.Ex]
      ring

theorem finiteWeilLaw_monotone_covariance_nonneg {ι : Type*} [Fintype ι] [LinearOrder ι]
    (P : Law ι) (f g : ι →o ℝ) :
    P.Ex f * P.Ex g ≤ P.Ex (fun i => f i * g i) := by
  have h : 0 ≤ ∑ i, ∑ j, P i * P j * (f i - f j) * (g i - g j) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    have hp : 0 ≤ (f i - f j) * (g i - g j) := by
      rcases le_total i j with hij | hji
      · exact mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr (f.monotone hij)) (sub_nonpos.mpr (g.monotone hij))
      · exact mul_nonneg
          (sub_nonneg.mpr (f.monotone hji)) (sub_nonneg.mpr (g.monotone hji))
    simpa only [mul_assoc] using mul_nonneg (mul_nonneg (P.nonneg i) (P.nonneg j)) hp
  rw [finiteWeilLaw_covariance_pairwise] at h
  linarith only [h]

end RHTower
