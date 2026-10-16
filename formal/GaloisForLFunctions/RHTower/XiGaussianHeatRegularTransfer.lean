import GaloisForLFunctions.RHTower.XiGaussianHeatBlockJacobiCensus
import GaloisForLFunctions.HTGeometry.MomentNormalBlockRecurrence
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Exact polynomial transfer on the canonical heat-moment ladder

At every positive heat time, the regular heads form a polynomial Euclidean
chain. Its quotients have exactly the singular-gap degrees and its edges
are nonzero. A companion solution gives a polynomial frame with constant
nonzero determinant, hence a Bezout certificate and no common complex root
at adjacent regular heads. No positivity or nonsingular intermediate pivot
is assumed.
-/

open Polynomial Matrix HTGeometry
namespace RHTower
noncomputable section

/-- Canonical admission at the `j`th regular head. -/
def heatRegularAdmission (a : {t : ℝ // 0 < t}) (j : ℕ) : ℝ[X] :=
  monicMomentAdmissionPolynomial (heatRealMoments a) (heatRegularHead a j)

/-- First nonzero moment coupling after the `j`th regular head. -/
def heatRegularCoupling (a : {t : ℝ // 0 < t}) (j : ℕ) : ℝ :=
  momentBlockCoupling (heatRealMoments a) (heatRegularHead a j) (heatRegularGap a j)

/-- Monic polynomial quotient crossing the whole `j`th singular gap. -/
def heatRegularQuotient (a : {t : ℝ // 0 < t}) (j : ℕ) : ℝ[X] :=
  momentBlockQuotient (heatRealMoments a) (heatRegularHead a j) (heatRegularGap a j)

/-- Nonzero edge between two consecutive normal blocks. -/
def heatRegularEdge (a : {t : ℝ // 0 < t}) (j : ℕ) : ℝ :=
  heatRegularCoupling a (j + 1) / heatRegularCoupling a j

@[simp] theorem heatRegularAdmission_zero (a : {t : ℝ // 0 < t}) :
    heatRegularAdmission a 0 = 1 := by
  simp [heatRegularAdmission, heatRegularHead, monicMomentAdmissionPolynomial_eq,
    Polynomial.ofFn_eq_sum_monomial]

theorem heatRegularCoupling_ne_zero (a : {t : ℝ // 0 < t}) (j : ℕ) :
    heatRegularCoupling a j ≠ 0 :=
  (heatRegularGap_normalBlock a j).coupling_ne

theorem heatRegularEdge_ne_zero (a : {t : ℝ // 0 < t}) (j : ℕ) :
    heatRegularEdge a j ≠ 0 :=
  div_ne_zero (heatRegularCoupling_ne_zero a (j + 1)) (heatRegularCoupling_ne_zero a j)

theorem heatRegularQuotient_monic_degree (a : {t : ℝ // 0 < t}) (j : ℕ) :
    (heatRegularQuotient a j).Monic ∧
      (heatRegularQuotient a j).natDegree = heatRegularGap a j :=
  ⟨momentBlockQuotient_monic _ _ _, momentBlockQuotient_natDegree _ _ _⟩

/-- The actual all-time recurrence skips every singular intermediate pivot. -/
theorem hcf_regular_head_recurrence (a : {t : ℝ // 0 < t}) (j : ℕ) :
    heatRegularAdmission a (j + 2) =
      heatRegularQuotient a (j + 1) * heatRegularAdmission a (j + 1) -
        C (heatRegularEdge a j) * heatRegularAdmission a j := by
  have h₁ : MomentNormalBlock (heatRealMoments a)
      (heatRegularHead a j + heatRegularGap a j) (heatRegularGap a (j + 1)) := by
    rw [heatRegularHead_add_gap]
    exact heatRegularGap_normalBlock a (j + 1)
  simpa only [heatRegularAdmission, heatRegularQuotient, heatRegularEdge,
    heatRegularCoupling, heatRegularHead_add_gap] using
    (heatRegularGap_normalBlock a j).admission_recurrence h₁

/-- Each Euclidean remainder is exactly the preceding canonical admission,
up to a specified nonzero scalar; the entire singular gap is retained. -/
theorem hcf_regular_head_euclidean_step (a : {t : ℝ // 0 < t}) (j : ℕ) :
    heatRegularEdge a j ≠ 0 ∧
      (heatRegularQuotient a (j + 1)).Monic ∧
      (heatRegularQuotient a (j + 1)).natDegree = heatRegularGap a (j + 1) ∧
      heatRegularAdmission a (j + 2) /ₘ heatRegularAdmission a (j + 1) =
        heatRegularQuotient a (j + 1) ∧
      heatRegularAdmission a (j + 2) %ₘ heatRegularAdmission a (j + 1) =
        -C (heatRegularEdge a j) * heatRegularAdmission a j := by
  refine ⟨heatRegularEdge_ne_zero a j, (heatRegularQuotient_monic_degree a (j + 1)).1,
    (heatRegularQuotient_monic_degree a (j + 1)).2, ?_, ?_⟩
  · simp only [heatRegularAdmission, heatRegularQuotient, momentBlockQuotient,
      heatRegularHead_add_gap]
  · have h₁ : MomentNormalBlock (heatRealMoments a)
        (heatRegularHead a j + heatRegularGap a j) (heatRegularGap a (j + 1)) := by
      rw [heatRegularHead_add_gap]
      exact heatRegularGap_normalBlock a (j + 1)
    simpa only [heatRegularAdmission, heatRegularEdge, heatRegularCoupling,
      heatRegularHead_add_gap] using
      (heatRegularGap_normalBlock a j).admission_remainder h₁

/-- Companion solution, normalized by the initial source coupling. -/
def heatRegularCompanion (a : {t : ℝ // 0 < t}) : ℕ → ℝ[X]
  | 0 => 0
  | 1 => C (heatRegularCoupling a 0)
  | j + 2 => heatRegularQuotient a (j + 1) * heatRegularCompanion a (j + 1) -
      C (heatRegularEdge a j) * heatRegularCompanion a j

@[simp] theorem heatRegularCompanion_zero (a : {t : ℝ // 0 < t}) :
    heatRegularCompanion a 0 = 0 := rfl

@[simp] theorem heatRegularCompanion_one (a : {t : ℝ // 0 < t}) :
    heatRegularCompanion a 1 = C (heatRegularCoupling a 0) := rfl

theorem heatRegularCompanion_recurrence (a : {t : ℝ // 0 < t}) (j : ℕ) :
    heatRegularCompanion a (j + 2) =
      heatRegularQuotient a (j + 1) * heatRegularCompanion a (j + 1) -
        C (heatRegularEdge a j) * heatRegularCompanion a j := rfl

/-- The two polynomial solutions have a constant, explicitly nonzero
Casoratian, equal to minus the first surviving source coupling. -/
theorem hcf_regular_head_casoratian (a : {t : ℝ // 0 < t}) (j : ℕ) :
    heatRegularAdmission a (j + 1) * heatRegularCompanion a j -
      heatRegularCompanion a (j + 1) * heatRegularAdmission a j =
        C (-heatRegularCoupling a j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      _ = C (heatRegularEdge a j) *
          (heatRegularAdmission a (j + 1) * heatRegularCompanion a j -
            heatRegularCompanion a (j + 1) * heatRegularAdmission a j) := by
        rw [hcf_regular_head_recurrence, heatRegularCompanion_recurrence]
        ring
      _ = C (heatRegularEdge a j) * C (-heatRegularCoupling a j) := by rw [ih]
      _ = C (-heatRegularCoupling a (j + 1)) := by
        rw [← C_mul, mul_neg, heatRegularEdge,
          div_mul_cancel₀ _ (heatRegularCoupling_ne_zero a j)]

/-- Explicit Bezout coefficients for adjacent regular-head admissions. -/
theorem hcf_regular_head_bezout (a : {t : ℝ // 0 < t}) (j : ℕ) :
    (C ((heatRegularCoupling a j)⁻¹) * heatRegularCompanion a (j + 1)) *
        heatRegularAdmission a j +
      (-(C ((heatRegularCoupling a j)⁻¹) * heatRegularCompanion a j)) *
        heatRegularAdmission a (j + 1) = 1 := by
  have hw : heatRegularCompanion a (j + 1) * heatRegularAdmission a j -
      heatRegularCompanion a j * heatRegularAdmission a (j + 1) =
        C (heatRegularCoupling a j) := by
    have h := hcf_regular_head_casoratian a j
    rw [C_neg] at h
    linear_combination -h
  calc
    _ = C ((heatRegularCoupling a j)⁻¹) *
        (heatRegularCompanion a (j + 1) * heatRegularAdmission a j -
          heatRegularCompanion a j * heatRegularAdmission a (j + 1)) := by ring
    _ = 1 := by
      rw [hw, ← C_mul, inv_mul_cancel₀ (heatRegularCoupling_ne_zero a j), C_1]

/-- Coprimality holds at every positive time, including indefinite sections
and arbitrary runs of zero Hankel pivots. -/
theorem hcf_regular_head_coprime (a : {t : ℝ // 0 < t}) (j : ℕ) :
    IsCoprime (heatRegularAdmission a j) (heatRegularAdmission a (j + 1)) :=
  ⟨_, _, hcf_regular_head_bezout a j⟩

theorem hcf_regular_head_no_common_root (a : {t : ℝ // 0 < t}) (j : ℕ) (z : ℂ) :
    aeval z (heatRegularAdmission a j) ≠ 0 ∨
      aeval z (heatRegularAdmission a (j + 1)) ≠ 0 :=
  aeval_ne_zero_of_isCoprime (hcf_regular_head_coprime a j) z

/-- Polynomial frame of the two independent canonical solutions. -/
def heatRegularFrame (a : {t : ℝ // 0 < t}) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ[X] :=
  !![heatRegularAdmission a (j + 1), heatRegularCompanion a (j + 1);
     heatRegularAdmission a j, heatRegularCompanion a j]

/-- One step of polynomial transfer across a complete normal block. -/
def heatRegularTransfer (a : {t : ℝ // 0 < t}) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ[X] :=
  !![heatRegularQuotient a (j + 1), -C (heatRegularEdge a j); 1, 0]

theorem heatRegularFrame_det (a : {t : ℝ // 0 < t}) (j : ℕ) :
    (heatRegularFrame a j).det = C (-heatRegularCoupling a j) := by
  rw [heatRegularFrame, Matrix.det_fin_two_of]
  exact hcf_regular_head_casoratian a j

theorem heatRegularTransfer_det (a : {t : ℝ // 0 < t}) (j : ℕ) :
    (heatRegularTransfer a j).det = C (heatRegularEdge a j) := by
  simp [heatRegularTransfer, Matrix.det_fin_two_of]

/-- The canonical polynomial frame and every step are invertible over the
polynomial ring itself, and the transfer equation is exact. -/
theorem hcf_regular_head_transfer (a : {t : ℝ // 0 < t}) (j : ℕ) :
    IsUnit (heatRegularFrame a j) ∧ IsUnit (heatRegularTransfer a j) ∧
      heatRegularFrame a (j + 1) = heatRegularTransfer a j * heatRegularFrame a j := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, heatRegularFrame_det, isUnit_C, isUnit_iff_ne_zero]
    simpa using heatRegularCoupling_ne_zero a j
  · rw [Matrix.isUnit_iff_isUnit_det, heatRegularTransfer_det, isUnit_C, isUnit_iff_ne_zero]
    exact heatRegularEdge_ne_zero a j
  · rw [heatRegularTransfer, heatRegularFrame, heatRegularFrame, Matrix.mul_fin_two]
    simp only [neg_mul, one_mul, zero_mul, add_zero, ← sub_eq_add_neg]
    rw [hcf_regular_head_recurrence, heatRegularCompanion_recurrence]

end
end RHTower
