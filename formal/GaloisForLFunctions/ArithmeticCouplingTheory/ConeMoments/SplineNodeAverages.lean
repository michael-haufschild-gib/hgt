import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineHeightCorrection

/-!
# Spline moment Jacobians on selected nodes

Equal-weight averaging preserves the ordinary/conjugate decomposition of
real spline node corrections. Row bounds on these two matrices control the
Jacobian defect independently of how the nodes were selected.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Equal-weight averaging over arbitrary real nodes. -/
def splineNodeAverage (x : Fin n → ℝ) (f : ℝ → ℂ) : ℂ :=
  (∑ j, f (x j))/(n:ℂ)

lemma splineNodeAverage_add (x : Fin n → ℝ) (f g : ℝ → ℂ) :
    splineNodeAverage x (fun y => f y+g y)=splineNodeAverage x f+splineNodeAverage x g := by
  simp only [splineNodeAverage,sum_add_distrib,add_div]

lemma splineNodeAverage_sub (x : Fin n → ℝ) (f g : ℝ → ℂ) :
    splineNodeAverage x (fun y => f y-g y)=splineNodeAverage x f-splineNodeAverage x g := by
  simp only [splineNodeAverage,sum_sub_distrib,sub_div]

lemma splineNodeAverage_mul_const (x : Fin n → ℝ) (f : ℝ → ℂ) (c : ℂ) :
    splineNodeAverage x (fun y => f y*c)=splineNodeAverage x f*c := by
  simp only [splineNodeAverage,← sum_mul]
  ring

lemma splineNodeAverage_sum (x : Fin n → ℝ) (f : ι → ℝ → ℂ) :
    splineNodeAverage x (fun y => ∑ i, f i y)=∑ i, splineNodeAverage x (f i) := by
  unfold splineNodeAverage
  rw [sum_comm,sum_div]

lemma norm_splineNodeAverage_le (hn : 0 < n) (x : Fin n → ℝ)
    {f : ℝ → ℂ} {C : ℝ} (hf : ∀ j, ‖f (x j)‖ ≤ C) : ‖splineNodeAverage x f‖ ≤ C := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rw [splineNodeAverage,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ hnR).2
  calc
    _ ≤ ∑ j, ‖f (x j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, C := sum_le_sum fun j _ => hf j
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma splineNodeAverage_slope_correction (x : Fin n → ℝ) (δ : ℝ)
    (t : ι → ℝ) (y : ι → ℂ) (i : ι) :
    splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*
      (splineHeightCorrection δ t y u:ℂ))=
      ∑ j, (splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*splineDual δ (t j) u)*y j+
        splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*
          (starRingEnd ℂ) (splineDual δ (t j) u))*(starRingEnd ℂ) (y j)) := by
  simp_rw [splineHeightCorrection_complex,mul_sum,mul_add,← mul_assoc]
  rw [splineNodeAverage_sum]
  apply sum_congr rfl
  intro j _
  rw [splineNodeAverage_add,splineNodeAverage_mul_const,splineNodeAverage_mul_const]

/-- Row bounds for the ordinary and conjugate pairings control the real
node-motion Jacobian on an arbitrary selected node set. -/
lemma norm_splineNodeAverage_slope_correction_sub_le [DecidableEq ι]
    (x : Fin n → ℝ) {δ : ℝ} {t : ι → ℝ} {A B : ι → ι → ℝ}
    (hA : ∀ i j, ‖splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*splineDual δ (t j) u)-
      (if i=j then 1 else 0)‖ ≤ A i j)
    (hB : ∀ i j, ‖splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*
      (starRingEnd ℂ) (splineDual δ (t j) u))‖ ≤ B i j)
    (y : ι → ℂ) (i : ι) :
    ‖splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*
      (splineHeightCorrection δ t y u:ℂ))-y i‖ ≤ (∑ j, (A i j+B i j))*‖y‖ := by
  rw [splineNodeAverage_slope_correction]
  have he : (∑ j, (splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*splineDual δ (t j) u)*y j+
      splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*
        (starRingEnd ℂ) (splineDual δ (t j) u))*(starRingEnd ℂ) (y j)))-y i=
      ∑ j, ((splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*splineDual δ (t j) u)-
        (if i=j then 1 else 0))*y j+
      splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*
        (starRingEnd ℂ) (splineDual δ (t j) u))*(starRingEnd ℂ) (y j)) := by
    simp only [sub_mul,sub_add,sum_sub_distrib,sum_add_distrib]
    simp
    ring
  rw [he]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j, (A i j+B i j)*‖y‖ := by
      apply sum_le_sum
      intro j _
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul,norm_mul,Complex.norm_conj,add_mul]
      exact add_le_add
        (mul_le_mul (hA i j) (norm_le_pi_norm y j) (norm_nonneg _)
          ((norm_nonneg _).trans (hA i j)))
        (mul_le_mul (hB i j) (norm_le_pi_norm y j) (norm_nonneg _)
          ((norm_nonneg _).trans (hB i j)))
    _ = _ := (sum_mul _ _ _).symm

#print axioms norm_splineNodeAverage_slope_correction_sub_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
