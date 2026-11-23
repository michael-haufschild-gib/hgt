import GaloisForLFunctions.HTGeometry.GaussianBoxMass
import Mathlib.MeasureTheory.Constructions.Pi

/-! # A coupling box with an exponentially small exceptional probability -/
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- A box of radius 2(D+m+1) for m independent standard Gaussian
coefficients misses probability at most 2 to the minus D. -/
theorem gaussian_dimension_box (ι : Type*) [Fintype ι] (D : ℕ) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    let T := 2*((D:ℝ)+(Fintype.card ι:ℝ)+1)
    μ {x | ¬∀ i, |x i| ≤ T} ≤ ENNReal.ofReal ((1/2:ℝ)^D) := by
  classical
  intro μ T
  let m : ℝ := Fintype.card ι
  let A (i : ι) := {x : ι → ℝ | T ≤ |x i|}
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hsub : {x : ι → ℝ | ¬∀ i, |x i| ≤ T} ⊆ ⋃ i, A i := by
    intro x hx
    obtain ⟨i,hi⟩ := not_forall.mp hx
    exact mem_iUnion.mpr ⟨i,(lt_of_not_ge hi).le⟩
  have hp (i : ι) : μ.real (A i) ≤ 2*exp (-T^2/2) :=
    measureReal_abs_ge_le_of_standardGaussian (measurable_pi_apply i).aemeasurable
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq hT
  have hh := (measureReal_mono hsub).trans ((measureReal_iUnion_fintype_le A).trans
    (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hp i)))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have hm : 0≤m := Nat.cast_nonneg _
  have hD : (0:ℝ)≤D := Nat.cast_nonneg _
  have h₁ : 2*m ≤ exp (2*m) := (le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _)
  have h₂ : 2*m-T^2/2 ≤ -(D:ℝ) := by
    change 2*m-(2*((D:ℝ)+m+1))^2/2 ≤ _
    nlinarith only [hD,hm,sq_nonneg ((D:ℝ)+m)]
  have he : exp (-(D:ℝ)) ≤ (1/2:ℝ)^D := by
    rw [exp_neg,←mul_one (D:ℝ),exp_nat_mul,one_div,inv_pow]
    exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr
      (pow_le_pow_left₀ (by norm_num) (by simpa using add_one_le_exp (1:ℝ)) D)
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  apply hh.trans
  calc
    _ = (2*m)*exp (-T^2/2) := by dsimp only [m]; ring
    _ ≤ exp (2*m)*exp (-T^2/2) := mul_le_mul_of_nonneg_right h₁ (exp_pos _).le
    _ = exp (2*m-T^2/2) := by rw [←exp_add]; congr 1; ring
    _ ≤ exp (-(D:ℝ)) := exp_le_exp.mpr h₂
    _ ≤ _ := he

#print axioms gaussian_dimension_box
end
end GaloisForLFunctions.HTGeometry.SpectralJets
