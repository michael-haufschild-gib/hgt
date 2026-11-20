import GaloisForLFunctions.ExceptionalLayerTheory.HighDerivativeAreasOfTheXiDivisor

/-!
# Counting each zero multiplicity by changing the aperture

Place first-derivative sensors at any finite list of distinct candidate
zeros. At radius √n/u and threshold u², a point of order m contributes
min(n,m) to the limiting normalized area. The increment from n to n+1
counts orders above n. Three successive aperture areas recover the
number of points of any prescribed positive order without resolving
their individual readings.
-/

noncomputable section
open Complex Filter MeasureTheory Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Total of the normalized first-derivative areas measured at the sites. -/
def firstDerivativeAperture (t : Finset ℂ) (n : ℕ) (u : ℝ) : ℝ :=
  ∑ z ∈ t, (u^2*volume.real (xiDerivativeWindow 1 z (Real.sqrt n) u))/Real.pi

private theorem sqrt_min_sq (n m : ℕ) :
    (min (Real.sqrt n) (Real.sqrt m))^2=((min n m:ℕ):ℝ) := by
  rcases le_total n m with h | h
  · rw [min_eq_left h,min_eq_left (Real.sqrt_le_sqrt (by exact_mod_cast h)),
      Real.sq_sqrt (Nat.cast_nonneg _)]
  · rw [min_eq_right h,min_eq_right (Real.sqrt_le_sqrt (by exact_mod_cast h)),
      Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The aperture sum measures the multiplicity truncated at n. Regular
points in the candidate set contribute zero for all n. -/
theorem first_derivative_aperture_limit (t : Finset ℂ) (n : ℕ) :
    Tendsto (firstDerivativeAperture t n) atTop (𝓝 (∑ z ∈ t, ((min n (hadamardOrder z):ℕ):ℝ))) := by
  apply tendsto_finsetSum
  intro z _
  have h := (xi_derivative_area_profile z 1 (Real.sqrt_nonneg (n:ℝ))).div_const Real.pi
  have he : ((hadamardOrder z:ℝ)*(1:ℕ).factorial)^(((1+1:ℕ):ℝ)⁻¹)=Real.sqrt (hadamardOrder z) := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rwa [he,sqrt_min_sq,mul_div_cancel_left₀ _ Real.pi_ne_zero] at h

private theorem card_by_ones (t : Finset ℂ) (P : ℂ → Prop) [DecidablePred P] :
    (∑ z ∈ t, if P z then (1:ℝ) else 0) = ((t.filter P).card:ℝ) := by
  rw [←Finset.sum_filter]
  simp

private theorem clipped_step (n m : ℕ) :
    ((min (n+1) m:ℕ):ℝ)-(min n m:ℕ) = if n < m then 1 else 0 := by
  by_cases h : n < m
  · rw [if_pos h,min_eq_left (Nat.succ_le_of_lt h),min_eq_left h.le,Nat.cast_succ]
    ring
  · rw [if_neg h,min_eq_right ((le_of_not_gt h).trans (Nat.le_succ n)),
      min_eq_right (le_of_not_gt h),sub_self]

/-- The first increment counts points whose multiplicity is at least n+1. -/
theorem aperture_increment_counts_above (t : Finset ℂ) (n : ℕ) :
    Tendsto (fun u : ℝ => firstDerivativeAperture t (n+1) u-firstDerivativeAperture t n u)
      atTop (𝓝 ((t.filter (fun z => n < hadamardOrder z)).card:ℝ)) := by
  have h := (first_derivative_aperture_limit t (n+1)).sub (first_derivative_aperture_limit t n)
  simp only [←Finset.sum_sub_distrib,clipped_step,card_by_ones] at h
  exact h

/-- A second finite difference counts sites of exactly the requested
order. The integral signal eventually distinguishes neighboring counts. -/
theorem three_apertures_count_each_order (t : Finset ℂ) (n : ℕ) :
    Tendsto (fun u : ℝ => 2*firstDerivativeAperture t (n+1) u-firstDerivativeAperture t n u-
      firstDerivativeAperture t (n+2) u) atTop
      (𝓝 ((t.filter (fun z => hadamardOrder z=n+1)).card:ℝ)) := by
  have h := (aperture_increment_counts_above t n).sub (aperture_increment_counts_above t (n+1))
  have he : ((t.filter (fun z => n < hadamardOrder z)).card:ℝ)-
      ((t.filter (fun z => n+1 < hadamardOrder z)).card:ℝ) =
      ((t.filter (fun z => hadamardOrder z=n+1)).card:ℝ) := by
    rw [←card_by_ones,←card_by_ones,←card_by_ones,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : hadamardOrder z=n+1
    · simp [hz]
    · by_cases hlt : n < hadamardOrder z
      · have hlt' : n+1 < hadamardOrder z := by omega
        simp [hz,hlt,hlt']
      · have hlt' : ¬n+1 < hadamardOrder z := by omega
        simp [hz,hlt,hlt']
  rw [he] at h
  apply h.congr
  intro u
  change (_-_)-(_-_)=_
  ring

#print axioms first_derivative_aperture_limit
#print axioms aperture_increment_counts_above
#print axioms three_apertures_count_each_order
end GaloisForLFunctions.ExceptionalLayerTheory
