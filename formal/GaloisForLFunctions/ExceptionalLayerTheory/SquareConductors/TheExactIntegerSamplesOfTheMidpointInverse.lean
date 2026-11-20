import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheTernaryBoundaryDataOfThePrimeMidpoint
import Mathlib.Data.Nat.Choose.Sum

/-!
# Which integer samples determine one midpoint reconstruction?

At ternary depth b, the 2^b paths to the boundary merge into b+1
dyadic sites. A forcing value from layer c occurs with a binomial weight
at depth b−1−c. Every displayed site has strictly positive sensitivity.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Mean on the b+1 dyadic sites reached by b steps of size 2 or 4. -/
def dyadicMidpointAverage (f : ℕ → ℝ) (b m : ℕ) :=
  (1/2:ℝ)^b*∑ j ∈ range (b+1), (b.choose j:ℝ)*f (2^(b+j)*m)

private theorem average_step (f : ℕ → ℝ) (b m : ℕ) :
    dyadicMidpointAverage f (b+1) m =
      (dyadicMidpointAverage f b (2*m)+dyadicMidpointAverage f b (4*m))/2 := by
  have h := sum_choose_succ_mul (fun i _ => f (2^(b+1+i)*m)) b
  have hl (i : ℕ) : 2^(b+1+i)*m=2^(b+i)*(2*m) := by
    rw [show b+1+i=b+i+1 by omega,pow_succ,mul_assoc]
  have hr (i : ℕ) : 2^(b+1+(i+1))*m=2^(b+i)*(4*m) := by
    rw [show b+1+(i+1)=b+i+2 by omega,pow_add,mul_assoc]
    rfl
  change (∑ i ∈ range (b+2), ((b+1).choose i:ℝ)*f (2^(b+1+i)*m)) = _ at h
  simp only [dyadicMidpointAverage,h,pow_succ (1/2:ℝ) b]
  simp_rw [hr,hl]
  ring

private theorem average_zero_steps (f : ℕ → ℝ) (m : ℕ) : dyadicMidpointAverage f 0 m=f m := by
  simp [dyadicMidpointAverage]

/-- Discrete Green formula. Boundary data use a single binomial row.
Forcing uses a triangle of binomial rows with different ternary valuations. -/
theorem ternary_binomial_green (seed data : ℕ → ℝ) (b m : ℕ) :
    ternaryMidpointRow seed data b m = dyadicMidpointAverage seed b m+
      (∑ c ∈ range b, dyadicMidpointAverage (fun z => data (3^c*z)) (b-1-c) m)/2 := by
  induction b generalizing m with
  | zero => simp [ternaryMidpointRow,average_zero_steps]
  | succ b ih =>
    have window : (∑ c ∈ range b,
        dyadicMidpointAverage (fun z => data (3^c*z)) (b+1-1-c) m) =
        ((∑ c ∈ range b, dyadicMidpointAverage (fun z => data (3^c*z)) (b-1-c) (2*m))+
         (∑ c ∈ range b, dyadicMidpointAverage (fun z => data (3^c*z)) (b-1-c) (4*m)))/2 := by
      rw [←sum_add_distrib,Finset.sum_div]
      refine sum_congr rfl fun c hc => ?_
      have hlt := mem_range.mp hc
      rw [show b+1-1-c=(b-1-c)+1 by omega,average_step]
    rw [ternaryMidpointRow_succ_apply,ih,ih,average_step,Finset.sum_range_succ,window,
      show b+1-1-b=0 by omega,average_zero_steps]
    ring

private theorem average_pulse_support (b m i : ℕ) :
    0 < dyadicMidpointAverage (fun z => if z=i then 1 else 0) b m ↔
      ∃ j ≤ b, 2^(b+j)*m=i := by
  rw [dyadicMidpointAverage,mul_pos_iff_of_pos_left (by positivity)]
  rw [sum_pos_iff_of_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (by split <;> norm_num))]
  constructor
  · rintro ⟨j,hj,h⟩
    refine ⟨j,Nat.lt_succ_iff.mp (mem_range.mp hj),?_⟩
    by_contra he
    simp only [if_neg he,mul_zero,lt_irrefl] at h
  · rintro ⟨j,hj,he⟩
    refine ⟨j,mem_range.mpr (Nat.lt_succ_iff.mpr hj),?_⟩
    simp only [if_pos he,mul_one]
    exact_mod_cast Nat.choose_pos hj

/-- A unit perturbation of a boundary value affects a target exactly
at the listed b+1 sites. -/
theorem boundary_sample_indispensable (b m i : ℕ) :
    0 < ternaryMidpointRow (fun z => if z=i then 1 else 0) (fun _ => 0) b m ↔
      ∃ j ≤ b, 2^(b+j)*m=i := by
  have hz (r : ℕ) : dyadicMidpointAverage (fun _ => 0) r m=0 := by
    simp [dyadicMidpointAverage]
  rw [ternary_binomial_green]
  simpa only [hz,sum_const_zero,zero_div,add_zero] using average_pulse_support b m i

/-- Forcing data at every occupied depth are individually indispensable.
The criterion also excludes every integer outside the sampling triangle. -/
theorem forcing_sample_indispensable (b m i : ℕ) :
    0 < ternaryMidpointRow (fun _ => 0) (fun z => if z=i then 1 else 0) b m ↔
      ∃ c < b, ∃ j ≤ b-1-c, 3^c*(2^(b-1-c+j)*m)=i := by
  have hz : dyadicMidpointAverage (fun _ => 0) b m=0 := by simp [dyadicMidpointAverage]
  have hscale (c r : ℕ) : dyadicMidpointAverage (fun z => if 3^c*z=i then 1 else 0) r m =
      dyadicMidpointAverage (fun z => if z=i then 1 else 0) r (3^c*m) := by
    unfold dyadicMidpointAverage
    congr 1
    exact sum_congr rfl fun j _ => by
      dsimp only
      rw [show 3^c*(2^(r+j)*m)=2^(r+j)*(3^c*m) by ac_rfl]
  have hn (c r : ℕ) : 0 ≤ dyadicMidpointAverage (fun z => if z=i then 1 else 0) r (3^c*m) := by
    unfold dyadicMidpointAverage
    exact mul_nonneg (by positivity) (sum_nonneg fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (by dsimp only; split <;> norm_num))
  rw [ternary_binomial_green,hz,zero_add,div_pos_iff_of_pos_right (by norm_num)]
  simp_rw [hscale]
  rw [sum_pos_iff_of_nonneg (fun c _ => hn c _)]
  simp only [mem_range,average_pulse_support]
  apply exists_congr
  intro c
  apply and_congr_right
  intro _
  apply exists_congr
  intro j
  rw [show 2^(b-1-c+j)*(3^c*m)=3^c*(2^(b-1-c+j)*m) by ac_rfl]

/-- For the actual prime price the same samples reproduce θ at 3^b m. -/
theorem theta_from_binomial_midpoint_samples (b m : ℕ) :
    Chebyshev.theta (3^b*m:ℕ)=
      dyadicMidpointAverage (fun z : ℕ => Chebyshev.theta z) b m+
        (∑ c ∈ range b, dyadicMidpointAverage (fun z => primeMidpointPrice (3^c*z)) (b-1-c) m)/2 := by
  have he : primeMidpointPrice=integerMidpointObservation (fun z : ℕ => Chebyshev.theta z) :=
    funext prime_midpoint_price_eq
  rw [he,←ternary_binomial_green,ternary_row_recovers_price]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
