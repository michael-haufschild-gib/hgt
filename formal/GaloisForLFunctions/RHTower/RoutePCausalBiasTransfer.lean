import GaloisForLFunctions.RHTower.RoutePPrimeCovarianceBudget

/-!
# Reversible finite-window bias transfer

The two causal differences with gains `b` and `c` are compared in both
directions. The loss is linear in their difference, rather than a fixed
loss for each prime. This retains summability for the actual prime bias.
-/

open Finset MeasureTheory

namespace RHTower.RoutePWindow

private theorem shifted_energy_le (f : ℝ → ℝ) (hf : Continuous f)
    (hz : ∀ t ≤ 0, f t = 0) {a T b : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hb0 : 0 ≤ b) (hb : b ≤ 3/4) :
    (∫ t in (0 : ℝ)..T, (f (t-a))^2) ≤
      16*(∫ t in (0 : ℝ)..T, (f t-b*f (t-a))^2) := by
  have hrec := delay_recovery_square f hf hz ha hT hb0 (by linarith : b ≤ 1)
  have hden : (1/16 : ℝ) ≤ (1-b)^2 := by nlinarith
  have hnon : 0 ≤ ∫ t in (0 : ℝ)..T, (f t)^2 :=
    intervalIntegral.integral_nonneg_of_forall hT (fun _ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hden hnon
  have hshift := shift_square_integral_le f hf hz ha hT
  nlinarith

private theorem perturbation_energy_le (k s : ℝ → ℝ)
    (hk : Continuous k) (hs : Continuous s) {T d : ℝ}
    (hT : 0 ≤ T) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hpaid : (∫ t in (0 : ℝ)..T, (s t)^2) ≤
      16*(∫ t in (0 : ℝ)..T, (k t)^2)) :
    (∫ t in (0 : ℝ)..T, (k t+d*s t)^2) ≤
      (1+33*d)*(∫ t in (0 : ℝ)..T, (k t)^2) ∧
    (∫ t in (0 : ℝ)..T, (k t-d*s t)^2) ≤
      (1+33*d)*(∫ t in (0 : ℝ)..T, (k t)^2) := by
  have hpoint (x y : ℝ) :
      (x+d*y)^2 ≤ (1+d)*(x^2+d*y^2) ∧
      (x-d*y)^2 ≤ (1+d)*(x^2+d*y^2) := by
    constructor
    · nlinarith [mul_nonneg hd0 (sq_nonneg (x-y))]
    · nlinarith [mul_nonneg hd0 (sq_nonneg (x+y))]
  have hright : Continuous (fun t => (1+d)*((k t)^2+d*(s t)^2)) :=
    ((hk.pow 2).add ((hs.pow 2).const_mul d)).const_mul (1+d)
  have hplus := intervalIntegral.integral_mono_on (μ := volume) hT
    (((hk.add (hs.const_mul d)).pow 2).intervalIntegrable 0 T)
    (hright.intervalIntegrable 0 T) (fun t _ => (hpoint (k t) (s t)).1)
  have hminus := intervalIntegral.integral_mono_on (μ := volume) hT
    (((hk.sub (hs.const_mul d)).pow 2).intervalIntegrable 0 T)
    (hright.intervalIntegrable 0 T) (fun t _ => (hpoint (k t) (s t)).2)
  simp only [Pi.pow_apply] at hplus hminus
  have hI : (∫ t in (0 : ℝ)..T, (1+d)*((k t)^2+d*(s t)^2)) =
      (1+d)*((∫ t in (0 : ℝ)..T, (k t)^2)+d*(∫ t in (0 : ℝ)..T, (s t)^2)) := by
    have hkI : IntervalIntegrable (fun t => (k t)^2) volume 0 T :=
      (hk.pow 2).intervalIntegrable 0 T
    have hsI : IntervalIntegrable (fun t => d*(s t)^2) volume 0 T :=
      ((hs.pow 2).const_mul d).intervalIntegrable 0 T
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hkI hsI,
      intervalIntegral.integral_const_mul]
  rw [hI] at hplus hminus
  have hknon : 0 ≤ ∫ t in (0 : ℝ)..T, (k t)^2 :=
    intervalIntegral.integral_nonneg_of_forall hT (fun _ => sq_nonneg _)
  have hcost : (1+d)*(1+16*d) ≤ 1+33*d := by nlinarith
  have hbound : (1+d)*((∫ t in (0 : ℝ)..T, (k t)^2)+
      d*(∫ t in (0 : ℝ)..T, (s t)^2)) ≤
      (1+33*d)*(∫ t in (0 : ℝ)..T, (k t)^2) := by
    calc
      _ ≤ (1+d)*((∫ t in (0 : ℝ)..T, (k t)^2)+
          d*(16*(∫ t in (0 : ℝ)..T, (k t)^2))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpaid hd0)) (by linarith)
      _ = ((1+d)*(1+16*d))*(∫ t in (0 : ℝ)..T, (k t)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcost hknon
  exact ⟨hplus.trans hbound, hminus.trans hbound⟩

/-- Both directions retain the small difference between the gains. -/
theorem difference_energy_comparison (f : ℝ → ℝ) (hf : Continuous f)
    (hz : ∀ t ≤ 0, f t = 0) {a T b c : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hb0 : 0 ≤ b) (hb : b ≤ 3/4) (hc0 : 0 ≤ c) (hcb : c ≤ b) :
    (∫ t in (0 : ℝ)..T, (f t-b*f (t-a))^2) ≤
      (1+33*(b-c))*(∫ t in (0 : ℝ)..T, (f t-c*f (t-a))^2) ∧
    (∫ t in (0 : ℝ)..T, (f t-c*f (t-a))^2) ≤
      (1+33*(b-c))*(∫ t in (0 : ℝ)..T, (f t-b*f (t-a))^2) := by
  have hs : Continuous (fun t => f (t-a)) := hf.comp (continuous_id.sub continuous_const)
  have hd0 : 0 ≤ b-c := sub_nonneg.mpr hcb
  have hd1 : b-c ≤ 1 := by linarith
  have hc := hcb.trans hb
  have hp := (perturbation_energy_le (fun t => f t-b*f (t-a)) (fun t => f (t-a))
    (hf.sub (hs.const_mul b)) hs hT hd0 hd1
    (shifted_energy_le f hf hz ha hT hb0 hb)).1
  have hm := (perturbation_energy_le (fun t => f t-c*f (t-a)) (fun t => f (t-a))
    (hf.sub (hs.const_mul c)) hs hT hd0 hd1
    (shifted_energy_le f hf hz ha hT hc0 hc)).2
  have hplus (t : ℝ) : f t-b*f (t-a)+(b-c)*f (t-a) = f t-c*f (t-a) := by ring
  have hminus (t : ℝ) : f t-c*f (t-a)-(b-c)*f (t-a) = f t-b*f (t-a) := by ring
  simp_rw [hplus] at hp
  simp_rw [hminus] at hm
  exact ⟨hm, hp⟩

end RHTower.RoutePWindow
