import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.AnEndpointDerivativeOnSquaredNodes
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.RecoveringLogMultipliersByShortVerticalTranslations

/-!
# Derivative energy from a one-sided window of unit length

Squared-node differentiation only samples heights within one unit of the
observation. An order proportional to the bandwidth plus the logarithm of
the coefficient mass makes its Taylor remainder bounded. The resulting
local energy inequality has polynomial dependence on this order.
-/

noncomputable section
open Finset Complex MeasureTheory
open _root_.HTGeometry
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def windowSamples (q : ℕ) := range (2*q+1) ×ˢ (univ : Finset Bool)
private def windowWeight (q : ℕ) (j : ℕ × Bool) : ℂ :=
  if j.2 then (squareNodeWeight q j.1:ℂ) else -(squareNodeWeight q j.1:ℂ)
private def windowPoint (q : ℕ) (j : ℕ × Bool) : ℝ := if j.2 then squareNode q j.1 else 0

private theorem window_sum (q : ℕ) (f : ℝ → ℂ) :
    (∑ j ∈ windowSamples q, windowWeight q j*f (windowPoint q j)) =
      ∑ j ∈ range (2*q+1), (squareNodeWeight q j:ℂ)*(f (squareNode q j)-f 0) := by
  rw [windowSamples,sum_product]
  apply sum_congr rfl
  intro j _
  simp only [Fintype.sum_bool,windowWeight,windowPoint,ite_true,ite_false,Bool.false_eq_true]
  ring

private theorem window_weight_bound {q : ℕ} (hq : 0 < q) (j : ℕ × Bool) :
    ‖windowWeight q j‖ ≤ (q:ℝ)^2 := by
  rcases j with ⟨j,b⟩
  cases b <;> simpa only [windowWeight,ite_true,ite_false,Bool.false_eq_true,norm_neg,
    Complex.norm_real,Real.norm_eq_abs] using squareNodeWeight_abs_le q j hq

private theorem windowPoint_mem {q : ℕ} (hq : 0 < q) {j : ℕ × Bool} (hj : j ∈ windowSamples q) :
    windowPoint q j ∈ Set.Icc (0:ℝ) 1 := by
  rcases j with ⟨j,b⟩
  have hj' : j ∈ range (2*q+1) := (mem_product.mp hj).1
  cases b
  · exact ⟨le_rfl,zero_le_one⟩
  · exact squareNode_mem q j hq hj'

private theorem window_card (q : ℕ) : ((windowSamples q).card:ℝ)=2*(2*(q:ℝ)+1) := by
  simp [windowSamples,card_product]; ring

private theorem factorial_window_tail {x B : ℝ} (hx : 0 ≤ x) (hxB : x ≤ B) (k : ℕ)
    (hk : 4*B ≤ (k:ℝ)*Real.log 2) :
    (x^k/k.factorial)*Real.exp x ≤ Real.exp (-B) := by
  apply le_of_mul_le_mul_left (a:=(2:ℝ)^k) _ (by positivity)
  calc (2:ℝ)^k*((x^k/k.factorial)*Real.exp x) =
        ((2*x)^k/k.factorial)*Real.exp x := by rw [mul_pow]; ring
    _ ≤ Real.exp (2*x)*Real.exp x := mul_le_mul_of_nonneg_right
      (Real.pow_div_factorial_le_exp (2*x) (mul_nonneg zero_le_two hx) k) (Real.exp_pos _).le
    _ ≤ 2^k*Real.exp (-B) := by
      rw [←Real.rpow_natCast (2:ℝ) k,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),←Real.exp_add,←Real.exp_add,
        Real.exp_le_exp]
      linarith only [hxB,hk]

private theorem mode_translate (freq t h x : ℝ) :
    verticalMode freq (t+h*x) = verticalMode freq t * cexp ((x:ℂ)*(((h*freq:ℝ):ℂ)*I)) := by
  unfold verticalMode
  rw [←exp_add]
  congr 1
  push_cast
  ring

/-- Sample the derivative of an actual finite exponential sum. The retained
coefficient mass is bounded by exp B, and every point lies within one unit
of t when the step is in the closed unit interval about zero. -/
private theorem window_derivative_error (a : ℕ → ℂ) (freq : ℕ → ℝ) (S : Finset ℕ)
    {q : ℕ} (hq : 0 < q) {B h : ℝ} (hh : |h| ≤ 1)
    (hfreq : ∀ n ∈ S, |freq n| ≤ B) (hmass : (∑ n ∈ S, ‖a n‖) ≤ Real.exp B)
    (horder : 4*B ≤ (q+1:ℕ)*Real.log 2) (t : ℝ) :
    ‖(h:ℂ)*deriv (genPoly a freq S) t-
      ∑ j ∈ windowSamples q, windowWeight q j*genPoly a freq S (t+h*windowPoint q j)‖ ≤
      (2*(q:ℝ)+1)*(q:ℝ)^2 := by
  let J := (2*(q:ℝ)+1)*(q:ℝ)^2
  let z (n : ℕ) := ((h*freq n:ℝ):ℂ)*I
  let p (n : ℕ) := ∑ j ∈ range (2*q+1), (squareNodeWeight q j:ℂ)*
    (cexp ((squareNode q j:ℂ)*z n)-1)
  have hs (n : ℕ) : (∑ j ∈ windowSamples q, windowWeight q j*verticalMode (freq n) (t+h*windowPoint q j)) =
      verticalMode (freq n) t*p n := by
    rw [window_sum q (fun x => verticalMode (freq n) (t+h*x))]
    simp only [mul_zero,add_zero]
    rw [show verticalMode (freq n) t*p n=∑ j ∈ range (2*q+1),
      verticalMode (freq n) t*((squareNodeWeight q j:ℂ)*(cexp ((squareNode q j:ℂ)*z n)-1)) from mul_sum ..]
    exact sum_congr rfl fun j _ => by rw [mode_translate]; dsimp only [z]; ring
  have H (n : ℕ) (hn : n ∈ S) : ‖z n-p n‖ ≤ J*Real.exp (-B) := by
    have hz : ‖z n‖ ≤ B := by
      rw [show ‖z n‖=|h| * |freq n| by simp [z,Real.norm_eq_abs]]
      exact (mul_le_of_le_one_left (abs_nonneg _) hh).trans (hfreq n hn)
    rw [norm_sub_rev]
    have E := squareNode_exponential_error hq (z n)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at E
    exact E.trans (mul_le_mul_of_nonneg_left (factorial_window_tail (norm_nonneg _) hz _ horder)
      (by positivity))
  have he : (∑ j ∈ windowSamples q, windowWeight q j*genPoly a freq S (t+h*windowPoint q j)) =
      ∑ n ∈ S, a n*(verticalMode (freq n) t*p n) := by
    simp_rw [genPoly_eq_verticalMode_sum,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    rw [←hs,mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [he,deriv_genPoly_as_packet,genPoly_eq_verticalMode_sum,mul_sum,←sum_sub_distrib]
  have hc (n : ℕ) : (h:ℂ)*((freq n:ℂ)*I*a n*verticalMode (freq n) t)-
      a n*(verticalMode (freq n) t*p n) = (a n*verticalMode (freq n) t)*(z n-p n) := by
    dsimp only [z]; push_cast; ring
  simp_rw [hc]
  calc _ ≤ ∑ n ∈ S, ‖(a n*verticalMode (freq n) t)*(z n-p n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ‖a n‖*(J*Real.exp (-B)) := sum_le_sum fun n hn => by
      rw [norm_mul,norm_mul,show ‖verticalMode (freq n) t‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one]
      exact mul_le_mul_of_nonneg_left (H n hn) (norm_nonneg _)
    _ ≤ Real.exp B*(J*Real.exp (-B)) := by
      rw [←sum_mul]
      exact mul_le_mul_of_nonneg_right hmass (by dsimp only [J]; positivity)
    _ = _ := by rw [Real.exp_neg]; change _=J; field_simp

/-- A derivative mean on the same observation interval uses an order q
linear in B and costs at most a sextic polynomial in q. -/
theorem derivative_energy_of_logarithmic_size (a : ℕ → ℂ) (freq : ℕ → ℝ) (S : Finset ℕ)
    {q : ℕ} (hq : 0 < q) {A D B : ℝ} (hlen : 2 ≤ D-A) (hfreq : ∀ n ∈ S, |freq n| ≤ B)
    (hmass : (∑ n ∈ S, ‖a n‖) ≤ Real.exp B) (horder : 4*B ≤ (q+1:ℕ)*Real.log 2) :
    (∫ t in A..D, ‖deriv (genPoly a freq S) t‖^2) ≤
      16*(2*(q:ℝ)+1)^2*(q:ℝ)^4*((∫ t in A..D, ‖genPoly a freq S t‖^2)+(D-A)) := by
  let F := genPoly a freq S
  let M := (A+D)/2
  have hF : Continuous F := by unfold F genPoly; fun_prop
  have hG : Continuous (deriv F) := by dsimp only [F]; rw [deriv_genPoly_as_packet]; unfold genPoly; fun_prop
  have left := translated_sample_energy_on_subinterval (J:=windowSamples q) (windowWeight q)
    (fun j => 1*windowPoint q j) F (deriv F) hF hG (A:=A) (D:=D) (h:=1) (L:=A) (R:=M)
    (by dsimp [M]; linarith only [hlen]) (fun j hj => by
      obtain ⟨h0,h1⟩ := windowPoint_mem hq hj
      simp only [one_mul]; dsimp only [M]; constructor <;> linarith only [h0,h1,hlen])
    (fun t => window_derivative_error a freq S hq (by norm_num) hfreq hmass horder t)
  have right := translated_sample_energy_on_subinterval (J:=windowSamples q) (windowWeight q)
    (fun j => (-1)*windowPoint q j) F (deriv F) hF hG (A:=A) (D:=D) (h:=-1) (L:=M) (R:=D)
    (by dsimp [M]; linarith only [hlen]) (fun j hj => by
      obtain ⟨h0,h1⟩ := windowPoint_mem hq hj
      simp only [neg_one_mul]; dsimp only [M]; constructor <;> linarith only [h0,h1,hlen])
    (fun t => window_derivative_error a freq S hq (by norm_num) hfreq hmass horder t)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (f:=fun t => ‖deriv F t‖^2) ((hG.norm.pow 2).intervalIntegrable A M) ((hG.norm.pow 2).intervalIntegrable M D)
  let I₀ := ∫ t in A..D, ‖F t‖^2
  have hI : 0 ≤ I₀ := intervalIntegral.integral_nonneg (by linarith only [hlen]) fun _ _ => sq_nonneg _
  have hW : (∑ j ∈ windowSamples q, ‖windowWeight q j‖^2) ≤ (windowSamples q).card*(q:ℝ)^4 := by
    have he := sum_le_sum (s:=windowSamples q) (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (window_weight_bound hq j) 2)
    simpa only [sum_const,nsmul_eq_mul,←pow_mul] using he
  have hcmp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW
    (by positivity : 0 ≤ 4*((windowSamples q).card:ℝ))) hI
  rw [window_card] at hcmp
  simp only [one_pow,neg_sq,one_mul,window_card] at left right
  change (∫ t in A..D, ‖deriv F t‖^2) ≤ 16*(2*(q:ℝ)+1)^2*(q:ℝ)^4*(I₀+(D-A))
  rw [←hsplit]
  have hrem := mul_nonneg (by positivity : 0 ≤ (2*(q:ℝ)+1)^2*(q:ℝ)^4)
    (show 0 ≤ D-A by linarith only [hlen])
  dsimp only [I₀] at hI hcmp ⊢
  linarith only [left,right,hcmp,hrem]

#print axioms derivative_energy_of_logarithmic_size

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
