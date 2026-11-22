import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Quadratic remainder for an affine energy label

After scaling an occupation by its integer label, its translation is a
step of size 1/n in a fixed positive interval. Compactness there gives
a uniform quadratic bound even for negative translations.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift

open Metric Set

def weight (x : ℝ) (s : ℂ) : ℂ := (x:ℂ)^(-s)

theorem weight_entire {x : ℝ} (hx : 0 < x) : Differentiable ℂ (weight x) := by
  have he : weight x = fun s => Complex.exp (Complex.log (x:ℂ)*(-s)) := by
    funext s
    exact Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne') _
  rw [he]
  exact (differentiable_id.neg.const_mul _).cexp

theorem weight_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (s : ℂ) :
    weight (x*y) s = weight x s*weight y s := by
  simp only [weight,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hx hy]

theorem weight_succ {x : ℝ} (hx : 0 < x) (s : ℂ) :
    weight x (s+1) = weight x s*(x:ℂ)⁻¹ := by
  rw [weight,weight,show -(s+1) = -s-1 by ring,Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_one,div_eq_mul_inv]

theorem affine_pos {b a u : ℝ} (hb : 0 < b) (he : 0 < b+a) (hu : u ∈ Icc 0 1) : 0 < b+a*u := by
  by_cases ha : 0 ≤ a
  · exact add_pos_of_pos_of_nonneg hb (mul_nonneg ha hu.1)
  · linarith only [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha) (sub_nonneg.mpr hu.2),he]

private theorem weight_derivative {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasDerivAt (fun y => weight y s) (-s*weight x (s+1)) x := by
  rcases eq_or_ne s 0 with rfl | hs
  · simpa [weight] using (hasDerivAt_const x (1:ℂ))
  · simpa only [weight,neg_add_rev,sub_eq_add_neg,add_comm (-1:ℂ)] using
      hasDerivAt_ofReal_cpow_const hx.ne' (neg_ne_zero.mpr hs)

private def first (a : ℝ) (s : ℂ) := (a:ℂ)*(-s)

private theorem affine_derivative {b a u : ℝ} (hp : 0 < b+a*u) (s : ℂ) :
    HasDerivAt (fun y : ℝ => weight (b+a*y) s) (first a s*weight (b+a*u) (s+1)) u := by
  have h := (weight_derivative hp s).scomp u (((hasDerivAt_id u).const_mul a).const_add b)
  simpa only [Function.comp_def,id_eq,mul_one,Complex.real_smul,first,mul_assoc] using h

private theorem quadratic_bound {f g h : ℝ → ℂ} {u K : ℝ} (hu : 0 ≤ u) (hK : 0 ≤ K)
    (hf : ∀ y ∈ Icc 0 u, HasDerivAt f (g y) y)
    (hg : ∀ y ∈ Icc 0 u, HasDerivAt g (h y) y) (hh : ∀ y ∈ Icc 0 u, ‖h y‖ ≤ K) :
    ‖f u-f 0-(u:ℂ)*g 0‖ ≤ K*u^2 := by
  have h₀ : (0:ℝ) ∈ Icc 0 u := ⟨le_rfl,hu⟩
  have hu' : u ∈ Icc 0 u := ⟨hu,le_rfl⟩
  let F (y : ℝ) := f y-(y:ℂ)*g 0
  have hd (y : ℝ) (hy : y ∈ Icc 0 u) : HasDerivWithinAt F (g y-g 0) (Icc 0 u) y := by
    have hlin := (hasDerivAt_id y).ofReal_comp.mul_const (g 0)
    simpa only [F,Pi.sub_def,id_eq,Complex.ofReal_one,one_mul] using ((hf y hy).sub hlin).hasDerivWithinAt
  have hb (y : ℝ) (hy : y ∈ Icc 0 u) : ‖g y-g 0‖ ≤ K*u := by
    have h := (convex_Icc 0 u).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hg x hx).hasDerivWithinAt) hh h₀ hy
    rw [sub_zero,Real.norm_eq_abs,abs_of_nonneg hy.1] at h
    exact h.trans (mul_le_mul_of_nonneg_left hy.2 hK)
  have h := (convex_Icc 0 u).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb h₀ hu'
  simpa only [F,Complex.ofReal_zero,zero_mul,sub_zero,Real.norm_eq_abs,abs_of_nonneg hu,
    sub_right_comm (f u),pow_two,mul_assoc] using h

/-- A compact temperature disk controls the normalized affine remainder on the whole unit interval. -/
theorem normalized_bound {b a : ℝ} (hb : 0 < b) (he : 0 < b+a) (w : ℂ) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ closedBall w R, ∀ u ∈ Icc (0:ℝ) 1,
      ‖weight (b+a*u) s-weight b s+s*(a:ℂ)*(u:ℂ)*weight b (s+1)‖ ≤ K*u^2 := by
  let S := closedBall w R ×ˢ Icc (0:ℝ) 1
  let H (p : ℂ × ℝ) := first a p.1*(first a (p.1+1)*weight (b+a*p.2) ((p.1+1)+1))
  have hbase : ContinuousOn (fun p : ℂ × ℝ => ((b+a*p.2:ℝ):ℂ)) S := by fun_prop
  have hpow : ContinuousOn (fun p : ℂ × ℝ => weight (b+a*p.2) ((p.1+1)+1)) S :=
    hbase.cpow (by fun_prop) (fun p hp => Complex.ofReal_mem_slitPlane.mpr (affine_pos hb he hp.2))
  have hH : ContinuousOn H S := by
    unfold H first
    exact (by fun_prop : ContinuousOn (fun p : ℂ × ℝ => (a:ℂ)*(-p.1)) S).mul
      ((by fun_prop : ContinuousOn (fun p : ℂ × ℝ => (a:ℂ)*(-(p.1+1))) S).mul hpow)
  obtain ⟨M,hM⟩ := ((isCompact_closedBall w R).prod isCompact_Icc).exists_bound_of_continuousOn hH
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro s hs u hu
  let f (y : ℝ) := weight (b+a*y) s
  let g (y : ℝ) := first a s*weight (b+a*y) (s+1)
  have hpos (y : ℝ) (hy : y ∈ Icc 0 u) := affine_pos hb he ⟨hy.1,hy.2.trans hu.2⟩
  have h := quadratic_bound (f := f) (g := g) (h := fun y => H (s,y)) hu.1 (le_max_right M 0)
    (fun y hy => affine_derivative (hpos y hy) s)
    (fun y hy => (affine_derivative (hpos y hy) (s+1)).const_mul (first a s))
    (fun y hy => (hM (s,y) ⟨hs,hy.1,hy.2.trans hu.2⟩).trans (le_max_left _ _))
  simp only [f,g,first,mul_zero,add_zero] at h
  convert h using 2
  ring

/-- The constant and first derivative removed from the heat of an affine label. -/
def remainder (b a n : ℝ) (s : ℂ) :=
  weight (b*n+a) s-weight (b*n) s+s*(a:ℂ)*weight (b*n) (s+1)

theorem inverse_unit {n : ℝ} (hn : 1 ≤ n) : n⁻¹ ∈ Icc (0:ℝ) 1 :=
  ⟨inv_nonneg.mpr (zero_le_one.trans hn),inv_le_one_of_one_le₀ hn⟩

theorem affine_value_pos {b a n : ℝ} (hb : 0 < b) (he : 0 < b+a) (hn : 1 ≤ n) : 0 < b*n+a := by
  have h : b*n+a = n*(b+a*n⁻¹) := by
    field_simp [(zero_lt_one.trans_le hn).ne']
  rw [h]
  exact mul_pos (zero_lt_one.trans_le hn) (affine_pos hb he (inverse_unit hn))

theorem remainder_bound {b a : ℝ} (hb : 0 < b) (he : 0 < b+a) (w : ℂ) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ closedBall w R, ∀ n : ℝ, 1 ≤ n →
      ‖remainder b a n s‖ ≤ ‖weight n s‖ * (K*(n⁻¹)^2) := by
  obtain ⟨K,hK,h⟩ := normalized_bound hb he w R
  refine ⟨K,hK,?_⟩
  intro s hs n hn
  have hn₀ := zero_lt_one.trans_le hn
  have hi := inverse_unit hn
  have heq : b*n+a = n*(b+a*n⁻¹) := by field_simp [hn₀.ne']
  have hfac : remainder b a n s = weight n s *
      (weight (b+a*n⁻¹) s-weight b s+s*(a:ℂ)*((n⁻¹:ℝ):ℂ)*weight b (s+1)) := by
    rw [remainder,heq,weight_mul hn₀.le (affine_pos hb he hi).le,
      weight_mul hb.le hn₀.le,weight_mul hb.le hn₀.le,weight_succ hn₀,Complex.ofReal_inv]
    ring
  rw [hfac,norm_mul]
  exact mul_le_mul_of_nonneg_left (h s hs _ hi) (norm_nonneg _)

#print axioms remainder_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift
