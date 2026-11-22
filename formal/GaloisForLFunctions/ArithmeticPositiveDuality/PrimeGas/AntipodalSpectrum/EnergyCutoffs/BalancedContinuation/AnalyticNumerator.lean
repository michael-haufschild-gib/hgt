import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedContinuation.DigitRecursion
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Holomorphic digit correction for the balanced trace

Differentiation in the real label gains one full power of decay. On each
compact disk strictly to the right of −1/2 the balanced heat at a fixed
inverse temperature greater than 1/2 dominates all digit differences.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation

open Metric Set

private theorem power_increment {n m d p : ℝ} {s : ℂ} (hn : 1 ≤ n) (hm : n ≤ m)
    (hd : 0 ≤ d) (hp : 0 < p) (hs : p ≤ s.re+1) :
    ‖((m+d:ℝ):ℂ)^(-s)-(m:ℂ)^(-s)‖ ≤ ‖s‖*d*n^(-p) := by
  rcases eq_or_ne s 0 with rfl | hne
  · simp
  have hn₀ : 0 < n := zero_lt_one.trans_le hn
  have hmn := hn₀.trans_le hm
  let I := Set.Icc m (m+d)
  let f (y : ℝ) := (y:ℂ)^(-s)
  let f' (y : ℝ) := (-s)*(y:ℂ)^(-s-1)
  have hder (y : ℝ) (hy : y ∈ I) : HasDerivWithinAt f (f' y) I y :=
    (hasDerivAt_ofReal_cpow_const (hmn.trans_le hy.1).ne' (neg_ne_zero.mpr hne)).hasDerivWithinAt
  have hb (y : ℝ) (hy : y ∈ I) : ‖f' y‖ ≤ ‖s‖*n^(-p) := by
    change ‖(-s)*(y:ℂ)^(-s-1)‖ ≤ _
    rw [norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos (hmn.trans_le hy.1)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
    have hnY := hm.trans hy.1
    calc y^(-s-1).re ≤ y^(-p) := Real.rpow_le_rpow_of_exponent_le (hn.trans hnY)
           (by simp only [Complex.sub_re,Complex.neg_re,Complex.one_re]; linarith only [hs])
         _ ≤ n^(-p) := Real.rpow_le_rpow_of_nonpos hn₀ hnY (neg_nonpos.mpr hp.le)
  have h := (convex_Icc m (m+d)).norm_image_sub_le_of_norm_hasDerivWithin_le hder hb
    (left_mem_Icc.mpr (le_add_of_nonneg_right hd)) (right_mem_Icc.mpr (le_add_of_nonneg_right hd))
  change ‖((m+d:ℝ):ℂ)^(-s)-(m:ℂ)^(-s)‖ ≤ ‖s‖*n^(-p)*‖m+d-m‖ at h
  simpa only [add_sub_cancel_left,Real.norm_eq_abs,abs_of_nonneg hd,mul_right_comm] using h

private theorem majorant (t : ExceptionalTime) (j : ℕ) (d : Fin (radix t j)) (x : Label t j)
    (s : ℂ) (p : ℝ) (hp : 1/2 < p) (hs : p ≤ s.re+1) :
    ‖correction t j d x s‖ ≤ ‖s‖*(d.val:ℝ)*‖balancedHeat t j (p:ℂ) x‖ := by
  let b := (dilation t j).val
  let n := x.val.val
  have hn : 1 ≤ n := x.property
  have hmn : n ≤ b*n := Nat.le_mul_of_pos_left n (dilation t j).pos
  have h := power_increment (n := (n:ℝ)) (m := (b:ℝ)*n) (d := (d.val:ℝ))
    (by exact_mod_cast hn) (by exact_mod_cast hmn) (Nat.cast_nonneg _) (by linarith only [hp]) hs
  have hnorm : ‖balancedHeat t j (p:ℂ) x‖ = (n:ℝ)^(-p) := by
    rw [balancedHeat,heat_eq_cpow]
    change ‖(n:ℂ)^(-(p:ℂ))‖ = (n:ℝ)^(-p)
    rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos
      (by exact_mod_cast x.property : 0 < (n:ℝ))]
    rfl
  rw [hnorm,correction,balancedHeat,← heat_mul,heat_eq_cpow,heat_eq_cpow,child_value,PNat.mul_coe]
  change ‖((d.val+b*n:ℕ):ℂ)^(-s)-((b*n:ℕ):ℂ)^(-s)‖ ≤ _
  simpa only [Nat.cast_add,Nat.cast_mul,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_natCast,
    add_comm (d.val:ℂ)] using h

private theorem heat_entire (a : ℕ+) : Differentiable ℂ (fun z => heat z a) :=
  (differentiable_id.neg.mul_const (energy a:ℂ)).cexp

private theorem correction_entire (t : ExceptionalTime) (j : ℕ) (d : Fin (radix t j)) (x : Label t j) :
    Differentiable ℂ (correction t j d x) :=
  (heat_entire (child t j d x)).sub ((heat_entire (dilation t j)).mul (heat_entire _))

private theorem column_diff (t : ExceptionalTime) (j : ℕ) (d : Fin (radix t j)) (w : ℂ) (hw : -(1/2) < w.re) :
    DifferentiableAt ℂ (fun s => ∑' x : Label t j, correction t j d x s) w := by
  let R := (w.re+1/2)/2
  let p := w.re+1-R
  have hR : 0 < R := by dsimp [R]; linarith only [hw]
  have hp : 1/2 < p := by dsimp [p,R]; linarith only [hw]
  let K := (‖w‖+R)*(d.val:ℝ)
  apply HTGeometry.differentiableAt_tsum_of_cauchy_dominated (R := R)
    (bound := fun x => K*‖balancedHeat t j (p:ℂ) x‖) hR
  · exact fun x => (correction_entire t j d x).differentiableOn
  · intro x s hs
    have hsub : ‖s-w‖ < R := mem_ball_iff_norm.mp hs
    have hr := (Complex.abs_re_le_norm (s-w)).trans hsub.le
    rw [Complex.sub_re,abs_le] at hr
    have hsp : p ≤ s.re+1 := by dsimp [p]; linarith only [hr.1]
    have hK : ‖s‖ ≤ ‖w‖+R := by
      calc ‖s‖ = ‖(s-w)+w‖ := by rw [sub_add_cancel]
           _ ≤ ‖s-w‖+‖w‖ := norm_add_le _ _
           _ ≤ ‖w‖+R := by linarith only [hsub]
    exact (majorant t j d x s p hp hsp).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _)) (norm_nonneg _))
  · exact ((balanced_heat_summable_iff t j (p:ℂ)).mpr hp).mul_left K

/-- The corrected numerator is holomorphic a full unit beyond the absolute heat boundary. -/
theorem numerator_analytic (t : ExceptionalTime) (j : ℕ) (w : {z : ℂ // -(1/2) < z.re}) :
    AnalyticAt ℂ (numerator t j) w.val := by
  let U := {z : ℂ | -(1/2) < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds w.property)
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.add
  · exact DifferentiableAt.fun_sum (fun d _ => (heat_entire _ s))
  · exact DifferentiableAt.fun_sum (fun d _ => column_diff t j d s hs)

#print axioms numerator_analytic

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation
