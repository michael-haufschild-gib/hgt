import GaloisForLFunctions.ExceptionalLayerTheory.ThePositivePrimeFactorialCountHasASquareRootError
import GaloisForLFunctions.RHTower.PrimeZetaLogAsymptotic

/-!
# The square contribution at the half line

Squaring the Euler factor of the positive factorial correction and inserting
zeta at twice the argument removes both its linear and its quadratic term.
The remaining logarithms are bounded by a summable cube, uniformly down to
the half line.
-/

noncomputable section

open Finset ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius
open _root_.RHTower.Sieve

namespace GaloisForLFunctions.ExceptionalLayerTheory
open GaloisForLFunctions.TransHorizonIncidenceMechanics

private abbrev hfac : ArithmeticFunction ℝ := reciprocalFactorial*(μ:ArithmeticFunction ℝ)

/-- The real Dirichlet series after removing the ordinary zeta factor. -/
def reciprocalFactorialEulerCorrection (s : ℝ) : ℝ := ∑' n : ℕ, hfac n*(n:ℝ)^(-s)

private theorem correction_local_exp {p : ℕ} (hp : p.Prime) (z : ℝ) :
    (∑' k : ℕ, hfac (p^k)*z^k)=(1-z)*Real.exp z := by
  let f := fun k : ℕ => z^k/(k.factorial:ℝ)
  have hv : Summable f := (NormedSpace.expSeries_div_hasSum_exp z).summable
  have he : ∑' k, f k = Real.exp z := _root_.RHTower.tsum_pow_div_factorial_eq_exp z
  have hs (k : ℕ) : hfac (p^(k+1))*z^(k+1)=f (k+1)-z*f k := by
    rw [mul_moebius_apply_prime_pow _ hp,reciprocalFactorial_pow hp,reciprocalFactorial_pow hp]
    dsimp only [f]
    rw [pow_succ z k]; ring
  have hsa := (summable_nat_add_iff 1).mpr hv
  have hgs : Summable (fun k : ℕ => hfac (p^k)*z^k) := by
    apply (summable_nat_add_iff 1).mp
    exact (hsa.sub (hv.mul_left z)).congr (fun k => (hs k).symm)
  have hm : hfac.IsMultiplicative :=
    (show reciprocalFactorial.IsMultiplicative from localEuler_isMultiplicative _).mul
      isMultiplicative_moebius.intCast
  have hc := hv.tsum_eq_zero_add
  rw [he,show f 0=1 by simp [f]] at hc
  rw [hgs.tsum_eq_zero_add,tsum_congr hs,hsa.tsum_sub (hv.mul_left z),tsum_mul_left,he,
    pow_zero,pow_zero,hm.map_one,mul_one]
  linarith only [hc]

private theorem correction_hasProd {s : ℝ} (hs : 1/2<s) :
    HasProd (fun p : Nat.Primes =>
      (1-((p:ℕ):ℝ)^(-s))*Real.exp (((p:ℕ):ℝ)^(-s))) (reciprocalFactorialEulerCorrection s) := by
  have hm : hfac.IsMultiplicative :=
    (show reciprocalFactorial.IsMultiplicative from localEuler_isMultiplicative _).mul
      isMultiplicative_moebius.intCast
  have hl : Summable (fun n : ℕ => ‖hfac n*(n:ℝ)^(-s)‖) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
      reciprocalFactorial_correction_summable hs
  have he := EulerProduct.eulerProduct_hasProd (f := fun n : ℕ => hfac n*(n:ℝ)^(-s))
    (by simp [hm.map_one]) (fun {m n} hc => by
      rw [hm.map_mul_of_coprime hc,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]; ring)
    hl (by simp)
  apply he.congr_fun
  intro p
  rw [← correction_local_exp p.prop]
  refine tsum_congr fun k => congrArg (hfac ((p:ℕ)^k)*·) ?_
  rw [Nat.cast_pow,← Real.rpow_natCast ((p:ℕ):ℝ) k,← Real.rpow_mul (Nat.cast_nonneg _),
    ← Real.rpow_natCast (((p:ℕ):ℝ)^(-s)) k,← Real.rpow_mul (Nat.cast_nonneg _),mul_comm]

private def cubicLog (z : ℝ) := 2*z+Real.log (1-z)-Real.log (1+z)

private theorem cubicLog_bound {z : ℝ} (hz : 0<z) (hz' : z≤3/4) :
    -(5*z^3)≤cubicLog z ∧ cubicLog z≤0 := by
  let f' (v : ℝ) := -2*v^2/(1-v^2)
  have hd {v : ℝ} (hv : 0≤v) (hv' : v≤z) : HasDerivAt cubicLog (f' v) v := by
    have h₋ : 0<1-v := by linarith only [hv',hz']
    have h₊ : 0<1+v := by linarith only [hv]
    have hh := (((hasDerivAt_id v).const_mul 2).add
      (((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v)).log h₋.ne')).sub
      (((hasDerivAt_const v (1:ℝ)).add (hasDerivAt_id v)).log h₊.ne')
    convert hh using 1
    dsimp only [f']
    have hf : 1-v^2=(1-v)*(1+v) := by ring
    rw [hf]; field_simp [h₊.ne',h₋.ne'] <;> ring
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope cubicLog f' hz
    (fun v hv => (hd hv.1 hv.2).continuousAt.continuousWithinAt)
    (fun v hv => hd hv.1.le hv.2.le)
  rw [show cubicLog 0=0 by simp [cubicLog],sub_zero,sub_zero] at he
  have hc2 := (sq_le_sq₀ hc.1.le hz.le).mpr hc.2.le
  have hz2 := (sq_le_sq₀ hz.le (by norm_num : (0:ℝ)≤3/4)).mpr hz'
  have hden : 0<1-c^2 := by nlinarith only [hc2,hz2]
  have hf : -(5*z^2)≤f' c ∧ f' c≤0 := by
    constructor
    · apply (le_div_iff₀ hden).mpr
      have hden' : (7:ℝ)/16≤1-c^2 := by nlinarith only [hc2,hz2]
      nlinarith only [hc2,mul_le_mul_of_nonneg_left hden' (sq_nonneg z),sq_nonneg z]
    · exact div_nonpos_of_nonpos_of_nonneg (by nlinarith only [sq_nonneg c]) hden.le
  have hx := (eq_div_iff hz.ne').mp he
  constructor
  · nlinarith only [hx,mul_le_mul_of_nonneg_right hf.1 hz.le]
  · exact hx ▸ mul_nonpos_of_nonpos_of_nonneg hf.2 hz.le

private theorem exp_cubicLog {z : ℝ} (hz : 0≤z) (hu : z<1) :
    Real.exp (cubicLog z)=((1-z)*Real.exp z)^2*(1-z^2)⁻¹ := by
  have hl : 0<1-z := sub_pos.mpr hu
  have hr : 0<1+z := by linarith only [hz]
  rw [cubicLog,Real.exp_sub,Real.exp_add,Real.exp_log hl,Real.exp_log hr,two_mul,Real.exp_add,
    show 1-z^2=(1-z)*(1+z) by ring]
  field_simp [hl.ne',hr.ne'] <;> ring

/-- From the right of one half, the square of the correction times zeta at
twice the argument stays between two strictly positive constants. -/
theorem reciprocalFactorialEulerCorrection_square_bounds :
    ∃ c : ℝ, 0<c ∧ ∀ s : ℝ, 1/2<s →
      c≤(reciprocalFactorialEulerCorrection s)^2*(riemannZeta ((2*s:ℝ):ℂ)).re ∧
      (reciprocalFactorialEulerCorrection s)^2*(riemannZeta ((2*s:ℝ):ℂ)).re≤1 := by
  let major (p : Nat.Primes) := 5*((p:ℕ):ℝ)^(-(3/2:ℝ))
  have hmaj : Summable major :=
    ((Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ)< -1)).subtype Nat.Prime).mul_left 5
  let C := ∑' p, major p
  refine ⟨Real.exp (-C),Real.exp_pos _,fun s hs => ?_⟩
  let z (p : Nat.Primes) := ((p:ℕ):ℝ)^(-s)
  have hp₀ (p : Nat.Primes) : 0<((p:ℕ):ℝ) := by exact_mod_cast p.prop.pos
  have hp₁ (p : Nat.Primes) : 1≤((p:ℕ):ℝ) := by exact_mod_cast p.prop.one_le
  have hz₀ (p : Nat.Primes) : 0<z p := Real.rpow_pos_of_pos (hp₀ p) _
  have hex (p : Nat.Primes) (k : ℕ) : (z p)^k=((p:ℕ):ℝ)^((-s)*(k:ℝ)) := by
    rw [← Real.rpow_natCast (z p) k,← Real.rpow_mul (hp₀ p).le]; rfl
  have hz₁ (p : Nat.Primes) : z p≤3/4 := by
    have h₂ : (z p)^2≤((p:ℕ):ℝ)⁻¹ := by
      rw [hex,← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (hp₁ p) (by push_cast; linarith only [hs])
    have hi : ((p:ℕ):ℝ)⁻¹≤1/2 := by
      rw [one_div,inv_le_inv₀ (hp₀ p) (by norm_num)]; exact_mod_cast p.prop.two_le
    by_contra! h
    nlinarith only [h₂,hi,h,sq_nonneg (z p-3/4)]
  have hlog (p : Nat.Primes) : -(major p)≤cubicLog (z p) ∧ cubicLog (z p)≤0 := by
    have he := cubicLog_bound (hz₀ p) (hz₁ p)
    have hm : (z p)^3≤((p:ℕ):ℝ)^(-(3/2:ℝ)) := by
      rw [hex]
      exact Real.rpow_le_rpow_of_exponent_le (hp₁ p) (by push_cast; linarith only [hs])
    exact ⟨(neg_le_neg (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤5))).trans he.1,he.2⟩
  have he := correction_hasProd hs
  have hzeta := _root_.RHTower.hasProd_primeEulerFactor (show 1<2*s by linarith only [hs])
  have hprod : HasProd (fun p : Nat.Primes => Real.exp (cubicLog (z p)))
      ((reciprocalFactorialEulerCorrection s)^2*(riemannZeta ((2*s:ℝ):ℂ)).re) := by
    rw [pow_two]
    apply ((he.mul he).mul hzeta).congr_fun
    intro p
    rw [exp_cubicLog (hz₀ p).le (lt_of_le_of_lt (hz₁ p) (by norm_num)),pow_two]
    have hs' : (z p)^2=((p:ℕ):ℝ)^(-(2*s)) := (hex p 2).trans (by push_cast; ring_nf)
    rw [hs']; rfl
  constructor
  · refine ge_of_tendsto' hprod (fun S => ?_)
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    have hS := hmaj.sum_le_tsum S (fun p _ => by dsimp only [major]; positivity)
    have hL := sum_le_sum (fun p (_ : p∈S) => (hlog p).1)
    rw [sum_neg_distrib] at hL
    exact (neg_le_neg hS).trans hL
  · refine le_of_tendsto' hprod (fun S => ?_)
    rw [← Real.exp_sum,Real.exp_le_one_iff]
    exact sum_nonpos fun p _ => (hlog p).2

#print axioms reciprocalFactorialEulerCorrection_square_bounds

end GaloisForLFunctions.ExceptionalLayerTheory
