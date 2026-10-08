import GaloisForLFunctions.RHTower.WeilWorkDeficitPrimeKernelBudget

/-!
# Opposite signs of the first two actual integer correlation columns

The Schlaefli integral and its order recurrence bound the order-one/order-zero
Bessel ratio. Expanding the actual cusp polynomials then gives opposite strict
signs for the first two product kernels throughout `x ≥ 2`. Absolute divisor
summation transfers those signs to every nontrivial integer shift and gives
opposite strict energy gaps at `x = 1`.

The first-derivative gap disproves the universal first-kernel comparison
proposed in WP06 C21a. This does not decide simultaneous positive-mixture
cancellation or the spectral-deficit target.
-/

open MeasureTheory Set Polynomial
open GaloisForLFunctions.HTGeometry
open RHTower RHTower.WeilWorkDeficitPrimeKernel
noncomputable section
namespace RHTower.WeilWorkDeficitSign

private theorem bessel_two {z : ℝ} (hz : 0 < z) :
    realModifiedBesselKOrder z 2 = realModifiedBesselKOrder z 0 +
      (2/z)*realModifiedBesselKOrder z 1 := by
  have h := modifiedBesselKOrder_add_one hz (1:ℂ)
  norm_num at h
  rw [show (2:ℂ)=(2:ℝ) by norm_num,
    show (0:ℂ)=(0:ℝ) by norm_num, show (1:ℂ)=(1:ℝ) by norm_num,
    modifiedBesselKOrder_ofReal hz, modifiedBesselKOrder_ofReal hz,
    modifiedBesselKOrder_ofReal hz] at h
  exact_mod_cast h

private theorem bessel_ratio {z : ℝ} (hz : 1 ≤ z) :
    realModifiedBesselKOrder z 1 ≤ (1+1/z)*realModifiedBesselKOrder z 0 := by
  have hz0 : 0 < z := by linarith
  have h0 := integrableOn_realBesselOrderKernel hz0 0
  have h1 := integrableOn_realBesselOrderKernel hz0 1
  have h2 := integrableOn_realBesselOrderKernel hz0 2
  have hpoint (u : ℝ) : 4*realBesselOrderKernel z 1 u - 3*realBesselOrderKernel z 0 u ≤
      realBesselOrderKernel z 2 u := by
    have hc : 4*Real.cosh u-3 ≤ Real.cosh (2*u) := by
      rw [two_mul,Real.cosh_add]
      nlinarith [Real.cosh_sq_sub_sinh_sq u, sq_nonneg (Real.cosh u-1)]
    have he := mul_le_mul_of_nonneg_left hc (Real.exp_pos (-z*Real.cosh u)).le
    simp only [realBesselOrderKernel,one_mul,zero_mul,Real.cosh_zero,mul_one]
    calc _ = Real.exp (-z*Real.cosh u)*(4*Real.cosh u-3) := by ring
         _ ≤ _ := he
  have hi : 4*realModifiedBesselKOrder z 1-3*realModifiedBesselKOrder z 0 ≤
      realModifiedBesselKOrder z 2 := by
    rw [realModifiedBesselKOrder,realModifiedBesselKOrder,realModifiedBesselKOrder,
      ← integral_const_mul, ← integral_const_mul, ← integral_sub (h1.const_mul 4) (h0.const_mul 3)]
    exact integral_mono_ae ((h1.const_mul 4).sub (h0.const_mul 3)) h2
      (Filter.Eventually.of_forall hpoint)
  rw [bessel_two hz0] at hi
  have hb0 := (realModifiedBesselKOrder_pos hz0 0).le
  have hb1 := (realModifiedBesselKOrder_pos hz0 1).le
  have hs : (2*z-1)*realModifiedBesselKOrder z 1 ≤ 2*z*realModifiedBesselKOrder z 0 := by
    have h := mul_le_mul_of_nonneg_left hi hz0.le
    have he : z*((2/z)*realModifiedBesselKOrder z 1) = 2*realModifiedBesselKOrder z 1 := by
      field_simp
    nlinarith
  have hz1 : 0 < 2*z-1 := by linarith
  have hc : 2*z/(2*z-1) ≤ 1+1/z := by
    rw [div_le_iff₀ hz1]
    field_simp
    nlinarith
  calc _ ≤ (2*z/(2*z-1))*realModifiedBesselKOrder z 0 := by
         rw [div_mul_eq_mul_div, le_div_iff₀ hz1]
         nlinarith only [hs]
       _ ≤ _ := mul_le_mul_of_nonneg_right hc hb0

private theorem poly_zero : riemannKernelPoly 0 =
    C (4*Real.pi^2)*X^2-C (6*Real.pi)*X := by
  apply Polynomial.funext
  intro x
  simp [riemannKernelPoly,riemannCuspPoly,cuspDeriv]
  ring

private theorem poly_one : riemannKernelPoly 1 =
    C (-15*Real.pi)*X+C (30*Real.pi^2)*X^2-C (8*Real.pi^3)*X^3 := by
  have he : riemannKernelPoly 1 = cuspDeriv (riemannKernelPoly 0) := by
    simp [riemannKernelPoly]
  rw [he,poly_zero]
  apply Polynomial.funext
  intro x
  simp [cuspDeriv, -map_pow]
  ring

private theorem bessel_neg (z r : ℝ) :
    realModifiedBesselKOrder z (-r) = realModifiedBesselKOrder z r := by
  simp [realModifiedBesselKOrder,realBesselOrderKernel,neg_mul,Real.cosh_neg]

private theorem kernel_zero (x : ℝ) : productKernel 0 x =
    4*(Real.pi*x)^2 * ((4*(Real.pi*x)^2+9)*realModifiedBesselKOrder (2*Real.pi*x) 0 -
      12*(Real.pi*x)*realModifiedBesselKOrder (2*Real.pi*x) 1) := by
  have hd : (riemannKernelPoly 0).natDegree = 2 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_riemannKernelPoly_le 0)
    rw [poly_zero]
    norm_num only [coeff_sub,coeff_C_mul,coeff_X_pow,coeff_X]
    simp only [ite_true,ite_false,mul_one,mul_zero,sub_zero]
    positivity
  unfold productKernel
  rw [hd,poly_zero]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,coeff_sub,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num [bessel_neg]
  ring

private theorem kernel_one {x : ℝ} (hx : 0 < x) : productKernel 1 x =
    -(Real.pi*x)^2 * ((64*(Real.pi*x)^4+1140*(Real.pi*x)^2+225)*
      realModifiedBesselKOrder (2*Real.pi*x) 0 -
      (480*(Real.pi*x)^3+660*(Real.pi*x))*realModifiedBesselKOrder (2*Real.pi*x) 1) := by
  have hd : (riemannKernelPoly 1).natDegree = 3 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_riemannKernelPoly_le 1)
    rw [poly_one]
    norm_num only [coeff_sub,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X]
    simp only [ite_true,ite_false,mul_one,mul_zero,add_zero,zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero 3 Real.pi_pos.ne'))
  unfold productKernel
  rw [hd,poly_one]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,coeff_sub,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num [bessel_neg]
  rw [bessel_two (by positivity : 0 < 2*Real.pi*x)]
  field_simp
  ring

/-- The order-zero product kernel is strictly positive throughout the arithmetic tail. -/
theorem productKernel_zero_pos {x : ℝ} (hx : 2 ≤ x) : 0 < productKernel 0 x := by
  have hy : 6 ≤ Real.pi*x := by nlinarith [Real.pi_gt_three]
  have hr := bessel_ratio (by nlinarith : 1 ≤ 2*Real.pi*x)
  have hp := realModifiedBesselKOrder_pos (by nlinarith : 0 < 2*Real.pi*x) 0
  have he : 12*(Real.pi*x)*(1+1/(2*Real.pi*x)) = 12*(Real.pi*x)+6 := by field_simp; ring
  have hb : 0 < (4*(Real.pi*x)^2+9)*realModifiedBesselKOrder (2*Real.pi*x) 0 -
      12*(Real.pi*x)*realModifiedBesselKOrder (2*Real.pi*x) 1 := by
    have hm := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 12*(Real.pi*x))
    have he' := congrArg (fun v : ℝ => v*realModifiedBesselKOrder (2*Real.pi*x) 0) he
    have hc : 0 < 4*(Real.pi*x)^2-12*(Real.pi*x)+3 := by nlinarith
    nlinarith only [hm,he',mul_pos hc hp]
  rw [kernel_zero]
  exact mul_pos (by positivity) hb

/-- The first-derivative product kernel is strictly negative throughout the arithmetic tail. -/
theorem productKernel_one_neg {x : ℝ} (hx : 2 ≤ x) : productKernel 1 x < 0 := by
  have hx0 : 0 < x := by linarith
  have hy : 6 ≤ Real.pi*x := by nlinarith [Real.pi_gt_three]
  have hr := bessel_ratio (by nlinarith : 1 ≤ 2*Real.pi*x)
  have hp := realModifiedBesselKOrder_pos (by nlinarith : 0 < 2*Real.pi*x) 0
  have he : (480*(Real.pi*x)^3+660*(Real.pi*x))*(1+1/(2*Real.pi*x)) =
      480*(Real.pi*x)^3+240*(Real.pi*x)^2+660*(Real.pi*x)+330 := by field_simp; ring
  have hq : 0 < 64*(Real.pi*x)^4-480*(Real.pi*x)^3+900*(Real.pi*x)^2-660*(Real.pi*x)-105 := by
    have heq : 64*(Real.pi*x)^4-480*(Real.pi*x)^3+900*(Real.pi*x)^2-660*(Real.pi*x)-105 =
        64*(Real.pi*x-6)^4+1056*(Real.pi*x-6)^3+6084*(Real.pi*x-6)^2+
          13596*(Real.pi*x-6)+7599 := by ring
    rw [heq]
    have hnon : 0 ≤ Real.pi*x-6 := by linarith
    positivity
  have hb : 0 < (64*(Real.pi*x)^4+1140*(Real.pi*x)^2+225)*
      realModifiedBesselKOrder (2*Real.pi*x) 0 -
      (480*(Real.pi*x)^3+660*(Real.pi*x))*realModifiedBesselKOrder (2*Real.pi*x) 1 := by
    have hm := mul_le_mul_of_nonneg_left hr
      (by positivity : 0 ≤ 480*(Real.pi*x)^3+660*(Real.pi*x))
    have he' := congrArg (fun v : ℝ => v*realModifiedBesselKOrder (2*Real.pi*x) 0) he
    nlinarith only [hm,he',mul_pos hq hp]
  rw [kernel_one hx0]
  exact mul_neg_of_neg_of_pos (by nlinarith [sq_pos_of_pos (by nlinarith : 0 < Real.pi*x)]) hb

open RHTower.WeilWorkDeficitBessel

private theorem kernel_hasSum (k : ℕ) (y : ℝ) :
    HasSum (fun N : ℕ => (N.divisorsAntidiagonal.card : ℝ) * Real.exp (y/2) *
      productKernel k ((N:ℝ)*Real.exp y))
      (∫ u, (riemannKernelDeriv k u).re * (riemannKernelDeriv k (u-y)).re) := by
  have h := (hasSum_sum (s := Finset.range ((riemannKernelPoly k).natDegree+1))
    (fun j _ => hasSum_sum (s := Finset.range ((riemannKernelPoly k).natDegree+1))
      (fun l _ => (summable_divisor_bessel j l y).hasSum.mul_left
        ((riemannKernelPoly k).coeff j * (riemannKernelPoly k).coeff l)))).mul_left ((-1:ℝ)^k)
  convert h using 1 <;> try rfl
  · funext N
    simp only [productKernel,besselMonomial,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  · exact derivative_correlation_bessel k k y

private theorem signed_correlation_pos (e : ℝ) (k : ℕ)
    (hk : ∀ x : ℝ, 2 ≤ x → 0 < e*productKernel k x)
    {n : ℕ} (hn : 2 ≤ n) :
    0 < e*(∫ u, (riemannKernelDeriv k u).re *
      (riemannKernelDeriv k (u-Real.log n)).re) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs := (kernel_hasSum k (Real.log n)).mul_left e
  have he (N : ℕ) : e*((N.divisorsAntidiagonal.card:ℝ)*Real.exp (Real.log n/2)*
      productKernel k ((N:ℝ)*Real.exp (Real.log n))) =
      ((N.divisorsAntidiagonal.card:ℝ)*Real.exp (Real.log n/2))*(e*productKernel k ((N:ℝ)*n)) := by
    rw [Real.exp_log hn0]
    ring
  have hnon (N : ℕ) : 0 ≤ e*((N.divisorsAntidiagonal.card:ℝ)*Real.exp (Real.log n/2)*
      productKernel k ((N:ℝ)*Real.exp (Real.log n))) := by
    by_cases hN : N=0
    · simp [hN,Nat.divisorsAntidiagonal_zero]
    · rw [he]
      apply mul_nonneg (by positivity) (hk _ ?_).le
      have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
  have hpos : 0 < e*((1:ℕ).divisorsAntidiagonal.card*Real.exp (Real.log n/2)*
      productKernel k (((1:ℕ):ℝ)*Real.exp (Real.log n))) := by
    rw [he]
    simp only [Nat.divisorsAntidiagonal_one,Finset.card_singleton,Nat.cast_one,one_mul]
    exact mul_pos (Real.exp_pos _) (hk _ (by exact_mod_cast hn))
  simpa only [hs.tsum_eq] using hs.summable.tsum_pos hnon 1 hpos

private theorem signed_energy_gap_pos (e : ℝ) (k : ℕ)
    (hk : ∀ x : ℝ, 2 ≤ x → 0 < e*productKernel k x) :
    0 < e*((∫ u, (riemannKernelDeriv k u).re^2)-productKernel k 1) := by
  have hs : HasSum (fun N : ℕ => e*((N.divisorsAntidiagonal.card:ℝ)*productKernel k N))
      (e*(∫ u, (riemannKernelDeriv k u).re^2)) := by
    simpa only [zero_div,Real.exp_zero,mul_one,sub_zero,←pow_two] using
      (kernel_hasSum k 0).mul_left e
  have hg : HasSum (fun N : ℕ => if N=1 then e*productKernel k 1 else 0)
      (e*productKernel k 1) := by
    apply hasSum_single 1
    intro b hb
    simp [hb]
  have hgap := hs.sub hg
  have hn (N : ℕ) : 0 ≤ e*((N.divisorsAntidiagonal.card:ℝ)*productKernel k N)-
      (if N=1 then e*productKernel k 1 else 0) := by
    by_cases hN0 : N=0
    · simp [hN0,Nat.divisorsAntidiagonal_zero]
    by_cases hN1 : N=1
    · simp [hN1,Nat.divisorsAntidiagonal_one]
    rw [if_neg hN1,sub_zero]
    have h := mul_nonneg (Nat.cast_nonneg N.divisorsAntidiagonal.card)
      (hk N (by exact_mod_cast (by omega : 2 ≤ N))).le
    nlinarith only [h]
  have hp : 0 < e*(((2:ℕ).divisorsAntidiagonal.card:ℝ)*productKernel k 2)-
      (if (2:ℕ)=1 then e*productKernel k 1 else 0) := by
    have hcard : 0 < (2:ℕ).divisorsAntidiagonal.card := by
      apply Finset.card_pos.2
      exact ⟨(1,2),by simp [Nat.mem_divisorsAntidiagonal]⟩
    have h := mul_pos (by exact_mod_cast hcard : (0:ℝ)<(2:ℕ).divisorsAntidiagonal.card)
      (hk 2 le_rfl)
    norm_num only at *
    simp only [ite_false,sub_zero] at *
    nlinarith only [h]
  have hh := hgap.summable.tsum_pos hn 2 hp
  rw [hgap.tsum_eq] at hh
  nlinarith only [hh]

/-- Every nontrivial integer shift has positive order-zero correlation. -/
theorem correlation_zero_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < (∫ u, (riemannKernelDeriv 0 u).re *
      (riemannKernelDeriv 0 (u-Real.log n)).re) := by
  simpa only [one_mul] using signed_correlation_pos 1 0
    (fun x hx => by simpa only [one_mul] using productKernel_zero_pos hx) hn

/-- Every nontrivial integer shift has negative first-derivative correlation. -/
theorem correlation_one_neg {n : ℕ} (hn : 2 ≤ n) :
    (∫ u, (riemannKernelDeriv 1 u).re *
      (riemannKernelDeriv 1 (u-Real.log n)).re) < 0 := by
  have h := signed_correlation_pos (-1) 1
    (fun x hx => by nlinarith [productKernel_one_neg hx]) hn
  linarith

/-- At order zero, the first product-kernel value lies strictly below the full energy. -/
theorem productKernel_zero_one_lt_energy :
    productKernel 0 1 < ∫ u, (riemannKernelDeriv 0 u).re^2 := by
  have h := signed_energy_gap_pos 1 0
    (fun x hx => by simpa only [one_mul] using productKernel_zero_pos hx)
  linarith

/-- At order one, the first product-kernel value lies strictly above the full energy. -/
theorem energy_one_lt_productKernel_one_one :
    (∫ u, (riemannKernelDeriv 1 u).re^2) < productKernel 1 1 := by
  have h := signed_energy_gap_pos (-1) 1
    (fun x hx => by nlinarith [productKernel_one_neg hx])
  linarith

end RHTower.WeilWorkDeficitSign
