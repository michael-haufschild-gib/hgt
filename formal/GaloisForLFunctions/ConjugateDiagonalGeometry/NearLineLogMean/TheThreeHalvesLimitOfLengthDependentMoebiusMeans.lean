import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheEndpointScalesOfTheSmoothedMoebiusTail
import GaloisForLFunctions.ArithmeticProduction.TheLengthPrecisionLaw

/-!
# The two-mode limit for logarithmically smoothed Möbius windows

The Dirichlet mean-value theorem charges the squared coefficient mass.
Its weight at n, relative to the squarefree harmonic diagonal, is exactly
the square of the endpoint scale. This controls the mean even at lengths
and orders where the absolute coefficient tail diverges. The two undamped
modes contribute one and one half.
-/

noncomputable section
open Finset Filter Topology MeasureTheory ArithmeticFunction
open GaloisForLFunctions.ArithmeticProduction
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def ratio (n : ℕ) := Real.log 2/Real.log (max 2 n : ℕ)
private def a (m n : ℕ) := (ratio n:ℂ)^m*_root_.RHTower.mobCoeff n
private def mass (n : ℕ) := ((moebius n:ℤ):ℝ)^2/(n:ℝ)

private theorem weighted_line (m N : ℕ) (t : ℝ) : logDampedMoebius m N t = linePoly (a m) N t := by
  change _root_.RHTower.edPoly (a m) (Icc 1 N) _ = _root_.RHTower.edPoly (a m) (Icc 1 N) _
  congr 1
  norm_num [MultiscaleMollifiedZetaField.linePoint]

private theorem r_nonneg (n : ℕ) : 0 ≤ ratio n :=
  div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ max 2 n by omega)))

private theorem a_norm (m n : ℕ) : ‖a m n‖^2=((moebius n:ℤ):ℝ)^2*(ratio n)^(2*m) := by
  rw [a,norm_mul,_root_.RHTower.mobCoeff,Complex.norm_intCast,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (r_nonneg n),mul_pow,←pow_mul,sq_abs,show m*2=2*m by omega]
  ring

private theorem split_two {G : Type*} [AddCommGroup G] {N : ℕ} (hN : 2 ≤ N) (f : ℕ → G) :
    (∑ n ∈ Icc 1 N, f n)=f 1+f 2+∑ n ∈ Icc 3 N, f n := by
  have hsub : Icc 1 2 ⊆ Icc 1 N := fun n hn => mem_Icc.mpr
    ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans hN⟩
  have hi : Icc 1 N \ Icc 1 2 = Icc 3 N := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_sdiff,Finset.mem_Icc]
    omega
  have hh := sum_sdiff_eq_sub (f:=f) hsub
  rw [hi] at hh
  have hI : Icc 1 2=({1,2}:Finset ℕ) := by
    apply Finset.ext; intro n; simp only [mem_Icc,mem_insert,mem_singleton]; omega
  rw [hI,sum_insert (by simp),sum_singleton] at hh
  exact (eq_sub_iff_add_eq.mp hh).symm.trans (add_comm _ _)

private theorem a_first (m : ℕ) : ‖a m 1‖^2=1 ∧ ‖a m 2‖^2=1 := by
  have hL := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  constructor <;> simp [a_norm,ratio,div_self hL,ArithmeticFunction.moebius_apply_prime Nat.prime_two]

private theorem scale_rat (m : ℕ) {n : ℕ} (h : 2 ≤ n) :
    (logTailScale m n)^2=(n:ℝ)*(ratio n)^(2*m) := by
  rw [ratio,max_eq_right h,logTailScale_sq _ (by exact_mod_cast (show 1 < n by omega))]

private theorem htail_le {N : ℕ} :
    (∑ n ∈ Icc 3 N, mass n) ≤ harmonicMoebiusDiagonal N := by
  rw [harmonicMoebiusDiagonal,Nat.floor_natCast]
  exact sum_le_sum_of_subset_of_nonneg (fun n hn => mem_Icc.mpr
    ⟨by have := (mem_Icc.mp hn).1; omega,(mem_Icc.mp hn).2⟩)
    fun n _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

private theorem tail_bounds (m N : ℕ) :
    let H := harmonicMoebiusDiagonal N
    let V := max (logTailScale m 3) (logTailScale m N)
    (∑ n ∈ Icc 3 N, ‖a m n‖^2) ≤ H*V^2 ∧
    (∑ n ∈ Icc 3 N, ‖a m n‖^2/n) ≤ H*(Real.log 2/Real.log 3)^(2*m) := by
  intro H V
  have hlow (n : ℕ) (hn : n ∈ Icc 3 N) : ratio n ≤ Real.log 2/Real.log 3 := by
    have hn3 := (mem_Icc.mp hn).1
    rw [ratio,max_eq_right (by omega : 2 ≤ n)]
    exact div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) (Real.log_pos (by norm_num))
      (Real.log_le_log (by norm_num) (by exact_mod_cast hn3))
  have htop (n : ℕ) (hn : n ∈ Icc 3 N) : ‖a m n‖^2 ≤ mass n*V^2 := by
    have h3 := (mem_Icc.mp hn).1
    have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h := logTailScale_le_endpoints m (by norm_num : (1:ℝ)<3)
      (show (3:ℝ) ≤ n by exact_mod_cast h3) (Nat.cast_le.mpr (mem_Icc.mp hn).2)
    have hh := pow_le_pow_left₀ (Real.exp_pos _).le h 2
    change (logTailScale m n)^2 ≤ V^2 at hh
    rw [scale_rat m (by omega : 2 ≤ n)] at hh
    calc ‖a m n‖^2 = mass n*((n:ℝ)*(ratio n)^(2*m)) := by rw [a_norm,mass]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have htail := (sum_le_sum htop).trans_eq (sum_mul ..).symm
  have hres := htail.trans (mul_le_mul_of_nonneg_right (htail_le (N:=N)) (sq_nonneg V))
  let r := (Real.log 2/Real.log 3)^(2*m)
  have hr : 0 ≤ r := pow_nonneg (div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num))) _
  have hsq (n : ℕ) (hn : n ∈ Icc 3 N) : ‖a m n‖^2/n ≤ mass n*r := by
    rw [a_norm,mass,mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (r_nonneg n) (hlow n hn) _)
      (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hdt := ((sum_le_sum hsq).trans_eq (sum_mul ..).symm).trans
    (mul_le_mul_of_nonneg_right (htail_le (N:=N)) hr)
  exact ⟨hres,hdt⟩

/-- A finite window's distance from the two-mode mean. The first term is
the diagonal tail. The second is the Dirichlet mean-value error on that
very window and uses only the two endpoint scales. -/
theorem finite_window_error_from_three_halves (m : ℕ) {N : ℕ} (hN : 3 ≤ N)
    {A D : ℝ} (hAD : A < D) :
    let H := harmonicMoebiusDiagonal N
    let V := max (logTailScale m 3) (logTailScale m N)
    |(∫ t in A..D, ‖logDampedMoebius m N t‖^2)/(D-A)-3/2| ≤
      H*(Real.log 2/Real.log 3)^(2*m) + 208*(2+H*V^2)/(D-A) := by
  intro H V
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hres,hdt⟩ := tail_bounds m N
  let r := (Real.log 2/Real.log 3)^(2*m)
  have hdt0 : 0 ≤ ∑ n ∈ Icc 3 N, ‖a m n‖^2/n := by positivity
  have hz := abs_integral_norm_sq_linePoly_sub_le (a m) N A D
  simp_rw [←weighted_line] at hz
  rw [split_two hN2 (fun n => ‖a m n‖^2/n),split_two hN2 (fun n => ‖a m n‖^2)] at hz
  simp only [(a_first m).1,(a_first m).2,Nat.cast_one,Nat.cast_ofNat,div_one] at hz
  let I := ∫ t in A..D, ‖logDampedMoebius m N t‖^2
  let b := ∑ n ∈ Icc 3 N, ‖a m n‖^2/(n:ℝ)
  change 0 ≤ b at hdt0
  change b ≤ H*r at hdt
  have hAD' := sub_pos.mpr hAD
  have he : I/(D-A)-3/2=(I-(D-A)*(1+1/2+b))/(D-A)+b := by field_simp; ring
  change |I/(D-A)-3/2| ≤ H*r+208*(2+H*V^2)/(D-A)
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div,abs_of_pos hAD',abs_of_nonneg hdt0]
  have hme := hz.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1+1:ℝ)) hres) (by norm_num : (0:ℝ) ≤ 208))
  have hd := div_le_div_of_nonneg_right hme hAD'.le
  change |I-(D-A)*(1+1/2+b)|/(D-A) ≤ 208*((1+1)+H*V^2)/(D-A) at hd
  change _ ≤ H*r+208*(2+H*V^2)/(D-A)
  linarith only [hd,hdt]

/-- Mean-square distance to the undamped two-mode polynomial on the
original observation window. The error contains only the tail coefficients. -/
theorem finite_two_mode_approximation (m : ℕ) {N : ℕ} (hN : 3 ≤ N) {A D : ℝ} (hAD : A < D) :
    let H := harmonicMoebiusDiagonal N
    let V := max (logTailScale m 3) (logTailScale m N)
    (∫ t in A..D, ‖logDampedMoebius m N t -
      MultiscaleMollifiedZetaField.moebiusPoly 2 (MultiscaleMollifiedZetaField.linePoint t)‖^2)/(D-A) ≤
      H*(Real.log 2/Real.log 3)^(2*m) + 208*(H*V^2)/(D-A) := by
  intro H V
  have hN2 : 2 ≤ N := by omega
  let c (n : ℕ) := if n ≤ 2 then 0 else a m n
  have htail {G : Type} [AddCommGroup G] (f : ℕ → ℂ → G) (hf : ∀ n, f n 0 = 0) :
      (∑ n ∈ Icc 1 N, f n (c n)) = ∑ n ∈ Icc 3 N, f n (a m n) := by
    rw [split_two hN2]
    simp only [c,show 1 ≤ 2 by decide,le_refl,if_true,hf,zero_add]
    apply sum_congr rfl
    intro n hn
    rw [if_neg (by have := (mem_Icc.mp hn).1; omega)]
  have he (t : ℝ) : logDampedMoebius m N t -
      MultiscaleMollifiedZetaField.moebiusPoly 2 (MultiscaleMollifiedZetaField.linePoint t) = linePoly c N t := by
    have hb := logDamped_two_mode_le_tail_mass m (N:=2) le_rfl t
    rw [logDampedTailMass,show Icc 3 2 = (∅ : Finset ℕ) from Finset.Icc_eq_empty_of_lt (by decide),sum_empty,
      norm_le_zero_iff,sub_eq_zero] at hb
    rw [←hb,weighted_line,weighted_line]
    unfold linePoly _root_.RHTower.edPoly
    rw [htail (fun n z => z * ((n:ℝ):ℂ)^(-(((1/2:ℝ):ℂ)+(t:ℂ)*Complex.I))) (fun _ => zero_mul _),split_two hN2,split_two (N:=2) le_rfl]
    rw [show Icc 3 2 = (∅ : Finset ℕ) from Finset.Icc_eq_empty_of_lt (by decide),sum_empty,add_zero]
    abel
  simp_rw [he]
  have hz := abs_integral_norm_sq_linePoly_sub_le c N A D
  rw [htail (fun n z => ‖z‖^2/n) (by intro n; simp),htail (fun _ z => ‖z‖^2) (by intro n; simp)] at hz
  obtain ⟨hres,hdiag⟩ := tail_bounds m N
  have h := (le_abs_self _).trans hz
  apply (div_le_iff₀ (sub_pos.mpr hAD)).mpr
  rw [add_mul,div_mul_cancel₀ _ (sub_pos.mpr hAD).ne']
  have hd := mul_le_mul_of_nonneg_right hdiag (sub_pos.mpr hAD).le
  have hr := mul_le_mul_of_nonneg_left hres (by norm_num : (0:ℝ) ≤ 208)
  change _ ≤ harmonicMoebiusDiagonal N*(Real.log 2/Real.log 3)^(2*m)*(D-A) +
    208*(harmonicMoebiusDiagonal N*(max (logTailScale m 3) (logTailScale m N))^2)
  linarith only [h,hd,hr]

private theorem exp_neg_penalty_three (m : ℕ) :
    Real.exp (-logTailPenalty m 3)=(Real.log 2/Real.log 3)^m := by
  have hL := div_pos (Real.log_pos (by norm_num : (1:ℝ)<3)) (Real.log_pos (by norm_num : (1:ℝ)<2))
  rw [logTailPenalty,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hL,←inv_pow,inv_div]

private theorem scale_sq_penalty {x : ℝ} (hx : 0 < x) (m : ℕ) {α : ℝ}
    (h : α*Real.log x ≤ logTailPenalty m x) : (logTailScale m x)^2 ≤ x^(1-2*α) := by
  rw [logTailScale,←Real.exp_nat_mul,Real.rpow_def_of_pos hx,Real.exp_le_exp]
  push_cast
  linarith only [h]

private def windowMajorant (m N : ℕ) (T : ℝ) :=
  let H := harmonicMoebiusDiagonal N
  let V := max (logTailScale m 3) (logTailScale m N)
  H*(Real.log 2/Real.log 3)^(2*m)+208*(2+H*V^2)/(T-1)

private theorem windowMajorant_tendsto_zero {θ α : ℝ} (hθ : 0 < θ) (hα : 0 < α)
    (hmargin : θ*(1-2*α) < 1) (m : ℝ → ℕ)
    (hpay : ∀ᶠ T : ℝ in atTop, α*Real.log ⌊T^θ⌋₊ ≤ logTailPenalty (m T) ⌊T^θ⌋₊) :
    Tendsto (fun T : ℝ => windowMajorant (m T) ⌊T^θ⌋₊ T) atTop (𝓝 0) := by
  let N (T : ℝ) := ⌊T^θ⌋₊
  let C := _root_.RHTower.Sieve.squarefreeDensity+(|squarefreeHarmonicConstant|+12)
  have hdens : 0 < _root_.RHTower.Sieve.squarefreeDensity := by rw [_root_.RHTower.Sieve.squarefreeDensity_eq]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let b := max 0 (1-2*α)
  let p := θ*b
  have hb : 0 ≤ b := le_max_left _ _
  have hp : 0 ≤ p := mul_nonneg hθ.le hb
  have hp1 : p < 1 := by
    rcases le_total 0 (1-2*α) with h|h
    · simpa only [p,b,max_eq_right h] using hmargin
    · simp only [p,b,max_eq_left h,mul_zero,zero_lt_one]
  have hgap := sub_pos.mpr hp1
  have hn : Tendsto N atTop atTop := tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hθ)
  have hy := Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hn)
  have hlog : Tendsto (fun T : ℝ => Real.log T/T^(1-p)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hgap).tendsto_div_nhds_zero
  have h0 := (hy.inv_tendsto_atTop.const_mul C).add
    (((show Tendsto (fun T : ℝ => T) atTop atTop from tendsto_id).inv_tendsto_atTop.const_mul 832).add (hlog.const_mul (1248*C*θ)))
  have hbound : Tendsto (fun T : ℝ => C*(Real.log (N T))⁻¹+
      (832*T⁻¹+(1248*C*θ)*(Real.log T/T^(1-p)))) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add,Function.comp_apply,Pi.inv_apply] using h0
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    unfold windowMajorant harmonicMoebiusDiagonal
    dsimp only
    have h0 := sub_pos.mpr hT
    have hlog : 0 ≤ Real.log 2/Real.log 3 := div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num))
    positivity
  filter_upwards [eventually_ge_atTop (2:ℝ),hn.eventually_ge_atTop 3,hy.eventually_ge_atTop 1,
    hn.eventually (cutoff_penalty_at_three hα),hpay] with T hT hN hy1 hthree hpen
  let y := Real.log (N T)
  let H := harmonicMoebiusDiagonal (N T)
  let V := max (logTailScale (m T) 3) (logTailScale (m T) (N T))
  have hT1 : 1 < T := by linarith only [hT]
  have hT0 := zero_lt_one.trans hT1
  have hn1 : (1:ℝ) ≤ N T := Nat.one_le_cast.mpr (by omega)
  have hy0 : 0 < y := zero_lt_one.trans_le hy1
  have hH := squarefree_harmonic_le_log hn1 hy1
  change H ≤ C*y at hH
  have hH0 : 0 ≤ H := by unfold H harmonicMoebiusDiagonal; positivity
  have hNT : (N T:ℝ) ≤ T^θ := Nat.floor_le (Real.rpow_nonneg hT0.le _)
  have hyT : y ≤ θ*Real.log T := by
    simpa only [Real.log_rpow hT0] using Real.log_le_log (zero_lt_one.trans_le hn1) hNT
  have hTpow : 1 ≤ T^p := Real.one_le_rpow hT1.le hp
  have hnq := (scale_sq_penalty (zero_lt_one.trans_le hn1) (m T) hpen).trans
    ((Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right 0 (1-2*α))).trans
      (Real.rpow_le_rpow (zero_le_one.trans hn1) hNT hb))
  change (logTailScale (m T) (N T))^2 ≤ (T^θ)^b at hnq
  rw [←Real.rpow_mul hT0.le] at hnq
  have hr0 : 0 ≤ Real.log 2/Real.log 3 := div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num))
  have hr1 : Real.log 2/Real.log 3 ≤ 1 := (div_le_one (Real.log_pos (by norm_num))).mpr
    (Real.log_le_log (by norm_num) (by norm_num))
  have hsmall := Real.exp_le_exp.mpr (neg_le_neg (hthree _ hpen))
  have hex : Real.exp (-(2*Real.log y))=(y^2)⁻¹ := by rw [Real.exp_neg,show 2*Real.log y=Real.log (y^2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (sq_pos_of_pos hy0)]
  change Real.exp (-logTailPenalty (m T) 3) ≤ Real.exp (-(2*Real.log y)) at hsmall
  rw [hex,exp_neg_penalty_three] at hsmall
  have hrpow : (Real.log 2/Real.log 3)^(2*m T) ≤ (y^2)⁻¹ := by
    rw [two_mul,pow_add]
    exact (mul_le_of_le_one_left (pow_nonneg hr0 _) (pow_le_one₀ hr0 hr1)).trans hsmall
  have hfirst := mul_le_mul hH hrpow (pow_nonneg hr0 _) (mul_nonneg hC hy0.le)
  have heq : C*y*(y^2)⁻¹=C*y⁻¹ := by field_simp
  rw [heq] at hfirst
  have hv3 : (logTailScale (m T) 3)^2 ≤ 3 := by
    rw [logTailScale_sq _ (by norm_num : (1:ℝ)<3)]
    exact mul_le_of_le_one_right (by norm_num) (pow_le_one₀ hr0 hr1)
  have hv : V^2 ≤ 3*T^p := by
    rcases le_total (logTailScale (m T) 3) (logTailScale (m T) (N T)) with h|h
    · rw [show V=logTailScale (m T) (N T) from max_eq_right h]
      exact hnq.trans (le_mul_of_one_le_left (zero_le_one.trans hTpow) (by norm_num))
    · rw [show V=logTailScale (m T) 3 from max_eq_left h]
      exact hv3.trans (le_mul_of_one_le_right (by norm_num) hTpow)
  have htden : 1/(T-1) ≤ 2/T := (div_le_div_iff₀ (sub_pos.mpr hT1) hT0).mpr (by linarith only [hT])
  have hcT := hH.trans (mul_le_mul_of_nonneg_left hyT hC)
  have hR := mul_le_mul hcT hv (sq_nonneg V) (mul_nonneg hC (mul_nonneg hθ.le (Real.log_nonneg hT1.le)))
  have hrem := mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add (le_refl (2:ℝ)) hR) (by norm_num : (0:ℝ) ≤ 208))
    htden (div_nonneg zero_le_one (sub_pos.mpr hT1).le)
    (mul_nonneg (by norm_num) (add_nonneg zero_le_two ((mul_nonneg hH0 (sq_nonneg V)).trans hR)))
  have hquot : T^p/T=(T^(1-p))⁻¹ := by
    rw [←Real.rpow_neg hT0.le,show -(1-p)=p-1 by ring,Real.rpow_sub hT0,Real.rpow_one]
  have he : 208*(2+(C*(θ*Real.log T))*(3*T^p))*(2/T) =
      832*T⁻¹+(1248*C*θ)*(Real.log T/T^(1-p)) := by
    rw [div_eq_mul_inv (Real.log T),←hquot]; ring
  rw [he,one_div] at hrem
  apply add_le_add hfirst
  simpa only [div_eq_mul_inv] using hrem

/-- For a fixed polynomial length exponent θ, the full mean tends to 3/2
once the logarithmic penalty fraction α satisfies θ(1-2α)<1. The order
can change independently at each height. -/
theorem moebius_mean_tendsto_three_halves {θ α : ℝ} (hθ : 0 < θ) (hα : 0 < α)
    (hmargin : θ*(1-2*α) < 1) (m : ℝ → ℕ)
    (hpay : ∀ᶠ T : ℝ in atTop, α*Real.log ⌊T^θ⌋₊ ≤ logTailPenalty (m T) ⌊T^θ⌋₊) :
    Tendsto (fun T : ℝ => logDampedMoment (m T) θ T/(T-1)) atTop (𝓝 (3/2)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (windowMajorant_tendsto_zero hθ hα hmargin m hpay)
  filter_upwards [eventually_gt_atTop (1:ℝ),(tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hθ)).eventually_ge_atTop 3] with T hT hN
  exact (Real.norm_eq_abs _).le.trans (finite_window_error_from_three_halves (m T) hN hT)

/-- Every translate of the observation window has the same two-mode
mean-square approximation, even when its starting point depends on height. -/
theorem moebius_section_two_mode_convergence_on_translates {θ α : ℝ}
    (hθ : 0 < θ) (hα : 0 < α) (hmargin : θ*(1-2*α) < 1) (m : ℝ → ℕ) (start : ℝ → ℝ)
    (hpay : ∀ᶠ T : ℝ in atTop, α*Real.log ⌊T^θ⌋₊ ≤ logTailPenalty (m T) ⌊T^θ⌋₊) :
    Tendsto (fun T : ℝ => (∫ t in start T..(start T+(T-1)), ‖logDampedMoebius (m T) ⌊T^θ⌋₊ t -
      MultiscaleMollifiedZetaField.moebiusPoly 2 (MultiscaleMollifiedZetaField.linePoint t)‖^2)/(T-1))
      atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (windowMajorant_tendsto_zero hθ hα hmargin m hpay)
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact div_nonneg (intervalIntegral.integral_nonneg (le_add_of_nonneg_right (sub_nonneg.mpr hT.le))
      fun _ _ => sq_nonneg _) (sub_pos.mpr hT).le
  filter_upwards [eventually_gt_atTop (1:ℝ),(tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hθ)).eventually_ge_atTop 3] with T hT hN
  have hd : start T < start T+(T-1) := lt_add_of_pos_right _ (sub_pos.mpr hT)
  have H := finite_two_mode_approximation (m T) hN hd
  dsimp only at H
  rw [add_sub_cancel_left] at H
  apply H.trans
  exact add_le_add le_rfl (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2)) (by norm_num : (0:ℝ) ≤ 208)) (sub_pos.mpr hT).le)

/-- The complete section converges to its first two modes in time-averaged
mean square, including at penalty fraction 1/2 for every polynomial length. -/
theorem moebius_section_two_mode_convergence {θ α : ℝ} (hθ : 0 < θ) (hα : 0 < α)
    (hmargin : θ*(1-2*α) < 1) (m : ℝ → ℕ)
    (hpay : ∀ᶠ T : ℝ in atTop, α*Real.log ⌊T^θ⌋₊ ≤ logTailPenalty (m T) ⌊T^θ⌋₊) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖logDampedMoebius (m T) ⌊T^θ⌋₊ t -
      MultiscaleMollifiedZetaField.moebiusPoly 2 (MultiscaleMollifiedZetaField.linePoint t)‖^2)/(T-1))
      atTop (𝓝 0) := by
  simpa only [show ∀ T : ℝ, 1+(T-1)=T from fun _ => by ring] using moebius_section_two_mode_convergence_on_translates hθ hα hmargin
    m (fun _ => 1) hpay

/-- The explicit cutoff order obtains the same exact limit. -/
theorem cutoff_order_three_halves {θ α : ℝ} (hθ : 0 < θ) (hα : 0 < α) (hmargin : θ*(1-2*α) < 1) :
    Tendsto (fun T : ℝ => logDampedMoment (cutoffLogarithmicOrder α ⌊T^θ⌋₊) θ T/(T-1))
      atTop (𝓝 (3/2)) := by
  apply moebius_mean_tendsto_three_halves hθ hα hmargin
  exact ((tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hθ)).eventually_ge_atTop 3).mono
    fun T hT => cutoffLogarithmicOrder_penalty α hT

/-- Subcritical filters can have divergent absolute tail and the exact
two-mode mean on the same growing polynomial sections. -/
theorem divergent_tail_with_two_mode_mean {θ α : ℝ} (hθ : 0 < θ) (hα : 0 < α)
    (hhalf : α < 1/2) (hmargin : θ*(1-2*α) < 1) :
    let N := fun T : ℝ => ⌊T^θ⌋₊
    (Tendsto (fun T => logDampedTailMass (cutoffLogarithmicOrder α (N T)) (N T)) atTop atTop) ∧
    Tendsto (fun T => logDampedMoment (cutoffLogarithmicOrder α (N T)) θ T/(T-1)) atTop (𝓝 (3/2)) :=
  ⟨(subcritical_cutoff_tail_diverges hα.le hhalf).comp (tendsto_nat_floor_atTop.comp
    (tendsto_rpow_atTop hθ)),cutoff_order_three_halves hθ hα hmargin⟩

#print axioms moebius_section_two_mode_convergence_on_translates
#print axioms moebius_section_two_mode_convergence
#print axioms finite_two_mode_approximation
#print axioms divergent_tail_with_two_mode_mean
#print axioms cutoff_order_three_halves
#print axioms moebius_mean_tendsto_three_halves
#print axioms finite_window_error_from_three_halves

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
