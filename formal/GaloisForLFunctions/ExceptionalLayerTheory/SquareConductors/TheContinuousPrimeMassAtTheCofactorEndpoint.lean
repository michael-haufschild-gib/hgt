import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.FourCofactorCapsAtAZetaZero
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.FirstPrimesBeyondTheConductorInTheSignedPrefix
import GaloisForLFunctions.RHTower.BurnolAlternatingHarmonic

/-!
# Continuous prime mass at a common lower prime endpoint

A first-prime interval above P and below product y has length y/v-P at
cofactor v. Its signed mass has a constant term proportional to P.
Taking the difference of two product endpoints removes that term.
-/

noncomputable section
open Finset RHTower.DQPT
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem cofactorDyadicCoefficient_pos : 0<cofactorDyadicCoefficient := by
  have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
  by_contra! h
  have hprod := mul_nonpos_of_nonpos_of_nonneg h (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  linarith only [cofactor_density_normalization,hlog,hprod]

/-- The common lower prime endpoint has strictly negative density drift.
The fourth alternating harmonic sum and its positive remainder give log 2 > 2/3. -/
theorem cofactor_density_drift_neg : (cofactorDyadicCoefficient-1)/2<0 := by
  have h := _root_.RHTower.burnolAlternatingHarmonic_eq 4
  have hr := _root_.RHTower.burnolAltTail_split 4
  have hp := _root_.RHTower.burnolAltTailRemainder_nonneg 4
  have ha : _root_.RHTower.burnolAlternatingHarmonic 4=(7/12:ℝ) := by
    norm_num [_root_.RHTower.burnolAlternatingHarmonic,Finset.sum_range_succ]
  rw [ha,show (-1:ℝ)^4=1 by norm_num,one_mul] at h
  have hl : (2/3:ℝ)<Real.log 2 := by linarith only [h,hr,hp]
  by_contra! hc
  have hm := mul_le_mul_of_nonneg_right (show (3/2:ℝ)≤1+cofactorDyadicCoefficient/2 by linarith only [hc])
    (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  linarith only [hl,hm,cofactor_density_normalization]

private theorem alternating_quotient_at_one (N : ℕ) :
    dqptAltPartialSum 1 N = (_root_.RHTower.burnolAlternatingHarmonic N : ℂ) := by
  simp [dqptAltPartialSum,_root_.RHTower.burnolAlternatingHarmonic,dqptRp,Complex.cpow_neg_one,div_eq_mul_inv]

/-- At the density pole only the two signed last-cap remainders survive. -/
theorem cofactorDirichletPrefix_density {N : ℕ} (hN : 0<N) :
    cofactorDirichletPrefix 1 N =
      (((-1:ℝ)^N*_root_.RHTower.burnolAltTail N+
        cofactorDyadicCoefficient/2*(-1:ℝ)^(N/2)*_root_.RHTower.burnolAltTail (N/2):ℝ):ℂ) := by
  rw [cofactorDirichletPrefix_eq,if_neg hN.ne',alternating_quotient_at_one,alternating_quotient_at_one,
    _root_.RHTower.burnolAlternatingHarmonic_eq N,_root_.RHTower.burnolAlternatingHarmonic_eq (N/2)]
  have h : (((1+cofactorDyadicCoefficient/2)*Real.log 2:ℝ):ℂ)=1 := by
    rw [cofactor_density_normalization,Complex.ofReal_one]
  rw [dqptRp,Complex.cpow_neg_one]
  push_cast at h ⊢
  linear_combination -h

private theorem harmonic_tail_bounds (m : ℕ) : 0<_root_.RHTower.burnolAltTail m ∧
    _root_.RHTower.burnolAltTail m≤1/((m:ℝ)+1) := by
  rw [_root_.RHTower.burnolAltTail_split]
  have h₀ := _root_.RHTower.burnolAltTailRemainder_nonneg m
  have h₁ := _root_.RHTower.burnolAltTailRemainder_le m
  have hm : (0:ℝ)<(m:ℝ)+1 := by positivity
  have hu := one_div_le_one_div_of_le hm
    (le_mul_of_one_le_right hm.le (by linarith only [Nat.cast_nonneg (α := ℝ) m] : (1:ℝ)≤(m:ℝ)+2))
  have he : 1/(2*((m:ℝ)+1))=(1/((m:ℝ)+1))/2 := by field_simp
  rw [he]
  constructor
  · exact add_pos_of_pos_of_nonneg (half_pos (one_div_pos.mpr hm)) (div_nonneg h₀ (by norm_num))
  · linarith only [h₁.trans hu]

/-- The harmonic density has size O(1/N) at every sharp cap. -/
theorem cofactorDirichletPrefix_density_bound {N : ℕ} (hN : 0<N) :
    ‖cofactorDirichletPrefix 1 N‖ ≤
      1/((N:ℝ)+1)+(cofactorDyadicCoefficient/2)*(1/(((N/2:ℕ):ℝ)+1)) := by
  rw [cofactorDirichletPrefix_density hN,Complex.norm_real,Real.norm_eq_abs]
  apply (abs_add_le _ _).trans
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,mul_one,
    abs_of_pos (harmonic_tail_bounds N).1,abs_of_pos (harmonic_tail_bounds (N/2)).1,
    abs_of_pos (div_pos cofactorDyadicCoefficient_pos (by norm_num : (0:ℝ) < 2))]
  exact add_le_add (harmonic_tail_bounds N).2
    (mul_le_mul_of_nonneg_left (harmonic_tail_bounds (N/2)).2 (div_pos cofactorDyadicCoefficient_pos (by norm_num : (0:ℝ) < 2)).le)

/-- Two sharp caps in each block of four give opposite strict density signs. -/
theorem opposite_cofactor_density_endpoints {K : ℕ} (hK : 0<K) :
    0<(cofactorDirichletPrefix 1 (4*K)).re ∧ (cofactorDirichletPrefix 1 (4*K+3)).re<0 := by
  rw [cofactorDirichletPrefix_density (by omega : 0<4*K),
    cofactorDirichletPrefix_density (by omega : 0<4*K+3),Complex.ofReal_re,Complex.ofReal_re]
  rw [show 4*K/2=2*K by omega,show (4*K+3)/2=2*K+1 by omega]
  simp only [pow_add,pow_mul,show (-1:ℝ)^4=1 by norm_num,show (-1:ℝ)^2=1 by norm_num,
    show (-1:ℝ)^3= -1 by norm_num,one_pow,pow_one,one_mul,mul_one,mul_neg_one,neg_one_mul]
  have h₀ := (harmonic_tail_bounds (4*K)).1
  have h₁ := (harmonic_tail_bounds (2*K)).1
  have h₂ := (harmonic_tail_bounds (4*K+3)).1
  have h₃ := (harmonic_tail_bounds (2*K+1)).1
  constructor
  · exact add_pos h₀ (mul_pos (div_pos cofactorDyadicCoefficient_pos (by norm_num)) h₁)
  · linarith only [h₂,mul_pos (div_pos cofactorDyadicCoefficient_pos (by norm_num : (0:ℝ)<2)) h₃]

/-- Signed cofactor mass of the continuous intervals from 1 to x/v. -/
def cofactorDensityRamp (x : ℝ) : ℝ :=
  ∑ j ∈ range ⌊x⌋₊, innerJump 1 (j+1)*(x/((j:ℝ)+1)-1)

/-- With lower prime endpoint P the scaled ramp is the signed total length
of the prime intervals (P, b/v] over the cofactors v ≤ b/P. -/
theorem cofactorDensityRamp_interval_lengths {P : ℝ} (hP : 0<P) (b : ℝ) :
    P*cofactorDensityRamp (b/P) = ∑ j ∈ range ⌊b/P⌋₊, innerJump 1 (j+1)*(b/((j:ℝ)+1)-P) := by
  unfold cofactorDensityRamp
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  field_simp

/-- On a product cell a < pv ≤ b the difference of scaled ramps is the
signed length of the prime intervals max(P, a/v) < p ≤ b/v. -/
theorem cofactorDensityRamp_cell {P a b : ℝ} (hP : 0<P) (ha : 0≤a) (hab : a≤b) :
    P*cofactorDensityRamp (b/P)-P*cofactorDensityRamp (a/P) =
      ∑ j ∈ range ⌊b/P⌋₊, innerJump 1 (j+1)*(b/((j:ℝ)+1)-max P (a/((j:ℝ)+1))) := by
  have hm : ⌊a/P⌋₊ ≤ ⌊b/P⌋₊ := Nat.floor_mono (div_le_div_of_nonneg_right hab hP.le)
  have hlow (j : ℕ) (hj : j ∈ range ⌊a/P⌋₊) :
      innerJump 1 (j+1)*(b/((j:ℝ)+1)-max P (a/((j:ℝ)+1))) =
        innerJump 1 (j+1)*(b/((j:ℝ)+1)-P)-innerJump 1 (j+1)*(a/((j:ℝ)+1)-P) := by
    have hj1 : ((j+1:ℕ):ℝ) ≤ a/P :=
      (Nat.le_floor_iff (div_nonneg ha hP.le)).mp (Nat.succ_le_of_lt (mem_range.mp hj))
    push_cast at hj1
    have hPa : P ≤ a/((j:ℝ)+1) := by
      rw [le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ hP] at hj1
      linarith only [hj1]
    rw [max_eq_right hPa]
    ring
  have hhigh (j : ℕ) (hj : j ∈ Ico ⌊a/P⌋₊ ⌊b/P⌋₊) :
      innerJump 1 (j+1)*(b/((j:ℝ)+1)-max P (a/((j:ℝ)+1))) =
        innerJump 1 (j+1)*(b/((j:ℝ)+1)-P) := by
    have hj1 : a/P < (j:ℝ)+1 := (Nat.lt_floor_add_one (a/P)).trans_le
      (by exact_mod_cast Nat.succ_le_succ (mem_Ico.mp hj).1)
    have haP : a/((j:ℝ)+1) ≤ P := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hP] at hj1
      linarith only [hj1]
    rw [max_eq_left haP]
  rw [cofactorDensityRamp_interval_lengths hP,cofactorDensityRamp_interval_lengths hP,
    ←sum_range_add_sum_Ico (fun j : ℕ => innerJump 1 (j+1)*(b/((j:ℝ)+1)-max P (a/((j:ℝ)+1)))) hm,
    sum_congr rfl hlow,sum_congr rfl hhigh,
    ←sum_range_add_sum_Ico (fun j : ℕ => innerJump 1 (j+1)*(b/((j:ℝ)+1)-P)) hm,sum_sub_distrib]
  ring

private theorem ramp_moments (x : ℝ) :
    cofactorDensityRamp x = x*(cofactorDirichletPrefix 1 ⌊x⌋₊).re -
      (cofactorDirichletPrefix 0 ⌊x⌋₊).re := by
  have e : (cofactorDensityRamp x:ℂ) =
      (x:ℂ)*cofactorDirichletPrefix 1 ⌊x⌋₊ - cofactorDirichletPrefix 0 ⌊x⌋₊ := by
    unfold cofactorDensityRamp cofactorDirichletPrefix
    push_cast
    rw [mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    simp only [dqptRp,Complex.cpow_neg_one,neg_zero,Complex.cpow_zero,mul_one,div_eq_mul_inv]
    push_cast
    ring
  simpa only [Complex.ofReal_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero]
    using congrArg Complex.re e

private theorem alternating_at_zero (n : ℕ) :
    dqptAltPartialSum 0 n=(1-(-1:ℂ)^n)/2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [dqptAltPartialSum_succ,ih,pow_succ]
    simp only [dqptRp,neg_zero,Complex.cpow_zero,mul_one]
    ring

private theorem cofactor_mass_at_zero {m : ℕ} (hm : 0 < m) :
    (cofactorDirichletPrefix 0 m).re = (1-cofactorDyadicCoefficient)/2+
      ((-1:ℝ)^m+cofactorDyadicCoefficient*(-1:ℝ)^(m/2))/2 := by
  have e : cofactorDirichletPrefix 0 m = (((1-cofactorDyadicCoefficient)/2+
      ((-1:ℝ)^m+cofactorDyadicCoefficient*(-1:ℝ)^(m/2))/2:ℝ):ℂ) := by
    rw [cofactorDirichletPrefix_eq,if_neg hm.ne',alternating_at_zero,alternating_at_zero]
    simp only [dqptRp,neg_zero,Complex.cpow_zero,mul_one]
    push_cast
    ring
  rw [e,Complex.ofReal_re]

/-- Uniform across a fractional last cell, including the unit cofactor. -/
private theorem scaled_harmonic_tail {y : ℝ} {j : ℕ} (hl : (j:ℝ)≤y) (hu : y≤(j:ℝ)+1) :
    |y*_root_.RHTower.burnolAltTail j-1/2| ≤ 1/((j:ℝ)+1) := by
  let L := (j:ℝ)+1
  have hL : 0<L := by dsimp only [L]; positivity
  have hL' : 0<L+1 := by positivity
  have hy := (Nat.cast_nonneg j).trans hl
  have htail := _root_.RHTower.abs_burnolAltTail_sub_le j
  change |_root_.RHTower.burnolAltTail j-1/(2*L)| ≤ 1/(2*L*((j:ℝ)+2)) at htail
  rw [show (j:ℝ)+2=L+1 by dsimp only [L]; ring] at htail
  have hsplit : y*_root_.RHTower.burnolAltTail j-1/2 =
      y*(_root_.RHTower.burnolAltTail j-1/(2*L))-(L-y)/(2*L) := by
    field_simp [hL.ne']; ring
  rw [hsplit]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg hy,abs_of_nonneg (div_nonneg (sub_nonneg.mpr hu) (by positivity))]
  have ht := mul_le_mul hu htail (abs_nonneg _) hL.le
  have he : L*(1/(2*L*(L+1)))=1/(2*(L+1)) := by field_simp [hL.ne',hL'.ne']
  rw [he] at ht
  have hfirst := ht.trans (one_div_le_one_div_of_le (by positivity : 0<2*L)
    (by linarith only : 2*L≤2*(L+1)))
  have hsecond := div_le_div_of_nonneg_right (show L-y≤1 by dsimp only [L]; linarith only [hl])
    (by positivity : 0≤2*L)
  exact (add_le_add hfirst hsecond).trans_eq (by change 1/(2*L)+1/(2*L)=1/L; field_simp [hL.ne']; ring)

/-- The signed density through one product cut has a constant leading term.
The cap-dependent parity terms of both terminal moments cancel. -/
theorem cofactor_density_ramp_asymptotic {x : ℝ} (hx0 : 0<x) :
    |cofactorDensityRamp x-(cofactorDyadicCoefficient-1)/2| ≤
      (1+2*|cofactorDyadicCoefficient|)/x := by
  by_cases hx : 1≤x
  swap
  · have hf : ⌊x⌋₊<1 := (Nat.floor_lt hx0.le).mpr (by simpa only [Nat.cast_one] using lt_of_not_ge hx)
    rw [cofactorDensityRamp,show ⌊x⌋₊=0 by omega,range_zero,sum_empty,zero_sub,abs_neg,
      abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have ht := abs_sub cofactorDyadicCoefficient 1
    rw [abs_one] at ht
    have hC : 0≤1+2*|cofactorDyadicCoefficient| := by positivity
    calc _ ≤ 1+2*|cofactorDyadicCoefficient| := by linarith only [ht,abs_nonneg cofactorDyadicCoefficient]
         _ ≤ _ := (le_div_iff₀ hx0).mpr (mul_le_of_le_one_right hC (lt_of_not_ge hx).le)
  let m := ⌊x⌋₊
  let k := m/2
  let c := cofactorDyadicCoefficient
  have hm : 0 < m := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using hx
  have hmx : (m:ℝ)≤x := Nat.floor_le hx0.le
  have hxm : x≤(m:ℝ)+1 := (Nat.lt_floor_add_one x).le
  have hkm : (2:ℝ)*k ≤ m := by exact_mod_cast (show 2*k ≤ m by dsimp only [k]; omega)
  have hmk : (m:ℝ)≤2*k+1 := by exact_mod_cast (show m≤2*k+1 by dsimp only [k]; omega)
  have hkx : (k:ℝ)≤x/2 := by linarith only [hkm,hmx]
  have hxk : x/2≤(k:ℝ)+1 := by linarith only [hmk,hxm]
  have hD : cofactorDensityRamp x-(c-1)/2 =
      (-1:ℝ)^m*(x*_root_.RHTower.burnolAltTail m-1/2)+
      c*(-1:ℝ)^k*((x/2)*_root_.RHTower.burnolAltTail k-1/2) := by
    rw [ramp_moments,cofactorDirichletPrefix_density hm,Complex.ofReal_re,cofactor_mass_at_zero hm]
    dsimp only [m,k,c]
    ring
  rw [hD]
  apply (abs_add_le _ _).trans
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,mul_one]
  have ha := (scaled_harmonic_tail hmx hxm).trans (one_div_le_one_div_of_le hx0 hxm)
  have hb := (scaled_harmonic_tail hkx hxk).trans (one_div_le_one_div_of_le (half_pos hx0) hxk)
  exact (add_le_add ha (mul_le_mul_of_nonneg_left hb (abs_nonneg c))).trans_eq
    (by change 1/x+|c| * (1/(x/2))=(1+2*|c|)/x; field_simp [hx0.ne'])

/-- Signed continuous prime mass on the sharp product cell a < pv ≤ b,
with common lower prime endpoint P. The bound is uniform in b. -/
theorem cofactor_density_on_product_interval {P a b : ℝ} (hP : 0<P) (ha : 0<a) (hb : a≤b) :
    |P*cofactorDensityRamp (b/P)-P*cofactorDensityRamp (a/P)| ≤
      2*(1+2*|cofactorDyadicCoefficient|)*P^2/a := by
  let c := (cofactorDyadicCoefficient-1)/2
  let K := 1+2*|cofactorDyadicCoefficient|
  have hK : 0≤K := by dsimp only [K]; positivity
  have hax := div_pos ha hP
  have hxy := div_le_div_of_nonneg_right hb hP.le
  have h₁ := cofactor_density_ramp_asymptotic hax
  have h₂ := (cofactor_density_ramp_asymptotic (hax.trans_le hxy)).trans
    (div_le_div_of_nonneg_left hK hax hxy)
  rw [←mul_sub,abs_mul,abs_of_pos hP,show cofactorDensityRamp (b/P)-cofactorDensityRamp (a/P)=
    (cofactorDensityRamp (b/P)-c)-(cofactorDensityRamp (a/P)-c) by ring]
  exact (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h₂ h₁)) hP.le).trans_eq
    (by change P*(K/(a/P)+K/(a/P))=2*K*P^2/a; field_simp [hP.ne',ha.ne']; ring)

/-- Continuous first-prime mass in the original positive quotient cells
above U. The last cell is clipped at U with its original sign. -/
def continuousFirstPrimeQuotients (P : ℝ) (U k : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 (k/U), centeredPrimeWeight 1 j *
    (P*cofactorDensityRamp (((k:ℝ)/j)/P) -
      P*cofactorDensityRamp (max (U:ℝ) ((k:ℝ)/((j:ℝ)+1))/P))

/-- All surviving density intervals together cost O(P²k/U²), including
the final partial quotient cell and the common lower prime endpoint. -/
theorem continuous_first_prime_quotient_bound :
    ∃ C : ℝ, 0≤C ∧ ∀ {P : ℝ}, 0<P → ∀ {U : ℕ}, 0<U → ∀ k : ℕ,
      |continuousFirstPrimeQuotients P U k| ≤ C*P^2*k/(U:ℝ)^2 := by
  obtain ⟨B,hB,hW⟩ := centeredPrimeWeight_uniform
  let A := 2*(1+2*|cofactorDyadicCoefficient|)
  have hA : 0≤A := by dsimp only [A]; positivity
  refine ⟨B*A,mul_nonneg hB hA,fun {P} hP {U} hUn k => ?_⟩
  have hU : (0:ℝ)<U := Nat.cast_pos.mpr hUn
  unfold continuousFirstPrimeQuotients
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _j ∈ Icc 1 (k/U), B*(A*P^2/U) := by
              apply sum_le_sum
              intro j hj
              obtain ⟨hj₁,hj₂⟩ := mem_Icc.mp hj
              have hj0 : (0:ℝ)<j := Nat.cast_pos.mpr hj₁
              have huj : (U:ℝ)≤(k:ℝ)/j := by
                apply (le_div_iff₀ hj0).mpr
                exact_mod_cast (show U*j≤k by simpa only [Nat.mul_comm U j] using
                  (Nat.le_div_iff_mul_le hUn).mp hj₂)
              have hadj := div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) k) hj0
                (le_add_of_nonneg_right (zero_le_one : (0:ℝ)≤1))
              let a := max (U:ℝ) ((k:ℝ)/((j:ℝ)+1))
              have hua : (U:ℝ)≤a := le_max_left _ _
              have hc := cofactor_density_on_product_interval hP (hU.trans_le hua) (max_le huj hadj)
              rw [abs_mul]
              exact mul_le_mul (by simpa only [Nat.cast_one,mul_one] using hW (R := 1) le_rfl j)
                (hc.trans (div_le_div_of_nonneg_left (mul_nonneg hA (sq_nonneg P)) hU hua))
                (abs_nonneg _) hB
       _ ≤ ((k:ℝ)/U)*(B*(A*P^2/U)) := by
              rw [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
              exact mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
       _ = _ := by field_simp [hU.ne']

/-- Lebesgue density at the exact first-prime cutoff and all spline horizons. -/
def capFreePrimeDensityReading (U n : ℕ) :=
  splineCountReading n (continuousFirstPrimeQuotients (max 4 (capFreeFirstPrimeCut n):ℕ) U)

private theorem density_at_conductor_horizons :
    ∃ C : ℝ, 0≤C ∧ ∀ {n : ℕ}, 0<n → ∀ {k : ℕ}, k≤ splineHorizon n →
      |continuousFirstPrimeQuotients (max 4 (capFreeFirstPrimeCut n):ℕ) ⌊(n:ℝ)^(17/9:ℝ)⌋₊ k| ≤
        C*(n:ℝ)^(2/9:ℝ) := by
  obtain ⟨A,hA,ha⟩ := continuous_first_prime_quotient_bound
  obtain ⟨K,hK,hcut⟩ := capFreeFirstPrimeCut_linear
  obtain ⟨T,hT,hL⟩ := successorSquare_window_bound
  let G := A*(K+4)^2*T^2
  have hG : 0≤G := by dsimp only [G]; positivity
  refine ⟨4*G,by positivity,fun {n} hn {k} hk => ?_⟩
  let P := max 4 (capFreeFirstPrimeCut n)
  let X := (n:ℝ)^(17/9:ℝ)
  let U := ⌊X⌋₊
  let R := (n:ℝ)^(2/9:ℝ)
  have hn₁ : 1≤(n:ℝ) := by exact_mod_cast hn
  have hn₀ := zero_lt_one.trans_le hn₁
  have hx : 1≤X := Real.one_le_rpow hn₁ (by norm_num)
  have hu : 0<U := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using hx
  have hu₁ : 1≤(U:ℝ) := by exact_mod_cast hu
  have hp₀ : (0:ℝ)<P := Nat.cast_pos.mpr ((by decide : 0<4).trans_le (le_max_left _ _))
  have hp : (P:ℝ)≤(K+4)*n := by
    dsimp only [P]
    rw [Nat.cast_max,Nat.cast_ofNat]
    exact max_le (by linarith only [hn₁,mul_nonneg hK hn₀.le]) (by linarith only [hcut hn,hn₀.le])
  have hk' : (k:ℝ)≤(T*n)^2 := (Nat.cast_le.mpr hk).trans (hL hn)
  have hnum := mul_le_mul (pow_le_pow_left₀ hp₀.le hp 2) hk' (Nat.cast_nonneg k) (sq_nonneg _)
  have hX : X≤2*(U:ℝ) := by linarith only [Nat.lt_floor_add_one X,hu₁]
  have hX₂ := pow_le_pow_left₀ (zero_le_one.trans hx) hX 2
  have hR : 0≤R := Real.rpow_nonneg hn₀.le _
  have hpow : R*X^2=(n:ℝ)^4 := by
    dsimp only [R,X]
    rw [←Real.rpow_two ((n:ℝ)^(17/9:ℝ)),←Real.rpow_mul hn₀.le,←Real.rpow_add hn₀,
      show (2/9:ℝ)+(17/9)*2=(4:ℕ) by norm_num,Real.rpow_natCast]
  apply (ha hp₀ hu k).trans ((div_le_iff₀ (sq_pos_of_pos (Nat.cast_pos.mpr hu : (0:ℝ)<U))).mpr ?_)
  calc A*(P:ℝ)^2*k = A*((P:ℝ)^2*k) := by ring
       _ ≤ A*(((K+4)*n)^2*(T*n)^2) := mul_le_mul_of_nonneg_left hnum hA
       _ = G*(n:ℝ)^4 := by dsimp only [G]; ring
       _ = (G*R)*X^2 := by rw [←hpow]; ring
       _ ≤ (G*R)*(2*(U:ℝ))^2 := mul_le_mul_of_nonneg_left hX₂ (mul_nonneg hG hR)
       _ = _ := by ring

/-- All continuous first-prime density in the remaining signed prefix costs
O(M^(20/9)) on every terminal conductor fragment. -/
theorem seventeenNinths_prime_density_fragments :
    ∃ C : ℝ, 0≤C ∧ ∀ J M : ℕ,
      |∑ n ∈ Ioc J M, (n:ℝ)^2*capFreePrimeDensityReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n| ≤
        C*(M:ℝ)^(20/9:ℝ) := by
  obtain ⟨A,hA,ha⟩ := density_at_conductor_horizons
  obtain ⟨D,_,hD,_,hd⟩ := sampledSpline_differences
  obtain ⟨T,_,hT⟩ := successorSquare_window_bound
  let C := T^2*A*D
  have hC : 0≤C := by dsimp only [C]; positivity
  have row {n : ℕ} (hn : 0<n) :
      |(n:ℝ)^2*capFreePrimeDensityReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n| ≤ C*(n:ℝ)^(11/9:ℝ) := by
    have hn₀ : (0:ℝ)<n := Nat.cast_pos.mpr hn
    let R := (n:ℝ)^(2/9:ℝ)
    let E := (A*R)*(D/(n:ℝ)^3)
    have hR : 0≤R := Real.rpow_nonneg hn₀.le _
    have hE : 0≤E := mul_nonneg (mul_nonneg hA hR) (div_nonneg hD (pow_nonneg hn₀.le 3))
    rw [abs_mul,abs_of_nonneg (sq_nonneg (n:ℝ))]
    have hp : |capFreePrimeDensityReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n| ≤ (T*n)^2*E := by
      unfold capFreePrimeDensityReading splineCountReading
      apply (abs_sum_le_sum_abs _ _).trans
      calc _ ≤ ∑ _k ∈ Icc 1 (splineHorizon n), E := by
                apply sum_le_sum
                intro k hk
                rw [abs_mul]
                exact mul_le_mul (ha hn (mem_Icc.mp hk).2) ((hd hn k).1) (abs_nonneg _) (mul_nonneg hA hR)
           _ ≤ _ := by
                rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
                exact mul_le_mul_of_nonneg_right (hT hn) hE
    apply (mul_le_mul_of_nonneg_left hp (sq_nonneg (n:ℝ))).trans_eq
    rw [show (11/9:ℝ)=1+2/9 by norm_num,Real.rpow_add hn₀,Real.rpow_one]
    dsimp only [C,E,R]
    field_simp [hn₀.ne']
  refine ⟨C,hC,fun J M => ?_⟩
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _n ∈ Ioc J M, C*(M:ℝ)^(11/9:ℝ) := by
              apply sum_le_sum
              intro n hn
              exact (row ((Nat.zero_le J).trans_lt (mem_Ioc.mp hn).1)).trans (mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (Nat.cast_nonneg n) (Nat.cast_le.mpr (mem_Ioc.mp hn).2) (by norm_num)) hC)
       _ ≤ (M:ℝ)*(C*(M:ℝ)^(11/9:ℝ)) := by
              rw [sum_const,nsmul_eq_mul,Nat.card_Ioc]
              exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M J)) (by positivity)
       _ = _ := by
              rw [show (20/9:ℝ)=1+11/9 by norm_num,Real.rpow_add (Nat.cast_pos.mpr hM),Real.rpow_one]
              ring

/-- The original signed prefix is approximated on every fragment by the
ordinary first-prime reading with its interval lengths subtracted. -/
theorem seventeenNinths_first_prime_discrepancy_comparison :
    ∃ C : ℝ, 0≤C ∧ ∀ J M : ℕ,
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        (capFreeFirstPrimeReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n -
          capFreePrimeDensityReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n))| ≤ C*(M:ℝ)^3*conductorLog M := by
  obtain ⟨A,hA,ha⟩ := seventeenNinths_cap_free_first_prime_fragments
  obtain ⟨B,hB,hb⟩ := seventeenNinths_prime_density_fragments
  refine ⟨A+B,add_nonneg hA hB,fun J M => ?_⟩
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  let U := fun n : ℕ => ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  let E := fun n : ℕ => (n:ℝ)^2*(cappedUpperProductReading (U n) n n-capFreeFirstPrimeReading (U n) n)
  let D := fun n : ℕ => (n:ℝ)^2*capFreePrimeDensityReading (U n) n
  have he : (∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading (U n) n n -
      (capFreeFirstPrimeReading (U n) n-capFreePrimeDensityReading (U n) n))) =
      (∑ n ∈ Ioc J M, E n)+∑ n ∈ Ioc J M, D n := by
    rw [←sum_add_distrib]
    exact sum_congr rfl fun n _ => by dsimp only [D,E]; ring
  change |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading (U n) n n -
    (capFreeFirstPrimeReading (U n) n-capFreePrimeDensityReading (U n) n))| ≤ _
  rw [he]
  apply (abs_add_le _ _).trans ((add_le_add (ha J M) (hb J M)).trans _)
  have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM : (1:ℝ)≤M)
    (by norm_num : (20/9:ℝ)≤(3:ℕ))
  rw [Real.rpow_natCast] at hpow
  have hl := hpow.trans (le_mul_of_one_le_right (pow_nonneg (Nat.cast_nonneg M) 3) (conductorLog_one_le M))
  linarith only [mul_le_mul_of_nonneg_left hl hB]

#print axioms cofactor_density_drift_neg
#print axioms cofactorDirichletPrefix_density
#print axioms cofactorDirichletPrefix_density_bound
#print axioms opposite_cofactor_density_endpoints
#print axioms seventeenNinths_first_prime_discrepancy_comparison
#print axioms seventeenNinths_prime_density_fragments
#print axioms continuous_first_prime_quotient_bound
#print axioms cofactor_density_ramp_asymptotic
#print axioms cofactor_density_on_product_interval
#print axioms cofactorDensityRamp_interval_lengths
#print axioms cofactorDensityRamp_cell
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
