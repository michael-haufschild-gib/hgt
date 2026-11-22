import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedVariance.Continuation

/-!
# Residues transferred by the digit variance

At a twice-translated clock point the scale gap is 1 − B². Dividing the
variance coupling by that gap transports every surviving harmonic, with
the same frequency and a nonzero quadratic multiplier.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedVariance

open BalancedContinuation BalancedShift

abbrev second (t : ExceptionalTime) (j : ℕ) (k : ℤ) := point t j k-2

def multiplier (t : ExceptionalTime) (j : ℕ) (s : ℂ) := -(s*(s+1))/(24*((base t j:ℂ)+1))

theorem second_re (t : ExceptionalTime) (j : ℕ) (k : ℤ) : (second t j k).re = -(3/2) := by
  change (1/2:ℝ)-2 = -(3/2)
  ring

theorem scale_off (t : ExceptionalTime) (j : ℕ) (s : ℂ) (hs : ∀ k, s ≠ point t j k) :
    denominator t j s ≠ 0 := fun hz =>
  let ⟨k,hk⟩ := (scaleFactor_zero_iff _ _).mp hz
  hs k hk

private theorem clock_zero (t : ExceptionalTime) (j : ℕ) (k : ℤ) : denominator t j (point t j k) = 0 :=
  (scaleFactor_zero_iff _ _).mpr ⟨k,rfl⟩

private theorem second_scale (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    denominator t j (second t j k) = 1-(base t j:ℂ)^2 := by
  let u := second t j k
  let B := base t j
  have hb : (B:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (base_pos t j).ne'
  have h := clock_zero t j k
  rw [scale_weight,sub_eq_zero] at h
  have hu : (u+1)+1 = point t j k := by dsimp only [u,second]; ring
  rw [← hu,weight_succ (base_pos t j),weight_succ (base_pos t j)] at h
  rw [scale_weight]
  change 1-(radix t j:ℂ)*weight B u = 1-(B:ℂ)^2
  change 1 = (radix t j:ℂ)*(weight B u*(B:ℂ)⁻¹*(B:ℂ)⁻¹) at h
  field_simp [hb] at h
  linear_combination h

private theorem second_ne (t : ExceptionalTime) (j : ℕ) (k : ℤ) : denominator t j (second t j k) ≠ 0 :=
  scale_off t j _ (fun n hn => (by norm_num : -(3/2:ℝ) ≠ 1/2)
    ((second_re t j k).symm.trans (congrArg Complex.re hn)))

private theorem transfer_value (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    varianceFactor t j (second t j k) = multiplier t j (second t j k)*denominator t j (second t j k) := by
  let u := second t j k
  let B := base t j
  have hclock := clock_zero t j k
  rw [scale_weight,sub_eq_zero] at hclock
  have hB : (B:ℂ)+1 ≠ 0 := by exact_mod_cast (add_pos (base_pos t j) zero_lt_one).ne'
  rw [varianceFactor,multiplier,second_scale,sub_add_cancel]
  change u*(u+1)*(radix t j:ℂ)*((B:ℂ)-1)*weight B (point t j k)/24 =
    -(u*(u+1))/(24*((B:ℂ)+1))*(1-(B:ℂ)^2)
  calc
    _ = u*(u+1)*((B:ℂ)-1)*((radix t j:ℂ)*weight B (point t j k))/24 := by ring
    _ = _ := by rw [← hclock]; field_simp [hB]; ring

private theorem multiplier_ne (t : ExceptionalTime) (j : ℕ) (k : ℤ) : multiplier t j (second t j k) ≠ 0 := by
  let u := second t j k
  have hr := second_re t j k
  have hu : u ≠ 0 := by intro h; have he := congrArg Complex.re h; change (second t j k).re = 0 at he; linarith only [hr,he]
  have hv : u+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    change (second t j k).re+1=0 at he
    linarith only [hr,he]
  have hB : (base t j:ℂ)+1 ≠ 0 := by exact_mod_cast (add_pos (base_pos t j) zero_lt_one).ne'
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hu hv)) (mul_ne_zero (by norm_num) hB)

private theorem simple_data (t : ExceptionalTime) (j : ℕ) (s : Region) {v : ℂ}
    (h₀ : fullScale t j s.val = 0) (hd : HasDerivAt (fullScale t j) v s.val) (hv : v ≠ 0) :
    HTGeometry.laurentCoeff (continued t j) s.val (-1) = fullNum t j s.val/v ∧
    (meromorphicOrderAt (continued t j) s.val < 0 ↔ fullNum t j s.val ≠ 0) ∧
    (meromorphicOrderAt (continued t j) s.val = (-1:ℤ) ↔ fullNum t j s.val ≠ 0) := by
  have h := simple_scale (H := fun _ => 0) analyticAt_const (fullNum_analytic t j s)
    (scale_analytic t j s.val) h₀ (hd.deriv ▸ hv)
  simpa only [zero_add,hd.deriv,continued] using h

/-- Primary residues and the simple-pole support agree with the original balanced partition. -/
theorem primary_data (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    let w := point t j k
    HTGeometry.laurentCoeff (continued t j) w (-1) = HTGeometry.laurentCoeff (continuation t j) w (-1) ∧
      (meromorphicOrderAt (continued t j) w < 0 ↔ meromorphicOrderAt (continuation t j) w = (-1:ℤ)) ∧
      (meromorphicOrderAt (continued t j) w = (-1:ℤ) ↔ meromorphicOrderAt (continuation t j) w = (-1:ℤ)) := by
  let w := point t j k
  let l := 2*((logRadix t j).val:ℂ)
  let b := denominator t j (w+2)
  have hl : l ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (logRadix t j).property.ne')
  have hb : b ≠ 0 := scale_right t j ⟨w+2,by change (1/2:ℝ) < 1/2+2; norm_num⟩
  have hz := clock_zero t j k
  have hd : HasDerivAt (fullScale t j) (l*b) w := by
    simpa only [hz,zero_mul,add_zero] using
      (scaleFactor_derivative (logRadix t j) k).mul (movedScale_analytic t j w).differentiableAt.hasDerivAt
  have h := simple_data t j ⟨w,by change -(7/2:ℝ) < 1/2; norm_num⟩
    (by change denominator t j (point t j k)*_ = 0; rw [hz,zero_mul]) hd (mul_ne_zero hl hb)
  have hN : fullNum t j w = numerator t j w*b := by
    rw [overlap t j ⟨w,by change -(3/2:ℝ) < 1/2; norm_num⟩,centeredNum_clock]
  change HTGeometry.laurentCoeff (continued t j) w (-1) = _ ∧ _ at h ⊢
  simpa only [hN,mul_div_mul_right _ _ hb,mul_ne_zero_iff,and_iff_left hb,clock_residue,clock_pole_iff] using h

/-- Each lower-line residue is an explicit, nonzero multiple of its primary residue.
The corresponding poles occur in pairs and have order one. -/
theorem secondary_data (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    let u := second t j k
    let w := point t j k
    HTGeometry.laurentCoeff (continued t j) u (-1) =
      multiplier t j u*HTGeometry.laurentCoeff (continuation t j) w (-1) ∧
      (meromorphicOrderAt (continued t j) u < 0 ↔ meromorphicOrderAt (continuation t j) w = (-1:ℤ)) ∧
      (meromorphicOrderAt (continued t j) u = (-1:ℤ) ↔ meromorphicOrderAt (continuation t j) w = (-1:ℤ)) := by
  let u := second t j k
  let w := point t j k
  let l := 2*((logRadix t j).val:ℂ)
  let b := denominator t j u
  let v := multiplier t j u
  have hu : u+2 = w := sub_add_cancel _ _
  have hl : l ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (logRadix t j).property.ne')
  have hb : b ≠ 0 := second_ne t j k
  have hv : v ≠ 0 := multiplier_ne t j k
  have hzero : denominator t j (u+2) = 0 := hu ▸ clock_zero t j k
  have hder : HasDerivAt (denominator t j) l (u+2) := hu ▸ scaleFactor_derivative (logRadix t j) k
  have hm : HasDerivAt (fun z => denominator t j (z+2)) l u := by
    simpa only [Function.comp_def,id_eq,mul_one] using hder.comp u ((hasDerivAt_id u).add_const 2)
  have hd : HasDerivAt (fullScale t j) (b*l) u := by
    simpa only [hzero,mul_zero,zero_add] using (scaleFactor_analytic (logRadix t j).val u).differentiableAt.hasDerivAt.mul hm
  have hr : -(7/2) < u.re := by change -(7/2) < (second t j k).re; rw [second_re]; norm_num
  have h := simple_data t j ⟨u,hr⟩ (by change b*denominator t j (u+2) = 0; rw [hzero,mul_zero]) hd (mul_ne_zero hb hl)
  have hN : fullNum t j u = (v*b)*numerator t j w := by rw [fullNum,hzero,mul_zero,zero_add,hu,centeredNum_clock,transfer_value]
  have hr₁ : (v*b*numerator t j w)/(b*l) = v*(numerator t j w/l) := by field_simp [hb,hl]
  change HTGeometry.laurentCoeff (continued t j) u (-1) = _ ∧ _ at h ⊢
  simpa only [hN,hr₁,mul_ne_zero_iff,hv,hb,true_and,clock_residue,clock_pole_iff] using h

#print axioms primary_data
#print axioms secondary_data

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedVariance
