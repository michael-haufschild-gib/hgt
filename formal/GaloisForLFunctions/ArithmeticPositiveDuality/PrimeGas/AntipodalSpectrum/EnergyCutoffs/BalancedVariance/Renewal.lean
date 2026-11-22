import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedVariance.Trace
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedShift.DigitMoments

/-!
# Centered renewal at finite Taylor order

Grouping each derivative by its power of the signed digit expresses the
physical partition in shifted copies of itself. Reflection removes the
odd terms. At degree three, only the variance couples distinct temperatures.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedVariance

open BalancedContinuation BalancedShift

abbrev delta (t : ExceptionalTime) (j : ℕ) := displacement t j (center t j)
abbrev physical (t : ExceptionalTime) (j : ℕ) := partition t j (center t j)

def seeds (t : ExceptionalTime) (j : ℕ) (s : ℂ) :=
  ∑ d : First (radix t j), weight ((d.val.val:ℝ)+center t j) s

def regular (t : ExceptionalTime) (j m : ℕ) (s : ℂ) := seeds t j s+
  ∑ d : Fin (radix t j), errorTrace t j m (base t j) (delta t j d) s

def moment (t : ExceptionalTime) (j k : ℕ) : ℂ := ∑ d : Fin (radix t j), (delta t j d:ℂ)^k

def coupling (t : ExceptionalTime) (j : ℕ) (s : ℂ) (k : ℕ) :=
  (k.factorial:ℂ)⁻¹ * falling s k * weight (base t j) (s+(k:ℂ)) * moment t j k

private theorem endpoint_pos (t : ExceptionalTime) (j : ℕ) (d : Fin (radix t j)) :
    0 < base t j+delta t j d := by
  have hc : 1 < (radix t j:ℝ) := by exact_mod_cast radix_gt_one t j
  rw [delta,centered_digit_value,base_sq]
  nlinarith only [hc,Nat.cast_nonneg (α := ℝ) d.val,sq_nonneg ((radix t j:ℝ)-1)]

theorem regular_analytic (t : ExceptionalTime) (j m : ℕ) (w : {s : ℂ // 1/2-((m:ℝ)+1) < s.re}) :
    AnalyticAt ℂ (regular t j m) w.val := by
  apply AnalyticAt.add
  · apply Finset.analyticAt_fun_sum
    intro d _
    exact (weight_entire (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (center_pos t j))).analyticAt _
  · exact Finset.analyticAt_fun_sum _ (fun d _ => trace_analytic t j m (base_pos t j) (endpoint_pos t j d) w)

private theorem child_parent (t : ExceptionalTime) (j : ℕ) (d : Fin (radix t j)) (x : Label t j) :
    parent (digitTreeEquiv t j (.inr (d,x))) = base t j*parent x+delta t j d := by
  change (((child t j d x).val:ℝ)+center t j) = _
  rw [child_value,Nat.cast_add,Nat.cast_mul]
  unfold parent delta displacement labelValue base
  ring

private theorem physical_hasSum (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1/2 < z.re}) (k : ℕ) :
    HasSum (fun x : Label t j => weight (parent x) (s.val+(k:ℂ))) (physical t j (s.val+(k:ℂ))) := by
  apply Summable.hasSum
  apply ((shifted_heat_summable_iff t j ⟨center t j,by linarith only [center_pos t j]⟩ _).mpr ?_).of_norm
  simpa only [Complex.add_re,Complex.natCast_re] using
    (s.property.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg k)))

/-- The finite Taylor expansion is an exact recurrence after the remainder is traced. -/
theorem finite_renewal (t : ExceptionalTime) (j m : ℕ) (s : {z : ℂ // 1/2 < z.re}) :
    physical t j s.val = regular t j m s.val +
      ∑ k ∈ Finset.range (m+1), coupling t j s.val k * physical t j (s.val+(k:ℂ)) := by
  classical
  let C := radix t j
  let B := base t j
  let W (x : Label t j) := weight (parent x) s.val
  let e := digitTreeEquiv t j
  have hW : Summable W := by simpa only [Nat.cast_zero,add_zero] using (physical_hasSum t j s 0).summable
  have hT := e.summable_iff.mpr hW
  have hp := hT.comp_injective (Sum.inr_injective (α := First C))
  have hsplit := e.tsum_eq W
  rw [Summable.tsum_sum (f := fun u : DigitTree t j => W (e u)) Summable.of_finite hp,
    tsum_fintype (fun d : First C => W (e (.inl d))),hp.tsum_prod,tsum_fintype] at hsplit
  have hcol (d : Fin C) :
      (∑' x : Label t j, W (e (.inr (d,x)))) = errorTrace t j m B (delta t j d) s.val+
        ∑ k ∈ Finset.range (m+1), term B (delta t j d) s.val k * physical t j (s.val+(k:ℂ)) := by
    have hE := error_summable t j m (base_pos t j) (endpoint_pos t j d)
      ⟨s.val,by linarith only [s.property,Nat.cast_nonneg (α := ℝ) m]⟩
    have hpoly := hasSum_sum (s := Finset.range (m+1))
      (fun k _ => (physical_hasSum t j s k).mul_left (term B (delta t j d) s.val k))
    have h := hE.hasSum.add hpoly
    apply HasSum.tsum_eq
    apply h.congr_fun
    intro x
    exact (child_expansion (base_pos t j) (endpoint_pos t j d) (parent_ge_one x) s.val m).symm.trans
      (congrArg (fun n => weight n s.val) (child_parent t j d x).symm)
  change seeds t j s.val+(∑ d : Fin C, ∑' x : Label t j, W (e (.inr (d,x)))) = physical t j s.val at hsplit
  rw [← hsplit]
  simp only [hcol,Finset.sum_add_distrib,regular,add_assoc]
  congr 1
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_mul]
  congr 1
  unfold term coupling moment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem odd_coupling (t : ExceptionalTime) (j m : ℕ) (s : ℂ) : coupling t j s (2*m+1) = 0 := by
  have h := congrArg Complex.ofReal (centered_odd_moment t j m)
  simp only [Complex.ofReal_sum,Complex.ofReal_pow,Complex.ofReal_zero] at h
  rw [coupling,show moment t j (2*m+1) = 0 from h,mul_zero]

/-- Variance coefficient multiplying the twice-shifted heat. -/
def varianceFactor (t : ExceptionalTime) (j : ℕ) (s : ℂ) :=
  s*(s+1)*(radix t j:ℂ)*((base t j:ℂ)-1)*weight (base t j) (s+2)/24

theorem variance_renewal (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1/2 < z.re}) :
    denominator t j s.val*physical t j s.val =
      regular t j 3 s.val+varianceFactor t j s.val*physical t j (s.val+2) := by
  have h := finite_renewal t j 3 s
  have h₂ := congrArg Complex.ofReal (centered_second_moment t j)
  push_cast at h₂
  have hm : moment t j 2 = (radix t j:ℂ)*((base t j:ℂ)-1)/12 := by
    rw [base_sq,Complex.ofReal_pow,Complex.ofReal_natCast]
    change (∑ d : Fin (radix t j), (delta t j d:ℂ)^2) = _
    linear_combination h₂/12
  have h₀ : coupling t j s.val 0 = weight (base t j) s.val*(radix t j:ℂ) := by
    simp [coupling,falling,moment]
  have hV : coupling t j s.val 2 = varianceFactor t j s.val := by
    rw [coupling,hm]
    norm_num [falling,Nat.factorial,varianceFactor]
    ring
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.cast_zero,add_zero,
    h₀,hV,show coupling t j s.val 1 = 0 from odd_coupling t j 0 _,show coupling t j s.val 3 = 0 from odd_coupling t j 1 _,
    zero_mul,Nat.cast_ofNat] at h
  rw [scale_weight]
  linear_combination h

#print axioms finite_renewal
#print axioms odd_coupling
#print axioms variance_renewal

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedVariance
