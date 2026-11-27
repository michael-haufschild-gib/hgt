import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Paired
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.EdgeLimit

/-! # A finite-spectrum crossing from the uniform mean and unequal edge gaps -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks

open Finset Real Filter Topology Set

variable {X : Type*} [Fintype X]

private def difference (E : X → ℝ) (l u : X) (t : ℝ) := relativeZ E (-t) u - relativeZ E t l

/-- The derivative at zero reads the displacement of the uniform mean from the endpoint midpoint. -/
private theorem difference_derivative (E : X → ℝ) (l u : X) :
    HasDerivAt (difference E l u) (∑ x, ((E x-E u)+(E x-E l))) 0 := by
  have hot : HasDerivAt (fun t => relativeZ E (-t) u) (∑ x, (E x-E u)) 0 := by
    unfold relativeZ
    simp only [neg_neg]
    apply HasDerivAt.fun_sum
    intro x _
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const (E x-E u)).exp)
  have cold : HasDerivAt (fun t => relativeZ E t l) (∑ x, -(E x-E l)) 0 := by
    unfold relativeZ
    apply HasDerivAt.fun_sum
    intro x _
    simpa using ((((hasDerivAt_id (0:ℝ)).neg).mul_const (E x-E l)).exp)
  change HasDerivAt (fun t => relativeZ E (-t) u - relativeZ E t l) _ 0
  apply (hot.fun_sub cold).congr_deriv
  rw [← sum_sub_distrib]
  simp only [sub_neg_eq_add]

private theorem small_positive (E : X → ℝ) (l u : X)
    (h : 0 < ∑ x, ((E x-E u)+(E x-E l))) : ∃ t : ℝ, 0 < t ∧ 0 < difference E l u t := by
  have hz : difference E l u 0 = 0 := by simp [difference,relativeZ]
  have hs := (difference_derivative E l u).tendsto_slope_zero_right.eventually_const_lt h
  simp only [zero_add, hz, sub_zero, smul_eq_mul] at hs
  have hr : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hs'⟩ := (hr.and hs).exists
  exact ⟨t,ht,(mul_pos_iff_of_pos_left (inv_pos.mpr ht)).mp hs'⟩

/-- At large positive damping the smaller edge gap gives the smaller peak. -/
theorem eventually_peak_lt {F G : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : Tendsto (fun t => exp (t*a)*(1-F t)) atTop (𝓝 1))
    (hg : Tendsto (fun t => exp (t*b)*(1-G t)) atTop (𝓝 1)) :
    ∀ᶠ t in atTop, F t < G t := by
  have dec : Tendsto (fun t : ℝ => exp (-t*(b-a))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul,mul_comm (b-a)] using
      tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (sub_pos.mpr hab))
  have he (t : ℝ) : exp (-t*(b-a))*(exp (t*b)*(1-G t)) = exp (t*a)*(1-G t) := by
    rw [← mul_assoc, ← exp_add, show -t*(b-a)+t*b=t*a by ring]
  have z := dec.mul hg
  simp only [he,zero_mul] at z
  have s := hf.sub z
  rw [sub_zero] at s
  filter_upwards [s.eventually_const_lt zero_lt_one] with t ht
  change 0 < exp (t*a)*(1-F t)-exp (t*a)*(1-G t) at ht
  rw [← mul_sub] at ht
  have hp := (mul_pos_iff_of_pos_left (exp_pos _)).mp ht
  linarith only [hp]

/-- Reversed signs near zero and at infinity force a nonzero match of the peak probabilities. -/
theorem peak_crossing (E : X → ℝ) (l u : X) (hl : ∀ x, E l ≤ E x) (hu : ∀ x, E x ≤ E u)
    (hmean : 0 < ∑ x, ((E x-E u)+(E x-E l)))
    (hlarge : ∀ᶠ t : ℝ in atTop, largest E t < largest E (-t)) :
    ∃ t : ℝ, 0 < t ∧ largest E t = largest E (-t) := by
  obtain ⟨a,ha,hpa⟩ := small_positive E l u hmean
  obtain ⟨b,hab,hpb⟩ := ((eventually_ge_atTop a).and hlarge).exists
  have peaks (t : ℝ) (ht : 0 ≤ t) : largest E t = (relativeZ E t l)⁻¹ ∧
      largest E (-t) = (relativeZ E (-t) u)⁻¹ :=
    ⟨largest_at l (fun x => mul_le_mul_of_nonneg_left (hl x) ht),
     largest_at u (fun x => mul_le_mul_of_nonpos_left (hu x) (neg_nonpos.mpr ht))⟩
  rw [(peaks b (ha.le.trans hab)).1, (peaks b (ha.le.trans hab)).2] at hpb
  have hneg := (inv_lt_inv₀ (relativeZ_pos E b l) (relativeZ_pos E (-b) u)).mp hpb
  have hc : Continuous (difference E l u) := by unfold difference relativeZ; fun_prop
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc' hab hc.continuousOn
    (show (0:ℝ) ∈ Icc (difference E l u b) (difference E l u a) from ⟨sub_nonpos.mpr hneg.le,hpa.le⟩)
  have hp := ha.trans_le ht.1
  exact ⟨t,hp,(peaks t hp.le).1.trans ((congrArg Inv.inv (sub_eq_zero.mp he).symm).trans (peaks t hp.le).2.symm)⟩

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem total_count_eq (m : ℕ) (i j : I) :
    (∑ x : Boson I m, (count x i : ℝ)) = ∑ x : Boson I m, (count x j : ℝ) := by
  let R := Equiv.swap i j
  calc _ = ∑ x : Boson I m, (count (move m R x) j : ℝ) := by
             apply sum_congr rfl
             intro x _
             change (count x i : ℝ) = count x ((Equiv.swap i j).symm j)
             rw [Equiv.symm_swap,Equiv.swap_apply_right]
       _ = _ := Equiv.sum_comp (move m R) (fun x => (count x j : ℝ))

/-- Uniform fixed-count occupation gives every species the same total weight. -/
theorem total_read (m : ℕ) (p : I) (f : I → ℝ) :
    (∑ x : Boson I m, read f x) = (∑ x : Boson I m, (count x p : ℝ)) * ∑ i, f i := by
  rw [mul_sum]
  unfold read
  rw [sum_comm]
  exact sum_congr rfl fun i _ => by rw [← sum_mul, total_count_eq m i p]

theorem boson_mean_positive {m : ℕ} (hm : 0 < m) (e : I → ℝ) (l u : I)
    (h : 0 < ∑ i, ((e i-e u)+(e i-e l))) :
    0 < ∑ x : Boson I m, ((read e x-read e (pure m u))+(read e x-read e (pure m l))) := by
  have each (x : Boson I m) : (read e x-read e (pure m u))+(read e x-read e (pure m l)) =
      read (fun i => (e i-e u)+(e i-e l)) x := by
    rw [read_add,read_pure,read_pure,← read_const x,← read_const x]
    simp only [read,mul_sub,sum_sub_distrib]
  simp only [each, total_read m l]
  apply mul_pos _ h
  apply sum_pos' (fun x _ => Nat.cast_nonneg (count x l))
  exact ⟨pure m l,mem_univ _,by rw [count_pure,if_pos rfl]; exact Nat.cast_pos.mpr hm⟩

#print axioms peak_crossing
#print axioms total_read
#print axioms boson_mean_positive

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks
