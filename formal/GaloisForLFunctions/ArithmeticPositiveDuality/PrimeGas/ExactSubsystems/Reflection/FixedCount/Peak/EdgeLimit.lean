import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Thermal

/-! # Exact low-temperature leakage at a simple first excitation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak

open Finset Real Filter Topology

private theorem exp_decay {d : ℝ} (hd : 0 < d) :
    Tendsto (fun t : ℝ => exp (-t*d)) atTop (𝓝 0) := by
  have h := tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hd)
  simpa only [Function.comp_def, id_eq, neg_mul, mul_comm d] using h

/-- One excited state at gap d gives coefficient one in the loss of the largest Gibbs probability.
Every other excited state is separated by a strictly greater gap. -/
theorem leakage_limit {X : Type*} [Fintype X] (E : X → ℝ) (u v : X) {d : ℝ}
    (hd : 0 < d) (hv : E v-E u = d) (hh : ∀ x, x ≠ u → x ≠ v → d < E x-E u) :
    Tendsto (fun t => exp (t*d)*(1-largest E t)) atTop (𝓝 1) := by
  classical
  have hne : v ≠ u := by rintro rfl; rw [sub_self] at hv; exact hd.ne hv
  let U := univ.erase u
  have hmem : v ∈ U := mem_erase.mpr ⟨hne, mem_univ v⟩
  have he (t : ℝ) : exp (t*d)*(relativeZ E t u-1) = ∑ x ∈ U, exp (-t*(E x-E u-d)) := by
    rw [relativeZ, ← sum_erase_add univ (fun x => exp (-t*(E x-E u))) (mem_univ u)]
    simp only [sub_self, mul_zero, exp_zero, add_sub_cancel_right, mul_sum]
    apply sum_congr rfl
    intro x _
    rw [← exp_add]
    congr 1; ring
  have hterm (x : X) (hx : x ∈ U) : Tendsto (fun t : ℝ => exp (-t*(E x-E u-d))) atTop
      (𝓝 (if v=x then 1 else 0)) := by
    by_cases heq : v = x
    · subst x
      simp [hv]
    · rw [if_neg heq]
      exact exp_decay (sub_pos.mpr (hh x (ne_of_mem_erase hx) (Ne.symm heq)))
  have raw := tendsto_finsetSum U hterm
  rw [sum_ite_eq, if_pos hmem] at raw
  have scaled : Tendsto (fun t => exp (t*d)*(relativeZ E t u-1)) atTop (𝓝 1) :=
    raw.congr' (Eventually.of_forall fun t => (he t).symm)
  have cancel (t : ℝ) : exp (-t*d)*(exp (t*d)*(relativeZ E t u-1)) = relativeZ E t u-1 := by
    rw [← mul_assoc, ← exp_add, show -t*d+t*d=0 by ring, exp_zero, one_mul]
  have small := (exp_decay hd).mul scaled
  simp only [cancel, zero_mul] at small
  have z : Tendsto (fun t => relativeZ E t u) atTop (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using
      small.add (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1))
  have lower (x : X) : E u ≤ E x := by
    by_cases h : x = u
    · subst x; exact le_rfl
    by_cases h' : x = v
    · subst x; linarith only [hd, hv]
    linarith only [hd, hh x h h']
  have result := scaled.div z one_ne_zero
  rw [div_one] at result
  apply result.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change exp (t*d)*(relativeZ E t u-1)/relativeZ E t u = exp (t*d)*(1-largest E t)
  rw [largest_at u (fun x => mul_le_mul_of_nonneg_left (lower x) ht)]
  field_simp [(relativeZ_pos E t u).ne']

private theorem slower {F G : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : Tendsto (fun t => exp (t*a)*(1-F t)) atTop (𝓝 1))
    (hg : Tendsto (fun t => exp (t*b)*(1-G t)) atTop (𝓝 1)) :
    Tendsto (fun t => exp (t*a)*|F t-G t|) atTop (𝓝 1) := by
  have iden (t : ℝ) : exp (-t*(b-a))*(exp (t*b)*(1-G t)) = exp (t*a)*(1-G t) := by
    rw [← mul_assoc, ← exp_add, show -t*(b-a)+t*b=t*a by ring]
  have fast := (exp_decay (sub_pos.mpr hab)).mul hg
  simp only [iden, zero_mul] at fast
  have diff := (hf.sub fast).abs
  have eqv (t : ℝ) : |exp (t*a)*(1-F t)-exp (t*a)*(1-G t)| = exp (t*a)*|F t-G t| := by
    rw [← mul_sub, abs_mul, abs_of_pos (exp_pos _), show (1-F t)-(1-G t)=G t-F t by ring, abs_sub_comm]
  simpa only [eqv, sub_zero, abs_one] using diff

/-- Of two distinct simple edge gaps the smaller fixes the exact exponential scale of the
observable difference. -/
theorem peak_gap_limit {F G : ℝ → ℝ} {a b : ℝ} (hne : a ≠ b)
    (hf : Tendsto (fun t => exp (t*a)*(1-F t)) atTop (𝓝 1))
    (hg : Tendsto (fun t => exp (t*b)*(1-G t)) atTop (𝓝 1)) :
    Tendsto (fun t => exp (t*min a b)*|F t-G t|) atTop (𝓝 1) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le]
    exact slower h hf hg
  · rw [min_eq_right h.le]
    have flip (t : ℝ) : |G t-F t| = |F t-G t| := abs_sub_comm _ _
    simpa only [flip] using slower h hg hf

#print axioms leakage_limit
#print axioms peak_gap_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak
