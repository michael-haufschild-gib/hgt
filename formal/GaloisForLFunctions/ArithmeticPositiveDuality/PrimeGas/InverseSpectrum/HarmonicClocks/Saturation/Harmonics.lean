import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.Blocks

/-! # All harmonic limits at the sharp retention ceiling -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- Distance from a point in a disk to its rightmost point is controlled by its real deficit. -/
theorem harmonic_disk_defect {z : ℂ} {a : ℝ} (h : ‖z‖ ≤ a) :
    ‖z-(a:ℂ)‖^2 ≤ 2*a*(a-z.re) := by
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hs ⊢
  linarith only [hs]

private def harmonicCap (a : ℝ) (k : ℕ) : ℝ := if k = 0 then 1 else a

private theorem sum_harmonicCap (r : ℕ+) (a : ℝ) :
    ∑ k ∈ Finset.range r.val, harmonicCap a k = 1+((r.val:ℝ)-1)*a := by
  have h (k : ℕ) : harmonicCap a k = a+(if k = 0 then 1-a else 0) := by
    by_cases hk : k = 0 <;> simp [harmonicCap,hk]
  simp only [h,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    Finset.sum_ite_eq',if_pos (Finset.mem_range.mpr r.pos)]
  ring

private theorem tested_limit {r : ℕ+} {t d : ℕ → ℝ} {δ : ℝ} {v : ℕ → MissingWave}
    (hd : Tendsto d atTop (𝓝 δ)) (hc : ∀ j, harmonicTest r (d j) (v j) (t j))
    (hb : Tendsto (fun j => blockReading (v j) (t j) 0 r.val) atTop (𝓝 (((r.val:ℂ)*(retentionCeiling r δ:ℝ)))))
    {k : ℕ} (hk : 0 < k) (hl : k < r.val) :
    Tendsto (fun j => harmonicReading (v j) (t j) k) atTop (𝓝 (δ:ℂ)) := by
  let b (j h : ℕ) := harmonicReading (v j) (t j) h
  have hn (j h : ℕ) (hh : h < r.val) : 0 ≤ harmonicCap (d j) h-(b j h).re := by
    by_cases hz : h = 0
    · simp [hz,harmonicCap,b,harmonicReading_zero]
    · rw [harmonicCap,if_neg hz]
      exact sub_nonneg.mpr ((Complex.re_le_norm _).trans (hc j h (Nat.pos_of_ne_zero hz) hh))
  have hdif (j : ℕ) : d j-(b j k).re ≤ 1+((r.val:ℝ)-1)*d j-(blockReading (v j) (t j) 0 r.val).re := by
    have h := Finset.single_le_sum (f := fun h => harmonicCap (d j) h-(b j h).re)
      (fun h hh => hn j h (Finset.mem_range.mp hh)) (Finset.mem_range.mpr hl)
    rw [Finset.sum_sub_distrib,sum_harmonicCap] at h
    simpa only [harmonicCap,if_neg hk.ne',b,
      blockReading,Complex.re_sum,Nat.zero_add] using h
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hb
  change Tendsto (fun j => (blockReading (v j) (t j) 0 r.val).re) atTop
    (𝓝 (((r.val:ℂ)*(retentionCeiling r δ:ℝ))).re) at hr
  rw [← Complex.ofReal_natCast,← Complex.ofReal_mul,Complex.ofReal_re,order_mul_retention] at hr
  have hsum := ((hd.const_mul ((r.val:ℝ)-1)).const_add 1).sub hr
  rw [sub_self] at hsum
  have hz : Tendsto (fun j => d j-(b j k).re) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun j => sub_nonneg.mpr ((Complex.re_le_norm _).trans (hc j k hk hl)))
      (Eventually.of_forall hdif)
  have he := (hd.const_mul 2).mul hz
  rw [mul_zero] at he
  have he' : Tendsto (fun j => b j k-(d j:ℂ)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [he.eventually_lt_const (sq_pos_of_pos hε)] with j hj
    rw [dist_zero_right]
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp ((harmonic_disk_defect (hc j k hk hl)).trans_lt hj)
  simpa only [sub_add_cancel,zero_add] using he'.add hd.ofReal

/-- Even when the error levels drift, saturation fixes every measured and unmeasured harmonic. -/
theorem saturated_harmonic_limit {r : ℕ+} {t d : ℕ → ℝ} {δ : ℝ} {v : ℕ → MissingWave} {m : ℕ+ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (hd : Tendsto d atTop (𝓝 δ))
    (hc : ∀ j, harmonicTest r (d j) (v j) (t j))
    (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n)))
    (hs : HasSum m (retentionCeiling r δ)) (k : ℕ) :
    Tendsto (fun j => harmonicReading (v j) (t j) k) atTop (𝓝 (if r.val ∣ k then (1:ℂ) else (δ:ℂ))) := by
  have hb := saturated_block_limit ht hd hc hm hs
  have step (l : ℕ) : Tendsto (fun j => harmonicReading (v j) (t j) (l+r.val)-harmonicReading (v j) (t j) l)
      atTop (𝓝 0) := by
    simpa only [adjacent_block_difference,sub_self] using (hb (l+1)).sub (hb l)
  have base (l : ℕ) (hl : l < r.val) : Tendsto (fun j => harmonicReading (v j) (t j) l)
      atTop (𝓝 (if l = 0 then (1:ℂ) else (δ:ℂ))) := by
    by_cases h : l = 0
    · simp [h,harmonicReading_zero]
    · rw [if_neg h]
      exact tested_limit hd hc (hb 0) (Nat.pos_of_ne_zero h) hl
  have lift (l : ℕ) (hl : l < r.val) (q : ℕ) : Tendsto (fun j => harmonicReading (v j) (t j) (l+r.val*q))
      atTop (𝓝 (if l = 0 then (1:ℂ) else (δ:ℂ))) := by
    induction q with
    | zero => simpa only [Nat.mul_zero,Nat.add_zero] using base l hl
    | succ q ih =>
      simpa only [Nat.mul_succ,Nat.add_assoc,sub_add_cancel,zero_add] using (step (l+r.val*q)).add ih
  simpa only [Nat.mod_add_div,← Nat.dvd_iff_mod_eq_zero] using lift (k%r.val) (Nat.mod_lt k r.pos) (k/r.val)

#print axioms harmonic_disk_defect
#print axioms saturated_harmonic_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
