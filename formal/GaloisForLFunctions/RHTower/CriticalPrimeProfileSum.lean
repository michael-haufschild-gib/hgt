import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence

/-!
# The critical prime sum of the squared exponential defect

At the critical scaling `c_x = u / log x` the local Hellinger defect of a prime is
`(e^{u t_p} − 1)² / p` with `t_p = log p / log x`.  Summing it over the primes below the cutoff is
exactly the Mertens prime window of the profile `t ↦ (e^{ut} − 1)²/t`, which is continuous on the
unit interval because the numerator vanishes to second order at the origin.  Weak convergence of
that window therefore gives

`∑_{p ≤ x} (e^{u t_p} − 1)²/p → ∫₀¹ (e^{ut} − 1)²/t dt`,

which is twice the critical exponent of the squarefree normal cone.
-/

open Filter Topology Set

namespace RHTower

theorem abs_exp_sub_one_le_mul (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (by linarith [Real.one_le_exp hx] : (0:ℝ) ≤ Real.exp x - 1)]
    have h := Real.add_one_le_exp (-x)
    have hpos : (0 : ℝ) < Real.exp x := Real.exp_pos x
    have hmul : Real.exp x * (-x + 1) ≤ Real.exp x * Real.exp (-x) :=
      mul_le_mul_of_nonneg_left h hpos.le
    rw [← Real.exp_add] at hmul
    simp at hmul
    nlinarith [hmul]
  · have hxneg : x < 0 := hx
    have hle : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hxneg.le
    have hge : 1 + x ≤ Real.exp x := by
      have := Real.add_one_le_exp x
      linarith
    rw [abs_of_neg hxneg, abs_of_nonpos (by linarith : Real.exp x - 1 ≤ 0)]
    have hexp1 : (1 : ℝ) ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
    nlinarith [hge, hexp1]

/-- The critical profile `t ↦ (e^{ut} − 1)² / t`, extended by zero at the origin. -/
noncomputable def critProfile (u t : ℝ) : ℝ :=
  if t = 0 then 0 else (Real.exp (u * t) - 1) ^ (2 : ℕ) / t

theorem critProfile_def (u t : ℝ) :
    critProfile u t = if t = 0 then 0 else (Real.exp (u * t) - 1) ^ (2 : ℕ) / t := rfl

theorem critProfile_nonneg (u : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ critProfile u t := by
  rw [critProfile]
  split_ifs with h
  · exact le_rfl
  · positivity

theorem critProfile_le (u : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    critProfile u t ≤ u ^ (2 : ℕ) * Real.exp (2 * |u|) * t := by
  rw [critProfile]
  split_ifs with h
  · positivity
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h)
    have hbound : |Real.exp (u * t) - 1| ≤ |u| * t * Real.exp |u| := by
      refine le_trans (abs_exp_sub_one_le_mul (u * t)) ?_
      have habs : |u * t| = |u| * t := by rw [abs_mul, abs_of_nonneg ht0]
      rw [habs]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine Real.exp_le_exp.mpr ?_
      nlinarith [abs_nonneg u, ht1, ht0]
    have hsq : (Real.exp (u * t) - 1) ^ (2 : ℕ) ≤ (|u| * t * Real.exp |u|) ^ (2 : ℕ) := by
      have h1 : (Real.exp (u * t) - 1) ^ (2 : ℕ) = |Real.exp (u * t) - 1| ^ (2 : ℕ) := (sq_abs _).symm
      rw [h1]
      exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
    rw [div_le_iff₀ htpos]
    have hexp : (|u| * t * Real.exp |u|) ^ (2 : ℕ) = u ^ (2 : ℕ) * Real.exp (2 * |u|) * t ^ (2 : ℕ) := by
      rw [mul_pow, mul_pow, sq_abs, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    calc (Real.exp (u * t) - 1) ^ (2 : ℕ) ≤ (|u| * t * Real.exp |u|) ^ (2 : ℕ) := hsq
      _ = u ^ (2 : ℕ) * Real.exp (2 * |u|) * t ^ (2 : ℕ) := hexp
      _ = u ^ (2 : ℕ) * Real.exp (2 * |u|) * t * t := by ring


theorem continuousOn_critProfile (u : ℝ) : ContinuousOn (critProfile u) (Set.Icc 0 1) := by
  intro t ht
  rcases eq_or_ne t 0 with rfl | htne
  · have hval : critProfile u 0 = 0 := by rw [critProfile, if_pos rfl]
    rw [ContinuousWithinAt, hval]
    refine squeeze_zero' (g := fun x : ℝ => u ^ (2 : ℕ) * Real.exp (2 * |u|) * x) ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact critProfile_nonneg u hx.1
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact critProfile_le u hx.1 hx.2
    · have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Icc 0 1)) (nhds 0) :=
        (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
      have := hid.const_mul (u ^ (2 : ℕ) * Real.exp (2 * |u|))
      simpa using this
  · have hcont : ContinuousAt (fun x : ℝ => (Real.exp (u * x) - 1) ^ (2 : ℕ) / x) t := by
      refine ContinuousAt.div ?_ continuousAt_id htne
      exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
        continuous_const).pow 2).continuousAt
    have heq : critProfile u =ᶠ[nhds t] fun x : ℝ => (Real.exp (u * x) - 1) ^ (2 : ℕ) / x := by
      filter_upwards [isOpen_ne.mem_nhds htne] with x hx
      rw [critProfile, if_neg hx]
    exact ((hcont.congr heq.symm)).continuousWithinAt

theorem mertensPrimeWindow_critProfile_div (u : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    mertensPrimeWindow (critProfile u) N / Real.log N
      = ∑ n ∈ Finset.Icc 0 N,
          (if n.Prime then (Real.exp (u * (Real.log n / Real.log N)) - 1) ^ (2 : ℕ) / (n : ℝ) else 0) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  rw [mertensPrimeWindow, Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hp : n.Prime
  · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hne : Real.log (n : ℝ) / Real.log (N : ℝ) ≠ 0 := by positivity
    rw [if_pos hp, mertensPrimeWeight, if_pos hp, critProfile_def, if_neg hne]
    field_simp
  · rw [if_neg hp, mertensPrimeWeight, if_neg hp]
    simp

/-- **`(16)`: the critical prime sum converges to the profile integral.** -/
theorem tendsto_sum_critProfile (u : ℝ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N,
        (if n.Prime then (Real.exp (u * (Real.log n / Real.log N)) - 1) ^ (2 : ℕ) / (n : ℝ) else 0))
      atTop (nhds (∫ t in (0 : ℝ)..1, critProfile u t)) := by
  have hmain := tendsto_mertensPrimeWindow_div_log (continuousOn_critProfile u)
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact mertensPrimeWindow_critProfile_div u hN

end RHTower
