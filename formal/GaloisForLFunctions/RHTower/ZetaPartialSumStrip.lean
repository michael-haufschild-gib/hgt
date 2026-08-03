import GaloisForLFunctions.RHTower.FractionalPartZeta
import Mathlib.NumberTheory.AbelSummation

/-!
# Partial sums of the zeta series inside the critical strip

Abel summation applied to the constant coefficient sequence writes a partial sum of `k^(-w)` as an
integer-part integral.  Replacing the integer part by `t - fract t` isolates the elementary term
`N^(1-w)/(1-w)`, and the fractional-part integral converges as `N` grows, so the difference

`sum_{k<=N} k^(-w) - N^(1-w)/(1-w)`

tends to `zeta(w)` on the whole strip `0 < Re w < 1`.  This is the asymptotic that the region of
convergence of the Dirichlet series does not provide.
-/

open Complex Real MeasureTheory Set Filter Topology Finset

noncomputable section

namespace RHTower

/-- The coefficient sequence of the zeta series, normalized to vanish at zero. -/
def zetaSeriesCoeff : ℕ → ℂ := fun k => if k = 0 then 0 else 1

theorem zetaCoeff_zero : zetaSeriesCoeff 0 = 0 := by
  rw [zetaSeriesCoeff, if_pos rfl]

theorem sum_zetaCoeff (n : ℕ) : (∑ k ∈ Finset.Icc 0 n, zetaSeriesCoeff k) = (n : ℂ) := by
  induction n with
  | zero => simp [zetaSeriesCoeff]
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (Nat.zero_le _), ih, zetaSeriesCoeff,
        if_neg (Nat.succ_ne_zero m)]
      push_cast
      ring

theorem differentiableAt_ofReal_cpow_neg {w : ℂ} (hw : -w ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ (-w)) t :=
  differentiableAt_id.ofReal_cpow_const ht hw


theorem deriv_ofReal_cpow_neg {w : ℂ} (hw : -w ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    deriv (fun x : ℝ => (x : ℂ) ^ (-w)) t = -w * (t : ℂ) ^ (-w - 1) :=
  Complex.deriv_ofReal_cpow_const ht hw

theorem integrableOn_deriv_cpow_Icc {w : ℂ} (hw : -w ≠ 0) (N : ℕ) :
    IntegrableOn (deriv fun x : ℝ => (x : ℂ) ^ (-w)) (Icc (1 : ℝ) (N : ℝ)) := by
  have hcont : ContinuousOn (fun t : ℝ => -w * (t : ℂ) ^ (-w - 1)) (Icc (1 : ℝ) (N : ℝ)) := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    exact ContinuousAt.continuousWithinAt
      (continuousAt_const.mul
        (Complex.continuousAt_ofReal_cpow_const t (-w - 1) (Or.inr htne)))
  refine (hcont.integrableOn_compact isCompact_Icc).congr_fun ?_ measurableSet_Icc
  intro t ht
  exact (deriv_ofReal_cpow_neg hw (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).symm

/-- **Abel summation for the zeta partial sums.** -/
theorem sum_cpow_eq_abel {w : ℂ} (hw : w ≠ 0) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-w)) =
      ((N : ℝ) : ℂ) ^ (-w) * (N : ℂ) +
        w * ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-w - 1) := by
  have hwn : -w ≠ 0 := neg_ne_zero.mpr hw
  have hmain := sum_mul_eq_sub_integral_mul₀ (𝕜 := ℂ) zetaSeriesCoeff zetaCoeff_zero (N : ℝ)
    (fun t ht => differentiableAt_ofReal_cpow_neg hwn
      (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
    (integrableOn_deriv_cpow_Icc hwn N)
  rw [Nat.floor_natCast] at hmain
  have hleft : (∑ k ∈ Finset.Icc 0 N, ((k : ℝ) : ℂ) ^ (-w) * zetaSeriesCoeff k) =
      ∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-w) := by
    rw [show Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega]
    rw [Finset.sum_insert (by simp), zetaCoeff_zero, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [zetaSeriesCoeff, if_neg (by omega), mul_one]
  have hint : (∫ t in Set.Ioc (1 : ℝ) (N : ℝ),
      deriv (fun x : ℝ => (x : ℂ) ^ (-w)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, zetaSeriesCoeff k) =
      -w * ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-w - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have htne : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht.1)
    rw [deriv_ofReal_cpow_neg hwn htne, sum_zetaCoeff]
    ring
  rw [hleft, hint, sum_zetaCoeff] at hmain
  rw [hmain]
  ring

/-! ## The partial-sum asymptotic -/

theorem neg_sub_one_eq {w : ℂ} : (-w - 1 : ℂ) = -(w + 1) := by ring

theorem integrableOn_Ioc_fract_cpow {w : ℂ} (hw0 : 0 < w.re) (N : ℕ) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-w - 1))
      (Set.Ioc (1 : ℝ) (N : ℝ)) := by
  have h := integrableOn_Ioi_one_fract_cpow hw0
  refine (h.mono_set ?_).congr_fun ?_ measurableSet_Ioc
  · intro t ht
    exact ht.1
  · intro t _
    rw [neg_sub_one_eq]

theorem integrableOn_Ioc_cpow (w : ℂ) (N : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-w)) (Set.Ioc (1 : ℝ) (N : ℝ)) := by
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-w)) (Set.Icc (1 : ℝ) (N : ℝ)) := by
    intro t ht
    exact ContinuousAt.continuousWithinAt
      (Complex.continuousAt_ofReal_cpow_const t (-w)
        (Or.inr (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))))
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

/-- **The Abel identity in fractional-part form.** -/
theorem sum_cpow_sub_pow_eq {w : ℂ} (hw0 : 0 < w.re) (hwne1 : w ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-w)) - ((N : ℝ) : ℂ) ^ (1 - w) / (1 - w) =
      -w / (1 - w) -
        w * ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-w - 1) := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw0
    exact lt_irrefl 0 hw0
  have hw1ne : (1 : ℂ) - w ≠ 0 := by
    intro h
    exact hwne1 (by linear_combination -h)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hNne : ((N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hNpos)
  have hNle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- split the integer part
  have hsplit : (∫ t in Set.Ioc (1 : ℝ) (N : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-w - 1)) =
      (∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (t : ℂ) ^ (-w)) -
        ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-w - 1) := by
    rw [← integral_sub (integrableOn_Ioc_cpow w N) (integrableOn_Ioc_fract_cpow hw0 N)]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have htpos : (0 : ℝ) < t := lt_trans zero_lt_one ht.1
    have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htpos)
    have hfloor : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      have hz : ((⌊t⌋₊ : ℕ) : ℤ) = ⌊t⌋ := Int.natCast_floor_eq_floor htpos.le
      have h3 : ((⌊t⌋₊ : ℕ) : ℝ) = ((⌊t⌋ : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) hz
      have h2 : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
        rw [h3, Int.self_sub_fract]
      rw [show ((⌊t⌋₊ : ℕ) : ℂ) = (((⌊t⌋₊ : ℕ) : ℝ) : ℂ) by push_cast; ring, h2]
      push_cast
      ring
    have hpow : (t : ℂ) * (t : ℂ) ^ (-w - 1) = (t : ℂ) ^ (-w) := by
      nth_rewrite 1 [← Complex.cpow_one ((t : ℝ) : ℂ)]
      rw [← Complex.cpow_add _ _ htne]
      congr 1
      ring
    rw [hfloor, ← hpow]
    ring
  -- evaluate the elementary integral
  have helem : (∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (t : ℂ) ^ (-w)) =
      (((N : ℝ) : ℂ) ^ (1 - w) - 1) / (1 - w) := by
    rw [← intervalIntegral.integral_of_le hNle,
      integral_cpow (Or.inr ⟨by
        intro hcon
        exact hwne1 (by linear_combination -hcon), by
        intro hcon
        rcases Set.mem_uIcc.mp hcon with h | h
        · linarith [h.1]
        · linarith [h.2]⟩)]
    rw [Complex.ofReal_one, Complex.one_cpow, show (-w + 1 : ℂ) = 1 - w by ring]
  have hNpow : ((N : ℝ) : ℂ) ^ (-w) * (N : ℂ) = ((N : ℝ) : ℂ) ^ (1 - w) := by
    rw [show ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) by push_cast; ring,
      show (1 - w : ℂ) = -w + 1 by ring, Complex.cpow_add _ _ hNne, Complex.cpow_one]
  rw [sum_cpow_eq_abel hwne N, hsplit, helem, hNpow]
  field_simp
  ring


/-- **The partial-sum asymptotic for zeta inside the critical strip.**  The Dirichlet series does
not converge there; Abel summation and the fractional-part integral supply the limit instead. -/
theorem tendsto_sum_cpow_sub_pow {w : ℂ} (hw0 : 0 < w.re) (hwne1 : w ≠ 1) :
    Filter.Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-w)) -
        ((N : ℝ) : ℂ) ^ (1 - w) / (1 - w))
      Filter.atTop (nhds (riemannZeta w)) := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw0
    exact lt_irrefl 0 hw0
  have hw1ne : (1 : ℂ) - w ≠ 0 := by
    intro h
    exact hwne1 (by linear_combination -h)
  have hwm1 : w - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hwne1
  -- the truncated fractional-part integrals converge
  have hJ : Filter.Tendsto
      (fun N : ℕ => ∫ t in Set.Ioc (1 : ℝ) (N : ℝ),
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-w - 1))
      Filter.atTop (nhds (1 / (w - 1) - riemannZeta w / w)) := by
    have hbase := intervalIntegral_tendsto_integral_Ioi (a := (1 : ℝ))
      (f := fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)))
      (integrableOn_Ioi_one_fract_cpow hw0) (b := fun N : ℕ => (N : ℝ))
      tendsto_natCast_atTop_atTop
    rw [integral_Ioi_one_fract_cpow_of_re_pos hw0 hwne1] at hbase
    refine hbase.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [intervalIntegral.integral_of_le hNle]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    rw [neg_sub_one_eq]
  have hlim := ((tendsto_const_nhds (x := -w / (1 - w)) (f := Filter.atTop (α := ℕ))).sub
    (hJ.const_mul w))
  have hvalue : -w / (1 - w) - w * (1 / (w - 1) - riemannZeta w / w) = riemannZeta w := by
    field_simp
    ring
  rw [hvalue] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  exact (sum_cpow_sub_pow_eq hw0 hwne1 hN).symm

end RHTower
