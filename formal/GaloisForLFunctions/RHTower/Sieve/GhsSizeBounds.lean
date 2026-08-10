import GaloisForLFunctions.RHTower.Sieve.GhsEventual

/-!
# The unconditional terms are `o(N log N)`

The mean value's right-hand side has five terms.  Four of them do not involve the multiplicative
distance at all, and the argument is worth nothing unless those four are smaller than the trivial
bound `N·log N`.  Two of the four are bounded here:

```text
ghsScaleCount N ≤ (log log N)/log 2 ,        ghsRecursionError N = o(N·log N) .
```

The first is `Nat.pow_log_le_self` read backwards; the second is `log log N = o(log N)`, i.e.
`log =o(id)` composed with `log`.  Both are the shape the remaining terms need, since every one of
them is `N` times a fixed power of `log log N` over a positive power of `log N`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Filter Asymptotics Finset Topology

theorem mertensTail_nonneg : 0 ≤ RHTower.Mertens.mertensTail := by
  rw [RHTower.Mertens.mertensTail]
  exact tsum_nonneg fun i => by positivity

/-- `log log N = o(log N)`. -/
theorem tendsto_log_log_div_log :
    Tendsto (fun N : ℕ => Real.log (Real.log N) / Real.log N) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  exact h.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem tendsto_log_natCast_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- **The number of scales is at most `(log log N)/log 2`.** -/
theorem ghsScaleCount_le {N : ℕ} (hN : 16 ≤ N) :
    ((ghsScaleCount N : ℕ) : ℝ) ≤ Real.log (Real.log N) / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNR : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog16 : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hratio : (1 : ℝ) ≤ Real.log N / (4 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    rw [h16] at hlog16
    linarith
  have hm : 1 ≤ ⌊Real.log N / (4 * Real.log 2)⌋₊ := Nat.le_floor (by exact_mod_cast hratio)
  have hmR : (1 : ℝ) ≤ ((⌊Real.log N / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hm
  have hpow : (2 : ℕ) ^ ghsScaleCount N ≤ ⌊Real.log N / (4 * Real.log 2)⌋₊ :=
    Nat.pow_log_le_self 2 (by omega)
  have hpowR : (2 : ℝ) ^ ghsScaleCount N ≤ ((⌊Real.log N / (4 * Real.log 2)⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hfloor : ((⌊Real.log N / (4 * Real.log 2)⌋₊ : ℕ) : ℝ)
      ≤ Real.log N / (4 * Real.log 2) := Nat.floor_le (by linarith)
  -- take logarithms
  have hstep : (ghsScaleCount N : ℝ) * Real.log 2 ≤ Real.log (Real.log N / (4 * Real.log 2)) := by
    have hlogpow : Real.log ((2 : ℝ) ^ ghsScaleCount N) = (ghsScaleCount N : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    rw [← hlogpow]
    exact Real.log_le_log (by positivity) (le_trans hpowR hfloor)
  have hlogN : (0 : ℝ) < Real.log N := by
    rw [h16] at hlog16
    linarith
  have hdiv : Real.log (Real.log N / (4 * Real.log 2))
      = Real.log (Real.log N) - Real.log (4 * Real.log 2) := by
    rw [Real.log_div (ne_of_gt hlogN) (by positivity)]
  have hden : (1 : ℝ) ≤ 4 * Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hden0 : (0 : ℝ) ≤ Real.log (4 * Real.log 2) := Real.log_nonneg hden
  rw [le_div_iff₀ hlog2]
  rw [hdiv] at hstep
  linarith

/-- **The recursion error is `o(N·log N)`.** -/
theorem tendsto_ghsRecursionError_div :
    Tendsto (fun N : ℕ => ghsRecursionError N / ((N : ℝ) * Real.log N)) atTop (𝓝 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hT := mertensTail_nonneg
  set A : ℝ := 9 + RHTower.Mertens.mertensTail with hAdef
  set c : ℝ := (Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
      / Real.log 2 with hcdef
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; linarith
  have hc0 : (0 : ℝ) ≤ c := by
    rw [hcdef]
    have h3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  -- the majorant
  set g : ℕ → ℝ := fun N =>
    (A + Real.log 4 + A * c * 2) / Real.log N + (A * c) * (Real.log (Real.log N) / Real.log N)
    with hgdef
  have hgt : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (A + Real.log 4 + A * c * 2) / Real.log N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_log_natCast_atTop
    have h2 : Tendsto (fun N : ℕ => (A * c) * (Real.log (Real.log N) / Real.log N))
        atTop (𝓝 0) := by
      have := tendsto_log_log_div_log.const_mul (A * c)
      simpa using this
    have := h1.add h2
    rw [add_zero] at this
    exact this
  refine squeeze_zero' ?_ ?_ hgt
  · -- nonnegativity
    filter_upwards [Filter.eventually_ge_atTop 3] with N hN3
    have hN3R : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
    have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
    have hlogL : (0 : ℝ) ≤ Real.log ((Nat.log 2 N : ℕ) : ℝ) := Real.log_natCast_nonneg _
    rw [ghsRecursionError]
    have hnum : (0 : ℝ) ≤ A * (N : ℝ) + (N : ℝ) * Real.log 4
        + A * ((N : ℝ) * (c * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have h1 : (0 : ℝ) ≤ (N : ℝ) * (c * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ))) := by
        have : (0 : ℝ) ≤ 1 + Real.log ((Nat.log 2 N : ℕ) : ℝ) := by linarith
        positivity
      positivity
    have hden : (0 : ℝ) ≤ (N : ℝ) * Real.log N := by positivity
    exact div_nonneg hnum hden
  · -- the bound
    filter_upwards [Filter.eventually_ge_atTop 16] with N hN16
    have hN16R : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
    -- `Nat.log 2 N ≤ (log N)/log 2`
    have hnat : ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.log N / Real.log 2 := by
      have hp : (2 : ℕ) ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
      have hpR : (2 : ℝ) ^ Nat.log 2 N ≤ (N : ℝ) := by exact_mod_cast hp
      have hlp : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.log N :=
        Real.log_le_log (by positivity) hpR
      rw [Real.log_pow] at hlp
      rw [le_div_iff₀ hlog2]
      exact hlp
    have hlogle : Real.log ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.log (Real.log N) + 1 := by
      rcases eq_or_lt_of_le (Nat.zero_le (Nat.log 2 N)) with h | h
      · rw [← h]
        simp only [Nat.cast_zero, Real.log_zero]
        have hll : (0 : ℝ) ≤ Real.log (Real.log N) := by
          refine Real.log_nonneg ?_
          have h16 : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) hN16R
          have : Real.log 16 = 4 * Real.log 2 := by
            rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
            push_cast; ring
          have hd := Real.log_two_gt_d9
          linarith
        linarith
      · have h1 : (1 : ℝ) ≤ ((Nat.log 2 N : ℕ) : ℝ) := by exact_mod_cast h
        have hstep : Real.log ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.log (Real.log N / Real.log 2) :=
          Real.log_le_log (by linarith) hnat
        rw [Real.log_div (ne_of_gt hlogN) (ne_of_gt hlog2)] at hstep
        have hll2 : (-1 : ℝ) ≤ Real.log (Real.log 2) := by
          rw [show (-1 : ℝ) = Real.log (Real.exp (-1)) by rw [Real.log_exp]]
          refine Real.log_le_log (Real.exp_pos _) ?_
          have he : Real.exp (-1) ≤ 0.37 := by
            have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
            have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
            have hneg : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
            have hprod : Real.exp (-1) * Real.exp 1 = 1 := by
              rw [← Real.exp_add]; norm_num
            nlinarith [hprod, h, hpos, hneg]
          have hd := Real.log_two_gt_d9
          linarith
        linarith
    -- assemble
    rw [ghsRecursionError, hgdef]
    rw [div_le_iff₀ (by positivity)]
    have hexpand : ((A + Real.log 4 + A * c * 2) / Real.log N
          + (A * c) * (Real.log (Real.log N) / Real.log N)) * ((N : ℝ) * Real.log N)
        = (N : ℝ) * (A + Real.log 4 + A * c * 2 + A * c * Real.log (Real.log N)) := by
      field_simp
    rw [hexpand]
    have hmul : A * ((N : ℝ) * (c * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ))))
        ≤ (N : ℝ) * (A * c * (2 + Real.log (Real.log N))) := by
      have hin : (1 : ℝ) + Real.log ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 + Real.log (Real.log N) := by
        linarith
      have hAc : (0 : ℝ) ≤ A * c := mul_nonneg hA0 hc0
      nlinarith [hin, hAc, hN0.le, mul_nonneg hN0.le hAc]
    nlinarith [hmul, hN0.le]

end RHTower.Sieve

end
