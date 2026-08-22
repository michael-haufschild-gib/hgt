import GaloisForLFunctions.RHTower.DQPTEulerMaclaurin

/-!
# DQPT: the Euler–Maclaurin approximation of `S(a, b, β)`

**Proposition 4.5** of arXiv:2511.11199 (published Proposition 5.5): for `β > 0`, `β ≠ 1` and
integers `a ≤ b`,

`S(a,b,β) = ∑_{n=a}^{b} n^{−β}` is approximated by

`Ŝ(a,b,β) = (b^{1−β} − a^{1−β})/(1−β) + (a^{−β} + b^{−β})/2
              − ∑_{r=1}^{l₃} B_{2r}Γ(β+2r−1)/((2r)!Γ(β))·(b^{−β−2r+1} − a^{−β−2r+1})`

with remainder `|R_{l₃}| < 4/(2π)^{2l₃}·β(β+1)⋯(β+2l₃−2)/a^{β+2l₃−1}`.

Here the Gamma ratio `Γ(β+n)/Γ(β)` is written as the Pochhammer product `∏_{i<n}(β+i)`, which
the paper's own derivation (4.31) uses; `dqpt_pochhammer_eq_gamma_ratio` records the identity.

Main results:
* `dqptPowTower_isTower` — `x ↦ x^{−β}` has an explicit derivative tower on `(0, ∞)`;
* `dqpt_S_eq_emApprox_sub_rem` — **(4.28)/(4.31)**: the Euler–Maclaurin expansion of `S(a,b,β)`;
* `dqpt_em_remainder_bound` — **(4.34)**: the remainder bound.
-/

namespace RHTower.DQPT

open Filter Topology Set MeasureTheory

noncomputable section

/-! ## The derivative tower of `x ↦ x^{−β}` -/

/-- The derivative tower of `x ↦ x^{−β}`:
`F_j(x) = (−1)^j (∏_{i<j}(β+i)) x^{−β−j}`. -/
def dqptPowTower (β : ℝ) : ℕ → ℝ → ℝ := fun j x =>
  (-1 : ℝ) ^ j * (∏ i ∈ Finset.range j, (β + i)) * x ^ (-β - (j : ℝ))

@[simp] theorem dqptPowTower_zero (β x : ℝ) : dqptPowTower β 0 x = x ^ (-β) := by
  rw [dqptPowTower]
  norm_num

theorem dqptPowTower_isTower (β : ℝ) : DqptDerivTower (dqptPowTower β) (Set.Ioi 0) := by
  intro j x hx
  have hx0 : (0 : ℝ) < x := hx
  have hbase : HasDerivAt (fun y : ℝ => y ^ (-β - (j : ℝ)))
      ((-β - (j : ℝ)) * x ^ (-β - (j : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx0))
  have hmul := hbase.const_mul ((-1 : ℝ) ^ j * (∏ i ∈ Finset.range j, (β + i)))
  refine hmul.congr_deriv ?_
  rw [dqptPowTower, Finset.prod_range_succ]
  have hexp : (-β - ((j : ℝ) + 1)) = -β - (j : ℝ) - 1 := by ring
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [hcast, hexp, pow_succ]
  ring

theorem dqptPowTower_abs {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : 0 < x) (j : ℕ) :
    |dqptPowTower β j x| = (∏ i ∈ Finset.range j, (β + i)) * x ^ (-β - (j : ℝ)) := by
  have hprod : (0 : ℝ) < ∏ i ∈ Finset.range j, (β + i) := by
    refine Finset.prod_pos (fun i _ => ?_)
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  have hpow : (0 : ℝ) < x ^ (-β - (j : ℝ)) := Real.rpow_pos_of_pos hx _
  rw [dqptPowTower, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hprod, abs_of_pos hpow]

/-- The Pochhammer product is the Gamma ratio (the paper's `Γ(β+n)/Γ(β)`). -/
theorem dqpt_pochhammer_eq_gamma_ratio {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    ∏ i ∈ Finset.range n, (β + i) = Real.Gamma (β + n) / Real.Gamma β := by
  have hΓ : (0 : ℝ) < Real.Gamma β := Real.Gamma_pos_of_pos hβ
  induction n with
  | zero => simp [ne_of_gt hΓ]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hpos : (0 : ℝ) < β + (n : ℝ) := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hrec : Real.Gamma (β + (n : ℝ) + 1) = (β + (n : ℝ)) * Real.Gamma (β + (n : ℝ)) :=
        Real.Gamma_add_one (ne_of_gt hpos)
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast, show β + ((n : ℝ) + 1) = β + (n : ℝ) + 1 by ring, hrec]
      field_simp

/-! ## The Euler–Maclaurin approximation -/

/-- The paper's `Ŝ(a, b, β)` at order `l₃ = m+1`. -/
def dqptEMApprox (β : ℝ) (a b : ℝ) (m : ℕ) : ℝ :=
  (b ^ (1 - β) - a ^ (1 - β)) / (1 - β) + (a ^ (-β) + b ^ (-β)) / 2
    - ∑ r ∈ Finset.range (m + 1),
        ((bernoulli (2 * r + 2) : ℚ) : ℝ) / (((2 * r + 2).factorial : ℕ) : ℝ)
          * (∏ i ∈ Finset.range (2 * r + 1), (β + i))
          * (b ^ (-β - ((2 * r + 1 : ℕ) : ℝ)) - a ^ (-β - ((2 * r + 1 : ℕ) : ℝ)))

/-- **Proposition 4.5, the expansion (4.28)/(4.31).** -/
theorem dqpt_S_eq_emApprox_sub_rem {β : ℝ} (hβ1 : β ≠ 1) {A : ℕ} (hA : 1 ≤ A) (N m : ℕ) :
    ∑ n ∈ Finset.range (N + 1), ((A : ℝ) + n) ^ (-β)
      = dqptEMApprox β (A : ℝ) ((A : ℝ) + N) m
        - ∑ n ∈ Finset.range N, dqptEMJ (dqptPowTower β) (2 * m + 2) ((A : ℝ) + n) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAN : (0 : ℝ) < (A : ℝ) + (N : ℝ) := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hsub : Set.Icc ((A : ℝ)) ((A : ℝ) + (N : ℝ)) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le hA0 hx.1
  have htower : DqptDerivTower (dqptPowTower β) (Set.Icc ((A : ℝ)) ((A : ℝ) + (N : ℝ))) :=
    (dqptPowTower_isTower β).mono hsub
  have hem := dqpt_euler_maclaurin (F := dqptPowTower β) (a := (A : ℝ)) m N htower
  have hzero : ∀ y : ℝ, dqptPowTower β 0 y = y ^ (-β) := dqptPowTower_zero β
  simp only [hzero] at hem
  have hint : (∫ x in (A : ℝ)..((A : ℝ) + (N : ℝ)), x ^ (-β))
      = (((A : ℝ) + (N : ℝ)) ^ (1 - β) - (A : ℝ) ^ (1 - β)) / (1 - β) := by
    have hzeroNot : (0 : ℝ) ∉ Set.uIcc ((A : ℝ)) ((A : ℝ) + (N : ℝ)) := by
      rw [Set.uIcc_of_le (by linarith : (A : ℝ) ≤ (A : ℝ) + (N : ℝ))]
      intro hcon
      exact absurd hcon.1 (by linarith)
    rw [integral_rpow (Or.inr ⟨by intro hc; exact hβ1 (by linarith), hzeroNot⟩)]
    have hexp : -β + 1 = 1 - β := by ring
    rw [hexp]
  rw [hint] at hem
  have hodd : ∀ r : ℕ, ∀ y : ℝ, 0 < y →
      dqptPowTower β (2 * r + 1) y
        = -((∏ i ∈ Finset.range (2 * r + 1), (β + i)) * y ^ (-β - ((2 * r + 1 : ℕ) : ℝ))) := by
    intro r y _
    rw [dqptPowTower]
    have hs : (-1 : ℝ) ^ (2 * r + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    rw [hs]
    ring
  rw [hem, dqptEMApprox]
  have hterms : ∑ r ∈ Finset.range (m + 1),
        ((bernoulli (2 * r + 2) : ℚ) : ℝ) / (((2 * r + 2).factorial : ℕ) : ℝ)
          * (dqptPowTower β (2 * r + 1) ((A : ℝ) + (N : ℝ))
            - dqptPowTower β (2 * r + 1) (A : ℝ))
      = -∑ r ∈ Finset.range (m + 1),
          ((bernoulli (2 * r + 2) : ℚ) : ℝ) / (((2 * r + 2).factorial : ℕ) : ℝ)
            * (∏ i ∈ Finset.range (2 * r + 1), (β + i))
            * (((A : ℝ) + (N : ℝ)) ^ (-β - ((2 * r + 1 : ℕ) : ℝ))
              - (A : ℝ) ^ (-β - ((2 * r + 1 : ℕ) : ℝ))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hodd r _ hAN, hodd r _ hA0]
    ring
  rw [hterms]
  ring

end

end RHTower.DQPT

namespace RHTower.DQPT

open Filter Topology Set MeasureTheory

noncomputable section

/-! ## The remainder bound -/

theorem dqpt_abs_EMJ_le {F : ℕ → ℝ → ℝ} {t : ℝ}
    (hF : DqptDerivTower F (Set.Icc t (t + 1))) {k : ℕ} (hk : k ≠ 0) :
    |dqptEMJ F (2 * k) t|
      ≤ |((bernoulli (2 * k) : ℚ) : ℝ)| / (((2 * k).factorial : ℕ) : ℝ)
          * ∫ x in t..(t + 1), |F (2 * k) x| := by
  have hle : t ≤ t + 1 := by linarith
  have hcont : ContinuousOn (F (2 * k)) (Set.Icc t (t + 1)) := hF.continuousOn (2 * k)
  have hfac : (0 : ℝ) < (((2 * k).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hgcont : ContinuousOn
      (fun x : ℝ => |bernoulliFun (2 * k) (x - t) / (((2 * k).factorial : ℕ) : ℝ) * F (2 * k) x|)
      (Set.Icc t (t + 1)) := by
    refine ContinuousOn.abs (ContinuousOn.mul ?_ hcont)
    fun_prop
  have hg1 : IntervalIntegrable
      (fun x : ℝ => |bernoulliFun (2 * k) (x - t) / (((2 * k).factorial : ℕ) : ℝ)
        * F (2 * k) x|) volume t (t + 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [dqpt_uIcc_cell]
    exact hgcont
  have hg2 : IntervalIntegrable
      (fun x : ℝ => |((bernoulli (2 * k) : ℚ) : ℝ)| / (((2 * k).factorial : ℕ) : ℝ)
        * |F (2 * k) x|) volume t (t + 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [dqpt_uIcc_cell]
    exact ContinuousOn.mul continuousOn_const hcont.abs
  have hstep1 : |dqptEMJ F (2 * k) t|
      ≤ ∫ x in t..(t + 1),
          |bernoulliFun (2 * k) (x - t) / (((2 * k).factorial : ℕ) : ℝ) * F (2 * k) x| := by
    rw [dqptEMJ]
    exact intervalIntegral.abs_integral_le_integral_abs hle
  have hstep2 : (∫ x in t..(t + 1),
        |bernoulliFun (2 * k) (x - t) / (((2 * k).factorial : ℕ) : ℝ) * F (2 * k) x|)
      ≤ ∫ x in t..(t + 1),
          |((bernoulli (2 * k) : ℚ) : ℝ)| / (((2 * k).factorial : ℕ) : ℝ) * |F (2 * k) x| := by
    refine intervalIntegral.integral_mono_on hle hg1 hg2 (fun x hx => ?_)
    have hmem : x - t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith [hx.1]
      · linarith [hx.2]
    have hb := dqpt_abs_bernoulliFun_le hk hmem
    rw [abs_mul, abs_div, abs_of_pos hfac]
    exact mul_le_mul_of_nonneg_right (by
      exact div_le_div_of_nonneg_right hb (le_of_lt hfac)) (abs_nonneg _)
  refine hstep1.trans (hstep2.trans (le_of_eq ?_))
  rw [intervalIntegral.integral_const_mul]

/-- **Proposition 4.5, the remainder bound (4.34).** -/
theorem dqpt_em_remainder_bound {β : ℝ} (hβ : 0 < β) {A : ℕ} (hA : 1 ≤ A) (N m : ℕ) :
    |∑ n ∈ Finset.range N, dqptEMJ (dqptPowTower β) (2 * m + 2) ((A : ℝ) + n)|
      ≤ 4 / (2 * Real.pi) ^ (2 * m + 2) * (∏ i ∈ Finset.range (2 * m + 1), (β + i))
          * (A : ℝ) ^ (-β - ((2 * m + 1 : ℕ) : ℝ)) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hAN : (0 : ℝ) < (A : ℝ) + (N : ℝ) := by linarith
  have hfac : (0 : ℝ) < (((2 * m + 2).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hexp : (2 : ℕ) * (m + 1) = 2 * m + 2 := by ring
  -- cell bound
  have hcellbd : ∀ n : ℕ, n < N →
      |dqptEMJ (dqptPowTower β) (2 * m + 2) ((A : ℝ) + n)|
        ≤ |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / (((2 * m + 2).factorial : ℕ) : ℝ)
            * ∫ x in ((A : ℝ) + n)..((A : ℝ) + n + 1),
                (∏ i ∈ Finset.range (2 * m + 2), (β + i)) * x ^ (-β - ((2 * m + 2 : ℕ) : ℝ)) := by
    intro n _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsub : Set.Icc ((A : ℝ) + n) ((A : ℝ) + n + 1) ⊆ Set.Ioi (0 : ℝ) := by
      intro x hx
      have : (0 : ℝ) < (A : ℝ) + (n : ℝ) := by linarith
      exact lt_of_lt_of_le this hx.1
    have htower : DqptDerivTower (dqptPowTower β)
        (Set.Icc ((A : ℝ) + n) ((A : ℝ) + n + 1)) := (dqptPowTower_isTower β).mono hsub
    have hbase := dqpt_abs_EMJ_le (k := m + 1) htower (by omega)
    rw [hexp] at hbase
    refine hbase.trans ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by linarith : (A : ℝ) + (n : ℝ) ≤ (A : ℝ) + (n : ℝ) + 1)] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by linarith) hx.1
    exact dqptPowTower_abs hβ hx0 (2 * m + 2)
  -- the cell integrals add up
  have hintfun : ∀ p q : ℝ, 0 < p → p ≤ q → IntervalIntegrable
      (fun x : ℝ => (∏ i ∈ Finset.range (2 * m + 2), (β + i))
        * x ^ (-β - ((2 * m + 2 : ℕ) : ℝ))) volume p q := by
    intro p q hp hpq
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hpq]
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.rpow_const continuousOn_id (fun x hx => ?_)
    exact Or.inl (ne_of_gt (lt_of_lt_of_le hp hx.1))
  have hadj : ∑ n ∈ Finset.range N,
      (∫ x in ((A : ℝ) + n)..((A : ℝ) + (n + 1 : ℕ)),
        (∏ i ∈ Finset.range (2 * m + 2), (β + i)) * x ^ (-β - ((2 * m + 2 : ℕ) : ℝ)))
      = ∫ x in ((A : ℝ) + (0 : ℕ))..((A : ℝ) + (N : ℕ)),
        (∏ i ∈ Finset.range (2 * m + 2), (β + i)) * x ^ (-β - ((2 * m + 2 : ℕ) : ℝ)) := by
    refine intervalIntegral.sum_integral_adjacent_intervals (a := fun n : ℕ => (A : ℝ) + n)
      (fun n _ => ?_)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    refine hintfun _ _ (by linarith) ?_
    push_cast
    linarith
  -- assemble
  have habs : |∑ n ∈ Finset.range N, dqptEMJ (dqptPowTower β) (2 * m + 2) ((A : ℝ) + n)|
      ≤ ∑ n ∈ Finset.range N,
          |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / (((2 * m + 2).factorial : ℕ) : ℝ)
            * ∫ x in ((A : ℝ) + n)..((A : ℝ) + (n + 1 : ℕ)),
                (∏ i ∈ Finset.range (2 * m + 2), (β + i))
                  * x ^ (-β - ((2 * m + 2 : ℕ) : ℝ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
    have hcast : ((A : ℝ) + ((n + 1 : ℕ) : ℝ)) = (A : ℝ) + (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact hcellbd n (Finset.mem_range.mp hn)
  rw [← Finset.mul_sum, hadj] at habs
  refine habs.trans ?_
  -- evaluate the integral
  have hzeroNot : (0 : ℝ) ∉ Set.uIcc ((A : ℝ) + ((0 : ℕ) : ℝ)) ((A : ℝ) + ((N : ℕ) : ℝ)) := by
    rw [Set.uIcc_of_le (by push_cast; linarith :
      (A : ℝ) + ((0 : ℕ) : ℝ) ≤ (A : ℝ) + ((N : ℕ) : ℝ))]
    intro hcon
    have := hcon.1
    push_cast at this
    linarith
  have hne : (-β - ((2 * m + 2 : ℕ) : ℝ)) ≠ -1 := by
    have hpos : (2 : ℝ) ≤ ((2 * m + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : (2 : ℕ) ≤ 2 * m + 2)
    intro hc
    linarith
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨hne, hzeroNot⟩)]
  have hexp1 : -β - ((2 * m + 2 : ℕ) : ℝ) + 1 = -β - ((2 * m + 1 : ℕ) : ℝ) := by
    push_cast; ring
  rw [hexp1]
  have hden : (0 : ℝ) < β + ((2 * m + 1 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hnum : ((A : ℝ) + ((N : ℕ) : ℝ)) ^ (-β - ((2 * m + 1 : ℕ) : ℝ))
      ≤ (A : ℝ) ^ (-β - ((2 * m + 1 : ℕ) : ℝ)) := by
    refine Real.rpow_le_rpow_of_nonpos hA0 (by linarith) (by linarith)
  have hAp : (0 : ℝ) < (A : ℝ) ^ (-β - ((2 * m + 1 : ℕ) : ℝ)) := Real.rpow_pos_of_pos hA0 _
  have hANp : (0 : ℝ) < ((A : ℝ) + ((N : ℕ) : ℝ)) ^ (-β - ((2 * m + 1 : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hquot : (((A : ℝ) + ((N : ℕ) : ℝ)) ^ (-β - ((2 * m + 1 : ℕ) : ℝ))
        - ((A : ℝ) + ((0 : ℕ) : ℝ)) ^ (-β - ((2 * m + 1 : ℕ) : ℝ)))
      / (-β - ((2 * m + 1 : ℕ) : ℝ))
      ≤ (A : ℝ) ^ (-β - ((2 * m + 1 : ℕ) : ℝ)) / (β + ((2 * m + 1 : ℕ) : ℝ)) := by
    have hA0cast : ((A : ℝ) + ((0 : ℕ) : ℝ)) = (A : ℝ) := by push_cast; ring
    have hD : (-β - ((2 * m + 1 : ℕ) : ℝ)) = -(β + ((2 * m + 1 : ℕ) : ℝ)) := by ring
    rw [hD] at hANp
    rw [hA0cast, hD, div_neg, ← neg_div, neg_sub]
    exact (div_le_div_iff_of_pos_right hden).mpr (by linarith [hANp])
  have hprodpos : (0 : ℝ) < ∏ i ∈ Finset.range (2 * m + 2), (β + i) := by
    refine Finset.prod_pos (fun i _ => ?_)
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  have hbcoef : (0 : ℝ) ≤ |((bernoulli (2 * m + 2) : ℚ) : ℝ)| /
      (((2 * m + 2).factorial : ℕ) : ℝ) := by positivity
  have hstep : |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / (((2 * m + 2).factorial : ℕ) : ℝ)
      * ((∏ i ∈ Finset.range (2 * m + 2), (β + i))
        * ((((A : ℝ) + ((N : ℕ) : ℝ)) ^ (-β - ((2 * m + 1 : ℕ) : ℝ))
            - ((A : ℝ) + ((0 : ℕ) : ℝ)) ^ (-β - ((2 * m + 1 : ℕ) : ℝ)))
          / (-β - ((2 * m + 1 : ℕ) : ℝ))))
      ≤ |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / (((2 * m + 2).factorial : ℕ) : ℝ)
        * ((∏ i ∈ Finset.range (2 * m + 2), (β + i))
          * ((A : ℝ) ^ (-β - ((2 * m + 1 : ℕ) : ℝ)) / (β + ((2 * m + 1 : ℕ) : ℝ)))) := by
    refine mul_le_mul_of_nonneg_left ?_ hbcoef
    exact mul_le_mul_of_nonneg_left hquot (le_of_lt hprodpos)
  refine hstep.trans ?_
  -- the Bernoulli coefficient and the Pochhammer telescope
  have hprodsplit : (∏ i ∈ Finset.range (2 * m + 2), (β + i))
      = (∏ i ∈ Finset.range (2 * m + 1), (β + i)) * (β + ((2 * m + 1 : ℕ) : ℝ)) := by
    rw [Finset.prod_range_succ]
  have hBbound : |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / (((2 * m + 2).factorial : ℕ) : ℝ)
      ≤ 4 / (2 * Real.pi) ^ (2 * m + 2) := by
    have hpipos : (0 : ℝ) < (2 * Real.pi) ^ (2 * m + 2) := by positivity
    have hp : (0 : ℝ) < (2 : ℝ) ^ (2 * m + 2) := by positivity
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (2 * m + 2) := by
      have h2 : (2 : ℝ) ^ (2 : ℕ) ≤ (2 : ℝ) ^ (2 * m + 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at h2
      linarith
    have hle2 : (2 : ℝ) / (2 : ℝ) ^ (2 * m + 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hp (by norm_num)]
      linarith
    have hhalf : (1 : ℝ) / 2 ≤ 1 - 2 / (2 : ℝ) ^ (2 * m + 2) := by linarith
    have hinv2 : ((1 : ℝ) - 2 / (2 : ℝ) ^ (2 * m + 2))⁻¹ ≤ 2 := by
      rw [inv_eq_one_div]
      calc (1 : ℝ) / ((1 : ℝ) - 2 / (2 : ℝ) ^ (2 * m + 2)) ≤ 1 / ((1 : ℝ) / 2) :=
            one_div_le_one_div_of_le (by norm_num) hhalf
        _ = 2 := by norm_num
    have hkey := (dqpt_abs_bernoulli_bounds (k := m + 1) (by omega)).2
    rw [hexp] at hkey
    have hbound2 : |((bernoulli (2 * m + 2) : ℚ) : ℝ)|
        ≤ 2 * (((2 * m + 2).factorial : ℕ) : ℝ) / (2 * Real.pi) ^ (2 * m + 2) * 2 :=
      hkey.trans (mul_le_mul_of_nonneg_left hinv2 (by positivity))
    have hclear : 2 * (((2 * m + 2).factorial : ℕ) : ℝ) / (2 * Real.pi) ^ (2 * m + 2) * 2
        * (2 * Real.pi) ^ (2 * m + 2) = 4 * (((2 * m + 2).factorial : ℕ) : ℝ) := by
      field_simp
      ring
    rw [div_le_div_iff₀ hfac hpipos]
    nlinarith [hbound2, hpipos, hclear]
  have hrest : (0 : ℝ) ≤ (∏ i ∈ Finset.range (2 * m + 2), (β + i))
      * ((A : ℝ) ^ (-β - ((2 * m + 1 : ℕ) : ℝ)) / (β + ((2 * m + 1 : ℕ) : ℝ))) := by
    positivity
  refine (mul_le_mul_of_nonneg_right hBbound hrest).trans (le_of_eq ?_)
  rw [hprodsplit]
  field_simp

end

end RHTower.DQPT
