import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The Euler–Maclaurin sawtooth step, for a general integrand

On a unit interval `[m, m+1]` the local second Bernoulli half

```text
Q(x) = ((x - m)² - (x - m))/2
```

vanishes at both endpoints and has derivative the centred sawtooth `x - m - 1/2`.  Integrating a `C¹`
integrand against the sawtooth therefore produces **no boundary term**, and lifts the conditionally
summable `B₁` kernel to the bounded continuous `B₂` kernel.

The corpus already has this step specialized to the integrand `x ↦ x^{-s-1}`
(`RHTower.sawtooth_ibp_unit`, built for the zeta truncation).  This module states it for an arbitrary
`C¹` integrand, which is what an endpoint-jet estimate needs.

* `bernoulliHalf`, `hasDerivAt_bernoulliHalf`, `bernoulliHalf_endpoints`, `abs_bernoulliHalf_le` —
  the kernel, its derivative, its vanishing at the endpoints and its uniform bound `1/8`.
* `integral_sawtooth_mul_eq` — the integration by parts on one unit cell.
* `integral_fract_sub_half_mul_eq` — the same with the centred sawtooth written as `{x} - 1/2`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral Set

/-- The local second Bernoulli half on the cell starting at `m`. -/
def bernoulliHalf (m : ℤ) (x : ℝ) : ℝ := ((x - (m : ℝ)) ^ 2 - (x - (m : ℝ))) / 2

theorem hasDerivAt_bernoulliHalf (m : ℤ) (x : ℝ) :
    HasDerivAt (bernoulliHalf m) (x - (m : ℝ) - 1 / 2) x := by
  have h1 : HasDerivAt (fun y : ℝ => y - (m : ℝ)) 1 x := by
    simpa using (hasDerivAt_id x).sub_const (m : ℝ)
  have h2 : HasDerivAt (fun y : ℝ => (y - (m : ℝ)) ^ 2) (2 * (x - (m : ℝ)) ^ 1 * 1) x :=
    h1.pow 2
  have h3 : HasDerivAt (fun y : ℝ => (y - (m : ℝ)) ^ 2 - (y - (m : ℝ)))
      (2 * (x - (m : ℝ)) ^ 1 * 1 - 1) x := h2.fun_sub h1
  have h4 := h3.div_const 2
  have hval : (2 * (x - (m : ℝ)) ^ 1 * 1 - 1) / 2 = x - (m : ℝ) - 1 / 2 := by ring
  show HasDerivAt (fun y : ℝ => ((y - (m : ℝ)) ^ 2 - (y - (m : ℝ))) / 2) (x - (m : ℝ) - 1 / 2) x
  rw [← hval]
  exact h4

theorem bernoulliHalf_left (m : ℤ) : bernoulliHalf m (m : ℝ) = 0 := by
  rw [bernoulliHalf]
  simp

theorem bernoulliHalf_right (m : ℤ) : bernoulliHalf m ((m : ℝ) + 1) = 0 := by
  rw [bernoulliHalf]
  have h : (m : ℝ) + 1 - (m : ℝ) = 1 := by ring
  rw [h]
  norm_num

theorem abs_bernoulliHalf_le {m : ℤ} {x : ℝ} (hx : x ∈ Icc ((m : ℝ)) ((m : ℝ) + 1)) :
    |bernoulliHalf m x| ≤ 1 / 8 := by
  have h0 : (0 : ℝ) ≤ x - (m : ℝ) := by linarith [hx.1]
  have h1 : x - (m : ℝ) ≤ 1 := by linarith [hx.2]
  rw [bernoulliHalf, abs_le]
  constructor <;> nlinarith [sq_nonneg (x - (m : ℝ) - 1 / 2), sq_nonneg (x - (m : ℝ))]

theorem continuous_bernoulliHalf (m : ℤ) : Continuous (bernoulliHalf m) := by
  unfold bernoulliHalf
  fun_prop

/-- **The Euler–Maclaurin sawtooth step on one cell.**  The local `B₂` half vanishes at both integer
endpoints, so the boundary term is absent and the centred sawtooth is traded for the bounded kernel. -/
theorem integral_sawtooth_mul_eq (m : ℤ) {V V' : ℝ → ℝ}
    (hV : ∀ x ∈ uIcc ((m : ℝ)) ((m : ℝ) + 1), HasDerivAt V (V' x) x)
    (hV'i : IntervalIntegrable V' volume ((m : ℝ)) ((m : ℝ) + 1)) :
    (∫ x in ((m : ℝ))..((m : ℝ) + 1), (x - (m : ℝ) - 1 / 2) * V x)
      = -∫ x in ((m : ℝ))..((m : ℝ) + 1), bernoulliHalf m x * V' x := by
  have hcont : IntervalIntegrable (fun x : ℝ => x - (m : ℝ) - 1 / 2) volume
      ((m : ℝ)) ((m : ℝ) + 1) := by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := bernoulliHalf m) (u' := fun x : ℝ => x - (m : ℝ) - 1 / 2) (v := V) (v' := V')
    (a := (m : ℝ)) (b := (m : ℝ) + 1)
    (fun x _ => hasDerivAt_bernoulliHalf m x) (fun x hx => hV x hx) hcont hV'i
  rw [bernoulliHalf_left, bernoulliHalf_right, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  rw [← neg_eq_iff_eq_neg]
  rw [← hibp]

theorem fract_eq_sub_intCast {m : ℤ} {x : ℝ} (hx : x ∈ Ico ((m : ℝ)) ((m : ℝ) + 1)) :
    Int.fract x = x - (m : ℝ) := by
  have hfl : ⌊x⌋ = m := by
    rw [Int.floor_eq_iff]
    exact ⟨hx.1, hx.2⟩
  have hfr : Int.fract x = x - ((⌊x⌋ : ℤ) : ℝ) := rfl
  rw [hfl] at hfr
  exact hfr

/-- The same step with the centred sawtooth written through the fractional part. -/
theorem integral_fract_sub_half_mul_eq (m : ℤ) {V V' : ℝ → ℝ}
    (hV : ∀ x ∈ uIcc ((m : ℝ)) ((m : ℝ) + 1), HasDerivAt V (V' x) x)
    (hV'i : IntervalIntegrable V' volume ((m : ℝ)) ((m : ℝ) + 1)) :
    (∫ x in ((m : ℝ))..((m : ℝ) + 1), (Int.fract x - 1 / 2) * V x)
      = -∫ x in ((m : ℝ))..((m : ℝ) + 1), bernoulliHalf m x * V' x := by
  have hle : ((m : ℝ)) ≤ (m : ℝ) + 1 := by linarith
  have hcongr : (∫ x in ((m : ℝ))..((m : ℝ) + 1), (Int.fract x - 1 / 2) * V x)
      = ∫ x in ((m : ℝ))..((m : ℝ) + 1), (x - (m : ℝ) - 1 / 2) * V x := by
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : ({((m : ℝ) + 1)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
      MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton _)
    filter_upwards [hnull] with x hxne hxmem
    rw [Set.uIoc_of_le hle] at hxmem
    have hlt : x < (m : ℝ) + 1 := lt_of_le_of_ne hxmem.2 (by simpa using hxne)
    rw [fract_eq_sub_intCast ⟨hxmem.1.le, hlt⟩]
  rw [hcongr]
  exact integral_sawtooth_mul_eq m hV hV'i

/-! ## The trapezoid form and first-order Euler–Maclaurin -/

/-- **The trapezoid cell identity.**  Integrating the centred sawtooth against `g'` on one cell gives
the trapezoid rule's error.  Here the ramp does *not* vanish at the endpoints — it is `±1/2` — and those
two values are exactly the trapezoid weights. -/
theorem integral_sawtooth_trapezoid_cell (c : ℝ) {g g' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'c : Continuous g') :
    (∫ x in c..(c + 1), (x - c - 1 / 2) * g' x)
      = (g (c + 1) + g c) / 2 - ∫ x in c..(c + 1), g x := by
  have hu : ∀ x ∈ uIcc c (c + 1), HasDerivAt (fun y : ℝ => y - c - 1 / 2) 1 x := by
    intro x _
    simpa using ((hasDerivAt_id x).sub_const c).sub_const (1 / 2 : ℝ)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => y - c - 1 / 2) (u' := fun _ : ℝ => (1 : ℝ)) (v := g) (v' := g')
    (a := c) (b := c + 1)
    hu (fun x _ => hg x) intervalIntegrable_const (hg'c.intervalIntegrable _ _)
  have hone : (∫ x in c..(c + 1), (1 : ℝ) * g x) = ∫ x in c..(c + 1), g x :=
    intervalIntegral.integral_congr fun x _ => one_mul _
  rw [hone] at hibp
  rw [hibp]
  ring

/-- On a cell starting at an integer the fractional part may be replaced by the affine ramp. -/
theorem integral_fract_cell_eq (k : ℤ) (h : ℝ → ℝ) :
    (∫ x in ((k : ℝ))..((k : ℝ) + 1), (Int.fract x - 1 / 2) * h x)
      = ∫ x in ((k : ℝ))..((k : ℝ) + 1), (x - (k : ℝ) - 1 / 2) * h x := by
  have hle : ((k : ℝ)) ≤ (k : ℝ) + 1 := by linarith
  refine intervalIntegral.integral_congr_ae ?_
  have hnull : ({((k : ℝ) + 1)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton _)
  filter_upwards [hnull] with x hxne hxmem
  rw [Set.uIoc_of_le hle] at hxmem
  have hlt : x < (k : ℝ) + 1 := lt_of_le_of_ne hxmem.2 (by simpa using hxne)
  rw [fract_eq_sub_intCast ⟨hxmem.1.le, hlt⟩]

theorem intervalIntegrable_fract_mul (k : ℤ) {h : ℝ → ℝ} (hc : Continuous h) :
    IntervalIntegrable (fun x : ℝ => (Int.fract x - 1 / 2) * h x) volume
      ((k : ℝ)) ((k : ℝ) + 1) := by
  have hle : ((k : ℝ)) ≤ (k : ℝ) + 1 := by linarith
  have hbase : IntervalIntegrable (fun x : ℝ => (x - (k : ℝ) - 1 / 2) * h x) volume
      ((k : ℝ)) ((k : ℝ) + 1) := by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at hbase ⊢
  refine hbase.congr ?_
  have hnull : ({((k : ℝ) + 1)}ᶜ : Set ℝ)
      ∈ ae (volume.restrict (Ioc ((k : ℝ)) ((k : ℝ) + 1))) := by
    refine MeasureTheory.compl_mem_ae_iff.mpr ?_
    refine nonpos_iff_eq_zero.mp ?_
    exact le_trans (Measure.restrict_apply_le _ _) (le_of_eq (measure_singleton _))
  filter_upwards [hnull, ae_restrict_mem measurableSet_Ioc] with x hxne hxmem
  have hlt : x < (k : ℝ) + 1 := lt_of_le_of_ne hxmem.2 (by simpa using hxne)
  rw [fract_eq_sub_intCast ⟨hxmem.1.le, hlt⟩]

theorem sum_trapezoid_eq (g : ℝ → ℝ) : ∀ N : ℕ,
    (∑ k ∈ Finset.range N, (g ((k : ℝ) + 1) + g (k : ℝ)) / 2)
      = (∑ m ∈ Finset.range (N + 1), g (m : ℝ)) - (g 0 + g (N : ℝ)) / 2
  | 0 => by simp
  | (N + 1) => by
    have ih := sum_trapezoid_eq g N
    have hc : ((N + 1 : ℕ) : ℝ) = ((N : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun m : ℕ => g ((m : ℕ) : ℝ)) (N + 1), hc]
    ring

/-- **First-order Euler–Maclaurin.**  The centred sawtooth integrated against `g'` is exactly the
difference between the trapezoidal sum and the integral.  This is the identity that turns an arithmetic
sum of samples into an integral plus a sawtooth remainder. -/
theorem integral_fract_mul_deriv_eq {g g' : ℝ → ℝ} (N : ℕ)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'c : Continuous g') :
    (∫ x in (0 : ℝ)..((N : ℕ) : ℝ), (Int.fract x - 1 / 2) * g' x)
      = (∑ m ∈ Finset.range (N + 1), g ((m : ℕ) : ℝ)) - (g 0 + g ((N : ℕ) : ℝ)) / 2
        - ∫ x in (0 : ℝ)..((N : ℕ) : ℝ), g x := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hcast : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) = ((j : ℕ) : ℝ) + 1 := by
    intro j; push_cast; ring
  have hintcell : ∀ j : ℕ, IntervalIntegrable (fun x : ℝ => (Int.fract x - 1 / 2) * g' x) volume
      (((j : ℕ) : ℝ)) (((j : ℕ) : ℝ) + 1) := by
    intro j
    have h := intervalIntegrable_fract_mul ((j : ℕ) : ℤ) hg'c
    have hc : ((((j : ℕ) : ℤ)) : ℝ) = ((j : ℕ) : ℝ) := by push_cast; ring
    rwa [hc] at h
  have hpart1 := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => ((j : ℕ) : ℝ))
    (f := fun x : ℝ => (Int.fract x - 1 / 2) * g' x) (n := N)
    (fun j _ => by rw [hcast j]; exact hintcell j)
  have hpart2 := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => ((j : ℕ) : ℝ)) (f := g) (n := N)
    (fun j _ => hgc.intervalIntegrable (μ := volume) _ _)
  have hzero : ((0 : ℕ) : ℝ) = 0 := by norm_num
  rw [hzero] at hpart1 hpart2
  have hcell : ∀ j ∈ Finset.range N,
      (∫ x in (((j : ℕ) : ℝ))..(((j + 1 : ℕ)) : ℝ), (Int.fract x - 1 / 2) * g' x)
        = (g (((j : ℕ) : ℝ) + 1) + g ((j : ℕ) : ℝ)) / 2
          - ∫ x in (((j : ℕ) : ℝ))..(((j + 1 : ℕ)) : ℝ), g x := by
    intro j _
    rw [hcast j]
    have hfc : (∫ x in (((j : ℕ) : ℝ))..(((j : ℕ) : ℝ) + 1), (Int.fract x - 1 / 2) * g' x)
        = ∫ x in (((j : ℕ) : ℝ))..(((j : ℕ) : ℝ) + 1), (x - ((j : ℕ) : ℝ) - 1 / 2) * g' x := by
      have h := integral_fract_cell_eq ((j : ℕ) : ℤ) g'
      have hc : ((((j : ℕ) : ℤ)) : ℝ) = ((j : ℕ) : ℝ) := by push_cast; ring
      rwa [hc] at h
    rw [hfc, integral_sawtooth_trapezoid_cell (((j : ℕ) : ℝ)) hg hg'c]
  rw [← hpart1, Finset.sum_congr rfl hcell, Finset.sum_sub_distrib, ← hpart2,
    sum_trapezoid_eq g N]

end GaloisForLFunctions.RHTower

end
