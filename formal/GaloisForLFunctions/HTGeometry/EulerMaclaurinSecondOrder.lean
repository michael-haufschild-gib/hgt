import Mathlib

/-!
# Second-order Euler–Maclaurin summation

For a twice continuously differentiable complex function on `[0, N]`,

```text
∑_{m=0}^{N} f(m) = ∫_0^N f + (f(0) + f(N))/2 − ∫_0^N P₂(x) f''(x) dx,
```

where `P₂(x) = ({x}² − {x})/2` is the periodic second Bernoulli half.  The kernel `P₂` is bounded by
`1/8` and vanishes at the integers, so the two integrations by parts on each unit cell leave no
boundary term.  This is the form of Euler–Maclaurin with an *absolutely* convergent remainder: the
first-order sawtooth `{x} − 1/2` only gives a conditionally convergent tail.
-/

open Complex intervalIntegral MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The periodic second Bernoulli half -/

/-- The periodic second Bernoulli half `({x}² − {x})/2`. -/
def bernoulliHalfPer (x : ℝ) : ℝ := (Int.fract x ^ 2 - Int.fract x) / 2

theorem bernoulliHalfPer_intCast (m : ℤ) : bernoulliHalfPer (m : ℝ) = 0 := by
  rw [bernoulliHalfPer, Int.fract_intCast]
  norm_num

theorem bernoulliHalfPer_natCast (m : ℕ) : bernoulliHalfPer (m : ℝ) = 0 := by
  have := bernoulliHalfPer_intCast (m : ℤ)
  simpa using this

theorem abs_bernoulliHalfPer_le (x : ℝ) : |bernoulliHalfPer x| ≤ 1 / 8 := by
  have h0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  rw [bernoulliHalfPer, abs_le]
  constructor <;> nlinarith [sq_nonneg (Int.fract x - 1 / 2)]

theorem measurable_bernoulliHalfPer : Measurable bernoulliHalfPer := by
  unfold bernoulliHalfPer
  fun_prop

/-- On a unit cell the periodic kernel is the local quadratic. -/
theorem bernoulliHalfPer_eq_of_mem_Ico {m : ℤ} {x : ℝ} (hx : x ∈ Ico ((m : ℝ)) ((m : ℝ) + 1)) :
    bernoulliHalfPer x = ((x - (m : ℝ)) ^ 2 - (x - (m : ℝ))) / 2 := by
  have hfl : ⌊x⌋ = m := by
    rw [Int.floor_eq_iff]
    exact ⟨hx.1, hx.2⟩
  rw [bernoulliHalfPer, Int.fract, hfl]

/-- The local quadratic on the cell `[c, c+1]`. -/
def cellBernoulli (c : ℝ) (x : ℝ) : ℝ := ((x - c) ^ 2 - (x - c)) / 2

theorem hasDerivAt_cellBernoulli (c : ℝ) (x : ℝ) :
    HasDerivAt (cellBernoulli c) (x - c - 1 / 2) x := by
  have h1 : HasDerivAt (fun z : ℝ => z - c) 1 x := (hasDerivAt_id x).sub_const _
  have hraw := ((h1.pow 2).sub h1).div_const 2
  have hfun : (fun y : ℝ => ((fun z : ℝ => z - c) ^ 2 - fun z : ℝ => z - c) y / 2)
      = cellBernoulli c := by
    funext z
    simp [cellBernoulli, Pi.sub_apply, Pi.pow_apply]
  rw [hfun] at hraw
  refine hraw.congr_deriv ?_
  push_cast
  ring

theorem cellBernoulli_left (c : ℝ) : cellBernoulli c c = 0 := by
  rw [cellBernoulli]
  norm_num

theorem cellBernoulli_right (c : ℝ) : cellBernoulli c (c + 1) = 0 := by
  rw [cellBernoulli]
  norm_num

theorem continuous_cellBernoulli (c : ℝ) : Continuous (cellBernoulli c) := by
  unfold cellBernoulli
  fun_prop

/-! ## The two integrations by parts on a cell -/

/-- **Cell trapezoid identity.**  The centred sawtooth against `f'` is the trapezoid defect. -/
theorem integral_cellSaw_mul_deriv (c : ℝ) {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ uIcc c (c + 1), HasDerivAt f (f' x) x)
    (hf'i : IntervalIntegrable f' volume c (c + 1)) :
    (∫ x in c..(c + 1), ((x - c - 1 / 2 : ℝ) : ℂ) * f' x)
      = (f (c + 1) + f c) / 2 - ∫ x in c..(c + 1), f x := by
  have hu : ∀ x ∈ uIcc c (c + 1),
      HasDerivAt (fun y : ℝ => ((y - c - 1 / 2 : ℝ) : ℂ)) 1 x := by
    intro x _
    have hreal : HasDerivAt (fun y : ℝ => y - c - 1 / 2) 1 x :=
      ((hasDerivAt_id x).sub_const c).sub_const (1 / 2)
    simpa using hreal.ofReal_comp
  have hu'i : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume c (c + 1) :=
    intervalIntegrable_const
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hf hu'i hf'i
  rw [hibp]
  have hval1 : (((c + 1) - c - 1 / 2 : ℝ) : ℂ) = 1 / 2 := by
    push_cast
    ring
  have hval0 : ((c - c - 1 / 2 : ℝ) : ℂ) = -(1 / 2) := by
    push_cast
    ring
  rw [hval1, hval0]
  have hone : (∫ x in c..(c + 1), (1 : ℂ) * f x) = ∫ x in c..(c + 1), f x := by
    simp
  rw [hone]
  ring

/-- **Cell lifting identity.**  The centred sawtooth against `f'` lifts to the `B₂` kernel against
`f''` with no boundary term. -/
theorem integral_cellSaw_mul_deriv_two (c : ℝ) {f' f'' : ℝ → ℂ}
    (hf' : ∀ x ∈ uIcc c (c + 1), HasDerivAt f' (f'' x) x)
    (hf''i : IntervalIntegrable f'' volume c (c + 1)) :
    (∫ x in c..(c + 1), ((x - c - 1 / 2 : ℝ) : ℂ) * f' x)
      = -∫ x in c..(c + 1), ((cellBernoulli c x : ℝ) : ℂ) * f'' x := by
  have hu : ∀ x ∈ uIcc c (c + 1),
      HasDerivAt (fun y : ℝ => ((cellBernoulli c y : ℝ) : ℂ)) ((x - c - 1 / 2 : ℝ) : ℂ) x := by
    intro x _
    simpa using (hasDerivAt_cellBernoulli c x).ofReal_comp
  have hu'i : IntervalIntegrable (fun x : ℝ => ((x - c - 1 / 2 : ℝ) : ℂ)) volume c (c + 1) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hf' hu'i hf''i
  rw [hibp, cellBernoulli_left, cellBernoulli_right]
  simp

/-- **Cell Euler–Maclaurin.**  The trapezoid defect on a unit cell equals the `B₂` remainder. -/
theorem cell_euler_maclaurin (c : ℝ) {f f' f'' : ℝ → ℂ}
    (hf : ∀ x ∈ uIcc c (c + 1), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ uIcc c (c + 1), HasDerivAt f' (f'' x) x)
    (hf''i : IntervalIntegrable f'' volume c (c + 1)) :
    (f (c + 1) + f c) / 2 - (∫ x in c..(c + 1), f x)
      = -∫ x in c..(c + 1), ((cellBernoulli c x : ℝ) : ℂ) * f'' x := by
  have hf'c : ContinuousOn f' (uIcc c (c + 1)) := fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hf'i : IntervalIntegrable f' volume c (c + 1) :=
    hf'c.intervalIntegrable
  rw [← integral_cellSaw_mul_deriv c hf hf'i]
  exact integral_cellSaw_mul_deriv_two c hf' hf''i

theorem bernoulliHalfPer_eq_cellBernoulli_of_mem_Icc {m : ℤ} {x : ℝ}
    (hx : x ∈ Icc ((m : ℝ)) ((m : ℝ) + 1)) : bernoulliHalfPer x = cellBernoulli ((m : ℝ)) x := by
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · rw [bernoulliHalfPer_eq_of_mem_Ico ⟨hx.1, hlt⟩, cellBernoulli]
  · rw [heq, cellBernoulli_right]
    have : ((m : ℝ)) + 1 = (((m + 1 : ℤ)) : ℝ) := by push_cast; ring
    rw [this, bernoulliHalfPer_intCast]

theorem bernoulliHalfPer_eq_cellBernoulli_natCast {j : ℕ} {x : ℝ}
    (hx : x ∈ Icc ((j : ℝ)) ((j : ℝ) + 1)) : bernoulliHalfPer x = cellBernoulli ((j : ℝ)) x := by
  have hxm : x ∈ Icc (((j : ℤ) : ℝ)) (((j : ℤ) : ℝ) + 1) := by
    push_cast
    exact hx
  have h := bernoulliHalfPer_eq_cellBernoulli_of_mem_Icc hxm
  simpa using h

/-! ## The summed formula -/

theorem sum_trapezoid_complex (f : ℝ → ℂ) : ∀ N : ℕ,
    (∑ j ∈ Finset.range N, (f ((j : ℝ) + 1) + f (j : ℝ)) / 2)
      = (∑ m ∈ Finset.range (N + 1), f (m : ℝ)) - (f 0 + f (N : ℝ)) / 2
  | 0 => by simp
  | (N + 1) => by
    have ih := sum_trapezoid_complex f N
    have hc : ((N + 1 : ℕ) : ℝ) = ((N : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun m : ℕ => f ((m : ℕ) : ℝ)) (N + 1), hc]
    ring

/-- **Second-order Euler–Maclaurin summation.**  For a twice differentiable complex function on
`[0, ∞)` with continuous second derivative,
`∑_{m ≤ N} f(m) = ∫_0^N f + (f(0)+f(N))/2 − ∫_0^N P₂(x) f''(x) dx`. -/
theorem euler_maclaurin_second_order {f f' f'' : ℝ → ℂ} (N : ℕ)
    (hf : ∀ x ∈ Ici (0 : ℝ), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ici (0 : ℝ), HasDerivAt f' (f'' x) x)
    (hf''c : ContinuousOn f'' (Ici (0 : ℝ))) :
    (∑ m ∈ Finset.range (N + 1), f (m : ℝ))
      = (∫ x in (0 : ℝ)..(N : ℝ), f x) + (f 0 + f (N : ℝ)) / 2
        - ∫ x in (0 : ℝ)..(N : ℝ), ((bernoulliHalfPer x : ℝ) : ℂ) * f'' x := by
  have hsub : ∀ j : ℕ, uIcc ((j : ℝ)) ((j : ℝ) + 1) ⊆ Ici (0 : ℝ) := by
    intro j x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    exact le_trans hj hx.1
  have hf''cell : ∀ j : ℕ, ContinuousOn f'' (uIcc ((j : ℝ)) ((j : ℝ) + 1)) :=
    fun j => hf''c.mono (hsub j)
  have hf''i : ∀ j : ℕ, IntervalIntegrable f'' volume ((j : ℝ)) ((j : ℝ) + 1) :=
    fun j => (hf''cell j).intervalIntegrable
  have hfc : ContinuousOn f (Ici (0 : ℝ)) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfi : ∀ j : ℕ, IntervalIntegrable f volume ((j : ℝ)) ((j : ℝ) + 1) :=
    fun j => (hfc.mono (hsub j)).intervalIntegrable
  have hkercont : ∀ j : ℕ, IntervalIntegrable
      (fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) * f'' x) volume ((j : ℝ)) ((j : ℝ) + 1) := by
    intro j
    have hbase : IntervalIntegrable
        (fun x : ℝ => ((cellBernoulli ((j : ℝ)) x : ℝ) : ℂ) * f'' x)
        volume ((j : ℝ)) ((j : ℝ) + 1) :=
      ((continuous_ofReal.comp (continuous_cellBernoulli ((j : ℝ)))).continuousOn.mul
        (hf''cell j)).intervalIntegrable
    refine hbase.congr ?_
    intro x hx
    rw [uIoc_of_le (by linarith)] at hx
    show ((cellBernoulli ((j : ℝ)) x : ℝ) : ℂ) * f'' x = ((bernoulliHalfPer x : ℝ) : ℂ) * f'' x
    rw [bernoulliHalfPer_eq_cellBernoulli_natCast ⟨hx.1.le, hx.2⟩]
  have hcell : ∀ j ∈ Finset.range N,
      (f ((j : ℝ) + 1) + f (j : ℝ)) / 2 - (∫ x in ((j : ℝ))..((j : ℝ) + 1), f x)
        = -∫ x in ((j : ℝ))..((j : ℝ) + 1), ((bernoulliHalfPer x : ℝ) : ℂ) * f'' x := by
    intro j _
    have hem := cell_euler_maclaurin ((j : ℝ))
      (fun x hx => hf x (hsub j hx)) (fun x hx => hf' x (hsub j hx)) (hf''i j)
    rw [hem]
    congr 1
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    show ((cellBernoulli ((j : ℝ)) x : ℝ) : ℂ) * f'' x = ((bernoulliHalfPer x : ℝ) : ℂ) * f'' x
    rw [bernoulliHalfPer_eq_cellBernoulli_natCast hx]
  have hcast : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) = ((j : ℕ) : ℝ) + 1 := by
    intro j; push_cast; ring
  have hadd1 := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => ((j : ℕ) : ℝ)) (f := f) (n := N)
    (fun j _ => by rw [hcast j]; exact hfi j)
  have hadd2 := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => ((j : ℕ) : ℝ))
    (f := fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) * f'' x) (n := N)
    (fun j _ => by rw [hcast j]; exact hkercont j)
  have hzero : ((0 : ℕ) : ℝ) = 0 := by norm_num
  rw [hzero] at hadd1 hadd2
  have hsumcell : (∑ j ∈ Finset.range N,
      ((f ((j : ℝ) + 1) + f (j : ℝ)) / 2 - ∫ x in ((j : ℝ))..((j : ℝ) + 1), f x))
      = ∑ j ∈ Finset.range N,
        -∫ x in ((j : ℝ))..((j : ℝ) + 1), ((bernoulliHalfPer x : ℝ) : ℂ) * f'' x :=
    Finset.sum_congr rfl hcell
  rw [Finset.sum_sub_distrib, sum_trapezoid_complex f N] at hsumcell
  rw [Finset.sum_neg_distrib] at hsumcell
  have hrw1 : (∑ j ∈ Finset.range N, ∫ x in ((j : ℝ))..((j : ℝ) + 1), f x)
      = ∫ x in (0 : ℝ)..(N : ℝ), f x := by
    rw [← hadd1]
    exact Finset.sum_congr rfl fun j _ => by rw [hcast j]
  have hrw2 : (∑ j ∈ Finset.range N,
      ∫ x in ((j : ℝ))..((j : ℝ) + 1), ((bernoulliHalfPer x : ℝ) : ℂ) * f'' x)
      = ∫ x in (0 : ℝ)..(N : ℝ), ((bernoulliHalfPer x : ℝ) : ℂ) * f'' x := by
    rw [← hadd2]
    exact Finset.sum_congr rfl fun j _ => by rw [hcast j]
  rw [hrw1, hrw2] at hsumcell
  linear_combination hsumcell

/-- **Second-order Euler–Maclaurin, real form.** -/
theorem euler_maclaurin_second_order_real {f f' f'' : ℝ → ℝ} (N : ℕ)
    (hf : ∀ x ∈ Ici (0 : ℝ), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ici (0 : ℝ), HasDerivAt f' (f'' x) x)
    (hf''c : ContinuousOn f'' (Ici (0 : ℝ))) :
    (∑ m ∈ Finset.range (N + 1), f (m : ℝ))
      = (∫ x in (0 : ℝ)..(N : ℝ), f x) + (f 0 + f (N : ℝ)) / 2
        - ∫ x in (0 : ℝ)..(N : ℝ), bernoulliHalfPer x * f'' x := by
  have hC := euler_maclaurin_second_order (f := fun x => ((f x : ℝ) : ℂ))
    (f' := fun x => ((f' x : ℝ) : ℂ)) (f'' := fun x => ((f'' x : ℝ) : ℂ)) N
    (fun x hx => (hf x hx).ofReal_comp) (fun x hx => (hf' x hx).ofReal_comp)
    (continuous_ofReal.comp_continuousOn hf''c)
  have h1 : (∑ m ∈ Finset.range (N + 1), ((f (m : ℝ) : ℝ) : ℂ))
      = ((∑ m ∈ Finset.range (N + 1), f (m : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  have h2 : (∫ x in (0 : ℝ)..(N : ℝ), ((f x : ℝ) : ℂ))
      = ((∫ x in (0 : ℝ)..(N : ℝ), f x : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  have h3 : (∫ x in (0 : ℝ)..(N : ℝ), ((bernoulliHalfPer x : ℝ) : ℂ) * ((f'' x : ℝ) : ℂ))
      = ((∫ x in (0 : ℝ)..(N : ℝ), bernoulliHalfPer x * f'' x : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x _ => ?_
    push_cast
    ring
  rw [h1, h2, h3] at hC
  have hfinal : ((∑ m ∈ Finset.range (N + 1), f (m : ℝ) : ℝ) : ℂ)
      = (((∫ x in (0 : ℝ)..(N : ℝ), f x) + (f 0 + f (N : ℝ)) / 2
          - ∫ x in (0 : ℝ)..(N : ℝ), bernoulliHalfPer x * f'' x : ℝ) : ℂ) := by
    rw [hC]
    push_cast
    ring
  exact_mod_cast hfinal

end

end GaloisForLFunctions.HTGeometry
