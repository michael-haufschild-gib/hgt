import Mathlib

/-!
# The orbit of a phase system

A *phase system* is a finite family of steps `ℓ_i` with nonnegative weights `a_i`. Time `t` moves the
point `ω_t = (e^{−itℓ_i})_i` along a one-parameter subgroup of the torus. For the integers the steps are
`log p`, the orbit is `p^{−it}`, and the weights are chosen by the question.

The *column sum* `P(t) = Σ a_i cos(tℓ_i)` is positive definite on the time axis, and the *defect*
`D(t) = S − P(t) = Σ a_i (1 − cos(tℓ_i))` is half a squared Hilbert distance from `ω_0 = 1`. Because the
orbit is a group, this distance is translation invariant:

* **Group closure** (`sqrt_defect_add_le`, `defect_nat_mul_le`). `√D` is subadditive, so
  `D(nt) ≤ n² D(t)`. This is the pretentious triangle inequality.
* **Transport** (`column_sub_sq_le`). `|P(t) − P(s)|² ≤ 2 S D(t − s)`: a return moves every value by
  little.
* **Corners** (`defect_two_mul_le_antiDefect`, `two_mul_column_sq_le`, `three_four_one`). Doubling
  `ω ↦ ω²` sends both corners `±1` to `+1`: a visit near `−1` at time `t` is a visit near `+1` at time
  `2t`. The inequality `3 + 4cos + cos 2 ≥ 0` is this statement on the orbit.
* **Halász–Montgomery** (`sq_sum_column_le`). Large values at `N` heights force the column to be large
  on the differences of those heights, on average.
-/

open Finset Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- Steps and nonnegative weights on an index set. -/
structure PhaseSystem (ι : Type*) where
  /-- The step `ℓ_i`; for the integers `log p`. -/
  step : ι → ℝ
  /-- The weight `a_i`. -/
  weight : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i

/-- The chord `|e^{ix} − 1| = 2|sin(x/2)|`. -/
def chord (x : ℝ) : ℝ := 2 * |sin (x / 2)|

theorem chord_nonneg (x : ℝ) : 0 ≤ chord x := by unfold chord; positivity

theorem chord_le_two (x : ℝ) : chord x ≤ 2 := by
  unfold chord
  have := abs_sin_le_one (x / 2)
  linarith

theorem one_sub_cos_eq_chord_sq (x : ℝ) : 1 - cos x = chord x ^ 2 / 2 := by
  unfold chord
  have h : cos x = 1 - 2 * sin (x / 2) ^ 2 := by
    have := cos_sq' (x / 2)
    have h2 := cos_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h2
    rw [h2, this]
    ring
  rw [mul_pow, sq_abs, h]
  ring

/-- The chord is subadditive: `|e^{i(x+y)} − 1| ≤ |e^{ix} − 1| + |e^{iy} − 1|`. -/
theorem chord_add_le (x y : ℝ) : chord (x + y) ≤ chord x + chord y := by
  unfold chord
  have e : (x + y) / 2 = x / 2 + y / 2 := by ring
  rw [e, sin_add, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc
    |sin (x / 2) * cos (y / 2) + cos (x / 2) * sin (y / 2)|
        ≤ |sin (x / 2) * cos (y / 2)| + |cos (x / 2) * sin (y / 2)| := abs_add_le _ _
    _ = |sin (x / 2)| * |cos (y / 2)| + |cos (x / 2)| * |sin (y / 2)| := by
        rw [abs_mul, abs_mul]
    _ ≤ |sin (x / 2)| * 1 + 1 * |sin (y / 2)| := by
        gcongr
        · exact abs_cos_le_one _
        · exact abs_cos_le_one _
    _ = |sin (x / 2)| + |sin (y / 2)| := by ring

theorem chord_neg (x : ℝ) : chord (-x) = chord x := by
  unfold chord
  rw [neg_div, sin_neg, abs_neg]

/-- `|cos x − cos y| ≤ |e^{i(x−y)} − 1|`. -/
theorem abs_cos_sub_cos_le_chord (x y : ℝ) : |cos x - cos y| ≤ chord (x - y) := by
  unfold chord
  rw [cos_sub_cos, abs_mul, abs_mul]
  have h1 := abs_sin_le_one ((x + y) / 2)
  have h2 := abs_nonneg (sin ((x - y) / 2))
  have h3 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h3]
  nlinarith

/-- Weighted Cauchy–Schwarz: `(Σ a x)² ≤ (Σ a)(Σ a x²)`. -/
theorem sq_sum_mul_le {ι : Type*} (s : Finset ι) (a x : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i * x i) ^ 2 ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, a i * x i ^ 2 := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s ha
    (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _)) (fun i _ => le_of_eq (by ring))

/-- Minkowski in a weighted `ℓ²`. -/
theorem sqrt_sum_mul_add_sq_le {ι : Type*} (s : Finset ι) (a x y : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    √(∑ i ∈ s, a i * (x i + y i) ^ 2) ≤
      √(∑ i ∈ s, a i * x i ^ 2) + √(∑ i ∈ s, a i * y i ^ 2) := by
  set A := ∑ i ∈ s, a i * x i ^ 2
  set B := ∑ i ∈ s, a i * y i ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (sq_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (sq_nonneg _)
  have hC : (∑ i ∈ s, a i * (x i * y i)) ^ 2 ≤ A * B := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))
      (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _)) (fun i _ => le_of_eq (by ring))
  have hC' : ∑ i ∈ s, a i * (x i * y i) ≤ √A * √B := by
    rw [← Real.sqrt_mul hA]
    exact Real.le_sqrt_of_sq_le hC
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have e : ∑ i ∈ s, a i * (x i + y i) ^ 2 = A + 2 * ∑ i ∈ s, a i * (x i * y i) + B := by
    simp only [A, B, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  nlinarith

namespace PhaseSystem

variable {ι : Type*} [Fintype ι] (S : PhaseSystem ι)

/-- The size `S = Σ a_i`. -/
def size : ℝ := ∑ i, S.weight i

/-- The column sum `P(t) = Σ a_i cos(tℓ_i)`. -/
def column (t : ℝ) : ℝ := ∑ i, S.weight i * cos (t * S.step i)

/-- The defect `D(t) = S − P(t)`, the deficit from the start of the orbit. -/
def defect (t : ℝ) : ℝ := S.size - S.column t

/-- The anti-defect `S + P(t)`, the deficit from the corner `−1`. -/
def antiDefect (t : ℝ) : ℝ := S.size + S.column t

/-- The point of the orbit at time `t`. -/
def orbit (t : ℝ) (i : ι) : Circle := Circle.exp (-(t * S.step i))

omit [Fintype ι] in
/-- The orbit is a one-parameter subgroup. -/
theorem orbit_add (t u : ℝ) (i : ι) : S.orbit (t + u) i = S.orbit t i * S.orbit u i := by
  unfold orbit
  rw [← Circle.exp_add]
  congr 1
  ring

omit [Fintype ι] in
theorem orbit_zero (i : ι) : S.orbit 0 i = 1 := by
  simp [orbit]

/-- The column sum is read from the orbit. -/
theorem column_eq_sum_re_orbit (t : ℝ) :
    S.column t = ∑ i, S.weight i * ((S.orbit t i : ℂ)).re := by
  unfold column orbit
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, cos_neg]

theorem size_nonneg : 0 ≤ S.size := Finset.sum_nonneg fun i _ => S.weight_nonneg i

theorem defect_eq_sum (t : ℝ) : S.defect t = ∑ i, S.weight i * (1 - cos (t * S.step i)) := by
  unfold defect size column
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem antiDefect_eq_sum (t : ℝ) :
    S.antiDefect t = ∑ i, S.weight i * (1 + cos (t * S.step i)) := by
  unfold antiDefect size column
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem defect_nonneg (t : ℝ) : 0 ≤ S.defect t := by
  rw [defect_eq_sum]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (S.weight_nonneg i) (by linarith [cos_le_one (t * S.step i)])

theorem antiDefect_nonneg (t : ℝ) : 0 ≤ S.antiDefect t := by
  rw [antiDefect_eq_sum]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (S.weight_nonneg i) (by linarith [neg_one_le_cos (t * S.step i)])

theorem column_le_size (t : ℝ) : S.column t ≤ S.size := by
  have := S.defect_nonneg t
  unfold defect at this
  linarith

theorem neg_size_le_column (t : ℝ) : -S.size ≤ S.column t := by
  have := S.antiDefect_nonneg t
  unfold antiDefect at this
  linarith

@[simp] theorem column_zero : S.column 0 = S.size := by simp [column, size]

@[simp] theorem defect_zero : S.defect 0 = 0 := by simp [defect]

theorem column_neg (t : ℝ) : S.column (-t) = S.column t := by
  unfold column
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_mul, cos_neg]

theorem defect_neg (t : ℝ) : S.defect (-t) = S.defect t := by
  unfold defect
  rw [column_neg]

theorem defect_eq_sum_chord (t : ℝ) :
    S.defect t = (∑ i, S.weight i * chord (t * S.step i) ^ 2) / 2 := by
  rw [defect_eq_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_sub_cos_eq_chord_sq]
  ring

/-- **Group closure.** The root of the defect is subadditive in time. -/
theorem sqrt_defect_add_le (t u : ℝ) : √(S.defect (t + u)) ≤ √(S.defect t) + √(S.defect u) := by
  have hle : ∑ i, S.weight i * chord ((t + u) * S.step i) ^ 2 ≤
      ∑ i, S.weight i * (chord (t * S.step i) + chord (u * S.step i)) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (S.weight_nonneg i)
    rw [add_mul]
    exact pow_le_pow_left₀ (chord_nonneg _) (chord_add_le _ _) 2
  have hM := sqrt_sum_mul_add_sq_le Finset.univ S.weight (fun i => chord (t * S.step i))
    (fun i => chord (u * S.step i)) (fun i _ => S.weight_nonneg i)
  rw [defect_eq_sum_chord, defect_eq_sum_chord, defect_eq_sum_chord,
    Real.sqrt_div' _ (by norm_num), Real.sqrt_div' _ (by norm_num), Real.sqrt_div' _ (by norm_num),
    ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  exact (Real.sqrt_le_sqrt hle).trans hM

/-- Multiples of a return are returns, with the root of the defect growing linearly. -/
theorem sqrt_defect_nat_mul_le (n : ℕ) (t : ℝ) : √(S.defect (n * t)) ≤ n * √(S.defect t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ((n + 1 : ℕ) : ℝ) * t = n * t + t := by push_cast; ring
    rw [e]
    have := S.sqrt_defect_add_le (n * t) t
    push_cast
    linarith

/-- `D(nt) ≤ n² D(t)`. -/
theorem defect_nat_mul_le (n : ℕ) (t : ℝ) : S.defect (n * t) ≤ n ^ 2 * S.defect t := by
  have h := S.sqrt_defect_nat_mul_le n t
  have h0 := Real.sqrt_nonneg (S.defect (n * t))
  have := pow_le_pow_left₀ h0 h 2
  rw [Real.sq_sqrt (S.defect_nonneg _), mul_pow, Real.sq_sqrt (S.defect_nonneg _)] at this
  exact this

/-- **Transport.** A return moves every value of the column by little. -/
theorem column_sub_sq_le (t s : ℝ) : (S.column t - S.column s) ^ 2 ≤ 2 * S.size * S.defect (t - s) := by
  have hb : |S.column t - S.column s| ≤ ∑ i, S.weight i * chord ((t - s) * S.step i) := by
    unfold column
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← mul_sub, abs_mul, abs_of_nonneg (S.weight_nonneg i), sub_mul]
    exact mul_le_mul_of_nonneg_left (abs_cos_sub_cos_le_chord _ _) (S.weight_nonneg i)
  have hc := sq_sum_mul_le Finset.univ S.weight (fun i => chord ((t - s) * S.step i))
    (fun i _ => S.weight_nonneg i)
  have hd : ∑ i, S.weight i * chord ((t - s) * S.step i) ^ 2 = 2 * S.defect (t - s) := by
    rw [defect_eq_sum_chord]
    ring
  rw [hd] at hc
  have h0 : 0 ≤ ∑ i, S.weight i * chord ((t - s) * S.step i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (S.weight_nonneg i) (chord_nonneg _)
  calc
    (S.column t - S.column s) ^ 2 = |S.column t - S.column s| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ i, S.weight i * chord ((t - s) * S.step i)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ ≤ S.size * (2 * S.defect (t - s)) := hc
    _ = 2 * S.size * S.defect (t - s) := by ring

/-- **Corners.** A visit near `−1` at time `t` is a visit near `+1` at time `2t`. -/
theorem defect_two_mul_le_antiDefect (t : ℝ) : S.defect (2 * t) ≤ 4 * S.antiDefect t := by
  rw [defect_eq_sum, antiDefect_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hw := S.weight_nonneg i
  have e : cos (2 * t * S.step i) = 2 * cos (t * S.step i) ^ 2 - 1 := by
    rw [show 2 * t * S.step i = 2 * (t * S.step i) by ring, cos_two_mul]
  rw [e]
  have h1 := cos_le_one (t * S.step i)
  have h2 := neg_one_le_cos (t * S.step i)
  have : 1 - (2 * cos (t * S.step i) ^ 2 - 1) ≤ 4 * (1 + cos (t * S.step i)) := by nlinarith
  nlinarith

/-- The Cauchy form of doubling: `2 P(t)² ≤ S (S + P(2t))`. -/
theorem two_mul_column_sq_le (t : ℝ) : 2 * S.column t ^ 2 ≤ S.size * S.antiDefect (2 * t) := by
  have hc := sq_sum_mul_le Finset.univ S.weight (fun i => cos (t * S.step i))
    (fun i _ => S.weight_nonneg i)
  have e : S.antiDefect (2 * t) = 2 * ∑ i, S.weight i * cos (t * S.step i) ^ 2 := by
    rw [antiDefect_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show 2 * t * S.step i = 2 * (t * S.step i) by ring, cos_two_mul]
    ring
  rw [e]
  unfold column size at *
  linarith

/-- `3 + 4 cos + cos 2 ≥ 0` on the orbit. -/
theorem three_four_one (t : ℝ) : 0 ≤ 3 * S.size + 4 * S.column t + S.column (2 * t) := by
  have e : 3 * S.size + 4 * S.column t + S.column (2 * t) =
      ∑ i, S.weight i * (2 * (1 + cos (t * S.step i)) ^ 2) := by
    unfold size column
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show 2 * t * S.step i = 2 * (t * S.step i) by ring, cos_two_mul]
    ring
  rw [e]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (S.weight_nonneg i) (by positivity)

/-- **Halász–Montgomery on the orbit.** `(Σ_{t∈A} P(t))² ≤ S Σ_{t,u∈A} P(t − u)`. -/
theorem sq_sum_column_le (A : Finset ℝ) :
    (∑ t ∈ A, S.column t) ^ 2 ≤ S.size * ∑ t ∈ A, ∑ u ∈ A, S.column (t - u) := by
  set C : ι → ℝ := fun i => ∑ t ∈ A, cos (t * S.step i) with hC
  set D : ι → ℝ := fun i => ∑ t ∈ A, sin (t * S.step i) with hD
  have h1 : ∑ t ∈ A, S.column t = ∑ i, S.weight i * C i := by
    unfold column
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hC, Finset.mul_sum]
  have h2 : ∑ t ∈ A, ∑ u ∈ A, S.column (t - u) = ∑ i, S.weight i * (C i ^ 2 + D i ^ 2) := by
    have e : ∀ t u : ℝ, S.column (t - u) = ∑ i, S.weight i *
        (cos (t * S.step i) * cos (u * S.step i) + sin (t * S.step i) * sin (u * S.step i)) := by
      intro t u
      unfold column
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_mul, cos_sub]
    have key : ∀ i, ∑ t ∈ A, ∑ u ∈ A, S.weight i *
        (cos (t * S.step i) * cos (u * S.step i) + sin (t * S.step i) * sin (u * S.step i)) =
        S.weight i * (C i ^ 2 + D i ^ 2) := by
      intro i
      have hc : C i ^ 2 = ∑ t ∈ A, ∑ u ∈ A, cos (t * S.step i) * cos (u * S.step i) := by
        rw [sq, hC]
        exact Finset.sum_mul_sum _ _ _ _
      have hd : D i ^ 2 = ∑ t ∈ A, ∑ u ∈ A, sin (t * S.step i) * sin (u * S.step i) := by
        rw [sq, hD]
        exact Finset.sum_mul_sum _ _ _ _
      rw [hc, hd, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    simp_rw [e]
    calc
      ∑ t ∈ A, ∑ u ∈ A, ∑ i, S.weight i *
          (cos (t * S.step i) * cos (u * S.step i) + sin (t * S.step i) * sin (u * S.step i))
          = ∑ t ∈ A, ∑ i, ∑ u ∈ A, S.weight i *
          (cos (t * S.step i) * cos (u * S.step i) + sin (t * S.step i) * sin (u * S.step i)) :=
            Finset.sum_congr rfl fun t _ => Finset.sum_comm
      _ = ∑ i, ∑ t ∈ A, ∑ u ∈ A, S.weight i *
          (cos (t * S.step i) * cos (u * S.step i) + sin (t * S.step i) * sin (u * S.step i)) :=
            Finset.sum_comm
      _ = ∑ i, S.weight i * (C i ^ 2 + D i ^ 2) := Finset.sum_congr rfl fun i _ => key i
  rw [h1, h2]
  have hc := sq_sum_mul_le Finset.univ S.weight C (fun i _ => S.weight_nonneg i)
  refine hc.trans (mul_le_mul_of_nonneg_left ?_ S.size_nonneg)
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (S.weight_nonneg i)
  nlinarith [sq_nonneg (D i)]

end PhaseSystem

end

end GaloisForLFunctions.PrimeTorusTheory
