import Mathlib

/-!
# Even positive-definite functions on an additive group

A real function `φ` on an additive commutative group `G` is positive definite when every Gram form
`Σᵢ Σⱼ cᵢ cⱼ φ(xᵢ − xⱼ)` with real coefficients is nonnegative. Real coefficients only see the even
part of `φ`; the boundary divisors of this programme are even, so the theory is stated for even
positive-definite functions.

* `abs_le_apply_zero`: `|φ u| ≤ φ 0`.
* `apply_add_of_eq` / `apply_add_of_eq_neg`: if `φ h = ± φ 0` then `φ (h + u) = ± φ u`.
* Integer-valued classification: if `φ 0 = 1` and `φ` is integer valued, then `φ` takes values in
  `{-1, 0, 1}`, its nonvanishing set is a subgroup, and on that subgroup `φ` is a `±1` character
  (`intValued_mul`, `nonvanishingSubgroup`).
* `progression_gram`: along a progression `r • h` the Fejér Gram vector gives
  `0 ≤ N φ 0 + 2 Σ_{r<N} (N − (r+1)) φ((r+1) • h)`.
* `progression_mass_le`: if `φ (r • h) ≤ 0` for every `r ≥ 1`, the total mass `Σ_{r ≥ 1} −φ(r • h)`
  is at most `φ 0 / 2`.
* Positive multiples and pointwise limits of even positive-definite functions are even positive
  definite.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

variable {G : Type*} [AddCommGroup G]

/-- Real-coefficient positive definiteness on an additive group. -/
def IsPosDef (φ : G → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, c i * c j * φ (x i - x j)

/-- An even real-coefficient positive-definite function. -/
structure IsEvenPosDef (φ : G → ℝ) : Prop where
  even : ∀ u, φ (-u) = φ u
  posDef : IsPosDef φ

namespace IsEvenPosDef

variable {φ : G → ℝ}

/-- Two-point Gram form at `0` and `h`. -/
theorem two_point (hφ : IsEvenPosDef φ) (h : G) (a b : ℝ) :
    0 ≤ (a ^ 2 + b ^ 2) * φ 0 + 2 * a * b * φ h := by
  have := hφ.posDef 2 ![0, h] ![a, b]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, zero_sub,
    sub_zero, hφ.even] at this
  nlinarith [this]

theorem apply_zero_nonneg (hφ : IsEvenPosDef φ) : 0 ≤ φ 0 := by
  have := hφ.two_point 0 1 0
  simpa using this

/-- A positive-definite function is bounded by its value at the origin. -/
theorem abs_le_apply_zero (hφ : IsEvenPosDef φ) (u : G) : |φ u| ≤ φ 0 := by
  have h1 := hφ.two_point u 1 1
  have h2 := hφ.two_point u 1 (-1)
  rw [abs_le]
  constructor <;> nlinarith [h1, h2]

/-- Three-point Gram form at `0`, `h` and `-u`. -/
theorem three_point (hφ : IsEvenPosDef φ) (h u : G) (a b c : ℝ) :
    0 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * φ 0 + 2 * a * b * φ h + 2 * a * c * φ u +
      2 * b * c * φ (h + u) := by
  have := hφ.posDef 3 ![0, h, -u] ![a, b, c]
  have e1 : (-u : G) - h = -(h + u) := by abel
  have e2 : h - -u = h + u := sub_neg_eq_add h u
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, sub_self, zero_sub, sub_zero, neg_neg, e1, e2,
    hφ.even] at this
  nlinarith [this]

/-- If `φ h = φ 0`, translation by `h` fixes `φ`. -/
theorem apply_add_of_eq (hφ : IsEvenPosDef φ) {h : G} (hh : φ h = φ 0) (u : G) :
    φ (h + u) = φ u := by
  have h0 := hφ.apply_zero_nonneg
  rcases h0.eq_or_lt with h00 | h0pos
  · have hu := hφ.abs_le_apply_zero u
    have hhu := hφ.abs_le_apply_zero (h + u)
    rw [← h00] at hu hhu
    rw [abs_nonpos_iff.mp hu, abs_nonpos_iff.mp hhu]
  · set x := φ u - φ (h + u)
    have key := hφ.three_point h u (φ 0) (-φ 0) (-x)
    rw [hh] at key
    have hx : φ 0 * x ^ 2 ≤ 0 := by nlinarith [key]
    have : x ^ 2 ≤ 0 := by nlinarith [hx, h0pos]
    have hx0 : x = 0 := by nlinarith [sq_nonneg x]
    linarith [hx0]

/-- If `φ h = -φ 0`, translation by `h` negates `φ`. -/
theorem apply_add_of_eq_neg (hφ : IsEvenPosDef φ) {h : G} (hh : φ h = -φ 0) (u : G) :
    φ (h + u) = -φ u := by
  have h0 := hφ.apply_zero_nonneg
  rcases h0.eq_or_lt with h00 | h0pos
  · have hu := hφ.abs_le_apply_zero u
    have hhu := hφ.abs_le_apply_zero (h + u)
    rw [← h00] at hu hhu
    rw [abs_nonpos_iff.mp hu, abs_nonpos_iff.mp hhu, neg_zero]
  · set y := φ u + φ (h + u)
    have key := hφ.three_point h u (φ 0) (φ 0) (-y)
    rw [hh] at key
    have hy : φ 0 * y ^ 2 ≤ 0 := by nlinarith [key]
    have : y ^ 2 ≤ 0 := by nlinarith [hy, h0pos]
    have hy0 : y = 0 := by nlinarith [sq_nonneg y]
    linarith [hy0]

/-- Positive multiples stay positive definite. -/
theorem smul (hφ : IsEvenPosDef φ) {a : ℝ} (ha : 0 ≤ a) : IsEvenPosDef (fun u => a * φ u) where
  even u := by rw [hφ.even]
  posDef n x c := by
    have := hφ.posDef n x c
    have h : ∑ i, ∑ j, c i * c j * (a * φ (x i - x j)) =
        a * ∑ i, ∑ j, c i * c j * φ (x i - x j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h]
    exact mul_nonneg ha this

end IsEvenPosDef

/-- Pointwise limits of even positive-definite functions are even positive definite. -/
theorem isEvenPosDef_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → G → ℝ}
    {φ : G → ℝ} (hF : ∀ᶠ i in l, IsEvenPosDef (F i))
    (hlim : ∀ u, Tendsto (fun i => F i u) l (𝓝 (φ u))) : IsEvenPosDef φ where
  even u := by
    refine tendsto_nhds_unique ?_ (hlim u)
    refine (hlim (-u)).congr' ?_
    filter_upwards [hF] with i hi
    exact hi.even u
  posDef n x c := by
    have hT : Tendsto (fun i => ∑ a, ∑ b, c a * c b * F i (x a - x b)) l
        (𝓝 (∑ a, ∑ b, c a * c b * φ (x a - x b))) :=
      tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
        (hlim (x a - x b)).const_mul _
    refine ge_of_tendsto hT ?_
    filter_upwards [hF] with i hi
    exact hi.posDef n x c

/-! ### Integer-valued positive-definite functions -/

section IntValued

variable {φ : G → ℝ}

/-- An integer-valued even positive-definite function with `φ 0 = 1` takes values in `{-1,0,1}`. -/
theorem intValued_values (hφ : IsEvenPosDef φ) (h0 : φ 0 = 1) (hint : ∀ u, ∃ n : ℤ, φ u = n)
    (u : G) : φ u = -1 ∨ φ u = 0 ∨ φ u = 1 := by
  obtain ⟨n, hn⟩ := hint u
  have hb := hφ.abs_le_apply_zero u
  rw [h0, hn] at hb
  have hb' : |n| ≤ 1 := by exact_mod_cast hb
  rcases abs_le.mp hb' with ⟨hl, hr⟩
  interval_cases n <;> simp [hn]

/-- On the nonvanishing set, an integer-valued `φ` with `φ 0 = 1` is multiplicative. -/
theorem intValued_mul (hφ : IsEvenPosDef φ) (h0 : φ 0 = 1) (hint : ∀ u, ∃ n : ℤ, φ u = n)
    {h : G} (hh : φ h ≠ 0) (u : G) : φ (h + u) = φ h * φ u := by
  rcases intValued_values hφ h0 hint h with h1 | h1 | h1
  · rw [hφ.apply_add_of_eq_neg (by rw [h1, h0]) u, h1]
    ring
  · exact absurd h1 hh
  · rw [hφ.apply_add_of_eq (by rw [h1, h0]) u, h1, one_mul]

/-- The nonvanishing set of an integer-valued even positive-definite `φ` with `φ 0 = 1` is a
subgroup; on it `φ` is a `±1` character (`intValued_mul`). -/
def nonvanishingSubgroup (hφ : IsEvenPosDef φ) (h0 : φ 0 = 1)
    (hint : ∀ u, ∃ n : ℤ, φ u = n) : AddSubgroup G where
  carrier := {u | φ u ≠ 0}
  zero_mem' := by simp [h0]
  add_mem' {a b} ha hb := by
    change φ (a + b) ≠ 0
    rw [intValued_mul hφ h0 hint ha b]
    exact mul_ne_zero ha hb
  neg_mem' {a} ha := by
    change φ (-a) ≠ 0
    rw [hφ.even]
    exact ha

theorem mem_nonvanishingSubgroup (hφ : IsEvenPosDef φ) (h0 : φ 0 = 1)
    (hint : ∀ u, ∃ n : ℤ, φ u = n) (u : G) :
    u ∈ nonvanishingSubgroup hφ h0 hint ↔ φ u ≠ 0 := Iff.rfl

/-- A boundary zero `φ h = -1` forces the value `1` at `2h`. -/
theorem intValued_double (hφ : IsEvenPosDef φ) (h0 : φ 0 = 1) (hint : ∀ u, ∃ n : ℤ, φ u = n)
    {h : G} (hh : φ h = -1) : φ (h + h) = 1 := by
  rw [intValued_mul hφ h0 hint (by rw [hh]; norm_num) h, hh]
  norm_num

/-- If `φ 0 = 1`, `φ` is integer valued and nonpositive away from `0`, and `G` has no
`2`-torsion, then `φ` is the indicator of `{0}`. -/
theorem intValued_eq_zero_of_nonpos (hφ : IsEvenPosDef φ) (h0 : φ 0 = 1)
    (hint : ∀ u, ∃ n : ℤ, φ u = n) (hnp : ∀ u, u ≠ 0 → φ u ≤ 0)
    (htor : ∀ u : G, u + u = 0 → u = 0) {u : G} (hu : u ≠ 0) : φ u = 0 := by
  rcases intValued_values hφ h0 hint u with h1 | h1 | h1
  · have h2 := intValued_double hφ h0 hint h1
    have hne : u + u ≠ 0 := fun h => hu (htor u h)
    have := hnp (u + u) hne
    linarith
  · exact h1
  · have := hnp u hu
    linarith

end IntValued

/-! ### Progressions -/

/-- The Fejér double-sum identity: for an even `g : ℤ → ℝ`,
`Σ_{i<N} Σ_{j<N} g(i − j) = N g 0 + 2 Σ_{r<N} (N − (r+1)) g(r+1)`. -/
theorem sum_range_sum_range_sub (g : ℤ → ℝ) (hg : ∀ z, g (-z) = g z) (N : ℕ) :
    ∑ i ∈ range N, ∑ j ∈ range N, g ((i : ℤ) - j) =
      N * g 0 + 2 * ∑ r ∈ range N, ((N : ℝ) - (r + 1)) * g ((r : ℤ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hrefl : ∑ j ∈ range N, g ((N : ℤ) - j) = ∑ r ∈ range N, g ((r : ℤ) + 1) := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < N := Finset.mem_range.mp hj
      congr 1
      omega
    have hcol : ∑ i ∈ range N, g ((i : ℤ) - N) = ∑ r ∈ range N, g ((r : ℤ) + 1) := by
      rw [← hrefl]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hg]
      congr 1
      ring
    have hsplit : ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), g ((i : ℤ) - j) =
        ∑ i ∈ range N, ∑ j ∈ range N, g ((i : ℤ) - j) + ∑ i ∈ range N, g ((i : ℤ) - N) +
          ∑ j ∈ range N, g ((N : ℤ) - j) + g 0 := by
      rw [Finset.sum_range_succ]
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib, sub_self]
      ring
    rw [hsplit, ih, hrefl, hcol]
    have hcoef : ∑ r ∈ range (N + 1), (((N + 1 : ℕ) : ℝ) - (r + 1)) * g ((r : ℤ) + 1) =
        ∑ r ∈ range N, ((N : ℝ) - (r + 1)) * g ((r : ℤ) + 1) +
          ∑ r ∈ range N, g ((r : ℤ) + 1) := by
      rw [Finset.sum_range_succ, ← Finset.sum_add_distrib]
      push_cast
      simp only [sub_self, zero_mul, add_zero]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [hcoef]
    push_cast
    ring

namespace IsEvenPosDef

variable {φ : G → ℝ}

/-- The Fejér Gram inequality along the progression `r • h`. -/
theorem progression_gram (hφ : IsEvenPosDef φ) (h : G) (N : ℕ) :
    0 ≤ N * φ 0 + 2 * ∑ r ∈ range N, ((N : ℝ) - (r + 1)) * φ ((r + 1) • h) := by
  set g : ℤ → ℝ := fun z => φ (z • h) with hgdef
  have hg : ∀ z, g (-z) = g z := fun z => by simp only [hgdef, neg_zsmul, hφ.even]
  have hpd := hφ.posDef N (fun i => ((i : ℕ) : ℤ) • h) (fun _ => 1)
  simp only [one_mul] at hpd
  have hconv : ∑ i : Fin N, ∑ j : Fin N, φ (((i : ℕ) : ℤ) • h - ((j : ℕ) : ℤ) • h) =
      ∑ i ∈ range N, ∑ j ∈ range N, g ((i : ℤ) - j) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin N, φ (((i : ℕ) : ℤ) • h -
      ((j : ℕ) : ℤ) • h))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun j => φ ((i : ℤ) • h - (j : ℤ) • h))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hgdef]
    rw [sub_zsmul, sub_eq_add_neg]
  rw [hconv, sum_range_sum_range_sub g hg] at hpd
  have e0 : g 0 = φ 0 := by simp [hgdef]
  have hsum : ∑ r ∈ range N, ((N : ℝ) - (r + 1)) * g ((r : ℤ) + 1) =
      ∑ r ∈ range N, ((N : ℝ) - (r + 1)) * φ ((r + 1) • h) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hgdef]
    rw [show ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) by push_cast; ring, natCast_zsmul]
  rw [e0, hsum] at hpd
  exact hpd

/-- **Progression mass law.** If `φ` is nonpositive along `h, 2h, 3h, …`, the total mass of
`−φ` on any initial segment of the progression is at most `φ 0 / 2`. -/
theorem progression_mass_le (hφ : IsEvenPosDef φ) (h : G)
    (hneg : ∀ r : ℕ, φ ((r + 1) • h) ≤ 0) (R : ℕ) :
    ∑ r ∈ range R, -φ ((r + 1) • h) ≤ φ 0 / 2 := by
  set M := ∑ r ∈ range R, -φ ((r + 1) • h)
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun r _ => by linarith [hneg r]
  by_contra hlt
  push Not at hlt
  have hgap : 0 < M - φ 0 / 2 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (R * M / (M - φ 0 / 2) + R)
  have hNR : (R : ℝ) < N := by
    have : 0 ≤ R * M / (M - φ 0 / 2) := div_nonneg (by positivity) hgap.le
    linarith
  have hgram := hφ.progression_gram h N
  have hRN : R ≤ N := by exact_mod_cast hNR.le
  -- Only the first `R` terms are kept; each kept coefficient is at least `N − R`.
  have hdrop : ∑ r ∈ range N, ((N : ℝ) - (r + 1)) * φ ((r + 1) • h) ≤
      ∑ r ∈ range R, ((N : ℝ) - (r + 1)) * φ ((r + 1) • h) := by
    rw [← Finset.sum_range_add_sum_Ico _ hRN]
    have : ∑ r ∈ Finset.Ico R N, ((N : ℝ) - (r + 1)) * φ ((r + 1) • h) ≤ 0 := by
      refine Finset.sum_nonpos fun r hr => ?_
      have hr' : r < N := (Finset.mem_Ico.mp hr).2
      have hc : 0 ≤ (N : ℝ) - (r + 1) := by
        have : (r : ℝ) + 1 ≤ N := by exact_mod_cast hr'
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos hc (hneg r)
    linarith
  have hkeep : ∑ r ∈ range R, ((N : ℝ) - (r + 1)) * φ ((r + 1) • h) ≤
      ((N : ℝ) - R) * ∑ r ∈ range R, φ ((r + 1) • h) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    have hr' : r < R := Finset.mem_range.mp hr
    have hcoef : (N : ℝ) - R ≤ (N : ℝ) - (r + 1) := by
      have : (r : ℝ) + 1 ≤ R := by exact_mod_cast hr'
      linarith
    exact mul_le_mul_of_nonpos_right hcoef (hneg r)
  have hsum : ∑ r ∈ range R, φ ((r + 1) • h) = -M := by
    simp only [M, Finset.sum_neg_distrib, neg_neg]
  rw [hsum] at hkeep
  have key : ((N : ℝ) - R) * M ≤ N * φ 0 / 2 := by nlinarith [hgram, hdrop, hkeep]
  have hdiv : R * M / (M - φ 0 / 2) < N - R := by linarith
  rw [div_lt_iff₀ hgap] at hdiv
  nlinarith [hdiv, key]

end IsEvenPosDef

end GaloisForLFunctions.MultiplicativePositivityGeometry
