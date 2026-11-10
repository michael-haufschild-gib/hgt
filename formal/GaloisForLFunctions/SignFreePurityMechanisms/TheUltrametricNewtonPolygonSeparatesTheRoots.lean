import GaloisForLFunctions.SignFreePurityMechanisms.SeparationForcesRationality

/-!
# The ultrametric Newton polygon separates the roots

Let `v` be a nonarchimedean absolute value on a field `L` and `f = ∑ a_k X ^ k` a polynomial of
degree `n` whose coefficients are nonzero with strictly log-concave sizes,
`v a_j * v a_{j+2} < (v a_{j+1}) ^ 2`. The Newton polygon of `f` then has `n` sides of length one.

* At a root `z` two terms `a_k z ^ k` share the largest size, and by strict concavity they are
  consecutive: `v a_i = v a_{i+1} * v z` (`HasSimpleSlopes.exists_slope_of_isRoot`).
* On the whole sphere `v w = v z` the quotient `f / (X - z)` has one strictly largest term, so it
  has no zero there (`HasSimpleSlopes.eval_divByMonic_ne_zero`).

Hence the roots are simple and `v` is injective on them (`HasSimpleSlopes.injOn_isRoot`): a
condition on the coefficients alone produces the separation, and no quantitative gap is needed.

Over a complete ultrametric field `K` the spectral norm of an algebraic extension is such an
absolute value, and it takes the same value on conjugate elements. A polynomial over `K` with
strictly log-concave coefficient norms therefore splits over `K`
(`splits_of_strict_logConcave`). Every partial sum of the `p`-adic theta series
`∑ p ^ (k ^ 2) X ^ k` is an example (`padicTheta_splits`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.SignFreePurityMechanisms

/-! ### Strictly log-concave positive sequences -/

/-- A positive sequence on `[0, n]` with `T k * T (k + 2) < T (k + 1) ^ 2`. -/
structure IsStrictLogConcave (T : ℕ → ℝ) (n : ℕ) : Prop where
  pos : ∀ k ≤ n, 0 < T k
  concave : ∀ k, k + 2 ≤ n → T k * T (k + 2) < T (k + 1) ^ 2

namespace IsStrictLogConcave

variable {T : ℕ → ℝ} {n : ℕ}

/-- After a step that does not increase, the next step decreases strictly. -/
theorem step_down (h : IsStrictLogConcave T n) {k : ℕ} (hk : k + 2 ≤ n)
    (hle : T (k + 1) ≤ T k) : T (k + 2) < T (k + 1) := by
  have h2 : T (k + 1) ^ 2 ≤ T k * T (k + 1) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right hle (h.pos (k + 1) (by omega)).le
  exact lt_of_mul_lt_mul_left ((h.concave k hk).trans_le h2) (h.pos k (by omega)).le

/-- Before a step that does not decrease, the previous step increases strictly. -/
theorem step_up (h : IsStrictLogConcave T n) {k : ℕ} (hk : k + 2 ≤ n)
    (hle : T (k + 1) ≤ T (k + 2)) : T k < T (k + 1) := by
  have h2 : T (k + 1) ^ 2 ≤ T (k + 1) * T (k + 2) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_left hle (h.pos (k + 1) (by omega)).le
  exact lt_of_mul_lt_mul_right ((h.concave k hk).trans_le h2) (h.pos (k + 2) hk).le

/-- Once `T (i + 1) ≤ T i`, the sequence decreases strictly from `i + 1` on and stays below
`T i`. -/
theorem decreasing_after (h : IsStrictLogConcave T n) {i : ℕ} (hi : T (i + 1) ≤ T i) (d : ℕ)
    (hd : i + d + 2 ≤ n) : T (i + d + 2) < T (i + d + 1) ∧ T (i + d + 1) ≤ T i := by
  induction d with
  | zero => exact ⟨h.step_down hd hi, hi⟩
  | succ d ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    exact ⟨h.step_down (k := i + d + 1) hd h1.le, h1.le.trans h2⟩

theorem succ_lt_of_succ_le (h : IsStrictLogConcave T n) {i : ℕ} (hi : T (i + 1) ≤ T i) {l : ℕ}
    (hil : i + 1 ≤ l) (hl : l + 1 ≤ n) : T (l + 1) < T l := by
  obtain ⟨d, rfl⟩ : ∃ d, l = i + d + 1 := ⟨l - (i + 1), by omega⟩
  exact (h.decreasing_after hi d hl).1

theorem lt_of_succ_le (h : IsStrictLogConcave T n) {i : ℕ} (hi : T (i + 1) ≤ T i) {l : ℕ}
    (hil : i + 2 ≤ l) (hl : l ≤ n) : T l < T i := by
  obtain ⟨d, rfl⟩ : ∃ d, l = i + d + 2 := ⟨l - (i + 2), by omega⟩
  exact (h.decreasing_after hi d hl).1.trans_le (h.decreasing_after hi d hl).2

/-- Once `T i ≤ T (i + 1)`, the sequence increases strictly up to `i`. -/
theorem increasing_before (h : IsStrictLogConcave T n) {i : ℕ} (hin : i + 1 ≤ n)
    (hi : T i ≤ T (i + 1)) (d k : ℕ) (hk : k + d + 1 = i) :
    T k < T (k + 1) ∧ T (k + 1) ≤ T i := by
  induction d generalizing k with
  | zero =>
    obtain rfl : k + 1 = i := hk
    exact ⟨h.step_up hin hi, le_rfl⟩
  | succ d ih =>
    obtain ⟨h1, h2⟩ := ih (k + 1) (by omega)
    exact ⟨h.step_up (by omega) h1.le, h1.le.trans h2⟩

theorem lt_succ_of_le_succ (h : IsStrictLogConcave T n) {i : ℕ} (hin : i + 1 ≤ n)
    (hi : T i ≤ T (i + 1)) {k : ℕ} (hki : k < i) : T k < T (k + 1) := by
  obtain ⟨d, hd⟩ : ∃ d, k + d + 1 = i := ⟨i - k - 1, by omega⟩
  exact (h.increasing_before hin hi d k hd).1

theorem lt_of_le_succ (h : IsStrictLogConcave T n) {i : ℕ} (hin : i + 1 ≤ n)
    (hi : T i ≤ T (i + 1)) {k : ℕ} (hki : k < i) : T k < T i := by
  obtain ⟨d, hd⟩ : ∃ d, k + d + 1 = i := ⟨i - k - 1, by omega⟩
  exact (h.increasing_before hin hi d k hd).1.trans_le (h.increasing_before hin hi d k hd).2

end IsStrictLogConcave

/-! ### Polynomials whose Newton polygon has only sides of length one -/

section Abstract

variable {L : Type*} [Field L] {v : AbsoluteValue L ℝ} {f : L[X]}

/-- The coefficients of `f` up to the degree are nonzero and their sizes are strictly
log-concave: the Newton polygon of `f` for `v` has only sides of length one. -/
structure HasSimpleSlopes (v : AbsoluteValue L ℝ) (f : L[X]) : Prop where
  ne_zero : ∀ j ≤ f.natDegree, f.coeff j ≠ 0
  concave : ∀ j, j + 2 ≤ f.natDegree →
    v (f.coeff j) * v (f.coeff (j + 2)) < v (f.coeff (j + 1)) ^ 2

/-- The size of the term of degree `k` of `f` on the sphere of radius `r`. -/
def termSize (v : AbsoluteValue L ℝ) (f : L[X]) (r : ℝ) (k : ℕ) : ℝ :=
  v (f.coeff k) * r ^ k

theorem apply_coeff_mul_pow (v : AbsoluteValue L ℝ) (f : L[X]) (z : L) (k : ℕ) :
    v (f.coeff k * z ^ k) = termSize v f (v z) k := by
  rw [termSize, v.map_mul, v.map_pow]

theorem termSize_succ (v : AbsoluteValue L ℝ) (f : L[X]) (r : ℝ) (k : ℕ) :
    termSize v f r (k + 1) = v (f.coeff (k + 1)) * r * r ^ k := by
  rw [termSize]
  ring

/-- A nonarchimedean absolute value of a sum is the size of a strictly larger summand. -/
theorem apply_add_eq_left (hv : IsNonarchimedean v) {x y : L} (h : v y < v x) :
    v (x + y) = v x := by
  rw [IsNonarchimedean.add_eq_max_of_ne' v hv (fun a => (v.map_neg a).symm) h.ne',
    max_eq_left h.le]

/-- On every sphere the term sizes of `f` are strictly log-concave. -/
theorem HasSimpleSlopes.isStrictLogConcave (h : HasSimpleSlopes v f) {r : ℝ} (hr : 0 < r) :
    IsStrictLogConcave (termSize v f r) f.natDegree where
  pos k hk := mul_pos (v.pos (h.ne_zero k hk)) (pow_pos hr k)
  concave k hk := by
    have hlt := mul_lt_mul_of_pos_right (h.concave k hk) (pow_pos hr (2 * k + 2))
    calc termSize v f r k * termSize v f r (k + 2)
        = v (f.coeff k) * v (f.coeff (k + 2)) * r ^ (2 * k + 2) := by
          simp only [termSize]
          ring
      _ < v (f.coeff (k + 1)) ^ 2 * r ^ (2 * k + 2) := hlt
      _ = termSize v f r (k + 1) ^ 2 := by
          simp only [termSize]
          ring

theorem HasSimpleSlopes.ne_zero_of_isRoot (h : HasSimpleSlopes v f) {z : L} (hz : f.IsRoot z) :
    z ≠ 0 := by
  rintro rfl
  exact h.ne_zero 0 (Nat.zero_le _) (by rw [coeff_zero_eq_eval_zero]; exact hz)

/-- **The slopes.** At a root `z` the largest term size is attained twice, since the terms sum
to zero, and two largest terms of a strictly log-concave sequence are consecutive. Hence
`v z` is one of the ratios `v a_i / v a_{i+1}`. -/
theorem HasSimpleSlopes.exists_slope_of_isRoot (hv : IsNonarchimedean v)
    (h : HasSimpleSlopes v f) {z : L} (hz : f.IsRoot z) :
    ∃ i, i + 1 ≤ f.natDegree ∧ v (f.coeff i) = v (f.coeff (i + 1)) * v z := by
  have hr : 0 < v z := v.pos (h.ne_zero_of_isRoot hz)
  have hlc := h.isStrictLogConcave hr
  have hz' : f.eval z = 0 := hz
  obtain ⟨m, hm, hmax⟩ :=
    exists_max_image (range (f.natDegree + 1)) (termSize v f (v z)) ⟨0, by simp⟩
  have hmn : m ≤ f.natDegree := Nat.lt_succ_iff.mp (mem_range.mp hm)
  -- the largest size is attained twice
  obtain ⟨k, hk, hkm, hle⟩ : ∃ k ∈ range (f.natDegree + 1), k ≠ m ∧
      termSize v f (v z) m ≤ termSize v f (v z) k := by
    by_contra hcon
    push Not at hcon
    have hsum : v (∑ i ∈ range (f.natDegree + 1), f.coeff i * z ^ i) = v (f.coeff m * z ^ m) :=
      IsNonarchimedean.apply_sum_eq_of_lt hv (fun a => (v.map_neg a).symm) hm
        (fun j hj hjm => by
          rw [apply_coeff_mul_pow, apply_coeff_mul_pow]
          exact hcon j hj hjm)
    rw [← eval_eq_sum_range, hz', map_zero, apply_coeff_mul_pow] at hsum
    exact (hlc.pos m hmn).ne hsum
  have hkn : k ≤ f.natDegree := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hkm' : termSize v f (v z) k = termSize v f (v z) m := le_antisymm (hmax k hk) hle
  -- two largest terms are consecutive, and their equality is the slope
  have hcons : ∀ i l, i < l → l ≤ f.natDegree →
      termSize v f (v z) l = termSize v f (v z) i →
      (∀ j ∈ range (f.natDegree + 1), termSize v f (v z) j ≤ termSize v f (v z) i) →
      ∃ i, i + 1 ≤ f.natDegree ∧ v (f.coeff i) = v (f.coeff (i + 1)) * v z := by
    intro i l hil hl hTl hmaxi
    have hl1 : l = i + 1 := by
      by_contra hne
      exact (hlc.lt_of_succ_le (hmaxi (i + 1) (mem_range.mpr (by omega))) (by omega) hl).ne hTl
    subst hl1
    refine ⟨i, hl, ?_⟩
    rw [termSize_succ, termSize] at hTl
    exact (mul_right_cancel₀ (pow_pos hr i).ne' hTl).symm
  rcases lt_or_gt_of_ne hkm with hlt | hgt
  · exact hcons k m hlt hmn hkm'.symm fun j hj => (hmax j hj).trans hkm'.ge
  · exact hcons m k hgt hkn hkm' hmax

/-- **The multiplicities.** Let `z` be a root, on the sphere of radius `v a_j / v a_{j+1}`.
Horner's recursion gives the coefficient sizes of `g = f / (X - z)`: `v b_k = v a_{k+1}` for
`k ≥ j`, from the top, and `v b_k * v z = v a_k` for `k < j`, from the bottom. On the sphere
the term of degree `j` of `g` is strictly the largest, so `g` does not vanish there. -/
theorem HasSimpleSlopes.eval_divByMonic_ne_zero (hv : IsNonarchimedean v)
    (h : HasSimpleSlopes v f) {z : L} (hz : f.IsRoot z) {w : L} (hw : v w = v z) :
    (f /ₘ (X - C z)).eval w ≠ 0 := by
  obtain ⟨j, hjn, hj⟩ := h.exists_slope_of_isRoot hv hz
  have hr : 0 < v z := v.pos (h.ne_zero_of_isRoot hz)
  have hlc := h.isStrictLogConcave hr
  have hTj : termSize v f (v z) (j + 1) = termSize v f (v z) j := by
    rw [termSize_succ, termSize, ← hj]
  -- the quotient and its recursion
  obtain ⟨g, hg⟩ : ∃ g, g = f /ₘ (X - C z) := ⟨_, rfl⟩
  rw [← hg]
  have hfg : (X - C z) * g = f := hg ▸ mul_divByMonic_eq_iff_isRoot.mpr hz
  have hrec : ∀ k, g.coeff k = f.coeff (k + 1) + z * g.coeff (k + 1) := fun k => by
    rw [hg]
    exact coeff_divByMonic_X_sub_C_rec f z k
  have hgdeg : g.natDegree < f.natDegree := by
    rw [hg, natDegree_divByMonic f (monic_X_sub_C z), natDegree_X_sub_C]
    omega
  have hzero : f.coeff 0 = -(z * g.coeff 0) := by
    rw [← hfg, mul_coeff_zero]
    simp
  -- sizes above the slope
  have hupper : ∀ d k, k + d + 1 = f.natDegree → j ≤ k →
      v (g.coeff k) = v (f.coeff (k + 1)) := by
    intro d
    induction d with
    | zero =>
      intro k hk _
      have h0 : g.coeff (k + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hrec k, h0, mul_zero, add_zero]
    | succ d ih =>
      intro k hk hjk
      have ih' := ih (k + 1) (by omega) (by omega)
      have hlt : v (z * g.coeff (k + 1)) < v (f.coeff (k + 1)) := by
        have hdec := hlc.succ_lt_of_succ_le hTj.le (l := k + 1) (by omega) (by omega)
        rw [termSize_succ v f (v z) (k + 1), termSize] at hdec
        rw [v.map_mul, ih', mul_comm]
        exact lt_of_mul_lt_mul_right hdec (pow_pos hr _).le
      rw [hrec k]
      exact apply_add_eq_left hv hlt
  -- sizes below the slope
  have hlower : ∀ k, k < j → v (g.coeff k) * v z = v (f.coeff k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hzero, v.map_neg, v.map_mul, mul_comm]
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hinc := hlc.lt_succ_of_le_succ hjn hTj.ge (k := k) (by omega)
      rw [termSize_succ v f (v z) k, termSize] at hinc
      have hlt : v (g.coeff k) < v (-f.coeff (k + 1)) := by
        rw [v.map_neg]
        have h1 := lt_of_mul_lt_mul_right hinc (pow_pos hr k).le
        rw [← ih'] at h1
        exact lt_of_mul_lt_mul_right h1 hr.le
      have hsplit : z * g.coeff (k + 1) = -f.coeff (k + 1) + g.coeff k := by
        rw [hrec k]
        ring
      rw [mul_comm, ← v.map_mul, hsplit, apply_add_eq_left hv hlt, v.map_neg]
  have hgj : v (g.coeff j) = v (f.coeff (j + 1)) :=
    hupper (f.natDegree - j - 1) j (by omega) le_rfl
  -- the term of degree `j` dominates on the sphere
  have hdom : ∀ k ∈ range f.natDegree, k ≠ j →
      v (g.coeff k * w ^ k) < v (g.coeff j * w ^ j) := by
    intro k hk hkj
    have hkn : k < f.natDegree := mem_range.mp hk
    rw [v.map_mul, v.map_mul, v.map_pow, v.map_pow, hw, hgj]
    refine lt_of_mul_lt_mul_right ?_ hr.le
    have hR : v (f.coeff (j + 1)) * v z ^ j * v z = termSize v f (v z) j := by
      rw [← hTj, termSize_succ]
      ring
    rcases lt_or_gt_of_ne hkj with hlt | hgt
    · have hL : v (g.coeff k) * v z ^ k * v z = termSize v f (v z) k := by
        rw [termSize, ← hlower k hlt]
        ring
      rw [hL, hR]
      exact hlc.lt_of_le_succ hjn hTj.ge hlt
    · have hL : v (g.coeff k) * v z ^ k * v z = termSize v f (v z) (k + 1) := by
        rw [termSize_succ, hupper (f.natDegree - k - 1) k (by omega) hgt.le]
        ring
      rw [hL, hR]
      exact hlc.lt_of_succ_le hTj.le (by omega) (by omega)
  have hsum : v (g.eval w) = v (g.coeff j * w ^ j) := by
    rw [eval_eq_sum_range' hgdeg]
    exact IsNonarchimedean.apply_sum_eq_of_lt hv (fun a => (v.map_neg a).symm)
      (mem_range.mpr (by omega)) hdom
  have hpos : 0 < v (g.coeff j * w ^ j) := by
    rw [v.map_mul, v.map_pow, hw, hgj]
    exact mul_pos (v.pos (h.ne_zero _ hjn)) (pow_pos hr j)
  intro h0
  rw [h0, map_zero] at hsum
  exact hpos.ne hsum

/-- The roots are simple. -/
theorem HasSimpleSlopes.derivative_eval_ne_zero (hv : IsNonarchimedean v)
    (h : HasSimpleSlopes v f) {z : L} (hz : f.IsRoot z) : f.derivative.eval z ≠ 0 := by
  have hne := h.eval_divByMonic_ne_zero hv hz rfl
  have hfg := mul_divByMonic_eq_iff_isRoot.mpr hz
  generalize f /ₘ (X - C z) = g at hne hfg
  rw [← hfg]
  simpa [derivative_mul] using hne

/-- **Separation from the coefficients.** A nonarchimedean absolute value is injective on the
roots of a polynomial with strictly log-concave coefficient sizes. -/
theorem HasSimpleSlopes.injOn_isRoot (hv : IsNonarchimedean v) (h : HasSimpleSlopes v f) :
    Set.InjOn (v : L → ℝ) {z | f.IsRoot z} := by
  intro z hz w hw hzw
  have hne := h.eval_divByMonic_ne_zero hv hz hzw.symm
  have hfg := mul_divByMonic_eq_iff_isRoot.mpr (show f.IsRoot z from hz)
  have hw' : f.eval w = 0 := hw
  rw [← hfg, eval_mul, eval_sub, eval_X, eval_C] at hw'
  rcases mul_eq_zero.mp hw' with h0 | h0
  · exact (sub_eq_zero.mp h0).symm
  · exact absurd h0 hne

end Abstract

/-- In an ultrametric normed field the norm is injective on the roots of a polynomial with
strictly log-concave coefficient norms. -/
theorem injOn_norm_isRoot {K : Type*} [NormedField K] [IsUltrametricDist K] (f : K[X])
    (hne : ∀ j ≤ f.natDegree, f.coeff j ≠ 0)
    (hconc : ∀ j, j + 2 ≤ f.natDegree →
      ‖f.coeff j‖ * ‖f.coeff (j + 2)‖ < ‖f.coeff (j + 1)‖ ^ 2) :
    Set.InjOn (fun z : K => ‖z‖) {z | f.IsRoot z} :=
  HasSimpleSlopes.injOn_isRoot (v := NormedField.toAbsoluteValue K)
    IsUltrametricDist.isNonarchimedean_norm ⟨hne, hconc⟩

/-! ### Complete ultrametric fields -/

section Complete

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {L : Type*} [Field L] [Algebra K L]

variable (K L) in
/-- The spectral norm of an algebraic extension of a complete ultrametric field, as an absolute
value: it is multiplicative because the field is complete. -/
noncomputable def spectralAbsoluteValue [Algebra.IsAlgebraic K L] : AbsoluteValue L ℝ where
  toFun := spectralNorm K L
  map_mul' x y := spectralAlgNorm_mul (K := K) x y
  nonneg' := spectralNorm_nonneg
  eq_zero' x := ⟨fun hx => eq_zero_of_map_spectralNorm_eq_zero hx
    (Algebra.IsAlgebraic.isAlgebraic x), fun hx => by rw [hx, spectralNorm_zero]⟩
  add_le' _ _ := isNonarchimedean_spectralNorm.add_le spectralNorm_nonneg

theorem isNonarchimedean_spectralAbsoluteValue [Algebra.IsAlgebraic K L] :
    IsNonarchimedean (spectralAbsoluteValue K L) :=
  isNonarchimedean_spectralNorm

variable {f : K[X]}

/-- Strictly log-concave coefficient norms over `K` give simple slopes for the spectral norm
over `L`, which extends the norm of `K`. -/
theorem hasSimpleSlopes_map [Algebra.IsAlgebraic K L] (hne : ∀ j ≤ f.natDegree, f.coeff j ≠ 0)
    (hconc : ∀ j, j + 2 ≤ f.natDegree →
      ‖f.coeff j‖ * ‖f.coeff (j + 2)‖ < ‖f.coeff (j + 1)‖ ^ 2) :
    HasSimpleSlopes (spectralAbsoluteValue K L) (f.map (algebraMap K L)) where
  ne_zero j hj := by
    rw [natDegree_map] at hj
    rw [coeff_map]
    exact (_root_.map_ne_zero (algebraMap K L)).mpr (hne j hj)
  concave j hj := by
    rw [natDegree_map] at hj
    have e : ∀ a : K, spectralAbsoluteValue K L (algebraMap K L a) = ‖a‖ :=
      fun a => spectralNorm_extends a
    rw [coeff_map, coeff_map, coeff_map, e, e, e]
    exact hconc j hj

/-- The hypothesis of the separation principle, from the coefficients: the spectral norm is
injective on the roots. -/
theorem injOn_spectralNorm_rootSet [Algebra.IsAlgebraic K L]
    (hne : ∀ j ≤ f.natDegree, f.coeff j ≠ 0)
    (hconc : ∀ j, j + 2 ≤ f.natDegree →
      ‖f.coeff j‖ * ‖f.coeff (j + 2)‖ < ‖f.coeff (j + 1)‖ ^ 2) :
    Set.InjOn (spectralNorm K L) (f.rootSet L) := by
  have h := (hasSimpleSlopes_map (L := L) hne hconc).injOn_isRoot
    isNonarchimedean_spectralAbsoluteValue
  have hroot : ∀ x ∈ f.rootSet L, (f.map (algebraMap K L)).IsRoot x := fun x hx => by
    rw [IsRoot.def, eval_map_algebraMap]
    exact (mem_rootSet.mp hx).2
  intro x hx y hy hxy
  exact h (hroot x hx) (hroot y hy) hxy

/-- **Rationality from the coefficients, Galois form.** In a Galois extension of a complete
ultrametric field every root of a polynomial with strictly log-concave coefficient norms lies in
the base field: the separation principle with its hypothesis supplied by the Newton polygon. -/
theorem mem_range_algebraMap_of_strict_logConcave [IsGalois K L]
    (hne : ∀ j ≤ f.natDegree, f.coeff j ≠ 0)
    (hconc : ∀ j, j + 2 ≤ f.natDegree →
      ‖f.coeff j‖ * ‖f.coeff (j + 2)‖ < ‖f.coeff (j + 1)‖ ^ 2)
    {x : L} (hx : x ∈ f.rootSet L) : x ∈ Set.range (algebraMap K L) :=
  mem_range_algebraMap_of_spectralNorm_injOn f (injOn_spectralNorm_rootSet hne hconc) hx

/-- In an algebraically closed algebraic extension every root lies in the base field. The
conjugates of a root `x` are roots with the spectral norm of `x`, which depends only on the
minimal polynomial; by the separation they equal `x`, and `x` is a simple root, so its minimal
polynomial has degree one. No separability of the extension is used. -/
theorem mem_range_of_isRoot_of_isAlgClosed [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (hne : ∀ j ≤ f.natDegree, f.coeff j ≠ 0)
    (hconc : ∀ j, j + 2 ≤ f.natDegree →
      ‖f.coeff j‖ * ‖f.coeff (j + 2)‖ < ‖f.coeff (j + 1)‖ ^ 2)
    {x : L} (hx : (f.map (algebraMap K L)).IsRoot x) : x ∈ (algebraMap K L).range := by
  classical
  have hslopes := hasSimpleSlopes_map (L := L) hne hconc
  have hna : IsNonarchimedean (spectralAbsoluteValue K L) :=
    isNonarchimedean_spectralAbsoluteValue
  have hf0 : f ≠ 0 := fun h0 => hne 0 (Nat.zero_le _) (by rw [h0, coeff_zero])
  have hF0 : f.map (algebraMap K L) ≠ 0 := Polynomial.map_ne_zero hf0
  have hxint : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hmdvd : minpoly K x ∣ f :=
    minpoly.dvd K x (by rwa [IsRoot.def, eval_map_algebraMap] at hx)
  -- every root of the minimal polynomial is `x`
  have hroots : ∀ y ∈ ((minpoly K x).map (algebraMap K L)).roots, y = x := by
    intro y hy
    have hmy : aeval y (minpoly K x) = 0 := by
      have hy' := isRoot_of_mem_roots hy
      rwa [IsRoot.def, eval_map_algebraMap] at hy'
    have hmin : minpoly K y = minpoly K x :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hxint) hmy
        (minpoly.monic hxint)).symm
    have hyroot : (f.map (algebraMap K L)).IsRoot y := by
      obtain ⟨q, hq⟩ := hmdvd
      rw [IsRoot.def, eval_map_algebraMap, hq, map_mul, hmy, zero_mul]
    have hnorm : spectralAbsoluteValue K L y = spectralAbsoluteValue K L x := by
      show spectralValue (minpoly K y) = spectralValue (minpoly K x)
      rw [hmin]
    exact hslopes.injOn_isRoot hna hyroot hx hnorm
  -- so the minimal polynomial is a power of `X - x`, and `x` is a simple root
  have hsplit : ((minpoly K x).map (algebraMap K L)).Splits := IsAlgClosed.splits _
  have hcard : ((minpoly K x).map (algebraMap K L)).roots.card = (minpoly K x).natDegree := by
    rw [← hsplit.natDegree_eq_card_roots, natDegree_map]
  have hmult : ((minpoly K x).map (algebraMap K L)).rootMultiplicity x =
      (minpoly K x).natDegree := by
    rw [← count_roots, Multiset.eq_replicate.mpr ⟨hcard, hroots⟩, Multiset.count_replicate_self]
  have hle := rootMultiplicity_le_rootMultiplicity_of_dvd hF0
    (Polynomial.map_dvd (algebraMap K L) hmdvd) x
  have hone : (f.map (algebraMap K L)).rootMultiplicity x ≤ 1 := by
    by_contra hgt
    exact hslopes.derivative_eval_ne_zero hna hx
      ((one_lt_rootMultiplicity_iff_isRoot hF0).mp (not_le.mp hgt)).2
  have hpos := minpoly.natDegree_pos hxint
  exact minpoly.natDegree_eq_one_iff.mp (by omega)

/-- **The ultrametric Newton polygon with sides of length one.** Over a complete ultrametric
field a polynomial with nonzero coefficients of strictly log-concave norms splits. -/
theorem splits_of_strict_logConcave (f : K[X]) (hne : ∀ j ≤ f.natDegree, f.coeff j ≠ 0)
    (hconc : ∀ j, j + 2 ≤ f.natDegree →
      ‖f.coeff j‖ * ‖f.coeff (j + 2)‖ < ‖f.coeff (j + 1)‖ ^ 2) : f.Splits :=
  Splits.of_splits_map (algebraMap K (AlgebraicClosure K)) (IsAlgClosed.splits _) fun _ hx =>
    mem_range_of_isRoot_of_isAlgClosed hne hconc (isRoot_of_mem_roots hx)

/-- The roots are as many as the degree, counted in the base field. -/
theorem card_roots_of_strict_logConcave (f : K[X]) (hne : ∀ j ≤ f.natDegree, f.coeff j ≠ 0)
    (hconc : ∀ j, j + 2 ≤ f.natDegree →
      ‖f.coeff j‖ * ‖f.coeff (j + 2)‖ < ‖f.coeff (j + 1)‖ ^ 2) :
    f.roots.card = f.natDegree :=
  (splits_of_strict_logConcave f hne hconc).natDegree_eq_card_roots.symm

end Complete

/-! ### The `p`-adic theta polynomials -/

section Theta

variable (p : ℕ) [Fact p.Prime]

/-- The partial sums of the `p`-adic theta series `∑ p ^ (k ^ 2) X ^ k`. -/
noncomputable def padicTheta (n : ℕ) : ℚ_[p][X] :=
  ∑ k ∈ range (n + 1), C ((p : ℚ_[p]) ^ k ^ 2) * X ^ k

theorem coeff_padicTheta {n j : ℕ} (hj : j ≤ n) :
    (padicTheta p n).coeff j = (p : ℚ_[p]) ^ j ^ 2 := by
  rw [padicTheta, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq, if_pos (mem_range.mpr (Nat.lt_succ_of_le hj))]

theorem natCast_padic_ne_zero : (p : ℚ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

theorem natDegree_padicTheta (n : ℕ) : (padicTheta p n).natDegree = n := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · exact natDegree_sum_le_of_forall_le _ _ fun k hk =>
      (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (mem_range.mp hk))
  · rw [coeff_padicTheta p le_rfl]
    exact pow_ne_zero _ (natCast_padic_ne_zero p)

theorem norm_coeff_padicTheta {n j : ℕ} (hj : j ≤ n) :
    ‖(padicTheta p n).coeff j‖ = ((p : ℝ)⁻¹) ^ j ^ 2 := by
  rw [coeff_padicTheta p hj, norm_pow, Padic.norm_p]

theorem coeff_padicTheta_ne_zero (n : ℕ) :
    ∀ j ≤ (padicTheta p n).natDegree, (padicTheta p n).coeff j ≠ 0 := fun j hj => by
  rw [natDegree_padicTheta] at hj
  rw [coeff_padicTheta p hj]
  exact pow_ne_zero _ (natCast_padic_ne_zero p)

/-- The coefficient norms `p ^ (-k ^ 2)` are strictly log-concave:
`k ^ 2 + (k + 2) ^ 2 = 2 (k + 1) ^ 2 + 2`. -/
theorem norm_coeff_padicTheta_strict_logConcave (n : ℕ) :
    ∀ j, j + 2 ≤ (padicTheta p n).natDegree →
      ‖(padicTheta p n).coeff j‖ * ‖(padicTheta p n).coeff (j + 2)‖ <
        ‖(padicTheta p n).coeff (j + 1)‖ ^ 2 := fun j hj => by
  have hp : p.Prime := Fact.out
  have hq0 : 0 < ((p : ℝ)⁻¹) := inv_pos.mpr (Nat.cast_pos.mpr hp.pos)
  have hq1 : ((p : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  rw [natDegree_padicTheta] at hj
  rw [norm_coeff_padicTheta p (by omega : j ≤ n), norm_coeff_padicTheta p hj,
    norm_coeff_padicTheta p (by omega : j + 1 ≤ n), ← pow_add, ← pow_mul]
  have hexp : (j + 1) ^ 2 * 2 + 2 = j ^ 2 + (j + 2) ^ 2 := by ring
  exact pow_lt_pow_right_of_lt_one₀ hq0 hq1 (by omega)

/-- Every partial sum of the `p`-adic theta series splits over `ℚ_p`. -/
theorem padicTheta_splits (n : ℕ) : (padicTheta p n).Splits :=
  splits_of_strict_logConcave _ (coeff_padicTheta_ne_zero p n)
    (norm_coeff_padicTheta_strict_logConcave p n)

/-- Its `n` roots in `ℚ_p` have pairwise distinct norms. -/
theorem padicTheta_roots (n : ℕ) :
    (padicTheta p n).roots.card = n ∧
      Set.InjOn (fun z : ℚ_[p] => ‖z‖) {z | (padicTheta p n).IsRoot z} :=
  ⟨by rw [card_roots_of_strict_logConcave _ (coeff_padicTheta_ne_zero p n)
      (norm_coeff_padicTheta_strict_logConcave p n), natDegree_padicTheta],
    injOn_norm_isRoot _ (coeff_padicTheta_ne_zero p n)
      (norm_coeff_padicTheta_strict_logConcave p n)⟩

end Theta

#print axioms HasSimpleSlopes.injOn_isRoot
#print axioms mem_range_algebraMap_of_strict_logConcave
#print axioms splits_of_strict_logConcave
#print axioms padicTheta_splits
#print axioms padicTheta_roots

end GaloisForLFunctions.SignFreePurityMechanisms
