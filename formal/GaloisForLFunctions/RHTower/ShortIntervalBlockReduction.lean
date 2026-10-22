import Mathlib

/-!
# The block reduction for prime counts in a fixed short interval

Guth–Maynard reduce the second moment of `ψ(x + y) − ψ(x) − y` over `x ∈ [X, 2X]`, for a window of
FIXED length `y`, to the second moment of the MULTIPLICATIVE window `ψ(u + δu) − ψ(u) − δu` over
`[X, 3X]`.  The reduction is purely real-analytic and is stated here for an arbitrary `P : ℝ → ℝ`:

* `fixedIncr_eq_sum_sub_bdry` — along the geometric grid `x (1 + δ)^j` the fixed increment is the sum
  of the multiplicative increments minus one boundary increment (an algebraic identity);
* `sq_fixedIncr_le` — Cauchy–Schwarz against the constant one;
* `integral_comp_mul_le` — a dilated block integral is at most the integral over `[X, 3X]`;
* `integral_sq_fixedIncr_le` — the reduction, `∫_X^{2X} g² ≤ 2J² ∫_X^{3X} f² + 2 ∫ boundary²`.

This is the inequality that converts the corpus's almost-all short-interval layer, which is built for
multiplicative windows because those have `x`-independent zero coefficients, into a statement about a
fixed window length.
-/

set_option autoImplicit false

namespace RHTower

open Finset MeasureTheory intervalIntegral

noncomputable section

/-- The multiplicative window increment of `P` at `u` with ratio `1 + δ`. -/
noncomputable def multIncr (P : ℝ → ℝ) (δ u : ℝ) : ℝ := P (u * (1 + δ)) - P u - δ * u

/-- The fixed window increment of `P` at `x` with length `y`. -/
noncomputable def fixedIncr (P : ℝ → ℝ) (y x : ℝ) : ℝ := P (x + y) - P x - y

/-- The `j`-th grid point `x (1 + δ)^j`. -/
noncomputable def gridPt (δ x : ℝ) (j : ℕ) : ℝ := x * (1 + δ) ^ j

/-- Telescoping the multiplicative increments along the geometric grid. -/
theorem sum_multIncr_gridPt (P : ℝ → ℝ) {δ : ℝ} (hδ : δ ≠ 0) (x : ℝ) (J : ℕ) :
    ∑ j ∈ range J, multIncr P δ (gridPt δ x j)
      = P (gridPt δ x J) - P x - (gridPt δ x J - x) := by
  have hstep : ∀ j : ℕ, gridPt δ x j * (1 + δ) = gridPt δ x (j + 1) := by
    intro j; unfold gridPt; ring
  have h1 : ∑ j ∈ range J, (P (gridPt δ x (j + 1)) - P (gridPt δ x j))
      = P (gridPt δ x J) - P (gridPt δ x 0) :=
    Finset.sum_range_sub (fun j => P (gridPt δ x j)) J
  have h0 : gridPt δ x 0 = x := by unfold gridPt; simp
  have hgeom : ∑ j ∈ range J, δ * gridPt δ x j = gridPt δ x J - x := by
    have hne : (1 + δ) ≠ 1 := by intro h; apply hδ; linarith
    have : ∑ j ∈ range J, δ * gridPt δ x j = δ * x * ∑ j ∈ range J, (1 + δ) ^ j := by
      unfold gridPt; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [this, geom_sum_eq hne]
    unfold gridPt
    field_simp
    ring
  calc ∑ j ∈ range J, multIncr P δ (gridPt δ x j)
      = ∑ j ∈ range J, ((P (gridPt δ x (j + 1)) - P (gridPt δ x j)) - δ * gridPt δ x j) := by
        apply Finset.sum_congr rfl; intro j _
        unfold multIncr
        rw [hstep j]
    _ = (∑ j ∈ range J, (P (gridPt δ x (j + 1)) - P (gridPt δ x j)))
          - ∑ j ∈ range J, δ * gridPt δ x j := by rw [Finset.sum_sub_distrib]
    _ = P (gridPt δ x J) - P x - (gridPt δ x J - x) := by rw [h1, h0, hgeom]

/-- The boundary increment from the last grid point back to `x + y`. -/
noncomputable def bdryIncr (P : ℝ → ℝ) (y x : ℝ) (δ : ℝ) (J : ℕ) : ℝ :=
  P (gridPt δ x J) - P (x + y) - (gridPt δ x J - (x + y))

/-- **The block decomposition.**  The fixed window increment is the sum of the multiplicative
increments along the grid, minus the boundary increment.  Purely algebraic. -/
theorem fixedIncr_eq_sum_sub_bdry (P : ℝ → ℝ) {δ : ℝ} (hδ : δ ≠ 0) (y x : ℝ) (J : ℕ) :
    fixedIncr P y x
      = (∑ j ∈ range J, multIncr P δ (gridPt δ x j)) - bdryIncr P y x δ J := by
  rw [sum_multIncr_gridPt P hδ x J]
  unfold fixedIncr bdryIncr
  ring




/-- Cauchy–Schwarz against the constant one: `(∑ a)² ≤ J ∑ a²`. -/
theorem sq_sum_le_card_mul_sum_sq (J : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ range J, a j) ^ 2 ≤ (J : ℝ) * ∑ j ∈ range J, (a j) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (range J) a (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  linarith [h]

/-- **The squared block bound.**  Pointwise in `x`: the square of the fixed window increment is at
most `2J` times the sum of the squares of the multiplicative increments along the grid, plus twice
the square of the boundary increment. -/
theorem sq_fixedIncr_le (P : ℝ → ℝ) {δ : ℝ} (hδ : δ ≠ 0) (y x : ℝ) (J : ℕ) :
    (fixedIncr P y x) ^ 2
      ≤ 2 * (J : ℝ) * (∑ j ∈ range J, (multIncr P δ (gridPt δ x j)) ^ 2)
        + 2 * (bdryIncr P y x δ J) ^ 2 := by
  rw [fixedIncr_eq_sum_sub_bdry P hδ y x J]
  have hcs := sq_sum_le_card_mul_sum_sq J (fun j => multIncr P δ (gridPt δ x j))
  nlinarith [sq_nonneg ((∑ j ∈ range J, multIncr P δ (gridPt δ x j)) + bdryIncr P y x δ J),
    sq_nonneg (bdryIncr P y x δ J)]




/-- One dilated block integral: `∫_X^{2X} g(x c) dx ≤ ∫_X^{3X} g` for `1 ≤ c`, `2c ≤ 3`, `g ≥ 0`. -/
theorem integral_comp_mul_le {g : ℝ → ℝ} {X c : ℝ} (hX : 0 < X) (hc1 : 1 ≤ c) (hc2 : 2 * c ≤ 3)
    (hg : ∀ u, 0 ≤ g u) (hsrc : IntervalIntegrable g volume X (3 * X)) :
    ∫ x in X..(2 * X), g (x * c) ≤ ∫ u in X..(3 * X), g u := by
  have hc0 : c ≠ 0 := by positivity
  rw [integral_comp_mul_right g hc0]
  have hmono : ∫ u in (X * c)..(2 * X * c), g u ≤ ∫ u in X..(3 * X), g u := by
    refine integral_mono_interval (by nlinarith) (by nlinarith) (by nlinarith) ?_ hsrc
    exact Filter.Eventually.of_forall fun u => hg u
  have hpos : 0 ≤ ∫ u in X..(3 * X), g u := by
    refine intervalIntegral.integral_nonneg (by linarith) ?_
    intro u _; exact hg u
  have hcinv : c⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact hc1
  have hc0' : (0 : ℝ) < c := by linarith
  simp only [smul_eq_mul]
  calc c⁻¹ * ∫ u in (X * c)..(2 * X * c), g u
      ≤ c⁻¹ * ∫ u in X..(3 * X), g u := by
        exact mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ 1 * ∫ u in X..(3 * X), g u := by exact mul_le_mul_of_nonneg_right hcinv hpos
    _ = _ := one_mul _




/-- **The block / Cauchy–Schwarz reduction.**  The second moment of the fixed window increment on
`[X, 2X]` is controlled by `J²` times the second moment of the multiplicative increment on
`[X, 3X]`, plus the boundary term. -/
theorem integral_sq_fixedIncr_le (P : ℝ → ℝ) {δ X y : ℝ} (hδ : 0 < δ) (hX : 0 < X) (J : ℕ)
    (hJ : 2 * (1 + δ) ^ J ≤ 3)
    (hsrc : IntervalIntegrable (fun u => (multIncr P δ u) ^ 2) volume X (3 * X))
    (hblk : ∀ j ∈ range J,
      IntervalIntegrable (fun x => (multIncr P δ (gridPt δ x j)) ^ 2) volume X (2 * X))
    (hfix : IntervalIntegrable (fun x => (fixedIncr P y x) ^ 2) volume X (2 * X))
    (hbd : IntervalIntegrable (fun x => (bdryIncr P y x δ J) ^ 2) volume X (2 * X)) :
    ∫ x in X..(2 * X), (fixedIncr P y x) ^ 2
      ≤ 2 * (J : ℝ) ^ 2 * (∫ u in X..(3 * X), (multIncr P δ u) ^ 2)
        + 2 * ∫ x in X..(2 * X), (bdryIncr P y x δ J) ^ 2 := by
  have hX2 : X ≤ 2 * X := by linarith
  have hδ1 : (1 : ℝ) ≤ 1 + δ := by linarith
  -- the summed integrand is integrable
  have hsum : IntervalIntegrable
      (fun x => ∑ j ∈ range J, (multIncr P δ (gridPt δ x j)) ^ 2) volume X (2 * X) := by
    have h := IntervalIntegrable.sum (range J) hblk
    have e : (∑ i ∈ range J, fun x => (multIncr P δ (gridPt δ x i)) ^ 2)
        = fun x => ∑ j ∈ range J, (multIncr P δ (gridPt δ x j)) ^ 2 := by
      funext x; simp [Finset.sum_apply]
    rwa [e] at h
  have hRHS : IntervalIntegrable
      (fun x => 2 * (J : ℝ) * (∑ j ∈ range J, (multIncr P δ (gridPt δ x j)) ^ 2)
        + 2 * (bdryIncr P y x δ J) ^ 2) volume X (2 * X) :=
    (hsum.const_mul _).add (hbd.const_mul _)
  -- pointwise, then integrate
  have hstep : ∫ x in X..(2 * X), (fixedIncr P y x) ^ 2
      ≤ ∫ x in X..(2 * X), (2 * (J : ℝ) * (∑ j ∈ range J, (multIncr P δ (gridPt δ x j)) ^ 2)
          + 2 * (bdryIncr P y x δ J) ^ 2) :=
    integral_mono_on hX2 hfix hRHS fun x _ => sq_fixedIncr_le P hδ.ne' y x J
  -- split the right-hand integral
  rw [integral_add (hsum.const_mul _) (hbd.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (s := range J)
      (f := fun j x => (multIncr P δ (gridPt δ x j)) ^ 2) hblk] at hstep
  -- each dilated block integral is at most the source integral
  have hterm : ∀ j ∈ range J,
      (∫ x in X..(2 * X), (multIncr P δ (gridPt δ x j)) ^ 2)
        ≤ ∫ u in X..(3 * X), (multIncr P δ u) ^ 2 := by
    intro j hj
    have hjJ : j ≤ J := le_of_lt (Finset.mem_range.mp hj)
    have hc1 : (1 : ℝ) ≤ (1 + δ) ^ j := one_le_pow₀ hδ1
    have hc2 : 2 * (1 + δ) ^ j ≤ 3 := by
      have : (1 + δ) ^ j ≤ (1 + δ) ^ J := pow_le_pow_right₀ hδ1 hjJ
      linarith
    exact integral_comp_mul_le (g := fun u => (multIncr P δ u) ^ 2) hX hc1 hc2
      (fun u => sq_nonneg _) hsrc
  have hsumle : (∑ j ∈ range J, ∫ x in X..(2 * X), (multIncr P δ (gridPt δ x j)) ^ 2)
      ≤ (J : ℝ) * ∫ u in X..(3 * X), (multIncr P δ u) ^ 2 := by
    calc (∑ j ∈ range J, ∫ x in X..(2 * X), (multIncr P δ (gridPt δ x j)) ^ 2)
        ≤ ∑ _j ∈ range J, ∫ u in X..(3 * X), (multIncr P δ u) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = (J : ℝ) * ∫ u in X..(3 * X), (multIncr P δ u) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hJ0 : (0 : ℝ) ≤ 2 * (J : ℝ) := by positivity
  nlinarith [hstep, mul_le_mul_of_nonneg_left hsumle hJ0]


/-- **The squared block bound with a pointwise block count.**  The telescope needs the exact number
of blocks `J` reaching past `x + y`, but Cauchy–Schwarz tolerates extending the sum to any uniform
`J₀ ≥ J`, since the summands are squares.  This is what lets the boundary increment be taken at the
pointwise `J` while the block sum is taken at a single `J₀`. -/
theorem sq_fixedIncr_le_of_le (P : ℝ → ℝ) {δ : ℝ} (hδ : δ ≠ 0) (y x : ℝ) (J J₀ : ℕ)
    (hJ : J ≤ J₀) :
    (fixedIncr P y x) ^ 2
      ≤ 2 * (J₀ : ℝ) * (∑ j ∈ range J₀, (multIncr P δ (gridPt δ x j)) ^ 2)
        + 2 * (bdryIncr P y x δ J) ^ 2 := by
  rw [fixedIncr_eq_sum_sub_bdry P hδ y x J]
  have hcs := sq_sum_le_card_mul_sum_sq J (fun j => multIncr P δ (gridPt δ x j))
  have hmono : (∑ j ∈ range J, (multIncr P δ (gridPt δ x j)) ^ 2)
      ≤ ∑ j ∈ range J₀, (multIncr P δ (gridPt δ x j)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hJ))
      fun _ _ _ => sq_nonneg _
  have hJle : (J : ℝ) ≤ (J₀ : ℝ) := Nat.cast_le.mpr hJ
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
  have hsum0 : (0 : ℝ) ≤ ∑ j ∈ range J₀, (multIncr P δ (gridPt δ x j)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hkey : (∑ j ∈ range J, multIncr P δ (gridPt δ x j)) ^ 2
      ≤ (J₀ : ℝ) * ∑ j ∈ range J₀, (multIncr P δ (gridPt δ x j)) ^ 2 := by
    refine hcs.trans ?_
    calc (J : ℝ) * ∑ j ∈ range J, (multIncr P δ (gridPt δ x j)) ^ 2
        ≤ (J : ℝ) * ∑ j ∈ range J₀, (multIncr P δ (gridPt δ x j)) ^ 2 :=
          mul_le_mul_of_nonneg_left hmono hJ0
      _ ≤ (J₀ : ℝ) * ∑ j ∈ range J₀, (multIncr P δ (gridPt δ x j)) ^ 2 :=
          mul_le_mul_of_nonneg_right hJle hsum0
  nlinarith [sq_nonneg ((∑ j ∈ range J, multIncr P δ (gridPt δ x j)) + bdryIncr P y x δ J),
    sq_nonneg (bdryIncr P y x δ J), hkey]


/-- The grid reaches past `x + y` eventually, since `1 + δ > 1`. -/
theorem exists_gridPt_ge {δ x y : ℝ} (hδ : 0 < δ) (hx : 0 < x) (_hy : 0 ≤ y) :
    ∃ J : ℕ, x + y ≤ gridPt δ x J := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((x + y) / x) (by linarith : (1 : ℝ) < 1 + δ)
  refine ⟨n, ?_⟩
  rw [gridPt, ← div_le_iff₀' hx] at *
  exact le_of_lt hn

/-- **The pointwise block count.**  The least `J` whose grid point reaches past `x + y` overshoots by
at most one window ratio, because the previous grid point falls short. -/
theorem exists_blockCount {δ x y : ℝ} (hδ : 0 < δ) (hx : 0 < x) (hy : 0 ≤ y) :
    ∃ J : ℕ, x + y ≤ gridPt δ x J ∧ gridPt δ x J ≤ (x + y) * (1 + δ) ∧
      ∀ J₀ : ℕ, x + y ≤ gridPt δ x J₀ → J ≤ J₀ := by
  classical
  have hex : ∃ J : ℕ, x + y ≤ gridPt δ x J := exists_gridPt_ge hδ hx hy
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, fun J₀ hJ₀ => Nat.find_min' hex hJ₀⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · -- the grid already starts past `x + y`, so `y = 0`
    have hspec := Nat.find_spec hex
    rw [h0] at hspec ⊢
    simp only [gridPt, pow_zero, mul_one] at hspec ⊢
    nlinarith
  · -- the previous grid point falls short
    obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hlt : ¬ (x + y ≤ gridPt δ x m) := Nat.find_min hex (by omega)
    have hstep : gridPt δ x (m + 1) = gridPt δ x m * (1 + δ) := by
      simp only [gridPt]; ring
    rw [hm, hstep]
    have h1 : gridPt δ x m < x + y := lt_of_not_ge hlt
    nlinarith

end

end RHTower
