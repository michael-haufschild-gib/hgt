import GaloisForLFunctions.FamilyContinuationTheory.TheSevenEighthsGeometryIsAVertex

/-!
# The exponent plane of the low side

Exponent statements for the low estimate of the compensated probe: scales `X = Z^{lx}`,
`Y = Z^{ly}`, row length `M = lx + ly`, slot length `ℓ`. All statements are identities and
inequalities between exponents, not bounds for arithmetic sums.

**Slots.** In the range of the reflection (`M + ℓ ≤ 1`) the low boundary is `5/6 + M₀/12` in the
rescaled row length `M₀ = M − 2ℓ` (`lowBoundary_eq_rescaled`); the two constraints of the low side
are `(1 − ℓ)/2 ≤ M₀ ≤ 1 − 3ℓ` (`rescaled_range_iff`). Without slots the boundary `7/8` is reached
at row length `1/2`. On the edge `M + ℓ = 1` the low boundary is `11/12 − ℓ/4`, the floor bin at
balanced scales forces `2/3 + ℓ`, and the allowance of the marked rows is inactive, exactly for
`ℓ ≤ 1/5`.

**Corners.** With the allowance inactive the low boundary is at least `13/15`
(`thirteen_fifteenths_le_lowBoundary`); with the constraint `3 + 5ℓ ≤ 6M`, which a saving of one
third of the slot length in the sums over the tuples of marks would give, it is at least `28/33`
(`twentyeight_thirtythirds_le_lowBoundary`). For rows of conductor `q_m²` and principal
frequencies of order `n` the corner without slots is `1 − 2/(3n)` (`corner_two_order`): the order
six is the best among the covers of odd order. When the nonprincipal rows of the linear form are
bounded by Cauchy–Schwarz against the mean square `Z²` of the Möbius sums over the twists of norm
up to `Z`, the corner with the low boundary is `31/34` in the regime `5 ly ≤ 11 lx`
(`thirtyone_thirtyfourths_le_corner`).

**Two reflections.** On the plane of exponents (rows `r`, length `l` of the index) the reflection
of a row is `(r, l) ↦ (r, 2r − l)` and the summation in the row index is `(r, l) ↦ (2l − r, l)`.
Their product is the translation by `2(r − l)` in both coordinates
(`iterate_sumScale_reflectScale`); the rows `Z^M` of an index of length `Z` have the second
description at the scale `(3M − 2, 4M − 3)`, where the generic bound gives at best `11/12`
(`one_sixth_le_translated`). The principal twists exceed the generic mean square by
`principalExcess`, which is their relative size minus the window `M − 1 − ℓ` of the summation.
With rows as long as the marked index the excess at `β = 1/2` is `(ℓ − 5)/6`.

**The sieve for the reflected rows.** In the positive form at family length `P = Z^θ` a term
`K^u N^v` of the large sieve for the reflected rows contributes the exponent `sieveTermExponent`
to the bound for the square of the target, next to the diagonal `1 + 5θ/6`. The optimal sieve
`K + N` gives `11/6` at `θ = 1`. A term with `4u + 3v ≥ 5` gives no half-plane at any family
length (`two_le_of_sieve_threshold`): this includes `K^{1/2} N` (the square row indices, on which
the quadratic symbol is principal), `N³/K` (one summation applied to the trivial bound) and `N²`
(a bound for each character sum by the square root of its conductor). A term `(KN)^{2/3}` would
give `71/36` at `θ = 7/6`. Without the reflection the sextic large sieve gives no half-plane in
the linear probe (`one_lt_of_directSextic_lt`).
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Budget

noncomputable section

/-! ### Slots -/

/-- In the range of the reflection the low boundary depends on the rescaled row length
`M − 2ℓ` alone. -/
theorem lowBoundary_eq_rescaled {lx ly ℓ : ℝ} (h : lx + ly + ℓ ≤ 1) :
    lowBoundary lx ly ℓ = 5 / 6 + (lx + ly - 2 * ℓ) / 12 := by
  unfold lowBoundary
  rw [max_eq_left (by linarith)]
  ring

/-- The two constraints of the low side in the rescaled row length. -/
theorem rescaled_range_iff (M ℓ : ℝ) :
    (1 + 3 * ℓ ≤ 2 * M ∧ M + ℓ ≤ 1) ↔ ((1 - ℓ) / 2 ≤ M - 2 * ℓ ∧ M - 2 * ℓ ≤ 1 - 3 * ℓ) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Without slots the boundary `7/8` is reached at row length `1/2`. -/
theorem lowBoundary_unslotted_half : lowBoundary (3 / 16) (5 / 16) 0 = 7 / 8 := by
  rw [lowBoundary_eq_rescaled (by norm_num)]
  norm_num

/-- On the edge `M + ℓ = 1` the low boundary is `11/12 − ℓ/4`. -/
theorem lowBoundary_edge {lx ly ℓ : ℝ} (h : lx + ly + ℓ = 1) :
    lowBoundary lx ly ℓ = 11 / 12 - ℓ / 4 := by
  rw [lowBoundary_eq_rescaled h.le]
  linarith

/-- On the edge with balanced scales the floor bin forces the boundary `2/3 + ℓ`. -/
theorem endpointExponent_edge_floor_bin (ℓ σ₀ : ℝ) :
    endpointExponent ((1 - ℓ) / 2) ((1 - ℓ) / 2) ℓ σ₀ 0 0 1 = 2 / 3 + ℓ - σ₀ := by
  unfold endpointExponent
  ring

/-- On the edge the allowance of the marked rows is inactive exactly for `ℓ ≤ 1/5`. -/
theorem edge_allowance_iff (ℓ : ℝ) : 1 + 3 * ℓ ≤ 2 * (1 - ℓ) ↔ ℓ ≤ 1 / 5 := by
  constructor <;> intro h <;> linarith

/-- On the edge the floor bin lies below the low boundary exactly for `ℓ ≤ 1/5`. -/
theorem edge_floor_bin_le_low_iff (ℓ : ℝ) : 2 / 3 + ℓ ≤ 11 / 12 - ℓ / 4 ↔ ℓ ≤ 1 / 5 := by
  constructor <;> intro h <;> linarith

/-! ### Corners -/

/-- **The corner of the low bound alone.** With the allowance inactive the low boundary is at
least `13/15`, the value at `(M, ℓ) = (4/5, 1/5)`. -/
theorem thirteen_fifteenths_le_lowBoundary {lx ly ℓ : ℝ} (h : 1 + 3 * ℓ ≤ 2 * (lx + ly)) :
    13 / 15 ≤ lowBoundary lx ly ℓ := by
  unfold lowBoundary
  have hμ0 : (0 : ℝ) ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hμ1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  generalize max 0 (lx + ly + ℓ - 1) = μ at hμ0 hμ1 ⊢
  linarith

/-- With the constraint `3 + 5ℓ ≤ 6M` in the place of `1 + 3ℓ ≤ 2M` the low boundary is at least
`28/33`. -/
theorem twentyeight_thirtythirds_le_lowBoundary {lx ly ℓ : ℝ}
    (h : 3 + 5 * ℓ ≤ 6 * (lx + ly)) : 28 / 33 ≤ lowBoundary lx ly ℓ := by
  unfold lowBoundary
  have hμ0 : (0 : ℝ) ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hμ1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  generalize max 0 (lx + ly + ℓ - 1) = μ at hμ0 hμ1 ⊢
  linarith

/-- The value `28/33` is attained at `(M, ℓ) = (8/11, 3/11)`. -/
theorem lowBoundary_tuple_saving_corner : lowBoundary (4 / 11) (4 / 11) (3 / 11) = 28 / 33 := by
  rw [lowBoundary_edge (by norm_num)]
  norm_num

/-- Rows of conductor `q_m²` and principal frequencies of order `n`: the corner of the low
boundary and the floor bin without slots is at least `1 − 2/(3n)`, the value at row length
`2/3`. -/
theorem corner_two_order {n : ℝ} (hn : 1 ≤ n) (M : ℝ) :
    1 - 2 / (3 * n) ≤ max (lowUnslotted 2 n M) (floorUnslotted n M) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hinv : 0 < 1 / n := by positivity
  have hinv1 : 1 / n ≤ 1 := by
    rw [div_le_one hn0]
    exact hn
  have e : 2 / (3 * n) = 2 / 3 * (1 / n) := by
    field_simp
  rw [e]
  rcases le_total M (2 / 3) with h | h
  · refine le_max_of_le_right ?_
    unfold floorUnslotted
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 / 3 - M)
      (by linarith : (0 : ℝ) ≤ 3 / 2 - 1 / n)]
  · refine le_max_of_le_left ?_
    unfold lowUnslotted
    have hm : (0 : ℝ) ≤ max 0 ((2 - 1) * M - 1) := le_max_left _ _
    generalize max 0 (((2 : ℝ) - 1) * M - 1) = m at hm ⊢
    have e2 : (1 - M / 2) / n = (1 - M / 2) * (1 / n) := by ring
    rw [e2]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ M - 2 / 3) hinv.le]

/-- Among the orders `n ≥ 6` the order six has the least corner: a cover of odd order `n₀ ≥ 3`
has principal frequencies of order `2n₀`. -/
theorem eight_ninths_le_corner_two_order {n : ℝ} (hn : 6 ≤ n) (M : ℝ) :
    8 / 9 ≤ max (lowUnslotted 2 n M) (floorUnslotted n M) := by
  refine le_trans ?_ (corner_two_order (by linarith) M)
  have h : 2 / (3 * n) ≤ 1 / 9 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith

/-- Boundary forced by the nonprincipal rows of the linear form when they are bounded by
Cauchy–Schwarz against a mean square `Z²` of the Möbius sums over the twists of norm up to `Z`. -/
def familyHighBoundary (lx ly : ℝ) : ℝ := 4 / 3 - lx / 3 - ly / 2

/-- In the regime `5 ly ≤ 11 lx` the corner of the low boundary and that bound is `31/34`. -/
theorem thirtyone_thirtyfourths_le_corner {lx ly : ℝ} (h : 5 * ly ≤ 11 * lx) :
    31 / 34 ≤ max (lowBoundaryGen lx ly 0) (familyHighBoundary lx ly) := by
  by_contra hcon
  rw [not_le, max_lt_iff] at hcon
  obtain ⟨ha, hb⟩ := hcon
  unfold lowBoundaryGen at ha
  unfold familyHighBoundary at hb
  have hν : ly - lx ≤ max 0 (ly - lx) := le_max_right _ _
  have hμ : (0 : ℝ) ≤ max 0 (lx + ly + 0 - 1) := le_max_left _ _
  generalize max 0 (ly - lx) = ν at ha hν
  generalize max 0 (lx + ly + 0 - 1) = μ at ha hμ
  linarith

/-- The value `31/34` is attained at `(lx, ly) = (5/17, 11/17)`. -/
theorem corner_family_attained :
    lowBoundary (5 / 17) (11 / 17) 0 = 31 / 34 ∧ familyHighBoundary (5 / 17) (11 / 17) = 31 / 34 := by
  refine ⟨?_, by norm_num [familyHighBoundary]⟩
  rw [lowBoundary_eq_rescaled (by norm_num)]
  norm_num

/-! ### Two reflections of the exponent plane -/

/-- Reflection of a row: the row length `r` is kept, the length `l` of the index becomes the dual
length `2r − l`. -/
def reflectScale (p : ℝ × ℝ) : ℝ × ℝ := (p.1, 2 * p.1 - p.2)

/-- Summation in the row index: the length `l` is kept, the row length `r` becomes `2l − r`. -/
def sumScale (p : ℝ × ℝ) : ℝ × ℝ := (2 * p.2 - p.1, p.2)

theorem reflectScale_involutive : Function.Involutive reflectScale := by
  rintro ⟨r, l⟩
  simp only [reflectScale, Prod.mk.injEq, true_and]
  ring

theorem sumScale_involutive : Function.Involutive sumScale := by
  rintro ⟨r, l⟩
  simp only [sumScale, Prod.mk.injEq, and_true]
  ring

/-- The product of the two reflections keeps `r − l` and moves both lengths by `2(r − l)`. -/
theorem sumScale_reflectScale (r l : ℝ) :
    sumScale (reflectScale (r, l)) = (r + 2 * (r - l), l + 2 * (r - l)) := by
  simp only [sumScale, reflectScale, Prod.mk.injEq]
  constructor <;> ring

/-- **The translation in scale.** -/
theorem iterate_sumScale_reflectScale (k : ℕ) (r l : ℝ) :
    (sumScale ∘ reflectScale)^[k] (r, l) = (r + 2 * k * (r - l), l + 2 * k * (r - l)) := by
  induction k generalizing r l with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.comp_apply, sumScale_reflectScale, ih]
    simp only [Prod.mk.injEq]
    push_cast
    constructor <;> ring

/-- Reflection, summation, reflection: the second description of the scale `(r, l)`. -/
theorem reflect_sum_reflect (r l : ℝ) :
    reflectScale (sumScale (reflectScale (r, l))) = (3 * r - 2 * l, 4 * r - 3 * l) := by
  simp only [sumScale, reflectScale, Prod.mk.injEq]
  constructor <;> ring

/-- The generic bound at the scale `(3M − 2, 4M − 3)` bounds `2β − 5/3` by
`(2/3 − M/2)/(4M − 3)`; on `3/4 < M ≤ 1` this is at least `1/6`, the value at `M = 1`. -/
theorem one_sixth_le_translated {M : ℝ} (h1 : 3 / 4 < M) (h2 : M ≤ 1) :
    1 / 6 ≤ (2 / 3 - M / 2) / (4 * M - 3) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem translated_at_one : (2 / 3 - (1 : ℝ) / 2) / (4 * 1 - 3) = 1 / 6 := by
  norm_num

/-- The boundary `1/3 + 7M/12` that an asymptotic on the short side would give without a deficit
of the other classes is below `5/6` for `M < 6/7`. -/
theorem deficit_free_boundary_lt {M : ℝ} (h : M < 6 / 7) : 1 / 3 + 7 * M / 12 < 5 / 6 := by
  linarith

/-- Exponent of the principal twists in the mean square of the Möbius sums over the twists of
norm up to `Z^{2 + 2ℓ − M}`, relative to its generic value: multiplicity one sixth of the family
length, amplitude `Z^{β + ℓ}`, index of length `Z^{1 + ℓ}`. -/
def principalRelativeSize (M ℓ β : ℝ) : ℝ := 2 * β + ℓ - 1 - 5 / 6 * (2 + 2 * ℓ - M)

/-- The excess of the principal twists in the mean square of the rows is their relative size
minus the window `M − 1 − ℓ` of the summation in the row index. -/
theorem principalExcess_eq_relativeSize_sub (M ℓ β : ℝ) :
    principalExcess M ℓ β = principalRelativeSize M ℓ β - (M - 1 - ℓ) := by
  unfold principalExcess principalRelativeSize
  ring

/-- At the published geometry: family length `3/2`, window `−1/3`, relative size
`2β − 25/12`. -/
theorem principalRelativeSize_published (β : ℝ) :
    principalRelativeSize (5 / 6) (1 / 6) β = 2 * β - 25 / 12 ∧
      (2 : ℝ) + 2 * (1 / 6) - 5 / 6 = 3 / 2 ∧ (5 / 6 : ℝ) - 1 - 1 / 6 = -(1 / 3) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  unfold principalRelativeSize
  ring

/-- In the range of the reflection the family is at least as long as `Z^{1 + 3ℓ}`. -/
theorem reflection_range_family_length {M ℓ : ℝ} (h : M + ℓ ≤ 1) :
    1 + 3 * ℓ ≤ 2 + 2 * ℓ - M := by
  linarith

/-- Rows as long as the marked index: the excess of the principal twists at `β = 1/2`. -/
theorem principalExcess_marked_length_half (ℓ : ℝ) :
    principalExcess (1 + ℓ) ℓ (1 / 2) = (ℓ - 5) / 6 := by
  unfold principalExcess
  ring

/-- Under the Riemann hypothesis for the family these rows are generic exactly for `ℓ ≤ 5`. -/
theorem principalExcess_marked_length_half_nonpos_iff (ℓ : ℝ) :
    principalExcess (1 + ℓ) ℓ (1 / 2) ≤ 0 ↔ ℓ ≤ 5 := by
  rw [principalExcess_marked_length_half]
  constructor <;> intro h <;> linarith

/-- At `ℓ = 5` the boundary of rows as long as the marked index is the line. -/
theorem lowBoundaryFree_marked_length_five {lx ly : ℝ} (h : lx ≤ ly) (hM : lx + ly = 1 + 5) :
    lowBoundaryFree lx ly 5 = 1 / 2 := by
  rw [lowBoundaryFree_marked_length h hM]
  norm_num

/-- The amplified mean square `P^{1/6} L^{11/6}` of the twists of norm up to `P = L²/R`, carried
to the rows by the summation in the row index (factor `R/L²`), is `R^{5/6} L^{1/6}`. -/
theorem amplified_rows (r l : ℝ) :
    (r - 2 * l) + (2 * l - r) / 6 + 11 * l / 6 = 5 * r / 6 + l / 6 := by
  ring

/-- For rows longer than the index it is at most the generic value `R`. -/
theorem amplified_rows_le {r l : ℝ} (h : l ≤ r) : 5 * r / 6 + l / 6 ≤ r := by
  linarith

/-! ### The sieve for the reflected rows -/

/-- The diagonal `P Z` of the positive form divided by the multiplicity `P^{1/6}` of the target,
`P = Z^θ`. -/
def diagonalExponent (θ : ℝ) : ℝ := 1 + 5 * θ / 6

/-- Contribution of a term `K^u N^v` of the large sieve for the reflected rows to the bound for
the square of the target in the positive form at family length `P = Z^θ`: rows `K = Z^{2 − θ}`,
dual length `N = K²/Z`, factor `Z²/K` from the summation in the row index, multiplicity
`P^{1/6}`. -/
def sieveTermExponent (u v θ : ℝ) : ℝ := θ + u * (2 - θ) + v * (3 - 2 * θ) - θ / 6

theorem sieveTermExponent_rows (θ : ℝ) : sieveTermExponent 1 0 θ = 2 - θ / 6 := by
  unfold sieveTermExponent
  ring

theorem sieveTermExponent_dual (θ : ℝ) : sieveTermExponent 0 1 θ = 3 - 7 * θ / 6 := by
  unfold sieveTermExponent
  ring

/-- With the optimal sieve `K + N` the family of length `θ = 1` gives `2β ≤ 11/6`. -/
theorem positiveForm_optimal :
    max (diagonalExponent 1) (max (sieveTermExponent 1 0 1) (sieveTermExponent 0 1 1)) =
      11 / 6 := by
  have h1 : diagonalExponent 1 = 11 / 6 := by norm_num [diagonalExponent]
  have h2 : sieveTermExponent 1 0 1 = 11 / 6 := by norm_num [sieveTermExponent]
  have h3 : sieveTermExponent 0 1 1 = 11 / 6 := by norm_num [sieveTermExponent]
  rw [h1, h2, h3, max_self, max_self]

/-- At the family length `6/5`, where the diagonal reaches the trivial `Z²`, a term `K^u N^v` has
the exponent `1 + (4u + 3v)/5`. -/
theorem sieveTermExponent_six_fifths (u v : ℝ) :
    sieveTermExponent u v (6 / 5) = 1 + (4 * u + 3 * v) / 5 := by
  unfold sieveTermExponent
  ring

/-- **The threshold of the row sieve.** A term `K^u N^v` with `4u + 3v ≥ 5` gives no half-plane:
at every family length the bound for the square of the target is at least the trivial `Z²`. -/
theorem two_le_of_sieve_threshold {u v : ℝ} (h : 5 ≤ 4 * u + 3 * v) (hs : 5 / 6 ≤ u + 2 * v)
    (θ : ℝ) : 2 ≤ max (diagonalExponent θ) (sieveTermExponent u v θ) := by
  rcases le_total (6 / 5) θ with hθ | hθ
  · refine le_max_of_le_left ?_
    unfold diagonalExponent
    linarith
  · refine le_max_of_le_right ?_
    unfold sieveTermExponent
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 6 / 5 - θ)
      (by linarith : (0 : ℝ) ≤ u + 2 * v - 5 / 6)]

/-- The term `K^{1/2} N` of the square row indices is on the threshold. -/
theorem two_le_of_square_rows (θ : ℝ) :
    2 ≤ max (diagonalExponent θ) (sieveTermExponent (1 / 2) 1 θ) :=
  two_le_of_sieve_threshold (by norm_num) (by norm_num) θ

/-- The term `N³/K`, one summation applied to the trivial bound, is on the threshold. -/
theorem two_le_of_one_summation (θ : ℝ) :
    2 ≤ max (diagonalExponent θ) (sieveTermExponent (-1) 3 θ) :=
  two_le_of_sieve_threshold (by norm_num) (by norm_num) θ

/-- The term `N²`, a bound for each character sum by the square root of its conductor, is past
the threshold. -/
theorem two_le_of_conductor_bound (θ : ℝ) :
    2 ≤ max (diagonalExponent θ) (sieveTermExponent 0 2 θ) :=
  two_le_of_sieve_threshold (by norm_num) (by norm_num) θ

theorem sieveTermExponent_two_thirds (θ : ℝ) :
    sieveTermExponent (2 / 3) (2 / 3) θ = 10 / 3 - 7 * θ / 6 := by
  unfold sieveTermExponent
  ring

/-- With a term `(KN)^{2/3}` no family length gives less than `71/36`. -/
theorem seventyone_thirtysixths_le (θ : ℝ) :
    71 / 36 ≤ max (diagonalExponent θ) (sieveTermExponent (2 / 3) (2 / 3) θ) := by
  rw [sieveTermExponent_two_thirds]
  rcases le_total (7 / 6) θ with hθ | hθ
  · refine le_max_of_le_left ?_
    unfold diagonalExponent
    linarith
  · refine le_max_of_le_right ?_
    linarith

/-- A sieve `K + N + (KN)^{2/3}` for the reflected rows gives `2β ≤ 71/36` at `θ = 7/6`. -/
theorem positiveForm_two_thirds :
    max (diagonalExponent (7 / 6)) (max (sieveTermExponent 1 0 (7 / 6))
      (max (sieveTermExponent 0 1 (7 / 6)) (sieveTermExponent (2 / 3) (2 / 3) (7 / 6)))) =
      71 / 36 := by
  have h1 : diagonalExponent (7 / 6) = 71 / 36 := by norm_num [diagonalExponent]
  have h2 : sieveTermExponent 1 0 (7 / 6) = 65 / 36 := by norm_num [sieveTermExponent]
  have h3 : sieveTermExponent 0 1 (7 / 6) = 59 / 36 := by norm_num [sieveTermExponent]
  have h4 : sieveTermExponent (2 / 3) (2 / 3) (7 / 6) = 71 / 36 := by
    norm_num [sieveTermExponent]
  rw [h1, h2, h3, h4, max_eq_right (by norm_num : (59 : ℝ) / 36 ≤ 71 / 36),
    max_eq_right (by norm_num : (65 : ℝ) / 36 ≤ 71 / 36), max_self]

/-- Exponent of the square of the direct estimate of the linear probe when the rows are bounded
by the sextic large sieve `Q + Z + (QZ)^{2/3}`, `Q = XY`, without the reflection: additive norm
`(Q + Y²)/Y` and the factor `1/Q`. -/
def directSexticExponent (lx ly : ℝ) : ℝ :=
  max lx ly + max (max (lx + ly) 1) (2 / 3 * (lx + ly + 1)) - (lx + ly)

/-- **Without the reflection the sextic large sieve gives no half-plane.** If the direct estimate
is below the square `X^{2/3} Z^{2β − 5/3}` of the principal term, then `β > 1`. -/
theorem one_lt_of_directSextic_lt {lx ly β : ℝ}
    (h : directSexticExponent lx ly < 2 * lx / 3 + 2 * β - 5 / 3) : 1 < β := by
  unfold directSexticExponent at h
  have h1 : lx ≤ max lx ly := le_max_left _ _
  have h2 : ly ≤ max lx ly := le_max_right _ _
  have h3 : lx + ly ≤ max (max (lx + ly) 1) (2 / 3 * (lx + ly + 1)) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have h4 : 2 / 3 * (lx + ly + 1) ≤ max (max (lx + ly) 1) (2 / 3 * (lx + ly + 1)) :=
    le_max_right _ _
  generalize max lx ly = a at h h1 h2
  generalize max (max (lx + ly) 1) (2 / 3 * (lx + ly + 1)) = b at h h3 h4
  linarith

/-- With the reflection and the optimal sieve the balanced geometry has the exponent `1/2`: the
direct estimate `Z^{1/4}` and the boundary `11/12`. -/
theorem balanced_direct_exponent (β : ℝ) :
    ((1 : ℝ) / 2 < 2 * (1 / 2) / 3 + 2 * β - 5 / 3) ↔ 11 / 12 < β := by
  constructor <;> intro h <;> linarith

end

end GaloisForLFunctions.FamilyContinuationTheory.Budget
