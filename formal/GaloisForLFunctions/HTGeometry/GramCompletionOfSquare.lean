import Mathlib

/-!
# Completing the square in a Gram matrix: a mixed block is a shifted Gram minus a quarter Gram

A weld construction that keeps one diagonal block and its forced mixed block, discarding the other
diagonal block, produces

```text
D = ∑ₙ cₙ ( uₙ uₙᵀ  +  ½ (uₙ vₙᵀ + vₙ uₙᵀ) ) ,
```

which is **not** a Gram matrix and has no inherited positivity.  Completing the square turns it into a
difference of two Grams:

```text
uuᵀ + ½(uvᵀ + vuᵀ)  =  (u + ½v)(u + ½v)ᵀ  −  ¼ v vᵀ .
```

So

> **`D ⪰ 0`  ⟺  `¼ · (Gram of v)  ⪯  (Gram of u + ½v)`**,

a Loewner comparison between two positive objects.  That is a strictly better-posed question than
"is the mixed block positive": both sides are manifestly positive semidefinite, and the content is a
domination, not a sign.

The identity is exact and holds entrywise for any weights and any features; positivity of the
weights is not needed for the identity, only for reading the two sides as Grams.
-/

open Finset

namespace GaloisForLFunctions

namespace GramSquare

variable {ι : Type*} {m : ℕ}

/-- The weighted Gram matrix of a family of feature vectors. -/
noncomputable def gram (F : Finset ι) (c : ι → ℝ) (u : ι → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => ∑ n ∈ F, c n * u n i * u n j

/-- The symmetrized mixed block of two feature families. -/
noncomputable def mixed (F : Finset ι) (c : ι → ℝ) (u v : ι → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => ∑ n ∈ F, c n * ((u n i * v n j + v n i * u n j) / 2)

/-- The shifted feature `u + ½v`. -/
noncomputable def shift (u v : ι → Fin m → ℝ) : ι → Fin m → ℝ :=
  fun n i => u n i + v n i / 2

/-- **Completion of the square for Gram blocks.**  The diagonal block plus its symmetrized mixed
block equals the Gram of the shifted feature minus a quarter of the other diagonal Gram.  Exact, for
arbitrary weights. -/
theorem gram_add_mixed_eq (F : Finset ι) (c : ι → ℝ) (u v : ι → Fin m → ℝ) :
    gram F c u + mixed F c u v
      = gram F c (shift u v) - (1 / 4 : ℝ) • gram F c v := by
  ext i j
  simp only [gram, mixed, shift, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **The positivity question, restated as a Loewner domination.**  The kept block is positive
semidefinite exactly when a quarter of the discarded Gram is dominated by the shifted Gram. -/
theorem gram_add_mixed_posSemidef_iff (F : Finset ι) (c : ι → ℝ) (u v : ι → Fin m → ℝ) :
    (gram F c u + mixed F c u v).PosSemidef
      ↔ ((gram F c (shift u v) - (1 / 4 : ℝ) • gram F c v).PosSemidef) := by
  rw [gram_add_mixed_eq]

/-- Both sides of the comparison are genuine Grams: with nonnegative weights the discarded block and
the shifted block are positive semidefinite, so the open question is a domination between two
positive objects rather than a sign. -/
theorem gram_posSemidef_of_nonneg (F : Finset ι) (c : ι → ℝ) (u : ι → Fin m → ℝ)
    (hc : ∀ n ∈ F, 0 ≤ c n) :
    ∀ x : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, x i * (gram F c u i j) * x j := by
  intro x
  have step1 : ∀ i j : Fin m, x i * (gram F c u i j) * x j
      = ∑ n ∈ F, c n * (x i * u n i) * (x j * u n j) := by
    intro i j
    simp only [gram, Matrix.of_apply]
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hswap : ∑ i, ∑ j, ∑ n ∈ F, c n * (x i * u n i) * (x j * u n j)
      = ∑ n ∈ F, ∑ i, ∑ j, c n * (x i * u n i) * (x j * u n j) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      (Finset.sum_comm :
        ∑ j : Fin m, ∑ n ∈ F, c n * (x i * u n i) * (x j * u n j)
          = ∑ n ∈ F, ∑ j : Fin m, c n * (x i * u n i) * (x j * u n j))]
    exact Finset.sum_comm
  have hsq : ∀ n : ι, ∑ i, ∑ j, c n * (x i * u n i) * (x j * u n j)
      = c n * (∑ i, x i * u n i) ^ 2 := by
    intro n
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  calc ∑ i, ∑ j, x i * (gram F c u i j) * x j
      = ∑ i, ∑ j, ∑ n ∈ F, c n * (x i * u n i) * (x j * u n j) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => step1 i j
    _ = ∑ n ∈ F, ∑ i, ∑ j, c n * (x i * u n i) * (x j * u n j) := hswap
    _ = ∑ n ∈ F, c n * (∑ i, x i * u n i) ^ 2 := Finset.sum_congr rfl fun n _ => hsq n
    _ ≥ 0 := Finset.sum_nonneg fun n hn => mul_nonneg (hc n hn) (sq_nonneg _)


/-! ### The quadratic form, and where the arithmetic enters

Evaluating the completed square on a test vector collapses it: with `aₙ = ⟨x,uₙ⟩` and
`bₙ = ⟨x,vₙ⟩`, so that `aₙ + bₙ = ⟨x,hₙ⟩` is the head pairing,

```text
⟨x, D x⟩ = ∑ₙ cₙ [ (aₙ + ½bₙ)² − ¼bₙ² ]  =  ∑ₙ cₙ aₙ (aₙ + bₙ) ,
```

**the successor–head correlation.**  When the two features are successive evaluations of one function,
`aₙ = Pₙ₊₁ − Pₙ` and `aₙ + bₙ = Pₙ₊₁`, and the elementary identity
`(b − a)b = ½(b − a)² + ½(b² − a²)` splits it into

```text
⟨x, D x⟩ = ½ ∑ₙ cₙ (Pₙ₊₁ − Pₙ)²   +   ½ ∑ₙ cₙ (Pₙ₊₁² − Pₙ²) .
```

The first sum is nonnegative for free.  The second is a **weighted telescoping sum**, and Abel
summation turns it into boundary terms minus `∑ₙ (cₙ₊₁ − cₙ) Pₙ₊₁²`.  For a von Mangoldt weight `c`
that difference oscillates — it is `+Λ` at a prime after a composite and `−Λ` at a composite after a
prime — so the sign of the whole form is governed by an explicit prime-side Abel sum against `P²`.

That is where the arithmetic enters, and it is the only place it does. -/

/-- The elementary split behind the decomposition: `(b − a)·b = ½(b − a)² + ½(b² − a²)`. -/
theorem sub_mul_self_split (a b : ℝ) :
    (b - a) * b = (b - a) ^ 2 / 2 + (b ^ 2 - a ^ 2) / 2 := by ring

/-- **The quadratic form of the completed square, as a difference-plus-telescope.**  For successive
evaluations `a n = P (n+1) − P n`, the form splits into a free nonnegative part and a weighted
telescoping part; only the second can be negative, and it carries the whole weight dependence. -/
theorem quadratic_form_split (F : Finset ℕ) (c : ℕ → ℝ) (P : ℕ → ℝ) :
    ∑ n ∈ F, c n * ((P (n + 1) - P n) * P (n + 1))
      = (∑ n ∈ F, c n * (P (n + 1) - P n) ^ 2) / 2
        + (∑ n ∈ F, c n * (P (n + 1) ^ 2 - P n ^ 2)) / 2 := by
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [sub_mul_self_split (P n) (P (n + 1))]
  ring

/-- The free half is nonnegative whenever the weights are. -/
theorem quadratic_form_free_part_nonneg (F : Finset ℕ) (c : ℕ → ℝ) (P : ℕ → ℝ)
    (hc : ∀ n ∈ F, 0 ≤ c n) :
    0 ≤ ∑ n ∈ F, c n * (P (n + 1) - P n) ^ 2 :=
  Finset.sum_nonneg fun n hn => mul_nonneg (hc n hn) (sq_nonneg _)

/-- **Sufficient condition.**  If the telescoping part is nonnegative — for instance for a
nondecreasing `P²` and nonnegative weights — the whole form is nonnegative, hence the Loewner
domination holds. -/
theorem quadratic_form_nonneg_of_telescope_nonneg (F : Finset ℕ) (c : ℕ → ℝ) (P : ℕ → ℝ)
    (hc : ∀ n ∈ F, 0 ≤ c n)
    (htel : 0 ≤ ∑ n ∈ F, c n * (P (n + 1) ^ 2 - P n ^ 2)) :
    0 ≤ ∑ n ∈ F, c n * ((P (n + 1) - P n) * P (n + 1)) := by
  rw [quadratic_form_split]
  have hfree := quadratic_form_free_part_nonneg F c P hc
  linarith


/-! ### The sign, settled: the successor–head form is indefinite

A single weighted source point already makes the form negative.  At one point the form is
`c·(P₁ − P₀)·P₁` with `P₀ = P t₀`, `P₁ = P t₁`, `t₀ < t₁`, and it is negative as soon as

```text
0 < P t₁ < P t₀ ,
```

i.e. as soon as the test function is positive at the later point and *decreasing* between the two.
For jets of positive depth the test functions satisfy `P 0 = 0`, which forbids a globally decreasing
positive `P` — but not a locally decreasing one.  The quadratic

```text
P t = t (a − t) ,       t₁ < a < t₀ + t₁ ,
```

does it: `P 0 = 0`, `P t₁ > 0` because `t₁ < a`, and `P t₀ − P t₁ = (t₀ − t₁)(a − t₀ − t₁) > 0`
because both factors are negative.  Such an `a` exists for every `0 < t₀ < t₁`, since
`t₁ < t₀ + t₁`.

So the successor–head correlation is **indefinite**, the Loewner domination of `gram_add_mixed_eq`
fails, and the subtractive block is not positive semidefinite. -/

/-- The two-point witness: a quadratic vanishing at `0` that is positive at `t₁` and larger at `t₀`. -/
theorem exists_quadratic_decreasing_positive {t₀ t₁ : ℝ} (h₀ : 0 < t₀) (h₁ : t₀ < t₁) :
    ∃ a : ℝ, t₁ < a ∧ a < t₀ + t₁ ∧
      (fun t : ℝ => t * (a - t)) 0 = 0 ∧
      0 < (fun t : ℝ => t * (a - t)) t₁ ∧
      (fun t : ℝ => t * (a - t)) t₁ < (fun t : ℝ => t * (a - t)) t₀ := by
  refine ⟨t₁ + t₀ / 2, by linarith, by linarith, by simp, ?_, ?_⟩
  · have ht₁ : 0 < t₁ := lt_trans h₀ h₁
    have : 0 < t₁ + t₀ / 2 - t₁ := by linarith
    exact mul_pos ht₁ this
  · have hfac : t₀ * (t₁ + t₀ / 2 - t₀) - t₁ * (t₁ + t₀ / 2 - t₁)
        = (t₀ - t₁) * ((t₁ + t₀ / 2) - t₀ - t₁) := by ring
    nlinarith [hfac, sub_neg.mpr h₁]

/-- **The successor–head form is indefinite.**  At a single weighted point with `0 < c`, the value
`c · (P t₁ − P t₀) · P t₁` is strictly negative for the witness of
`exists_quadratic_decreasing_positive`.  Hence the completed-square block of `gram_add_mixed_eq` is
not positive semidefinite in general. -/
theorem successorHead_form_neg {t₀ t₁ c : ℝ} (h₀ : 0 < t₀) (h₁ : t₀ < t₁) (hc : 0 < c) :
    ∃ P : ℝ → ℝ, P 0 = 0 ∧ c * ((P t₁ - P t₀) * P t₁) < 0 := by
  obtain ⟨a, _, _, hzero, hpos, hlt⟩ := exists_quadratic_decreasing_positive h₀ h₁
  refine ⟨fun t : ℝ => t * (a - t), hzero, ?_⟩
  have hneg : (fun t : ℝ => t * (a - t)) t₁ - (fun t : ℝ => t * (a - t)) t₀ < 0 := by linarith
  have := mul_neg_of_neg_of_pos hneg hpos
  exact mul_neg_of_pos_of_neg hc this


/-! ### The whole class of block combinations, and why finiteness and positivity exclude each other

The weld keeps `α = 1`, `β = 1`, `γ = 0` in

```text
α·uuᵀ + β·½(uvᵀ + vuᵀ) + γ·vvᵀ .
```

Since the pairings `⟨x,uₙ⟩` and `⟨x,vₙ⟩` are unconstrained, positivity of such a combination against
every feature family is exactly positivity of the scalar form `α a² + β a b + γ b²`, i.e. the `2 × 2`
discriminant condition

```text
0 ≤ α ,   0 ≤ γ ,   β² ≤ 4αγ .
```

Hence **`γ = 0` forces `β = 0`**: discarding the second diagonal block entirely forbids keeping any
mixed block.  That is the trade-off in full:

* the mixed block is what cancels the successor curvature defect (`…Cross_firstCurvature_pos`
  against `…FiniteGram_firstCurvature_neg`);
* keeping any of it requires keeping at least `β²/(4α)` of the second diagonal block;
* and the second diagonal block is the divergent one that had to be discarded for finiteness.

So no linear combination of the three blocks is simultaneously finite and positive with a
curvature-cancelling mixed term.  This closes the class, not merely the weld. -/

/-- **The block-combination criterion.**  A combination `α a² + β ab + γ b²` is nonnegative for all
pairings exactly when the `2 × 2` discriminant condition holds. -/
theorem blockCombination_nonneg_iff (α β γ : ℝ) :
    (∀ a b : ℝ, 0 ≤ α * a ^ 2 + β * a * b + γ * b ^ 2)
      ↔ (0 ≤ α ∧ 0 ≤ γ ∧ β ^ 2 ≤ 4 * α * γ) := by
  constructor
  · intro h
    refine ⟨by simpa using h 1 0, by simpa using h 0 1, ?_⟩
    by_contra hcon
    rw [not_le] at hcon
    have hα : 0 ≤ α := by simpa using h 1 0
    rcases eq_or_lt_of_le hα with hα0 | hαpos
    · -- α = 0 : then the form is β a b + γ b², unbounded below in a unless β = 0
      have hγ : 0 ≤ γ := by simpa using h 0 1
      have hβ : β = 0 := by
        by_contra hβ0
        have h1 := h (-(γ + 1) / β) 1
        have hcalc : α * (-(γ + 1) / β) ^ 2 + β * (-(γ + 1) / β) * 1 + γ * 1 ^ 2 = -1 := by
          rw [← hα0]
          field_simp
          ring
        rw [hcalc] at h1
        norm_num at h1
      rw [← hα0, hβ] at hcon
      norm_num at hcon
    · -- α > 0 : evaluate at the vertex
      have hvert := h (-β / (2 * α)) 1
      have hne : (2 : ℝ) * α ≠ 0 := by positivity
      field_simp at hvert
      nlinarith [hvert, hαpos]
  · rintro ⟨hα, hγ, hdisc⟩ a b
    rcases eq_or_lt_of_le hα with hα0 | hαpos
    · have hβ : β = 0 := by nlinarith [hdisc, sq_nonneg β]
      rw [← hα0, hβ]
      nlinarith [hγ, sq_nonneg b]
    · nlinarith [sq_nonneg (2 * α * a + β * b), hαpos, hdisc, sq_nonneg b]

/-- **Discarding the second diagonal block forbids any mixed block.**  If the combination is
nonnegative for all pairings and `γ = 0`, then `β = 0`. -/
theorem mixed_vanishes_of_second_block_discarded {α β : ℝ}
    (h : ∀ a b : ℝ, 0 ≤ α * a ^ 2 + β * a * b + 0 * b ^ 2) : β = 0 := by
  obtain ⟨_, _, hdisc⟩ := (blockCombination_nonneg_iff α β 0).mp h
  nlinarith [hdisc, sq_nonneg β]

/-- **The trade-off, stated.**  A positive block combination that keeps a nonzero mixed block must
retain a positive share of the second diagonal block. -/
theorem second_block_pos_of_mixed_ne_zero {α β γ : ℝ} (hβ : β ≠ 0)
    (h : ∀ a b : ℝ, 0 ≤ α * a ^ 2 + β * a * b + γ * b ^ 2) : 0 < γ := by
  obtain ⟨hα, hγ, hdisc⟩ := (blockCombination_nonneg_iff α β γ).mp h
  rcases eq_or_lt_of_le hγ with hγ0 | hγpos
  · exfalso
    rw [← hγ0] at hdisc
    have : β ^ 2 ≤ 0 := by nlinarith [hdisc]
    exact hβ (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg β)))
  · exact hγpos


/-! ### The last branch: features with no defect are power families, and those do not converge

The mixed block exists to repair a **Hankel** defect, not a positivity defect: a weighted Gram
`G i j = ∑ₙ cₙ uₙ(i) uₙ(j)` is automatically positive semidefinite, but it is a *moment* matrix only
when it depends on `i + j` alone.  Power features do that for free:

```text
uₙ(i) = tₙ^i    ⟹    G i j = ∑ₙ cₙ tₙ^{i+j} ,
```

Hankel and positive semidefinite with no correction at all — so a power family has **no defect to
cancel**, and needs no mixed block.

That closes the last branch, but by circularity rather than by a new obstruction.  A finite positive
semidefinite Hankel matrix *is* a truncated moment matrix (Hamburger), i.e. it is representable by a
power family against a positive measure.  So "a feature pair with no curvature defect" is exactly
"the Gram is already the moment matrix of a positive measure" — which for the prime-side data is the
conclusion being sought, not a route to it.  And the power family that would represent it,
`tₙ = log n` against the von Mangoldt weight, is precisely the divergent object the differencing was
introduced to repair. -/

/-- **Power features give a Hankel Gram.**  The entries depend on `i + j` alone. -/
theorem gram_power_isHankel (F : Finset ι) (c : ι → ℝ) (t : ι → ℝ) (i j i' j' : Fin m)
    (h : (i : ℕ) + (j : ℕ) = (i' : ℕ) + (j' : ℕ)) :
    gram F c (fun n k => t n ^ (k : ℕ)) i j = gram F c (fun n k => t n ^ (k : ℕ)) i' j' := by
  simp only [gram, Matrix.of_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add, h]

/-- With nonnegative weights a power-feature Gram is a positive semidefinite Hankel matrix, so it
carries no defect for a mixed block to repair. -/
theorem gram_power_nonneg (F : Finset ι) (c : ι → ℝ) (t : ι → ℝ)
    (hc : ∀ n ∈ F, 0 ≤ c n) (x : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * (gram F c (fun n k => t n ^ (k : ℕ)) i j) * x j :=
  gram_posSemidef_of_nonneg F c (fun n k => t n ^ (k : ℕ)) hc x

end GramSquare

end GaloisForLFunctions
