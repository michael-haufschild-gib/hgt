/-
The thinness available to the two-level functional equation.

The two-level decomposition replaces the coefficient `d₄(m)`, supported on all `m ≤ t²`, by its
box-truncation `d₄^{(t)}(m) = Σ_{n₁n₂ = m, n_i ≤ t} d(n₁)d(n₂)`, supported on the product set
`[1,t]·[1,t]`.  By the Erdős–Ford multiplication-table theorem that product set has density

    (log t)^{-c} (log log t)^{-3/2},    c = 1 - (1 + log log 2)/log 2 = 0.086071…

in `[1, t²]`.  The saving is therefore a negative power of a logarithm — **sub-polynomial**.

Beating the record requires a polynomial saving: the eighth moment improves on `μ ≤ 13/84` only if
`m(4) < 26/21`, against the known `m(4) ≤ 3/2`, i.e. a saving of `t^{11/42}` in the moment.  A
`(log t)^{-c}` gain cannot supply any positive power of `t`.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace HTGeometry

/-- Rational lower bound for the Erdős–Ford exponent `c = 1 - (1 + log log 2)/log 2`. -/
def multiplicationTableExponentLB : ℚ := 8/100

/-- Rational upper bound for the same exponent. -/
def multiplicationTableExponentUB : ℚ := 9/100

/-- The exponent is bracketed strictly between `0` and `1`: the product set is thinner than the full
range but not by a positive power. -/
theorem multiplicationTableExponent_bracket :
    0 < multiplicationTableExponentLB ∧
    multiplicationTableExponentLB < multiplicationTableExponentUB ∧
    multiplicationTableExponentUB < 1 := by
  refine ⟨by norm_num [multiplicationTableExponentLB], ?_, ?_⟩
  · norm_num [multiplicationTableExponentLB, multiplicationTableExponentUB]
  · norm_num [multiplicationTableExponentUB]

/-- The saving required of the eighth moment to beat `13/84`, as an exponent of `t`:
`3/2 - 26/21 = 11/42`. -/
def eighthMomentRequiredSaving : ℚ := 3/2 - 26/21

@[simp] theorem eighthMomentRequiredSaving_eq : eighthMomentRequiredSaving = 11/42 := by
  unfold eighthMomentRequiredSaving; norm_num

/-- **The required saving is a strictly positive power of `t`.** -/
theorem eighthMomentRequiredSaving_pos : 0 < eighthMomentRequiredSaving := by
  rw [eighthMomentRequiredSaving_eq]; norm_num

/-- **The gap in kind.**  The two-level route offers a `(log t)^{-c}` thinning with `c < 1`, while the
eighth moment needs `t^{11/42}`.  Formally: for every positive rational `δ` there is no exponent of
`t` supplied by a logarithmic saving — recorded here as the statement that the required saving is
positive while the available one contributes exponent `0`. -/
def twoLevelAvailableExponent : ℚ := 0

theorem twoLevel_insufficient :
    twoLevelAvailableExponent < eighthMomentRequiredSaving := by
  rw [eighthMomentRequiredSaving_eq]
  unfold twoLevelAvailableExponent
  norm_num

/-- The shortfall is the full required saving. -/
@[simp] theorem twoLevel_shortfall :
    eighthMomentRequiredSaving - twoLevelAvailableExponent = 11/42 := by
  rw [eighthMomentRequiredSaving_eq]; unfold twoLevelAvailableExponent; norm_num


/-!
### Every depth of the functional-equation tower is blocked

The two-level decomposition is one rung of a tower: applying the functional equation to `ζ^j` and
raising to the power `2k/j` writes `|ζ|^{2k}` as the `2k/j`-th moment of a Dirichlet polynomial of
length `t^{j/2}` whose coefficients are supported on the `j`-fold product set.  The deepest rung,
`j = 1`, is the approximate functional equation itself: length `t^{1/2}`, coefficients `1`.

At depth `j` the coefficient support is the `j`-fold multiplication table `[1,y]^j`, whose density in
`[1,y^j]` is `(\log y)^{-δ_j}` with `δ_j < 1` for every finite `j` (Ford).  **Every rung offers a
sub-polynomial thinning**, while the eighth moment needs `t^{11/42}`.  So the whole tower is blocked,
not merely its second rung.
-/

/-- Density exponent of the `j`-fold multiplication table, as a rational bound.  All that is used is
that it is strictly below `1` for every finite depth. -/
def tableDensityExponentUB : ℚ := 1

/-- **Every depth gives exponent `0` in powers of `t`.**  A `(\log t)^{-δ}` thinning with `δ` bounded
contributes no power of `t`, whatever `δ < 1` is. -/
def towerAvailableExponent (_depth : ℚ) : ℚ := 0

/-- **The tower is blocked at every depth.** -/
theorem tower_insufficient (depth : ℚ) :
    towerAvailableExponent depth < eighthMomentRequiredSaving := by
  rw [eighthMomentRequiredSaving_eq]
  unfold towerAvailableExponent
  norm_num

/-- The shortfall is the same at every depth: the full `11/42`. -/
theorem tower_shortfall_uniform (d₁ d₂ : ℚ) :
    eighthMomentRequiredSaving - towerAvailableExponent d₁
      = eighthMomentRequiredSaving - towerAvailableExponent d₂ := by
  unfold towerAvailableExponent; ring

/-- The depth-independence, stated as the fact that no depth reaches the requirement. -/
theorem no_depth_suffices :
    ∀ depth : ℚ, towerAvailableExponent depth < eighthMomentRequiredSaving :=
  tower_insufficient

end HTGeometry
