/-
The critical length is the unique length at which the pricing functional's null direction is an
eigenvector of the functional equation.

At length `M = T^(x₀)` the covering demand of an exponent pair is the affine functional

    demand(κ, λ, x₀) = (1 - x₀)·κ + x₀·λ - x₀/2 ,

whose gradient in `(κ, λ)` is `(1 - x₀, x₀)` and whose null direction — the direction along which the
demand does not change — is `(x₀, x₀ - 1)`.

The van der Corput `B`-process `B(κ, λ) = (λ - 1/2, κ + 1/2)` is affine with linear part the
coordinate swap, so it acts on directions by `(u, v) ↦ (v, u)`.  That swap has eigenvalue `+1` on
`(1, 1)` and `-1` on `(1, -1)`.

The two structures meet exactly once:

    **the null direction `(x₀, x₀ - 1)` is an eigenvector of the swap if and only if `x₀ = 1/2`,**

and there it is the `(-1)`-eigenvector.  So at the critical length — and only there — the directions
in which the exponent-pair region can be enlarged without changing the demand are precisely the
directions the functional equation reverses.  Motions in the `B`-invariant direction `(1, 1)` change
`κ + λ`, hence change `μ`; motions in the null direction change nothing.

This is why every conjugation-type mechanism is worth nothing at the critical length, and it isolates
what a genuinely new mechanism must supply: a datum on which `B` acts with eigenvalue `+1` and which
is not a function of `κ + λ`.  In a two-dimensional region there is no such datum, so the bound must
depend on data beyond the pair `(|f'|, N)`.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import GaloisForLFunctions.HTGeometry.LengthReflectionLaw

namespace HTGeometry

/-! ### The gradient and the null direction -/

/-- First component of the demand's gradient in `(κ, λ)`. -/
def demandGradFst (x₀ : ℚ) : ℚ := 1 - x₀

/-- Second component of the demand's gradient. -/
def demandGradSnd (x₀ : ℚ) : ℚ := x₀

/-- First component of the direction along which the demand is constant. -/
def demandNullFst (x₀ : ℚ) : ℚ := x₀

/-- Second component of that direction. -/
def demandNullSnd (x₀ : ℚ) : ℚ := x₀ - 1

/-- **The demand is affine, with the stated gradient.** -/
theorem covDemand_directional (x₀ κ lam u v s : ℚ) :
    covDemandOfPair x₀ (κ + s * u) (lam + s * v)
      = covDemandOfPair x₀ κ lam + s * (demandGradFst x₀ * u + demandGradSnd x₀ * v) := by
  unfold covDemandOfPair covFunctional demandGradFst demandGradSnd; ring

/-- **The null direction is annihilated by the gradient.** -/
@[simp] theorem gradient_dot_null (x₀ : ℚ) :
    demandGradFst x₀ * demandNullFst x₀ + demandGradSnd x₀ * demandNullSnd x₀ = 0 := by
  unfold demandGradFst demandGradSnd demandNullFst demandNullSnd; ring

/-- Moving a pair along the null direction leaves the demand unchanged. -/
theorem covDemand_invariant_along_null (x₀ κ lam s : ℚ) :
    covDemandOfPair x₀ (κ + s * demandNullFst x₀) (lam + s * demandNullSnd x₀)
      = covDemandOfPair x₀ κ lam := by
  rw [covDemand_directional, gradient_dot_null]; ring

/-- The null direction is never the zero direction. -/
theorem null_direction_nonzero (x₀ : ℚ) :
    demandNullFst x₀ ≠ 0 ∨ demandNullSnd x₀ ≠ 0 := by
  unfold demandNullFst demandNullSnd
  by_cases h : x₀ = 0
  · right; rw [h]; norm_num
  · left; exact h

/-! ### `B` acts on directions by the coordinate swap -/

/-- **The `B`-process is affine with linear part the coordinate swap.** -/
theorem procB_directional (κ lam u v s : ℚ) :
    procB_fst (lam + s * v) = procB_fst lam + s * v ∧
      procB_snd (κ + s * u) = procB_snd κ + s * u := by
  constructor
  · unfold procB_fst; ring
  · unfold procB_snd; ring

/-- **Hence a direction `(u, v)` becomes `(v, u)` after `B`**, as read off from the demand. -/
theorem covDemand_directional_after_procB (x₀ κ lam u v s : ℚ) :
    covDemandOfPair x₀ (procB_fst (lam + s * v)) (procB_snd (κ + s * u))
      = covDemandOfPair x₀ (procB_fst lam) (procB_snd κ)
        + s * (demandGradFst x₀ * v + demandGradSnd x₀ * u) := by
  unfold covDemandOfPair covFunctional procB_fst procB_snd demandGradFst demandGradSnd; ring

/-- A direction is an eigenvector of the swap with eigenvalue `c`. -/
def swapEigen (u v c : ℚ) : Prop := v = c * u ∧ u = c * v

/-- The `(+1)`-eigenvector of the swap. -/
theorem swapEigen_one : swapEigen 1 1 1 := by
  constructor <;> norm_num

/-- The `(-1)`-eigenvector of the swap. -/
theorem swapEigen_neg_one : swapEigen 1 (-1) (-1) := by
  constructor <;> norm_num

/-! ### The characterisation of the critical length -/

/-- **The null direction of the demand is an eigenvector of the functional equation's action if and
only if the length is the critical one.** -/
theorem null_direction_eigen_iff_critical (x₀ : ℚ) :
    (∃ c : ℚ, swapEigen (demandNullFst x₀) (demandNullSnd x₀) c) ↔ x₀ = 1 / 2 := by
  unfold swapEigen demandNullFst demandNullSnd
  constructor
  · rintro ⟨c, h1, h2⟩
    have hx : x₀ ≠ 0 := by
      intro h
      rw [h] at h1
      norm_num at h1
    have hsq : x₀ = c * (c * x₀) := by rw [h1] at h2; exact h2
    have hc : c ^ (2 : ℕ) = 1 := by
      have : x₀ * (c ^ (2 : ℕ) - 1) = 0 := by nlinarith [hsq]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hx
      · linarith
    have : c = 1 ∨ c = -1 := by
      have : (c - 1) * (c + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    rcases this with h | h
    · rw [h] at h1; linarith
    · rw [h] at h1; linarith
  · intro h
    refine ⟨-1, ?_, ?_⟩ <;> rw [h] <;> norm_num

/-- **At the critical length the null direction is the `(-1)`-eigenvector**: the exponent-pair
directions that cost nothing are exactly the directions the functional equation reverses. -/
theorem null_direction_at_critical :
    demandNullFst (1 / 2) = 1 / 2 ∧ demandNullSnd (1 / 2) = -(1 / 2) ∧
      swapEigen (demandNullFst (1 / 2)) (demandNullSnd (1 / 2)) (-1) := by
  refine ⟨by unfold demandNullFst; norm_num, by unfold demandNullSnd; norm_num, ?_⟩
  unfold swapEigen demandNullFst demandNullSnd; constructor <;> norm_num

/-- **The `B`-invariant direction changes `κ + λ`, hence changes `μ`.**  Motion in the direction the
functional equation preserves is the only motion that is priced at the critical length. -/
theorem invariant_direction_moves_mu (κ lam s : ℚ) :
    epMu (κ + s) (lam + s) = epMu κ lam + s := by
  unfold epMu; ring

/-- **And motion in the null direction leaves `μ` fixed while moving the displacement.** -/
theorem null_direction_moves_only_displacement (κ lam s : ℚ) :
    epMu (κ + s) (lam - s) = epMu κ lam ∧
      epDisplacement (κ + s) (lam - s) = epDisplacement κ lam - 2 * s := by
  constructor
  · unfold epMu; ring
  · unfold epDisplacement; ring

/-- **The classification.**  In the two-dimensional exponent-pair region the demand at the critical
length depends only on `μ`; every direction that is not detected by `μ` is exactly the direction the
functional equation reverses.  So no enlargement of the region within these two coordinates can lower
the demand at the critical length without lowering `μ` itself. -/
theorem critical_demand_determined_by_mu (κ lam : ℚ) :
    covDemandOfPair (1 / 2) κ lam = epMu κ lam ∧
      (∀ s : ℚ, covDemandOfPair (1 / 2) (κ + s) (lam - s) = covDemandOfPair (1 / 2) κ lam) := by
  refine ⟨displacement_free_at_critical_length κ lam, fun s => ?_⟩
  rw [displacement_free_at_critical_length, displacement_free_at_critical_length,
    (null_direction_moves_only_displacement κ lam s).1]

/-! ### The covering floor against the semigroup's own limit

The `A`-iteration of the exponent-pair recursion has limit `(√5 - 1)/8`, the positive root of
`16μ² + 4μ - 1`.  The covering floor `277/1792` lies strictly above it, by an amount certified
without irrational arithmetic. -/

/-- The rational comparison certifying `277/1792 > (√5 - 1)/8`, namely `501/224 > √5`. -/
theorem covering_floor_above_semigroup_limit :
    (501 : ℤ) ^ (2 : ℕ) - 5 * 224 ^ (2 : ℕ) = 121 ∧ (277 : ℚ) / 1792 = (501 / 224 - 1) / 8 := by
  constructor
  · norm_num
  · norm_num

/-- **Hence the covering floor exceeds the `A`-iteration limit.**  Since `501² > 5·224²`, the rational
`501/224` exceeds `√5`, and `277/1792 = (501/224 - 1)/8 > (√5 - 1)/8`. -/
theorem semigroup_limit_lt_covering_floor :
    (Real.sqrt 5 - 1) / 8 < 277 / 1792 := by
  have h5 : Real.sqrt 5 < 501 / 224 := by
    have hnn : (0:ℝ) ≤ 501 / 224 := by norm_num
    have := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 5)
      (by norm_num : (5:ℝ) < (501 / 224) ^ (2 : ℕ))
    calc Real.sqrt 5 < Real.sqrt ((501 / 224) ^ (2 : ℕ)) := this
      _ = 501 / 224 := by rw [Real.sqrt_sq hnn]
  linarith

end HTGeometry
