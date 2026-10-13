import Mathlib

/-!
# The Conrey–Ghosh–Gonek mollifier ratio: optimum and Feng orthogonality

For the simple-zero ratio `|Σ_γ ζ'M(ρ)|² / (N(T) Σ_γ |ζ'M(ρ)|²)` with mollifier
`M(s) = Σ_{h ≤ T^θ} μ(h) P(log(T^θ/h)/log T^θ) h^{−s}`, `P(0) = 0`, `P(1) = 1`, the main terms are
`S₁ = ½ + θI` and `S₂ = 1/3 + θI + θ²I² + J/(12θ)` with `I = ∫₀¹ P`, `J = ∫₀¹ P'²`, and
`J ≥ 1 + 12 (I − ½)²`.  This file proves the algebra of that problem.

* `sos_identity`: `((1+θ)³ − 1) S₂(I, 1 + 12(I−½)²) − (1+θ)³ S₁² = 3(1+θ)(I − (θ+3)/6)²`.
* `ratio_le` and `ratio_eq_of_opt`: `S₁²/S₂ ≤ 1 − (1+θ)⁻³`, with equality at `I = (θ+3)/6`, `J = 1 + θ²/3`
  (the quadratic `P(z) = z + θz(1 − z)`).
* `three_quarters_le_iff`, `ratio_bound_four_sevenths`: the bound reaches `3/4` iff `(1+θ)³ ≥ 4`; at `θ = 4/7` it is
  `988/1331 < 3/4`.
* `le_of_critical`: for a positive semidefinite symmetric form `G` and a linear functional `ℓ`, a point `v` with
  `G(v, ·) = c ℓ` maximises `ℓ(x)²/G(x, x)`.  Applied to the mollifier enlarged by the piece
  `μ(h) (Σ_{p∣h} log² p / log² T^θ) Q(·)`, whose cross term with `P*` has the kernel `fengKernel` and whose first
  moment has the kernel `θ s² − (θ²/6) s³` (in `s = 1 − t`),
* `fengKernel_eq`: `fengKernel = ((1+θ)³/(6θ)) (θ s² − (θ²/6) s³)` identically, so `P*` stays the global optimum:
  the enlarged mollifier gives no gain.
-/

noncomputable section

namespace RHTower

namespace CGGMollifier

/-- The first-moment main term `½ + θI`. -/
def numer (θ I : ℝ) : ℝ := 1 / 2 + θ * I

/-- The second-moment main term `1/3 + θI + θ²I² + J/(12θ)`. -/
def denom (θ I J : ℝ) : ℝ := 1 / 3 + θ * I + θ ^ 2 * I ^ 2 + J / (12 * θ)

/-- **Sum of squares behind the Conrey–Ghosh–Gonek optimum.** -/
theorem sos_identity {θ : ℝ} (hθ : θ ≠ 0) (I : ℝ) :
    ((1 + θ) ^ 3 - 1) * denom θ I (1 + 12 * (I - 1 / 2) ^ 2) - (1 + θ) ^ 3 * numer θ I ^ 2
      = 3 * (1 + θ) * (I - (θ + 3) / 6) ^ 2 := by
  unfold denom numer
  field_simp
  ring

theorem denom_pos {θ : ℝ} (hθ : 0 < θ) (I : ℝ) {J : ℝ} (hJ : 1 + 12 * (I - 1 / 2) ^ 2 ≤ J) :
    0 < denom θ I J := by
  unfold denom
  have h1 : 0 < J / (12 * θ) := div_pos (by nlinarith [sq_nonneg (I - 1 / 2)]) (by positivity)
  nlinarith [sq_nonneg (θ * I + 1 / 2)]

/-- `(1+θ)³ S₁² ≤ ((1+θ)³ − 1) S₂`. -/
theorem numer_sq_le {θ : ℝ} (hθ : 0 < θ) (I : ℝ) {J : ℝ} (hJ : 1 + 12 * (I - 1 / 2) ^ 2 ≤ J) :
    (1 + θ) ^ 3 * numer θ I ^ 2 ≤ ((1 + θ) ^ 3 - 1) * denom θ I J := by
  have hs := sos_identity hθ.ne' I
  have hmono : denom θ I (1 + 12 * (I - 1 / 2) ^ 2) ≤ denom θ I J := by
    unfold denom
    have : (1 + 12 * (I - 1 / 2) ^ 2) / (12 * θ) ≤ J / (12 * θ) :=
      div_le_div_of_nonneg_right hJ (by positivity)
    linarith
  have hc : 0 < (1 + θ) ^ 3 - 1 := by nlinarith [sq_nonneg θ]
  nlinarith [mul_le_mul_of_nonneg_left hmono hc.le, sq_nonneg (I - (θ + 3) / 6)]

/-- **The Conrey–Ghosh–Gonek law** `S₁²/S₂ ≤ 1 − (1+θ)⁻³`. -/
theorem ratio_le {θ : ℝ} (hθ : 0 < θ) (I : ℝ) {J : ℝ} (hJ : 1 + 12 * (I - 1 / 2) ^ 2 ≤ J) :
    numer θ I ^ 2 / denom θ I J ≤ 1 - 1 / (1 + θ) ^ 3 := by
  have hD := denom_pos hθ I hJ
  have h3 : 0 < (1 + θ) ^ 3 := by positivity
  rw [div_le_iff₀ hD, one_sub_div h3.ne', div_mul_eq_mul_div, le_div_iff₀ h3]
  nlinarith [numer_sq_le hθ I hJ]

/-- The bound is attained by `P(z) = z + θz(1 − z)`: `I = (θ+3)/6`, `J = 1 + θ²/3`. -/
theorem ratio_eq_of_opt {θ : ℝ} (hθ : 0 < θ) :
    numer θ ((θ + 3) / 6) ^ 2 / denom θ ((θ + 3) / 6) (1 + θ ^ 2 / 3) = 1 - 1 / (1 + θ) ^ 3 := by
  have hJ : 1 + 12 * ((θ + 3) / 6 - 1 / 2) ^ 2 = 1 + θ ^ 2 / 3 := by ring
  have hD := denom_pos hθ ((θ + 3) / 6) hJ.le
  have hs := sos_identity hθ.ne' ((θ + 3) / 6)
  rw [hJ] at hs
  have h3 : 0 < (1 + θ) ^ 3 := by positivity
  rw [div_eq_iff hD.ne', one_sub_div h3.ne', div_mul_eq_mul_div, eq_div_iff h3.ne']
  nlinarith [hs]

theorem three_quarters_le_iff {θ : ℝ} (hθ : 0 < θ) :
    3 / 4 ≤ 1 - 1 / (1 + θ) ^ 3 ↔ 4 ≤ (1 + θ) ^ 3 := by
  have h3 : 0 < (1 + θ) ^ 3 := by positivity
  have e : 1 - 1 / (1 + θ) ^ 3 = ((1 + θ) ^ 3 - 1) / (1 + θ) ^ 3 := by field_simp
  rw [e, le_div_iff₀ h3]
  constructor <;> intro h <;> linarith

/-- At the Kloosterman length `θ = 4/7` the law gives `988/1331 < 3/4`. -/
theorem ratio_bound_four_sevenths :
    1 - 1 / (1 + (4 / 7 : ℝ)) ^ 3 = 988 / 1331 ∧ (988 / 1331 : ℝ) < 3 / 4 := by
  constructor <;> norm_num

/-- **Cauchy–Schwarz for a positive semidefinite symmetric bilinear form.** -/
theorem sq_le_mul_of_psd {V : Type*} [AddCommGroup V] [Module ℝ V] (G : LinearMap.BilinForm ℝ V)
    (hsymm : ∀ x y, G x y = G y x) (hpsd : ∀ x, 0 ≤ G x x) (x y : V) :
    G x y ^ 2 ≤ G x x * G y y := by
  have h : ∀ t : ℝ, 0 ≤ G y y * (t * t) + 2 * G x y * t + G x x := by
    intro t
    have := hpsd (x + t • y)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at this
    rw [hsymm y x] at this
    linarith
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith

/-- **A critical point of `ℓ(x)²/G(x, x)` is its maximum.**  If `G(v, x) = c ℓ(x)` for every `x`, then
`ℓ(x)² G(v, v) ≤ ℓ(v)² G(x, x)` for every `x`. -/
theorem le_of_critical {V : Type*} [AddCommGroup V] [Module ℝ V] (G : LinearMap.BilinForm ℝ V)
    (hsymm : ∀ x y, G x y = G y x) (hpsd : ∀ x, 0 ≤ G x x) (ℓ : V →ₗ[ℝ] ℝ) {v : V} {c : ℝ}
    (hcrit : ∀ x, G v x = c * ℓ x) (x : V) :
    ℓ x ^ 2 * G v v ≤ ℓ v ^ 2 * G x x := by
  have hcs := sq_le_mul_of_psd G hsymm hpsd v x
  rw [hcrit x, hcrit v] at hcs
  have hvv : G v v = c * ℓ v := hcrit v
  have hpos : 0 ≤ c * ℓ v := hvv ▸ hpsd v
  rw [hvv]
  rcases hpos.lt_or_eq with hp | hp
  · have hxx := hpsd x
    have key : (c * ℓ v) * (ℓ x ^ 2 * (c * ℓ v)) ≤ (c * ℓ v) * (ℓ v ^ 2 * G x x) := by
      nlinarith [mul_le_mul_of_nonneg_left hcs (sq_nonneg (ℓ v))]
    exact le_of_mul_le_mul_left key hp
  · rw [← hp, mul_zero]
    exact mul_nonneg (sq_nonneg _) (hpsd x)

/-- The cross kernel of the piece `μ(h) (Σ_{p∣h} log² p / log² T^θ) Q` against `P*(z) = z + θz(1 − z)`, in the
variable `s = 1 − t`: the sum of the fourteen evaluated main-term integrals, with `I = ∫ P* = (θ + 3)/6`. -/
def fengKernel (θ s : ℝ) : ℝ :=
  let I := (θ + 3) / 6
  ((1 - θ) * s / (12 * θ) + s ^ 2 / 4)
  + (1 / 3) * (s - (1 - θ) * s ^ 2 - θ * s ^ 3)
  + θ ^ 2 * (I * s ^ 2 / 2 - s ^ 3 / 3 + (1 - θ) * s ^ 4 / 8 + θ * s ^ 5 / 15)
  - θ ^ 3 * ((1 - θ) * s ^ 5 / 120 + θ * s ^ 6 / 360)
  - θ ^ 2 * ((1 - θ) * s ^ 4 / 12 + θ * s ^ 5 / 30)
  - 2 * θ ^ 3 * (s ^ 4 / 24 - (1 - θ) * s ^ 5 / 120 - θ * s ^ 6 / 360)
  + θ * ((1 - θ) * s ^ 3 / 4 + θ * s ^ 4 / 8)
  + θ ^ 2 * (s ^ 3 / 2 - (1 - θ) * s ^ 4 / 8 - θ * s ^ 5 / 20)
  - θ ^ 3 * (I * s ^ 3 / 6 - s ^ 4 / 24 + (1 - θ) * s ^ 5 / 120 + θ * s ^ 6 / 360)
  + (1 / 3) * ((1 - θ) * s ^ 2 / 2 + θ * s ^ 3 / 3)
  + θ * (s ^ 2 / 2 - (1 - θ) * s ^ 3 / 6 - θ * s ^ 4 / 12)
  + θ ^ 2 * (I * s ^ 2 / 2 - s ^ 3 / 6 + (1 - θ) * s ^ 4 / 24 + θ * s ^ 5 / 60)
  - (1 / (12 * θ)) * ((1 - θ) * s + θ * s ^ 2)
  - (1 / 3) * (s - (1 - θ) * s ^ 2 / 2 - θ * s ^ 3 / 3)

/-- **Feng orthogonality.**  The cross kernel is proportional to the first-moment kernel `θ s² − (θ²/6) s³`, with
the factor `S₂/S₁ = (1+θ)³/(6θ)` of the optimum. -/
theorem fengKernel_eq {θ : ℝ} (hθ : θ ≠ 0) (s : ℝ) :
    fengKernel θ s = (1 + θ) ^ 3 / (6 * θ) * (θ * s ^ 2 - θ ^ 2 / 6 * s ^ 3) := by
  unfold fengKernel
  field_simp
  ring

end CGGMollifier

end RHTower
