import GaloisForLFunctions.ArithmeticEffectivityTheory.TheEffectivityCalculus

/-!
# Calibration: the effectivity function of `ℙ¹ × ℙ¹` over `𝔽_q`

The effectivity calculus is not vacuous: on the hyperbolic plane `⟨H, V⟩` of `ℙ¹ × ℙ¹` the
genuine section count is an effectivity function. For `D = aH + bV` the space `H⁰(𝒪(a, b))` has
dimension `(a + 1)(b + 1)` for `a, b ≥ 0`; its log-volume over `𝔽_q`, in units of `log q`, is
`(a + 1)⁺ (b + 1)⁺` (`p1SquareH0`), extended to real classes.

* **The surface** (`hyperbolicPlane`): `(a, b) · (a', b') = a b' + a' b`, fibres `H = (1, 0)`,
  `V = (0, 1)`, canonical class `κ = −2H − 2V`; the Euler characteristic with `χ₀ = 1` is
  `(a + 1)(b + 1)` (`eulerChar_hyperbolicPlane`).
* **Riemann–Roch is exact** (`p1SquareH0_add_dual`, `p1SquareH1_nonneg`). With `u = a + 1`,
  `v = b + 1`: `h⁰ + h² = u⁺v⁺ + u⁻v⁻`, so `h¹ = h⁰ + h² − χ` is `0` on the effective and
  anti-effective quadrants and `−uv ≥ 0` on the mixed ones; the Riemann inequality is `h¹ ≥ 0`
  (`riemannInequality_p1SquareH0`). There are no sections in negative degree (`p1SquareH0_eq_zero`).
* **Degree levels are bounded** (`p1SquareH0_degreeBounded`): on `a + b = t` the count is at most
  `((t + 2)/2)²`.

So `ℙ¹ × ℙ¹` satisfies every law of the calculus with an `h⁰` that is a dimension, and the Hodge
index follows (`hyperbolicPlane_hodgeIndex`) — here it is also visible directly, since the
primitive part is zero.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

open ArithmeticCastelnuovoSeveri

/-- The hyperbolic plane `⟨H, V⟩`, the numerical surface of `ℙ¹ × ℙ¹`. -/
def hyperbolicPlane : PolarSurface (ℝ × ℝ) where
  pair := LinearMap.mk₂ ℝ (fun x y : ℝ × ℝ => x.1 * y.2 + y.1 * x.2)
    (fun x x' y => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
  pair_comm x y := by simp only [LinearMap.mk₂_apply]; ring
  H := (1, 0)
  V := (0, 1)
  pair_H_H := by simp
  pair_V_V := by simp
  pair_H_V := by simp

theorem hyperbolicPlane_pair (x y : ℝ × ℝ) : hyperbolicPlane.pair x y = x.1 * y.2 + y.1 * x.2 := by
  simp [hyperbolicPlane]

/-- The canonical class `−2H − 2V` of `ℙ¹ × ℙ¹`. -/
def p1SquareCanonical : ℝ × ℝ := (-2, -2)

theorem p1SquareCanonical_eq :
    p1SquareCanonical = (-2 : ℝ) • hyperbolicPlane.H + (-2 : ℝ) • hyperbolicPlane.V := by
  simp [p1SquareCanonical, hyperbolicPlane]

/-- The Euler characteristic of `𝒪(a, b)` is `(a + 1)(b + 1)`. -/
theorem eulerChar_hyperbolicPlane (x : ℝ × ℝ) :
    eulerChar hyperbolicPlane p1SquareCanonical 1 x = (x.1 + 1) * (x.2 + 1) := by
  simp only [eulerChar, hyperbolicPlane_pair, p1SquareCanonical, Prod.fst_sub, Prod.snd_sub]
  ring

/-- `h⁰(𝒪(a, b)) = (a + 1)⁺ (b + 1)⁺`: the dimension of the space of sections, i.e. its
log-volume in base `q`. -/
def p1SquareH0 (x : ℝ × ℝ) : ℝ := max 0 (x.1 + 1) * max 0 (x.2 + 1)

theorem p1SquareH0_nonneg (x : ℝ × ℝ) : 0 ≤ p1SquareH0 x :=
  mul_nonneg (le_max_left _ _) (le_max_left _ _)

/-- **No sections in negative degree**: `h⁰ = 0` when `a < −1` or `b < −1`. -/
theorem p1SquareH0_eq_zero {x : ℝ × ℝ} (hx : x.1 + 1 ≤ 0 ∨ x.2 + 1 ≤ 0) : p1SquareH0 x = 0 := by
  rcases hx with h | h <;> simp [p1SquareH0, max_eq_left h]

/-- `h⁰(D) + h²(D) = u⁺v⁺ + u⁻v⁻` with `h²(D) = h⁰(κ − D)`, `u = a + 1`, `v = b + 1`. -/
theorem p1SquareH0_add_dual (x : ℝ × ℝ) :
    p1SquareH0 x + p1SquareH0 (p1SquareCanonical - x) =
      max 0 (x.1 + 1) * max 0 (x.2 + 1) + max 0 (-(x.1 + 1)) * max 0 (-(x.2 + 1)) := by
  simp only [p1SquareH0, p1SquareCanonical, Prod.fst_sub, Prod.snd_sub]
  rw [show -2 - x.1 + 1 = -(x.1 + 1) by ring, show -2 - x.2 + 1 = -(x.2 + 1) by ring]

/-- **Riemann–Roch on `ℙ¹ × ℙ¹`**: `h¹ = h⁰ + h² − χ ≥ 0`, with equality on the effective and
anti-effective quadrants. -/
theorem p1SquareH1_nonneg (u v : ℝ) :
    u * v ≤ max 0 u * max 0 v + max 0 (-u) * max 0 (-v) := by
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · rw [max_eq_right hu, max_eq_right hv, max_eq_left (by linarith), max_eq_left (by linarith)]
    ring_nf; exact le_refl _
  · rw [max_eq_right hu, max_eq_left hv, max_eq_left (by linarith)]
    nlinarith [mul_nonpos_iff.mpr (Or.inl ⟨hu, hv⟩)]
  · rw [max_eq_left hu, max_eq_right hv, max_eq_left (by linarith : -v ≤ 0)]
    nlinarith [mul_nonpos_iff.mpr (Or.inr ⟨hu, hv⟩)]
  · rw [max_eq_left hu, max_eq_left hv, max_eq_right (by linarith : 0 ≤ -u),
      max_eq_right (by linarith : 0 ≤ -v)]
    ring_nf; exact le_refl _

/-- **The Riemann inequality** for the section count of `ℙ¹ × ℙ¹`. -/
theorem riemannInequality_p1SquareH0 :
    RiemannInequality hyperbolicPlane p1SquareCanonical 1 p1SquareH0 := fun x => by
  rw [eulerChar_hyperbolicPlane, p1SquareH0_add_dual]
  exact p1SquareH1_nonneg _ _

/-- **Degree levels are bounded**: on `a + b = t`, `h⁰ ≤ ((t + 2)/2)²`. -/
theorem p1SquareH0_degreeBounded : DegreeBounded hyperbolicPlane p1SquareH0 := by
  intro t
  refine ⟨((t + 2) / 2) ^ 2, fun x hx => ?_⟩
  have hdeg : x.1 + x.2 = t := by
    simpa [PolarSurface.ample, hyperbolicPlane_pair, hyperbolicPlane] using hx
  simp only [p1SquareH0]
  rcases le_total (x.1 + 1) 0 with h1 | h1
  · rw [max_eq_left h1, zero_mul]; positivity
  rcases le_total (x.2 + 1) 0 with h2 | h2
  · rw [max_eq_left h2, mul_zero]; positivity
  rw [max_eq_right h1, max_eq_right h2]
  nlinarith [sq_nonneg (x.1 - x.2)]

/-- **The Hodge index of `ℙ¹ × ℙ¹` from its section count**, through the effectivity calculus. -/
theorem hyperbolicPlane_hodgeIndex : hyperbolicPlane.HodgeIndex :=
  hodgeIndex_of_riemannInequality hyperbolicPlane riemannInequality_p1SquareH0
    (degreeZeroSubquadratic_of_degreeBounded hyperbolicPlane p1SquareH0_degreeBounded)

end GaloisForLFunctions.ArithmeticEffectivityTheory
