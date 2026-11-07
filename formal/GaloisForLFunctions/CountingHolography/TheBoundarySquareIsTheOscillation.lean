import GaloisForLFunctions.CountingHolography.TheCountLawAtEveryGenus

/-!
# The boundary square is the oscillation

On a black hole `(q, t)` the Krein square `𝒬(x, y) = y² - t x y + q x²` is the norm of the probe
`y - x π` in the ring `ℤ[π] = ℤ[x]/(x² - t x + q)`, and its absolute value is the count of the probe
(`ArithmeticScatteringHolography.card_quotient_probeLattice`).

* **An oscillating mode makes the ring a lattice in `ℂ`.** If `t² ≤ 4q` the mode
  `α = t/2 + i √(q - t²/4)` is a root of `x² - t x + q` (`oscillatingMode_root`), on the circle
  `|α|² = q`, and the Krein square is the boundary square `𝒬(x, y) = |y - x α|²`
  (`kreinSquare_eq_normSq`). The count of a probe is then the area by which multiplication by
  `y - x α` scales the plane (`probeCount_eq_normSq`, `det_mulMatrix`): a count because it is an
  area.
* **An overdamped mode splits the ring over `ℝ`.** If `t² > 4q` the two modes are real, the Krein
  square factors as `(y - x α₁)(y - x α₂)` (`kreinSquare_eq_mul_of_real`), and an integer probe has
  `𝒬 < 0` (`exists_probe_neg_of_overdamped`): the count `|𝒬|` is not a square.

So the form is a boundary square exactly when the modes oscillate because the count of an oscillating
black hole is the norm of a complex number: the ring of probes embeds in `ℂ`.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography

/-- The oscillating mode `t/2 + i √(q - t²/4)`. -/
def oscillatingMode (q t : ℝ) : ℂ := ⟨t / 2, Real.sqrt (q - t ^ 2 / 4)⟩

/-- The oscillating mode is a root of the mode polynomial. -/
theorem oscillatingMode_root {q t : ℝ} (h : t ^ 2 ≤ 4 * q) :
    oscillatingMode q t ^ 2 - (t : ℂ) * oscillatingMode q t + (q : ℂ) = 0 := by
  unfold oscillatingMode
  set s := Real.sqrt (q - t ^ 2 / 4) with hsdef
  have hs : s ^ 2 = q - t ^ 2 / 4 := Real.sq_sqrt (by linarith)
  apply Complex.ext <;> simp [pow_two] <;> nlinarith [hs]

/-- The oscillating mode lies on the universal circle. -/
theorem normSq_oscillatingMode {q t : ℝ} (h : t ^ 2 ≤ 4 * q) : normSq (oscillatingMode q t) = q := by
  have hs : Real.sqrt (q - t ^ 2 / 4) ^ 2 = q - t ^ 2 / 4 := Real.sq_sqrt (by linarith)
  rw [normSq_apply]
  simp only [oscillatingMode]
  nlinarith [hs]

/-- **The Krein square of an oscillating black hole is a boundary square**, `|y - x α|²`. -/
theorem kreinSquare_eq_normSq {q t : ℝ} (h : t ^ 2 ≤ 4 * q) (x y : ℝ) :
    kreinSquare q t x y = normSq ((y : ℂ) - (x : ℂ) * oscillatingMode q t) := by
  have hs : Real.sqrt (q - t ^ 2 / 4) ^ 2 = q - t ^ 2 / 4 := Real.sq_sqrt (by linarith)
  rw [normSq_apply]
  simp only [oscillatingMode, sub_re, ofReal_re, mul_re, ofReal_im, sub_im, mul_im, zero_mul, sub_zero,
    add_zero]
  unfold kreinSquare
  nlinarith [hs]

/-- The boundary square on integer probes. -/
theorem kreinSquare_eq_normSq_int {q t : ℤ} (h : t ^ 2 ≤ 4 * q) (x y : ℤ) :
    ((kreinSquare q t x y : ℤ) : ℝ) = normSq ((y : ℂ) - (x : ℂ) * oscillatingMode q t) := by
  have h' : (t : ℝ) ^ 2 ≤ 4 * (q : ℝ) := by exact_mod_cast h
  have e := kreinSquare_eq_normSq h' (x : ℝ) (y : ℝ)
  rw [kreinSquare_cast, e]
  simp

/-- **The count of a probe on an oscillating black hole is the squared modulus of the probe.** -/
theorem probeCount_eq_normSq {q t : ℤ} (h : t ^ 2 ≤ 4 * q) (x y : ℤ) :
    (probeCount q t x y : ℝ) = normSq ((y : ℂ) - (x : ℂ) * oscillatingMode q t) := by
  have hn := (kreinSquare_int_nonneg_iff q t).mpr h x y
  rw [← kreinSquare_eq_normSq_int h]
  unfold probeCount
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hn)]

/-- The real matrix of multiplication by `μ` on `ℂ = ℝ²`. -/
def mulMatrix (μ : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := !![μ.re, -μ.im; μ.im, μ.re]

/-- **Multiplication by `μ` scales areas by `|μ|²`.** -/
theorem det_mulMatrix (μ : ℂ) : (mulMatrix μ).det = normSq μ := by
  rw [mulMatrix, Matrix.det_fin_two_of, normSq_apply]
  ring

/-- **An overdamped black hole factors over `ℝ`.** -/
theorem kreinSquare_eq_mul_of_real {q t : ℝ} (h : 4 * q < t ^ 2) :
    ∃ α₁ α₂ : ℝ, α₁ ≠ α₂ ∧ α₁ * α₂ = q ∧ ∀ x y : ℝ, kreinSquare q t x y = (y - x * α₁) * (y - x * α₂) := by
  set r := Real.sqrt (t ^ 2 - 4 * q)
  have hr : r ^ 2 = t ^ 2 - 4 * q := Real.sq_sqrt (by linarith)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
  refine ⟨(t + r) / 2, (t - r) / 2, by intro h; linarith, by nlinarith, fun x y => ?_⟩
  unfold kreinSquare
  nlinarith [hr]

/-- **An overdamped black hole has a probe with negative Krein square**: its count is not a square. -/
theorem exists_probe_neg_of_overdamped {q t : ℤ} (h : 4 * q < t ^ 2) :
    ∃ x y : ℤ, kreinSquare q t x y < 0 := by
  by_contra hn
  push Not at hn
  have := (kreinSquare_int_nonneg_iff q t).mp hn
  omega

/-- **The form is a boundary square exactly when the modes oscillate.** On the probes of a black hole
`(q, t)` the Krein square is the squared modulus of `y - x α` for a complex `α` exactly when
`t² ≤ 4q`. -/
theorem boundarySquare_iff {q t : ℤ} :
    (∃ α : ℂ, ∀ x y : ℤ, ((kreinSquare q t x y : ℤ) : ℝ) = normSq ((y : ℂ) - (x : ℂ) * α)) ↔
      t ^ 2 ≤ 4 * q := by
  constructor
  · rintro ⟨α, hα⟩
    rw [← kreinSquare_int_nonneg_iff]
    intro x y
    have := hα x y
    have h0 : (0 : ℝ) ≤ ((kreinSquare q t x y : ℤ) : ℝ) := by rw [this]; exact normSq_nonneg _
    exact_mod_cast h0
  · intro h
    exact ⟨oscillatingMode q t, kreinSquare_eq_normSq_int h⟩

end GaloisForLFunctions.CountingHolography

end
