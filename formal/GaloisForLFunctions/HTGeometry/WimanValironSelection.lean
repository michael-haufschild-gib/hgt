import GaloisForLFunctions.HTGeometry.WimanValironPolynomialBound
import GaloisForLFunctions.HTGeometry.BorelGrowthExponent

/-!
# Selecting the sampling parameters

The Wiman--Valiron estimate needs an interval on which the central index does not rise too fast: the
hypothesis is `2H (nu(e^{d+2H}) - nu(e^c)) / s < d - c`, a comparison between the total rise across
the sampling interval and its length.  The Borel growth lemma at an arbitrary exponent supplies
exactly such an interval: outside a set of finite measure the central index does not double across a
window of length `(nu+1)^{-α}`, and inside such a window the total rise is at most `nu + 1`.

Splitting that window as `d - c = σ/2` with `H = σ s / (8(nu+1))` turns the hypothesis into the
single requirement `s ≤ 2(nu+1)`, which any sublinear scale satisfies.  The parameters are therefore
never obstructed: for every scale rule and every bound `R` there is a radius beyond `R` at which the
whole chain applies.
-/

open MeasureTheory Complex Set

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-! ## A window in which the central index does not double -/

/-- **A radius beyond which the central index does not double across `(nu+1)^{-α}`.**  This is the
Borel growth lemma at exponent `α` applied to `y ↦ nu(e^y) + 1`; the exponent is free, so the window
may be taken far longer than the classical `1/nu`. -/
theorem exists_ge_centralIndex_no_double (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {α : ℝ} (hα : 0 < α) (R : ℝ) :
    ∃ x, R ≤ x ∧
      ((centralIndex a (Real.exp (x
          + (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ (-α))) : ℝ) + 1)
        < 2 * (((centralIndex a (Real.exp x) : ℝ)) + 1) := by
  have hmono : Monotone fun y : ℝ => ((centralIndex a (Real.exp y) : ℝ)) + 1 := by
    intro p q hpq
    have h := monotone_centralIndex_exp ha hn₀ hpq
    simp only
    linarith
  have hT1 : ∀ y : ℝ, (1 : ℝ) ≤ ((centralIndex a (Real.exp y) : ℝ)) + 1 := by
    intro y
    have : (0 : ℝ) ≤ ((centralIndex a (Real.exp y) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  exact Nevanlinna.exists_ge_lt_two_mul_rpow hmono hT1 hα R

/-! ## The sampling hypothesis -/

/-- **The measure hypothesis from a non-doubling window.**  On the left half of a window across
which the central index does not double, the sampling hypothesis of the Wiman--Valiron estimate
holds with `H = σ s / (8(nu+1))`, for every scale `s` below `2(nu+1)`. -/
theorem hsmall_of_no_double (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {x σ s H : ℝ} (hσ : 0 < σ) (hs : 0 < s)
    (hHdef : H = σ * s / (8 * (((centralIndex a (Real.exp x) : ℝ)) + 1)))
    (hnd : ((centralIndex a (Real.exp (x + σ)) : ℝ)) + 1
        < 2 * (((centralIndex a (Real.exp x) : ℝ)) + 1))
    (hsle : s ≤ 2 * (((centralIndex a (Real.exp x) : ℝ)) + 1)) :
    2 * H * ((centralIndex a (Real.exp ((x + σ / 2) + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp x) : ℝ)) / s < (x + σ / 2) - x := by
  have hν0 : (0 : ℝ) ≤ ((centralIndex a (Real.exp x) : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht : (0 : ℝ) < ((centralIndex a (Real.exp x) : ℝ)) + 1 := by linarith
  have hH : 0 < H := by
    rw [hHdef]
    positivity
  -- the sampling window stays inside the non-doubling window
  have h2H : 2 * H ≤ σ / 2 := by
    have hteq : 2 * (σ * s / (8 * (((centralIndex a (Real.exp x) : ℝ)) + 1)))
        = σ * s / (4 * (((centralIndex a (Real.exp x) : ℝ)) + 1)) := by
      field_simp
      ring
    rw [hHdef, hteq,
      div_le_iff₀ (by linarith : (0 : ℝ) < 4 * (((centralIndex a (Real.exp x) : ℝ)) + 1))]
    nlinarith [hsle, hσ, ht]
  have hle : (x + σ / 2) + 2 * H ≤ x + σ := by linarith
  have hmono := monotone_centralIndex_exp ha hn₀ hle
  -- the rise across the sampling window is below `nu + 1`
  have hrise : ((centralIndex a (Real.exp ((x + σ / 2) + 2 * H)) : ℝ)
      - (centralIndex a (Real.exp x) : ℝ)) < ((centralIndex a (Real.exp x) : ℝ)) + 1 := by
    have h1 : ((centralIndex a (Real.exp ((x + σ / 2) + 2 * H)) : ℝ))
        ≤ ((centralIndex a (Real.exp (x + σ)) : ℝ)) := hmono
    linarith
  have hmulH : 2 * H * ((centralIndex a (Real.exp ((x + σ / 2) + 2 * H)) : ℝ)
      - (centralIndex a (Real.exp x) : ℝ))
      < 2 * H * ((((centralIndex a (Real.exp x) : ℝ)) + 1)) :=
    mul_lt_mul_of_pos_left hrise (by linarith)
  have hvalmul : 2 * H * ((((centralIndex a (Real.exp x) : ℝ)) + 1)) = σ / 4 * s := by
    rw [hHdef]
    field_simp
    ring
  have hσs : (0 : ℝ) < σ * s := by positivity
  rw [show (x + σ / 2) - x = σ / 2 by ring, div_lt_iff₀ hs]
  nlinarith [hmulH, hvalmul, hσs]

/-- **The central index barely rises across the sampled window.**  With the same splitting, the
right end of the sampling window still lies inside the non-doubling window, so the central index
there is below twice its value at the left end. -/
theorem centralIndex_lt_two_mul_of_no_double (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {x σ s H : ℝ} (hσ : 0 < σ) (hs : 0 < s)
    (hHdef : H = σ * s / (8 * (((centralIndex a (Real.exp x) : ℝ)) + 1)))
    (hnd : ((centralIndex a (Real.exp (x + σ)) : ℝ)) + 1
        < 2 * (((centralIndex a (Real.exp x) : ℝ)) + 1))
    (hsle : s ≤ 2 * (((centralIndex a (Real.exp x) : ℝ)) + 1)) :
    ((centralIndex a (Real.exp ((x + σ / 2) + 2 * H)) : ℝ)) + 1
      < 2 * (((centralIndex a (Real.exp x) : ℝ)) + 1) := by
  have hν0 : (0 : ℝ) ≤ ((centralIndex a (Real.exp x) : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht : (0 : ℝ) < ((centralIndex a (Real.exp x) : ℝ)) + 1 := by linarith
  have h2H : 2 * H ≤ σ / 2 := by
    have hteq : 2 * (σ * s / (8 * (((centralIndex a (Real.exp x) : ℝ)) + 1)))
        = σ * s / (4 * (((centralIndex a (Real.exp x) : ℝ)) + 1)) := by
      field_simp
      ring
    rw [hHdef, hteq,
      div_le_iff₀ (by linarith : (0 : ℝ) < 4 * (((centralIndex a (Real.exp x) : ℝ)) + 1))]
    nlinarith [hsle, hσ, ht]
  have hle : (x + σ / 2) + 2 * H ≤ x + σ := by linarith
  have hmono := monotone_centralIndex_exp ha hn₀ hle
  have h1 : ((centralIndex a (Real.exp ((x + σ / 2) + 2 * H)) : ℝ))
      ≤ ((centralIndex a (Real.exp (x + σ)) : ℝ)) := hmono
  linarith

/-! ## A window half-width always exists -/

/-- Any scale at least `1/2` admits a natural window half-width in `[2s, 4s]`. -/
theorem exists_window_index {s : ℝ} (hs : 1 ≤ 2 * s) :
    ∃ N : ℕ, 0 < N ∧ 2 * s ≤ (N : ℝ) ∧ (N : ℝ) ≤ 4 * s := by
  refine ⟨⌈2 * s⌉₊, Nat.ceil_pos.mpr (by linarith), Nat.le_ceil _, ?_⟩
  have hlt : ((⌈2 * s⌉₊ : ℕ) : ℝ) < 2 * s + 1 := Nat.ceil_lt_add_one (by linarith)
  linarith

/-! ## The parameters are never obstructed -/

/-- **Admissible sampling parameters exist beyond every bound.**  For any scale rule that is
positive, at most `2(nu+1)` and at least `1/2`, and for every `R`, there are `x ≥ R`, an interval
`[x, d]`, a window half-width `H` and a window index `N` satisfying every hypothesis of the
Wiman--Valiron estimate.  The scale rule is free: `scale t = t^β` is admissible for every
`β ∈ (0, 1]` on `t ≥ 1`. -/
theorem exists_good_parameters (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {α : ℝ} (hα : 0 < α) (scale : ℝ → ℝ)
    (hpos : ∀ t : ℝ, 1 ≤ t → 0 < scale t)
    (hle : ∀ t : ℝ, 1 ≤ t → scale t ≤ 2 * t)
    (hone : ∀ t : ℝ, 1 ≤ t → 1 ≤ 2 * scale t)
    (R : ℝ) :
    ∃ (x d s H : ℝ) (N : ℕ), R ≤ x ∧ x ≤ d ∧ 0 < H ∧ 0 < s ∧ 0 < N ∧
      s = scale (((centralIndex a (Real.exp x) : ℝ)) + 1) ∧
      H = (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ (-α) * s
            / (8 * (((centralIndex a (Real.exp x) : ℝ)) + 1)) ∧
      2 * s ≤ (N : ℝ) ∧ (N : ℝ) ≤ 4 * s ∧
      ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)) + 1
        < 2 * (((centralIndex a (Real.exp x) : ℝ)) + 1) ∧
      2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
          - (centralIndex a (Real.exp x) : ℝ)) / s < d - x := by
  obtain ⟨x, hxR, hnd⟩ := exists_ge_centralIndex_no_double ha hn₀ hα R
  have hν0 : (0 : ℝ) ≤ ((centralIndex a (Real.exp x) : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht1 : (1 : ℝ) ≤ ((centralIndex a (Real.exp x) : ℝ)) + 1 := by linarith
  have ht : (0 : ℝ) < ((centralIndex a (Real.exp x) : ℝ)) + 1 := by linarith
  have hs : 0 < scale (((centralIndex a (Real.exp x) : ℝ)) + 1) := hpos _ ht1
  have hσ : (0 : ℝ) < (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ (-α) :=
    Real.rpow_pos_of_pos ht _
  obtain ⟨N, hN0, hN2, hN4⟩ := exists_window_index (hone _ ht1)
  refine ⟨x, x + (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ (-α) / 2,
    scale (((centralIndex a (Real.exp x) : ℝ)) + 1),
    (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ (-α)
      * scale (((centralIndex a (Real.exp x) : ℝ)) + 1)
      / (8 * (((centralIndex a (Real.exp x) : ℝ)) + 1)),
    N, hxR, by linarith, by positivity, hs, hN0, rfl, rfl, hN2, hN4, ?_, ?_⟩
  · exact centralIndex_lt_two_mul_of_no_double ha hn₀ hσ hs rfl hnd (hle _ ht1)
  · exact hsmall_of_no_double ha hn₀ hσ hs rfl hnd (hle _ ht1)

/-- **The Wiman--Valiron estimate holds at radii beyond every bound.**  Combining the parameter
selection with the tail form of the estimate: for every admissible scale rule and every `R` there is
a radius `e^y` with `y` past `R` at which the logarithmic derivative is within the explicit bound of
the central index.  Nothing is assumed about the function beyond entirety and a nonzero coefficient;
the exponent `α` and the scale rule are free, and it is their choice that makes the bound `o(nu)`. -/
theorem exists_radius_point_wiman_valiron_selected (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {α : ℝ} (hα : 0 < α) (scale : ℝ → ℝ)
    (hpos : ∀ t : ℝ, 1 ≤ t → 0 < scale t)
    (hle : ∀ t : ℝ, 1 ≤ t → scale t ≤ 2 * t)
    (hone : ∀ t : ℝ, 1 ≤ t → 1 ≤ 2 * scale t)
    (R : ℝ) :
    ∃ (x d s H L h : ℝ) (N : ℕ), R ≤ x ∧ x ≤ d ∧ 0 < H ∧ 0 < s ∧ 0 < N ∧
      s = scale (((centralIndex a (Real.exp x) : ℝ)) + 1) ∧
      H = (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ (-α) * s
            / (8 * (((centralIndex a (Real.exp x) : ℝ)) + 1)) ∧
      2 * s ≤ (N : ℝ) ∧ (N : ℝ) ≤ 4 * s ∧ L = 2 * s / H ∧ h = H / 2 ∧
      ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)) + 1
        < 2 * (((centralIndex a (Real.exp x) : ℝ)) + 1) ∧
      ∃ y ∈ Icc (x + H) (d + H), ∃ z : ℂ, ‖z‖ = Real.exp y ∧
        maxTerm a (Real.exp y) ≤ ‖coeffFun a z‖ ∧
        ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp y) : ℂ)‖
          ≤ (Real.sqrt (2 * (N : ℝ) + 1)
              + 2 * ((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))
                  * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L))))))
              * (2 * L * h
                + 2 * Real.log ((centralIndex a (Real.exp y) : ℝ) + 2 * L * h + 1
                    + 1 / (Real.exp h - 1)) / h)
            + Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
                + 2 * (2 * ((N : ℝ) + 1) ^ 2
                    * (((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))) ^ 3
                        * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))))))
              * (Real.sqrt (2 * (N : ℝ) + 1)
                + 2 * ((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))
                    * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L))))))) := by
  obtain ⟨x, d, s, H, N, hxR, hxd, hH, hs, hN0, hsdef, hHdef, hN2, hN4, hdouble, hsmall⟩ :=
    exists_good_parameters ha hn₀ hα scale hpos hle hone R
  refine ⟨x, d, s, H, 2 * s / H, H / 2, N, hxR, hxd, hH, hs, hN0, hsdef, hHdef, hN2, hN4, rfl, rfl,
    hdouble, ?_⟩
  exact exists_radius_point_wiman_valiron_tail ha hn₀ hxd hH hs rfl rfl hsmall hN0 hN2 hN4

end GaloisForLFunctions.HTGeometry
