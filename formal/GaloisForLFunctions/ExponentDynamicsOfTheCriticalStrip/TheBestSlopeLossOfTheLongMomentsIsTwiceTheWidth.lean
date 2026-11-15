import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.EveryRulerCarriesTheSeedAndEveryLever

/-!
# The best slope loss of the long moments is twice the width

The long second moment of the mollified zeta function is
`I(θ, T) = ∫₁ᵀ |ζ M_X(½ + it)|² dt` at the length `X = T^θ` of the Möbius polynomial. An
**exponent law** is a function `a(θ)` with `I(θ, T) ≤ C_θ T^{a(θ)}` for all `T ≥ 1`. A **slope law
with loss `κ`** is an exponent law with `a(2θ) ≤ a(θ) + κθ`: a stage map from the length `T^θ` to
the length `T^{2θ}` that loses the factor `T^{κθ}`. This module computes the best loss, with no
hypothesis on the zeros:

* **Stage calculus** (`le_of_slope_step`): `a(2θ) ≤ a(θ) + κθ` gives
  `a(2ⁿ) ≤ a(1) + κ(2ⁿ − 1)`.
* **A slope law is a half-plane** (`zetaZeroWidth_le_of_slopeLaw`): a slope law with loss
  `κ ≥ 0` gives `sup |Re ρ − ½| ≤ κ/2`.
* **Every loss from `2w` on occurs** (`slopeLaw_of_zetaZeroWidth_le`); the loss `3/4` occurs
  with no hypothesis (`slopeLaw_three_quarters`).
* **Ruler and best loss** (`isRuler_slopeLaw`, `isLeast_slopeLaw`): the least loss of a slope
  law is `2w`.

The receiver is the sharp converse of the slope of the long moments: along the lengths
`θ = 2ⁿ` a slope law is a bound `T^{K + κθ}` with `K` independent of `θ`.
-/

open Complex MeasureTheory Set Filter

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open GaloisForLFunctions.SquareRootThreshold
  (zetaZeroWidth zetaZeroWidth_nonneg zetaZeroWidth_le_three_eighths)

noncomputable section

/-- The long second moment of the mollified zeta function at the length `T^θ`. -/
def longMoment (θ T : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..T,
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      RHTower.edPoly ConjugateDiagonalGeometry.NearLineLogMean.moebiusMollifierCoeff
        (Finset.Icc 1 ⌊T ^ θ⌋₊) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2

/-- An **exponent law** of the long moments: `I(θ, T) ≤ C_θ T^{a(θ)}` for every length. -/
def IsMomentLaw (a : ℝ → ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → longMoment θ T ≤ C * T ^ a θ

/-- A **slope law with loss `κ`**: an exponent law with `a(2θ) ≤ a(θ) + κθ`. -/
def SlopeLaw (κ : ℝ) : Prop :=
  ∃ a : ℝ → ℝ, IsMomentLaw a ∧ ∀ θ : ℝ, 0 < θ → a (2 * θ) ≤ a θ + κ * θ

/-- **Stage calculus for slopes.** If `a(2θ) ≤ a(θ) + κθ` for all `θ > 0`, then
`a(2ⁿ) ≤ a(1) + κ(2ⁿ − 1)`. -/
theorem le_of_slope_step {a : ℝ → ℝ} {κ : ℝ}
    (h : ∀ θ : ℝ, 0 < θ → a (2 * θ) ≤ a θ + κ * θ) (n : ℕ) :
    a ((2 : ℝ) ^ n) ≤ a 1 + κ * ((2 : ℝ) ^ n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := h ((2 : ℝ) ^ n) (by positivity)
    have e : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ, mul_comm]
    rw [e]
    have e2 : a 1 + κ * (2 * (2 : ℝ) ^ n - 1) =
        a 1 + κ * ((2 : ℝ) ^ n - 1) + κ * (2 : ℝ) ^ n := by ring
    rw [e2]
    linarith

/-- **A slope law is a half-plane.** A slope law of the long moments with loss `κ ≥ 0` gives
`sup |Re ρ − ½| ≤ κ/2`. -/
theorem zetaZeroWidth_le_of_slopeLaw {κ : ℝ} (hκ : 0 ≤ κ) (h : SlopeLaw κ) :
    zetaZeroWidth ≤ κ / 2 := by
  obtain ⟨a, hlaw, hstep⟩ := h
  refine ConjugateDiagonalGeometry.NearLineLogMean.zetaZeroWidth_le_of_cofinal_moebius_mollifier_slope
    (β := κ / 2) (K := max (a 1 - κ) 0) (by linarith) (le_max_right _ _) fun θ₀ _ => ?_
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt θ₀ (by norm_num : (1 : ℝ) < 2)
  obtain ⟨C, hC0, hC⟩ := hlaw ((2 : ℝ) ^ n) (by positivity)
  refine ⟨(2 : ℝ) ^ n, hn.le, C, hC0,
    (eventually_ge_atTop (1 : ℝ)).frequently.mono fun T hT => ?_⟩
  have hexp : a ((2 : ℝ) ^ n) ≤ max (a 1 - κ) 0 + 2 * (κ / 2) * (2 : ℝ) ^ n := by
    have h1 := le_of_slope_step hstep n
    have h2 := le_max_left (a 1 - κ) 0
    have e : a 1 + κ * ((2 : ℝ) ^ n - 1) = (a 1 - κ) + 2 * (κ / 2) * (2 : ℝ) ^ n := by ring
    linarith
  have hlong := hC T hT
  unfold longMoment at hlong
  exact hlong.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT hexp) hC0)

/-- **Every loss from twice the width on occurs**: for `w ≤ β` the exponents `6 + 2βθ` are a
slope law with loss `2β`. -/
theorem slopeLaw_of_zetaZeroWidth_le {β : ℝ} (hβ : zetaZeroWidth ≤ β) : SlopeLaw (2 * β) :=
  ⟨fun θ => 6 + 2 * β * θ, fun _ hθ =>
    ConjugateDiagonalGeometry.NearLineLogMean.exists_moebius_mollifier_moment_le_of_width_le hβ hθ,
    fun θ _ => le_of_eq (by ring)⟩

/-- **The long moments have a slope law with loss `3/4`**, with no hypothesis on the zeros. -/
theorem slopeLaw_three_quarters : SlopeLaw (3 / 4) := by
  have h := slopeLaw_of_zetaZeroWidth_le zetaZeroWidth_le_three_eighths
  have e : (2 : ℝ) * (3 / 8) = 3 / 4 := by norm_num
  rwa [e] at h

/-- **The slope laws of the long moments are a ruler**: the zero width is at most `β` iff a
slope law with loss `2β` holds. -/
theorem isRuler_slopeLaw : IsRuler zetaZeroWidth (Set.Ici 0) fun β => SlopeLaw (2 * β) := by
  intro β hβ
  have hβ0 : 0 ≤ β := hβ
  refine ⟨slopeLaw_of_zetaZeroWidth_le, fun h => ?_⟩
  have h1 := zetaZeroWidth_le_of_slopeLaw (by linarith) h
  linarith

/-- **The least loss of a slope law of the long moments is twice the width.** -/
theorem isLeast_slopeLaw : IsLeast {κ : ℝ | 0 ≤ κ ∧ SlopeLaw κ} (2 * zetaZeroWidth) :=
  ⟨⟨by linarith [zetaZeroWidth_nonneg], slopeLaw_of_zetaZeroWidth_le le_rfl⟩, fun κ hκ => by
    have h := zetaZeroWidth_le_of_slopeLaw hκ.1 hκ.2
    linarith⟩

/-- The zero width vanishes iff the long moments have a slope law without loss. -/
theorem zetaZeroWidth_eq_zero_iff_slopeLaw_zero : zetaZeroWidth = 0 ↔ SlopeLaw 0 := by
  constructor
  · intro hw
    have h := slopeLaw_of_zetaZeroWidth_le (β := 0) hw.le
    rwa [mul_zero] at h
  · intro h
    have h1 := zetaZeroWidth_le_of_slopeLaw le_rfl h
    linarith [zetaZeroWidth_nonneg]

#print axioms zetaZeroWidth_le_of_slopeLaw
#print axioms slopeLaw_three_quarters
#print axioms isLeast_slopeLaw

end

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
