import GaloisForLFunctions.RHTower.ConstrainedWeilApertureAveraging
import GaloisForLFunctions.RHTower.ConstrainedWeilPlateauBounds

/-!
# The constant term of a normalised ray-term polynomial

Let `Θ > 0` bound every `|Im z_q|` and let the twisted odd test be centred at `γ ≠ 0`.  The
`−Θ`-shifted pair polynomial of a copy `q` has exponents `±c_i − Θ` and `−Θ` with
`c_i = −Im z_q + iν_i`, `ν₁ = Re z_q − γ`, `ν₂ = Re z_q + γ`.  Only exponents of real part `0` can pair
to a zero exponent, and these exist only when `|Im z_q| = Θ`: for `Im z_q = −Θ` they are `iν₁, iν₂`
(coefficients `κ(c₁), κ(c₂)`), for `Im z_q = Θ` they are `−iν₁, −iν₂` (coefficients `−κ(−c₁), −κ(−c₂)`).
Two of them pair to zero exactly when `ν₁ = 0` or `ν₂ = 0` (the sum `ν₁ + ν₂ = 2 Re z_q` never
vanishes), and then the pairing coefficient is `κ(Θ)²`.  Hence the constant term of the normalised
ray-term polynomial is `−(1/4) κ(Θ)² / z_q²` for the four copies with `|Im z_q| = Θ`, `|Re z_q| = |γ|`,
and `0` for every other copy.
-/

open MeasureTheory Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The `−Θ`-shifted pair polynomial. -/
def shiftedPairPoly (Θ γ : ℝ) (q : XiZeroCopy) : ExpPoly :=
  expPolyShift (-(Θ : ℂ)) (rayPairPoly γ q)

theorem normalizedRayTermPoly_eq (Θ γ : ℝ) (q : XiZeroCopy) :
    normalizedRayTermPoly Θ γ q
      = ExpPoly.smul (-(1 / 4 : ℂ) / xiSpectralPoint q ^ 2)
          (ExpPoly.mul (shiftedPairPoly Θ γ q) (shiftedPairPoly Θ γ q)) := rfl

theorem decaying_shiftedPairPoly {Θ : ℝ} (γ : ℝ) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| ≤ Θ) :
    ExpPoly.Decaying (shiftedPairPoly Θ γ q) := by
  unfold shiftedPairPoly
  refine decaying_expPolyShift fun p hp => ?_
  simp only [Complex.neg_re, Complex.ofReal_re]
  have h := abs_le.mp hq
  rcases rayPairPoly_exponent_re γ q hp with h1 | h1 | h1 <;> rw [h1] <;> linarith

/-! ## The zero-real-part filter of the shifted pair polynomial -/

/-- The filtered list: no entry survives when `|Im z_q| < Θ`. -/
theorem shiftedPairPoly_filter_of_lt {Θ : ℝ} (γ : ℝ) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| < Θ) :
    (shiftedPairPoly Θ γ q).filter (fun p => decide (p.2.re = 0)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro p hp
  unfold shiftedPairPoly at hp
  simp only [expPolyShift, List.mem_map] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, decide_eq_true_eq]
  have h := abs_lt.mp hq
  rcases rayPairPoly_exponent_re γ q hr with h1 | h1 | h1 <;> rw [h1] <;>
    (intro h0; linarith)

theorem plateauMomentPoly_of_ne {c : ℂ} (hc : c ≠ 0) :
    plateauMomentPoly c
      = [(plateauKappa c, c), (plateauRho c, 0), (-plateauKappa (-c), -c), (-plateauRho (-c), 0)] := by
  simp [plateauMomentPoly, hc]

theorem shiftedPairPoly_explicit (Θ γ : ℝ) {q : XiZeroCopy} (hc₁ : rayFreq₁ γ q ≠ 0)
    (hc₂ : rayFreq₂ γ q ≠ 0) :
    shiftedPairPoly Θ γ q
      = [(plateauKappa (rayFreq₁ γ q), rayFreq₁ γ q + -(Θ : ℂ)),
          (plateauRho (rayFreq₁ γ q), 0 + -(Θ : ℂ)),
          (-plateauKappa (-rayFreq₁ γ q), -rayFreq₁ γ q + -(Θ : ℂ)),
          (-plateauRho (-rayFreq₁ γ q), 0 + -(Θ : ℂ)),
          (plateauKappa (rayFreq₂ γ q), rayFreq₂ γ q + -(Θ : ℂ)),
          (plateauRho (rayFreq₂ γ q), 0 + -(Θ : ℂ)),
          (-plateauKappa (-rayFreq₂ γ q), -rayFreq₂ γ q + -(Θ : ℂ)),
          (-plateauRho (-rayFreq₂ γ q), 0 + -(Θ : ℂ))] := by
  unfold shiftedPairPoly rayPairPoly
  rw [plateauMomentPoly_of_ne hc₁, plateauMomentPoly_of_ne hc₂]
  simp [expPolyShift]

theorem rayFreq₁_ne_zero_of_im {Θ : ℝ} (hΘ : 0 < Θ) (γ : ℝ) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| = Θ) : rayFreq₁ γ q ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [rayFreq₁_re, Complex.zero_re, neg_eq_zero] at this
  rw [this, abs_zero] at hq
  linarith

theorem rayFreq₂_ne_zero_of_im {Θ : ℝ} (hΘ : 0 < Θ) (γ : ℝ) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| = Θ) : rayFreq₂ γ q ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [rayFreq₂_re, Complex.zero_re, neg_eq_zero] at this
  rw [this, abs_zero] at hq
  linarith

/-- The filtered list when `Im z_q = −Θ` (`Θ > 0`): the two entries `(κ(c_i), c_i − Θ)`. -/
theorem shiftedPairPoly_filter_of_neg {Θ : ℝ} (hΘ : 0 < Θ) (γ : ℝ) {q : XiZeroCopy}
    (hq : (xiSpectralPoint q).im = -Θ) :
    (shiftedPairPoly Θ γ q).filter (fun p => decide (p.2.re = 0))
      = [(plateauKappa (rayFreq₁ γ q), rayFreq₁ γ q + -(Θ : ℂ)),
          (plateauKappa (rayFreq₂ γ q), rayFreq₂ γ q + -(Θ : ℂ))] := by
  have habs : |(xiSpectralPoint q).im| = Θ := by rw [hq, abs_neg, abs_of_pos hΘ]
  rw [shiftedPairPoly_explicit Θ γ (rayFreq₁_ne_zero_of_im hΘ γ habs)
    (rayFreq₂_ne_zero_of_im hΘ γ habs)]
  simp [rayFreq₁_re, rayFreq₂_re, hq, hΘ.ne']

/-- The filtered list when `Im z_q = Θ` (`Θ > 0`): the two entries `(−κ(−c_i), −c_i − Θ)`. -/
theorem shiftedPairPoly_filter_of_pos {Θ : ℝ} (hΘ : 0 < Θ) (γ : ℝ) {q : XiZeroCopy}
    (hq : (xiSpectralPoint q).im = Θ) :
    (shiftedPairPoly Θ γ q).filter (fun p => decide (p.2.re = 0))
      = [(-plateauKappa (-rayFreq₁ γ q), -rayFreq₁ γ q + -(Θ : ℂ)),
          (-plateauKappa (-rayFreq₂ γ q), -rayFreq₂ γ q + -(Θ : ℂ))] := by
  have habs : |(xiSpectralPoint q).im| = Θ := by rw [hq, abs_of_pos hΘ]
  rw [shiftedPairPoly_explicit Θ γ (rayFreq₁_ne_zero_of_im hΘ γ habs)
    (rayFreq₂_ne_zero_of_im hΘ γ habs)]
  simp [rayFreq₁_re, rayFreq₂_re, hq, hΘ.ne']

/-! ## Constant terms of two-entry products -/

theorem constTerm_mul_pair (x y : ℂ × ℂ) :
    ExpPoly.constTerm (ExpPoly.mul [x, y] [x, y])
      = (if x.2 + x.2 = 0 then x.1 * x.1 else 0) + (if x.2 + y.2 = 0 then x.1 * y.1 else 0)
        + (if y.2 + x.2 = 0 then y.1 * x.1 else 0) + (if y.2 + y.2 = 0 then y.1 * y.1 else 0) := by
  simp [ExpPoly.mul, ExpPoly.constTerm, List.product_cons]
  ring

theorem constTerm_normalizedRayTermPoly_eq_smul {Θ : ℝ} (γ : ℝ) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| ≤ Θ) :
    ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)
      = -(1 / 4 : ℂ) / xiSpectralPoint q ^ 2
        * ExpPoly.constTerm (ExpPoly.mul
            ((shiftedPairPoly Θ γ q).filter fun p => decide (p.2.re = 0))
            ((shiftedPairPoly Θ γ q).filter fun p => decide (p.2.re = 0))) := by
  rw [normalizedRayTermPoly_eq, ExpPoly.constTerm_smul,
    ExpPoly.constTerm_mul_eq_constTerm_mul_filter (decaying_shiftedPairPoly γ hq)
      (decaying_shiftedPairPoly γ hq)]

/-- Copies with `|Im z_q| < Θ` have constant term `0`. -/
theorem constTerm_normalizedRayTermPoly_of_lt {Θ : ℝ} (γ : ℝ) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| < Θ) :
    ExpPoly.constTerm (normalizedRayTermPoly Θ γ q) = 0 := by
  rw [constTerm_normalizedRayTermPoly_eq_smul γ hq.le, shiftedPairPoly_filter_of_lt γ hq]
  simp [ExpPoly.mul, ExpPoly.constTerm]

/-- The pairing structure at the top level: with `ν₁ = Re z_q − γ`, `ν₂ = Re z_q + γ` and
`Re z_q ≠ 0`, the two frequencies never sum to zero. -/
theorem rayFreq_sum_ne_zero (γ : ℝ) {q : XiZeroCopy} (hre : (xiSpectralPoint q).re ≠ 0) :
    rayFreq₁ γ q + rayFreq₂ γ q ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [Complex.add_im, rayFreq₁_im, rayFreq₂_im, Complex.zero_im] at this
  apply hre
  linarith

/-- **Top copies, `Im z_q = −Θ`.**  The constant term is `−(1/4)κ(Θ)²/z_q²` times the number of
zero frequencies among `ν₁, ν₂` (which is `0` or `1`). -/
theorem constTerm_normalizedRayTermPoly_of_neg {Θ : ℝ} (hΘ : 0 < Θ) (γ : ℝ) {q : XiZeroCopy}
    (hq : (xiSpectralPoint q).im = -Θ) (hre : (xiSpectralPoint q).re ≠ 0) :
    ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)
      = -(1 / 4 : ℂ) / xiSpectralPoint q ^ 2
        * ((if (xiSpectralPoint q).re - γ = 0 then plateauKappa (Θ : ℂ) ^ 2 else 0)
          + (if (xiSpectralPoint q).re + γ = 0 then plateauKappa (Θ : ℂ) ^ 2 else 0)) := by
  have hle : |(xiSpectralPoint q).im| ≤ Θ := by rw [hq, abs_neg, abs_of_pos hΘ]
  rw [constTerm_normalizedRayTermPoly_eq_smul γ hle, shiftedPairPoly_filter_of_neg hΘ γ hq,
    constTerm_mul_pair]
  congr 1
  have hsum : rayFreq₁ γ q + -(Θ : ℂ) + (rayFreq₂ γ q + -(Θ : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, add_zero, rayFreq₁_im,
      rayFreq₂_im, Complex.zero_im] at this
    apply hre
    linarith
  have hsum' : rayFreq₂ γ q + -(Θ : ℂ) + (rayFreq₁ γ q + -(Θ : ℂ)) ≠ 0 := by
    rw [add_comm]; exact hsum
  simp only [hsum, hsum', if_false, add_zero]
  have e1 : rayFreq₁ γ q + -(Θ : ℂ) + (rayFreq₁ γ q + -(Θ : ℂ)) = 0 ↔ (xiSpectralPoint q).re - γ = 0 := by
    constructor
    · intro h
      have := congrArg Complex.im h
      simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, add_zero, rayFreq₁_im,
        Complex.zero_im] at this
      linarith
    · intro h
      apply Complex.ext <;> simp [rayFreq₁_re, rayFreq₁_im, hq, h]
  have e2 : rayFreq₂ γ q + -(Θ : ℂ) + (rayFreq₂ γ q + -(Θ : ℂ)) = 0 ↔ (xiSpectralPoint q).re + γ = 0 := by
    constructor
    · intro h
      have := congrArg Complex.im h
      simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, add_zero, rayFreq₂_im,
        Complex.zero_im] at this
      linarith
    · intro h
      apply Complex.ext <;> simp [rayFreq₂_re, rayFreq₂_im, hq, h]
  have k1 : (xiSpectralPoint q).re - γ = 0 → rayFreq₁ γ q = (Θ : ℂ) := by
    intro h
    apply Complex.ext
    · simp [rayFreq₁_re, hq]
    · simp [rayFreq₁_im, h]
  have k2 : (xiSpectralPoint q).re + γ = 0 → rayFreq₂ γ q = (Θ : ℂ) := by
    intro h
    apply Complex.ext
    · simp [rayFreq₂_re, hq]
    · simp [rayFreq₂_im, h]
  by_cases h1 : (xiSpectralPoint q).re - γ = 0 <;> by_cases h2 : (xiSpectralPoint q).re + γ = 0
  · exfalso
    apply hre
    linarith
  · rw [if_pos (e1.mpr h1), if_neg (fun h => h2 (e2.mp h)), if_pos h1, if_neg h2, k1 h1]
    ring
  · rw [if_neg (fun h => h1 (e1.mp h)), if_pos (e2.mpr h2), if_neg h1, if_pos h2, k2 h2]
    ring
  · rw [if_neg (fun h => h1 (e1.mp h)), if_neg (fun h => h2 (e2.mp h)), if_neg h1, if_neg h2]

/-- **Top copies, `Im z_q = Θ`.**  Same value as for `Im z_q = −Θ`. -/
theorem constTerm_normalizedRayTermPoly_of_pos {Θ : ℝ} (hΘ : 0 < Θ) (γ : ℝ) {q : XiZeroCopy}
    (hq : (xiSpectralPoint q).im = Θ) (hre : (xiSpectralPoint q).re ≠ 0) :
    ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)
      = -(1 / 4 : ℂ) / xiSpectralPoint q ^ 2
        * ((if (xiSpectralPoint q).re - γ = 0 then plateauKappa (Θ : ℂ) ^ 2 else 0)
          + (if (xiSpectralPoint q).re + γ = 0 then plateauKappa (Θ : ℂ) ^ 2 else 0)) := by
  have hle : |(xiSpectralPoint q).im| ≤ Θ := by rw [hq, abs_of_pos hΘ]
  rw [constTerm_normalizedRayTermPoly_eq_smul γ hle, shiftedPairPoly_filter_of_pos hΘ γ hq,
    constTerm_mul_pair]
  congr 1
  have hsum : -rayFreq₁ γ q + -(Θ : ℂ) + (-rayFreq₂ γ q + -(Θ : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, add_zero,
      rayFreq₁_im, rayFreq₂_im, Complex.zero_im] at this
    apply hre
    linarith
  have hsum' : -rayFreq₂ γ q + -(Θ : ℂ) + (-rayFreq₁ γ q + -(Θ : ℂ)) ≠ 0 := by
    rw [add_comm]; exact hsum
  simp only [hsum, hsum', if_false, add_zero]
  have e1 : -rayFreq₁ γ q + -(Θ : ℂ) + (-rayFreq₁ γ q + -(Θ : ℂ)) = 0 ↔ (xiSpectralPoint q).re - γ = 0 := by
    constructor
    · intro h
      have := congrArg Complex.im h
      simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, rayFreq₁_im,
        Complex.zero_im] at this
      linarith
    · intro h
      apply Complex.ext <;> simp [rayFreq₁_re, rayFreq₁_im, hq, h]
  have e2 : -rayFreq₂ γ q + -(Θ : ℂ) + (-rayFreq₂ γ q + -(Θ : ℂ)) = 0 ↔ (xiSpectralPoint q).re + γ = 0 := by
    constructor
    · intro h
      have := congrArg Complex.im h
      simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, rayFreq₂_im,
        Complex.zero_im] at this
      linarith
    · intro h
      apply Complex.ext <;> simp [rayFreq₂_re, rayFreq₂_im, hq, h]
  have k1 : (xiSpectralPoint q).re - γ = 0 → -rayFreq₁ γ q = (Θ : ℂ) := by
    intro h
    apply Complex.ext
    · simp [rayFreq₁_re, hq]
    · simp [rayFreq₁_im, h]
  have k2 : (xiSpectralPoint q).re + γ = 0 → -rayFreq₂ γ q = (Θ : ℂ) := by
    intro h
    apply Complex.ext
    · simp [rayFreq₂_re, hq]
    · simp [rayFreq₂_im, h]
  by_cases h1 : (xiSpectralPoint q).re - γ = 0 <;> by_cases h2 : (xiSpectralPoint q).re + γ = 0
  · exfalso
    apply hre
    linarith
  · rw [if_pos (e1.mpr h1), if_neg (fun h => h2 (e2.mp h)), if_pos h1, if_neg h2, k1 h1]
    ring
  · rw [if_neg (fun h => h1 (e1.mp h)), if_pos (e2.mpr h2), if_neg h1, if_pos h2, k2 h2]
    ring
  · rw [if_neg (fun h => h1 (e1.mp h)), if_neg (fun h => h2 (e2.mp h)), if_neg h1, if_neg h2]

/-- **Constant term of the normalised ray term** for every copy with `|Im z_q| ≤ Θ`, `Re z_q ≠ 0`:
`−(1/4)κ(Θ)²/z_q²` times the number of vanishing frequencies (`Re z_q = ±γ`) when `|Im z_q| = Θ`,
and `0` otherwise. -/
theorem constTerm_normalizedRayTermPoly {Θ : ℝ} (hΘ : 0 < Θ) (γ : ℝ) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| ≤ Θ) (hre : (xiSpectralPoint q).re ≠ 0) :
    ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)
      = if |(xiSpectralPoint q).im| = Θ then
          -(1 / 4 : ℂ) / xiSpectralPoint q ^ 2
            * ((if (xiSpectralPoint q).re - γ = 0 then plateauKappa (Θ : ℂ) ^ 2 else 0)
              + (if (xiSpectralPoint q).re + γ = 0 then plateauKappa (Θ : ℂ) ^ 2 else 0))
        else 0 := by
  by_cases htop : |(xiSpectralPoint q).im| = Θ
  · rw [if_pos htop]
    rcases abs_eq (le_of_lt hΘ) |>.mp htop with h | h
    · exact constTerm_normalizedRayTermPoly_of_pos hΘ γ h hre
    · exact constTerm_normalizedRayTermPoly_of_neg hΘ γ h hre
  · rw [if_neg htop]
    exact constTerm_normalizedRayTermPoly_of_lt γ (lt_of_le_of_ne hq htop)

end

end RHTower
