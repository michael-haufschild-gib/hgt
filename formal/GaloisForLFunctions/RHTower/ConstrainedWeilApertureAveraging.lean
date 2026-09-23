import GaloisForLFunctions.RHTower.ConstrainedWeilPlateauProfile
import GaloisForLFunctions.RHTower.ConstrainedWeilNegativityWitness
import GaloisForLFunctions.HTGeometry.ExponentialPolynomialWindowMean

/-!
# Ray terms of the plateau profile as exponential polynomials in the aperture

For the plateau profile the twisted moment at complex frequency `c` is the exponential polynomial
`e^{ca} κ(c) + ρ(c) − e^{−ca} κ(−c) − ρ(−c)` in the aperture `a` (and `0` when `c = 0`, by oddness).
Hence the pair moment at a zero copy `q` and centre `γ` is the exponential polynomial
`P_q = M(c₁) ++ M(c₂)` with `c₁ = −Im z_q + i(Re z_q − γ)`, `c₂ = −Im z_q + i(Re z_q + γ)`, and the
ray term `−(1/4) P_q² / z_q²` is the exponential polynomial `smul (−1/(4 z_q²)) (mul P_q P_q)`.
Normalising by `e^{−2Θa}` with `Θ ≥ |Im z_q|` shifts every exponent into the closed left half-plane,
so the window-mean law of `ExponentialPolynomialWindowMean` applies.
-/

open MeasureTheory Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Shifting exponents -/

/-- Shift every exponent by `s`; the evaluation is multiplied by `e^{sa}`. -/
def expPolyShift (s : ℂ) (P : ExpPoly) : ExpPoly := P.map fun p => (p.1, p.2 + s)

theorem eval_expPolyShift (s : ℂ) (P : ExpPoly) (a : ℝ) :
    ExpPoly.eval (expPolyShift s P) a = Complex.exp (s * (a : ℂ)) * ExpPoly.eval P a := by
  induction P with
  | nil => simp [expPolyShift]
  | cons p P ih =>
    simp only [expPolyShift, List.map_cons, ExpPoly.eval_cons] at ih ⊢
    rw [ih, add_mul, Complex.exp_add]
    ring

theorem decaying_expPolyShift {s : ℂ} {P : ExpPoly} (h : ∀ p ∈ P, p.2.re + s.re ≤ 0) :
    ExpPoly.Decaying (expPolyShift s P) := by
  intro p hp
  simp only [expPolyShift, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [Complex.add_re]
  exact h q hq

/-! ## The moment polynomial -/

/-- The exponential polynomial of the plateau moment at complex frequency `c`. -/
def plateauMomentPoly (c : ℂ) : ExpPoly :=
  if c = 0 then []
  else [(plateauKappa c, c), (plateauRho c, 0), (-plateauKappa (-c), -c), (-plateauRho (-c), 0)]

theorem twistedMoment_zero_zero {a : ℝ} (ψ : OddSmoothProfile a) : twistedMoment ψ 0 0 = 0 := by
  have h := twistedMoment_neg_neg ψ 0 0
  rw [neg_zero] at h
  have h2 : (2 : ℂ) * twistedMoment ψ 0 0 = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **The plateau moment is an exponential polynomial in the aperture.** -/
theorem twistedMoment_plateauProfile_eq_eval {a : ℝ} (ha : 1 / 2 ≤ a) (ha0 : 0 ≤ a) (b μ : ℝ) :
    twistedMoment (plateauProfile a ha0) b μ
      = ExpPoly.eval (plateauMomentPoly ((b : ℂ) + I * (μ : ℂ))) a := by
  by_cases hc : (b : ℂ) + I * (μ : ℂ) = 0
  · have hb : b = 0 := by
      have := congrArg Complex.re hc
      simpa using this
    have hμ : μ = 0 := by
      have := congrArg Complex.im hc
      simpa using this
    rw [hb, hμ, twistedMoment_zero_zero]
    simp [plateauMomentPoly]
  · rw [twistedMoment_plateauProfile ha ha0 hc]
    simp only [plateauMomentPoly, hc, if_false, ExpPoly.eval_cons, ExpPoly.eval_nil, zero_mul,
      Complex.exp_zero, mul_one, add_zero]
    ring

/-- The first frequency of a copy at a centre. -/
def rayFreq₁ (γ : ℝ) (q : XiZeroCopy) : ℂ :=
  ((-(xiSpectralPoint q).im : ℝ) : ℂ) + I * (((xiSpectralPoint q).re - γ : ℝ) : ℂ)

/-- The second frequency of a copy at a centre. -/
def rayFreq₂ (γ : ℝ) (q : XiZeroCopy) : ℂ :=
  ((-(xiSpectralPoint q).im : ℝ) : ℂ) + I * (((xiSpectralPoint q).re + γ : ℝ) : ℂ)

theorem rayFreq₁_re (γ : ℝ) (q : XiZeroCopy) : (rayFreq₁ γ q).re = -(xiSpectralPoint q).im := by
  simp [rayFreq₁]

theorem rayFreq₂_re (γ : ℝ) (q : XiZeroCopy) : (rayFreq₂ γ q).re = -(xiSpectralPoint q).im := by
  simp [rayFreq₂]

theorem rayFreq₁_im (γ : ℝ) (q : XiZeroCopy) : (rayFreq₁ γ q).im = (xiSpectralPoint q).re - γ := by
  simp [rayFreq₁]

theorem rayFreq₂_im (γ : ℝ) (q : XiZeroCopy) : (rayFreq₂ γ q).im = (xiSpectralPoint q).re + γ := by
  simp [rayFreq₂]

/-- The pair-moment polynomial of a copy at a centre. -/
def rayPairPoly (γ : ℝ) (q : XiZeroCopy) : ExpPoly :=
  plateauMomentPoly (rayFreq₁ γ q) ++ plateauMomentPoly (rayFreq₂ γ q)

theorem twistedPairMoment_plateauProfile_eq_eval {a : ℝ} (ha : 1 / 2 ≤ a) (ha0 : 0 ≤ a) (γ : ℝ)
    (q : XiZeroCopy) :
    twistedPairMoment (plateauProfile a ha0) γ q = ExpPoly.eval (rayPairPoly γ q) a := by
  unfold twistedPairMoment rayPairPoly
  rw [ExpPoly.eval_append, twistedMoment_plateauProfile_eq_eval ha ha0,
    twistedMoment_plateauProfile_eq_eval ha ha0]
  rfl

/-- The ray-term polynomial of a copy at a centre. -/
def rayTermPoly (γ : ℝ) (q : XiZeroCopy) : ExpPoly :=
  ExpPoly.smul (-(1 / 4 : ℂ) / xiSpectralPoint q ^ (2 : ℕ))
    (ExpPoly.mul (rayPairPoly γ q) (rayPairPoly γ q))

/-- **The ray term of the plateau profile is an exponential polynomial in the aperture.** -/
theorem twistedRayTerm_plateauProfile_eq_eval {a : ℝ} (ha : 1 / 2 ≤ a) (ha0 : 0 ≤ a) (γ : ℝ)
    (q : XiZeroCopy) :
    twistedRayTerm (plateauProfile a ha0) γ q = ExpPoly.eval (rayTermPoly γ q) a := by
  unfold twistedRayTerm rayTermPoly
  rw [ExpPoly.eval_smul, ExpPoly.eval_mul, ← twistedPairMoment_plateauProfile_eq_eval ha ha0]
  ring

/-- The normalised ray-term polynomial: exponents shifted by `−2Θ`, realised as the product of the
two `−Θ`-shifted pair polynomials. -/
def normalizedRayTermPoly (Θ γ : ℝ) (q : XiZeroCopy) : ExpPoly :=
  ExpPoly.smul (-(1 / 4 : ℂ) / xiSpectralPoint q ^ (2 : ℕ))
    (ExpPoly.mul (expPolyShift (-(Θ : ℂ)) (rayPairPoly γ q))
      (expPolyShift (-(Θ : ℂ)) (rayPairPoly γ q)))

theorem eval_normalizedRayTermPoly {a : ℝ} (ha : 1 / 2 ≤ a) (ha0 : 0 ≤ a) (Θ γ : ℝ)
    (q : XiZeroCopy) :
    ExpPoly.eval (normalizedRayTermPoly Θ γ q) a
      = Complex.exp (-(2 * Θ : ℝ) * (a : ℂ)) * twistedRayTerm (plateauProfile a ha0) γ q := by
  unfold normalizedRayTermPoly
  rw [ExpPoly.eval_smul, ExpPoly.eval_mul, eval_expPolyShift,
    ← twistedPairMoment_plateauProfile_eq_eval ha ha0]
  unfold twistedRayTerm
  have : Complex.exp (-(2 * Θ : ℝ) * (a : ℂ))
      = Complex.exp (-(Θ : ℂ) * (a : ℂ)) * Complex.exp (-(Θ : ℂ) * (a : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [this]
  ring

/-- Every exponent of the pair polynomial has real part `±Im z_q` or `0`. -/
theorem rayPairPoly_exponent_re (γ : ℝ) (q : XiZeroCopy) {p : ℂ × ℂ} (hp : p ∈ rayPairPoly γ q) :
    p.2.re = -(xiSpectralPoint q).im ∨ p.2.re = (xiSpectralPoint q).im ∨ p.2.re = 0 := by
  unfold rayPairPoly plateauMomentPoly at hp
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · split_ifs at hp with h
    · simp at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · left; exact rayFreq₁_re γ q
      · right; right; rfl
      · right; left; simp [rayFreq₁_re]
      · right; right; rfl
  · split_ifs at hp with h
    · simp at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · left; exact rayFreq₂_re γ q
      · right; right; rfl
      · right; left; simp [rayFreq₂_re]
      · right; right; rfl

/-- If `Θ ≥ |Im z_q|` the normalised ray-term polynomial is decaying. -/
theorem decaying_normalizedRayTermPoly {Θ : ℝ} (hΘ : 0 ≤ Θ) (γ : ℝ) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| ≤ Θ) :
    ExpPoly.Decaying (normalizedRayTermPoly Θ γ q) := by
  unfold normalizedRayTermPoly
  refine ExpPoly.decaying_smul _ (ExpPoly.decaying_mul ?_ ?_) <;>
  · refine decaying_expPolyShift fun p hp => ?_
    simp only [Complex.neg_re, Complex.ofReal_re]
    have h := abs_le.mp hq
    rcases rayPairPoly_exponent_re γ q hp with h1 | h1 | h1 <;> rw [h1] <;> linarith

end

end RHTower
