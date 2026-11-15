import GaloisForLFunctions.RHTower.ArithmeticCotangentPhaseTransport

/-!
# Nonvanishing of the two Deligne–Lusztig rational trace expressions

The inverse-chord coefficient from Kuzmin–Landau identifies the imaginary
parts of the split and unitary expressions in https://arxiv.org/abs/2610.40335,
Propositions 3.15 and 4.4. Cotangent monotonicity makes both strictly negative.
The parameter may be any integer at least two; primality is unnecessary for
these analytic identities. These are statements about the explicit rational
expressions, without assuming any geometric trace formula.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LefschetzTrace

/-- A unit complex number whose argument is measured in turns. -/
def unitPhase (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

/-- Multiplying the phase by an integer raises its unit value to that power. -/
theorem unitPhase_nat_mul (t : ℝ) (m : ℕ) :
    unitPhase ((m : ℝ) * t) = unitPhase t ^ m := by
  rw [unitPhase, unitPhase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The second cyclotomic phase is the corresponding power of the first. -/
theorem unitPhase_nat_div (m : ℕ) (d : ℝ) :
    unitPhase ((m : ℝ) / d) = unitPhase (1 / d) ^ m := by
  rw [← unitPhase_nat_mul]
  congr 1
  ring

/-- The inverse-chord coefficient, expressed without a complex division. -/
def chordFactor (t : ℝ) : ℂ := -RHTower.Sieve.klCoeff t

/-- Cotangent of the half-angle of a phase measured in turns. -/
def cotangent (t : ℝ) : ℝ := Real.cos (Real.pi * t) / Real.sin (Real.pi * t)

private theorem chordFactor_rectangular (t : ℝ) :
    chordFactor t = (1 / 2 : ℂ) + Complex.I / 2 * (cotangent t : ℂ) := by
  change -(-(1 / 2 : ℂ) - Complex.I / 2 * (cotangent t : ℂ)) = _
  ring

theorem chordFactor_re (t : ℝ) : (chordFactor t).re = 1 / 2 := by
  rw [chordFactor_rectangular]
  simp

theorem chordFactor_im (t : ℝ) : (chordFactor t).im = cotangent t / 2 := by
  rw [chordFactor_rectangular]
  simp <;> ring

/-- In the open first turn the chord coefficient is the literal inverse. -/
theorem chordFactor_eq_inv (t : Set.Ioo (0 : ℝ) 1) :
    chordFactor t = (1 - unitPhase t)⁻¹ := by
  have h := RHTower.Sieve.klCoeff_mul t.property.1 t.property.2
  have hm : chordFactor t * (1 - unitPhase t) = 1 := by
    calc
      _ = RHTower.Sieve.klCoeff t * (unitPhase t - 1) := by rw [chordFactor]; ring
      _ = 1 := h
  exact eq_inv_of_mul_eq_one_left hm

/-- No chord in the open first turn vanishes. -/
theorem unitPhase_chord_ne_zero (t : Set.Ioo (0 : ℝ) 1) : 1 - unitPhase t ≠ 0 := by
  have h := RHTower.Sieve.klCoeff_mul t.property.1 t.property.2
  intro hz
  have he : unitPhase t = 1 := (sub_eq_zero.mp hz).symm
  change RHTower.Sieve.klCoeff t * (unitPhase t - 1) = 1 at h
  rw [he, sub_self, mul_zero] at h
  exact zero_ne_one h

/-- The split rational expression, with `y` denoting the `p`-th phase power. -/
def splitRational (p : ℝ) (x y : ℂ) : ℂ :=
  ((p ^ 2 + p + 1 : ℝ) : ℂ) *
    (((p + 1 : ℝ) : ℂ) * (y - x) / ((1 - x) ^ 2 * (1 - y)) +
      (1 + ((p - 1 : ℝ) : ℂ) * x) / (1 - x) ^ 2 + y ^ 2 / (1 - y) ^ 2)

/-- The unitary rational expression, with `y` denoting the `p`-th phase power. -/
def unitaryRational (p : ℝ) (x y : ℂ) : ℂ :=
  let c₀ : ℂ := (((p + 1) * (p - 2) / 2 : ℝ) : ℂ)
  let cᵤ : ℂ := (((p + 1) * (3 * p - 2) / 2 : ℝ) : ℂ)
  let cᵥ : ℂ := (((p + 1) * (3 * p - 4) / 2 : ℝ) : ℂ)
  (cᵤ * x - c₀) / (1 - x) ^ 2 -
    ((p ^ 3 + 1 : ℝ) : ℂ) * x / ((1 - x) * (1 - y)) +
    y * (cᵥ - c₀ * y) / (1 - y) ^ 2

/-- Rewriting the split expression through two inverse chords exposes its imaginary part. -/
theorem splitRational_im (p : ℝ) (t u : Set.Ioo (0 : ℝ) 1) :
    (splitRational p (unitPhase t) (unitPhase u)).im =
      (p ^ 2 + p + 1) * (p - 1) / 4 * (cotangent u - cotangent t) := by
  have he : splitRational p (unitPhase t) (unitPhase u) =
      ((p ^ 2 + p + 1 : ℝ) : ℂ) *
        (((p + 1 : ℝ) : ℂ) * chordFactor t * (chordFactor u - chordFactor t) +
          (p : ℂ) * chordFactor t ^ 2 - ((p - 1 : ℝ) : ℂ) * chordFactor t +
          (chordFactor u - 1) ^ 2) := by
    rw [splitRational, chordFactor_eq_inv, chordFactor_eq_inv]
    push_cast
    field_simp [unitPhase_chord_ne_zero t, unitPhase_chord_ne_zero u]
    ring
  rw [he]
  simp only [pow_two, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.sub_im,
    Complex.sub_re, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    chordFactor_re, chordFactor_im]
  ring

/-- The unitary self-intersection terms cancel from the imaginary part. -/
theorem unitaryRational_im (p : ℝ) (t u : Set.Ioo (0 : ℝ) 1) :
    (unitaryRational p (unitPhase t) (unitPhase u)).im =
      (p + 1) * (p ^ 2 - 1) / 4 * (cotangent u - cotangent t) := by
  let c₀ : ℂ := (((p + 1) * (p - 2) / 2 : ℝ) : ℂ)
  let cᵤ : ℂ := (((p + 1) * (3 * p - 2) / 2 : ℝ) : ℂ)
  let cᵥ : ℂ := (((p + 1) * (3 * p - 4) / 2 : ℝ) : ℂ)
  have he : unitaryRational p (unitPhase t) (unitPhase u) =
      (cᵤ - c₀) * chordFactor t ^ 2 - cᵤ * chordFactor t -
        ((p ^ 3 + 1 : ℝ) : ℂ) * (chordFactor t - 1) * chordFactor u +
        cᵥ * (chordFactor u ^ 2 - chordFactor u) - c₀ * (chordFactor u - 1) ^ 2 := by
    rw [unitaryRational, chordFactor_eq_inv, chordFactor_eq_inv]
    dsimp only [c₀, cᵤ, cᵥ]
    field_simp [unitPhase_chord_ne_zero t, unitPhase_chord_ne_zero u]
    ring
  rw [he]
  dsimp only [c₀, cᵤ, cᵥ]
  simp only [pow_two, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.sub_im,
    Complex.sub_re, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    chordFactor_re, chordFactor_im]
  ring

/-- The split expression at the canonical cyclotomic phase. -/
def splitExpression (n : ℕ) : ℂ :=
  let p : ℝ := n + 2
  splitRational p (unitPhase (1 / (p ^ 2 + p + 1))) (unitPhase (1 / (p ^ 2 + p + 1)) ^ (n + 2))

/-- The unitary expression at the canonical cyclotomic phase. -/
def unitaryExpression (n : ℕ) : ℂ :=
  let p : ℝ := n + 2
  unitaryRational p (unitPhase (1 / (p ^ 2 - 1))) (unitPhase (1 / (p ^ 2 - 1)) ^ (n + 2))

/-- The split imaginary part is strictly negative for every integer parameter at least two. -/
theorem splitExpression_im_neg (n : ℕ) : (splitExpression n).im < 0 := by
  let p : ℝ := n + 2
  have hp : 2 ≤ p := by dsimp [p]; exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 0 < p - 1 := by linarith only [hp]
  have hN : 0 < p ^ 2 + p + 1 := by positivity
  have h0 : 0 < 1 / (p ^ 2 + p + 1) := by positivity
  have hlt : 1 / (p ^ 2 + p + 1) < p / (p ^ 2 + p + 1) :=
    div_lt_div_of_pos_right (by linarith) hN
  have h1 : p / (p ^ 2 + p + 1) < 1 := by
    rw [div_lt_one hN]
    nlinarith only [sq_nonneg p]
  let t : Set.Ioo (0 : ℝ) 1 := ⟨_, h0, hlt.trans h1⟩
  let u : Set.Ioo (0 : ℝ) 1 := ⟨_, h0.trans hlt, h1⟩
  have hphase : unitPhase (p / (p ^ 2 + p + 1)) =
      unitPhase (1 / (p ^ 2 + p + 1)) ^ (n + 2) := by
    simpa only [p, Nat.cast_add, Nat.cast_ofNat] using unitPhase_nat_div (n + 2) (p ^ 2 + p + 1)
  change (splitRational p (unitPhase t) (unitPhase t ^ (n + 2))).im < 0
  rw [← hphase]
  change (splitRational p (unitPhase t) (unitPhase u)).im < 0
  rw [splitRational_im]
  have hc : cotangent u - cotangent t < 0 :=
    sub_neg.mpr (RHTower.PhaseCotangent.cotangent_strictAnti h0 hlt h1)
  exact mul_neg_of_pos_of_neg (by positivity) hc

/-- The unitary imaginary part is strictly negative for every integer parameter at least two. -/
theorem unitaryExpression_im_neg (n : ℕ) : (unitaryExpression n).im < 0 := by
  let p : ℝ := n + 2
  have hp : 2 ≤ p := by dsimp [p]; exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 0 < p - 1 := by linarith only [hp]
  have hM : 0 < p ^ 2 - 1 := by nlinarith only [hp, sq_nonneg (p - 2)]
  have h0 : 0 < 1 / (p ^ 2 - 1) := by positivity
  have hlt : 1 / (p ^ 2 - 1) < p / (p ^ 2 - 1) :=
    div_lt_div_of_pos_right (by linarith) hM
  have h1 : p / (p ^ 2 - 1) < 1 := by
    rw [div_lt_one hM]
    nlinarith only [hp, sq_nonneg (p - 2)]
  let t : Set.Ioo (0 : ℝ) 1 := ⟨_, h0, hlt.trans h1⟩
  let u : Set.Ioo (0 : ℝ) 1 := ⟨_, h0.trans hlt, h1⟩
  have hphase : unitPhase (p / (p ^ 2 - 1)) =
      unitPhase (1 / (p ^ 2 - 1)) ^ (n + 2) := by
    simpa only [p, Nat.cast_add, Nat.cast_ofNat] using unitPhase_nat_div (n + 2) (p ^ 2 - 1)
  change (unitaryRational p (unitPhase t) (unitPhase t ^ (n + 2))).im < 0
  rw [← hphase]
  change (unitaryRational p (unitPhase t) (unitPhase u)).im < 0
  rw [unitaryRational_im]
  have hc : cotangent u - cotangent t < 0 :=
    sub_neg.mpr (RHTower.PhaseCotangent.cotangent_strictAnti h0 hlt h1)
  exact mul_neg_of_pos_of_neg (by positivity) hc

/-- Both explicit trace expressions are nonzero. -/
theorem expressions_ne_zero (n : ℕ) : splitExpression n ≠ 0 ∧ unitaryExpression n ≠ 0 := by
  constructor
  · intro h
    have hi := splitExpression_im_neg n
    rw [h, Complex.zero_im] at hi
    exact (lt_irrefl 0) hi
  · intro h
    have hi := unitaryExpression_im_neg n
    rw [h, Complex.zero_im] at hi
    exact (lt_irrefl 0) hi

#print axioms splitRational_im
#print axioms unitaryRational_im
#print axioms expressions_ne_zero

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LefschetzTrace
