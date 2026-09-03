import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownVariableUpperColoring

/-!
# Uniform scalar absorption for Menon's Case II

The selected-factor dichotomy already puts every active factor above `a^(1/8)`.  This removes the
label and the horizontal displacement from the logarithmic Möbius-saving condition, leaving one
explicit scalar envelope shared by all active colors.
-/

namespace RHTower.Sieve

noncomputable section

/-- Selection-independent scalar cost sufficient to eliminate the medium-Mobius branch. -/
def menonHeathBrownCaseIIAbsorptionEnvelope
    (A : ℝ) (L X a : ℕ) : ℝ :=
  (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
    ((Real.log ((a : ℝ) ^ (1 / 8 : ℝ))) ^ (-A) *
      maynardLongPolylogEnvelope X)

/-- The selected-factor lower bound and `sigma >= 1` reduce every literal label absorption
condition to one label-independent scalar inequality. -/
theorem menonHeathBrownCaseII_absorption_of_envelope
    {A : ℝ} {L X a cells : ℕ} {T0 t sigma tau V Δ Q y : ℝ}
    {label : MenonHeathBrownCaseIILabel L X cells}
    (hA : 0 ≤ A) (ha : (64 : ℝ) ^ 8 ≤ (a : ℝ)) (hsigma : 1 ≤ sigma)
    (hselection :
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma tau V Δ Q y label)
    (henvelope : menonHeathBrownCaseIIAbsorptionEnvelope A L X a < Q) :
    (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
        (((groupedDyadicLower
          (heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q) : ℕ) : ℝ) ^ (1 - sigma) *
          (Real.log (((2 ^ heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))) ^ (-A) *
            maynardLongPolylogEnvelope X) < Q := by
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
  let R : ℝ := (a : ℝ) ^ (1 / 8 : ℝ)
  have ha1 : (1 : ℝ) < (a : ℝ) := by
    calc
      (1 : ℝ) < 64 ^ 8 := by norm_num
      _ ≤ (a : ℝ) := ha
  have hRpos : 0 < R := by dsimp only [R]; positivity
  have hlogRpos : 0 < Real.log R := by
    rw [show Real.log R = (1 / 8 : ℝ) * Real.log (a : ℝ) by
      dsimp only [R]
      exact Real.log_rpow (by positivity) _]
    exact mul_pos (by norm_num) (Real.log_pos ha1)
  have haNat : 1 ≤ a := by exact_mod_cast ha1.le
  have hRN : R ≤ N := by
    dsimp only [R, N]
    exact menonHeathBrownCaseIISelection_factorLower haNat hselection
  have hNpos : 0 < N := hRpos.trans_le hRN
  have hlogRN : Real.log R ≤ Real.log N := Real.log_le_log hRpos hRN
  have hlogNpos : 0 < Real.log N := hlogRpos.trans_le hlogRN
  have hpow : (Real.log N) ^ (-A) ≤ (Real.log R) ^ (-A) := by
    rw [Real.rpow_neg hlogNpos.le, Real.rpow_neg hlogRpos.le]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hlogNpos A)
      (Real.rpow_pos_of_pos hlogRpos A)).2
        (Real.rpow_le_rpow hlogRpos.le hlogRN hA)
  have hgroup :
      (((groupedDyadicLower
        (heathBrownBoxFactorExponent
          label.box.a label.box.b label.box.q) : ℕ) : ℝ) ^ (1 - sigma)) ≤ 1 := by
    have hgroupNat : 1 ≤ groupedDyadicLower
        (heathBrownBoxFactorExponent label.box.a label.box.b label.box.q) :=
      one_le_groupedDyadicLower
        (heathBrownBoxFactorExponent label.box.a label.box.b label.box.q)
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hgroupNat) (by linarith)
  have hcost :
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
          (((groupedDyadicLower
            (heathBrownBoxFactorExponent
              label.box.a label.box.b label.box.q) : ℕ) : ℝ) ^ (1 - sigma) *
            (Real.log N) ^ (-A) * maynardLongPolylogEnvelope X)
        ≤ menonHeathBrownCaseIIAbsorptionEnvelope A L X a := by
    rw [menonHeathBrownCaseIIAbsorptionEnvelope]
    change (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
        (((groupedDyadicLower
          (heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q) : ℕ) : ℝ) ^ (1 - sigma) *
          (Real.log N) ^ (-A) * maynardLongPolylogEnvelope X) ≤
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
        ((Real.log R) ^ (-A) * maynardLongPolylogEnvelope X)
    have henv0 : 0 ≤ maynardLongPolylogEnvelope X :=
      (one_le_maynardLongPolylogEnvelope X).trans' zero_le_one
    have hinner :
        (((groupedDyadicLower
          (heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q) : ℕ) : ℝ) ^ (1 - sigma)) *
            (Real.log N) ^ (-A) ≤ (Real.log R) ^ (-A) := by
      calc
        (((groupedDyadicLower
            (heathBrownBoxFactorExponent
              label.box.a label.box.b label.box.q) : ℕ) : ℝ) ^ (1 - sigma)) *
              (Real.log N) ^ (-A)
            ≤ 1 * (Real.log N) ^ (-A) :=
          mul_le_mul_of_nonneg_right hgroup (Real.rpow_nonneg hlogNpos.le _)
        _ = (Real.log N) ^ (-A) := one_mul _
        _ ≤ (Real.log R) ^ (-A) := hpow
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hinner henv0) (by positivity)
  have hcost' :
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
          (((groupedDyadicLower
            (heathBrownBoxFactorExponent
              label.box.a label.box.b label.box.q) : ℕ) : ℝ) ^ (1 - sigma) *
            (Real.log (((2 ^ heathBrownBoxFactorExponent
              label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))) ^ (-A) *
              maynardLongPolylogEnvelope X)
        ≤ menonHeathBrownCaseIIAbsorptionEnvelope A L X a := by
    simpa only [N] using hcost
  exact hcost'.trans_lt henvelope

end

end RHTower.Sieve
