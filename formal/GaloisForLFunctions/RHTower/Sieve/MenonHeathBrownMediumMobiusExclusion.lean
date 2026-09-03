import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIColoring
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownMediumMobiusPolynomialFrequency

/-!
# Pointwise exclusion of Menon's medium Mobius color

The arbitrary logarithmic saving is inserted into the exact selected-core lower bound.  This
module exposes the sole remaining task as a scalar absorption inequality; no frequency count is
spent on the Mobius branch.
-/

noncomputable section

namespace RHTower.Sieve

open Filter Finset

/-- A medium factor of length at least `a^(1/8)` has a twenty-fourth-power frequency horizon at
least `a^3`.  This is the exact exponent arithmetic used in Menon's Case IIa. -/
theorem rpow_cube_le_pow_twentyFour_of_rpow_oneEighth_le
    {a N : ℝ} (ha : 0 ≤ a) (hN : a ^ (1 / 8 : ℝ) ≤ N) :
    a ^ (3 : ℕ) ≤ N ^ (24 : ℕ) := by
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg ha _) hN 24
  calc
    a ^ (3 : ℕ) = (a ^ (1 / 8 : ℝ)) ^ (24 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
      norm_num
    _ ≤ N ^ (24 : ℕ) := hpow

/-- The medium alternative itself supplies the polynomial-frequency premise from the ambient
cubic frequency band. -/
theorem abs_selectedFrequency_le_factor_pow_twentyFour_of_medium
    {L X a cells : ℕ} {T0 t sigma tau V Δ Q y : ℝ}
    {label : MenonHeathBrownCaseIILabel L X cells}
    (hselection :
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma tau V Δ Q y label)
    (hmedium : label.isLong = false)
    (hfrequency : |y + tau| ≤ (a : ℝ) ^ (3 : ℕ)) :
    |y + tau| ≤
      (((2 ^ heathBrownBoxFactorExponent
        label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^ (24 : ℕ) := by
  have hbranch := hselection.2.2.2.2.2
  simp only [hmedium, Bool.false_eq_true, ↓reduceIte] at hbranch
  exact hfrequency.trans
    (rpow_cube_le_pow_twentyFour_of_rpow_oneEighth_le (by positivity) hbranch.1)

/-- Once the literal logarithmic saving absorbs the finite box cost, a selected factor cannot be
Mobius.  The theorem stays on the actual Perron line and retains the full box lower edge. -/
theorem eventually_heathBrownCaseII_selectedFactor_ne_moebius
    (A : ℝ) :
    ∀ᶠ q : ℕ in atTop,
      ∀ (L X a cells : ℕ) (T0 t sigma tau V Δ Q y : ℝ)
        (label : MenonHeathBrownCaseIILabel L X cells),
      1 ≤ X →
      1 ≤ sigma →
      heathBrownBoxFactorExponent label.box.a label.box.b label.box.q label.factor = q →
      2 ^ q ≤ L →
      |y + tau| ≤ (((2 ^ q : ℕ) : ℝ)) ^ (24 : ℕ) →
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
          (((groupedDyadicLower
            (heathBrownBoxFactorExponent
              label.box.a label.box.b label.box.q) : ℕ) : ℝ) ^ (1 - sigma) *
            (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A) *
              maynardLongPolylogEnvelope X) < Q →
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma tau V Δ Q y label →
      heathBrownBoxFactorKind 3 label.box.m label.factor ≠ .moebius := by
  filter_upwards [
    eventually_norm_heathBrownDyadicCoreProduct_of_medium_moebius_le_rpow A]
    with q hq
  intro L X a cells T0 t sigma tau V Δ Q y label hX hsigma hexponent hqL
    hfrequency habsorb hselection hkind
  have hupper := hq L X 3 label.box label.factor sigma (y + tau)
    hX hsigma hkind hexponent hqL hfrequency
  have hselectedCore : Q ≤
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
        ‖heathBrownDyadicCoreProduct L X 3 label.box.m
          label.box.a label.box.b label.box.q
          ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)‖ :=
    hselection.2.2.2.1
  have hcost0 : 0 ≤
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hupper hcost0
  exact (not_lt_of_ge (hselectedCore.trans hscaled)) habsorb

end RHTower.Sieve
