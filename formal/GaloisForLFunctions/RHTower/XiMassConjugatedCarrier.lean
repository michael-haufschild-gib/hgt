import GaloisForLFunctions.RHTower.XiMassCausticSymbolState

/-!
# The caustic operator on the conjugated carrier

Writing the mass profile as `e^{-aZ}·G`, where `G` collects everything that varies on the scale of
the height rather than on the scale of the phase, the caustic-null jet operator becomes

`4a⁴·(e^{-aZ}G) − (e^{-aZ}G)″ = e^{-aZ}·[ (4a⁴ − a²(Z′)² + aZ″)·G + 2aZ′·G′ − G″ ]`,

and `4a⁴ − a²(Z′)² = 4a⁴ − a²w²/Z²` is the caustic symbol.

In this form the gain is transparent: the symbol is `O(u^{-1/2})` on the balance window, `Z″` is
`O(1/u)`, and `Z′` is bounded, so each application of the operator costs one derivative of `G` and
buys a half power of the height.  The `(K₀, K₁)` basis hides this, because the two Bessel carriers
share their leading exponential and the cancellation lives in their sum rather than in either slot.
-/

open Complex

namespace RHTower

noncomputable section

/-- The transport rate `Z′ = w/Z`. -/
def xiMassRadiusRate (τ w : ℂ) : ℂ := w / xiMassHeightRadius τ w

/-- **The derivative of the transport rate**: `Z″ = 1/Z − w²/Z³`. -/
theorem hasDerivAt_xiMassRadiusRate {τ w : ℂ} (hw : 0 < (τ ^ 2 + w ^ 2).re) :
    HasDerivAt (xiMassRadiusRate τ)
      (1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3) w := by
  have hZne : xiMassHeightRadius τ w ≠ 0 := xiMassHeightRadius_ne_zero hw
  have hZ : HasDerivAt (xiMassHeightRadius τ) (w / xiMassHeightRadius τ w) w :=
    hasDerivAt_xiMassHeightRadius hw
  have hdiv := (hasDerivAt_id w).div hZ hZne
  have heq : (1 * xiMassHeightRadius τ w - w * (w / xiMassHeightRadius τ w))
        / xiMassHeightRadius τ w ^ 2
      = 1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3 := by
    field_simp
  rw [← heq]
  exact hdiv

/-- **One derivative of the conjugated carrier.** -/
theorem hasDerivAt_expNegRadius_mul {a : ℝ} {τ w : ℂ} (hw : 0 < (τ ^ 2 + w ^ 2).re)
    {Gf : ℂ → ℂ} {G' : ℂ} (hG : HasDerivAt Gf G' w) :
    HasDerivAt (fun v : ℂ => Complex.exp (-(a : ℂ) * xiMassHeightRadius τ v) * Gf v)
      (Complex.exp (-(a : ℂ) * xiMassHeightRadius τ w)
        * (G' - (a : ℂ) * xiMassRadiusRate τ w * Gf w)) w := by
  have hZ : HasDerivAt (xiMassHeightRadius τ) (w / xiMassHeightRadius τ w) w :=
    hasDerivAt_xiMassHeightRadius hw
  have hexp : HasDerivAt (fun v : ℂ => Complex.exp (-(a : ℂ) * xiMassHeightRadius τ v))
      (Complex.exp (-(a : ℂ) * xiMassHeightRadius τ w)
        * (-(a : ℂ) * (w / xiMassHeightRadius τ w))) w :=
    (hZ.const_mul (-(a : ℂ))).cexp
  have hmul := hexp.mul hG
  have heq : Complex.exp (-(a : ℂ) * xiMassHeightRadius τ w)
        * (-(a : ℂ) * (w / xiMassHeightRadius τ w)) * Gf w
      + Complex.exp (-(a : ℂ) * xiMassHeightRadius τ w) * G'
      = Complex.exp (-(a : ℂ) * xiMassHeightRadius τ w)
        * (G' - (a : ℂ) * xiMassRadiusRate τ w * Gf w) := by
    rw [xiMassRadiusRate]
    ring
  rw [← heq]
  exact hmul

/-- **The caustic combination on the conjugated carrier.**  The symbol multiplies `G`; the rest is
one transport term against `G′` and one plain second derivative. -/
theorem hasDerivAt_expNegRadius_caustic {a : ℝ} {τ w : ℂ} (hw : 0 < (τ ^ 2 + w ^ 2).re)
    {Gf G'f : ℂ → ℂ} {G'' : ℂ}
    (hGw : HasDerivAt Gf (G'f w) w) (hG' : HasDerivAt G'f G'' w) :
    HasDerivAt
      (fun v : ℂ => Complex.exp (-(a : ℂ) * xiMassHeightRadius τ v)
        * (G'f v - (a : ℂ) * xiMassRadiusRate τ v * Gf v))
      (Complex.exp (-(a : ℂ) * xiMassHeightRadius τ w)
        * (G'' - (a : ℂ) * (1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3)
              * Gf w
            - 2 * (a : ℂ) * xiMassRadiusRate τ w * G'f w
            + (a : ℂ) ^ 2 * xiMassRadiusRate τ w ^ 2 * Gf w)) w := by
  have hrate := hasDerivAt_xiMassRadiusRate hw
  have hinner : HasDerivAt (fun v : ℂ => G'f v - (a : ℂ) * xiMassRadiusRate τ v * Gf v)
      (G'' - ((a : ℂ) * (1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3)
          * Gf w + (a : ℂ) * xiMassRadiusRate τ w * G'f w)) w := by
    have hprod := ((hrate.const_mul (a : ℂ)).mul hGw)
    exact hG'.sub hprod
  have hmain := hasDerivAt_expNegRadius_mul (a := a) hw hinner
  have heq : Complex.exp (-(a : ℂ) * xiMassHeightRadius τ w)
        * ((G'' - ((a : ℂ) * (1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3)
              * Gf w + (a : ℂ) * xiMassRadiusRate τ w * G'f w))
          - (a : ℂ) * xiMassRadiusRate τ w * (G'f w - (a : ℂ) * xiMassRadiusRate τ w * Gf w))
      = Complex.exp (-(a : ℂ) * xiMassHeightRadius τ w)
        * (G'' - (a : ℂ) * (1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3)
              * Gf w
            - 2 * (a : ℂ) * xiMassRadiusRate τ w * G'f w
            + (a : ℂ) ^ 2 * xiMassRadiusRate τ w ^ 2 * Gf w) := by
    ring
  rw [← heq]
  exact hmain

/-- **The caustic symbol is the diagonal of the conjugated operator.** -/
theorem xiCaustic_conjugated_symbol {a : ℝ} {τ w : ℂ} (hw : 0 < (τ ^ 2 + w ^ 2).re) (G G' G'' : ℂ) :
    4 * (a : ℂ) ^ 4 * G
        - (G'' - (a : ℂ) * (1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3) * G
          - 2 * (a : ℂ) * xiMassRadiusRate τ w * G'
          + (a : ℂ) ^ 2 * xiMassRadiusRate τ w ^ 2 * G)
      = xiMassCausticSymbolC a τ w * G
        + ((a : ℂ) * (1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3) * G
          + 2 * (a : ℂ) * xiMassRadiusRate τ w * G' - G'') := by
  have hZ2 : xiMassHeightRadius τ w ^ 2 = τ ^ 2 + w ^ 2 := xiMassHeightRadius_sq hw
  have hZne : xiMassHeightRadius τ w ≠ 0 := xiMassHeightRadius_ne_zero hw
  have hsym : xiMassCausticSymbolC a τ w
      = 4 * (a : ℂ) ^ 4 - (a : ℂ) ^ 2 * xiMassRadiusRate τ w ^ 2 := by
    rw [xiMassCausticSymbolC_eq_sub_sq hw, xiMassRadiusRate]
    field_simp
  rw [hsym]
  ring

end

end RHTower
