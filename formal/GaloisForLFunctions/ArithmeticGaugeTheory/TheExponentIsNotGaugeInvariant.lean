import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponent

/-!
# The gauge exponent is not gauge invariant

Gauge-invariant data are constant on the gauge torus, since the gauge torus is a single orbit of its
own translations. The Möbius gauge exponent is not constant: it is at most `1/2` at Haar-almost every
point and at least `3/4` on a residual set. Consequently no certificate built from gauge-invariant
(multiplicative) information can bound the exponent at the trivial point below `3/4`.

* **Both values occur** (`exists_gaugeExponent_moebius_le_half`,
  `exists_threeQuarters_le_gaugeExponent_moebius`). A full-measure set and a residual set of the
  compact torus are nonempty.
* **Not constant** (`gaugeExponent_moebius_not_const`).
* **No multiplicative certificate** (`threeQuarters_le_of_gaugeInvariant_bound`). If `Φ` is invariant
  under every gauge translation and bounds the Möbius exponent at every gauge point, then
  `Φ(0) ≥ 3/4`. A bound at `0` that is good enough for RH must use information that distinguishes `0`
  from other gauge points.

This is the exponent form of the statement that multiplicative arguments prove almost-sure laws
and decide nothing at the trivial point. It is the gauge-theoretic reason why an index ceiling, or any
Riemann–Roch substitute, cannot be read from gauge-invariant data.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- Some gauge point has Möbius exponent at most `1/2`. -/
theorem exists_gaugeExponent_moebius_le_half :
    ∃ x : GaugeTorus, gaugeExponent moebiusSource x ≤ 1 / 2 :=
  (ae_gaugeExponent_le_half norm_moebiusSource_le).exists

/-- Some gauge point has Möbius exponent at least `3/4`. -/
theorem exists_threeQuarters_le_gaugeExponent_moebius :
    ∃ x : GaugeTorus, 3 / 4 ≤ gaugeExponent moebiusSource x :=
  (dense_of_mem_residual moebius_exponent_threeQuarters_residual).nonempty

/-- **The Möbius exponent is not constant on the gauge torus.** -/
theorem gaugeExponent_moebius_not_const :
    ¬ ∃ c : ℝ, ∀ x : GaugeTorus, gaugeExponent moebiusSource x = c := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx⟩ := exists_gaugeExponent_moebius_le_half
  obtain ⟨y, hy⟩ := exists_threeQuarters_le_gaugeExponent_moebius
  rw [hc] at hx hy
  linarith

/-- **No multiplicative certificate.** A gauge-invariant bound on the Möbius exponent is at least
`3/4` everywhere, in particular at the trivial point. -/
theorem threeQuarters_le_of_gaugeInvariant_bound (Φ : GaugeTorus → ℝ)
    (hΦ : ∀ x y : GaugeTorus, Φ (x + y) = Φ x)
    (hb : ∀ x : GaugeTorus, gaugeExponent moebiusSource x ≤ Φ x) : 3 / 4 ≤ Φ 0 := by
  obtain ⟨y, hy⟩ := exists_threeQuarters_le_gaugeExponent_moebius
  have h := hΦ 0 y
  rw [zero_add] at h
  linarith [hb y]

end GaloisForLFunctions.ArithmeticGaugeTheory
