import GaloisForLFunctions.ArithmeticGaugeTheory.TheTypicalExponentIsOneHalf
import GaloisForLFunctions.ArithmeticGaugeTheory.TheArchimedeanLineCarriesTheExponent
import GaloisForLFunctions.RHTower.MertensSquareRootOmega

/-!
# The trivial point is never better than typical

Haar-almost every gauge point has Möbius exponent `1/2` (`ae_gaugeExponent_moebius_eq_half`). At the
trivial point the twisted Möbius sums are the Mertens function, and `M(x)` is not `o(√x)`
(`RHTower.not_mertensFunctionReal_isLittleO_sqrt`, from a zero on the critical line). So:

* **The floor at the trivial point** (`half_le_gaugeExponent_moebius_trivial`). The trivial point has
  exponent at least `1/2`, i.e. at least the typical exponent
  (`typicalExponent_le_gaugeExponent_moebius_trivial`). Consequently `Θ ≥ 1/2`
  (`half_le_zetaZeroAbscissa`).
* **RH as an equality** (`riemannHypothesis_iff_trivialPoint_eq_typical`). RH holds iff the trivial
  point has exactly the typical exponent.
* **The class of the trivial point** (`typicalExponent_le_gaugeExponent_moebius_finiteFlip`,
  `typicalExponent_le_gaugeExponent_moebius_verticalShift`). Finite modifications and vertical shifts of
  the trivial point are never better than typical either.

The exponent of the trivial point can only err upward. RH is therefore an extremal statement: the
trivial point sits at the floor that Haar-almost every point attains. Whether `1/2` is the floor of the
exponent on all of `G` is open.
-/

open MeasureTheory Finset Filter Topology Asymptotics

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- At the trivial point the twisted Möbius sum is the Mertens function. -/
theorem norm_moebiusGaugeSum_trivial (x : ℝ) :
    ‖moebiusGaugeSum ⌊x⌋₊ 0‖ = |RHTower.mertensFunctionReal x| := by
  have h : moebiusGaugeSum ⌊x⌋₊ 0 = ((RHTower.mertensFunctionReal x : ℝ) : ℂ) := by
    simp [moebiusGaugeSum, RHTower.mertensFunctionReal, twist_trivialPoint]
  rw [h, Complex.norm_real, Real.norm_eq_abs]

/-- **The floor at the trivial point.** The Möbius exponent of the trivial point is at least `1/2`. -/
theorem half_le_gaugeExponent_moebius_trivial : 1 / 2 ≤ gaugeExponent moebiusSource 0 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨θ, h1, h2⟩ := exists_between hlt
  obtain ⟨C, hC, hb⟩ := gaugePowerBound_moebius_iff.mp
    (gaugePowerBound_of_gaugeExponent_lt norm_moebiusSource_le h1)
  have hθ0 : 0 ≤ θ := (gaugeExponent_nonneg norm_moebiusSource_le).trans h1.le
  -- A power bound below `1/2` makes `M(x) = o(√x)`.
  refine RHTower.not_mertensFunctionReal_isLittleO_sqrt (IsLittleO.of_bound fun c hc => ?_)
  have hgrow : Tendsto (fun x : ℝ => x ^ (1 / 2 - θ)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hgrow.eventually_ge_atTop (C * 2 ^ θ / c)]
    with x hx1 hx2
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, ← norm_moebiusGaugeSum_trivial, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg x)]
  have hfl : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * x := by
    have := Nat.floor_le hx0.le
    linarith
  have hpow : (((⌊x⌋₊ : ℕ) : ℝ) + 1) ^ θ ≤ (2 * x) ^ θ :=
    Real.rpow_le_rpow (by positivity) hfl hθ0
  have hsplit : (2 * x) ^ θ = 2 ^ θ * x ^ θ := Real.mul_rpow (by norm_num) hx0.le
  have hsqrt : Real.sqrt x = x ^ θ * x ^ (1 / 2 - θ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    congr 1
    ring
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 θ
  calc ‖moebiusGaugeSum ⌊x⌋₊ 0‖ ≤ C * (((⌊x⌋₊ : ℕ) : ℝ) + 1) ^ θ := hb _
    _ ≤ C * (2 ^ θ * x ^ θ) := by rw [← hsplit]; exact mul_le_mul_of_nonneg_left hpow hC
    _ = C * 2 ^ θ / c * c * x ^ θ := by field_simp
    _ ≤ x ^ (1 / 2 - θ) * c * x ^ θ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx2 hc.le) hxθ.le
    _ = c * Real.sqrt x := by rw [hsqrt]; ring

/-- **The trivial point is never better than typical.** -/
theorem typicalExponent_le_gaugeExponent_moebius_trivial :
    typicalExponent moebiusSource ≤ gaugeExponent moebiusSource 0 := by
  rw [typicalExponent_moebius_eq_half]
  exact half_le_gaugeExponent_moebius_trivial

/-- `Θ ≥ 1/2`, read from the trivial point. -/
theorem half_le_zetaZeroAbscissa : 1 / 2 ≤ RHTower.zetaZeroAbscissa := by
  rw [← gaugeExponent_moebius_trivial]
  exact half_le_gaugeExponent_moebius_trivial

/-- **RH is the equality of the trivial and the typical exponent.** -/
theorem riemannHypothesis_iff_trivialPoint_eq_typical :
    RiemannHypothesis ↔ gaugeExponent moebiusSource 0 = typicalExponent moebiusSource := by
  rw [riemannHypothesis_iff_trivialPoint_typical]
  exact ⟨fun h => le_antisymm h typicalExponent_le_gaugeExponent_moebius_trivial, le_of_eq⟩

/-- Finite modifications of the trivial point are never better than typical. -/
theorem typicalExponent_le_gaugeExponent_moebius_finiteFlip (F : Finset ℕ) {x : GaugeTorus}
    (h : ∀ q, q.Prime → q ∉ F → twist x q = 1) :
    typicalExponent moebiusSource ≤ gaugeExponent moebiusSource x := by
  rw [gaugeExponent_moebius_finiteFlip F h, ← gaugeExponent_moebius_trivial]
  exact typicalExponent_le_gaugeExponent_moebius_trivial

/-- Vertical shifts of the trivial point are never better than typical. -/
theorem typicalExponent_le_gaugeExponent_moebius_verticalShift (t : ℝ) :
    typicalExponent moebiusSource ≤ gaugeExponent moebiusSource (verticalShift t) := by
  rw [gaugeExponent_moebius_verticalShift, ← gaugeExponent_moebius_trivial]
  exact typicalExponent_le_gaugeExponent_moebius_trivial

end GaloisForLFunctions.ArithmeticGaugeTheory
