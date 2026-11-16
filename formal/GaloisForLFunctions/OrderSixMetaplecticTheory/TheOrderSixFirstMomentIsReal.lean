import GaloisForLFunctions.OrderSixMetaplecticTheory.TheOrderSixFamilyIsOrthogonalToTheUntwistedSquare
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheUntwistedThetaMainTermIsReal

/-!
# The order-six first moment is real

The order-six weight of a row is `ω₆(c) = Γ(c) χ₂(c) G̃(c)²`, the root number `Φ(c)` of a squarefree row
(`rowRootNumber_eq_weil_mul_cubicTwo`). Each factor conjugates under `c ↦ c̄`: the Weil index by the explicit
formula `Γ(a + bω) = (1 + i^{−b} + i^a + i^{b−a})/2` (`fixedDualAverage_conj`), `χ₂ = (·/−2)₃²` because `−2` is
real, and `G̃` by `normalizedCubicUnitGauss_conj`. Hence `ω₆(c̄) = \overline{ω₆(c)}` (`orderSixWeight_conj`).

Conjugation preserves the squarefree odd rows and their norms, so the Gaussian-smoothed first moment of the
order-six family is real for every `X` (`star_gaussianSmoothedOrderSix`): any main term of the family is a real
multiple of `X^{2/3}`, a real combination of the 2-ramified twisted residues.
-/

noncomputable section

open scoped Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover

theorem star_I_zpow (k : ℤ) : star (Complex.I ^ k) = Complex.I ^ (-k) := by
  rw [star_zpow₀, Complex.star_def, Complex.conj_I, ← Complex.inv_I, inv_zpow, zpow_neg]

/-- `Γ(c̄) = \overline{Γ(c)}`. -/
theorem fixedDualAverage_conj (c : O) : fixedDualAverage (conjO c) = star (fixedDualAverage c) := by
  obtain ⟨a, b, rfl⟩ := Coordinates.exists_coordinates c
  change fixedDualAverage (conjO (Coordinates.eval a b)) = star (fixedDualAverage (Coordinates.eval a b))
  rw [Coordinates.conj_eval, fixedDualAverage_formula, fixedDualAverage_formula, star_div₀, star_add, star_add,
    star_add, star_one, star_I_zpow, star_I_zpow, star_I_zpow, star_ofNat]
  congr 1
  rw [neg_neg, show -b - (a - b) = -a by ring, show -(b - a) = a - b by ring]
  ring

theorem cubicTwoChar_conj (c : O) : cubicTwoChar (conjO c) = star (cubicTwoChar c) := by
  unfold cubicTwoChar
  have h : symbol (conjO c) (-2) = conjO (symbol c (-2)) := by
    have h' := symbol_conjO c (-2)
    rwa [map_neg, map_ofNat] at h'
  rw [h, ringComplex_conjO, star_pow]

/-- The order-six weight `ω₆(c) = Γ(c) χ₂(c) G̃(c)²`. -/
def orderSixWeight (c : O) : ℂ := fixedDualAverage c * cubicTwoChar c * normalizedCubicUnitGauss c ^ 2

/-- **`ω₆(c̄) = \overline{ω₆(c)}`.** -/
theorem orderSixWeight_conj (c : O) : orderSixWeight (conjO c) = star (orderSixWeight c) := by
  unfold orderSixWeight
  rw [fixedDualAverage_conj, cubicTwoChar_conj, normalizedCubicUnitGauss_conj, star_mul', star_mul', star_pow]

/-- The coefficient of the order-six family on ideals: `ω₆` of the primary generator on squarefree odd rows. -/
def orderSixCoefficient (A : Ideal O) : ℂ :=
  if Squarefree A ∧ primaryIdealGenerator A ≠ 0 ∧ ¬ (2 : O) ∣ primaryIdealGenerator A then
    orderSixWeight (primaryIdealGenerator A) else 0

theorem two_dvd_conjO_iff {x : O} : (2 : O) ∣ conjO x ↔ (2 : O) ∣ x := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨conjO k, ?_⟩
    rw [← conjO_conjO x, hk, map_mul, map_ofNat conjO]
  · rintro ⟨k, rfl⟩
    exact ⟨conjO k, by rw [map_mul, map_ofNat conjO]⟩

theorem orderSixCoefficient_conj (A : Ideal O) :
    orderSixCoefficient (conjIdeal A) = star (orderSixCoefficient A) := by
  have hiff : (Squarefree (conjIdeal A) ∧ primaryIdealGenerator (conjIdeal A) ≠ 0 ∧
      ¬ (2 : O) ∣ primaryIdealGenerator (conjIdeal A)) ↔
      (Squarefree A ∧ primaryIdealGenerator A ≠ 0 ∧ ¬ (2 : O) ∣ primaryIdealGenerator A) := by
    rw [squarefree_conjIdeal_iff, primaryIdealGenerator_conj, two_dvd_conjO_iff]
    exact and_congr_right' (and_congr_left' (not_congr (map_eq_zero_iff _ conjO.injective)))
  unfold orderSixCoefficient
  by_cases h : Squarefree A ∧ primaryIdealGenerator A ≠ 0 ∧ ¬ (2 : O) ∣ primaryIdealGenerator A
  · rw [if_pos (hiff.mpr h), if_pos h, primaryIdealGenerator_conj, orderSixWeight_conj]
  · rw [if_neg (mt hiff.mp h), if_neg h, star_zero]

/-- The Gaussian-smoothed first moment of the order-six family over squarefree odd rows. -/
def gaussianSmoothedOrderSix (X : ℝ) : ℂ :=
  ∑' A : Ideal O, orderSixCoefficient A *
    (RHTower.smoothAFELogGaussian (Real.log ((Ideal.absNorm A : ℝ) / X)) : ℂ)

/-- **The order-six first moment is real.** -/
theorem star_gaussianSmoothedOrderSix (X : ℝ) :
    star (gaussianSmoothedOrderSix X) = gaussianSmoothedOrderSix X := by
  let f : Ideal O → ℂ := fun A => orderSixCoefficient A *
    (RHTower.smoothAFELogGaussian (Real.log ((Ideal.absNorm A : ℝ) / X)) : ℂ)
  change star (∑' A, f A) = ∑' A, f A
  calc star (∑' A, f A) = ∑' A, star (f A) := tsum_star
    _ = ∑' A, f (conjIdealEquiv.toEquiv A) := by
        congr 1
        funext A
        change _ = orderSixCoefficient (conjIdeal A) *
          (RHTower.smoothAFELogGaussian (Real.log ((Ideal.absNorm (conjIdeal A) : ℝ) / X)) : ℂ)
        rw [orderSixCoefficient_conj, absNorm_conjIdeal, star_mul', Complex.star_def, Complex.conj_ofReal]
    _ = ∑' A, f A := conjIdealEquiv.toEquiv.tsum_eq f

end GaloisForLFunctions.OrderSixMetaplecticTheory
