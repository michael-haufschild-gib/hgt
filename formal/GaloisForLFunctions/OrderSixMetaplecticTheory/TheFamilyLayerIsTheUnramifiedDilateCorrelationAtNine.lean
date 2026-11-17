import GaloisForLFunctions.OrderSixMetaplecticTheory.EveryLayerIsTheUnitLayerOfAnEvenTwist

/-!
# The family layer is the unramified dilate correlation at nine

Twisted multiplicativity at the ramified frequency `9 = ωλ⁴` turns the 3-adic character of the family layer into a
dilation. For `λ ∤ h` the source mask leaves only `h = ±g` with `g` primary, and
`T(9g)T(1) = (9/g)₃T(9)T(g)`, so (`thetaNine_identity`)

`T(h) T(9h) T(1) = (9/h)₃ T(9) T(h)²`,   `(9/h)₃ = (ω²λ²/h)₃²`.

Hence the unramified dilate correlation `Σ_{λ ∤ h} ψ(h)T(h)T(9h)(4π|ξ_h|)^{−s}` is `T(9)/T(1)` times the unramified
theta square twisted by `ψξ_{ω²λ²}` (`unramifiedDilateNine_eq`), and for even `ψ` (`unramifiedDilateNine_eq_layer`)

`T(1) Σ_{λ ∤ h} ψ(h)T(h)T(9h)(4π|ξ_h|)^{−s} = 2T(9) C̄² Z_{ψ³}(3s/2 − 1)(4π|ξ₁|)^{−s} S^ψ_{ω²λ²}(s/2)`:

the layer `ω²λ²` of the order-six family is read by the correlation of `θ` with its dilate by `9` (the Hecke
correlation `θ(3w)θ(w/3)` at the ramified prime), on unramified frequencies, with weight `T(9)`.
-/

noncomputable section

open MeasureTheory UniqueFactorizationMonoid
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicKubota MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi
  SpectralTheoryOfTheCubicCover

theorem not_three_dvd_of_not_lambda_dvd {h : O} (hl : ¬ lambda ∣ h) : ¬ (3 : O) ∣ h :=
  fun h3 => hl (lambda_dvd_three.trans h3)

theorem symbol_neg_den (x c : O) : symbol x (-c) = symbol x c := by
  unfold symbol
  rw [Ideal.span_singleton_neg]

/-- `T(g)T(9g)T(1) = (9/g)₃T(9)T(g)²` for primary `g`. -/
theorem thetaNine_primary {g : O} (hg0 : g ≠ 0) (hg : lambda ^ 2 ∣ g - 1) :
    rationalSourceResidualFourierCoefficient g * rationalSourceResidualFourierCoefficient (9 * g) *
        rationalSourceResidualFourierCoefficient 1 =
      ringComplex (symbol 9 g) * rationalSourceResidualFourierCoefficient 9 *
        rationalSourceResidualFourierCoefficient g ^ 2 := by
  have hgen : primaryIdealGenerator (Ideal.span {g}) = g := primaryIdealGenerator_span g hg0 hg
  have hI : primaryIdealGenerator (Ideal.span {g}) ≠ 0 := by rw [hgen]; exact hg0
  have h := sourceCoefficient_twisted_mul 9 (by norm_num) (Ideal.span {g}) hI
    (by rw [hgen]; exact nine_coprime_of_primary hg)
  rw [hgen] at h
  linear_combination rationalSourceResidualFourierCoefficient g * h

/-- **The dilate by nine on unramified frequencies:** `T(h)T(9h)T(1) = (9/h)₃T(9)T(h)²` for `λ ∤ h`. -/
theorem thetaNine_identity (h : O) (hl : ¬ lambda ∣ h) :
    rationalSourceResidualFourierCoefficient h * rationalSourceResidualFourierCoefficient (9 * h) *
        rationalSourceResidualFourierCoefficient 1 =
      ringComplex (symbol 9 h) * rationalSourceResidualFourierCoefficient 9 *
        rationalSourceResidualFourierCoefficient h ^ 2 := by
  by_cases hT : rationalSourceResidualFourierCoefficient h = 0
  · rw [hT]
    ring
  have hh : h ≠ 0 := fun h0 => hl (h0 ▸ dvd_zero _)
  rcases primary_or_negative_primary_of_source_mask h (not_three_dvd_of_not_lambda_dvd hl)
      (sourceFourier_phase_of_ne_zero h hh hT) with hp | hp
  · exact thetaNine_primary hh hp
  · have hg := thetaNine_primary (neg_ne_zero.mpr hh) hp
    rw [show 9 * -h = -(9 * h) by ring, rationalSourceResidualFourierCoefficient_neg,
      rationalSourceResidualFourierCoefficient_neg, symbol_neg_den] at hg
    exact hg

/-- The unramified dilate correlation `Σ_{λ ∤ h} ψ(h)T(h)T(9h)(4π|ξ_h|)^{−s}`. -/
def unramifiedDilateNine (ψ : O →* ℂ) (s : ℂ) : ℂ :=
  besselDirichlet (fun h => if lambda ∣ h then 0 else ψ h *
    (rationalSourceResidualFourierCoefficient h * rationalSourceResidualFourierCoefficient (9 * h))) s

/-- **The unramified dilate correlation at nine is the `ξ_{ω²λ²}`-twisted unramified theta square.** -/
theorem unramifiedDilateNine_eq (ψ : O →* ℂ) (s : ℂ) :
    rationalSourceResidualFourierCoefficient 1 * unramifiedDilateNine ψ s =
      rationalSourceResidualFourierCoefficient 9 *
        twistDirichletG (ψ * layerChar (omega ^ 2 * lambda ^ 2) * unramifiedChar) s := by
  unfold unramifiedDilateNine twistDirichletG besselDirichlet
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun h => ?_
  dsimp only
  split_ifs with h0 hl
  · ring
  · have hz : unramifiedChar h = 0 := by
      change (if lambda ∣ h then 0 else 1 : ℂ) = 0
      rw [if_pos hl]
    rw [MonoidHom.mul_apply, hz]
    ring
  · have hu : unramifiedChar h = 1 := by
      change (if lambda ∣ h then 0 else 1 : ℂ) = 1
      rw [if_neg hl]
    have hξ : layerChar (omega ^ 2 * lambda ^ 2) h = ringComplex (symbol 9 h) := by
      change (if lambda ∣ h then 0 else ringComplex (symbol (omega ^ 2 * lambda ^ 2) h) ^ 2) = _
      rw [if_neg hl, symbol_nine_eq_sq, map_pow]
    have hid := thetaNine_identity h hl
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, hu, hξ]
    linear_combination (ψ h * ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) * hid

/-- `ω²` as a unit. -/
def omegaSqUnit : Oˣ :=
  ⟨omega ^ 2, omega, by rw [← pow_succ]; exact omega_primitive.pow_eq_one,
    by rw [← pow_succ']; exact omega_primitive.pow_eq_one⟩

/-- **The unramified twist by an even `ψξ_{uλ^m}` reads the layer `uλ^m` of `ψ`.** -/
theorem unramifiedTwist_layer (ψ : O →* ℂ) (hψb : ∀ x, ‖ψ x‖ ≤ 1) (hev : ψ (-1) = 1) (u : Oˣ) (m : ℕ)
    (s : ℂ) (hs : 4 < s.re) :
    twistDirichletG (ψ * layerChar ((u : O) * lambda ^ m) * unramifiedChar) s = 2 * star rationalSourceThetaScalar ^ 2 *
      cubeZetaG ψ (3 * (s / 2) - 1) * ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ^ (-s) *
        twistedSquarefreeSeriesG ψ ((u : O) * lambda ^ m) (s / 2) := by
  have hb : ∀ x, ‖(ψ * layerChar ((u : O) * lambda ^ m)) x‖ ≤ 1 := fun x => by
    rw [MonoidHom.mul_apply, norm_mul]
    exact mul_le_one₀ (hψb x) (norm_nonneg _) (layerChar_norm_le _ x)
  rw [unramifiedTwist_eq _ hb s hs, cubeZetaG_mul_eq ψ _ (layerChar_cube u m),
    ← twistedSquarefreeSeriesG_layer, MonoidHom.mul_apply, MonoidHom.mul_apply, map_one, map_one, hev,
    layerChar_neg_one]
  ring

/-- **The family layer is the unramified dilate correlation at nine.** For even `ψ` and `Re s > 4`,
`T(1) Σ_{λ∤h}ψ(h)T(h)T(9h)(4π|ξ_h|)^{−s} = 2T(9)C̄²Z_{ψ³}(3s/2 − 1)(4π|ξ₁|)^{−s}S^ψ_{ω²λ²}(s/2)`. -/
theorem unramifiedDilateNine_eq_layer (ψ : O →* ℂ) (hψb : ∀ x, ‖ψ x‖ ≤ 1) (hev : ψ (-1) = 1) (s : ℂ)
    (hs : 4 < s.re) :
    rationalSourceResidualFourierCoefficient 1 * unramifiedDilateNine ψ s =
      2 * rationalSourceResidualFourierCoefficient 9 * star rationalSourceThetaScalar ^ 2 *
        cubeZetaG ψ (3 * (s / 2) - 1) * ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ^ (-s) *
          twistedSquarefreeSeriesG ψ (omega ^ 2 * lambda ^ 2) (s / 2) := by
  rw [unramifiedDilateNine_eq, show omega ^ 2 * lambda ^ 2 = (omegaSqUnit : O) * lambda ^ 2 from rfl,
    unramifiedTwist_layer ψ hψb hev omegaSqUnit 2 s hs]
  ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
