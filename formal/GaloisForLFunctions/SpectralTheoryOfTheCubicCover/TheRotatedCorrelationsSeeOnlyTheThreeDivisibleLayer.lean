import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquaredThetaSeriesSplitsIntoNineTwists

/-!
# The rotated correlations see only the three-divisible layer

For a unit `ε`, the rotated correlation series of the projected cubic theta coefficients is

`C_ε(s) = Σ_{h ≠ 0} T(εh) T(h) (4π|ξ_h|)^{−s}`   (`Re s > 4`; `C_1 = D`).

Across the split `h = u λ^m gen I`, twisted multiplicativity gives
`T(εuλ^m g) T(uλ^m g) T(1)² = (εuλ^m/g)₃ (uλ^m/g)₃ T(εuλ^m) T(uλ^m) T(g)²`, and the product of symbols is the
square `(ε²uλ^m/g)₃²` (`symbol_rotated_pair`: `(εuλ^m)(uλ^m) ε³ = (ε²uλ^m)²`). Hence
(`rotatedCorrelation_eq_zeta_mul`)

`C_ε(s) = \overline{C}² Z₀(3s/2 − 1) Σ_{u, m} (T(εuλ^m) T(uλ^m)/T(1)²) (4π|ξ_{uλ^m}|)^{−s} S_{ε²uλ^m}(s/2)`.

For `ε ≠ ±1` the layers `m = 0` and `m = 1` vanish (`rotatedLayerCoeff_zero`, `rotatedLayerCoeff_one`):
`T(u)` needs `u = ±1`, and then `T(εu)` needs `εu = ±1`; `T(uλ) = 0` always. So `C_ω` and `C_{ω²}` only read
frequencies divisible by `3` (`rotatedCorrelation_eq_three_layer`): the unit layer `2 (4π|ξ₁|)^{−s} S_1(s/2)`
of `D` is invisible to every nontrivial rotation.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi

theorem norm_ringComplex_val_unit (ε : Oˣ) : ‖ringComplex (ε : O)‖ = 1 := by
  have h := ringComplex_norm_sq_eq_absNorm_span (ε : O)
  rw [Ideal.span_singleton_eq_top.mpr ε.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (2 : ℕ) ≠ 0)).mp h

theorem norm_cuspFrequency_unit_mul (ε : Oˣ) (h : O) :
    ‖cuspFrequency ((ε : O) * h)‖ = ‖cuspFrequency h‖ := by
  rw [mul_comm, cuspFrequency_mul_right, norm_mul, norm_ringComplex_val_unit, mul_one]

/-- The rotated correlation series `C_ε(s) = Σ_{h ≠ 0} T(εh) T(h) (4π|ξ_h|)^{−s}`. -/
def rotatedCorrelation (ε : Oˣ) (s : ℂ) : ℂ :=
  ∑' h : O, if h = 0 then 0 else
    rationalSourceResidualFourierCoefficient ((ε : O) * h) * rationalSourceResidualFourierCoefficient h *
      ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)

/-- The layer coefficient `T(εuλ^m) T(uλ^m)/T(1)² · (4π|ξ_{uλ^m}|)^{−s}`. -/
def rotatedLayerCoeff (ε u : Oˣ) (m : ℕ) (s : ℂ) : ℂ :=
  rationalSourceResidualFourierCoefficient (((ε * u : Oˣ) : O) * lambda ^ m) *
      rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) /
        rationalSourceResidualFourierCoefficient 1 ^ 2 *
    ((4 * Real.pi * ‖cuspFrequency ((u : O) * lambda ^ m)‖ : ℝ) : ℂ) ^ (-s)

/-- `(εuλ^m/a)₃ (uλ^m/a)₃ = (ε²uλ^m/a)₃²` at primary `a`. -/
theorem symbol_rotated_pair (ε u : Oˣ) (m : ℕ) (a : O) (ha : lambda ^ 2 ∣ a - 1) :
    symbol (((ε * u : Oˣ) : O) * lambda ^ m) a * symbol ((u : O) * lambda ^ m) a =
      symbol (((ε ^ 2 * u : Oˣ) : O) * lambda ^ m) a ^ 2 := by
  have hε : IsCoprime (ε : O) a := ⟨↑ε⁻¹, 0, by simp⟩
  calc _ = symbol ((((ε * u : Oˣ) : O) * lambda ^ m) * ((u : O) * lambda ^ m)) a :=
        (symbol_mul_numerator _ _ _).symm
    _ = symbol ((((ε * u : Oˣ) : O) * lambda ^ m) * ((u : O) * lambda ^ m) * (ε : O) ^ 3) a :=
        (symbol_mul_cube _ _ a ha hε).symm
    _ = symbol ((((ε ^ 2 * u : Oˣ) : O) * lambda ^ m) * (((ε ^ 2 * u : Oˣ) : O) * lambda ^ m)) a := by
        congr 1
        simp only [Units.val_mul, Units.val_pow_eq_pow_val]
        ring
    _ = _ := by
        rw [symbol_mul_numerator]
        exact (sq _).symm

/-- The terms of `C_ε(s)` are absolutely summable for `Re s > 4` (`2|xy| ≤ |x|² + |y|²`). -/
theorem summable_rotatedCorrelation_term (ε : Oˣ) (s : ℂ) (hs : 4 < s.re) :
    Summable (fun h : O => if h = 0 then (0 : ℂ) else
      rationalSourceResidualFourierCoefficient ((ε : O) * h) * rationalSourceResidualFourierCoefficient h *
        ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) := by
  set a : O → ℝ := fun h => if h = 0 then 0 else
    ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 * ‖cuspFrequency h‖ ^ (-s.re) with ha
  have hA : Summable a := summable_sourceCoefficient_sq_rpow hs
  have hAε : Summable (fun h => a ((ε : O) * h)) := hA.comp_injective (mul_right_injective₀ ε.ne_zero)
  refine Summable.of_norm_bounded ((hAε.add hA).mul_left ((4 * Real.pi) ^ (-s.re) / 2)) (fun h => ?_)
  by_cases hh : h = 0
  · simp [ha, hh]
  have hεh : (ε : O) * h ≠ 0 := mul_ne_zero ε.ne_zero hh
  have hξ : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  simp only [ha, hh, hεh, if_false, norm_mul, norm_cuspFrequency_unit_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re,
    Real.mul_rpow (by positivity) hξ.le]
  have hp : 0 < (4 * Real.pi) ^ (-s.re) := by positivity
  have hq : 0 < ‖cuspFrequency h‖ ^ (-s.re) := by positivity
  nlinarith [mul_nonneg (mul_pos hp hq).le (sq_nonneg (‖rationalSourceResidualFourierCoefficient ((ε : O) * h)‖ -
    ‖rationalSourceResidualFourierCoefficient h‖))]

/-- **The rotated split.** For `Re s > 4`,
`C_ε(s) = Σ_{u, m} (T(εuλ^m) T(uλ^m)/T(1)²) (4π|ξ_{uλ^m}|)^{−s} P_{ε²uλ^m}(s/2)`. -/
theorem rotatedCorrelation_eq_twisted (ε : Oˣ) (s : ℂ) (hs : 4 < s.re) :
    rotatedCorrelation ε s = ∑' u : Oˣ, ∑' m : ℕ,
      rotatedLayerCoeff ε u m s * twistedPrimarySeries (((ε ^ 2 * u : Oˣ) : O) * lambda ^ m) (s / 2) := by
  set F : O → ℂ := fun h => if h = 0 then (0 : ℂ) else
    rationalSourceResidualFourierCoefficient ((ε : O) * h) * rationalSourceResidualFourierCoefficient h *
      ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s) with hF
  set g : O → Ideal O → ℂ := fun h₀ I => unramifiedNormWeight (s / 2) I *
    (ringComplex (symbol h₀ (primaryIdealGenerator I)) ^ 2 *
      rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ^ 2) with hg
  have hT1 : rationalSourceResidualFourierCoefficient 1 ≠ 0 := fun hz =>
    rationalSourceThetaScalar_ne_zero (by rw [rationalSourceThetaScalar, hz, star_zero])
  have hterm : ∀ p : Oˣ × ℕ × GoodIdeal, F (frequencySplit p) =
      rotatedLayerCoeff ε p.1 p.2.1 s * g (((ε ^ 2 * p.1 : Oˣ) : O) * lambda ^ p.2.1) p.2.2.1 := by
    rintro ⟨u, m, I, hI⟩
    have h1 := eq_div_of_mul_eq hT1 (sourceCoefficient_twisted_mul _ (ramified_ne_zero (ε * u) m) I hI
      (ramified_isCoprime_gen (ε * u) m I hI))
    have h2 := eq_div_of_mul_eq hT1 (sourceCoefficient_twisted_mul _ (ramified_ne_zero u m) I hI
      (ramified_isCoprime_gen u m I hI))
    have hsym : ringComplex (symbol (((ε * u : Oˣ) : O) * lambda ^ m) (primaryIdealGenerator I)) *
        ringComplex (symbol ((u : O) * lambda ^ m) (primaryIdealGenerator I)) =
          ringComplex (symbol (((ε ^ 2 * u : Oˣ) : O) * lambda ^ m) (primaryIdealGenerator I)) ^ 2 := by
      rw [← map_mul, ← map_pow, symbol_rotated_pair ε u m _ (primaryIdealGenerator_spec I hI).2]
    have hrot : (ε : O) * ((u : O) * lambda ^ m * primaryIdealGenerator I) =
        ((ε * u : Oˣ) : O) * lambda ^ m * primaryIdealGenerator I := by
      rw [Units.val_mul]
      ring
    simp only [hF, hg, rotatedLayerCoeff, frequencySplit]
    rw [if_neg (mul_ne_zero (ramified_ne_zero u m) hI), hrot, h1, h2, frequencyWeight_split s _ I hI,
      ← hsym]
    ring
  have hFs : Summable F := summable_rotatedCorrelation_term ε s hs
  have hGs : Summable (fun p : Oˣ × ℕ × GoodIdeal => F (frequencySplit p)) :=
    hFs.comp_injective frequencySplit_injective
  have hsupp : Function.support F ⊆ Set.range frequencySplit := by
    intro h hh
    have hh0 : h ≠ 0 := by
      intro hz
      exact hh (by simp only [hF, hz, if_true])
    exact frequencySplit_surjective h hh0
  have hgood : ∀ h₀ : O, ∑' I : GoodIdeal, g h₀ I.1 = twistedPrimarySeries h₀ (s / 2) := by
    intro h₀
    refine tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryIdealGenerator I ≠ 0}) ?_
    intro I hI
    by_contra hb
    exact hI (by simp only [hg]; rw [unramifiedNormWeight_of_bad _ _ (not_not.mp hb), zero_mul])
  calc rotatedCorrelation ε s = ∑' h : O, F h := rfl
    _ = ∑' p : Oˣ × ℕ × GoodIdeal, F (frequencySplit p) := (frequencySplit_injective.tsum_eq hsupp).symm
    _ = ∑' u : Oˣ, ∑' q : ℕ × GoodIdeal, F (frequencySplit (u, q)) := hGs.tsum_prod
    _ = ∑' u : Oˣ, ∑' m : ℕ, ∑' I : GoodIdeal, F (frequencySplit (u, m, I)) :=
        tsum_congr fun u => (hGs.prod_factor u).tsum_prod
    _ = _ := by
        refine tsum_congr fun u => tsum_congr fun m => ?_
        simp only [hterm]
        rw [tsum_mul_left, hgood]

/-- **The cube factor of the rotated correlations.** For `Re s > 4`,
`C_ε(s) = \overline{C}² Z₀(3s/2 − 1) Σ_{u, m} (T(εuλ^m) T(uλ^m)/T(1)²) (4π|ξ_{uλ^m}|)^{−s} S_{ε²uλ^m}(s/2)`. -/
theorem rotatedCorrelation_eq_zeta_mul (ε : Oˣ) (s : ℂ) (hs : 4 < s.re) :
    rotatedCorrelation ε s = star rationalSourceThetaScalar ^ 2 * unramifiedIdealZeta (3 * (s / 2) - 1) *
      ∑' u : Oˣ, ∑' m : ℕ, rotatedLayerCoeff ε u m s *
        twistedSquarefreeSeries (((ε ^ 2 * u : Oˣ) : O) * lambda ^ m) (s / 2) := by
  have hw : 1 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith
  rw [rotatedCorrelation_eq_twisted ε s hs, ← tsum_mul_left]
  refine tsum_congr fun u => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [twistedPrimarySeries_eq _ m _ hw]
  ring

/-- The unit layer is invisible to a nontrivial rotation: `T(εu) T(u) = 0` for `ε ≠ ±1`. -/
theorem rotatedLayerCoeff_zero (ε u : Oˣ) (h1 : (ε : O) ≠ 1) (h2 : (ε : O) ≠ -1) (s : ℂ) :
    rotatedLayerCoeff ε u 0 s = 0 := by
  have hz : rationalSourceResidualFourierCoefficient ((ε * u : Oˣ) : O) *
      rationalSourceResidualFourierCoefficient (u : O) = 0 := by
    by_contra hne
    obtain ⟨hεu, hu⟩ := mul_ne_zero_iff.mp hne
    have hεu' := sourceCoefficient_unit_eq (ε * u) hεu
    rw [Units.val_mul] at hεu'
    rcases sourceCoefficient_unit_eq u hu with hu' | hu' <;> rw [hu'] at hεu' <;>
      rcases hεu' with h | h
    · exact h1 (by simpa using h)
    · exact h2 (by simpa using h)
    · exact h2 (by linear_combination -h)
    · exact h1 (by linear_combination -h)
  simp only [rotatedLayerCoeff, pow_zero, mul_one, hz, zero_div, zero_mul]

/-- No frequency of λ-adic valuation one: `T(εuλ) T(uλ) = 0`. -/
theorem rotatedLayerCoeff_one (ε u : Oˣ) (s : ℂ) : rotatedLayerCoeff ε u 1 s = 0 := by
  simp only [rotatedLayerCoeff, pow_one, sourceCoefficient_unit_mul_lambda u, mul_zero, zero_div, zero_mul]

/-- Dropping two vanishing initial terms of a series over `ℕ`. -/
theorem tsum_shift_two (f : ℕ → ℂ) (h0 : f 0 = 0) (h1 : f 1 = 0) :
    ∑' m, f m = ∑' m, f (m + 2) := by
  refine ((add_left_injective 2).tsum_eq fun m hm => ?_).symm
  have hm2 : 2 ≤ m := by
    by_contra hlt
    interval_cases m
    · exact hm h0
    · exact hm h1
  exact ⟨m - 2, Nat.sub_add_cancel hm2⟩

/-- **Only the three-divisible layer.** For `ε ≠ ±1` and `Re s > 4`,
`C_ε(s) = \overline{C}² Z₀(3s/2 − 1) Σ_u Σ_{m ≥ 2} (T(εuλ^m) T(uλ^m)/T(1)²) (4π|ξ_{uλ^m}|)^{−s} S_{ε²uλ^m}(s/2)`. -/
theorem rotatedCorrelation_eq_three_layer (ε : Oˣ) (h1 : (ε : O) ≠ 1) (h2 : (ε : O) ≠ -1)
    (s : ℂ) (hs : 4 < s.re) :
    rotatedCorrelation ε s = star rationalSourceThetaScalar ^ 2 * unramifiedIdealZeta (3 * (s / 2) - 1) *
      ∑' u : Oˣ, ∑' m : ℕ, rotatedLayerCoeff ε u (m + 2) s *
        twistedSquarefreeSeries (((ε ^ 2 * u : Oˣ) : O) * lambda ^ (m + 2)) (s / 2) := by
  rw [rotatedCorrelation_eq_zeta_mul ε s hs]
  refine congrArg (star rationalSourceThetaScalar ^ 2 * unramifiedIdealZeta (3 * (s / 2) - 1) * ·)
    (tsum_congr fun u => tsum_shift_two (fun m => rotatedLayerCoeff ε u m s *
      twistedSquarefreeSeries (((ε ^ 2 * u : Oˣ) : O) * lambda ^ m) (s / 2)) ?_ ?_)
  · rw [rotatedLayerCoeff_zero ε u h1 h2, zero_mul]
  · rw [rotatedLayerCoeff_one, zero_mul]

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
