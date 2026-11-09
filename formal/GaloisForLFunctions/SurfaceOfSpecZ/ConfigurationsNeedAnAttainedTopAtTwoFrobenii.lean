import GaloisForLFunctions.SurfaceOfSpecZ.ConfigurationsNeedAnAttainedTopAtFinitelyManyFrobenii

/-!
# Zero configurations need an attained top at two Frobenii

The case `r = 2` of `exists_zeroConfig_finPrimes_bddBelow_nonattained`: for all primes `p, q` and
`0 < Θ ≤ ½` there is a tempered configuration without real zeros, with `sup Re ρ = ½ + Θ` not
attained, whose spline traces satisfy `2 Re S(a log p + b log q) ≥ −5` for all `a, b`. The attainment
hypothesis of `onLine_of_bddBelow_twoPrimes_of_max` (`TwoFrobeniiSuffice`) cannot be removed.

For `ζ` the same degrees in count form: if every single-degree class `Γ_1 + Γ_{pᵃqᵇ}` carries an
`ℕ`-count with Tate limit its defect, the asymptotic abscissa law holds
(`asymptoticAbscissaLaw_of_planeDefect_nonneg_twoPrimes`), and RH is these counts together with
`ZerosApproachLine` (`riemannHypothesis_iff_zerosApproachLine_and_effectiveCounts_twoPrimes`). The
lag classes `Γ_m + Γ_n`, `m, n ∈ ⟨p, q⟩`, decide RH alone (`TheEffectiveClassesOfTwoFrobenii`).
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open CountingHolography

/-- **Two Frobenii need an attained top**, for genuine configurations: the attainment hypothesis of
`onLine_of_bddBelow_twoPrimes_of_max` cannot be removed. -/
theorem exists_zeroConfig_twoPrimes_bddBelow_nonattained {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧ (∀ β < 1 / 2 + Θ, ∃ ρ ∈ Z.carrier, β < ρ.re) ∧
      ∀ a b : ℕ, -5 ≤ 2 * (lagStructure Z (boxSpline 1 3) (a * Real.log p + b * Real.log q)).re := by
  obtain ⟨Z, h1, h2, h3, h4, h5⟩ := exists_zeroConfig_finPrimes_bddBelow_nonattained ![p, q]
    (fun i => by fin_cases i <;> simp [hp, hq]) hΘ hΘ2
  refine ⟨Z, h1, h2, h3, h4, fun a b => ?_⟩
  have := h5 ![a, b]
  simpa [Fin.sum_univ_two] using this

/-! ### For `ζ`: counts on the single-degree classes -/

theorem log_pow_mul_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (a b : ℕ) :
    Real.log ((p ^ a * q ^ b : ℕ) : ℝ) = a * Real.log p + b * Real.log q := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  push_cast
  rw [Real.log_mul (pow_pos hp0 a).ne' (pow_pos hq0 b).ne', Real.log_pow, Real.log_pow]

/-- **Copositivity of the single-degree planes of two Frobenii gives the abscissa law.** -/
theorem asymptoticAbscissaLaw_of_planeDefect_nonneg_twoPrimes {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : ∀ a b : ℕ, 0 ≤ planeDefect (p ^ a * q ^ b) (1, 1)) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_bddBelow_twoPrimes hp hq hpq
    (K := 2 * zetaScalingDatum.orbitCorr splineCycle 0) fun a b => ?_
  have := h a b
  rw [planeDefect_one_one, orbitCorr_eq_re_lagStructure_spline,
    orbitCorr_eq_re_lagStructure_spline, log_pow_mul_pow hp hq] at this
  rw [orbitCorr_eq_re_lagStructure_spline]
  linarith

/-- **RH is the approach to the line plus counts on the single-degree classes of two Frobenii.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_effectiveCounts_twoPrimes {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    RiemannHypothesis ↔ _root_.RHTower.BacklundConverse.ZerosApproachLine ∧ ∀ a b : ℕ,
      ∃ K : ℕ → ℕ, Tendsto (fun m : ℕ => (K m : ℝ) / (m : ℝ) ^ 2) atTop
        (𝓝 (planeDefect (p ^ a * q ^ b) (1, 1))) := by
  rw [_root_.RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw]
  constructor
  · rintro ⟨hZ, hA⟩
    have hRH :=
      _root_.RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr ⟨hZ, hA⟩
    refine ⟨hZ, fun a b => ?_⟩
    have hd : 0 < p ^ a * q ^ b := Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
    have h := planeDefect_nonneg_of_RH hRH hd 1 1
    exact ⟨fun m => ⌊(m : ℝ) ^ 2 * planeDefect (p ^ a * q ^ b) (1, 1)⌋₊, tendsto_floor_div_sq h⟩
  · rintro ⟨hZ, h⟩
    refine ⟨hZ, asymptoticAbscissaLaw_of_planeDefect_nonneg_twoPrimes hp hq hpq fun a b => ?_⟩
    obtain ⟨K, hK⟩ := h a b
    exact ge_of_tendsto' hK fun m => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

end GaloisForLFunctions.SurfaceOfSpecZ
