import GaloisForLFunctions.SurfaceOfSpecZ.TheWidthIsTheStepanovExponentAtThePrimes
import GaloisForLFunctions.SquareRootThreshold.NegativityRateEqualsMaximalDepth

/-!
# Weil positivity at the prime two-bumps

Weil's criterion asks `W(f, f) ≥ 0` for every test `f`. With `B` the cubic spline, the even two-bump
test at separation `v` is `f_v = B + τ_v B` (`twoBump B v 1`), and
`Re W(f_v, f_v) = 2 Re S(0) + 2 Re S(v)` (`re_W_primeTwoBump_eq`), the defect `δ(Γ_1 + Γ_{e^v})` of
the effective class of a plane. By `TheStepanovCountAtThePrimeDegrees` and
`TheWidthIsTheStepanovExponentAtThePrimes` one countable family of tests suffices, one per prime:

* `riemannHypothesis_iff_weil_primeTwoBumps`: RH iff `Re W(f_{log p}, f_{log p}) ≥ 0` for every prime;
* `riemannHypothesis_iff_weil_primeTwoBumps_bddBelow`: RH iff these values are bounded below;
* `zetaZeroWidth_le_iff_weil_primeTwoBumps`: for `0 ≤ a < ½`, the width is `≤ a` iff
  `Re W(f_{log p}, f_{log p}) ≥ −K p^a` for every prime.

Every `f_{log p}` is a sum of two translates of one fixed spline; the separations are the logarithms
of the primes.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **The prime two-bump identity.** `Re W(B + τ_v B, B + τ_v B) = 2 Re S(0) + 2 Re S(v)`. -/
theorem re_W_primeTwoBump_eq (v : ℝ) :
    (zetaZeroConfig.W (twoBump (boxSpline 1 3) v 1) (twoBump (boxSpline 1 3) v 1)).re =
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) 0).re +
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) v).re := by
  have hb := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hZ := SquareRootThreshold.temperedConfig_zetaZeroConfig
  rw [re_W_unit_twoBump zetaZeroConfig hZ hb hbs v (by simp),
    conj_lagStructure_neg zetaZeroConfig hZ hb hbs v, one_mul,
    show lagStructure zetaZeroConfig (boxSpline 1 3) v + lagStructure zetaZeroConfig (boxSpline 1 3) v =
      2 * lagStructure zetaZeroConfig (boxSpline 1 3) v by ring]
  simp

/-- **Weil positivity at the prime two-bumps is RH.** -/
theorem riemannHypothesis_iff_weil_primeTwoBumps :
    RiemannHypothesis ↔ ∀ p : ℕ, p.Prime →
      0 ≤ (zetaZeroConfig.W (twoBump (boxSpline 1 3) (Real.log p) 1)
        (twoBump (boxSpline 1 3) (Real.log p) 1)).re := by
  constructor
  · intro hRH p hp
    have h := (riemannHypothesis_iff_hasseWeil_integerDegrees.mp hRH) p hp.pos
    rw [ScalingDatum.HasseWeilAt, orbitCorr_eq_re_lagStructure_spline,
      orbitCorr_eq_re_lagStructure_spline] at h
    rw [re_W_primeTwoBump_eq]; linarith [(abs_le.mp h).1]
  · intro h
    rw [riemannHypothesis_iff_bddBelow_primeDegrees]
    refine ⟨2 * (lagStructure zetaZeroConfig (boxSpline 1 3) 0).re, fun p hp => ?_⟩
    have := h p hp
    rw [re_W_primeTwoBump_eq] at this
    linarith

/-- **A lower bound at the prime two-bumps is RH.** -/
theorem riemannHypothesis_iff_weil_primeTwoBumps_bddBelow :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime →
      -K ≤ (zetaZeroConfig.W (twoBump (boxSpline 1 3) (Real.log p) 1)
        (twoBump (boxSpline 1 3) (Real.log p) 1)).re := by
  constructor
  · intro hRH
    exact ⟨0, fun p hp => by
      rw [neg_zero]; exact riemannHypothesis_iff_weil_primeTwoBumps.mp hRH p hp⟩
  · rintro ⟨K, hK⟩
    rw [riemannHypothesis_iff_bddBelow_primeDegrees]
    refine ⟨K + 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) 0).re, fun p hp => ?_⟩
    have := hK p hp
    rw [re_W_primeTwoBump_eq] at this
    linarith

/-- **The width is the growth exponent of the negative part at the prime two-bumps.** -/
theorem zetaZeroWidth_le_iff_weil_primeTwoBumps {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    zetaZeroWidth ≤ a ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime →
      -(K * (p : ℝ) ^ a) ≤ (zetaZeroConfig.W (twoBump (boxSpline 1 3) (Real.log p) 1)
        (twoBump (boxSpline 1 3) (Real.log p) 1)).re := by
  rw [zetaZeroWidth_le_iff_bddBelow_primeDegrees ha0 ha]
  set c0 := 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) 0).re with hc0
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K + |c0|, fun p hp => ?_⟩
    have h1 := hK p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ a :=
      Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) ha0
    have h2 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg c0)
    rw [re_W_primeTwoBump_eq, ← hc0]
    nlinarith [neg_abs_le c0]
  · rintro ⟨K, hK⟩
    refine ⟨K + |c0|, fun p hp => ?_⟩
    have h1 := hK p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ a :=
      Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) ha0
    have h2 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg c0)
    rw [re_W_primeTwoBump_eq, ← hc0] at h1
    nlinarith [le_abs_self c0]

end GaloisForLFunctions.SurfaceOfSpecZ
