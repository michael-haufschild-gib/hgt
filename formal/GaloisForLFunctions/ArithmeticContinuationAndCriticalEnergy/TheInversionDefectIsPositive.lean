import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheSelfImprovingEnergyIdentity
import GaloisForLFunctions.RHTower.BoseMellinCoordinate

/-!
# The inversion defect is positive, and only the positive part of the source feeds it

The self-improving identity pairs the source with the defect `ρ_ε(n) = n − m₀(ε) Φ_ε(n)` of the
inversion law.  That defect is *nonnegative*, and the reason is elementary: the density is the
reciprocal of the real zeta series at `1 + ε`, the floor is at most the quotient, and the partial
sum of the series is at most the series, so

`m₀(ε) Φ_ε(n) ≤ n · m₀(ε) Σ_{j ≤ n} j^{-(1+ε)} ≤ n`  (`inversionDefect_nonneg`),

with `ρ_ε(n) ≤ n` on the other side (`inversionDefect_le_self`).  Hence the explicit term of the
identity is a pairing against a **positive** weight, and only the positive excursions of the centred
source can inflate it:

`E_T(ε) ≤ ⟪A_ε⁺, ρ_ε⟫_T − ⟪A_ε, D^{ζ_ε,≥2} A_ε⟫_T`  (`dampedMobiusEnergy_le_posPart_pairing_sub`).

So the criterion of the self-improving identity becomes one-sided: a sublinear bound on the
*positive part* of the source against an explicit positive weight, plus a lower bound on the
off-diagonal anti-correlation, already gives admission
(`admits_of_onesided_sublinear_pairings`) and, cofinally, the Riemann hypothesis
(`riemannHypothesis_of_cofinal_onesided_pairings`).  This is a criterion that reads the signs of the
source, which the corpus's own rule for the regime below half damping demands.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The density is the reciprocal of the real zeta series -/

theorem pmPowerDampedDivisorDensity_re_eq {ε : ℝ} (hε : 0 < ε) :
    (pmPowerDampedDivisorDensity ε).re = 1 / realZetaSeries (1 + ε) := by
  have hcast : ((1 + ε : ℝ) : ℂ) = 1 + (ε : ℂ) := by push_cast; ring
  have h := ofReal_realZetaSeries (s := 1 + ε) (by linarith : (1 : ℝ) < 1 + ε)
  rw [hcast] at h
  rw [pmPowerDampedDivisorDensity, ← h, ← Complex.ofReal_one, ← Complex.ofReal_div,
    Complex.ofReal_re]

theorem pmPowerDampedDivisorDensity_re_pos {ε : ℝ} (hε : 0 < ε) :
    0 < (pmPowerDampedDivisorDensity ε).re := by
  rw [pmPowerDampedDivisorDensity_re_eq hε]
  exact one_div_pos.mpr (realZetaSeries_pos (by linarith))

/-- The partial sums of the real zeta series are at most the series. -/
theorem sum_Icc_rpow_le_realZetaSeries {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (∑ j ∈ Icc 1 n, (j : ℝ) ^ (-(1 + ε))) ≤ realZetaSeries (1 + ε) := by
  have hsum := summable_realZetaTerm (s := 1 + ε) (by linarith)
  have hreindex : (∑ j ∈ Icc 1 n, (j : ℝ) ^ (-(1 + ε))) =
      ∑ i ∈ range n, ((i : ℝ) + 1) ^ (-(1 + ε)) := by
    have hIcc : (Icc 1 n : Finset ℕ) = Ico 1 (n + 1) := by
      ext j
      rw [mem_Icc, mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by simp) fun i _ => ?_
    push_cast
    ring_nf
  rw [hreindex, realZetaSeries]
  exact hsum.sum_le_tsum _ (fun i _ => by positivity)

/-! ## §2. The defect is nonnegative -/

/-- The damped unit floor sum is at most the horizon times the partial zeta sum. -/
theorem dampedUnitFloorSum_le {ε : ℝ} (_hε : 0 < ε) (n : ℕ) :
    dampedUnitFloorSum ε n ≤ (n : ℝ) * ∑ j ∈ Icc 1 n, (j : ℝ) ^ (-(1 + ε)) := by
  rw [dampedUnitFloorSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hfloor : (((n / j : ℕ) : ℝ)) ≤ (n : ℝ) / (j : ℝ) := Nat.cast_div_le
  have hpow : (0 : ℝ) < (j : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hj0 _
  have hsplit : (j : ℝ) ^ (-(1 + ε)) = (j : ℝ) ^ (-ε) * ((j : ℝ) ^ (-1 : ℝ)) := by
    rw [← Real.rpow_add hj0]
    congr 1
    ring
  calc (j : ℝ) ^ (-ε) * ((n / j : ℕ) : ℝ) ≤ (j : ℝ) ^ (-ε) * ((n : ℝ) / (j : ℝ)) :=
        mul_le_mul_of_nonneg_left hfloor hpow.le
    _ = (n : ℝ) * ((j : ℝ) ^ (-ε) * ((j : ℝ) ^ (-1 : ℝ))) := by
        rw [Real.rpow_neg_one]
        field_simp
    _ = (n : ℝ) * (j : ℝ) ^ (-(1 + ε)) := by rw [hsplit]

/-- **The inversion defect is nonnegative.** -/
theorem inversionDefect_nonneg {ε : ℝ} (hε : 0 < ε) (n : ℕ) : 0 ≤ inversionDefect ε n := by
  have hm0 := pmPowerDampedDivisorDensity_re_pos hε
  have hfloor := dampedUnitFloorSum_le hε n
  have hpart := sum_Icc_rpow_le_realZetaSeries hε n
  have hZ : 0 < realZetaSeries (1 + ε) := realZetaSeries_pos (by linarith)
  have hmul : (pmPowerDampedDivisorDensity ε).re * dampedUnitFloorSum ε n ≤ (n : ℝ) := by
    have h1 : (pmPowerDampedDivisorDensity ε).re * dampedUnitFloorSum ε n ≤
        (pmPowerDampedDivisorDensity ε).re * ((n : ℝ) * ∑ j ∈ Icc 1 n, (j : ℝ) ^ (-(1 + ε))) :=
      mul_le_mul_of_nonneg_left hfloor hm0.le
    have h2 : (pmPowerDampedDivisorDensity ε).re *
        ((n : ℝ) * ∑ j ∈ Icc 1 n, (j : ℝ) ^ (-(1 + ε))) ≤ (n : ℝ) := by
      rw [pmPowerDampedDivisorDensity_re_eq hε]
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hZ]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [mul_le_mul_of_nonneg_left hpart hn0]
    linarith
  rw [inversionDefect]
  linarith

/-- The defect never exceeds the horizon. -/
theorem inversionDefect_le_self {ε : ℝ} (hε : 0 < ε) (n : ℕ) : inversionDefect ε n ≤ (n : ℝ) := by
  have hm0 := pmPowerDampedDivisorDensity_re_pos hε
  have hΦ : 0 ≤ dampedUnitFloorSum ε n := by
    rw [dampedUnitFloorSum]
    exact Finset.sum_nonneg fun j _ => by positivity
  rw [inversionDefect]
  nlinarith

/-! ## §3. Only the positive part of the source feeds the explicit term -/

/-- **The one-sided energy bound.**  The explicit term pairs the source against a positive weight,
so its negative excursions can only help. -/
theorem dampedMobiusEnergy_le_posPart_pairing_sub {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    dampedMobiusEnergy ε T ≤
      pronicPairing T (fun n => max (pmPowerDampedCenteredDivisorPrefix ε n) 0)
          (inversionDefect ε) -
        pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (offDiagonalUnitDilation ε) := by
  have hle : pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (inversionDefect ε) ≤
      pronicPairing T (fun n => max (pmPowerDampedCenteredDivisorPrefix ε n) 0)
        (inversionDefect ε) := by
    unfold pronicPairing
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by
      have : (0 : ℝ) < n := by exact_mod_cast hn1
      positivity
    have hρ := inversionDefect_nonneg hε n
    have hmax : pmPowerDampedCenteredDivisorPrefix ε n ≤
        max (pmPowerDampedCenteredDivisorPrefix ε n) 0 := le_max_left _ _
    apply div_le_div_of_nonneg_right _ hn0.le
    exact mul_le_mul_of_nonneg_right hmax hρ
  have hid := dampedMobiusEnergy_eq_pairing_sub ε T
  linarith

/-- **The one-sided criterion for admission.**  A sublinear bound on the positive part of the source
against the explicit positive weight, with a lower bound on the off-diagonal anti-correlation,
gives admission at that damping. -/
theorem admits_of_onesided_sublinear_pairings {ε κ κ' : ℝ} (hε : 0 < ε) (hκ : 0 ≤ κ)
    (hκ' : 0 ≤ κ')
    (h1 : ∀ T : ℕ, pronicPairing T (fun n => max (pmPowerDampedCenteredDivisorPrefix ε n) 0)
      (inversionDefect ε) ≤ κ * Real.sqrt (dampedMobiusEnergy ε T) + κ')
    (h2 : ∀ T : ℕ,
      -(pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (offDiagonalUnitDilation ε)) ≤
        κ * Real.sqrt (dampedMobiusEnergy ε T) + κ') :
    Admits dampedMobiusEnergy ε := by
  refine admits_of_sublinear_pairings hκ hκ' (fun T => ?_) h2
  have hle : pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (inversionDefect ε) ≤
      pronicPairing T (fun n => max (pmPowerDampedCenteredDivisorPrefix ε n) 0)
        (inversionDefect ε) := by
    have h := dampedMobiusEnergy_le_posPart_pairing_sub hε T
    have hid := dampedMobiusEnergy_eq_pairing_sub ε T
    linarith
  exact hle.trans (h1 T)

/-- **The one-sided criterion for the Riemann hypothesis.** -/
theorem riemannHypothesis_of_cofinal_onesided_pairings
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε κ κ' : ℝ, 0 < ε ∧ ε < δ ∧ 0 ≤ κ ∧ 0 ≤ κ' ∧
      (∀ T : ℕ, pronicPairing T (fun n => max (pmPowerDampedCenteredDivisorPrefix ε n) 0)
          (inversionDefect ε) ≤ κ * Real.sqrt (dampedMobiusEnergy ε T) + κ') ∧
        (∀ T : ℕ,
          -(pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε)
            (offDiagonalUnitDilation ε)) ≤
            κ * Real.sqrt (dampedMobiusEnergy ε T) + κ')) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_cofinallyAdmits.mpr fun δ hδ => ?_
  obtain ⟨ε, κ, κ', hε0, hεδ, hκ, hκ', h1, h2⟩ := h δ hδ
  exact ⟨ε, hε0, hεδ, admits_of_onesided_sublinear_pairings hε0 hκ hκ' h1 h2⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
