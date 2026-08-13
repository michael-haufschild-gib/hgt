import GaloisForLFunctions.RHTower.Sieve.MaynardOptimizerEndpointAbsorption

/-!
# Moving-endpoint count for one literal selected-cell fibre

Exact optimizer crossing and endpoint absorption combine to put every nonempty color fibre in one
of Maynard's two required count alternatives.  No fixed endpoint deficit or scheduled length
interval remains.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- After charging a second half-reserve to an external multiplier, every moving-endpoint literal
selected-cell fibre satisfies one exact Maynard alternative.  This is the form stable under a
finite-colour sum. -/
theorem eventually_maynardWindowRelevantSelectedCell_scaled_fibre_first_or_second (A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 / 2 ≤ c → 997 / 1000 < alpha →
      alpha ≤ 1 - routeTEndpointGlobalDeficit A T →
      0 < delta →
      ∀ M : ℝ, 0 ≤ M →
      M ≤ T ^ (routeTEndpointGlobalDeficit A T / 400) →
      ∀ (label : HeathBrownSelectionLabel L X 60) (S : Finset ℕ),
      S.Nonempty → S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha label) →
      M * (S.card : ℝ) ≤
          maynardHarmonicFactor K delta *
            T ^ (mu * (1 - alpha) - routeTEndpointGlobalDeficit A T / 200) ∨
        M * (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
            routeTEndpointGlobalDeficit A T / 200) := by
  filter_upwards [eventually_maynardOptimizerFixedLogCost_absorbed A
      (2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
        maynardEnergyEnvelopeConstant)
        (mul_pos
          (mul_pos (by positivity)
            (lt_of_lt_of_le zero_lt_one maynardRaisedWidthConstant_one_le))
          maynardEnergyEnvelopeConstant_pos)
        0 400 (by norm_num),
    eventually_gt_atTop (1 : ℝ)] with T hcost hT
  intro L X K mu N0 c alpha delta hmuLo hmuHi hc halphaLo halphaEndpoint
    hdelta M hM0 hM label S hSne hS lam hgap hdiam hselection
  let d := routeTEndpointGlobalDeficit A T
  let alpha0 := alpha - (1 - alpha) / 100
  have hd : 0 < d := routeTEndpointGlobalDeficit_pos A (by linarith)
  have hdGap : d ≤ 1 - alpha := by dsimp only [d] at halphaEndpoint ⊢; linarith
  have halphaHi : alpha < 1 := by linarith
  have halpha0Lo : 99 / 100 ≤ alpha0 := by dsimp only [alpha0]; linarith
  have halpha0Hi : alpha0 < 1 := by dsimp only [alpha0]; linarith
  have hcost' : ∀ N e : ℕ, 1 ≤ N → (N : ℝ) ≤ T →
      e ≤ maynardFixedPolylogExponentBound →
      2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
          (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e *
          maynardEnergyEnvelopeConstant ≤
        T ^ ((1 - alpha) / 100) := by
    intro N e hN hNT he
    have hraw := hcost N e hN hNT he
    have hraw' :
        2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
            (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e *
            maynardEnergyEnvelopeConstant ≤ T ^ (d / 400) := by
      calc
        2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
              (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e *
              maynardEnergyEnvelopeConstant =
            (2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
              maynardEnergyEnvelopeConstant) *
              (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e := by ring
        _ ≤ T ^ (d / 400) := by
          norm_num [d] at hraw ⊢
          exact hraw
    have hpow := Real.rpow_le_rpow_of_exponent_le hT.le
      (show d / 400 ≤ (1 - alpha) / 100 by nlinarith)
    exact hraw'.trans hpow
  obtain ⟨ell, hell, hell51, hcross, hover, _hexponent, hHuxley⟩ :=
    exists_maynardWindowRelevantSelectedCell_fibre_optimizer_huxley
      L X K hT (by linarith) halphaLo (by linarith) halpha0Lo halpha0Hi
      (by rfl) hmuLo label S hSne hS lam hdelta hgap hdiam hselection hcost'
  let beta := maynardSubHeightSelectedExponent T label
  let r : ℝ := (ell : ℝ) * beta
  obtain ⟨r0, hr0⟩ := hSne
  rcases hselection r0 hr0 with
    ⟨_helig, _hrel, _hcore, _hune, _husub, _hbetaT, _hbetaHi,
      hlength, _hlarge, hbranch⟩
  have hsmall : beta ≤ 5 / 12 := by
    rcases hbranch with hsmall | hmoderate | hoverweight
    · simpa [IsMaynardSelectedCellBranch, beta] using hsmall
    · have := hmoderate.2.2.1
      linarith
    · have := hoverweight.2.1
      linarith
  let Y : ℝ :=
    (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)
  have hYeq : Y = T ^ r := by
    have hAeq : (groupedDyadicLower (heathBrownSelectedExponent label) : ℝ) =
        T ^ beta := by simpa [beta] using hlength
    dsimp only [Y, r]
    rw [Nat.cast_pow, hAeq, ← Real.rpow_natCast,
      ← Real.rpow_mul (by linarith : 0 ≤ T)]
    congr 1
    ring
  have hraw := card_le_of_selected_huxley_with_fixed_polylog_raw
    hc (by linarith : alpha ≤ 1) hdelta label S ell hell hell51 hHuxley
  let e : ℕ := 2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
    (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)
  let PL : ℝ := (1 + Real.log (maynardRaisedWidthConstant * Y)) ^ e
  let C : ℝ := 2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant
  have hY1 : 1 ≤ Y := by
    dsimp only [Y]
    exact_mod_cast Nat.one_le_pow ell _ (one_le_groupedDyadicLower _)
  have hPL0 : 0 ≤ PL := by
    dsimp only [PL]
    have hbase : 0 ≤ 1 + Real.log (maynardRaisedWidthConstant * Y) := by
      have hprod : 1 ≤ maynardRaisedWidthConstant * Y :=
        one_le_mul_of_one_le_of_one_le maynardRaisedWidthConstant_one_le hY1
      linarith [Real.log_nonneg hprod]
    exact pow_nonneg hbase e
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg _))
      (le_trans (by norm_num) maynardRaisedWidthConstant_one_le)
  have hEnv1 : 1 ≤ maynardEnergyEnvelopeConstant := by
    dsimp only [maynardEnergyEnvelopeConstant]
    have := maynardRaisedWidthConstant_one_le
    nlinarith
  have heBound : e ≤ maynardFixedPolylogExponentBound := by
    dsimp only [e]
    exact heathBrownSelected_fixedPolylogExponent_le label hell51
  have hYhi : Y ≤ T := by
    have htheta : maynardHuxleyOptimizer alpha0 ≤ 25 / 49 := by
      dsimp only [maynardHuxleyOptimizer]
      rw [div_le_iff₀ (by linarith : 0 < 4 * alpha0 - 2)]
      nlinarith
    have hrOne : r ≤ 1 := by
      have hover' : r < maynardHuxleyOptimizer alpha0 + beta := by
        simpa [r, beta] using hover
      have hfixed : (25 / 49 : ℝ) + 5 / 12 < 1 := by norm_num
      linarith
    rw [hYeq]
    have := Real.rpow_le_rpow_of_exponent_le hT.le hrOne
    simpa using this
  let N : ℕ := (groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact Nat.one_le_pow ell _ (one_le_groupedDyadicLower _)
  have hcostFullRaw := hcost N e hN (by simpa [N, Y] using hYhi) heBound
  have hcostFull : C * PL * maynardEnergyEnvelopeConstant ≤ T ^ (d / 400) := by
    convert hcostFullRaw using 1 <;> simp only [C, PL, N, Y, e, d] <;> ring
  have hcostSmall : C * PL ≤ T ^ (d / 400) := by
    have hleft : C * PL ≤ C * PL * maynardEnergyEnvelopeConstant := by
      calc
        C * PL = C * PL * 1 := by ring
        _ ≤ C * PL * maynardEnergyEnvelopeConstant :=
          mul_le_mul_of_nonneg_left hEnv1 (mul_nonneg hC0 hPL0)
    exact hleft.trans hcostFull
  have hp : 0 ≤ 2 - 2 * alpha := by linarith
  have hYpow : Y ^ (2 - 2 * alpha) = T ^ (r * (2 - 2 * alpha)) := by
    rw [hYeq, ← Real.rpow_mul (by linarith : 0 ≤ T)]
  have hHF0 : 0 ≤ maynardHarmonicFactor K delta :=
    (maynardHarmonicFactor_pos K hdelta).le
  have hcountBase : (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
      T ^ (2 * r * (1 - alpha) + d / 400) := by
    have hraw' : (S.card : ℝ) ≤ C *
        maynardHarmonicFactor K delta * PL * Y ^ (2 - 2 * alpha) := by
      simpa [C, PL, e, Y] using hraw
    calc
      (S.card : ℝ) ≤ C * maynardHarmonicFactor K delta * PL *
          Y ^ (2 - 2 * alpha) := hraw'
      _ = maynardHarmonicFactor K delta * (C * PL) *
          Y ^ (2 - 2 * alpha) := by ring
      _ = maynardHarmonicFactor K delta * (C * PL) *
          T ^ (r * (2 - 2 * alpha)) := by rw [hYpow]
      _ ≤ maynardHarmonicFactor K delta * T ^ (d / 400) *
          T ^ (r * (2 - 2 * alpha)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcostSmall hHF0)
          (Real.rpow_nonneg (by linarith) _)
      _ = maynardHarmonicFactor K delta *
          (T ^ (d / 400) * T ^ (r * (2 - 2 * alpha))) := by ring
      _ = maynardHarmonicFactor K delta *
          T ^ (d / 400 + r * (2 - 2 * alpha)) := by
        rw [← Real.rpow_add (by linarith : 0 < T)]
      _ = maynardHarmonicFactor K delta *
          T ^ (2 * r * (1 - alpha) + d / 400) := by
        congr 2
        ring
  have hcount : M * (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
      T ^ (2 * r * (1 - alpha) + d / 200) := by
    calc
      M * (S.card : ℝ) ≤ M * (maynardHarmonicFactor K delta *
          T ^ (2 * r * (1 - alpha) + d / 400)) :=
        mul_le_mul_of_nonneg_left hcountBase hM0
      _ ≤ T ^ (d / 400) * (maynardHarmonicFactor K delta *
          T ^ (2 * r * (1 - alpha) + d / 400)) :=
        mul_le_mul_of_nonneg_right hM
          (mul_nonneg hHF0 (Real.rpow_nonneg (by linarith) _))
      _ = maynardHarmonicFactor K delta *
          (T ^ (d / 400) * T ^ (2 * r * (1 - alpha) + d / 400)) := by ring
      _ = maynardHarmonicFactor K delta *
          T ^ (2 * r * (1 - alpha) + d / 200) := by
        rw [← Real.rpow_add (by linarith : 0 < T)]
        congr 2
        ring
  rcases routeT_exact_crossing_first_or_second hmuLo hmuHi
    halphaLo.le halphaHi (by rfl) hsmall
    (by simpa [r, beta] using hover) hd.le hdGap with hfirst | hsecond
  · left
    have hfirstStrong : 2 * r * (1 - alpha) + d / 200 ≤
        mu * (1 - alpha) - d / 200 := by linarith
    exact hcount.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT.le hfirstStrong) hHF0)
  · right
    have hsecondStrong : 2 * r * (1 - alpha) + d / 200 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 200 := by linarith
    exact hcount.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT.le hsecondStrong) hHF0)

/-- Unscaled one-fibre consequence of the finite-sum-stable theorem. -/
theorem eventually_maynardWindowRelevantSelectedCell_fibre_first_or_second (A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 / 2 ≤ c → 997 / 1000 < alpha →
      alpha ≤ 1 - routeTEndpointGlobalDeficit A T →
      0 < delta →
      ∀ (label : HeathBrownSelectionLabel L X 60) (S : Finset ℕ),
      S.Nonempty → S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha label) →
      (S.card : ℝ) ≤
          maynardHarmonicFactor K delta * T ^ (mu * (1 - alpha)) ∨
        (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha)) := by
  filter_upwards [eventually_maynardWindowRelevantSelectedCell_scaled_fibre_first_or_second A,
    eventually_gt_atTop (1 : ℝ)] with T hscaled hT
  intro L X K mu N0 c alpha delta hmuLo hmuHi hc halphaLo halphaEndpoint
    hdelta label S hSne hS lam hgap hdiam hselection
  have hd : 0 ≤ routeTEndpointGlobalDeficit A T :=
    (routeTEndpointGlobalDeficit_pos A (by linarith)).le
  have hM : (1 : ℝ) ≤ T ^ (routeTEndpointGlobalDeficit A T / 400) :=
    Real.one_le_rpow hT.le (div_nonneg hd (by norm_num))
  have hHF0 : 0 ≤ maynardHarmonicFactor K delta :=
    (maynardHarmonicFactor_pos K hdelta).le
  rcases hscaled hmuLo hmuHi hc halphaLo halphaEndpoint hdelta
    1 (by norm_num) hM label S hSne hS lam hgap hdiam hselection with hfirst | hsecond
  · left
    have hexponent : mu * (1 - alpha) - routeTEndpointGlobalDeficit A T / 200 ≤
        mu * (1 - alpha) := by linarith
    simpa using hfirst.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT.le hexponent) hHF0)
  · right
    have hexponent :
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
            routeTEndpointGlobalDeficit A T / 200 ≤
          1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by linarith
    simpa using hsecond.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT.le hexponent) hHF0)

end RHTower.Sieve
