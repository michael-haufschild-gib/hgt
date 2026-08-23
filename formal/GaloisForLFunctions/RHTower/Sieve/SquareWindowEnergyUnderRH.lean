import GaloisForLFunctions.RHTower.Sieve.DyadicWindowErrorUnderRH
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSquareCorrelationEnergy

/-!
# `RH ⟹` the square-aperture correlation energy is subpower

Reading the dyadic mass at the aperture `X = m²/2` turns the RH error bound into
`|W(m²) − c m| ≪ m^{2a}` for every `a > 0`, and the exact finite identity
`C_M = ∑_{m ≤ M}(W(m²) − c m)²` then gives `C_M ≪ M^{1+4a}`.  With the forward implication
already Lean-closed this completes the equivalence.
-/

namespace RHTower.Sieve

open Filter ArithmeticFunction

noncomputable section

/-- At the aperture `X = m²/2` the dyadic mass is exactly the square-window prime sum. -/
theorem dyadicSqrtVonMangoldtMass_square_eq (m : ℕ) :
    dyadicSqrtVonMangoldtMass (((m ^ 2 : ℕ) : ℝ) / 2) = dyadicWeightedPrimeWindow (m ^ 2) := by
  have hfl : ⌊((m ^ 2 : ℕ) : ℝ) / 2⌋₊ = m ^ 2 / 2 :=
    Nat.floor_div_eq_div (K := ℝ) (m ^ 2) 2
  have hfl2 : ⌊2 * (((m ^ 2 : ℕ) : ℝ) / 2)⌋₊ = m ^ 2 := by
    rw [show 2 * (((m ^ 2 : ℕ) : ℝ) / 2) = ((m ^ 2 : ℕ) : ℝ) by ring, Nat.floor_natCast]
  rw [dyadicSqrtVonMangoldtMass, dyadicWeightedPrimeWindow, hfl, hfl2]

/-- The centring constant at the aperture `m²/2`. -/
theorem sqrt_square_half_centring (m : ℕ) :
    2 * (Real.sqrt 2 - 1) * Real.sqrt (((m ^ 2 : ℕ) : ℝ) / 2)
      = 2 * (1 - (Real.sqrt 2)⁻¹) * (m : ℝ) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hcast : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  rw [hcast, Real.sqrt_div (by positivity) 2, Real.sqrt_sq (Nat.cast_nonneg m)]
  field_simp

/-- **The centred square-window deviation is subpower, under RH.** -/
theorem exists_squarePrimeWindowCenteredDeviation_bound (hRH : RiemannHypothesis) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |squarePrimeWindowCenteredDeviation m| ≤ C * (m : ℝ) ^ (2 * a) := by
  obtain ⟨C, hC0, hC⟩ := exists_dyadicSqrtVonMangoldtMass_error_bound hRH ha ha1
  refine ⟨C + 2, by positivity, ?_⟩
  intro m hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hpowpos : (0 : ℝ) < (m : ℝ) ^ (2 * a) := Real.rpow_pos_of_pos hm0 _
  have hpow1 : (1 : ℝ) ≤ (m : ℝ) ^ (2 * a) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hm1 (show (0:ℝ) ≤ 2 * a by linarith)
  have hs2 : (1 : ℝ) < Real.sqrt 2 := by
    have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using h
  rcases eq_or_lt_of_le hm with h1 | h2
  · -- the single aperture `m = 1`
    have hmeq : m = 1 := h1.symm
    subst hmeq
    have hW1 : dyadicWeightedPrimeWindow (1 ^ 2) = 0 := by
      rw [dyadicWeightedPrimeWindow]
      norm_num
    have hinv : (0 : ℝ) < (Real.sqrt 2)⁻¹ := by positivity
    have hinv1 : (Real.sqrt 2)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      exact Or.inr hs2
    have hval : squarePrimeWindowCenteredDeviation 1
        = -(2 * (1 - (Real.sqrt 2)⁻¹)) := by
      rw [squarePrimeWindowCenteredDeviation, hW1]
      norm_num
    rw [hval, abs_neg, abs_of_nonneg (by nlinarith [hinv1])]
    simp only [Nat.cast_one, Real.one_rpow]
    nlinarith [hinv, hC0]
  · -- the apertures `m ≥ 2`
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2
    have hcast : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
    have hX1 : (1 : ℝ) ≤ ((m ^ 2 : ℕ) : ℝ) / 2 := by
      rw [hcast]; nlinarith [hm2]
    have hb := hC (((m ^ 2 : ℕ) : ℝ) / 2) hX1
    rw [dyadicSqrtVonMangoldtMass_square_eq, sqrt_square_half_centring] at hb
    have hXa : (((m ^ 2 : ℕ) : ℝ) / 2) ^ a ≤ (m : ℝ) ^ (2 * a) := by
      have hmid : (((m ^ 2 : ℕ) : ℝ) / 2) ^ a ≤ (((m : ℝ) ^ 2)) ^ a := by
        refine Real.rpow_le_rpow (by positivity) ?_ ha.le
        rw [hcast]; nlinarith [hm0]
      refine hmid.trans (le_of_eq ?_)
      rw [← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_mul hm0.le]
      congr 1
    have hdev : |squarePrimeWindowCenteredDeviation m| ≤ C * (m : ℝ) ^ (2 * a) := by
      rw [squarePrimeWindowCenteredDeviation]
      exact hb.trans (mul_le_mul_of_nonneg_left hXa hC0.le)
    nlinarith [hdev, hpowpos]

/-- **`RH ⟹` the square-aperture correlation energy is subpower.** -/
theorem squarePrimeWindowCorrelationEnergySubpower_of_riemannHypothesis
    (hRH : RiemannHypothesis) : SquarePrimeWindowCorrelationEnergySubpower := by
  intro δ hδ
  have ha : (0 : ℝ) < min δ 1 / 4 := by
    have : (0 : ℝ) < min δ 1 := lt_min hδ (by norm_num)
    linarith
  have ha1 : min δ 1 / 4 ≤ 1 := by
    have : min δ 1 ≤ 1 := min_le_right _ _
    linarith
  obtain ⟨C, hC0, hC⟩ := exists_squarePrimeWindowCenteredDeviation_bound hRH ha ha1
  refine Asymptotics.IsBigO.of_bound (C ^ 2) ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hexp : (0 : ℝ) < 4 * (min δ 1 / 4) := by linarith
  have hMpow : (0 : ℝ) < (M : ℝ) ^ (4 * (min δ 1 / 4)) := Real.rpow_pos_of_pos hM0 _
  -- each term is bounded by the top of the range
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      (squarePrimeWindowCenteredDeviation m) ^ 2
        ≤ C ^ 2 * (M : ℝ) ^ (4 * (min δ 1 / 4)) := by
    intro m hmem
    rw [Finset.mem_Icc] at hmem
    have hb := hC m hmem.1
    have habs : (squarePrimeWindowCenteredDeviation m) ^ 2
        = |squarePrimeWindowCenteredDeviation m| ^ 2 := (sq_abs _).symm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmem.1
    have hmM : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmem.2
    have hpow0 : (0 : ℝ) ≤ (m : ℝ) ^ (2 * (min δ 1 / 4)) :=
      Real.rpow_nonneg (by linarith) _
    have hsq : |squarePrimeWindowCenteredDeviation m| ^ 2
        ≤ (C * (m : ℝ) ^ (2 * (min δ 1 / 4))) ^ 2 := by
      have h0 : (0 : ℝ) ≤ |squarePrimeWindowCenteredDeviation m| := abs_nonneg _
      nlinarith [hb, h0]
    have hid : (C * (m : ℝ) ^ (2 * (min δ 1 / 4))) ^ 2
        = C ^ 2 * (m : ℝ) ^ (4 * (min δ 1 / 4)) := by
      rw [mul_pow, ← Real.rpow_natCast ((m : ℝ) ^ (2 * (min δ 1 / 4))) 2,
        ← Real.rpow_mul (by linarith : (0:ℝ) ≤ (m:ℝ)),
        show (2 * (min δ 1 / 4)) * ((2 : ℕ) : ℝ) = 4 * (min δ 1 / 4) by push_cast; ring]
    have hmono : (m : ℝ) ^ (4 * (min δ 1 / 4)) ≤ (M : ℝ) ^ (4 * (min δ 1 / 4)) :=
      Real.rpow_le_rpow (by linarith) hmM (by linarith)
    rw [habs]
    refine hsq.trans ?_
    rw [hid]
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  have hsum := Finset.sum_le_card_nsmul (Finset.Icc 1 M)
    (fun m => (squarePrimeWindowCenteredDeviation m) ^ 2)
    (C ^ 2 * (M : ℝ) ^ (4 * (min δ 1 / 4))) hterm
  rw [Nat.card_Icc, nsmul_eq_mul] at hsum
  have hcard : ((M + 1 - 1 : ℕ) : ℝ) = (M : ℝ) := by push_cast; ring
  rw [hcard] at hsum
  have henergy : squareWindowCorrelationEnergy M
      = ∑ m ∈ Finset.Icc 1 M, (squarePrimeWindowCenteredDeviation m) ^ 2 :=
    squareWindowCorrelationEnergy_eq_centeredDeviation_square_sum M
  have hnonneg : 0 ≤ squareWindowCorrelationEnergy M := squareWindowCorrelationEnergy_nonneg M
  have hfinal : (M : ℝ) * (C ^ 2 * (M : ℝ) ^ (4 * (min δ 1 / 4)))
      ≤ C ^ 2 * (M : ℝ) ^ (1 + δ) := by
    have hmul : (M : ℝ) * (M : ℝ) ^ (4 * (min δ 1 / 4))
        = (M : ℝ) ^ (1 + 4 * (min δ 1 / 4)) := by
      rw [Real.rpow_add hM0, Real.rpow_one]
    have hle : (M : ℝ) ^ (1 + 4 * (min δ 1 / 4)) ≤ (M : ℝ) ^ (1 + δ) := by
      refine Real.rpow_le_rpow_of_exponent_le hM1 ?_
      have : min δ 1 ≤ δ := min_le_left _ _
      linarith
    calc (M : ℝ) * (C ^ 2 * (M : ℝ) ^ (4 * (min δ 1 / 4)))
        = C ^ 2 * ((M : ℝ) * (M : ℝ) ^ (4 * (min δ 1 / 4))) := by ring
      _ = C ^ 2 * (M : ℝ) ^ (1 + 4 * (min δ 1 / 4)) := by rw [hmul]
      _ ≤ C ^ 2 * (M : ℝ) ^ (1 + δ) := mul_le_mul_of_nonneg_left hle (by positivity)
  have hpow1 : (0 : ℝ) ≤ (M : ℝ) ^ (1 + δ) := Real.rpow_nonneg hM0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hpow1, henergy]
  linarith [hsum, hfinal]

/-- **The exact equivalence.**  The square-aperture correlation energy is subpower if and only if
the Riemann hypothesis holds. -/
theorem riemannHypothesis_iff_squarePrimeWindowCorrelationEnergySubpower :
    RiemannHypothesis ↔ SquarePrimeWindowCorrelationEnergySubpower :=
  ⟨squarePrimeWindowCorrelationEnergySubpower_of_riemannHypothesis,
    riemannHypothesis_of_squarePrimeWindowCorrelationEnergySubpower⟩

end

end RHTower.Sieve
