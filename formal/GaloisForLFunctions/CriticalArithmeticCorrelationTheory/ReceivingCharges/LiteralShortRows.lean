import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.AffineShortRows
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralMultiplierGeometry
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralPrimeIncidence

/-!
# Prime-progression control of actual short rows

Both original offset signs satisfy the supported affine estimate.
Every horizon cutoff and the full proper-power remainder are retained.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open MeasureTheory Finset ArithmeticFunction
open GaloisForLFunctions
open CriticalArithmeticCorrelationTheory BezoutValuationIncidence
  CriticalScaleArithmeticRigidity ArithmeticCouplingTheory

/-- The two literal signs obey the short-row prime-progression bound with every original cutoff. -/
theorem exists_literal_prime_short_row_bound :
    ∃ p₀ : ℕ, 8 ≤ p₀ ∧ ∀ (φ : ℝ → ℝ), ContDiff ℝ 2 φ →
      (∀ u, u ∉ Set.Icc 0 1 → φ u = 0) → (0 < ∫ u, φ u ^ 2) →
      ∀ (c : ℝ), 0 < c → ∀ (N n : ℕ), n ∈ Icc 1 N → c / N ≤ 1 →
      linearPrimeStrip c ≤ N → 2 * c * Real.exp 1 * linearPrimeStrip c ≤ N →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p₀ ≤ p) →
      (∀ p ∈ P, linearPrimeStrip c < p) →
      (∀ p ∈ P, p ^ 2 ≤ literalMultiplierLower c N n) →
      ∀ (G : ℕ → ℝ) (s V : ℝ), 0 ≤ V → (∀ j, |G j| ≤ V) →
      |logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N
        (fun j => G j * incidencePacket P (fun _ => s) j) n| ≤
        4 * (linearPrimeStrip c : ℝ) * |s| * V *
          (1027 * literalMultiplierWidth c * (∑ p ∈ P, 1 / (p : ℝ)) +
            576 * (P.card : ℝ) * (literalMultiplierLower c N n : ℝ) ^ (-(7 / 16 : ℝ))) := by
  obtain ⟨p₀, hp₀, hband⟩ := exists_affine_short_band_bound
  refine ⟨p₀, hp₀, ?_⟩
  intro φ hφ hsupp hmass c hc N n hn hwidth hB hsep P hp hpp hBP hpH G s V hV hG
  have hn1 := (mem_Icc.mp hn).1
  have hN : 1 ≤ N := hn1.trans (mem_Icc.mp hn).2
  have hU : 0 ≤ 2 * ∫ u, φ u ^ 2 := mul_nonneg zero_le_two hmass.le
  have hsign (T : ℕ → ℕ → ℕ) (f : ℕ → ℕ → ℝ) (b : ℕ → ℕ → ℕ)
      (hb : ∀ p ∈ P, ∀ h ∈ Icc 1 (linearPrimeStrip c), p.Coprime (b p h))
      (hf : ∀ k ∈ Icc 1 (N + linearPrimeStrip c), ∀ h ∈ Icc 1 (linearPrimeStrip c),
        |f k h| ≤ 2 * ∫ u, φ u ^ 2)
      (hs : ∀ k ∈ Icc 1 (N + linearPrimeStrip c), ∀ h ∈ Icc 1 (linearPrimeStrip c),
        f k h ≠ 0 → k ∈ Icc (literalMultiplierLower c N n) (literalMultiplierUpper c N n))
      (hi : ∀ p ∈ P, ∀ k ∈ Icc 1 (N + linearPrimeStrip c), ∀ h ∈ Icc 1 (linearPrimeStrip c),
        f k h * ((if p ∣ T k h then (1 : ℝ) else 0) - 1 / p) =
          f k h * ((if n * k ≡ b p h [MOD p] then (1 : ℝ) else 0) - 1 / p)) :
      |∑ k ∈ Icc 1 (N + linearPrimeStrip c), (vonMangoldt k / (k : ℝ)) *
        ∑ h ∈ Icc 1 (linearPrimeStrip c),
          (G (T k h) * incidencePacket P (fun _ => s) (T k h)) * f k h| ≤
        |s| * (linearPrimeStrip c : ℝ) * V * (2 * ∫ u, φ u ^ 2) *
          (1027 * literalMultiplierWidth c * (∑ p ∈ P, 1 / (p : ℝ)) +
            576 * (P.card : ℝ) * (literalMultiplierLower c N n : ℝ) ^ (-(7 / 16 : ℝ))) := by
    have he :
        (∑ k ∈ Icc 1 (N + linearPrimeStrip c), (vonMangoldt k / (k : ℝ)) *
          ∑ h ∈ Icc 1 (linearPrimeStrip c),
            (G (T k h) * incidencePacket P (fun _ => s) (T k h)) * f k h) =
        ∑ i ∈ Icc 1 (N + linearPrimeStrip c) ×ˢ Icc 1 (linearPrimeStrip c),
          ((vonMangoldt i.1 / (i.1 : ℝ)) * f i.1 i.2) * G (T i.1 i.2) *
            incidencePacket P (fun _ => s) (T i.1 i.2) := by
      simp only [sum_product, mul_sum]
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro h _
      ring
    rw [he, finite_prime_band_row]
    have hsum :
        (∑ p ∈ P, ∑ i ∈ Icc 1 (N + linearPrimeStrip c) ×ˢ Icc 1 (linearPrimeStrip c),
          ((vonMangoldt i.1 / (i.1 : ℝ)) * f i.1 i.2) * G (T i.1 i.2) *
            ((if p ∣ T i.1 i.2 then (1 : ℝ) else 0) - 1 / p)) =
        ∑ p ∈ P, ∑ h ∈ Icc 1 (linearPrimeStrip c), ∑ k ∈ Icc 1 (N + linearPrimeStrip c),
          (vonMangoldt k / (k : ℝ)) * G (T k h) * f k h *
            ((if n * k ≡ b p h [MOD p] then (1 : ℝ) else 0) - 1 / p) := by
      simp only [sum_product]
      apply sum_congr rfl
      intro p hpP
      rw [sum_comm]
      apply sum_congr rfl
      intro h hh
      apply sum_congr rfl
      intro k hk
      calc
        _ = (vonMangoldt k / (k : ℝ)) * G (T k h) *
            (f k h * ((if p ∣ T k h then (1 : ℝ) else 0) - 1 / p)) := by ring
        _ = _ := by rw [hi p hpP k hk h hh]; ring
    rw [hsum]
    exact hband P (literalMultiplierLower c N n) (literalMultiplierUpper c N n)
      (N + linearPrimeStrip c) (linearPrimeStrip c) n hp hpp hpH b hb
      (fun _ k h => G (T k h)) f s (2 * ∫ u, φ u ^ 2) V (literalMultiplierWidth c)
      hU hV (literalMultiplierWidth_nonneg c) (fun _ _ _ _ _ _ => hG _) hf hs
      (literalMultiplierWidth_bounds hc hN hn1 hB)
  have hplus := hsign (fun k h => k * n + h)
    (fun k h => positiveLiteralUpwardKernel φ c N k h n) (fun p h => p - h)
    (fun p hpP h hh => prime_positive_offset_unit (hp p hpP) (mem_Icc.mp hh).1
      ((mem_Icc.mp hh).2.trans_lt (hBP p hpP)))
    (fun k hk h hh => (abs_literalUpwardKernels_le_of_separation hφ hsupp hc hN
      (mem_Icc.mp hk).1 hh hn1 hwidth hsep).1)
    (fun k hk h hh => positiveLiteralUpwardKernel_support hφ hsupp hc hN
      (mem_Icc.mp hk).1 (mem_Icc.mp hh).1 hn1 hwidth)
    (by
      intro p hpP k _ h hh
      have hhp : h ≤ p := ((mem_Icc.mp hh).2.trans_lt (hBP p hpP)).le
      simp only [dvd_positive_shift_iff hhp, Nat.mul_comm k n])
  have hminus := hsign (fun k h => k * n - h)
    (fun k h => negativeLiteralUpwardKernel φ c N k h n) (fun _ h => h)
    (fun p hpP h hh => prime_negative_offset_unit (hp p hpP) (mem_Icc.mp hh).1
      ((mem_Icc.mp hh).2.trans_lt (hBP p hpP)))
    (fun k hk h hh => (abs_literalUpwardKernels_le_of_separation hφ hsupp hc hN
      (mem_Icc.mp hk).1 hh hn1 hwidth hsep).2)
    (fun k hk h hh => negativeLiteralUpwardKernel_support hφ hsupp hc hN
      (mem_Icc.mp hk).1 (mem_Icc.mp hh).1 hn1 hwidth)
    (by
      intro p _ k _ h _
      by_cases hhk : h ≤ k * n
      · simp only [dvd_negative_shift_iff hhk, Nat.mul_comm k n]
      · have hz : negativeLiteralUpwardKernel φ c N k h n = 0 := by
          rw [negativeLiteralUpwardKernel, if_neg (by omega)]
        rw [hz, zero_mul, zero_mul])
  rw [logarithmicUpwardProfileCoefficient_eq_rows, abs_div, abs_of_pos hmass]
  apply (div_le_iff₀ hmass).mpr
  exact ((abs_add_le _ _).trans (add_le_add hplus hminus)).trans_eq (by ring)

#print axioms exists_literal_prime_short_row_bound

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
