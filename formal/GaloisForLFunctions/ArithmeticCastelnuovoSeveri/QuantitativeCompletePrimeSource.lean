import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompletePrimeSourceTransfer

/-! # An explicit error constant for the full prime source on logarithmic cells

The same source supremum and Lipschitz bounds pay the divisibility quadrature
and every signed successor contribution. The finite prime weight is exact.
-/

noncomputable section
open Finset MeasureTheory

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

/-- Explicit coefficient of the `1/N` error in the complete prime source. -/
def completeCellPrimeRate (B : ℕ) (C K : ℝ) : ℝ :=
  primeWeightSum B *
    (Real.sqrt ((B : ℝ) * C ^ 2) * Real.sqrt ((B : ℝ) ^ 2 * K ^ 2) +
      (B : ℝ) * (2 * C * K))

theorem completeCellPrimeRate_nonneg (B : ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    0 ≤ completeCellPrimeRate B C K := by
  unfold completeCellPrimeRate
  exact mul_nonneg (primeWeightSum_nonneg B) (by positivity)

private theorem lipschitz_product_shift {f : ℝ → ℝ} {K : NNReal}
    (hK : LipschitzWith K f) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |f u| ≤ C) (t : ℝ) :
    LipschitzWith (2 * ⟨C, hC⟩ * K) (fun u => f u * f (u + t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have h1 := hK.norm_sub_le u v
  have h2 := hK.norm_sub_le (u + t) (v + t)
  simp only [Real.norm_eq_abs] at h1 h2
  rw [show (u + t) - (v + t) = u - v by ring] at h2
  change |f u * f (u + t) - f v * f (v + t)| ≤ (2 * C * (K : ℝ)) * |u - v|
  calc |f u * f (u + t) - f v * f (v + t)| =
        |(f u - f v) * f (u + t) + f v * (f (u + t) - f (v + t))| := by
          congr 1; ring
    _ ≤ |f u - f v| * |f (u + t)| + |f v| * |f (u + t) - f (v + t)| := by
      simpa only [abs_mul] using abs_add_le ((f u - f v) * f (u + t))
        (f v * (f (u + t) - f (v + t)))
    _ ≤ ((K : ℝ) * |u - v|) * C + C * ((K : ℝ) * |u - v|) :=
      add_le_add (mul_le_mul h1 (hb (u + t)) (abs_nonneg _) (by positivity))
        (mul_le_mul (hb v) h2 (abs_nonneg _) hC)
    _ = _ := by ring

/-- A product of two bounded source translates has Lipschitz constant `2 C K`. -/
theorem abs_primeCellSpine_self_sub_le {f : ℝ → ℝ} {K : NNReal}
    (hK : LipschitzWith K f) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |f u| ≤ C)
    (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    |primeCellSpine (logSamples f R N) (logSamples f R N) N (N * B) B -
      smoothPrimePair f f| ≤ primeWeightSum B * ((B : ℝ) * (2 * C * (K : ℝ))) / N := by
  let w : ℕ → ℝ := fun m => 2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m
  have hw (m : ℕ) : 0 ≤ w m := div_nonneg
    (mul_nonneg (by norm_num) (ArithmeticFunction.vonMangoldt_nonneg (n := m)))
    (Real.sqrt_nonneg m)
  rw [smoothPrimePair_eq_sum f f R hB (fun u hu => ⟨hs u hu, hs u hu⟩)]
  unfold primeCellSpine primeWeightSum
  rw [← sum_sub_distrib, sum_mul, sum_div]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro m hm
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw m),
    cellSpine_logSamples_eq f f R hN B (mem_Icc.mp hm).1]
  have hq := abs_logQuadrature_sub_integral_le
    (lipschitz_product_shift hK hC hb (Real.log m)) R hN hB
    (fun u hu => by rw [hs u hu, zero_mul])
  change _ ≤ ((B : ℝ) * (2 * C * (K : ℝ))) / N at hq
  have hd := mul_le_mul_of_nonneg_left hq (hw m)
  simpa only [← mul_div_assoc] using hd

/-- The exact prime series of the literal cells has the explicit `1/N` bound. -/
theorem abs_cellPrimeEnergy_sub_primeSum_le {f : ℝ → ℝ} {K : NNReal}
    (hK : LipschitzWith K f) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |f u| ≤ C)
    (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    |cellPrimeEnergy (logSamples f R N) N (N * B) - _root_.RHTower.primeSum f| ≤
      completeCellPrimeRate B C K / N := by
  have hsupport := logSamples_eq_zero_above R hN hB
    (fun u hu => hs u (Or.inr hu.le))
  rw [← fullPrimeSectionPair_self_logSamples f R hN (N * B) (hs (-R) (Or.inl le_rfl)),
    ← smoothPrimePair_self_eq_primeSum,
    fullPrimeSectionPair_eq _ _ hN (N * B) hB le_rfl hsupport]
  have hsplit := abs_add_le
    (primeSectionPair (logSamples f R N) (logSamples f R N) N (N * B) B -
      primeCellSpine (logSamples f R N) (logSamples f R N) N (N * B) B)
    (primeCellSpine (logSamples f R N) (logSamples f R N) N (N * B) B - smoothPrimePair f f)
  rw [sub_add_sub_cancel, primeSectionPair_sub_spine _ _ hN (N * B) B hsupport] at hsplit
  calc _ ≤ |primeCellRemainder (logSamples f R N) (logSamples f R N) N (N * B) B| +
        |primeCellSpine (logSamples f R N) (logSamples f R N) N (N * B) B - smoothPrimePair f f| :=
      hsplit
    _ ≤ (primeWeightSum B * (Real.sqrt ((B : ℝ) * C ^ 2) *
          Real.sqrt ((B : ℝ) ^ 2 * (K : ℝ) ^ 2))) / N +
        primeWeightSum B * ((B : ℝ) * (2 * C * (K : ℝ))) / N :=
      add_le_add (abs_primeCellRemainder_logSamples_le hC hb hK R hN hB B
        (fun u hu => hs u (Or.inr hu.le)))
        (abs_primeCellSpine_self_sub_le hK hC hb R hN hB hs)
    _ = completeCellPrimeRate B C K / N := by unfold completeCellPrimeRate; ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.abs_cellPrimeEnergy_sub_primeSum_le
