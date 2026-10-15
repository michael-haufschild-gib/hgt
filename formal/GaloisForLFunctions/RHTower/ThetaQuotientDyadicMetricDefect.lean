import GaloisForLFunctions.RHTower.ThetaQuotientPairedBlockMetric

/-!
# Exact dyadic defect of the theta paired-block metric

Let `D` be the full theta quotient and `G₀` its positive paired-block metric.
The two matrix elements of `G₀ D - D* G₀` joining frequencies `n` to `±2n`
obey an exact source identity. Writing `r = (Φ₂ₙ-Φₙ)/Φₙ` and
`s = (Φ₄ₙ-Φ₂ₙ)/Φ₂ₙ`, a linear combination cancels `Φ₃ₙ` and equals

`-2 Φₙ r (1+s) (3+r-2s) < 0`.

Thus each dyadic scale carries a nonzero metric defect. Every exact repair
must supply the opposite signed functional at every scale; agreement with
`G₀` outside finitely many Fourier frequencies is impossible.
-/

open MeasureTheory
open scoped InnerProductSpace
namespace RHTower
noncomputable section
local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

private theorem metric_pos (n : ℕ) :
    pairedBlockMetric (unitFourierBasis (blockPos n)) =
      unitFourierBasis (blockPos n) +
        (pairRatio n : ℂ) • unitFourierBasis (blockNeg n) := by
  rw [pairedBlockMetric, add_apply,
    one_apply_eq_self,
    pairMetricOffDiag_apply_of_mem (pairProj_unitFourierBasis_pos n),
    frequencySwap_apply, inner_unitFourierBasis, inner_unitFourierBasis,
    if_pos rfl, if_neg (Ne.symm (blockPos_ne_blockNeg n))]
  simp

private theorem metric_neg (n : ℕ) :
    pairedBlockMetric (unitFourierBasis (blockNeg n)) =
      unitFourierBasis (blockNeg n) +
        (pairRatio n : ℂ) • unitFourierBasis (blockPos n) := by
  rw [pairedBlockMetric, add_apply,
    one_apply_eq_self,
    pairMetricOffDiag_apply_of_mem (pairProj_unitFourierBasis_neg n),
    frequencySwap_apply, inner_unitFourierBasis, inner_unitFourierBasis,
    if_neg (blockPos_ne_blockNeg n), if_pos rfl]
  simp

private theorem metric_nat_pos {n : ℕ} (hn : 1 ≤ n) :
    pairedBlockMetric (unitFourierBasis n) =
      unitFourierBasis n + (dyadicRatio n : ℂ) • unitFourierBasis (-(n : ℤ)) := by
  have h := metric_pos (n - 1)
  have he : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have heZ : ((n - 1 : ℕ) : ℤ) + 1 = n := by omega
  simpa only [blockPos, blockNeg, pairRatio, he, heZ] using h

private theorem metric_nat_neg {n : ℕ} (hn : 1 ≤ n) :
    pairedBlockMetric (unitFourierBasis (-(n : ℤ))) =
      unitFourierBasis (-(n : ℤ)) + (dyadicRatio n : ℂ) • unitFourierBasis n := by
  have h := metric_neg (n - 1)
  have he : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have heZ : ((n - 1 : ℕ) : ℤ) + 1 = n := by omega
  simpa only [blockPos, blockNeg, pairRatio, he, heZ] using h

/-- The source pairing whose zero value is necessary for metric self-adjointness. -/
def thetaQuotientMetricDefectEntry (Q : ThetaL2 →L[ℂ] ThetaL2) (m n : ℤ) : ℂ :=
  ⟪Q (unitFourierBasis m),
    thetaQuotientOperator (unitFourierBasis n)⟫_ℂ -
  ⟪thetaQuotientOperator (unitFourierBasis m),
    Q (unitFourierBasis n)⟫_ℂ

private theorem reverse_entry {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ⟪thetaQuotientOperator (unitFourierBasis m), unitFourierBasis n⟫_ℂ =
      (((cdfAction n - cdfAction (m - n)) / (2 * Real.pi * m) : ℝ) : ℂ) := by
  rw [← inner_conj_symm, inner_unitFourierBasis_thetaQuotientOperator hn hm,
    Complex.conj_ofReal]

private theorem entry_pos {n : ℕ} (hn : 1 ≤ n) :
    (4 * Real.pi * n) * (thetaQuotientMetricDefectEntry pairedBlockMetric n (2 * (n : ℤ))).re =
      (-dyadicRatio n + 2 * dyadicRatio (2 * n)) *
        (cdfAction (3 * (n : ℤ)) - cdfAction n) -
      2 * cdfAction n * dyadicRatio n * (1 + dyadicRatio (2 * n)) := by
  have hnz : (n : ℤ) ≠ 0 := by omega
  have hn2 : 1 ≤ 2 * n := by omega
  have h2z : 2 * (n : ℤ) ≠ 0 := by omega
  have hmz : -(n : ℤ) ≠ 0 := neg_ne_zero.mpr hnz
  have hm2z : -(2 * (n : ℤ)) ≠ 0 := neg_ne_zero.mpr h2z
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnz
  have hratio : cdfAction n * dyadicRatio n =
      cdfAction (2 * (n : ℤ)) - cdfAction n := by
    rw [dyadicRatio, mul_div_cancel₀ _ (cdfAction_pos hn).ne']
  unfold thetaQuotientMetricDefectEntry
  rw [metric_nat_pos hn, show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by simp,
    metric_nat_pos hn2]
  simp only [inner_add_left, inner_smul_left, inner_add_right, inner_smul_right,
    Complex.conj_ofReal]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [inner_unitFourierBasis_thetaQuotientOperator hnz h2z,
    inner_unitFourierBasis_thetaQuotientOperator hmz h2z,
    reverse_entry hnz h2z, reverse_entry hnz hm2z]
  have e1 : 2 * (n : ℤ) - n = n := by ring
  have e2 : 2 * (n : ℤ) - -n = 3 * n := by ring
  have e3 : (n : ℤ) - 2 * n = -n := by ring
  have e4 : (n : ℤ) - -(2 * n) = 3 * n := by ring
  simp only [e1, e2, e3, e4, cdfAction_neg]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_add,
    Complex.ofReal_re, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  have hb : cdfAction (2 * (n : ℤ)) =
      cdfAction n + cdfAction n * dyadicRatio n := by linarith only [hratio]
  rw [hb]
  field_simp
  ring

private theorem entry_neg {n : ℕ} (hn : 1 ≤ n) :
    (4 * Real.pi * n) * (thetaQuotientMetricDefectEntry pairedBlockMetric n (-(2 * (n : ℤ)))).re =
      3 * (cdfAction (3 * (n : ℤ)) - cdfAction n) -
      2 * cdfAction n * dyadicRatio n * (1 + dyadicRatio (2 * n)) := by
  have hnz : (n : ℤ) ≠ 0 := by omega
  have hn2 : 1 ≤ 2 * n := by omega
  have h2z : 2 * (n : ℤ) ≠ 0 := by omega
  have hmz : -(n : ℤ) ≠ 0 := neg_ne_zero.mpr hnz
  have hm2z : -(2 * (n : ℤ)) ≠ 0 := neg_ne_zero.mpr h2z
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnz
  have hratio : cdfAction n * dyadicRatio n =
      cdfAction (2 * (n : ℤ)) - cdfAction n := by
    rw [dyadicRatio, mul_div_cancel₀ _ (cdfAction_pos hn).ne']
  unfold thetaQuotientMetricDefectEntry
  rw [metric_nat_pos hn, show -(2 * (n : ℤ)) = -((2 * n : ℕ) : ℤ) by simp,
    metric_nat_neg hn2]
  simp only [inner_add_left, inner_smul_left, inner_add_right, inner_smul_right,
    Complex.conj_ofReal, Nat.cast_mul, Nat.cast_ofNat]
  rw [inner_unitFourierBasis_thetaQuotientOperator hnz hm2z,
    inner_unitFourierBasis_thetaQuotientOperator hmz hm2z,
    reverse_entry hnz hm2z, reverse_entry hnz h2z]
  have e1 : -(2 * (n : ℤ)) - n = -(3 * n) := by ring
  have e2 : -(2 * (n : ℤ)) - -n = -n := by ring
  have e3 : (n : ℤ) - 2 * n = -n := by ring
  have e4 : (n : ℤ) - -(2 * n) = 3 * n := by ring
  simp only [e1, e2, e3, e4, cdfAction_neg]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_add,
    Complex.ofReal_re, Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  have hb : cdfAction (2 * (n : ℤ)) =
      cdfAction n + cdfAction n * dyadicRatio n := by linarith only [hratio]
  rw [hb]
  field_simp
  ring

/-- A real linear observation of the full metric defect on two adjacent dyadic pairs. -/
def thetaQuotientDyadicMetricDefect (Q : ThetaL2 →L[ℂ] ThetaL2) (n : ℕ) : ℝ :=
  (4 * Real.pi * n) *
    (3 * (thetaQuotientMetricDefectEntry Q n (2 * (n : ℤ))).re +
      (dyadicRatio n - 2 * dyadicRatio (2 * n)) *
        (thetaQuotientMetricDefectEntry Q n (-(2 * (n : ℤ)))).re)

/-- The middle-frequency source action cancels exactly from the dyadic defect. -/
theorem thetaQuotientDyadicMetricDefect_paired_eq {n : ℕ} (hn : 1 ≤ n) :
    thetaQuotientDyadicMetricDefect pairedBlockMetric n =
      -2 * cdfAction n * dyadicRatio n * (1 + dyadicRatio (2 * n)) *
        (3 + dyadicRatio n - 2 * dyadicRatio (2 * n)) := by
  calc
    thetaQuotientDyadicMetricDefect pairedBlockMetric n =
      3 * ((4 * Real.pi * n) *
        (thetaQuotientMetricDefectEntry pairedBlockMetric n (2 * (n : ℤ))).re) +
      (dyadicRatio n - 2 * dyadicRatio (2 * n)) *
        ((4 * Real.pi * n) *
          (thetaQuotientMetricDefectEntry pairedBlockMetric n (-(2 * (n : ℤ)))).re) := by
      unfold thetaQuotientDyadicMetricDefect
      ring
    _ = _ := by rw [entry_pos hn, entry_neg hn]; ring

/-- Every dyadic scale has a strictly oriented full-source defect. -/
theorem thetaQuotientDyadicMetricDefect_paired_neg {n : ℕ} (hn : 1 ≤ n) :
    thetaQuotientDyadicMetricDefect pairedBlockMetric n < 0 := by
  rw [thetaQuotientDyadicMetricDefect_paired_eq hn]
  have ha := cdfAction_pos hn
  have hr : 0 < dyadicRatio n := (dyadicRatio_mem_Ioo hn).1
  have hs : 0 < dyadicRatio (2 * n) := (dyadicRatio_mem_Ioo (by omega : 1 ≤ 2 * n)).1
  have hs1 : dyadicRatio (2 * n) < 1 := (dyadicRatio_mem_Ioo (by omega : 1 ≤ 2 * n)).2
  have hf : 0 < 3 + dyadicRatio n - 2 * dyadicRatio (2 * n) := by linarith
  have hp : 0 < 2 * cdfAction n * dyadicRatio n * (1 + dyadicRatio (2 * n)) *
      (3 + dyadicRatio n - 2 * dyadicRatio (2 * n)) := by positivity
  nlinarith only [hp]

private theorem defectEntry_zero_of_symmetry (Q : ThetaL2 →L[ℂ] ThetaL2)
    (hQ : ContinuousLinearMap.adjoint Q = Q)
    (hQD : Q ∘L thetaQuotientOperator = ContinuousLinearMap.adjoint thetaQuotientOperator ∘L Q)
    (m n : ℤ) : thetaQuotientMetricDefectEntry Q m n = 0 := by
  unfold thetaQuotientMetricDefectEntry
  rw [← hQ, ContinuousLinearMap.adjoint_inner_left, hQ]
  have h := DFunLike.congr_fun hQD (unitFourierBasis n)
  change Q (thetaQuotientOperator (unitFourierBasis n)) =
    ContinuousLinearMap.adjoint thetaQuotientOperator (Q (unitFourierBasis n)) at h
  rw [h, ContinuousLinearMap.adjoint_inner_right, sub_self]

/-- The positive paired-block metric cannot symmetrize the full theta quotient. -/
theorem pairedBlockMetric_not_symmetrizes_thetaQuotientOperator :
    pairedBlockMetric ∘L thetaQuotientOperator ≠
      ContinuousLinearMap.adjoint thetaQuotientOperator ∘L pairedBlockMetric := by
  intro h
  have hz := defectEntry_zero_of_symmetry pairedBlockMetric
    (ContinuousLinearMap.isSelfAdjoint_iff'.mp isSelfAdjoint_pairedBlockMetric) h
  have hneg := thetaQuotientDyadicMetricDefect_paired_neg (n := 1) le_rfl
  simp only [thetaQuotientDyadicMetricDefect, hz, Complex.zero_re, mul_zero, add_zero,
    lt_self_iff_false] at hneg

/-- Additivity retains the complete correction, including all cross-frequency terms. -/
theorem thetaQuotientDyadicMetricDefect_add
    (Q R : ThetaL2 →L[ℂ] ThetaL2) (n : ℕ) :
    thetaQuotientDyadicMetricDefect (Q + R) n =
      thetaQuotientDyadicMetricDefect Q n + thetaQuotientDyadicMetricDefect R n := by
  simp only [thetaQuotientDyadicMetricDefect, thetaQuotientMetricDefectEntry,
    add_apply, inner_add_left, inner_add_right, Complex.sub_re, Complex.add_re]
  ring

/-- Every exact self-adjoint repair supplies the opposite signed source charge at every scale. -/
theorem thetaQuotientDyadicMetricDefect_repair_eq
    (R : ThetaL2 →L[ℂ] ThetaL2)
    (hQ : ContinuousLinearMap.adjoint (pairedBlockMetric + R) = pairedBlockMetric + R)
    (hQD : (pairedBlockMetric + R) ∘L thetaQuotientOperator =
      ContinuousLinearMap.adjoint thetaQuotientOperator ∘L (pairedBlockMetric + R))
    {n : ℕ} (hn : 1 ≤ n) :
    thetaQuotientDyadicMetricDefect R n =
      2 * cdfAction n * dyadicRatio n * (1 + dyadicRatio (2 * n)) *
        (3 + dyadicRatio n - 2 * dyadicRatio (2 * n)) := by
  have he := defectEntry_zero_of_symmetry (pairedBlockMetric + R) hQ hQD
  have hz : thetaQuotientDyadicMetricDefect (pairedBlockMetric + R) n = 0 := by
    simp only [thetaQuotientDyadicMetricDefect, he, Complex.zero_re,
      mul_zero, add_zero]
  rw [thetaQuotientDyadicMetricDefect_add,
    thetaQuotientDyadicMetricDefect_paired_eq hn] at hz
  linarith only [hz]

/-- A symmetrizer must change at least one of three Fourier vectors at every dyadic scale. -/
theorem thetaQuotient_symmetrizer_changes_each_dyadic_pair
    (Q : ThetaL2 →L[ℂ] ThetaL2)
    (hQ : ContinuousLinearMap.adjoint Q = Q)
    (hQD : Q ∘L thetaQuotientOperator = ContinuousLinearMap.adjoint thetaQuotientOperator ∘L Q)
    {n : ℕ} (hn : 1 ≤ n) :
    Q (unitFourierBasis n) ≠ pairedBlockMetric (unitFourierBasis n) ∨
    Q (unitFourierBasis (2 * (n : ℤ))) ≠
      pairedBlockMetric (unitFourierBasis (2 * (n : ℤ))) ∨
    Q (unitFourierBasis (-(2 * (n : ℤ)))) ≠
      pairedBlockMetric (unitFourierBasis (-(2 * (n : ℤ)))) := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  have hz1 := defectEntry_zero_of_symmetry Q hQ hQD n (2 * (n : ℤ))
  have hz2 := defectEntry_zero_of_symmetry Q hQ hQD n (-(2 * (n : ℤ)))
  simp only [thetaQuotientMetricDefectEntry, h1, h2, h3] at hz1 hz2
  have hneg := thetaQuotientDyadicMetricDefect_paired_neg hn
  simp only [thetaQuotientDyadicMetricDefect, thetaQuotientMetricDefectEntry,
    hz1, hz2, Complex.zero_re, mul_zero, add_zero, lt_self_iff_false] at hneg

/-- Changing only finitely many Fourier frequencies cannot repair the paired-block metric. -/
theorem no_eventually_pairedBlockMetric_thetaQuotient_symmetrizer :
    ¬ ∃ Q : ThetaL2 →L[ℂ] ThetaL2,
      ContinuousLinearMap.adjoint Q = Q ∧
      Q ∘L thetaQuotientOperator = ContinuousLinearMap.adjoint thetaQuotientOperator ∘L Q ∧
      ∃ N : ℕ, ∀ m : ℤ, N < m.natAbs →
        Q (unitFourierBasis m) = pairedBlockMetric (unitFourierBasis m) := by
  rintro ⟨Q, hQ, hQD, N, htail⟩
  have habs : (((N + 1 : ℕ) : ℤ)).natAbs = N + 1 := Int.natAbs_natCast _
  have h1 := htail ((N + 1 : ℕ) : ℤ) (by rw [habs]; omega)
  have h2 := htail (2 * ((N + 1 : ℕ) : ℤ)) (by
    rw [Int.natAbs_mul, habs]
    change N < 2 * (N + 1)
    omega)
  have h3 := htail (-(2 * ((N + 1 : ℕ) : ℤ))) (by
    rw [Int.natAbs_neg, Int.natAbs_mul, habs]
    change N < 2 * (N + 1)
    omega)
  rcases thetaQuotient_symmetrizer_changes_each_dyadic_pair Q hQ hQD
    (n := N + 1) (by omega) with h | h | h
  · exact h (by simpa using h1)
  · exact h h2
  · exact h h3

end
end RHTower
