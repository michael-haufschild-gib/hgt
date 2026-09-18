import GaloisForLFunctions.PNTPlus.ZetaBounds
import GaloisForLFunctions.RHTower.HighBlockChiModulus
import GaloisForLFunctions.RHTower.ChiPairWeightJets

/-!
# Two inputs for the main terms of the crude `ζΨ` gate

* `re_riemannZeta_ofReal_neg`: `Re ζ(σ) < 0` for real `1/3 < σ < 1`, from the Euler–Maclaurin
  representation at `N = 1` (Zeta23/PNT+): `ζ(σ) = 1 − 1/(1−σ) − 1/2 + σ∫_1^∞(⌊x⌋+½−x)x^{−σ−1}dx`
  with `|σ∫…| ≤ 1`, so `Re ζ(σ) ≤ 3/2 − 1/(1−σ) < 0`.  This is what makes the direct diagonal
  main term `ζ(2σ₀)(∫w)S₁` nonpositive (`S₁ ≥ 0`), so it can be dropped in the upper bound.
* `norm_chiPairWeight_le`: `‖χ(σ₀+it)χ(σ₀−it)‖ ≤ (t/2π)^{2d}·e` for `t ≥ 4`, `σ₀ = ½ − d`,
  `0 ≤ d ≤ 1/4`, from the exact modulus identity of `HighBlockChiModulus`.
-/

open Complex

namespace RHTower

noncomputable section

/-- **`ζ` is negative on `(1/3, 1)`.** -/
theorem re_riemannZeta_ofReal_neg {σ : ℝ} (hσ1 : 1 / 3 < σ) (hσ2 : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 := by
  have hσ0 : 0 < σ := by linarith
  have hre : 0 < ((σ : ℂ)).re := by simp [hσ0]
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  rw [← Zeta0EqZeta one_pos hre hs1, riemannZeta0_apply]
  have hI := ZetaBnd_aux1b 1 le_rfl (t := (0 : ℝ)) hσ0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Nat.cast_one,
    Real.rpow_neg zero_le_one, Real.one_rpow, inv_one] at hI
  simp_rw [div_cpow_eq_cpow_neg] at hI
  simp only [Finset.sum_range_succ, Finset.sum_range_one, Nat.cast_zero, Nat.cast_one,
    Complex.zero_cpow hs0, Complex.one_cpow, div_zero, zero_add, div_one]
  set X : ℂ := (σ : ℂ) * ∫ x in Set.Ioi (1 : ℝ),
    ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-((σ : ℂ) + 1)) with hX
  have hXnorm : ‖X‖ ≤ 1 := by
    rw [hX, norm_mul, Complex.norm_of_nonneg hσ0.le]
    calc σ * ‖∫ x in Set.Ioi (1 : ℝ),
          ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-((σ : ℂ) + 1))‖
        ≤ σ * (1 / σ) := mul_le_mul_of_nonneg_left hI hσ0.le
      _ = 1 := by field_simp
  have hXre : X.re ≤ 1 := (Complex.re_le_norm X).trans hXnorm
  have h1 : ((1 : ℂ) + (-1 / (1 - (σ : ℂ)) + -1 / 2 + X)).re
      = 1 + (-1 / (1 - σ) + -1 / 2 + X.re) := by
    have e1 : (-1 / (1 - (σ : ℂ))) = ((-1 / (1 - σ) : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((-1 / 2 : ℂ)) = ((-1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, Complex.add_re, Complex.add_re, Complex.add_re, Complex.one_re,
      Complex.ofReal_re, Complex.ofReal_re]
  rw [h1]
  have h3 : 3 / 2 < 1 / (1 - σ) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have h4 : -1 / (1 - σ) = -(1 / (1 - σ)) := by ring
  rw [h4]
  linarith

/-! ## The modulus of the `χ`-pair weight -/

theorem displacedLinePt_neg_eq_conj (d t : ℝ) :
    displacedLinePt d (-t) = (starRingEnd ℂ) (displacedLinePt d t) := by
  unfold displacedLinePt
  apply Complex.ext <;> simp

/-- **Sharp modulus of the `χ`-pair weight**: `‖χ(σ₀+it)χ(σ₀−it)‖ ≤ (t/2π)^{2d} e`. -/
theorem norm_chiPairWeight_le {d t : ℝ} (hd0 : 0 ≤ d) (hd4 : d ≤ 1 / 4) (ht : 4 ≤ t) :
    ‖chiPairWeight d t‖ ≤ chiModulusWeight (2 * d) t * Real.exp 1 := by
  have ht0 : 0 < t := by linarith
  obtain ⟨e, he, heq⟩ := exists_norm_zetaChi_displacedLinePt_eq_weight_mul_exp hd0 hd4 ht0
  unfold chiPairWeight
  rw [norm_mul, displacedLinePt_neg_eq_conj, zetaChi_conj, Complex.norm_conj, heq]
  have hw : chiModulusWeight d t * chiModulusWeight d t = chiModulusWeight (2 * d) t := by
    unfold chiModulusWeight
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  have he1 : 2 * e ≤ 1 := by
    have hπ : Real.pi ≤ 4 := Real.pi_le_four
    have hπt : Real.pi / t ≤ 1 := by
      rw [div_le_one ht0]; linarith
    have h5t : 5 / t ^ 2 ≤ 5 / 16 := by
      have : (16 : ℝ) ≤ t ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
    have hsum : d * (Real.pi / t + 5 / t ^ 2) ≤ 1 / 4 * (1 + 5 / 16) := by
      apply mul_le_mul hd4 (by linarith) (by positivity) (by norm_num)
    have := (abs_le.mp he).2
    linarith
  have hw2 : 0 ≤ chiModulusWeight (2 * d) t := by unfold chiModulusWeight; positivity
  calc chiModulusWeight d t * Real.exp e * (chiModulusWeight d t * Real.exp e)
      = (chiModulusWeight d t * chiModulusWeight d t) * Real.exp (2 * e) := by
        rw [show (2 : ℝ) * e = e + e by ring, Real.exp_add]; ring
    _ ≤ chiModulusWeight (2 * d) t * Real.exp 1 := by
        rw [hw]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he1) hw2

end

end RHTower
