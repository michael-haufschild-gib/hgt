import GaloisForLFunctions.RHTower.VonMangoldtGammaClockDescent
import GaloisForLFunctions.RHTower.SpurCumulantBounds

/-!
# All-depth orientation of the von Mangoldt--Gamma descent anomaly

The finite Gamma clock does not intertwine source translation.  On a single positive exponential
source atom, its zeroth output coordinate is exactly the omitted Taylor tail of `exp (-rate)`.
Taylor's theorem therefore gives a strict alternating orientation at every positive clock depth.

The final theorem specializes this to the actual resolved von Mangoldt mass `Lambda(n) / n` and
frequency `log n`.  It is a source-specific positivity result: it neither reconstructs Xi nor
assumes anything about its divisor.  It does not yet prove that the reduced Euler-boundary
Gauss--Ward response equals the canonical completed prime--Gamma moment form.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open Polynomial
open GaloisForLFunctions.HTGeometry

/-- The scalar Taylor-tail atom exposed in the zeroth coordinate at Gamma depth `N`. -/
def singletonExponentialGammaAnomalyAtom
    (weight rate x : ℝ) (N : ℕ) : ℂ :=
  (weight : ℂ) * Complex.exp (-(x : ℂ) * (rate : ℂ)) *
    (((expNegTruncPoly N).eval rate : ℝ) - Real.exp (-rate))

theorem singletonExponentialGammaAnomalyAtom_eq_ofReal
    (weight rate x : ℝ) (N : ℕ) :
    singletonExponentialGammaAnomalyAtom weight rate x N =
      (weight * Real.exp (-x * rate) *
        ((expNegTruncPoly N).eval rate - Real.exp (-rate)) : ℝ) := by
  rw [singletonExponentialGammaAnomalyAtom]
  push_cast
  rfl

/-- The omitted exponential Taylor tail has a strict alternating orientation at every positive
depth and every positive rate. -/
theorem expNegTruncPoly_sub_exp_oriented_pos
    {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : 0 < x) :
    0 < (-1 : ℝ) ^ (m + 1) *
      ((expNegTruncPoly m).eval x - Real.exp (-x)) := by
  obtain ⟨Q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  obtain ⟨x', hx', hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := fun y : ℝ => Real.exp (-y)) (x := x) (x₀ := 0) (n := Q)
      (ne_of_lt hx) (contDiff_exp_neg.contDiffOn)
  rw [taylorWithinEval_exp_neg_eq_expNegTruncPoly hx Q] at hrem
  have hx'u : x' ∈ Set.Ioo (0 : ℝ) x := by
    simpa [Set.uIoo_of_le hx.le] using hx'
  have hpositive :
      0 < Real.exp (-x') * x ^ (Q + 1) / ((Q + 1).factorial : ℝ) := by
    positivity
  have heq :
      (expNegTruncPoly (Q + 1)).eval x - Real.exp (-x) =
        (-1 : ℝ) ^ (Q + 2) *
          (Real.exp (-x') * x ^ (Q + 1) / ((Q + 1).factorial : ℝ)) := by
    calc
      (expNegTruncPoly (Q + 1)).eval x - Real.exp (-x) =
          -(Real.exp (-x) - (expNegTruncPoly (Q + 1)).eval x) := by ring
      _ = -(((-1 : ℝ) ^ (Q + 1) * Real.exp (-x')) *
          x ^ (Q + 1) / ((Q + 1).factorial : ℝ)) := by
        rw [hrem, iteratedDeriv_exp_neg]
        simp only [sub_zero]
      _ = (-1 : ℝ) ^ (Q + 2) *
          (Real.exp (-x') * x ^ (Q + 1) / ((Q + 1).factorial : ℝ)) := by
        rw [show Q + 2 = (Q + 1) + 1 by omega, pow_succ]
        ring
  rw [heq]
  calc
    0 < Real.exp (-x') * x ^ (Q + 1) / ((Q + 1).factorial : ℝ) := hpositive
    _ = (-1 : ℝ) ^ (Q + 1 + 1) *
        ((-1 : ℝ) ^ (Q + 2) *
          (Real.exp (-x') * x ^ (Q + 1) / ((Q + 1).factorial : ℝ))) := by
      rw [show Q + 1 + 1 = Q + 2 by omega]
      rw [← mul_assoc, ← pow_add]
      rw [Even.neg_one_pow (show Even ((Q + 2) + (Q + 2)) from ⟨Q + 2, rfl⟩)]
      ring

/-- The Taylor remainder after applying its canonical depth orientation. -/
def expNegOrientedRemainder (m : ℕ) (rate : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m + 1) *
    ((expNegTruncPoly m).eval rate - Real.exp (-rate))

theorem singletonExponentialGammaAnomalyAtom_oriented_re_pos
    (weight rate x : ℝ) (hweight : 0 < weight) (hrate : 0 < rate)
    (N : ℕ) (hN : 0 < N) :
    0 < (-1 : ℝ) ^ (N + 1) *
      (singletonExponentialGammaAnomalyAtom weight rate x N).re := by
  rw [singletonExponentialGammaAnomalyAtom_eq_ofReal]
  simp only [Complex.ofReal_re]
  calc
    0 < (weight * Real.exp (-x * rate)) *
        ((-1 : ℝ) ^ (N + 1) *
          ((expNegTruncPoly N).eval rate - Real.exp (-rate))) :=
      mul_pos (mul_pos hweight (Real.exp_pos _))
        (expNegTruncPoly_sub_exp_oriented_pos hN hrate)
    _ = (-1 : ℝ) ^ (N + 1) *
        (weight * Real.exp (-x * rate) *
          ((expNegTruncPoly N).eval rate - Real.exp (-rate))) := by ring

/-- The scalar atom is not an auxiliary construction: it is exactly the zeroth coordinate of the
finite source-to-Gamma descent anomaly on a singleton exponential packet. -/
theorem finiteExponentialGammaAnomaly_singleton_zero_apply
    (weight rate x : ℝ) (N : ℕ) (hN : 0 < N) :
    finiteExponentialGammaAnomaly
        (fun _ : Fin 1 => (weight : ℂ))
        (fun _ : Fin 1 => (rate : ℂ)) (x : ℂ) N
        (fun _ => 1) ⟨0, hN⟩ =
      singletonExponentialGammaAnomalyAtom weight rate x N := by
  rw [finiteExponentialGammaAnomaly, clockDescentAnomaly_apply]
  simp only [gammaClockTranslation, finiteExponentialJetObservation,
    finiteExponentialSourceShift, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_one, Fin.isValue]
  simp only [Pi.sub_apply, pow_zero, mul_one]
  rw [singletonExponentialGammaAnomalyAtom]
  rw [eval_expNegTruncPoly]
  simp only [gammaClockTranslationCoefficient, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  push_cast
  have hsum :
      (∑ j : Fin N,
        ((j : ℕ).factorial : ℂ)⁻¹ *
          ((weight : ℂ) * (-(rate : ℂ)) ^ (j : ℕ) *
            Complex.exp (-(x : ℂ) * (rate : ℂ)))) =
        ∑ j ∈ Finset.range N,
          (j.factorial : ℂ)⁻¹ *
            ((weight : ℂ) * (-(rate : ℂ)) ^ j *
              Complex.exp (-(x : ℂ) * (rate : ℂ))) := by
    simpa using Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (j.factorial : ℂ)⁻¹ *
        ((weight : ℂ) * (-(rate : ℂ)) ^ j *
          Complex.exp (-(x : ℂ) * (rate : ℂ)))) N
  simp only [one_div]
  rw [hsum]
  change
    (∑ j ∈ Finset.range N,
      ((j.factorial : ℂ)⁻¹ *
        ((weight : ℂ) * (-(rate : ℂ)) ^ j *
          Complex.exp (-(x : ℂ) * (rate : ℂ))))) -
      (weight : ℂ) * Complex.exp (-(rate : ℂ)) *
        Complex.exp (-(x : ℂ) * (rate : ℂ)) = _
  ring_nf
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Every anomaly coordinate is a derivative monomial times the zeroth-coordinate anomaly at the
residual depth.  This is the exact full-jet version of the scalar Taylor-tail identity. -/
theorem finiteExponentialGammaAnomaly_singleton_apply_eq_zeroAtom
    (weight rate x : ℝ) (N : ℕ) (i : Fin N) :
    finiteExponentialGammaAnomaly
        (fun _ : Fin 1 => (weight : ℂ))
        (fun _ : Fin 1 => (rate : ℂ)) (x : ℂ) N
        (fun _ => 1) i =
      (-(rate : ℂ)) ^ (i : ℕ) *
        singletonExponentialGammaAnomalyAtom weight rate x (N - (i : ℕ)) := by
  rw [finiteExponentialGammaAnomaly, clockDescentAnomaly_apply]
  simp only [gammaClockTranslation, finiteExponentialJetObservation,
    finiteExponentialSourceShift, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_one, Fin.isValue, Pi.sub_apply]
  rw [singletonExponentialGammaAnomalyAtom]
  rw [eval_expNegTruncPoly]
  push_cast
  simp only [mul_one]
  have hN : (i : ℕ) + (N - (i : ℕ)) = N := Nat.add_sub_of_le i.isLt.le
  rw [show (∑ j : Fin N,
      gammaClockTranslationCoefficient (i : ℕ) (j : ℕ) *
        ((weight : ℂ) * (-(rate : ℂ)) ^ (j : ℕ) *
          Complex.exp (-(x : ℂ) * (rate : ℂ)))) =
      ∑ j ∈ Finset.range N,
        gammaClockTranslationCoefficient (i : ℕ) j *
          ((weight : ℂ) * (-(rate : ℂ)) ^ j *
            Complex.exp (-(x : ℂ) * (rate : ℂ))) by
        simpa using Fin.sum_univ_eq_sum_range
          (fun j : ℕ => gammaClockTranslationCoefficient (i : ℕ) j *
            ((weight : ℂ) * (-(rate : ℂ)) ^ j *
              Complex.exp (-(x : ℂ) * (rate : ℂ)))) N]
  have hsplit :
      (∑ j ∈ Finset.range N,
        gammaClockTranslationCoefficient (i : ℕ) j *
          ((weight : ℂ) * (-(rate : ℂ)) ^ j *
            Complex.exp (-(x : ℂ) * (rate : ℂ)))) =
      (∑ j ∈ Finset.range (i : ℕ),
        gammaClockTranslationCoefficient (i : ℕ) j *
          ((weight : ℂ) * (-(rate : ℂ)) ^ j *
            Complex.exp (-(x : ℂ) * (rate : ℂ)))) +
      ∑ h ∈ Finset.range (N - (i : ℕ)),
        gammaClockTranslationCoefficient (i : ℕ) ((i : ℕ) + h) *
          ((weight : ℂ) * (-(rate : ℂ)) ^ ((i : ℕ) + h) *
            Complex.exp (-(x : ℂ) * (rate : ℂ))) := by
    calc
      _ = ∑ j ∈ Finset.range ((i : ℕ) + (N - (i : ℕ))),
          gammaClockTranslationCoefficient (i : ℕ) j *
            ((weight : ℂ) * (-(rate : ℂ)) ^ j *
              Complex.exp (-(x : ℂ) * (rate : ℂ))) := by rw [hN]
      _ = _ := Finset.sum_range_add _ _ _
  rw [hsplit]
  have hleft :
      (∑ j ∈ Finset.range (i : ℕ),
        gammaClockTranslationCoefficient (i : ℕ) j *
          ((weight : ℂ) * (-(rate : ℂ)) ^ j *
            Complex.exp (-(x : ℂ) * (rate : ℂ)))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [gammaClockTranslationCoefficient, if_neg]
    · simp
    · exact Nat.not_le.mpr (Finset.mem_range.mp hj)
  rw [hleft, zero_add]
  have hright :
      (∑ h ∈ Finset.range (N - (i : ℕ)),
        gammaClockTranslationCoefficient (i : ℕ) ((i : ℕ) + h) *
          ((weight : ℂ) * (-(rate : ℂ)) ^ ((i : ℕ) + h) *
            Complex.exp (-(x : ℂ) * (rate : ℂ)))) =
        (-(rate : ℂ)) ^ (i : ℕ) *
          ((weight : ℂ) * Complex.exp (-(x : ℂ) * (rate : ℂ)) *
            ∑ h ∈ Finset.range (N - (i : ℕ)),
              ((-1 : ℂ) ^ h / (h.factorial : ℂ)) * (rate : ℂ) ^ h) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [gammaClockTranslationCoefficient, if_pos (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left, pow_add, div_eq_mul_inv]
    ring
  rw [hright]
  ring

/-- After the single depth sign is applied, every coordinate is the positive-rate monomial times
the same oriented Taylor remainder at the residual depth. -/
theorem finiteExponentialGammaAnomaly_singleton_oriented_re_eq
    (weight rate x : ℝ) (N : ℕ) (i : Fin N) :
    (-1 : ℝ) ^ (N + 1) *
      (finiteExponentialGammaAnomaly
        (fun _ : Fin 1 => (weight : ℂ))
        (fun _ : Fin 1 => (rate : ℂ)) (x : ℂ) N
        (fun _ => 1) i).re =
      weight * Real.exp (-x * rate) * rate ^ (i : ℕ) *
        expNegOrientedRemainder (N - (i : ℕ)) rate := by
  rw [finiteExponentialGammaAnomaly_singleton_apply_eq_zeroAtom]
  have hre :
      ((-(rate : ℂ)) ^ (i : ℕ) *
        singletonExponentialGammaAnomalyAtom weight rate x (N - (i : ℕ))).re =
      (-(rate : ℝ)) ^ (i : ℕ) *
        (weight * Real.exp (-x * rate) *
          ((expNegTruncPoly (N - (i : ℕ))).eval rate - Real.exp (-rate))) := by
    rw [singletonExponentialGammaAnomalyAtom_eq_ofReal]
    rw [← Complex.ofReal_neg]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  rw [hre]
  have hsign :
      (-1 : ℝ) ^ (N + 1) * (-(rate : ℝ)) ^ (i : ℕ) =
        rate ^ (i : ℕ) * (-1 : ℝ) ^ ((N - (i : ℕ)) + 1) := by
    rw [neg_pow]
    have hNdecomp : N + 1 = ((N - (i : ℕ)) + 1) + (i : ℕ) := by omega
    rw [hNdecomp, pow_add]
    have hisq : ((-1 : ℝ) ^ (i : ℕ)) * ((-1 : ℝ) ^ (i : ℕ)) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow (Even.add_self (i : ℕ))
    ring_nf at hisq ⊢
    rw [hisq]
    ring
  rw [expNegOrientedRemainder]
  calc
    (-1 : ℝ) ^ (N + 1) *
        ((-(rate : ℝ)) ^ (i : ℕ) *
          (weight * Real.exp (-x * rate) *
            ((expNegTruncPoly (N - (i : ℕ))).eval rate - Real.exp (-rate)))) =
      ((-1 : ℝ) ^ (N + 1) * (-(rate : ℝ)) ^ (i : ℕ)) *
        (weight * Real.exp (-x * rate) *
          ((expNegTruncPoly (N - (i : ℕ))).eval rate - Real.exp (-rate))) := by ring
    _ = (rate ^ (i : ℕ) * (-1 : ℝ) ^ ((N - (i : ℕ)) + 1)) *
        (weight * Real.exp (-x * rate) *
          ((expNegTruncPoly (N - (i : ℕ))).eval rate - Real.exp (-rate))) := by rw [hsign]
    _ = weight * Real.exp (-x * rate) * rate ^ (i : ℕ) *
        ((-1 : ℝ) ^ ((N - (i : ℕ)) + 1) *
          ((expNegTruncPoly (N - (i : ℕ))).eval rate - Real.exp (-rate))) := by ring

/-- Strict all-coordinate orientation of the actual finite descent anomaly. -/
theorem finiteExponentialGammaAnomaly_singleton_oriented_re_pos
    (weight rate x : ℝ) (hweight : 0 < weight) (hrate : 0 < rate)
    (N : ℕ) (i : Fin N) :
    0 < (-1 : ℝ) ^ (N + 1) *
      (finiteExponentialGammaAnomaly
        (fun _ : Fin 1 => (weight : ℂ))
        (fun _ : Fin 1 => (rate : ℂ)) (x : ℂ) N
        (fun _ => 1) i).re := by
  rw [finiteExponentialGammaAnomaly_singleton_oriented_re_eq]
  apply mul_pos
  · exact mul_pos (mul_pos hweight (Real.exp_pos _)) (pow_pos hrate _)
  · exact expNegTruncPoly_sub_exp_oriented_pos
      (Nat.sub_pos_of_lt i.isLt) hrate

/-- Strict orientation of the actual finite descent anomaly, before any reconstruction or limit. -/
theorem finiteExponentialGammaAnomaly_singleton_zero_oriented_re_pos
    (weight rate x : ℝ) (hweight : 0 < weight) (hrate : 0 < rate)
    (N : ℕ) (hN : 0 < N) :
    0 < (-1 : ℝ) ^ (N + 1) *
      (finiteExponentialGammaAnomaly
        (fun _ : Fin 1 => (weight : ℂ))
        (fun _ : Fin 1 => (rate : ℂ)) (x : ℂ) N
        (fun _ => 1) ⟨0, hN⟩).re := by
  rw [finiteExponentialGammaAnomaly_singleton_zero_apply weight rate x N hN]
  exact singletonExponentialGammaAnomalyAtom_oriented_re_pos
    weight rate x hweight hrate N hN

theorem finiteVonMangoldtWeight_eq_ofReal
    {n : ℕ} (hn : n ≠ 0) :
    finiteVonMangoldtWeight n =
      (ArithmeticFunction.vonMangoldt n / n : ℝ) := by
  rw [finiteVonMangoldtWeight, LSeries.term_of_ne_zero hn, Complex.cpow_one]
  push_cast
  rfl

/-- Every resolved prime-power atom of the actual von Mangoldt source lies in the same strict
alternating Gamma-anomaly cone at every positive depth. -/
theorem finiteVonMangoldtGammaAtom_zero_oriented_re_pos
    {n : ℕ} (hn : 1 < n) (hLambda : 0 < ArithmeticFunction.vonMangoldt n)
    (x : ℝ) (N : ℕ) (hN : 0 < N) :
    0 < (-1 : ℝ) ^ (N + 1) *
      (finiteExponentialGammaAnomaly
        (fun _ : Fin 1 => finiteVonMangoldtWeight n)
        (fun _ : Fin 1 => finiteVonMangoldtFrequency n) (x : ℂ) N
        (fun _ => 1) ⟨0, hN⟩).re := by
  rw [finiteVonMangoldtWeight_eq_ofReal (by omega : n ≠ 0)]
  change 0 < (-1 : ℝ) ^ (N + 1) *
    (finiteExponentialGammaAnomaly
      (fun _ : Fin 1 => ((ArithmeticFunction.vonMangoldt n / n : ℝ) : ℂ))
      (fun _ : Fin 1 => ((Real.log n : ℝ) : ℂ)) (x : ℂ) N
      (fun _ => 1) ⟨0, hN⟩).re
  apply finiteExponentialGammaAnomaly_singleton_zero_oriented_re_pos
  · exact div_pos hLambda (by exact_mod_cast (show 0 < n by omega))
  · exact Real.log_pos (by exact_mod_cast hn)

/-- Every jet coordinate of a resolved prime-power atom has the same strict depth orientation. -/
theorem finiteVonMangoldtGammaAtom_oriented_re_pos
    {n : ℕ} (hn : 1 < n) (hLambda : 0 < ArithmeticFunction.vonMangoldt n)
    (x : ℝ) (N : ℕ) (i : Fin N) :
    0 < (-1 : ℝ) ^ (N + 1) *
      (finiteExponentialGammaAnomaly
        (fun _ : Fin 1 => finiteVonMangoldtWeight n)
        (fun _ : Fin 1 => finiteVonMangoldtFrequency n) (x : ℂ) N
        (fun _ => 1) i).re := by
  rw [finiteVonMangoldtWeight_eq_ofReal (by omega : n ≠ 0)]
  change 0 < (-1 : ℝ) ^ (N + 1) *
    (finiteExponentialGammaAnomaly
      (fun _ : Fin 1 => ((ArithmeticFunction.vonMangoldt n / n : ℝ) : ℂ))
      (fun _ : Fin 1 => ((Real.log n : ℝ) : ℂ)) (x : ℂ) N
      (fun _ => 1) i).re
  apply finiteExponentialGammaAnomaly_singleton_oriented_re_pos
  · exact div_pos hLambda (by exact_mod_cast (show 0 < n by omega))
  · exact Real.log_pos (by exact_mod_cast hn)

end

end RHTower
