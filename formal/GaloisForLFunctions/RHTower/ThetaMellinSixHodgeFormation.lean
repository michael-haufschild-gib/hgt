import GaloisForLFunctions.RHTower.ThetaMellinSixIntegralNuclearFormation
import GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvaturePrimeLift
import GaloisForLFunctions.RHTower.PrimeHodgeHistorySurvivalFredholmColligation
import GaloisForLFunctions.RHTower.EulerPrimitivePolarizedHodgeBetaTransgression

/-!
# The theta Mellin-six holonomy forms the Hodge response and the prime-mixed defect

Write `G_θ` for the pole-stripped Mellin response of the first theta atom (`= Γ_ℝ` on `Re s > 1`).

* **(TM6H.7)** The odd-Hodge Beta response is a theta holonomy of length three:
  `h(a) = -(1/2π) Γ_ℝ(2a+1)/Γ_ℝ(2a+4)` for `a > -1/2`, and `= -(1/2π) G_θ(2a+1)/G_θ(2a+4)`
  for `a > 0`.
* **(TM6H.8)** At the two forced grades the middle response cancels:
  `h(n+1) h(n+5/2) = (1/4π²) G_θ(2n+3)/G_θ(2n+9)`.
* **(TM6H.5), (TM6H.9)–(TM6H.10)** `H_0 = 1`; the theta flux diagonal `Φ_θ = diag(H_n - H_{n+1})`
  is the history marginal `Φ`, and `𝖳_θ = Φ_θ ⊗ A_d` is the prime-mixed integral–nuclear defect
  `𝖳_d`: positive, Schatten-one, trace and trace norm one, prime-mixed, with every history tail
  trace equal to `H_n`.
* **(TM6H.11)** `∑_n (H_n - H_{n+1}) = Tr Φ_θ = Tr 𝖳_θ = -ind C = 1`.
-/

open Complex MeasureTheory Filter
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-! ## (TM6H.7)–(TM6H.8) -/

theorem gammaReal_ofReal (x : ℝ) :
    Complex.Gammaℝ (x : ℂ) = ((Real.pi ^ (-x / 2) * Real.Gamma (x / 2) : ℝ) : ℂ) := by
  rw [Complex.Gammaℝ_def, Complex.ofReal_mul, ← Complex.Gamma_ofReal,
    Complex.ofReal_cpow Real.pi_pos.le]
  push_cast
  ring_nf

/-- **(TM6H.7), Gamma form.**  `h(a) = -(1/2π) Γ_ℝ(2a+1)/Γ_ℝ(2a+4)` for `a > -1/2`. -/
theorem eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaReal {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    (eulerPrimitiveBoundaryHodgeBetaColumn a : ℂ) =
      -(1 / (2 * (Real.pi : ℂ))) *
        (Complex.Gammaℝ ((2 * a + 1 : ℝ) : ℂ) / Complex.Gammaℝ ((2 * a + 4 : ℝ) : ℂ)) := by
  rw [eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio ha, gammaReal_ofReal, gammaReal_ofReal]
  have hpi := Real.pi_pos
  have hG1 := Real.Gamma_pos_of_pos (show (0 : ℝ) < (2 * a + 1) / 2 by linarith)
  have hG4 := Real.Gamma_pos_of_pos (show (0 : ℝ) < (2 * a + 4) / 2 by linarith)
  have h1 : (2 * a + 1) / 2 = a + 1 / 2 := by ring
  have h4 : (2 * a + 4) / 2 = a + 2 := by ring
  have hpow : Real.pi ^ (-(2 * a + 1) / 2) / Real.pi ^ (-(2 * a + 4) / 2) =
      Real.pi * Real.sqrt Real.pi := by
    rw [← Real.rpow_sub hpi, show -(2 * a + 1) / 2 - -(2 * a + 4) / 2 = 1 + 1 / 2 by ring,
      Real.rpow_add hpi, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hhalf : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [← Complex.ofReal_div, h1, h4]
  rw [show Real.pi ^ (-(2 * a + 1) / 2) * Real.Gamma (a + 1 / 2) /
      (Real.pi ^ (-(2 * a + 4) / 2) * Real.Gamma (a + 2)) =
        (Real.pi ^ (-(2 * a + 1) / 2) / Real.pi ^ (-(2 * a + 4) / 2)) *
          (Real.Gamma (a + 1 / 2) / Real.Gamma (a + 2)) by
      rw [h1] at hG1
      rw [h4] at hG4
      field_simp, hpow, hhalf]
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpi.ne'
  have hs : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hpi.le
  push_cast
  field_simp

/-- **(TM6H.7), theta form.**  For `a > 0`, `h(a) = -(1/2π) G_θ(2a+1)/G_θ(2a+4)`. -/
theorem eulerPrimitiveBoundaryHodgeBetaColumn_eq_thetaResponse {a : ℝ} (ha : 0 < a) :
    (eulerPrimitiveBoundaryHodgeBetaColumn a : ℂ) =
      -(1 / (2 * (Real.pi : ℂ))) *
        (thetaCuspPoleStrippedMellinResponse ((2 * a + 1 : ℝ) : ℂ) /
          thetaCuspPoleStrippedMellinResponse ((2 * a + 4 : ℝ) : ℂ)) := by
  rw [eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaReal (by linarith),
    thetaCuspPoleStrippedMellinResponse_eq_GammaR (by simp; linarith),
    thetaCuspPoleStrippedMellinResponse_eq_GammaR (by simp; linarith)]

/-- **(TM6H.8).**  `h(n+1) h(n+5/2) = (1/4π²) G_θ(2n+3)/G_θ(2n+9)`. -/
theorem hodgeBetaColumn_product_eq_thetaHolonomy (n : ℕ) :
    (eulerPrimitiveBoundaryHodgeBetaColumn (n + 1) *
        eulerPrimitiveBoundaryHodgeBetaColumn (n + 5 / 2) : ℂ) =
      1 / (4 * (Real.pi : ℂ) ^ 2) *
        (thetaCuspPoleStrippedMellinResponse ((2 * n + 3 : ℕ) : ℂ) /
          thetaCuspPoleStrippedMellinResponse ((2 * n + 9 : ℕ) : ℂ)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  rw [eulerPrimitiveBoundaryHodgeBetaColumn_eq_thetaResponse (by linarith),
    eulerPrimitiveBoundaryHodgeBetaColumn_eq_thetaResponse (by linarith)]
  have e1 : ((2 * ((n : ℝ) + 1) + 1 : ℝ) : ℂ) = 2 * (n : ℂ) + 3 := by push_cast; ring
  have e2 : ((2 * ((n : ℝ) + 1) + 4 : ℝ) : ℂ) = 2 * (n : ℂ) + 6 := by push_cast; ring
  have e3 : ((2 * ((n : ℝ) + 5 / 2) + 1 : ℝ) : ℂ) = 2 * (n : ℂ) + 6 := by push_cast; ring
  have e4 : ((2 * ((n : ℝ) + 5 / 2) + 4 : ℝ) : ℂ) = 2 * (n : ℂ) + 9 := by push_cast; ring
  rw [e1, e2, e3, e4]
  have hre : 1 < (2 * (n : ℂ) + 6).re := by simp; linarith
  have h6 : thetaCuspPoleStrippedMellinResponse (2 * (n : ℂ) + 6) ≠ 0 := by
    rw [thetaCuspPoleStrippedMellinResponse_eq_GammaR hre]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
  field_simp
  ring

/-! ## (TM6H.5), (TM6H.9)–(TM6H.11) -/

theorem thetaCuspMellinSixHolonomy_zero : thetaCuspMellinSixHolonomy 0 = 1 := by
  rw [thetaCuspMellinSixHolonomy_eq_primeHodgeHistory_m, PrimeHodgeHistory.m_zero,
    Complex.ofReal_one]

theorem zero_lt_thetaCuspMellinSixFlux (n : ℕ) : 0 < thetaCuspMellinSixFlux n := by
  rw [thetaCuspMellinSixFlux_eq_primeHodgeHistory_w]
  exact PrimeHodgeHistory.w_pos n

theorem summable_thetaCuspMellinSixFlux_sq :
    Summable fun n => thetaCuspMellinSixFlux n ^ 2 := by
  simp_rw [thetaCuspMellinSixFlux_eq_primeHodgeHistory_w]
  exact PrimeHodgeHistory.summable_w.of_nonneg_of_le (fun n => sq_nonneg _) fun n => by
    have h0 := (PrimeHodgeHistory.w_pos n).le
    have h1 := PrimeHodgeHistory.w_le_two_thirds n
    nlinarith

/-- **(TM6H.9).**  `𝖳_θ = Φ_θ ⊗ A_d` with the theta-formed history flux. -/
def thetaFormedDefectOperator {d : ℝ} (hd : 0 < d) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  historyStokesOperator thetaCuspMellinSixFlux (fun n => (zero_lt_thetaCuspMellinSixFlux n).le)
    summable_thetaCuspMellinSixFlux_sq hd

theorem historyStokesKernel_thetaFlux (d : ℝ) :
    historyStokesKernel thetaCuspMellinSixFlux d = primeHodgeHistoryDefectKernel d := by
  funext ab
  simp only [historyStokesKernel, primeHodgeHistoryDefectKernel,
    thetaCuspMellinSixFlux_eq_primeHodgeHistory_w]

/-- **(TM6H.10).**  `𝖳_θ = 𝖳_d`. -/
theorem thetaFormedDefectOperator_eq {d : ℝ} (hd : 0 < d) :
    thetaFormedDefectOperator hd = primeHodgeHistoryDefectOperator hd := by
  rw [thetaFormedDefectOperator, historyStokesOperator, primeHodgeHistoryDefectOperator]
  congr 1
  exact historyStokesKernel_thetaFlux d

/-- **(TM6H.10), transfer.**  `𝖳_θ` is positive, Schatten-one with trace and trace norm one,
prime-mixed on every history slice, and its history-tail traces are the theta holonomies `H_n`. -/
theorem thetaFormedDefectOperator_properties {d : ℝ} (hd : 0 < d) :
    (thetaFormedDefectOperator hd).IsPositive ∧
      MemSchattenClass 1 (thetaFormedDefectOperator hd) ∧
      ContinuousLinearMap.opTrace (thetaFormedDefectOperator hd) = 1 ∧
      traceNorm PrimeHodgeHistoryHilbert (thetaFormedDefectOperator hd) = 1 ∧
      (∀ n p q, historyStokesKernel thetaCuspMellinSixFlux d ((n, p), (n, q)) ≠ 0) ∧
      (∀ n, ((∑' kp : PrimeHodgeHistoryIndex,
        primeHodgeHistoryDiagonalWeight d (kp.1 + n, kp.2) : ℝ) : ℂ) =
          thetaCuspMellinSixHolonomy n) := by
  rw [thetaFormedDefectOperator_eq hd]
  obtain ⟨h1, h2, h3, h4, h5⟩ := primeHodgeHistoryIntegralNuclearDefect hd
  refine ⟨h1, h2, h3, h4, fun n p q => ?_, fun n => ?_⟩
  · rw [historyStokesKernel_thetaFlux]
    exact h5 n p q
  · rw [tsum_primeHodgeHistoryDiagonalWeight_shift hd, thetaCuspMellinSixHolonomy_eq_primeHodgeHistory_m]

/-- **(TM6H.11).**  The normalized theta Mellin-six boundary loss is the integral nuclear trace and
the negative Fredholm index of the survival shift: all equal one. -/
theorem thetaMellinSix_boundaryLoss_conservation :
    (∑' n, thetaCuspMellinSixFlux n) = 1 ∧
      ContinuousLinearMap.opTrace (thetaFormedDefectOperator (d := 1) one_pos) = 1 ∧
      ((-primeHodgeHistorySurvivalShiftIndex : ℤ) : ℂ) =
        ContinuousLinearMap.opTrace (thetaFormedDefectOperator (d := 1) one_pos) ∧
      ((∑' n, thetaCuspMellinSixFlux n : ℝ) : ℂ) =
        ContinuousLinearMap.opTrace primeHodgeHistoryFluxOperator := by
  have hsum : (∑' n, thetaCuspMellinSixFlux n) = 1 := by
    simp_rw [thetaCuspMellinSixFlux_eq_primeHodgeHistory_w]
    exact PrimeHodgeHistory.tsum_w
  have htr := (thetaFormedDefectOperator_properties (d := 1) one_pos).2.2.1
  refine ⟨hsum, htr, ?_, ?_⟩
  · rw [htr, primeHodgeHistorySurvivalShiftIndex_eq_neg_one]
    norm_num
  · rw [hsum, opTrace_primeHodgeHistoryFluxOperator, Complex.ofReal_one]

end

end RHTower
