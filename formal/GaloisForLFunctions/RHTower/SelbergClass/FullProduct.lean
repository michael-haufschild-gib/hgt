import GaloisForLFunctions.RHTower.SelbergClass.Full
import GaloisForLFunctions.RHTower.SelbergClass.EntireFiniteOrderAlgebra
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# Ordinary products in the full Selberg carrier

The ordinary product of two represented Dirichlet series has convolution coefficients, additive
Euler-log coefficients, multiplied continuation data, and concatenated gamma data.  The only
coefficient-growth input is the unconditional divisor bound.
-/

open scoped BigOperators
open Complex Filter Set

namespace RHTower

noncomputable section

/-- Gamma data for the ordinary product of two Selberg-class presentations. -/
def selbergGammaDataMul (F G : SelbergGammaData) : SelbergGammaData where
  Q := F.Q * G.Q
  Q_pos := mul_pos F.Q_pos G.Q_pos
  rank := F.rank + G.rank
  lambda := Fin.addCases F.lambda G.lambda
  lambda_pos := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa only [Fin.addCases_left] using F.lambda_pos i
    · intro i
      simpa only [Fin.addCases_right] using G.lambda_pos i
  mu := Fin.addCases F.mu G.mu
  mu_re_nonneg := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa only [Fin.addCases_left] using F.mu_re_nonneg i
    · intro i
      simpa only [Fin.addCases_right] using G.mu_re_nonneg i
  rootNumber := F.rootNumber * G.rootNumber
  rootNumber_norm := by
    rw [norm_mul, F.rootNumber_norm, G.rootNumber_norm]
    norm_num

/-- The gamma factor of concatenated data is the product of the two gamma factors. -/
theorem selbergGammaDataMul_gammaFactor (F G : SelbergGammaData) (s : ℂ) :
    (selbergGammaDataMul F G).gammaFactor s = F.gammaFactor s * G.gammaFactor s := by
  simp only [selbergGammaDataMul, SelbergGammaData.gammaFactor, Pi.mul_apply,
    Finset.prod_apply]
  change (↑(F.Q * G.Q) : ℂ) ^ s *
      ∏ j : Fin (F.rank + G.rank),
        Complex.Gamma (((Fin.addCases F.lambda G.lambda j : ℝ) : ℂ) * s +
          Fin.addCases F.mu G.mu j) =
      ((F.Q : ℂ) ^ s * ∏ j : Fin F.rank,
        Complex.Gamma ((F.lambda j : ℂ) * s + F.mu j)) *
      ((G.Q : ℂ) ^ s * ∏ j : Fin G.rank,
        Complex.Gamma ((G.lambda j : ℂ) * s + G.mu j))
  rw [Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg F.Q_pos.le G.Q_pos.le]
  ring

/-- Analytic-continuation data for an ordinary product. -/
def selbergAnalyticContinuationMul
    (F G : SelbergAnalyticContinuation) : SelbergAnalyticContinuation where
  poleOrder := F.poleOrder + G.poleOrder
  regularized := F.regularized.mul G.regularized

/-- The represented value of product continuation data is the product of represented values. -/
theorem selbergAnalyticContinuationMul_value
    (F G : SelbergAnalyticContinuation) (s : ℂ) :
    (selbergAnalyticContinuationMul F G).value s = F.value s * G.value s := by
  simp only [selbergAnalyticContinuationMul, SelbergAnalyticContinuation.value,
    EntireFiniteOrder.mul_apply, pow_add]
  rw [div_mul_div_comm]

/-- Completed values of product data multiply pointwise. -/
theorem selbergCompletedValue_mul
    (F G : ExtendedSelbergClass) (s : ℂ) :
    selbergCompletedValue (selbergGammaDataMul F.gammaData G.gammaData)
      (selbergAnalyticContinuationMul F.continuation G.continuation) s =
      selbergCompletedValue F.gammaData F.continuation s *
        selbergCompletedValue G.gammaData G.continuation s := by
  simp only [selbergCompletedValue]
  rw [selbergGammaDataMul_gammaFactor, selbergAnalyticContinuationMul_value]
  ring

private theorem card_divisorsAntidiagonal_eq_card_divisors (n : ℕ) :
    n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones,
    ← Nat.sum_divisorsAntidiagonal (fun _ _ => (1 : ℕ))]

private theorem ramanujan_mul (F G : SelbergClass) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
      ‖(F.coeff * G.coeff) n‖ ≤ C * (n : ℝ) ^ ε := by
  have hδ : 0 < ε / 2 := by linarith
  obtain ⟨CF, hCF, hF⟩ := F.ramanujan (ε / 2) hδ
  obtain ⟨CG, hCG, hG⟩ := G.ramanujan (ε / 2) hδ
  obtain ⟨CD, hCD, hD⟩ := card_divisors_le_const_mul_rpow hδ
  refine ⟨CF * CG * CD, mul_pos (mul_pos hCF hCG) hCD, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [ArithmeticFunction.mul_apply]
  calc
    ‖∑ x ∈ n.divisorsAntidiagonal, F.coeff x.1 * G.coeff x.2‖
        ≤ ∑ x ∈ n.divisorsAntidiagonal, ‖F.coeff x.1 * G.coeff x.2‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _x ∈ n.divisorsAntidiagonal,
          CF * CG * (n : ℝ) ^ (ε / 2) := by
      apply Finset.sum_le_sum
      intro x hx
      have hx1 : x.1 ≠ 0 := by
        exact (Nat.pos_of_mem_divisors
          (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).ne'
      have hx2 : x.2 ≠ 0 := by
        exact (Nat.pos_of_mem_divisors
          (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).ne'
      have hxy : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have hxyR : (x.1 : ℝ) * (x.2 : ℝ) = (n : ℝ) := by
        exact_mod_cast hxy
      rw [norm_mul]
      calc
        ‖F.coeff x.1‖ * ‖G.coeff x.2‖
            ≤ (CF * (x.1 : ℝ) ^ (ε / 2)) *
                (CG * (x.2 : ℝ) ^ (ε / 2)) :=
              mul_le_mul (hF x.1 hx1) (hG x.2 hx2) (norm_nonneg _) (by positivity)
        _ = CF * CG * ((x.1 : ℝ) * (x.2 : ℝ)) ^ (ε / 2) := by
              rw [Real.mul_rpow (by positivity) (by positivity)]
              ring
        _ = CF * CG * (n : ℝ) ^ (ε / 2) := by rw [hxyR]
    _ = (n.divisorsAntidiagonal.card : ℝ) *
          (CF * CG * (n : ℝ) ^ (ε / 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (n.divisors.card : ℝ) *
          (CF * CG * (n : ℝ) ^ (ε / 2)) := by
      rw [card_divisorsAntidiagonal_eq_card_divisors]
    _ ≤ (CD * (n : ℝ) ^ (ε / 2)) *
          (CF * CG * (n : ℝ) ^ (ε / 2)) := by
      exact mul_le_mul_of_nonneg_right (hD n hn1) (by positivity)
    _ = CF * CG * CD * ((n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2)) := by
      ring
    _ = CF * CG * CD * (n : ℝ) ^ ε := by
      rw [← Real.rpow_add hnR]
      have hsum : ε / 2 + ε / 2 = ε := by ring
      rw [hsum]

private theorem eulerLogCoeff_add_primePower (F G : SelbergClass) {n : ℕ}
    (h : (F.eulerLogCoeff + G.eulerLogCoeff) n ≠ 0) :
    ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p ^ k := by
  rw [ArithmeticFunction.add_apply] at h
  by_cases hF : F.eulerLogCoeff n = 0
  · have hG : G.eulerLogCoeff n ≠ 0 := by
      intro hG
      exact h (by rw [hF, hG, add_zero])
    exact G.eulerLogCoeff_primePower hG
  · exact F.eulerLogCoeff_primePower hF

private theorem eulerLogBound_add (F G : SelbergClass) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
      ‖(F.eulerLogCoeff + G.eulerLogCoeff) n‖ ≤
        C * (n : ℝ) ^ max F.eulerTheta G.eulerTheta := by
  obtain ⟨CF, hCF, hF⟩ := F.eulerLogBound
  obtain ⟨CG, hCG, hG⟩ := G.eulerLogBound
  refine ⟨CF + CG, add_pos hCF hCG, ?_⟩
  intro n hn
  have hn1 : 1 ≤ (n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  rw [ArithmeticFunction.add_apply]
  calc
    ‖F.eulerLogCoeff n + G.eulerLogCoeff n‖
        ≤ ‖F.eulerLogCoeff n‖ + ‖G.eulerLogCoeff n‖ := norm_add_le _ _
    _ ≤ CF * (n : ℝ) ^ F.eulerTheta + CG * (n : ℝ) ^ G.eulerTheta :=
      add_le_add (hF n hn) (hG n hn)
    _ ≤ CF * (n : ℝ) ^ max F.eulerTheta G.eulerTheta +
          CG * (n : ℝ) ^ max F.eulerTheta G.eulerTheta := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _)) hCF.le
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right _ _)) hCG.le
    _ = (CF + CG) * (n : ℝ) ^ max F.eulerTheta G.eulerTheta := by ring

/-- The ordinary product of two full Selberg-class carriers. -/
noncomputable def SelbergClass.mul (F G : SelbergClass) : SelbergClass where
  coeff := F.coeff * G.coeff
  coeff_ne_zero := by
    intro h
    have h1 := congrArg (fun a : ArithmeticFunction ℂ => a 1) h
    rw [ArithmeticFunction.mul_apply_one, F.coeff_one, G.coeff_one] at h1
    norm_num at h1
  lSeriesSummable := by
    intro s hs
    exact ArithmeticFunction.LSeriesSummable_mul
      (F.lSeriesSummable s hs) (G.lSeriesSummable s hs)
  continuation := selbergAnalyticContinuationMul F.continuation G.continuation
  lSeries_eq_value := by
    intro s hs
    calc
      LSeries (fun n => (F.coeff * G.coeff) n) s =
          LSeries (fun n => F.coeff n) s * LSeries (fun n => G.coeff n) s :=
        ArithmeticFunction.LSeries_mul' (F.lSeriesSummable s hs) (G.lSeriesSummable s hs)
      _ = F.continuation.value s * G.continuation.value s := by
        rw [F.lSeries_eq_value s hs, G.lSeries_eq_value s hs]
      _ = (selbergAnalyticContinuationMul F.continuation G.continuation).value s :=
        (selbergAnalyticContinuationMul_value F.continuation G.continuation s).symm
  gammaData := selbergGammaDataMul F.gammaData G.gammaData
  functionalEquation := by
    filter_upwards [F.functionalEquation, G.functionalEquation] with s hF hG
    simp only [selbergConjugateReflection] at hF hG ⊢
    simp only [selbergCompletedValue_mul]
    rw [hF, hG, star_mul]
    simp only [selbergGammaDataMul]
    ring
  coeff_one := by
    rw [ArithmeticFunction.mul_apply_one, F.coeff_one, G.coeff_one]
    norm_num
  ramanujan := ramanujan_mul F G
  eulerLogCoeff := F.eulerLogCoeff + G.eulerLogCoeff
  eulerLogCoeff_primePower := eulerLogCoeff_add_primePower F G
  eulerTheta := max F.eulerTheta G.eulerTheta
  eulerTheta_lt_half := max_lt F.eulerTheta_lt_half G.eulerTheta_lt_half
  eulerLogBound := eulerLogBound_add F G
  eulerLogSummable := by
    intro s hs
    exact (F.eulerLogSummable s hs).add (G.eulerLogSummable s hs)
  eulerProduct := by
    intro s hs
    calc
      Complex.exp (LSeries (F.eulerLogCoeff + G.eulerLogCoeff) s) =
          Complex.exp (LSeries F.eulerLogCoeff s + LSeries G.eulerLogCoeff s) := by
            rw [LSeries_add (F.eulerLogSummable s hs) (G.eulerLogSummable s hs)]
      _ = Complex.exp (LSeries F.eulerLogCoeff s) *
          Complex.exp (LSeries G.eulerLogCoeff s) := Complex.exp_add _ _
      _ = F.continuation.value s * G.continuation.value s := by
        rw [F.eulerProduct s hs, G.eulerProduct s hs]
      _ = (selbergAnalyticContinuationMul F.continuation G.continuation).value s :=
        (selbergAnalyticContinuationMul_value F.continuation G.continuation s).symm

@[simp]
theorem SelbergClass.mul_coeff (F G : SelbergClass) :
    (F.mul G).coeff = F.coeff * G.coeff :=
  rfl

@[simp]
theorem SelbergClass.mul_eulerLogCoeff (F G : SelbergClass) :
    (F.mul G).eulerLogCoeff = F.eulerLogCoeff + G.eulerLogCoeff :=
  rfl

end

end RHTower
