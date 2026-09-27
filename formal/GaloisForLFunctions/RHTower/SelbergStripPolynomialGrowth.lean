import GaloisForLFunctions.RHTower.SelbergCuspGrowthEveryBasePoint
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Polynomial growth of a class member on vertical strips

Every member of the extended Selberg class grows at most polynomially in the height on every
closed vertical strip (`ExtendedSelbergClass.exists_polynomial_bound_strip`):

* to the right of `Re w = 2` the Dirichlet series is bounded;
* on a vertical line far to the left the asymmetric functional equation expresses `F` through a
  sine factor, which grows like `e^{π Σλ_j |Im w|}`, and a product of `2r` Gamma values whose real
  parts are fixed and whose imaginary parts are `±(λ_j Im w + Im μ_j)`; the Gamma decay
  `e^{-π|Im|/2}` of each pair cancels the sine growth exactly, leaving a power of the height;
* in between, Phragmén–Lindelöf in the strip applies to the regularized entire function divided by
  a power of `w - c₀`, whose finite-order growth `e^{B|w|^ρ}` is far below the admissible
  `exp(B' e^{c|Im w|})`.
-/

open Complex Filter Topology Set Asymptotics
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- `Γ` on a vertical line to the right of the imaginary axis, at every height. -/
theorem exists_bound_norm_Gamma_vertical_line (x : ℝ) (hx : 0 < x) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ y : ℝ,
      ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ ≤
        C * (1 + |y|) ^ N * Real.exp (-(Real.pi * |y| / 2)) := by
  obtain ⟨C, N, hC, hb⟩ := exists_sharp_bound_norm_Gamma_strip x x
  refine ⟨max C (Real.Gamma x * Real.exp (Real.pi / 2)), N, le_max_of_le_left hC, fun y => ?_⟩
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  have hexp_pos : 0 < Real.exp (-(Real.pi * |y| / 2)) := Real.exp_pos _
  by_cases hy : 1 ≤ |y|
  · have h := hb _ (by rw [hre]) (by rw [hre]) (by rw [him]; exact hy)
    rw [him] at h
    refine h.trans ?_
    have hpow : |y| ^ N ≤ (1 + |y|) ^ N := pow_le_pow_left₀ (abs_nonneg y) (by linarith) N
    have hmax := le_max_left C (Real.Gamma x * Real.exp (Real.pi / 2))
    have hstep : C * |y| ^ N * Real.exp (-(Real.pi * |y| / 2)) ≤
        max C (Real.Gamma x * Real.exp (Real.pi / 2)) * (1 + |y|) ^ N *
          Real.exp (-(Real.pi * |y| / 2)) := by
      gcongr
    exact hstep
  · push Not at hy
    have h := norm_Gamma_le_Gamma_re (s := (x : ℂ) + (y : ℂ) * I) (by rw [hre]; exact hx)
    rw [hre] at h
    refine h.trans ?_
    have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
    have h1 : Real.Gamma x ≤ Real.Gamma x * Real.exp (Real.pi / 2) *
        Real.exp (-(Real.pi * |y| / 2)) := by
      rw [mul_assoc, ← Real.exp_add]
      have : 0 ≤ Real.pi / 2 + -(Real.pi * |y| / 2) := by
        have := Real.pi_pos
        nlinarith [abs_nonneg y]
      calc Real.Gamma x = Real.Gamma x * 1 := (mul_one _).symm
        _ ≤ Real.Gamma x * Real.exp (Real.pi / 2 + -(Real.pi * |y| / 2)) :=
          mul_le_mul_of_nonneg_left (Real.one_le_exp this) hGx.le
    have hpow : (1 : ℝ) ≤ (1 + |y|) ^ N := one_le_pow₀ (by linarith [abs_nonneg y])
    calc Real.Gamma x ≤ Real.Gamma x * Real.exp (Real.pi / 2) *
          Real.exp (-(Real.pi * |y| / 2)) := h1
      _ ≤ max C (Real.Gamma x * Real.exp (Real.pi / 2)) * (1 + |y|) ^ N *
            Real.exp (-(Real.pi * |y| / 2)) := by
          have hm := le_max_right C (Real.Gamma x * Real.exp (Real.pi / 2))
          have hpos : 0 ≤ Real.Gamma x * Real.exp (Real.pi / 2) := by positivity
          calc Real.Gamma x * Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * |y| / 2))
              = Real.Gamma x * Real.exp (Real.pi / 2) * 1 * Real.exp (-(Real.pi * |y| / 2)) := by
                ring
            _ ≤ max C (Real.Gamma x * Real.exp (Real.pi / 2)) * (1 + |y|) ^ N *
                Real.exp (-(Real.pi * |y| / 2)) := by
                gcongr

/-- A class member is bounded to the right of `Re w = 2`. -/
theorem ExtendedSelbergClass.exists_bound_right (F : ExtendedSelbergClass) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, 2 ≤ w.re → ‖F w‖ ≤ M := by
  have hsumm : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => (F.coeff n : ℂ)) ((2 : ℝ) : ℂ) n‖) :=
    (F.lSeriesSummable ((2 : ℝ) : ℂ) (by simp)).norm
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun n => (F.coeff n : ℂ)) ((2 : ℝ) : ℂ) n‖,
    tsum_nonneg fun n => norm_nonneg _, fun w hw => ?_⟩
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term (fun n => (F.coeff n : ℂ)) w n‖) :=
    hsumm.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_term_le_of_re_le hw n)
  have hval : F w = LSeries (fun n => (F.coeff n : ℂ)) w :=
    (F.lSeries_eq_value w (by linarith)).symm
  rw [hval]
  calc ‖LSeries (fun n => (F.coeff n : ℂ)) w‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n => (F.coeff n : ℂ)) w n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n => (F.coeff n : ℂ)) ((2 : ℝ) : ℂ) n‖ :=
        hnorm.tsum_le_tsum (fun n => norm_term_le_of_re_le hw n) hsumm

/-- The sine factor grows at most like `e^{π Σ λ_j |Im w|}`. -/
theorem SelbergGammaData.norm_asymmetricS_le (G : SelbergGammaData) (w : ℂ) :
    ‖G.asymmetricS w‖ ≤ (2 : ℝ) ^ G.rank * Real.exp (Real.pi * ∑ j, |(G.mu j).im|) *
      Real.exp (Real.pi * (∑ j, G.lambda j) * |w.im|) := by
  unfold SelbergGammaData.asymmetricS
  rw [norm_mul, norm_pow, norm_prod]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.exp_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    Real.exp_sum]
  refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_
  refine (norm_sin_le_exp_abs_im _).trans (Real.exp_le_exp.2 ?_)
  have him : ((Real.pi : ℂ) * ((G.lambda j : ℂ) * w + G.mu j)).im =
      Real.pi * (G.lambda j * w.im + (G.mu j).im) := by
    simp [Complex.mul_im]
  rw [him, abs_mul, abs_of_pos Real.pi_pos]
  have hl := G.lambda_pos j
  have htri : |G.lambda j * w.im + (G.mu j).im| ≤ G.lambda j * |w.im| + |(G.mu j).im| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hl]
  nlinarith [Real.pi_pos]

/-- On a vertical line far to the left, the archimedean factor decays like
`e^{-π Σ λ_j |Im w|}` up to a power of the height. -/
theorem SelbergGammaData.exists_bound_norm_asymmetricH_line (G : SelbergGammaData) {a : ℝ}
    (ha : a < 1) (haμ : ∀ j, G.lambda j * a < 1 - (G.mu j).re) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ w : ℂ, w.re = a →
      ‖G.asymmetricH w‖ ≤ C * (1 + |w.im|) ^ N *
        Real.exp (-(Real.pi * (∑ j, G.lambda j) * |w.im|)) := by
  classical
  -- the two Gamma arguments of each pair have fixed positive real parts
  have hx1 : ∀ j, 0 < G.lambda j * (1 - a) + (G.mu j).re := fun j => by
    have := G.lambda_pos j; have := G.mu_re_nonneg j; nlinarith
  have hx2 : ∀ j, 0 < 1 - G.lambda j * a - (G.mu j).re := fun j => by linarith [haμ j]
  choose C1 N1 hC1 hb1 using fun j => exists_bound_norm_Gamma_vertical_line _ (hx1 j)
  choose C2 N2 hC2 hb2 using fun j => exists_bound_norm_Gamma_vertical_line _ (hx2 j)
  set A : ℝ := 1 + ∑ j, (|(G.mu j).im| + G.lambda j) with hA
  have hA1 : 1 ≤ A := by
    have : 0 ≤ ∑ j, (|(G.mu j).im| + G.lambda j) :=
      Finset.sum_nonneg fun j _ => by have := G.lambda_pos j; positivity
    linarith
  set K0 : ℝ := ‖((2 * Real.pi : ℂ) ^ G.rank)⁻¹‖ * G.Q ^ (1 - 2 * a) with hK0
  refine ⟨K0 * ∏ j, (C1 j * C2 j * A ^ (N1 j + N2 j) * Real.exp (Real.pi * |(G.mu j).im|)),
    ∑ j, (N1 j + N2 j), mul_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg G.Q_pos.le _))
      (Finset.prod_nonneg fun j _ => by have := hC1 j; have := hC2 j; positivity), fun w hw => ?_⟩
  unfold SelbergGammaData.asymmetricH
  rw [norm_mul, norm_mul, norm_mul, norm_prod, norm_prod]
  -- the unimodular phase
  have hphase : ∏ j, ‖(G.lambda j : ℂ) ^ ((2 : ℂ) * I * ((G.mu j).im : ℂ))‖ = 1 := by
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (G.lambda_pos j)]
    simp
  have hQ : ‖(G.Q : ℂ) ^ (1 - 2 * w)‖ = G.Q ^ (1 - 2 * a) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos G.Q_pos]
    simp [hw]
  rw [hphase, mul_one, hQ]
  -- each Gamma pair
  have hpair : ∀ j, ‖Complex.Gamma ((G.lambda j : ℂ) * (1 - w) + star (G.mu j)) *
      Complex.Gamma (1 - (G.lambda j : ℂ) * w - G.mu j)‖ ≤
      C1 j * C2 j * A ^ (N1 j + N2 j) * Real.exp (Real.pi * |(G.mu j).im|) *
        ((1 + |w.im|) ^ (N1 j + N2 j) * Real.exp (-(Real.pi * G.lambda j * |w.im|))) := by
    intro j
    have hl := G.lambda_pos j
    set y : ℝ := G.lambda j * w.im + (G.mu j).im with hy
    have hz1 : (G.lambda j : ℂ) * (1 - w) + star (G.mu j) =
        ((G.lambda j * (1 - a) + (G.mu j).re : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [hw, hy, Complex.mul_re, Complex.mul_im]
      · simp [hw, hy, Complex.mul_re, Complex.mul_im]
        ring
    have hz2 : 1 - (G.lambda j : ℂ) * w - G.mu j =
        ((1 - G.lambda j * a - (G.mu j).re : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [hw, hy, Complex.mul_re, Complex.mul_im]
      · simp [hw, hy, Complex.mul_re, Complex.mul_im]
        ring
    rw [norm_mul, hz1, hz2]
    have h1 := hb1 j (-y)
    have h2 := hb2 j (-y)
    rw [abs_neg] at h1 h2
    have hyle : 1 + |y| ≤ A * (1 + |w.im|) := by
      have hyt : |y| ≤ G.lambda j * |w.im| + |(G.mu j).im| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos hl]
      have hsum_le : |(G.mu j).im| + G.lambda j ≤ ∑ i, (|(G.mu i).im| + G.lambda i) :=
        Finset.single_le_sum (f := fun i => |(G.mu i).im| + G.lambda i)
          (fun i _ => by have := G.lambda_pos i; positivity) (Finset.mem_univ j)
      have hmu : |(G.mu j).im| ≤ A - 1 - G.lambda j := by linarith
      have hlam : G.lambda j ≤ A - 1 - |(G.mu j).im| := by linarith
      nlinarith [abs_nonneg w.im, abs_nonneg (G.mu j).im]
    have hydecay : Real.exp (-(Real.pi * |y| / 2)) * Real.exp (-(Real.pi * |y| / 2)) ≤
        Real.exp (Real.pi * |(G.mu j).im|) * Real.exp (-(Real.pi * G.lambda j * |w.im|)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hlow : G.lambda j * |w.im| - |(G.mu j).im| ≤ |y| := by
        have : |G.lambda j * w.im| ≤ |y| + |(G.mu j).im| := by
          have := abs_sub_abs_le_abs_sub (G.lambda j * w.im + (G.mu j).im) (G.mu j).im
          simp only [add_sub_cancel_right] at this
          rw [hy]
          have h' := abs_add_le (G.lambda j * w.im + (G.mu j).im) (-(G.mu j).im)
          simp only [add_neg_cancel_right, abs_neg] at h'
          exact h'
        rw [abs_mul, abs_of_pos hl] at this
        linarith
      nlinarith [Real.pi_pos]
    have hp1 : (1 + |y|) ^ N1 j ≤ A ^ N1 j * (1 + |w.im|) ^ N1 j := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hyle _
    have hp2 : (1 + |y|) ^ N2 j ≤ A ^ N2 j * (1 + |w.im|) ^ N2 j := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hyle _
    calc ‖Complex.Gamma (((G.lambda j * (1 - a) + (G.mu j).re : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)‖ *
          ‖Complex.Gamma (((1 - G.lambda j * a - (G.mu j).re : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)‖
        ≤ (C1 j * (1 + |y|) ^ N1 j * Real.exp (-(Real.pi * |y| / 2))) *
          (C2 j * (1 + |y|) ^ N2 j * Real.exp (-(Real.pi * |y| / 2))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by have := hC1 j; positivity)
      _ = C1 j * C2 j * ((1 + |y|) ^ N1 j * (1 + |y|) ^ N2 j) *
          (Real.exp (-(Real.pi * |y| / 2)) * Real.exp (-(Real.pi * |y| / 2))) := by ring
      _ ≤ C1 j * C2 j * ((A ^ N1 j * (1 + |w.im|) ^ N1 j) * (A ^ N2 j * (1 + |w.im|) ^ N2 j)) *
          (Real.exp (Real.pi * |(G.mu j).im|) * Real.exp (-(Real.pi * G.lambda j * |w.im|))) := by
          have := hC1 j; have := hC2 j
          gcongr
      _ = C1 j * C2 j * A ^ (N1 j + N2 j) * Real.exp (Real.pi * |(G.mu j).im|) *
          ((1 + |w.im|) ^ (N1 j + N2 j) * Real.exp (-(Real.pi * G.lambda j * |w.im|))) := by
          rw [pow_add, pow_add]; ring
  have hprod := Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j (_ : j ∈ Finset.univ) =>
    hpair j
  rw [Finset.prod_mul_distrib] at hprod
  have hexpprod : ∏ j, ((1 + |w.im|) ^ (N1 j + N2 j) *
      Real.exp (-(Real.pi * G.lambda j * |w.im|))) =
      (1 + |w.im|) ^ (∑ j, (N1 j + N2 j)) *
        Real.exp (-(Real.pi * (∑ j, G.lambda j) * |w.im|)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [hexpprod] at hprod
  calc ‖((2 * Real.pi : ℂ) ^ G.rank)⁻¹‖ * G.Q ^ (1 - 2 * a) *
        ∏ j, ‖Complex.Gamma ((G.lambda j : ℂ) * (1 - w) + star (G.mu j)) *
          Complex.Gamma (1 - (G.lambda j : ℂ) * w - G.mu j)‖
      ≤ K0 * ((∏ j, (C1 j * C2 j * A ^ (N1 j + N2 j) * Real.exp (Real.pi * |(G.mu j).im|))) *
          ((1 + |w.im|) ^ (∑ j, (N1 j + N2 j)) *
            Real.exp (-(Real.pi * (∑ j, G.lambda j) * |w.im|)))) := by
        rw [hK0]
        exact mul_le_mul_of_nonneg_left hprod
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg G.Q_pos.le _))
    _ = _ := by ring

/-- A power of an affine function of `x ≥ 0` is dominated by every exponential `e^{cx}`. -/
theorem exists_rpow_add_le_mul_exp {c ρ D : ℝ} (hc : 0 < c) (hρ : 0 ≤ ρ) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → (D + x) ^ ρ ≤ K * Real.exp (c * x) := by
  set ρ' : ℝ := ρ + 1 with hρ'
  have hρ'pos : 0 < ρ' := by linarith
  refine ⟨(ρ' / c) ^ ρ * Real.exp (c * D), by positivity, fun x hx => ?_⟩
  have hDx : 0 ≤ D + x := by linarith
  have hlin : c / ρ' * (D + x) ≤ Real.exp (c / ρ' * (D + x)) := by
    have := Real.add_one_le_exp (c / ρ' * (D + x))
    linarith
  have hpow : (c / ρ' * (D + x)) ^ ρ ≤ Real.exp (c / ρ' * (D + x)) ^ ρ :=
    Real.rpow_le_rpow (by positivity) hlin hρ
  rw [← Real.exp_mul] at hpow
  have hexp : c / ρ' * (D + x) * ρ ≤ c * (D + x) := by
    have h1 : c / ρ' * ρ ≤ c := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hρ'pos]
      nlinarith
    nlinarith
  have hmul : (c / ρ' * (D + x)) ^ ρ = (c / ρ') ^ ρ * (D + x) ^ ρ :=
    Real.mul_rpow (by positivity) hDx
  have hcρ : 0 < (c / ρ') ^ ρ := Real.rpow_pos_of_pos (by positivity) _
  have hkey : (c / ρ') ^ ρ * (D + x) ^ ρ ≤ Real.exp (c * (D + x)) := by
    rw [← hmul]
    exact hpow.trans (Real.exp_le_exp.2 hexp)
  have hinv : (ρ' / c) ^ ρ * (c / ρ') ^ ρ = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    rw [show ρ' / c * (c / ρ') = 1 by field_simp, Real.one_rpow]
  calc (D + x) ^ ρ = (ρ' / c) ^ ρ * ((c / ρ') ^ ρ * (D + x) ^ ρ) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ (ρ' / c) ^ ρ * Real.exp (c * (D + x)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (ρ' / c) ^ ρ * Real.exp (c * D) * Real.exp (c * x) := by
        rw [mul_add, Real.exp_add]; ring

/-- On a vertical line far to the left a class member grows at most polynomially. -/
theorem ExtendedSelbergClass.exists_bound_left_line (F : ExtendedSelbergClass) {a : ℝ}
    (ha : a < -1) (haμ : ∀ j, F.gammaData.lambda j * a < 1 - (F.gammaData.mu j).re) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ w : ℂ, w.re = a → ‖F w‖ ≤ C * (1 + |w.im|) ^ N := by
  set G := F.gammaData
  obtain ⟨CH, NH, hCH, hH⟩ := G.exists_bound_norm_asymmetricH_line (by linarith) haμ
  obtain ⟨M, hM, hMb⟩ := F.exists_bound_right
  set KS : ℝ := (2 : ℝ) ^ G.rank * Real.exp (Real.pi * ∑ j, |(G.mu j).im|)
  refine ⟨KS * CH * M, NH, by positivity, fun w hw => ?_⟩
  have hFE := F.value_eq_asymmetric_of_farLeft (s := w) (by rw [hw]; linarith)
    (fun j => by rw [hw]; exact haμ j)
  rw [hFE, norm_mul, norm_mul, norm_mul, G.norm_invariantRootNumber, one_mul]
  have hS := G.norm_asymmetricS_le w
  have hHw := hH w hw
  have hR : ‖selbergConjugateReflection F w‖ ≤ M := by
    rw [selbergConjugateReflection, norm_star]
    exact hMb _ (by simp [hw]; linarith)
  have hexp : Real.exp (Real.pi * (∑ j, G.lambda j) * |w.im|) *
      Real.exp (-(Real.pi * (∑ j, G.lambda j) * |w.im|)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc ‖G.asymmetricS w‖ * ‖G.asymmetricH w‖ * ‖selbergConjugateReflection F w‖
      ≤ (KS * Real.exp (Real.pi * (∑ j, G.lambda j) * |w.im|)) *
          (CH * (1 + |w.im|) ^ NH * Real.exp (-(Real.pi * (∑ j, G.lambda j) * |w.im|))) * M :=
        mul_le_mul (mul_le_mul hS hHw (norm_nonneg _) (by positivity)) hR (norm_nonneg _)
          (by positivity)
    _ = KS * CH * M * (1 + |w.im|) ^ NH *
          (Real.exp (Real.pi * (∑ j, G.lambda j) * |w.im|) *
            Real.exp (-(Real.pi * (∑ j, G.lambda j) * |w.im|))) := by ring
    _ = KS * CH * M * (1 + |w.im|) ^ NH := by rw [hexp, mul_one]

/-- **Polynomial growth of a class member on every closed vertical strip.** -/
theorem ExtendedSelbergClass.exists_polynomial_bound_strip (F : ExtendedSelbergClass)
    (σ₁ σ₂ : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → 1 ≤ |w.im| →
      ‖F w‖ ≤ C * |w.im| ^ N := by
  classical
  set G := F.gammaData
  set S : ℝ := ∑ j, (1 + |(G.mu j).re|) / G.lambda j with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun j _ => by have := G.lambda_pos j; positivity
  set a : ℝ := min σ₁ (-2) - S - 1 with ha
  set b : ℝ := max σ₂ 2 with hb
  have haσ : a < σ₁ := by have := min_le_left σ₁ (-2); linarith
  have ha1 : a < -1 := by have := min_le_right σ₁ (-2); linarith
  have hbσ : σ₂ ≤ b := le_max_left _ _
  have hb2 : 2 ≤ b := le_max_right _ _
  have hab : a < b := by linarith
  have haμ : ∀ j, G.lambda j * a < 1 - (G.mu j).re := by
    intro j
    have hl := G.lambda_pos j
    have hterm : (1 + |(G.mu j).re|) / G.lambda j ≤ S :=
      Finset.single_le_sum (f := fun i => (1 + |(G.mu i).re|) / G.lambda i)
        (fun i _ => by have := G.lambda_pos i; positivity) (Finset.mem_univ j)
    have hale : a ≤ -((1 + |(G.mu j).re|) / G.lambda j) - 1 := by
      have := min_le_right σ₁ (-2); linarith
    have h1 : G.lambda j * a ≤ -(1 + |(G.mu j).re|) - G.lambda j := by
      have h2 := mul_le_mul_of_nonneg_left hale hl.le
      have h3 : G.lambda j * (-((1 + |(G.mu j).re|) / G.lambda j) - 1) =
          -(1 + |(G.mu j).re|) - G.lambda j := by
        field_simp
      linarith
    have := le_abs_self (G.mu j).re
    linarith
  obtain ⟨CL, NL, hCL, hL⟩ := F.exists_bound_left_line ha1 haμ
  obtain ⟨M, hM, hMb⟩ := F.exists_bound_right
  set m : ℕ := F.continuation.poleOrder
  set R := F.continuation.regularized
  obtain ⟨A, B, ρ, hA, hB, hρ, hgrowth⟩ := R.growth
  set c₀ : ℝ := a - 1 with hc₀
  set P : ℕ := NL + m with hP
  set h : ℂ → ℂ := fun w => R w / (w - (c₀ : ℂ)) ^ P with hh
  have hFR : ∀ w : ℂ, w ≠ 1 → R w = F w * (w - 1) ^ m := by
    intro w hw1
    change R w = F.continuation.regularized w / (w - 1) ^ F.continuation.poleOrder * (w - 1) ^ m
    rw [div_mul_cancel₀]
    exact pow_ne_zero _ (sub_ne_zero.2 hw1)
  -- distances to `c₀` in the strip
  have hdist1 : ∀ w : ℂ, a ≤ w.re → 1 ≤ ‖w - (c₀ : ℂ)‖ := by
    intro w hw
    calc (1 : ℝ) ≤ (w - (c₀ : ℂ)).re := by simp [hc₀]; linarith
      _ ≤ |(w - (c₀ : ℂ)).re| := le_abs_self _
      _ ≤ ‖w - (c₀ : ℂ)‖ := Complex.abs_re_le_norm _
  have hdist_im : ∀ w : ℂ, |w.im| ≤ ‖w - (c₀ : ℂ)‖ := by
    intro w
    have := Complex.abs_im_le_norm (w - (c₀ : ℂ))
    simpa using this
  set D1 : ℝ := 1 + |c₀ - 1| with hD1
  have hw1 : ∀ w : ℂ, a ≤ w.re → ‖w - 1‖ ≤ D1 * ‖w - (c₀ : ℂ)‖ := by
    intro w hw
    have h1 := hdist1 w hw
    calc ‖w - 1‖ = ‖(w - (c₀ : ℂ)) + ((c₀ - 1 : ℝ) : ℂ)‖ := by push_cast; ring_nf
      _ ≤ ‖w - (c₀ : ℂ)‖ + ‖((c₀ - 1 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖w - (c₀ : ℂ)‖ + |c₀ - 1| := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖w - (c₀ : ℂ)‖ + |c₀ - 1| * ‖w - (c₀ : ℂ)‖ := by nlinarith [abs_nonneg (c₀ - 1)]
      _ = D1 * ‖w - (c₀ : ℂ)‖ := by rw [hD1]; ring
  have hD1pos : 1 ≤ D1 := by rw [hD1]; linarith [abs_nonneg (c₀ - 1)]
  -- edge bounds
  set CE : ℝ := max (CL * 2 ^ NL * D1 ^ m) (M * D1 ^ m) with hCE
  have hhnorm : ∀ w : ℂ, a ≤ w.re → w ≠ 1 →
      ‖h w‖ = ‖F w‖ * ‖w - 1‖ ^ m / ‖w - (c₀ : ℂ)‖ ^ P := by
    intro w hw hne
    simp only [hh]
    rw [hFR w hne, norm_div, norm_mul, norm_pow, norm_pow]
  have hleft : ∀ w : ℂ, w.re = a → ‖h w‖ ≤ CE := by
    intro w hw
    have hne : w ≠ 1 := by intro h1; rw [h1] at hw; simp at hw; linarith
    have hwa : a ≤ w.re := le_of_eq hw.symm
    rw [hhnorm w hwa hne]
    have hn := hdist1 w hwa
    have hnpos : 0 < ‖w - (c₀ : ℂ)‖ := by linarith
    rw [div_le_iff₀ (by positivity)]
    have hF := hL w hw
    have h1im : 1 + |w.im| ≤ 2 * ‖w - (c₀ : ℂ)‖ := by linarith [hdist_im w]
    have hp1 : (1 + |w.im|) ^ NL ≤ (2 * ‖w - (c₀ : ℂ)‖) ^ NL :=
      pow_le_pow_left₀ (by positivity) h1im _
    have hp2 : ‖w - 1‖ ^ m ≤ (D1 * ‖w - (c₀ : ℂ)‖) ^ m :=
      pow_le_pow_left₀ (norm_nonneg _) (hw1 w hwa) _
    calc ‖F w‖ * ‖w - 1‖ ^ m ≤ (CL * (1 + |w.im|) ^ NL) * (D1 * ‖w - (c₀ : ℂ)‖) ^ m :=
          mul_le_mul hF hp2 (by positivity) (by positivity)
      _ ≤ (CL * (2 * ‖w - (c₀ : ℂ)‖) ^ NL) * (D1 * ‖w - (c₀ : ℂ)‖) ^ m := by gcongr
      _ = CL * 2 ^ NL * D1 ^ m * ‖w - (c₀ : ℂ)‖ ^ P := by
          rw [hP, pow_add, mul_pow, mul_pow]; ring
      _ ≤ CE * ‖w - (c₀ : ℂ)‖ ^ P := by
          gcongr
          exact le_max_left _ _
  have hright : ∀ w : ℂ, w.re = b → ‖h w‖ ≤ CE := by
    intro w hw
    have hne : w ≠ 1 := by intro h1; rw [h1] at hw; simp at hw; linarith
    have hwa : a ≤ w.re := by rw [hw]; linarith
    rw [hhnorm w hwa hne]
    have hn := hdist1 w hwa
    rw [div_le_iff₀ (by positivity)]
    have hF := hMb w (by rw [hw]; exact hb2)
    have hp2 : ‖w - 1‖ ^ m ≤ (D1 * ‖w - (c₀ : ℂ)‖) ^ m :=
      pow_le_pow_left₀ (norm_nonneg _) (hw1 w hwa) _
    have hmono : ‖w - (c₀ : ℂ)‖ ^ m ≤ ‖w - (c₀ : ℂ)‖ ^ P :=
      pow_le_pow_right₀ hn (by omega)
    calc ‖F w‖ * ‖w - 1‖ ^ m ≤ M * (D1 * ‖w - (c₀ : ℂ)‖) ^ m :=
          mul_le_mul hF hp2 (by positivity) hM
      _ = M * D1 ^ m * ‖w - (c₀ : ℂ)‖ ^ m := by rw [mul_pow]; ring
      _ ≤ M * D1 ^ m * ‖w - (c₀ : ℂ)‖ ^ P := by gcongr
      _ ≤ CE * ‖w - (c₀ : ℂ)‖ ^ P := by
          gcongr
          exact le_max_right _ _
  -- differentiability on the closed strip
  have hdiff : DiffContOnCl ℂ h (Complex.re ⁻¹' Ioo a b) := by
    refine DifferentiableOn.diffContOnCl fun z hz => ?_
    have hzre : a ≤ z.re := by
      have hsub : closure (Complex.re ⁻¹' Ioo a b) ⊆ Complex.re ⁻¹' Icc a b :=
        closure_minimal (fun w hw => ⟨le_of_lt hw.1, le_of_lt hw.2⟩)
          (isClosed_Icc.preimage Complex.continuous_re)
      exact (hsub hz).1
    have hne : z - (c₀ : ℂ) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp [hc₀] at this
      linarith
    have hR : DifferentiableAt ℂ R z := (R.analytic z (Set.mem_univ z)).differentiableAt
    exact (hR.div ((differentiableAt_id.sub (differentiableAt_const _)).pow P)
      (pow_ne_zero _ hne)).differentiableWithinAt
  -- finite-order growth is admissible
  set c : ℝ := Real.pi / (2 * (b - a)) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; have := Real.pi_pos; apply div_pos this; linarith
  have hclt : c < Real.pi / (b - a) := by
    rw [hcdef]
    have hba : 0 < b - a := by linarith
    rw [div_lt_div_iff₀ (by positivity) hba]
    nlinarith [Real.pi_pos]
  set D : ℝ := |a| + |b| with hD
  obtain ⟨K, hK, hKb⟩ := exists_rpow_add_le_mul_exp (D := D) hcpos hρ (by positivity)
  have hgrow : h =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b)]
      fun z => Real.exp ((B * K) * Real.exp (c * |z.im|)) := by
    refine IsBigO.of_bound A ?_
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    have hzre : a < z.re ∧ z.re < b := hz
    have hn := hdist1 z hzre.1.le
    have hRz := hgrowth z
    have hnorm_z : ‖z‖ ≤ D + |z.im| := by
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ D + |z.im| := by
          have : |z.re| ≤ |a| + |b| := by
            rcases le_or_gt 0 z.re with h0 | h0
            · rw [abs_of_nonneg h0]; have := le_abs_self b; linarith [abs_nonneg a]
            · rw [abs_of_neg h0]; have := neg_abs_le a; linarith [abs_nonneg b]
          linarith
    have hpow : ‖z‖ ^ ρ ≤ K * Real.exp (c * |z.im|) :=
      (Real.rpow_le_rpow (norm_nonneg _) hnorm_z hρ).trans (hKb |z.im| (abs_nonneg _))
    have hden : 1 ≤ ‖(z - (c₀ : ℂ)) ^ P‖ := by rw [norm_pow]; exact one_le_pow₀ hn
    have hh1 : ‖h z‖ ≤ ‖R z‖ := by
      simp only [hh]
      rw [norm_div]
      exact div_le_self (norm_nonneg _) hden
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc ‖h z‖ ≤ ‖R z‖ := hh1
      _ ≤ A * Real.exp (B * ‖z‖ ^ ρ) := hRz
      _ ≤ A * Real.exp ((B * K) * Real.exp (c * |z.im|)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hA.le
          calc B * ‖z‖ ^ ρ ≤ B * (K * Real.exp (c * |z.im|)) :=
                mul_le_mul_of_nonneg_left hpow hB.le
            _ = (B * K) * Real.exp (c * |z.im|) := by ring
  have hPL : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖h w‖ ≤ CE := fun w hwa hwb =>
    PhragmenLindelof.vertical_strip hdiff ⟨c, hclt, B * K, hgrow⟩ hleft hright hwa hwb
  -- back to `F`
  have hCEnn : 0 ≤ CE := le_max_of_le_right (mul_nonneg hM (by positivity))
  refine ⟨CE * (b - c₀ + 1) ^ P, P, mul_nonneg hCEnn (pow_nonneg (by linarith) _),
    fun w hw1 hw2 hwim => ?_⟩
  have hwa : a ≤ w.re := by linarith
  have hwb : w.re ≤ b := by linarith
  have hne : w ≠ 1 := by
    intro h1; rw [h1] at hwim; norm_num at hwim
  have hn := hdist1 w hwa
  have hhw := hPL w hwa hwb
  rw [hhnorm w hwa hne, div_le_iff₀ (by positivity)] at hhw
  have hw1norm : 1 ≤ ‖w - 1‖ := by
    have := Complex.abs_im_le_norm (w - 1)
    simp at this
    linarith
  have hw1pow : 1 ≤ ‖w - 1‖ ^ m := one_le_pow₀ hw1norm
  have hdistub : ‖w - (c₀ : ℂ)‖ ≤ (b - c₀ + 1) * |w.im| := by
    calc ‖w - (c₀ : ℂ)‖ ≤ |(w - (c₀ : ℂ)).re| + |(w - (c₀ : ℂ)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |w.re - c₀| + |w.im| := by simp
      _ ≤ (b - c₀) + |w.im| := by
          rw [abs_of_nonneg (by linarith)]
          linarith
      _ ≤ (b - c₀ + 1) * |w.im| := by nlinarith
  have hFle : ‖F w‖ ≤ ‖F w‖ * ‖w - 1‖ ^ m := le_mul_of_one_le_right (norm_nonneg _) hw1pow
  calc ‖F w‖ ≤ ‖F w‖ * ‖w - 1‖ ^ m := hFle
    _ ≤ CE * ‖w - (c₀ : ℂ)‖ ^ P := hhw
    _ ≤ CE * ((b - c₀ + 1) * |w.im|) ^ P := by
        gcongr
    _ = CE * (b - c₀ + 1) ^ P * |w.im| ^ P := by rw [mul_pow]; ring

end

end RHTower
