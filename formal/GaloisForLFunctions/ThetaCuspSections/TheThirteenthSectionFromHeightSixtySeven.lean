import GaloisForLFunctions.ThetaCuspSections.PoleBudgetCurvature
import GaloisForLFunctions.ThetaCuspSections.CoupledCurrentTail
import GaloisForLFunctions.ThetaCuspSections.ParabolicPolynomialKernel
import GaloisForLFunctions.ThetaCuspSections.EverySectionFromItsVerifiedHeight

/-!
# The thirteenth theta section

The wider parabolic core and coupled current tail pay every polynomial of
degree at most twelve. The degree-uniform kernel retains the complete
weighted energy, and verified height 67 pays the intervening region.
-/

open Complex MeasureTheory Set Filter Topology Matrix Polynomial
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
open _root_.RHTower CriticalCollar QuantitativeCollar LogarithmicCollar
open GaloisForLFunctions.VerifiedHeightRungs

/-- The general weighted kernel pays the degree-twelve exterior. -/
theorem degree_twelve_parabolic_exterior {P : ℝ[X]} (hdeg : P.degree < 13)
    {b : ℝ} (hb : 66 ≤ |b|) :
    P.eval b ^ 2 ≤ 14600000 / (13 / 2) ^ 24 * |b| ^ 24 * parabolicEnergyAt (13 / 2) P := by
  have hh := polynomial_sq_le_parabolicEnergy (R := (13 / 2 : ℝ)) (by norm_num)
    (n := 12) hdeg (by linarith only [hb] : 10 * (13 / 2 : ℝ) ≤ |b|)
  have hE := parabolicEnergyAt_nonneg (by norm_num : (0 : ℝ) ≤ 13 / 2) P
  have hc : legendreLead 14 ≤ 2450 := by norm_num [legendreLead]
  have hc2 := pow_le_pow_left₀ (legendreLead_pos 14).le hc 2
  have hC : (16 / 15 * (100 / 99) ^ 2 * (29 / 2) * legendreLead 14 ^ 2 / (13 / 2) : ℝ) ≤
      14600000 := by nlinarith only [hc2]
  have hm := mul_le_mul_of_nonneg_right hC
    (by positivity : 0 ≤ (|b| / (13 / 2)) ^ 24 * parabolicEnergyAt (13 / 2) P)
  norm_num only [Nat.cast_ofNat] at hh
  calc
    _ ≤ _ := hh
    _ ≤ 14600000 * (|b| / (13 / 2)) ^ 24 * parabolicEnergyAt (13 / 2) P := by
      nlinarith only [hm]
    _ = _ := by rw [div_pow]; ring

private theorem tail_twenty_at_sixtySix :
    (66 : ℝ) ^ 20 * Real.exp (-(132 / 5)) * Real.exp (-66) ≤ 1.85e-4 := by
  have h : Real.exp (-(132 / 5)) * Real.exp (-66) = Real.exp (-92) * Real.exp (-(2 / 5)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  rw [mul_assoc, h]
  have he : Real.exp (-92) = (Real.exp 1 ^ 92)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    norm_num
  have h92 : Real.exp (-92) ≤ ((2.7182818283 : ℝ) ^ 92)⁻¹ := by
    rw [he]
    exact inv_anti₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 92)
  have h25 : Real.exp (-(2 / 5)) ≤ 0.6757 := by
    have h1 := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 5)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num at h1 ⊢
    linarith only [h1]
  calc (66 : ℝ) ^ 20 * (Real.exp (-92) * Real.exp (-(2 / 5)))
      ≤ 66 ^ 20 * (((2.7182818283 : ℝ) ^ 92)⁻¹ * 0.6757) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul h92 h25 (Real.exp_pos _).le (by positivity))
          (by positivity)
    _ ≤ _ := by norm_num

/-- The parabolic core pays the complete degree-twelve tail with a strict explicit reserve. -/
theorem form13_lower {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    {P : ℝ[X]} (hdeg : P.degree < 13) :
    a / 40000 * parabolicEnergyAt (13 / 2) P ≤ ∫ b : ℝ, P.eval b ^ 2 * current a b := by
  have habs : |a| ≤ 1 / 2 := by rw [abs_of_pos ha0]; exact ha
  have ha1 : |a| < 1 := habs.trans_lt (by norm_num)
  let E := parabolicEnergyAt (13 / 2) P
  have hE0 : 0 ≤ E := parabolicEnergyAt_nonneg (by norm_num : (0 : ℝ) ≤ 13 / 2) P
  let Z : ℝ := 1125000 * a * (14600000 / (13 / 2) ^ 24 * E) *
    (66 ^ 24 * Real.exp (-(132 / 5)))
  let Lo : ℝ → ℝ := fun b => a / 275 * Set.indicator (Icc (-(13 / 2) : ℝ) (13 / 2))
    (fun x => ((1 - 4 * x ^ 2 / 169) * P.eval x) ^ 2) b - Z * tailAt 66 b
  have hc : Continuous fun x : ℝ => ((1 - 4 * x ^ 2 / 169) * P.eval x) ^ 2 := by fun_prop
  have hind : Integrable (Set.indicator (Icc (-(13 / 2) : ℝ) (13 / 2))
      fun x => ((1 - 4 * x ^ 2 / 169) * P.eval x) ^ 2) :=
    hc.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hLo : Integrable Lo := (hind.const_mul _).sub ((integrable_tailAt 66).const_mul _)
  have hWint : Integrable fun b : ℝ => P.eval b ^ 2 * current a b := by
    have he (b : ℝ) : P.eval b ^ 2 * current a b =
        ∑ i ∈ Finset.range ((P ^ 2).natDegree + 1),
          (P ^ 2).coeff i * (b ^ i * current a b) := by
      rw [← eval_pow, eval_eq_sum_range, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [he]
    exact integrable_finsetSum _ fun i _ => (raw_integrable a ha1 i).const_mul _
  have hpoint (b : ℝ) : Lo b ≤ P.eval b ^ 2 * current a b := by
    have hW : 0 ≤ P.eval b ^ 2 := sq_nonneg _
    by_cases hb6 : b ∈ Icc (-(13 / 2) : ℝ) (13 / 2)
    · have habs6 : |b| ≤ 13 / 2 := abs_le.mpr hb6
      have hcore := current_ge_wide_parabolic ha0 ha habs6
      have hT0 : tailAt 66 b = 0 := by
        unfold tailAt
        rw [if_neg (by linarith only [habs6])]
      dsimp only [Lo]
      rw [Set.indicator_of_mem hb6, hT0, mul_zero, sub_zero]
      have hh := mul_le_mul_of_nonneg_left hcore hW
      nlinarith only [hh]
    · dsimp only [Lo]
      rw [Set.indicator_of_notMem hb6, mul_zero, zero_sub]
      by_cases hb66 : |b| ≤ 66
      · have hcur := current_nonneg_of_rhVerifiedThrough (T := 66) ha0 (by
          norm_num
          exact HadamardBudget.rhVerifiedThrough_sixtySeven) hb66
        have hT0 : tailAt 66 b = 0 := by
          unfold tailAt
          rw [if_neg (not_lt.mpr hb66)]
        rw [hT0, mul_zero, neg_zero]
        exact mul_nonneg hW hcur
      · have hb66' : 66 < |b| := not_le.mp hb66
        have hcur := abs_current_le_coupled habs b
        rw [abs_of_pos ha0] at hcur
        have hker := degree_twelve_parabolic_exterior hdeg hb66'.le
        change P.eval b ^ 2 ≤ 14600000 / (13 / 2) ^ 24 * |b| ^ 24 * E at hker
        have htl := pow_mul_exp_tail_of_le (T := (66 : ℝ)) (m := 24)
          (by norm_num) (by norm_num) hb66'.le
        rw [show -(2 / 5 * (66 : ℝ)) = -(132 / 5) by ring] at htl
        have hTv : tailAt 66 b = Real.exp (-|b|) := by
          unfold tailAt
          rw [if_pos hb66']
        rw [hTv]
        have hlow : -(P.eval b ^ 2 * (1125000 * a * Real.exp (-(7 / 5 * |b|)))) ≤
            P.eval b ^ 2 * current a b := by
          have hh := mul_le_mul_of_nonneg_left (abs_le.mp hcur).1 hW
          nlinarith only [hh]
        refine le_trans ?_ hlow
        rw [neg_le_neg_iff]
        have h1 := mul_le_mul_of_nonneg_right hker
          (by positivity : 0 ≤ 1125000 * a * Real.exp (-(7 / 5 * |b|)))
        refine h1.trans ?_
        have h2 := mul_le_mul_of_nonneg_left htl
          (by positivity : 0 ≤ 1125000 * a * (14600000 / (13 / 2) ^ 24 * E))
        dsimp only [Z]
        calc
          _ = 1125000 * a * (14600000 / (13 / 2) ^ 24 * E) *
              (|b| ^ 24 * Real.exp (-(7 / 5 * |b|))) := by ring
          _ ≤ _ := h2
          _ = _ := by ring
  have hint := integral_mono hLo hWint hpoint
  have henergy : (∫ b in (-(13 / 2) : ℝ)..(13 / 2),
      ((1 - 4 * b ^ 2 / 169) * P.eval b) ^ 2) = E := by
    dsimp only [E, parabolicEnergyAt]
    apply intervalIntegral.integral_congr
    intro b _
    congr 2
    ring
  have hval : (∫ b, Lo b) = a / 275 * E - Z * (2 * Real.exp (-66)) := by
    dsimp only [Lo]
    rw [integral_sub (hind.const_mul _) ((integrable_tailAt 66).const_mul _),
      integral_const_mul, integral_const_mul, integral_tailAt (by norm_num : (0 : ℝ) ≤ 66),
      integral_indicator measurableSet_Icc, setIntegral_congr_set Ioc_ae_eq_Icc.symm,
      ← intervalIntegral.integral_of_le (by norm_num), henergy]
  rw [hval] at hint
  have htail : Z * (2 * Real.exp (-66)) ≤ a * E / 277 := by
    have hAE : 0 ≤ a * E := by positivity
    have hm := mul_le_mul_of_nonneg_left tail_twenty_at_sixtySix hAE
    dsimp only [Z]
    calc
      _ = (a * E) * (66 ^ 20 * Real.exp (-(132 / 5)) * Real.exp (-66)) *
          (2 * 1125000 * (14600000 / (13 / 2) ^ 24) * 66 ^ 4) := by ring
      _ ≤ (a * E) * 1.85e-4 * (2 * 1125000 * (14600000 / (13 / 2) ^ 24) * 66 ^ 4) :=
        mul_le_mul_of_nonneg_right hm (by norm_num)
      _ ≤ _ := by
        have hnum : (1.85e-4 : ℝ) * (2 * 1125000 * (14600000 / (13 / 2) ^ 24) * 66 ^ 4) ≤
            1 / 277 := by norm_num
        nlinarith only [mul_le_mul_of_nonneg_left hnum hAE]
  change a / 40000 * E ≤ _
  nlinarith only [hint, htail, mul_nonneg ha0.le hE0]

/-- Every nonzero degree-twelve polynomial has strictly positive complete current energy. -/
theorem form13_pos {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    {P : ℝ[X]} (hdeg : P.degree < 13) (hP : P ≠ 0) :
    0 < ∫ b : ℝ, P.eval b ^ 2 * current a b := by
  exact (mul_pos (div_pos ha0 (by norm_num)) (parabolicEnergyAt_pos (by norm_num : (0 : ℝ) < 13 / 2) hP)).trans_le
    (form13_lower ha0 ha hdeg)

/-- Every critical aperture has a positive definite signed section of rank thirteen. -/
theorem thetaCuspCenterMixedSignedHankel_thirteen_posDef {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    (thetaCuspCenterMixedSignedHankel a 13).PosDef := by
  classical
  have habs : |a| < 1 := by
    rw [abs_of_pos ha0]
    linarith only [ha]
  apply signed_posDef_of_raw habs 13
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨raw_hermitian a 13, fun v hv => ?_⟩
  rw [star_trivial]
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ[X], P = ∑ i : Fin 13, C (v i) * X ^ (i : ℕ) := ⟨_, rfl⟩
  have hdeg : P.degree < 13 := by
    rw [hPdef]
    exact degree_sum_fin_lt v
  have hcoeff : ∀ j : Fin 13, P.coeff j = v j := by
    intro j
    rw [hPdef, finsetSum_coeff, Finset.sum_eq_single j]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro i _ hij
      rw [coeff_C_mul_X_pow, if_neg]
      intro h
      exact hij (Fin.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hP : P ≠ 0 := by
    intro h0
    apply hv
    funext j
    rw [← hcoeff j, h0, coeff_zero]
    rfl
  have hpos := form13_pos ha0 ha hdeg hP
  have heval : ∀ b : ℝ, P.eval b ^ 2 * current a b =
      ∑ i : Fin 13, ∑ j : Fin 13, v i * v j * (b ^ ((i : ℕ) + (j : ℕ)) * current a b) := by
    intro b
    have h1 : P.eval b = ∑ i : Fin 13, v i * b ^ (i : ℕ) := by
      rw [hPdef, eval_finsetSum]
      simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [h1, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  simp_rw [heval] at hpos
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (raw_integrable a habs _).const_mul _] at hpos
  have heq : v ⬝ᵥ rawHankel a 13 *ᵥ v = ∑ i : Fin 13, ∫ b : ℝ, ∑ j : Fin 13,
      v i * v j * (b ^ ((i : ℕ) + (j : ℕ)) * current a b) := by
    simp only [dotProduct, mulVec, rawHankel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (raw_integrable a habs _).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    unfold rawMoment
    ring
  rwa [heq]

#print axioms form13_lower
#print axioms thetaCuspCenterMixedSignedHankel_thirteen_posDef

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
