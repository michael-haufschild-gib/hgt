import GaloisForLFunctions.ThetaCuspSections.PowerCurrentCore
import GaloisForLFunctions.ThetaCuspSections.CoupledCurrentTail
import GaloisForLFunctions.ThetaCuspSections.PowerPolynomialKernel
import GaloisForLFunctions.ThetaCuspSections.EverySectionFromItsVerifiedHeight

/-!
# The fourteenth theta section

The source-paid radius-twelve power core and the general weighted kernel
pay every polynomial of degree at most thirteen. Verified height 67 keeps
the middle region nonnegative; the coupled current bound pays the full tail.
-/

open Complex MeasureTheory Set Filter Topology Matrix Polynomial
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
open _root_.RHTower CriticalCollar QuantitativeCollar LogarithmicCollar
open GaloisForLFunctions.VerifiedHeightRungs

/-- The general power-weighted kernel pays the degree-thirteen exterior. -/
theorem degree_thirteen_power_exterior {P : ℝ[X]} (hdeg : P.degree < 14)
    {b : ℝ} (hb : 66 ≤ |b|) :
    P.eval b ^ 2 ≤ 220000000000 / 12 ^ 26 * |b| ^ 26 * parabolicPowerEnergy 12 4 P := by
  have hh := polynomial_sq_le_parabolicPowerEnergy (R := (12 : ℝ)) (by norm_num) 4
    (n := 13) hdeg (by linarith only [hb] : 4 * (12 : ℝ) ≤ |b|)
  have hE := parabolicPowerEnergy_nonneg (by norm_num : (0 : ℝ) ≤ 12) 4 P
  have hc : legendreLead 21 ≤ 260000 := by norm_num [legendreLead]
  have hc2 := pow_le_pow_left₀ (legendreLead_pos 21).le hc 2
  have hC : (16 / 15 * (16 / 15) ^ 8 * (43 / 2) * legendreLead 21 ^ 2 / 12 : ℝ) ≤
      220000000000 := by nlinarith only [hc2]
  have hm := mul_le_mul_of_nonneg_right hC
    (by positivity : 0 ≤ (|b| / 12) ^ 26 * parabolicPowerEnergy 12 4 P)
  norm_num only [Nat.cast_ofNat] at hh
  calc
    _ ≤ _ := hh
    _ ≤ 220000000000 * (|b| / 12) ^ 26 * parabolicPowerEnergy 12 4 P := by
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

/-- The power core pays the complete degree-thirteen tail with a strict explicit reserve. -/
theorem form14_lower {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    {P : ℝ[X]} (hdeg : P.degree < 14) :
    a / 250 * parabolicPowerEnergy 12 4 P ≤ ∫ b : ℝ, P.eval b ^ 2 * current a b := by
  have habs : |a| ≤ 1 / 2 := by rw [abs_of_pos ha0]; exact ha
  have ha1 : |a| < 1 := habs.trans_lt (by norm_num)
  let E := parabolicPowerEnergy 12 4 P
  have hE0 : 0 ≤ E := parabolicPowerEnergy_nonneg (by norm_num : (0 : ℝ) ≤ 12) 4 P
  let Z : ℝ := 1125000 * a * (220000000000 / 12 ^ 26 * E) *
    (66 ^ 26 * Real.exp (-(132 / 5)))
  let Lo : ℝ → ℝ := fun b => a / 185 * Set.indicator (Icc (-12 : ℝ) 12)
    (fun x => ((1 - x ^ 2 / 144) ^ 4 * P.eval x) ^ 2) b - Z * tailAt 66 b
  have hc : Continuous fun x : ℝ => ((1 - x ^ 2 / 144) ^ 4 * P.eval x) ^ 2 := by fun_prop
  have hind : Integrable (Set.indicator (Icc (-12 : ℝ) 12)
      fun x => ((1 - x ^ 2 / 144) ^ 4 * P.eval x) ^ 2) :=
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
    by_cases hb6 : b ∈ Icc (-12 : ℝ) 12
    · have habs6 : |b| ≤ 12 := abs_le.mpr hb6
      have hcore := current_ge_power_core ha0 ha habs6
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
        have hker := degree_thirteen_power_exterior hdeg hb66'.le
        change P.eval b ^ 2 ≤ 220000000000 / 12 ^ 26 * |b| ^ 26 * E at hker
        have htl := pow_mul_exp_tail_of_le (T := (66 : ℝ)) (m := 26)
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
          (by positivity : 0 ≤ 1125000 * a * (220000000000 / 12 ^ 26 * E))
        dsimp only [Z]
        calc
          _ = 1125000 * a * (220000000000 / 12 ^ 26 * E) *
              (|b| ^ 26 * Real.exp (-(7 / 5 * |b|))) := by ring
          _ ≤ _ := h2
          _ = _ := by ring
  have hint := integral_mono hLo hWint hpoint
  have henergy : (∫ b in (-12 : ℝ)..12,
      ((1 - b ^ 2 / 144) ^ 4 * P.eval b) ^ 2) = E := by
    dsimp only [E, parabolicPowerEnergy]
    apply intervalIntegral.integral_congr
    intro b _
    ring
  have hval : (∫ b, Lo b) = a / 185 * E - Z * (2 * Real.exp (-66)) := by
    dsimp only [Lo]
    rw [integral_sub (hind.const_mul _) ((integrable_tailAt 66).const_mul _),
      integral_const_mul, integral_const_mul, integral_tailAt (by norm_num : (0 : ℝ) ≤ 66),
      integral_indicator measurableSet_Icc, setIntegral_congr_set Ioc_ae_eq_Icc.symm,
      ← intervalIntegral.integral_of_le (by norm_num), henergy]
  rw [hval] at hint
  have htail : Z * (2 * Real.exp (-66)) ≤ a * E / 1000 := by
    have hAE : 0 ≤ a * E := by positivity
    have hm := mul_le_mul_of_nonneg_left tail_twenty_at_sixtySix hAE
    dsimp only [Z]
    calc
      _ = (a * E) * (66 ^ 20 * Real.exp (-(132 / 5)) * Real.exp (-66)) *
          (2 * 1125000 * (220000000000 / 12 ^ 26) * 66 ^ 6) := by ring
      _ ≤ (a * E) * 1.85e-4 * (2 * 1125000 * (220000000000 / 12 ^ 26) * 66 ^ 6) :=
        mul_le_mul_of_nonneg_right hm (by norm_num)
      _ ≤ _ := by
        have hnum : (1.85e-4 : ℝ) * (2 * 1125000 * (220000000000 / 12 ^ 26) * 66 ^ 6) ≤
            1 / 1000 := by norm_num
        nlinarith only [mul_le_mul_of_nonneg_left hnum hAE]
  change a / 250 * E ≤ _
  nlinarith only [hint, htail, mul_nonneg ha0.le hE0]

/-- Every nonzero degree-thirteen polynomial has strictly positive complete current energy. -/
theorem form14_pos {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    {P : ℝ[X]} (hdeg : P.degree < 14) (hP : P ≠ 0) :
    0 < ∫ b : ℝ, P.eval b ^ 2 * current a b := by
  exact (mul_pos (div_pos ha0 (by norm_num)) (parabolicPowerEnergy_pos (by norm_num : (0 : ℝ) < 12) 4 hP)).trans_le
    (form14_lower ha0 ha hdeg)

/-- Every critical aperture has a positive definite signed section of rank fourteen. -/
theorem thetaCuspCenterMixedSignedHankel_fourteen_posDef {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    (thetaCuspCenterMixedSignedHankel a 14).PosDef := by
  classical
  have habs : |a| < 1 := by
    rw [abs_of_pos ha0]
    linarith only [ha]
  apply signed_posDef_of_raw habs 14
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨raw_hermitian a 14, fun v hv => ?_⟩
  rw [star_trivial]
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ[X], P = ∑ i : Fin 14, C (v i) * X ^ (i : ℕ) := ⟨_, rfl⟩
  have hdeg : P.degree < 14 := by
    rw [hPdef]
    exact degree_sum_fin_lt v
  have hcoeff : ∀ j : Fin 14, P.coeff j = v j := by
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
  have hpos := form14_pos ha0 ha hdeg hP
  have heval : ∀ b : ℝ, P.eval b ^ 2 * current a b =
      ∑ i : Fin 14, ∑ j : Fin 14, v i * v j * (b ^ ((i : ℕ) + (j : ℕ)) * current a b) := by
    intro b
    have h1 : P.eval b = ∑ i : Fin 14, v i * b ^ (i : ℕ) := by
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
  have heq : v ⬝ᵥ rawHankel a 14 *ᵥ v = ∑ i : Fin 14, ∫ b : ℝ, ∑ j : Fin 14,
      v i * v j * (b ^ ((i : ℕ) + (j : ℕ)) * current a b) := by
    simp only [dotProduct, mulVec, rawHankel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (raw_integrable a habs _).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    unfold rawMoment
    ring
  rwa [heq]

#print axioms form14_lower
#print axioms thetaCuspCenterMixedSignedHankel_fourteen_posDef

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
