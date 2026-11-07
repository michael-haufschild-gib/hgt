import GaloisForLFunctions.ThetaCuspSections.ParabolicCurrentCore
import GaloisForLFunctions.ThetaCuspSections.LegendrePolynomialKernel
import GaloisForLFunctions.ThetaCuspSections.EverySectionFromItsVerifiedHeight
import GaloisForLFunctions.ThetaCuspSections.TheSharpCurrentTail

/-!
# The twelfth theta section

A squared parabolic core on `[-6,6]` retains enough energy to pay the complete
exterior at degree eleven. The general Legendre kernel controls the polynomial
multiplied by `1-b²/36`; verified height 67 pays the intervening region.
-/

open Complex MeasureTheory Set Filter Topology Matrix Polynomial
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
open _root_.RHTower CriticalCollar QuantitativeCollar LogarithmicCollar
open GaloisForLFunctions.VerifiedHeightRungs

/-- The polynomial energy retained by the squared parabolic current core. -/
def parabolicEnergy (P : ℝ[X]) : ℝ :=
  ∫ b in (-6 : ℝ)..6, ((1 - b ^ 2 / 36) * P.eval b) ^ 2

theorem parabolicEnergy_nonneg (P : ℝ[X]) : 0 ≤ parabolicEnergy P :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _

/-- The general Legendre kernel pays the full degree-eleven exterior. -/
theorem degree_eleven_parabolic_exterior {P : ℝ[X]} (hdeg : P.degree < 12)
    {b : ℝ} (hb : 66 ≤ |b|) :
    P.eval b ^ 2 ≤ 5300000 / 6 ^ 22 * |b| ^ 22 * parabolicEnergy P := by
  by_cases hP : P = 0
  · subst P
    simp [parabolicEnergy]
  have hPN : P.natDegree < 12 := (natDegree_lt_iff_degree_lt hP).mpr hdeg
  let Q : ℝ[X] := (1 - X ^ 2) * P.comp (C 6 * X)
  have hQdeg : Q.degree < 14 := by
    have hW : (1 - X ^ 2 : ℝ[X]).natDegree ≤ 2 :=
      (natDegree_sub_le _ _).trans (by norm_num)
    have hlin : (C (6 : ℝ) * X).natDegree = 1 := by simp
    have hQN : Q.natDegree ≤ 13 := by
      have hh := natDegree_mul_le (p := (1 - X ^ 2 : ℝ[X])) (q := P.comp (C 6 * X))
      rw [natDegree_comp, hlin, mul_one] at hh
      dsimp only [Q]
      omega
    exact (degree_le_natDegree (p := Q)).trans_lt
      (by exact_mod_cast (show Q.natDegree < 14 by omega))
  have hQeval (x : ℝ) : Q.eval x = (1 - x ^ 2) * P.eval (6 * x) := by
    simp only [Q, eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_comp, eval_C]
  have hcov := intervalIntegral.mul_integral_comp_mul_add
    (f := fun b : ℝ => ((1 - b ^ 2 / 36) * P.eval b) ^ 2)
    (a := -1) (b := 1) (c := 6) (d := 0)
  have hscaled (x : ℝ) : ((1 - (6 * x + 0) ^ 2 / 36) * P.eval (6 * x + 0)) ^ 2 =
      Q.eval x ^ 2 := by
    rw [hQeval, add_zero]
    congr 2
    ring
  simp_rw [hscaled] at hcov
  norm_num only [mul_neg, mul_one, add_zero] at hcov
  have hI : (∫ x in (-1 : ℝ)..1, Q.eval x ^ 2) = parabolicEnergy P / 6 := by
    change 6 * (∫ x in (-1 : ℝ)..1, Q.eval x ^ 2) = parabolicEnergy P at hcov
    linarith only [hcov]
  have hval : Q.eval (b / 6) = (1 - b ^ 2 / 36) * P.eval b := by
    rw [hQeval, show 6 * (b / 6) = b by ring]
    congr 2
    ring
  have hpoint := polynomial_sq_le_legendreKernel 14 Q hQdeg (b / 6)
  rw [hval, mul_pow, hI] at hpoint
  let x : ℝ := |b| / 6
  have hx : 11 ≤ x := by dsimp only [x]; linarith only [hb]
  have hx0 : 0 < x := by linarith only [hx]
  have habs : |b / 6| = x := by simp only [abs_div, abs_ofNat, x]
  have hx2 : x ^ 2 = b ^ 2 / 36 := by
    dsimp only [x]
    rw [div_pow, sq_abs]
    norm_num
  have hc : legendreLead 13 ≤ 1300 := by norm_num [legendreLead]
  have hc2 := pow_le_pow_left₀ (legendreLead_pos 13).le hc 2
  have hk := legendreKernel_le_abs (x := b / 6) (by rw [habs]; linarith only [hx]) 13
  rw [habs] at hk
  have hk' : legendreKernel 14 (b / 6) ≤ (16 / 15 * (27 / 2) * 1300 ^ 2 : ℝ) * x ^ 26 := by
    norm_num only [Nat.cast_ofNat] at hk
    have hm := mul_le_mul_of_nonneg_right hc2
      (by positivity : 0 ≤ (16 / 15 * (27 / 2) : ℝ) * x ^ 26)
    nlinarith only [hk, hm]
  have hx16 : 16 ≤ x ^ 2 := by nlinarith only [hx]
  have hw : 15 / 16 * x ^ 2 ≤ x ^ 2 - 1 := by linarith only [hx16]
  have hws := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 15 / 16 * x ^ 2) hw 2
  have hw' : (15 / 16 : ℝ) ^ 2 * x ^ 4 ≤ (1 - b ^ 2 / 36) ^ 2 := by
    rw [← hx2]
    nlinarith only [hws]
  have hE := parabolicEnergy_nonneg P
  have hpay : ((15 / 16 : ℝ) ^ 2 * x ^ 4) * P.eval b ^ 2 ≤
      ((15 / 16 : ℝ) ^ 2 * x ^ 4) * (5300000 * x ^ 22 * parabolicEnergy P) := by
    calc
      _ ≤ (1 - b ^ 2 / 36) ^ 2 * P.eval b ^ 2 :=
        mul_le_mul_of_nonneg_right hw' (sq_nonneg _)
      _ ≤ legendreKernel 14 (b / 6) * (parabolicEnergy P / 6) := hpoint
      _ ≤ (16 / 15 * (27 / 2) * 1300 ^ 2 : ℝ) * x ^ 26 * (parabolicEnergy P / 6) :=
        mul_le_mul_of_nonneg_right hk' (by positivity)
      _ ≤ _ := by
        have hnum : (16 / 15 * (27 / 2) * 1300 ^ 2 : ℝ) / 6 ≤
            (15 / 16) ^ 2 * 5300000 := by norm_num
        have hm := mul_le_mul_of_nonneg_right hnum
          (by positivity : 0 ≤ x ^ 26 * parabolicEnergy P)
        have hp : x ^ 26 = x ^ 4 * x ^ 22 := by rw [← pow_add]
        rw [hp] at hm ⊢
        nlinarith only [hm]
  have hres : P.eval b ^ 2 ≤ 5300000 * x ^ 22 * parabolicEnergy P :=
    (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (15 / 16 : ℝ) ^ 2 * x ^ 4)).mp hpay
  exact hres.trans_eq (by dsimp only [x]; rw [div_pow]; ring)

/-- Nonzero polynomials of degree at most eleven have strictly positive parabolic energy. -/
theorem parabolicEnergy_pos {P : ℝ[X]} (hdeg : P.degree < 12) (hP : P ≠ 0) :
    0 < parabolicEnergy P := by
  refine lt_of_le_of_ne (parabolicEnergy_nonneg P) fun h0 => hP ?_
  refine eq_zero_of_infinite_isRoot P ((Set.Ici_infinite (66 : ℝ)).mono fun b hb => ?_)
  have habs : 66 ≤ |b| := le_trans hb (le_abs_self b)
  have hh := degree_eleven_parabolic_exterior hdeg habs
  rw [← h0, mul_zero] at hh
  exact pow_eq_zero_iff (by norm_num) |>.mp (le_antisymm hh (sq_nonneg _))

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

/-- The parabolic core pays the complete degree-eleven tail with a strict explicit reserve. -/
theorem form12_lower {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    {P : ℝ[X]} (hdeg : P.degree < 12) :
    a / 1200 * parabolicEnergy P ≤ ∫ b : ℝ, P.eval b ^ 2 * current a b := by
  have habs : |a| ≤ 1 / 2 := by rw [abs_of_pos ha0]; exact ha
  have ha1 : |a| < 1 := habs.trans_lt (by norm_num)
  let E := parabolicEnergy P
  have hE0 : 0 ≤ E := parabolicEnergy_nonneg P
  let Z : ℝ := 36000000 * a * (5300000 / 6 ^ 22 * E) *
    (66 ^ 22 * Real.exp (-(132 / 5)))
  let Lo : ℝ → ℝ := fun b => a / 300 * Set.indicator (Icc (-6 : ℝ) 6)
    (fun x => ((1 - x ^ 2 / 36) * P.eval x) ^ 2) b - Z * tailAt 66 b
  have hc : Continuous fun x : ℝ => ((1 - x ^ 2 / 36) * P.eval x) ^ 2 := by fun_prop
  have hind : Integrable (Set.indicator (Icc (-6 : ℝ) 6)
      fun x => ((1 - x ^ 2 / 36) * P.eval x) ^ 2) :=
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
    by_cases hb6 : b ∈ Icc (-6 : ℝ) 6
    · have habs6 : |b| ≤ 6 := abs_le.mpr hb6
      have hcore := current_ge_parabolic ha0 ha habs6
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
        have hcur := abs_current_le_sharp habs b
        rw [abs_of_pos ha0] at hcur
        have hker := degree_eleven_parabolic_exterior hdeg hb66'.le
        change P.eval b ^ 2 ≤ 5300000 / 6 ^ 22 * |b| ^ 22 * E at hker
        have htl := pow_mul_exp_tail_of_le (T := (66 : ℝ)) (m := 22)
          (by norm_num) (by norm_num) hb66'.le
        rw [show -(2 / 5 * (66 : ℝ)) = -(132 / 5) by ring] at htl
        have hTv : tailAt 66 b = Real.exp (-|b|) := by
          unfold tailAt
          rw [if_pos hb66']
        rw [hTv]
        have hlow : -(P.eval b ^ 2 * (36000000 * a * Real.exp (-(7 / 5 * |b|)))) ≤
            P.eval b ^ 2 * current a b := by
          have hh := mul_le_mul_of_nonneg_left (abs_le.mp hcur).1 hW
          nlinarith only [hh]
        refine le_trans ?_ hlow
        rw [neg_le_neg_iff]
        have h1 := mul_le_mul_of_nonneg_right hker
          (by positivity : 0 ≤ 36000000 * a * Real.exp (-(7 / 5 * |b|)))
        refine h1.trans ?_
        have h2 := mul_le_mul_of_nonneg_left htl
          (by positivity : 0 ≤ 36000000 * a * (5300000 / 6 ^ 22 * E))
        dsimp only [Z]
        calc
          _ = 36000000 * a * (5300000 / 6 ^ 22 * E) *
              (|b| ^ 22 * Real.exp (-(7 / 5 * |b|))) := by ring
          _ ≤ _ := h2
          _ = _ := by ring
  have hint := integral_mono hLo hWint hpoint
  have hval : (∫ b, Lo b) = a / 300 * E - Z * (2 * Real.exp (-66)) := by
    dsimp only [Lo]
    rw [integral_sub (hind.const_mul _) ((integrable_tailAt 66).const_mul _),
      integral_const_mul, integral_const_mul, integral_tailAt (by norm_num : (0 : ℝ) ≤ 66),
      integral_indicator measurableSet_Icc, setIntegral_congr_set Ioc_ae_eq_Icc.symm,
      ← intervalIntegral.integral_of_le (by norm_num)]
    rfl
  rw [hval] at hint
  have htail : Z * (2 * Real.exp (-66)) ≤ a * E / 400 := by
    have hAE : 0 ≤ a * E := by positivity
    have hm := mul_le_mul_of_nonneg_left tail_twenty_at_sixtySix hAE
    dsimp only [Z]
    calc
      _ = (a * E) * (66 ^ 20 * Real.exp (-(132 / 5)) * Real.exp (-66)) *
          (2 * 36000000 * (5300000 / 6 ^ 22) * 66 ^ 2) := by ring
      _ ≤ (a * E) * 1.85e-4 * (2 * 36000000 * (5300000 / 6 ^ 22) * 66 ^ 2) :=
        mul_le_mul_of_nonneg_right hm (by norm_num)
      _ ≤ _ := by
        have hnum : (1.85e-4 : ℝ) * (2 * 36000000 * (5300000 / 6 ^ 22) * 66 ^ 2) ≤
            1 / 400 := by norm_num
        nlinarith only [mul_le_mul_of_nonneg_left hnum hAE]
  change a / 1200 * E ≤ _
  nlinarith only [hint, htail]

/-- Every nonzero degree-eleven polynomial has strictly positive complete current energy. -/
theorem form12_pos {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    {P : ℝ[X]} (hdeg : P.degree < 12) (hP : P ≠ 0) :
    0 < ∫ b : ℝ, P.eval b ^ 2 * current a b := by
  exact (mul_pos (div_pos ha0 (by norm_num)) (parabolicEnergy_pos hdeg hP)).trans_le
    (form12_lower ha0 ha hdeg)

/-- Every critical aperture has a positive definite signed section of rank twelve. -/
theorem thetaCuspCenterMixedSignedHankel_twelve_posDef {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    (thetaCuspCenterMixedSignedHankel a 12).PosDef := by
  classical
  have habs : |a| < 1 := by
    rw [abs_of_pos ha0]
    linarith only [ha]
  apply signed_posDef_of_raw habs 12
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨raw_hermitian a 12, fun v hv => ?_⟩
  rw [star_trivial]
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ[X], P = ∑ i : Fin 12, C (v i) * X ^ (i : ℕ) := ⟨_, rfl⟩
  have hdeg : P.degree < 12 := by
    rw [hPdef]
    exact degree_sum_fin_lt v
  have hcoeff : ∀ j : Fin 12, P.coeff j = v j := by
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
  have hpos := form12_pos ha0 ha hdeg hP
  have heval : ∀ b : ℝ, P.eval b ^ 2 * current a b =
      ∑ i : Fin 12, ∑ j : Fin 12, v i * v j * (b ^ ((i : ℕ) + (j : ℕ)) * current a b) := by
    intro b
    have h1 : P.eval b = ∑ i : Fin 12, v i * b ^ (i : ℕ) := by
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
  have heq : v ⬝ᵥ rawHankel a 12 *ᵥ v = ∑ i : Fin 12, ∫ b : ℝ, ∑ j : Fin 12,
      v i * v j * (b ^ ((i : ℕ) + (j : ℕ)) * current a b) := by
    simp only [dotProduct, mulVec, rawHankel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (raw_integrable a habs _).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    unfold rawMoment
    ring
  rwa [heq]

#print axioms form12_lower
#print axioms thetaCuspCenterMixedSignedHankel_twelve_posDef

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
