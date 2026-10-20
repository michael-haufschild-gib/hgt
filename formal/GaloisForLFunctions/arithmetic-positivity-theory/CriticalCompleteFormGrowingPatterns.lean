import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalArchimedeanLogCoercivity
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalCompleteFormDivergence

/-!
# The complete critical form on growing patterns

For a critical source `g_b` on a dyadic scale block `M ≤ n + 1 ≤ 2M`, every non-archimedean
channel is controlled by the coefficient `ℓ¹` mass `B₁ = ∑ |b_n|`:

* the critical mass is at most `4 B₁²` (envelope `2 B₁ e^{x/2}`);
* both polar readouts are at most `24 B₁/M`, so the polar channel is at most `144 B₁²`;
* every prime atom is at most `K Λ(r)/r²`, and on a dyadic block the admission constant obeys
  `K ≤ 384 B₁²`.

The archimedean Lévy channel grows like `log M` in coefficient `ℓ²` (logarithmic critical
coercivity). Hence the complete critical energy satisfies
`E_crit(g_b) ≥ s (log M - c₀) ∑ b_n² - C B₁²`, and since `B₁² ≤ |S| ∑ b_n²`, it is strictly
positive for every nonzero pattern with `C |S| < s (log M - c₀)`: positivity holds for patterns
whose number of atoms grows logarithmically with the scale, with explicit constants and no limit
in the pattern. For translates of a fixed pattern this gives an effective threshold for the
eventual positivity of the complete critical form.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- The prime atom `Λ(r)/√r · ac(log r)` of a critical source. -/
def criticalPrimeAtom (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) : ℝ :=
  (if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ) else 0) *
    ∫ x : ℝ, criticalFactorialSource S b x * criticalFactorialSource S b (x - Real.log (r : ℝ))

/-- Every prime atom is at most `K Λ(r)/r²` with the admission constant `K`. -/
theorem abs_criticalPrimeAtom_le (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) :
    |criticalPrimeAtom S b r| ≤
      criticalFactorialPrimeConstant S b * envelopePrimeMajorant (3 / 2) r := by
  unfold criticalPrimeAtom
  by_cases hr : 2 ≤ r
  · have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hrs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrp
    have hcorr := critical_factorial_physical_correlation_bound S b (r - 1)
    rw [Nat.sub_add_cancel (show 1 ≤ r by omega)] at hcorr
    rw [if_pos hr, criticalFactorialSource_correlation_eq S b hr1, abs_mul,
      abs_mul, abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hrs.le),
      abs_of_pos (inv_pos.mpr hrs)]
    have h := mul_le_mul_of_nonneg_left hcorr (show 0 ≤
      ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ)) * (Real.sqrt (r : ℝ))⁻¹ by positivity)
    have hs := Real.sq_sqrt hrp.le
    have he : ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ)) *
        (Real.sqrt (r : ℝ))⁻¹ * (criticalFactorialPrimeConstant S b / (r : ℝ)) =
        criticalFactorialPrimeConstant S b * envelopePrimeMajorant (3 / 2) r := by
      unfold envelopePrimeMajorant
      rw [if_pos hr]
      norm_num only [show (3 / 2 : ℝ) + 1 / 2 = 2 by norm_num, Real.rpow_two]
      field_simp
      rw [hs]
      ring
    calc
      _ ≤ ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ)) *
          (Real.sqrt (r : ℝ))⁻¹ * (criticalFactorialPrimeConstant S b / (r : ℝ)) := by
        simpa only [mul_assoc] using h
      _ = _ := he
  · simp [hr, envelopePrimeMajorant]

/-- The complete prime channel `∑_r Λ(r)/√r · ac(log r)` of a critical source. -/
def criticalPrimeEnergy (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑' r : ℕ, criticalPrimeAtom S b r

/-- The prime channel is bounded by the admission constant times `∑ Λ(r)/r²`. -/
theorem abs_criticalPrimeEnergy_le (S : Finset ℕ) (b : ℕ → ℝ) :
    |criticalPrimeEnergy S b| ≤ criticalFactorialPrimeConstant S b * canonicalPrimeMajorantConstant := by
  have hs : Summable fun r => |criticalPrimeAtom S b r| := summable_criticalFactorialSource_prime S b
  unfold criticalPrimeEnergy canonicalPrimeMajorantConstant
  rw [← tsum_mul_left, ← Real.norm_eq_abs]
  have hn : Summable fun r => ‖criticalPrimeAtom S b r‖ := by simpa only [Real.norm_eq_abs] using hs
  refine (norm_tsum_le_tsum_norm hn).trans ?_
  exact hn.tsum_le_tsum (fun r => by rw [Real.norm_eq_abs]; exact abs_criticalPrimeAtom_le S b r)
    (summable_canonicalPrimeMajorant.mul_left _)

/-- On a dyadic scale block `M ≤ n + 1 ≤ 2M` (`M ≥ 2`) the admission constant is at most
`384 (∑ |b_n|)²`. -/
theorem criticalFactorialPrimeConstant_le_of_dyadic (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : ∀ n ∈ S, M ≤ n + 1 ∧ n + 1 ≤ 2 * M) :
    criticalFactorialPrimeConstant S b ≤ 384 * (∑ n ∈ S, |b n|) ^ 2 := by
  set B1 := ∑ n ∈ S, |b n|
  have hB1 : 0 ≤ B1 := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hP1 : ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) ≤ B1 / M := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun n hn => div_le_div_of_nonneg_left (abs_nonneg _) hMpos ?_
    exact_mod_cast (hS n hn).1
  have hB2 : ∑ n ∈ S, ((n + 1 : ℕ) : ℝ) * |b n| ≤ 2 * M * B1 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact_mod_cast (hS n hn).2
  have hP0 : 0 ≤ ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) := Finset.sum_nonneg fun n _ => by positivity
  unfold criticalFactorialPrimeConstant
  calc (12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) *
        (8 * ∑ n ∈ S, |b n| + 14 * ∑ n ∈ S, ((n + 1 : ℕ) : ℝ) * |b n|) ≤
        12 * (B1 / M) * (8 * B1 + 14 * (2 * M * B1)) := by
        gcongr
    _ = 12 * B1 ^ 2 * (8 / M + 28) := by field_simp; ring
    _ ≤ 12 * B1 ^ 2 * 32 := by
        gcongr
        have : 8 / (M : ℝ) ≤ 4 := by rw [div_le_iff₀ hMpos]; linarith
        linarith
    _ = 384 * B1 ^ 2 := by ring

/-- The critical mass is at most `4 (∑ |b_n|)²`. -/
theorem criticalAutocorrelation_zero_le (S : Finset ℕ) (b : ℕ → ℝ) :
    criticalAutocorrelation S b 0 ≤ 4 * (∑ n ∈ S, |b n|) ^ 2 := by
  set B1 := ∑ n ∈ S, |b n|
  unfold criticalAutocorrelation
  simp only [sub_zero]
  have hint : Integrable fun y => criticalFactorialSource S b y * criticalFactorialSource S b y := by
    obtain ⟨h1, h2⟩ := integrable_criticalFactorialSource S b
    have h := (memLp_two_iff_integrable_sq_norm h1.aestronglyMeasurable).mp h2
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hbd : Integrable ((Iic (0 : ℝ)).indicator fun y => 4 * B1 ^ 2 * Real.exp y) := by
    rw [integrable_indicator_iff measurableSet_Iic]
    exact (integrableOn_exp_Iic 0).const_mul _
  calc ∫ y, criticalFactorialSource S b y * criticalFactorialSource S b y ≤
        ∫ y, (Iic (0 : ℝ)).indicator (fun y => 4 * B1 ^ 2 * Real.exp y) y := by
        refine integral_mono hint hbd fun y => ?_
        have h := abs_criticalFactorialSource_le S b y
        by_cases hy : y ∈ Iic (0 : ℝ)
        · rw [indicator_of_mem hy] at h ⊢
          have hexp : Real.exp (y / 2) ^ 2 = Real.exp y := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
          calc criticalFactorialSource S b y * criticalFactorialSource S b y =
                |criticalFactorialSource S b y| ^ 2 := by rw [sq_abs, sq]
            _ ≤ (2 * B1 * Real.exp (y / 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
            _ = 4 * B1 ^ 2 * Real.exp y := by rw [mul_pow, hexp]; ring
        · rw [indicator_of_notMem hy] at h ⊢
          have : criticalFactorialSource S b y = 0 := abs_nonpos_iff.mp h
          rw [this, mul_zero]
    _ = 4 * B1 ^ 2 := by
        rw [integral_indicator measurableSet_Iic, integral_const_mul, integral_exp_Iic, Real.exp_zero,
          mul_one]

open _root_.Zeta23 in
/-- Gamma constant, polar and prime channels of a critical source. -/
def criticalArithmeticChannels (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  EF.gammaBracket 0 * criticalAutocorrelation S b 0 +
    2 * (criticalFactorialPolarReadout S b * criticalFactorialPolarEndpoint S b) -
    2 * criticalPrimeEnergy S b

/-- The complete critical energy of a critical source in Gamma–Lévy form. -/
def criticalCompleteEnergy (S : Finset ℕ) (b : ℕ → ℝ) : EReal :=
  (criticalLevyEnergy S b : EReal) + (criticalArithmeticChannels S b : EReal)

/-- Translated patterns are critical sources on translated supports. -/
theorem criticalTranslatedCompleteEnergy_eq (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) :
    criticalTranslatedCompleteEnergy S b n =
      criticalCompleteEnergy (S.image (fun j => n + j)) (fun q => b (q - n)) := rfl

open _root_.Zeta23 in
/-- Channel constant `4|Ω(0)| + 288 + 768 ∑ Λ(r)/r²`. -/
def criticalChannelConstant : ℝ :=
  4 * |EF.gammaBracket 0| + 288 + 768 * canonicalPrimeMajorantConstant

/-- The channel constant is nonnegative. -/
theorem criticalChannelConstant_nonneg : 0 ≤ criticalChannelConstant := by
  unfold criticalChannelConstant
  have := canonicalPrimeMajorantConstant_nonneg
  positivity

open _root_.Zeta23 in
/-- **Uniform channel bound.** On a dyadic scale block the Gamma constant, polar and prime channels
cost at most `C (∑ |b_n|)²`. -/
theorem neg_le_criticalArithmeticChannels (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : ∀ n ∈ S, M ≤ n + 1 ∧ n + 1 ≤ 2 * M) :
    -(criticalChannelConstant * (∑ n ∈ S, |b n|) ^ 2) ≤ criticalArithmeticChannels S b := by
  set B1 := ∑ n ∈ S, |b n|
  have hB1 : 0 ≤ B1 := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hac0 : 0 ≤ criticalAutocorrelation S b 0 := by
    unfold criticalAutocorrelation
    simp only [sub_zero]
    exact integral_nonneg fun y => mul_self_nonneg _
  have hac := criticalAutocorrelation_zero_le S b
  have hΩ : -(|EF.gammaBracket 0| * (4 * B1 ^ 2)) ≤ EF.gammaBracket 0 * criticalAutocorrelation S b 0 := by
    have h1 := neg_abs_le (EF.gammaBracket 0 * criticalAutocorrelation S b 0)
    rw [abs_mul, abs_of_nonneg hac0] at h1
    nlinarith [abs_nonneg (EF.gammaBracket 0)]
  have hP1 : ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) ≤ B1 / M := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun n hn => div_le_div_of_nonneg_left (abs_nonneg _) hMpos ?_
    exact_mod_cast (hS n hn).1
  have hpol : |criticalFactorialPolarReadout S b * criticalFactorialPolarEndpoint S b| ≤ 144 * B1 ^ 2 := by
    have h1 := (abs_criticalFactorialPolarReadout_le S b).trans
      (mul_le_mul_of_nonneg_left hP1 (by norm_num))
    have h2 := (criticalFactorialPolarEndpoint_bound S b).trans
      (mul_le_mul_of_nonneg_left hP1 (by norm_num))
    rw [abs_mul]
    calc _ ≤ (24 * (B1 / M)) * (24 * (B1 / M)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = 576 * B1 ^ 2 / (M : ℝ) ^ 2 := by ring
      _ ≤ 144 * B1 ^ 2 := by
          rw [div_le_iff₀ (by positivity)]
          have hM4 : (4 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hM4 (sq_nonneg B1)]
  have hpr := (abs_criticalPrimeEnergy_le S b).trans (mul_le_mul_of_nonneg_right
    (criticalFactorialPrimeConstant_le_of_dyadic S b hM hS) canonicalPrimeMajorantConstant_nonneg)
  have h2 := neg_abs_le (criticalFactorialPolarReadout S b * criticalFactorialPolarEndpoint S b)
  have h3 := le_abs_self (criticalPrimeEnergy S b)
  unfold criticalArithmeticChannels criticalChannelConstant
  nlinarith

/-- **Complete critical form on growing patterns.** For every finite family on a dyadic scale block
`M ≤ n + 1 ≤ 2M` (`M ≥ 2`) and every real coefficient vector,
`E_crit(g_b) ≥ s (log M - c₀) ∑ b_n² - C (∑ |b_n|)²`. -/
theorem criticalCompleteEnergy_ge (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : ∀ n ∈ S, M ≤ n + 1 ∧ n + 1 ≤ 2 * M) :
    ((criticalArchLogSlope * (Real.log M - criticalArchLogOffset) * ∑ n ∈ S, b n ^ 2 -
      criticalChannelConstant * (∑ n ∈ S, |b n|) ^ 2 : ℝ) : EReal) ≤ criticalCompleteEnergy S b := by
  set X := criticalArchLogSlope * (Real.log M - criticalArchLogOffset) * ∑ n ∈ S, b n ^ 2
  have hlev : (X : EReal) ≤ (criticalLevyEnergy S b : EReal) := by
    have h1 := ofReal_le_criticalLevyEnergy S b hM fun n hn => (hS n hn).1
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  have hch := neg_le_criticalArithmeticChannels S b hM hS
  unfold criticalCompleteEnergy
  rw [sub_eq_add_neg, EReal.coe_add]
  exact add_le_add hlev (EReal.coe_le_coe_iff.mpr hch)

/-- **Positivity of the complete critical form on growing patterns.** Every nonzero real pattern
on at most `s (log M - c₀)/C` scales of a dyadic block `[M, 2M]` has strictly positive complete
critical energy. -/
theorem criticalCompleteEnergy_pos (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : ∀ n ∈ S, M ≤ n + 1 ∧ n + 1 ≤ 2 * M)
    (hcard : criticalChannelConstant * S.card < criticalArchLogSlope * (Real.log M - criticalArchLogOffset))
    (hb : ∃ n ∈ S, b n ≠ 0) :
    0 < criticalCompleteEnergy S b := by
  obtain ⟨j, hj, hbj⟩ := hb
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 < E := lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  have hcs : (∑ n ∈ S, |b n|) ^ 2 ≤ S.card * E := by
    simpa only [sq_abs] using (sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => |b i|))
  have hC := criticalChannelConstant_nonneg
  have hpos : 0 < criticalArchLogSlope * (Real.log M - criticalArchLogOffset) * E -
      criticalChannelConstant * (∑ n ∈ S, |b n|) ^ 2 := by
    have h1 : criticalChannelConstant * (∑ n ∈ S, |b n|) ^ 2 ≤ criticalChannelConstant * S.card * E := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hcs hC
    have h2 : criticalChannelConstant * S.card * E <
        criticalArchLogSlope * (Real.log M - criticalArchLogOffset) * E := mul_lt_mul_of_pos_right hcard hE
    linarith
  exact lt_of_lt_of_le (EReal.coe_pos.mpr hpos) (criticalCompleteEnergy_ge S b hM hS)

/-- **Effective threshold for translated patterns.** If a nonzero pattern has all offsets at most
`n` and `C |S| < s (log(n+1) - c₀)`, its translate to scale `n` has positive complete critical
energy: patterns of up to logarithmically many atoms are admitted at every large scale. -/
theorem criticalTranslatedCompleteEnergy_pos (S : Finset ℕ) (b : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hSn : ∀ j ∈ S, j ≤ n)
    (hcard : criticalChannelConstant * S.card <
      criticalArchLogSlope * (Real.log (n + 1 : ℕ) - criticalArchLogOffset))
    (hb : ∃ j ∈ S, b j ≠ 0) :
    0 < criticalTranslatedCompleteEnergy S b n := by
  classical
  rw [criticalTranslatedCompleteEnergy_eq]
  refine criticalCompleteEnergy_pos _ _ (M := n + 1) (by omega) ?_ ?_ ?_
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨by omega, by have := hSn j hj; omega⟩
  · rwa [Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)]
  · obtain ⟨j, hj, hbj⟩ := hb
    exact ⟨n + j, Finset.mem_image_of_mem _ hj, by simpa using hbj⟩

end GaloisForLFunctions.ArithmeticPositivityTheory
