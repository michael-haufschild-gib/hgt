import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHaarGammaDebtIsAnAdditiveGraph
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.EveryHaarCellHasPositiveWeilEnergy

/-!
# A Gamma reserve on the original Haar prime edges

Multiplicatively related cells have a fixed gap. Centering the positive
Gamma kernel uses the exact zero means and bounds its coupling by the
smaller logarithm of two. Every odd prime-power channel therefore keeps
a positive part of its original divisor-square conductance.
-/

noncomputable section
open MeasureTheory Set Filter Finset
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry MeanZeroIntervals ArithmeticFunction

private theorem sqrt_mul_archLevyDensity_le_two {m n t : ℝ}
    (hm : 3 ≤ m) (hn : 3 ≤ n)
    (ht : Real.log (m * n - 1) - Real.log (n + 1) ≤ t) :
    Real.sqrt m * archLevyDensity t ≤ 2 := by
  have hm0 : 0 ≤ m := by linarith only [hm]
  have hn0 : 0 ≤ n := by linarith only [hn]
  have hmn := mul_le_mul_of_nonneg_right hm hn0
  have hnp : 0 < n + 1 := by linarith only [hn]
  have hmnp : 0 < m * n - 1 := by nlinarith only [hmn, hn]
  have he : (m * n - 1) / (n + 1) ≤ Real.exp t := by
    simpa only [Real.exp_sub, Real.exp_log hmnp, Real.exp_log hnp] using
      Real.exp_le_exp.mpr ht
  have htwo : 2 ≤ Real.exp t := by
    apply le_trans ?_ he
    apply (le_div_iff₀ hnp).mpr
    nlinarith only [hmn, hn]
  have hmexp : m ≤ 2 * Real.exp t := by
    have hmn2 := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ n by linarith only [hn]) hm0
    have hhalf : m / 2 ≤ (m * n - 1) / (n + 1) := by
      apply (le_div_iff₀ hnp).mpr
      nlinarith only [hmn2, hm]
    linarith only [hhalf.trans he]
  have hexp2 : Real.exp (-2 * t) * Real.exp t ^ 2 = 1 := by
    calc
      _ = Real.exp ((-2 * t) + t + t) := by
        rw [pow_two, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
      _ = 1 := by rw [show (-2 * t) + t + t = 0 by ring, Real.exp_zero]
  have hquad : (4 : ℝ) ≤ Real.exp t ^ 2 := by
    nlinarith only [htwo, sq_nonneg (Real.exp t - 2)]
  have htail : Real.exp (-2 * t) ≤ 1 / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hquad (Real.exp_pos (-2 * t)).le
    nlinarith only [hmul, hexp2]
  have hden : (3 / 4 : ℝ) ≤ 1 - Real.exp (-2 * t) := by linarith only [htail]
  have hexphalf : Real.exp (-t / 2) ^ 2 * Real.exp t = 1 := by
    calc
      _ = Real.exp ((-t / 2) + (-t / 2) + t) := by
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      _ = 1 := by rw [show (-t / 2) + (-t / 2) + t = 0 by ring, Real.exp_zero]
  have hnum_eq : (Real.sqrt m * Real.exp (-t / 2)) ^ 2 * Real.exp t = m := by
    calc
      _ = m * (Real.exp (-t / 2) ^ 2 * Real.exp t) := by
        rw [mul_pow, Real.sq_sqrt hm0]
        ring
      _ = m := by rw [hexphalf, mul_one]
  have hnum : (Real.sqrt m * Real.exp (-t / 2)) ^ 2 ≤ 2 := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos t)).mp
    simpa only [mul_comm (Real.exp t), hnum_eq] using hmexp
  have hsmall : Real.sqrt m * Real.exp (-t / 2) ≤ 3 / 2 := by
    nlinarith only [hnum, sq_nonneg (Real.sqrt m * Real.exp (-t / 2) - 3 / 2)]
  rw [archLevyDensity, ← mul_div_assoc]
  apply (div_le_iff₀ (by linarith only [hden] : 0 < 1 - Real.exp (-2 * t))).mpr
  linarith only [hsmall, hden]

/-- Every original balanced cell has at most one quarter of the first pair's width. -/
theorem four_haarMass_le_log_two {a : ℕ} (ha : 1 ≤ a) :
    4 * haarMass a ≤ Real.log 2 := by
  apply (four_haarMass_le_width ha).trans
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
  unfold logCellWidth
  rw [← Real.log_div (by positivity : (a : ℝ) + 1 ≠ 0) ha0.ne']
  apply Real.log_le_log (by positivity)
  rw [div_le_iff₀ ha0]
  linarith only [ha1]

/-- Removing the two null endpoints preserves the absolute mass of the Haar pair. -/
theorem setIntegral_abs_haarProfile_pair {a : ℕ} (ha : 1 ≤ a) :
    (∫ x in Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)),
      |haarProfile a x|) = 2 * haarMass a := by
  rw [← integral_abs_haarProfile ha, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (Real.log ((2 * a : ℕ) : ℝ))] with x hne
  by_cases hx : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, haarProfile_zero_outside_pair ha, abs_zero]
    intro hin
    exact hx ⟨lt_of_le_of_ne hin.1 hne.symm, hin.2⟩

private theorem haar_prime_edge_order {a b m : ℕ} (ha : 1 ≤ a) (hm : 3 ≤ m)
    (he : (2 * a + 1) * m = 2 * b + 1) : a < b := by
  have h := Nat.mul_le_mul_left (2 * a + 1) hm
  rw [he] at h
  omega

private theorem haar_prime_rectangle_density {a b m : ℕ} (ha : 1 ≤ a) (hm : 3 ≤ m)
    (he : (2 * a + 1) * m = 2 * b + 1) {x y : ℝ}
    (hx : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)))
    (hy : y ∈ Ioo (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ))) :
    0 < y - x ∧ archLevyDensity (y - x) ≤ 2 / Real.sqrt (m : ℝ) := by
  have hab := haar_prime_edge_order ha hm he
  have hsep : Real.log ((2 * a + 2 : ℕ) : ℝ) ≤ Real.log ((2 * b : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a + 2 ≤ 2 * b by omega))
  have hxy : 0 < y - x := by linarith only [hx.2, hy.1, hsep]
  have hlow : (m : ℝ) * ((2 * a + 1 : ℕ) : ℝ) - 1 = ((2 * b : ℕ) : ℝ) := by
    have heR : (((2 * a + 1 : ℕ) : ℝ)) * (m : ℝ) = ((2 * b + 1 : ℕ) : ℝ) :=
      by exact_mod_cast he
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at heR ⊢
    nlinarith only [heR]
  have hupp : ((2 * a + 1 : ℕ) : ℝ) + 1 = ((2 * a + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m))
  refine ⟨hxy, (le_div_iff₀ hs).mpr ?_⟩
  rw [mul_comm]
  apply sqrt_mul_archLevyDensity_le_two (by exact_mod_cast hm)
    (by exact_mod_cast (show 3 ≤ 2 * a + 1 by omega))
  rw [hlow, hupp]
  linarith only [hx.2, hy.1]

/-- On every multiplicative edge, mean cancellation leaves a Gamma coupling
strictly below the logarithmic weight of any odd prime-power channel. -/
theorem haarGammaCoupling_le_prime_scale {a b m : ℕ} (ha : 1 ≤ a) (hm : 3 ≤ m)
    (he : (2 * a + 1) * m = 2 * b + 1) :
    haarGammaCoupling a b ≤ Real.log 2 * haarMass b / Real.sqrt (m : ℝ) := by
  have hab := haar_prime_edge_order ha hm he
  have hb : 1 ≤ b := by omega
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m))
  let L : ℕ → ℝ := fun i => Real.log ((2 * i : ℕ) : ℝ)
  let U : ℕ → ℝ := fun i => Real.log ((2 * i + 2 : ℕ) : ℝ)
  let μ : Measure (ℝ × ℝ) := (volume.restrict (Ioo (L a) (U a))).prod
    (volume.restrict (Ioo (L b) (U b)))
  let P : ℝ × ℝ → ℝ := fun p => haarProfile a p.1 * haarProfile b p.2
  let H : ℝ × ℝ → ℝ := fun p => P p * archLevyDensity |p.2 - p.1|
  have hsep : U a ≤ L b := Real.log_le_log (by positivity)
    (by exact_mod_cast (show 2 * a + 2 ≤ 2 * b by omega))
  have hd : Disjoint (Ioo (L a) (U a)) (Ioo (L b) (U b)) := by
    apply disjoint_left.mpr
    intro x hx hy
    linarith only [hx.2, hy.1, hsep]
  have hrect : ∀ᵐ p ∂μ, p.1 ∈ Ioo (L a) (U a) ∧ p.2 ∈ Ioo (L b) (U b) := by
    have hx : ∀ᵐ p ∂μ, p.1 ∈ Ioo (L a) (U a) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
    have hy : ∀ᵐ p ∂μ, p.2 ∈ Ioo (L b) (U b) :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)
    filter_upwards [hx, hy] with p hp hq
    exact ⟨hp, hq⟩
  have hk : ∀ᵐ p ∂μ, 0 ≤ archLevyDensity |p.2 - p.1| ∧
      archLevyDensity |p.2 - p.1| ≤ 2 / Real.sqrt (m : ℝ) := by
    filter_upwards [hrect] with p hp
    have h := haar_prime_rectangle_density ha hm he hp.1 hp.2
    rw [abs_of_pos h.1]
    exact ⟨(archLevyDensity_pos h.1).le, h.2⟩
  have hPm : Measurable P := ((measurable_haarProfile a).comp measurable_fst).mul
    ((measurable_haarProfile b).comp measurable_snd)
  have hia : Integrable (haarProfile a) (volume.restrict (Ioo (L a) (U a))) :=
    (integrable_haarProfile a).restrict
  have hib : Integrable (haarProfile b) (volume.restrict (Ioo (L b) (U b))) :=
    (integrable_haarProfile b).restrict
  have hiP : Integrable P μ := hia.mul_prod hib
  have hPzero : (∫ p, P p ∂μ) = 0 := by
    calc
      _ = (∫ x in Ioo (L a) (U a), haarProfile a x) *
          (∫ y in Ioo (L b) (U b), haarProfile b y) :=
        integral_prod_mul (haarProfile a) (haarProfile b)
      _ = 0 := by rw [setIntegral_haarProfile_pair ha, zero_mul]
  have hPabs : (∫ p, |P p| ∂μ) = 4 * haarMass a * haarMass b := by
    calc
      _ = (∫ x in Ioo (L a) (U a), |haarProfile a x|) *
          (∫ y in Ioo (L b) (U b), |haarProfile b y|) := by
        simpa only [P, abs_mul] using
          integral_prod_mul (fun x : ℝ => |haarProfile a x|) (fun y : ℝ => |haarProfile b y|)
      _ = _ := by
        rw [setIntegral_abs_haarProfile_pair ha, setIntegral_abs_haarProfile_pair hb]
        ring
  have hwidth : U a - L a ≤ 1 := by
    rw [show U a - L a = logCellWidth a from haarPairWidth ha]
    exact (logCellWidth_le_inv ha).trans
      ((div_le_one (by positivity : (0 : ℝ) < a)).mpr (by exact_mod_cast ha))
  have hlt : L a < U a := by
    apply sub_pos.mp
    rw [show U a - L a = logCellWidth a from haarPairWidth ha]
    exact logCellWidth_pos ha
  have hiR : Integrable P (gammaRectangleMeasure (L a) (U a) (L b) (U b)) := by
    apply integrable_gammaRectangle_of_bound hlt hwidth hPm 1
    intro p
    change ‖haarProfile a p.1 * haarProfile b p.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (abs_haarProfile_le_one ha p.1) (abs_haarProfile_le_one hb p.2)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hraw : Integrable (fun p : ℝ × ℝ =>
      (ENNReal.ofReal (archLevyDensity |p.2 - p.1|)).toReal • P p) μ := by
    rwa [gammaRectangleMeasure_eq_density hd,
      integrable_withDensity_iff_integrable_smul' measurable_gammaKernel
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hiR
  have hreal : (fun p : ℝ × ℝ =>
      (ENNReal.ofReal (archLevyDensity |p.2 - p.1|)).toReal • P p) =ᵐ[μ] H := by
    filter_upwards [hk] with p hp
    rw [ENNReal.toReal_ofReal hp.1]
    exact mul_comm _ _
  have hiH : Integrable H μ := hraw.congr hreal
  have hR : haarGammaCoupling a b = -(∫ p, H p ∂μ) := by
    unfold haarGammaCoupling
    congr 1
    rw [gammaRectangleMeasure_eq_density hd,
      integral_withDensity_eq_integral_toReal_smul measurable_gammaKernel
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    exact integral_congr_ae hreal
  have hbound : ∀ᵐ p ∂μ, -H p ≤ (1 / Real.sqrt (m : ℝ)) * (|P p| - P p) := by
    filter_upwards [hk] with p hp
    by_cases hP : 0 ≤ P p
    · rw [abs_of_nonneg hP, sub_self, mul_zero]
      exact neg_nonpos.mpr (mul_nonneg hP hp.1)
    · have hPn : P p ≤ 0 := le_of_not_ge hP
      have hmul := mul_le_mul_of_nonneg_left hp.2 (neg_nonneg.mpr hPn)
      rw [abs_of_nonpos hPn]
      dsimp only [H]
      nlinarith only [hmul]
  calc
    haarGammaCoupling a b = ∫ p, -H p ∂μ := by rw [hR, integral_neg]
    _ ≤ ∫ p, (1 / Real.sqrt (m : ℝ)) * (|P p| - P p) ∂μ :=
      integral_mono_ae hiH.neg ((hiP.abs.sub hiP).const_mul _) hbound
    _ = (4 * haarMass a) * haarMass b / Real.sqrt (m : ℝ) := by
      rw [integral_const_mul, integral_sub hiP.abs hiP, hPabs, hPzero, sub_zero]
      ring
    _ ≤ Real.log 2 * haarMass b / Real.sqrt (m : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (four_haarMass_le_log_two ha) (haarMass_pos hb).le) hs.le

private theorem haar_prime_multiplier_odd {a b m : ℕ}
    (he : (2 * a + 1) * m = 2 * b + 1) : Odd m :=
  (show Odd (2 * b + 1) from ⟨b, by omega⟩).of_dvd_nat
    ⟨2 * a + 1, by simpa only [Nat.mul_comm] using he.symm⟩

private theorem haar_prime_multiplier_ge_three {a b m : ℕ} (hm : 2 ≤ m)
    (he : (2 * a + 1) * m = 2 * b + 1) : 3 ≤ m := by
  obtain ⟨k, hk⟩ := haar_prime_multiplier_odd he
  omega

private theorem log_three_le_haar_prime_weight {a b m : ℕ} (hm : 2 ≤ m)
    (he : (2 * a + 1) * m = 2 * b + 1) (hΛ : vonMangoldt m ≠ 0) :
    Real.log 3 ≤ vonMangoldt m := by
  have hp := Nat.minFac_prime (by omega : m ≠ 1)
  have ho := (haar_prime_multiplier_odd he).of_dvd_nat (Nat.minFac_dvd m)
  have hp3 : 3 ≤ m.minFac := by
    have hp2 := hp.two_le
    obtain ⟨k, hk⟩ := ho
    omega
  rw [vonMangoldt_apply, if_pos (vonMangoldt_ne_zero_iff.mp hΛ)]
  exact Real.log_le_log (by norm_num) (by exact_mod_cast hp3)

/-- The fraction of each actual odd-prime conductance needed by its Gamma edge. -/
def haarPrimeGammaShare : ℝ := Real.log 2 / Real.log 3

theorem haarPrimeGammaShare_nonneg : 0 ≤ haarPrimeGammaShare :=
  div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num))

theorem haarPrimeGammaShare_lt_one : haarPrimeGammaShare < 1 := by
  apply (div_lt_one (Real.log_pos (by norm_num : (1 : ℝ) < 3))).mpr
  exact Real.log_lt_log (by norm_num) (by norm_num)

private theorem haar_prime_gamma_coefficient_le {a b m : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hm : 2 ≤ m)
    (he : (2 * a + 1) * m = 2 * b + 1) (hΛ : vonMangoldt m ≠ 0) :
    Real.sqrt (m : ℝ) * haarGammaCoupling a b ≤
      haarPrimeGammaShare * (vonMangoldt m * haarMass b) := by
  have hm3 := haar_prime_multiplier_ge_three hm he
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m))
  have hJ := (le_div_iff₀ hs).mp (haarGammaCoupling_le_prime_scale ha hm3 he)
  have hΛ3 := log_three_le_haar_prime_weight hm he hΛ
  have hweight : Real.log 2 ≤ haarPrimeGammaShare * vonMangoldt m := by
    have h := mul_le_mul_of_nonneg_left hΛ3 haarPrimeGammaShare_nonneg
    have heq : haarPrimeGammaShare * Real.log 3 = Real.log 2 := by
      rw [haarPrimeGammaShare]
      exact div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne'
    rwa [heq] at h
  calc
    _ ≤ Real.log 2 * haarMass b := by simpa only [mul_comm] using hJ
    _ ≤ (haarPrimeGammaShare * vonMangoldt m) * haarMass b :=
      mul_le_mul_of_nonneg_right hweight (haarMass_pos hb).le
    _ = _ := mul_assoc _ _ _

/-- The Gamma graph restricted to the literal nonzero prime channels. -/
def haarPrimeGammaGraphEnergy (d : ℕ → ℝ) (X : ℕ) : ℝ := by
  classical
  exact ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
    if (2 * a + 1) * m = 2 * b + 1 ∧ vonMangoldt m ≠ 0 then
      Real.sqrt (m : ℝ) * haarGammaCoupling a b * (d a / Real.sqrt m - d b) ^ 2 else 0

/-- The original divisor conductance left after its own Gamma interaction. -/
def haarPrimeGammaReserve (d : ℕ → ℝ) (X : ℕ) : ℝ := by
  classical
  exact ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
    if (2 * a + 1) * m = 2 * b + 1 ∧ vonMangoldt m ≠ 0 then
      (vonMangoldt m * haarMass b - Real.sqrt (m : ℝ) * haarGammaCoupling a b) *
        (d a / Real.sqrt m - d b) ^ 2 else 0

theorem haarPrimeGammaGraphEnergy_nonneg (d : ℕ → ℝ) (X : ℕ) :
    0 ≤ haarPrimeGammaGraphEnergy d X := by
  classical
  apply sum_nonneg
  intro m _
  apply sum_nonneg
  intro a ha
  apply sum_nonneg
  intro b hb
  split_ifs
  · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (haarGammaCoupling_nonneg (mem_Icc.mp ha).1 (mem_Icc.mp hb).1)) (sq_nonneg _)
  · exact le_rfl

/-- The Gamma payment and the remaining conductance partition the original edge squares. -/
theorem haarPrimeGammaReserve_add_graph (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeGammaReserve d X + haarPrimeGammaGraphEnergy d X =
      haarPrimeDivisorSquares d X := by
  classical
  unfold haarPrimeGammaReserve haarPrimeGammaGraphEnergy haarPrimeDivisorSquares
  simp only [← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases he : (2 * a + 1) * m = 2 * b + 1
  · by_cases hΛ : vonMangoldt m = 0
    · simp only [he, hΛ, ne_eq, not_true_eq_false, and_false, if_false, if_true,
        zero_mul, add_zero]
    · rw [if_pos ⟨he, hΛ⟩, if_pos he]
      ring
  · simp only [he, false_and, if_false, add_zero]

/-- A fixed positive fraction of every original divisor square survives all shared Gamma edges. -/
theorem haarPrimeGammaReserve_ge (d : ℕ → ℝ) (X : ℕ) :
    (1 - haarPrimeGammaShare) * haarPrimeDivisorSquares d X ≤ haarPrimeGammaReserve d X := by
  classical
  unfold haarPrimeDivisorSquares haarPrimeGammaReserve
  simp only [mul_sum]
  apply sum_le_sum
  intro m hm
  apply sum_le_sum
  intro a ha
  apply sum_le_sum
  intro b hb
  by_cases he : (2 * a + 1) * m = 2 * b + 1
  · by_cases hΛ : vonMangoldt m = 0
    · simp only [he, hΛ, ne_eq, not_true_eq_false, and_false, if_false, if_true,
        zero_mul, mul_zero, le_refl]
    · rw [if_pos he, if_pos ⟨he, hΛ⟩]
      have hc := haar_prime_gamma_coefficient_le (mem_Icc.mp ha).1 (mem_Icc.mp hb).1
        (mem_Icc.mp hm).1 he hΛ
      have hr : (1 - haarPrimeGammaShare) * (vonMangoldt m * haarMass b) ≤
          vonMangoldt m * haarMass b - Real.sqrt (m : ℝ) * haarGammaCoupling a b := by
        nlinarith only [hc]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hr
        (sq_nonneg (d a / Real.sqrt m - d b))
  · simp only [he, false_and, if_false, mul_zero, le_refl]

theorem haarPrimeGammaReserve_nonneg (d : ℕ → ℝ) (X : ℕ) :
    0 ≤ haarPrimeGammaReserve d X :=
  (mul_nonneg (sub_nonneg.mpr haarPrimeGammaShare_lt_one.le)
    (haarPrimeDivisorSquares_nonneg d X)).trans (haarPrimeGammaReserve_ge d X)

/-- The actual Gamma contribution on arithmetic edges is paid from their divisor squares alone. -/
theorem haarPrimeGammaGraphEnergy_le_divisorSquares (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeGammaGraphEnergy d X ≤ haarPrimeGammaShare * haarPrimeDivisorSquares d X := by
  have hs := haarPrimeGammaReserve_add_graph d X
  have hr := haarPrimeGammaReserve_ge d X
  nlinarith only [hs, hr]

/-- The absent-root charges survive the shared-edge Gamma payment in full. -/
theorem haarPrimeLogDefect_sub_primeGamma_eq (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeLogDefect d X - haarPrimeGammaGraphEnergy d X = haarPrimeGammaReserve d X +
      ∑ a ∈ Icc 1 X, vonMangoldt (2 * a + 1) * haarMass a * d a ^ 2 := by
  rw [haarPrimeLogDefect_eq, ← haarPrimeGammaReserve_add_graph]
  ring

/-- The paid edge term is exactly the original Gamma graph in the divisor ground coordinates. -/
theorem haar_prime_gamma_square_eq_graph (d : ℕ → ℝ) {a b m : ℕ} (hm : 2 ≤ m)
    (he : (2 * a + 1) * m = 2 * b + 1) :
    Real.sqrt (m : ℝ) * haarGammaCoupling a b * (d a / Real.sqrt m - d b) ^ 2 =
      haarGammaGraphWeight a b * (haarGroundCoordinate d a - haarGroundCoordinate d b) ^ 2 := by
  have hn : (0 : ℝ) < ((2 * a + 1 : ℕ) : ℝ) := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hrel : ((2 * b + 1 : ℕ) : ℝ) = ((2 * a + 1 : ℕ) : ℝ) * (m : ℝ) :=
    by exact_mod_cast he.symm
  simp only [haarGammaGraphWeight, haarGroundCoordinate, hrel, Real.sqrt_mul hn.le]
  field_simp [(Real.sqrt_pos.mpr hn).ne', (Real.sqrt_pos.mpr hm0).ne'] <;> ring

/-- The finite payment retains precisely the graph weights on the actual prime channels. -/
theorem haarPrimeGammaGraphEnergy_eq_ground (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeGammaGraphEnergy d X =
      ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        if (2 * a + 1) * m = 2 * b + 1 ∧ vonMangoldt m ≠ 0 then
          haarGammaGraphWeight a b * (haarGroundCoordinate d a - haarGroundCoordinate d b) ^ 2
        else 0 := by
  classical
  unfold haarPrimeGammaGraphEnergy
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  split_ifs with he
  · exact haar_prime_gamma_square_eq_graph d (mem_Icc.mp hm).1 he.1
  · rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
