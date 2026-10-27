import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticSectionSpace
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Arithmetic sections pay both pole moments

The tilted prime rows retain a positive diagonal reserve after paying the archimedean cross
kernel. Its weights `1 + (n/N)(1 + log N)` bound the two pole moments by complementary sums.
Weighted Young's inequality then pays the entire adverse pole product. This removes the
sinh-neutrality condition from the arithmetic section-space theorem.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- A spacing fraction that reserves enough energy for the full pole product. -/
def fullSectionRatio : ℝ :=
  min arithmeticSectionRatio (min (spacingRatio / 2) (1 / (8 * (Real.exp 1 + 1))))

theorem fullSectionRatio_pos : 0 < fullSectionRatio := by
  unfold fullSectionRatio
  exact lt_min arithmeticSectionRatio_pos
    (lt_min (div_pos spacingRatio_pos (by norm_num)) (by positivity))

theorem fullSectionRatio_le : fullSectionRatio ≤ arithmeticSectionRatio := min_le_left _ _

theorem fullSectionRatio_le_half_spacing : fullSectionRatio ≤ spacingRatio / 2 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem fullSectionRatio_le_pole : fullSectionRatio ≤ 1 / (8 * (Real.exp 1 + 1)) :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- The diagonal weight left by half of the tilted prime saving. -/
def sectionReserveWeight (N n : ℕ) : ℝ := 1 + (n : ℝ) / N * (1 + Real.log N)

theorem sectionReserveWeight_ge_one (N n : ℕ) : 1 ≤ sectionReserveWeight N n := by
  have := Real.log_natCast_nonneg N
  unfold sectionReserveWeight
  exact le_add_of_nonneg_right (by positivity)

theorem sectionReserveWeight_pos (N n : ℕ) : 0 < sectionReserveWeight N n :=
  zero_lt_one.trans_le (sectionReserveWeight_ge_one N n)

/-- The reserve mass of the independent local profiles. -/
def sectionReserve (N : ℕ) (G : ℕ → ℝ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, sectionReserveWeight N n * sectionMass (G n)

theorem sectionReserve_nonneg (N : ℕ) (G : ℕ → ℝ → ℝ) : 0 ≤ sectionReserve N G :=
  sum_nonneg fun n _ => mul_nonneg (sectionReserveWeight_pos N n).le (sectionMass_nonneg _)

/-- `log x ≤ x-1` compares the global logarithm with the logarithm at one arithmetic point. -/
theorem sectionReserveWeight_le {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    sectionReserveWeight N n ≤ 2 + (n : ℝ) / N * Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := hn0.trans_le (by exact_mod_cast hnN)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hN0 hn0)
  have h := mul_le_mul_of_nonneg_left hlog (div_pos hn0 hN0).le
  have he : (n : ℝ) / N * ((N : ℝ) / n - 1) = 1 - (n : ℝ) / N := by
    field_simp
  rw [he, Real.log_div hN0.ne' hn0.ne'] at h
  unfold sectionReserveWeight
  nlinarith only [h]

/-- The Markov form retains the pole reserve in addition to one unit of square mass. -/
theorem markovEnergy_arithmeticSection_ge_reserve {G : ℕ → ℝ → ℝ} {N : ℕ} {w : ℝ}
    (hg : ∀ n, ContDiff ℝ 2 (G n)) (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0)
    (hN : 1 ≤ N) (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N) :
    (∫ u, arithmeticSection N G u ^ 2) + sectionReserve N G / 8 ≤
      markovEnergy (fun u => (arithmeticSection N G u : ℂ)) := by
  have hδ := atomSpacing_pos hN
  have hwold : w ≤ arithmeticSectionRatio * atomSpacing N :=
    hw.trans (mul_le_mul_of_nonneg_right fullSectionRatio_le hδ.le)
  have hwhalf : w ≤ spacingRatio / 2 * atomSpacing N :=
    hw.trans (mul_le_mul_of_nonneg_right fullSectionRatio_le_half_spacing hδ.le)
  have hw2 : w ≤ atomSpacing N / 2 := by
    nlinarith only [hwhalf, spacingRatio_lt_half, hδ]
  have hw' : w < atomSpacing N := by linarith only [hw2, hδ]
  have hwN : 2 * w ≤ spacingRatio / N := by
    have h := mul_le_mul_of_nonneg_left (atomSpacing_le_inv hN) spacingRatio_pos.le
    nlinarith only [hwhalf, h]
  have hgc (n : ℕ) := profile_hasCompactSupport (hs n)
  have hf := contDiff_arithmeticSection hg N
  have hfc := hasCompactSupport_arithmeticSection hs N
  have hL := levyEnergy_arithmeticSection_ge hg hs hN hw0 hw2
  have hP := primeSum_arithmeticSection_le (fun n => (hg n).continuous) hgc hs hw'
  have hmass := integral_arithmeticSection_sq (fun n => (hg n).continuous) hgc hs hw'
  have hgain := arithmeticSectionGain_ge_one hN hw0 hwold
  have hrow : ∀ m ∈ Icc 1 N, 1 + sectionReserveWeight N m / 8 ≤
      2 * gammaHardyPhaseRate 0 +
        (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) -
        (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) := by
    intro m hm
    have hc := crossRow_le_saving (mem_Icc.mp hm).1 (mem_Icc.mp hm).2 hwN
    have hd := sectionReserveWeight_le (mem_Icc.mp hm).1 (mem_Icc.mp hm).2
    have he : (m : ℝ) / (4 * N) * Real.log m = ((m : ℝ) / N * Real.log m) / 4 := by
      ring
    rw [he] at hc ⊢
    unfold spacingConstant at hgain
    nlinarith only [hc, hd, hgain]
  have hsum := sum_le_sum (s := Icc 1 N) fun m hm =>
    mul_le_mul_of_nonneg_left (hrow m hm) (sectionMass_nonneg (G m))
  have hleft : ∑ m ∈ Icc 1 N, sectionMass (G m) *
      (1 + sectionReserveWeight N m / 8) =
        (∫ u, arithmeticSection N G u ^ 2) + sectionReserve N G / 8 := by
    rw [hmass, sectionReserve, sum_div, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  have hright : ∑ m ∈ Icc 1 N, sectionMass (G m) *
      (2 * gammaHardyPhaseRate 0 +
        (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) -
        (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m)) =
      2 * gammaHardyPhaseRate 0 * (∫ u, arithmeticSection N G u ^ 2) +
        (∑ m ∈ Icc 1 N, sectionMass (G m) *
          (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1)))) -
        ∑ m ∈ Icc 1 N, sectionMass (G m) *
          (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) := by
    rw [hmass]
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [hleft, hright] at hsum
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc]
  linarith only [hsum, hL, hP]

/-- The positive pole sees the reciprocal reserve through a quadratic arithmetic sum. -/
theorem sum_nat_div_sectionReserveWeight_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, (n : ℝ) / sectionReserveWeight N n ≤
      (N : ℝ) ^ 2 / (1 + Real.log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < 1 + Real.log N := by have := Real.log_natCast_nonneg N; positivity
  calc ∑ n ∈ Icc 1 N, (n : ℝ) / sectionReserveWeight N n
      ≤ ∑ n ∈ Icc 1 N, (N : ℝ) / (1 + Real.log N) := by
        refine sum_le_sum fun n hn => ?_
        rw [div_le_div_iff₀ (sectionReserveWeight_pos N n) hL]
        have he : (N : ℝ) * sectionReserveWeight N n = N + n * (1 + Real.log N) := by
          unfold sectionReserveWeight
          field_simp
        rw [he]
        linarith only [hN0]
    _ = (N : ℝ) ^ 2 / (1 + Real.log N) := by
      rw [sum_const, Nat.card_Icc]
      simp only [Nat.add_sub_cancel, nsmul_eq_mul]
      ring

/-- The negative pole sees at most the harmonic sum. -/
theorem sum_inv_nat_mul_sectionReserveWeight_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, 1 / ((n : ℝ) * sectionReserveWeight N n) ≤ 1 + Real.log N := by
  calc ∑ n ∈ Icc 1 N, 1 / ((n : ℝ) * sectionReserveWeight N n)
      ≤ ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ := by
        refine sum_le_sum fun n hn => ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        rw [← one_div]
        exact one_div_le_one_div_of_le hn0
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (sectionReserveWeight_ge_one N n) hn0.le)
    _ ≤ 1 + Real.log N := by
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        using harmonic_le_one_add_log N

/-- Cauchy–Schwarz on the support interval controls any bounded local moment. -/
theorem sectionMoment_sq_le {g k : ℝ → ℝ} {w K : ℝ}
    (hg : Continuous g) (hk : Continuous k) (hw : 0 ≤ w)
    (hs : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hb : ∀ u ∈ Set.Icc 0 w, k u ^ 2 ≤ K) :
    (∫ u, g u * k u) ^ 2 ≤ w * K * sectionMass g := by
  have hg2 : IntegrableOn (fun u => g u ^ 2) (Set.Icc 0 w) := (hg.pow 2).integrableOn_Icc
  have hk2 : IntegrableOn (fun u => k u ^ 2) (Set.Icc 0 w) := (hk.pow 2).integrableOn_Icc
  have hcs := HTGeometry.sq_integral_mul_le (μ := volume.restrict (Set.Icc 0 w))
    hg.aestronglyMeasurable hk.aestronglyMeasurable hg2 hk2
  have hprod : (∫ u, g u * k u) = ∫ u in Set.Icc 0 w, g u * k u := by
    rw [← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ Set.Icc 0 w
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, hs u hu, zero_mul]
  have hmass : sectionMass g = ∫ u in Set.Icc 0 w, g u ^ 2 := by
    rw [sectionMass, ← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ Set.Icc 0 w
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, hs u hu, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hkbound : (∫ u in Set.Icc 0 w, k u ^ 2) ≤ w * K := by
    calc (∫ u in Set.Icc 0 w, k u ^ 2) ≤ ∫ _u in Set.Icc 0 w, K :=
        setIntegral_mono_on hk2 continuous_const.integrableOn_Icc measurableSet_Icc hb
      _ = w * K := by
        rw [setIntegral_const]
        change (volume (Set.Icc (0 : ℝ) w)).toReal * K = w * K
        rw [Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hw]
  rw [← hprod, ← hmass] at hcs
  exact hcs.trans (by nlinarith only [mul_le_mul_of_nonneg_left hkbound (sectionMass_nonneg g)])

theorem poleA_profile_sq_le {g : ℝ → ℝ} {w : ℝ} (hg : Continuous g) (hw : 0 ≤ w)
    (hs : ∀ u, u ∉ Set.Icc 0 w → g u = 0) :
    poleA g ^ 2 ≤ w * Real.exp w * sectionMass g := by
  refine sectionMoment_sq_le hg (Real.continuous_exp.comp (continuous_id.div_const 2)) hw hs ?_
  intro u hu
  rw [pow_two, ← Real.exp_add, show u / 2 + u / 2 = u by ring]
  exact Real.exp_le_exp.mpr hu.2

theorem poleB_profile_sq_le {g : ℝ → ℝ} {w : ℝ} (hg : Continuous g) (hw : 0 ≤ w)
    (hs : ∀ u, u ∉ Set.Icc 0 w → g u = 0) :
    poleB g ^ 2 ≤ w * sectionMass g := by
  have h := sectionMoment_sq_le hg
    (Real.continuous_exp.comp (continuous_id.neg.div_const 2)) hw hs
    (K := 1) (fun u hu => by
      rw [pow_two, ← Real.exp_add, show -u / 2 + -u / 2 = -u by ring]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.1))
  simpa only [mul_one] using h

/-- Translating a local section multiplies its exponential moment by the arithmetic character. -/
theorem exponentialMoment_arithmeticSection {G : ℕ → ℝ → ℝ}
    (hg : ∀ n, Continuous (G n)) (hgc : ∀ n, HasCompactSupport (G n)) (N : ℕ) (a : ℝ) :
    (∫ u, arithmeticSection N G u * Real.exp (a * u)) =
      ∑ n ∈ Icc 1 N, Real.exp (a * Real.log n) * ∫ u, G n u * Real.exp (a * u) := by
  have hi (n : ℕ) : Integrable fun u => G n (u - Real.log n) * Real.exp (a * u) :=
    (((hg n).comp (continuous_sub_right _)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      ((hgc n).comp_homeomorph (Homeomorph.subRight _)).mul_right
  simp only [arithmeticSection, sum_mul]
  rw [integral_finsetSum _ fun n _ => hi n]
  refine sum_congr rfl fun n _ => ?_
  rw [← integral_add_right_eq_self
    (fun u => G n (u - Real.log n) * Real.exp (a * u)) (Real.log n)]
  simp only [add_sub_cancel_right]
  have he : ∀ u, G n u * Real.exp (a * (u + Real.log n)) =
      Real.exp (a * Real.log n) * (G n u * Real.exp (a * u)) := by
    intro u
    rw [mul_add, Real.exp_add]
    ring
  simp_rw [he]
  exact integral_const_mul _ _

/-- The increasing pole moment is controlled by the quadratic reciprocal-reserve sum. -/
theorem poleA_arithmeticSection_sq_le {G : ℕ → ℝ → ℝ} {N : ℕ} {w : ℝ}
    (hg : ∀ n, Continuous (G n)) (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0)
    (hN : 1 ≤ N) (hw : 0 ≤ w) :
    poleA (arithmeticSection N G) ^ 2 ≤
      (w * Real.exp w * ((N : ℝ) ^ 2 / (1 + Real.log N))) * sectionReserve N G := by
  have hgc (n : ℕ) := profile_hasCompactSupport (hs n)
  have he : ∀ u : ℝ, (1 / 2) * u = u / 2 := fun u => by ring
  have hA : poleA (arithmeticSection N G) =
      ∑ n ∈ Icc 1 N, Real.exp (Real.log n / 2) * poleA (G n) := by
    simpa only [he, ← poleA] using exponentialMoment_arithmeticSection hg hgc N (1 / 2)
  let r : ℕ → ℝ := fun n => Real.exp (Real.log n / 2) * poleA (G n)
  let p : ℕ → ℝ := fun n => w * Real.exp w * ((n : ℝ) / sectionReserveWeight N n)
  let q : ℕ → ℝ := fun n => sectionReserveWeight N n * sectionMass (G n)
  have hcs : (∑ n ∈ Icc 1 N, r n) ^ 2 ≤ (∑ n ∈ Icc 1 N, p n) * ∑ n ∈ Icc 1 N, q n := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul (Icc 1 N)
      (fun n _ => by dsimp [p]; have := sectionReserveWeight_pos N n; positivity)
      (fun n _ => mul_nonneg (sectionReserveWeight_pos N n).le (sectionMass_nonneg _)) ?_
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hexp : Real.exp (Real.log n / 2) ^ 2 = (n : ℝ) := by
      rw [pow_two, ← Real.exp_add, show Real.log n / 2 + Real.log n / 2 = Real.log n by ring,
        Real.exp_log hn0]
    dsimp [r, p, q]
    rw [mul_pow, hexp]
    calc (n : ℝ) * poleA (G n) ^ 2
        ≤ n * (w * Real.exp w * sectionMass (G n)) :=
          mul_le_mul_of_nonneg_left (poleA_profile_sq_le (hg n) hw (hs n)) hn0.le
      _ = _ := by field_simp [(sectionReserveWeight_pos N n).ne']; ring
  have hp : ∑ n ∈ Icc 1 N, p n ≤ w * Real.exp w * ((N : ℝ) ^ 2 / (1 + Real.log N)) := by
    simpa only [p, mul_sum] using mul_le_mul_of_nonneg_left
      (sum_nat_div_sectionReserveWeight_le hN) (mul_nonneg hw (Real.exp_pos w).le)
  rw [hA]
  exact hcs.trans (mul_le_mul_of_nonneg_right hp (sectionReserve_nonneg N G))

/-- The decreasing pole moment is controlled by the harmonic reciprocal-reserve sum. -/
theorem poleB_arithmeticSection_sq_le {G : ℕ → ℝ → ℝ} {N : ℕ} {w : ℝ}
    (hg : ∀ n, Continuous (G n)) (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0)
    (hw : 0 ≤ w) :
    poleB (arithmeticSection N G) ^ 2 ≤
      (w * (1 + Real.log N)) * sectionReserve N G := by
  have hgc (n : ℕ) := profile_hasCompactSupport (hs n)
  have he : ∀ u : ℝ, -(1 / 2) * u = -u / 2 := fun u => by ring
  have hB : poleB (arithmeticSection N G) =
      ∑ n ∈ Icc 1 N, Real.exp (-Real.log n / 2) * poleB (G n) := by
    simpa only [he, ← poleB] using exponentialMoment_arithmeticSection hg hgc N (-(1 / 2))
  let r : ℕ → ℝ := fun n => Real.exp (-Real.log n / 2) * poleB (G n)
  let p : ℕ → ℝ := fun n => w * (1 / ((n : ℝ) * sectionReserveWeight N n))
  let q : ℕ → ℝ := fun n => sectionReserveWeight N n * sectionMass (G n)
  have hcs : (∑ n ∈ Icc 1 N, r n) ^ 2 ≤ (∑ n ∈ Icc 1 N, p n) * ∑ n ∈ Icc 1 N, q n := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul (Icc 1 N)
      (fun n _ => by dsimp [p]; have := sectionReserveWeight_pos N n; positivity)
      (fun n _ => mul_nonneg (sectionReserveWeight_pos N n).le (sectionMass_nonneg _)) ?_
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hexp : Real.exp (-Real.log n / 2) ^ 2 = 1 / (n : ℝ) := by
      rw [pow_two, ← Real.exp_add,
        show -Real.log n / 2 + -Real.log n / 2 = -Real.log n by ring,
        Real.exp_neg, Real.exp_log hn0, one_div]
    dsimp [r, p, q]
    rw [mul_pow, hexp]
    calc 1 / (n : ℝ) * poleB (G n) ^ 2
        ≤ 1 / n * (w * sectionMass (G n)) :=
          mul_le_mul_of_nonneg_left (poleB_profile_sq_le (hg n) hw (hs n)) (by positivity)
      _ = _ := by field_simp [hn0.ne', (sectionReserveWeight_pos N n).ne']
  have hp : ∑ n ∈ Icc 1 N, p n ≤ w * (1 + Real.log N) := by
    simpa only [p, mul_sum] using mul_le_mul_of_nonneg_left
      (sum_inv_nat_mul_sectionReserveWeight_le N) hw
  rw [hB]
  exact hcs.trans (mul_le_mul_of_nonneg_right hp (sectionReserve_nonneg N G))

/-- Complementary moment bounds pay the pole product uniformly in the number of sections. -/
theorem neg_sectionReserve_le_poleProduct {G : ℕ → ℝ → ℝ} {N : ℕ} {w : ℝ}
    (hg : ∀ n, Continuous (G n)) (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0)
    (hN : 1 ≤ N) (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N) :
    -(sectionReserve N G / 8) ≤
      2 * poleA (arithmeticSection N G) * poleB (arithmeticSection N G) := by
  let A := poleA (arithmeticSection N G)
  let B := poleB (arithmeticSection N G)
  let L := 1 + Real.log N
  let D := sectionReserve N G
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < L := by dsimp [L]; have := Real.log_natCast_nonneg N; positivity
  have hD : 0 ≤ D := sectionReserve_nonneg N G
  have hA := mul_le_mul_of_nonneg_left (poleA_arithmeticSection_sq_le hg hs hN hw0.le)
    (show 0 ≤ L / N by positivity)
  have hB := mul_le_mul_of_nonneg_left (poleB_arithmeticSection_sq_le hg hs hw0.le)
    (show 0 ≤ (N : ℝ) / L by positivity)
  have heA : L / N * ((w * Real.exp w * ((N : ℝ) ^ 2 / L)) * D) =
      w * N * Real.exp w * D := by field_simp; ring
  have heB : (N : ℝ) / L * ((w * L) * D) = w * N * D := by field_simp; ring
  change L / N * A ^ 2 ≤ L / N * ((w * Real.exp w * ((N : ℝ) ^ 2 / L)) * D) at hA
  change (N : ℝ) / L * B ^ 2 ≤ (N : ℝ) / L * ((w * L) * D) at hB
  rw [heA] at hA
  rw [heB] at hB
  have hYoung : 0 ≤ L / N * A ^ 2 + 2 * A * B + (N : ℝ) / L * B ^ 2 := by
    have he : (L * A + N * B) ^ 2 / (L * N) =
        L / N * A ^ 2 + 2 * A * B + (N : ℝ) / L * B ^ 2 := by field_simp; ring
    rw [← he]
    positivity
  have hwN : w * N ≤ fullSectionRatio := by
    have h := hw.trans (mul_le_mul_of_nonneg_left (atomSpacing_le_inv hN) fullSectionRatio_pos.le)
    have he : fullSectionRatio * (1 / (N : ℝ)) = fullSectionRatio / N := by ring
    rw [he, le_div_iff₀ hN0] at h
    exact h
  have hw1 : w ≤ 1 := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hwwN : w ≤ w * N := by nlinarith only [hw0, hN1]
    linarith only [hwwN, hwN, fullSectionRatio_le_half_spacing, spacingRatio_lt_half]
  have hc : w * N * (Real.exp w + 1) ≤ 1 / 8 := by
    calc w * N * (Real.exp w + 1) ≤ fullSectionRatio * (Real.exp 1 + 1) :=
        mul_le_mul hwN (add_le_add_right (Real.exp_le_exp.mpr hw1) 1)
          (by positivity) fullSectionRatio_pos.le
      _ ≤ (1 / (8 * (Real.exp 1 + 1))) * (Real.exp 1 + 1) :=
        mul_le_mul_of_nonneg_right fullSectionRatio_le_pole (by positivity)
      _ = 1 / 8 := by field_simp
  have hcost := mul_le_mul_of_nonneg_right hc hD
  change -(D / 8) ≤ 2 * A * B
  nlinarith only [hYoung, hA, hB, hcost]

/-- The original Weil form is the Markov energy plus the two exponential pole readings. -/
theorem weilPair_eq_markovEnergy_add_poleProduct {f : ℝ → ℝ} (hf : f ∈ realTests) :
    weilPair f f = markovEnergy (cx f) + 2 * poleA f * poleB f := by
  have hcd := cx_contDiff hf.1
  have hcs := cx_hasCompactSupport hf.2
  have he := markovEnergy_eq_W_sub hcd hcs
  have hpole : (weilPoleTerm (Zeta23.EF.weilTest (cx f) (cx f))).re =
      2 * poleA f * poleB f := by
    have hm := integral_mul_exp_half_eq_cosh_add_sinh hf.1.continuous hf.2
    change poleA f = coshHalfMoment f + sinhHalfMoment f ∧
      poleB f = coshHalfMoment f - sinhHalfMoment f at hm
    have h := re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hf.1.continuous hf.2
    rw [hm.1, hm.2]
    convert h using 1 <;> ring
  have hW : (Zeta23.zetaZeroConfig.W (cx f) (cx f)).re = weilPair f f := by
    rw [weilPair, zeta_W_eq_weilFullFunctional_mixed hcd hcs hcd hcs]
  rw [hpole, hW] at he
  linarith only [he]

/-- The full Weil form dominates square mass on every independent arithmetic section.
No pole moment is constrained. -/
theorem integral_sq_le_weilPair_arithmeticSection {N : ℕ} (hN : 1 ≤ N)
    {w : ℝ} (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N)
    (f : arithmeticSectionTests N w) :
    (∫ u, f.1.1 u ^ 2) ≤ weilPair f.1.1 f.1.1 := by
  obtain ⟨G, hG, hsG, heG⟩ := f.2
  have hM := markovEnergy_arithmeticSection_ge_reserve hG hsG hN hw0 hw
  have hP := neg_sectionReserve_le_poleProduct (fun n => (hG n).continuous) hsG hN hw0 hw
  have hW := weilPair_eq_markovEnergy_add_poleProduct f.1.2
  rw [heG] at hW ⊢
  change weilPair (arithmeticSection N G) (arithmeticSection N G) =
    markovEnergy (fun u => (arithmeticSection N G u : ℂ)) +
      2 * poleA (arithmeticSection N G) * poleB (arithmeticSection N G) at hW
  linarith only [hM, hP, hW]

/-- The entire arithmetic section space has source-defined Riemann–Roch and ampleness
on the original scaling subsurface. -/
theorem arithmeticSections_effectivity {N : ℕ} (hN : 1 ≤ N)
    {w : ℝ} (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N) :
    (scalingSubsurface (arithmeticSectionTests N w)).RiemannRochAxiom
        (l2SourceCone 1 (arithmeticSectionTests N w)) ∧
      (scalingSubsurface (arithmeticSectionTests N w)).AmpleAxiom
        (l2SourceCone 1 (arithmeticSectionTests N w)) ∧
      (scalingSubsurface (arithmeticSectionTests N w)).HodgeIndex := by
  have hc : (0 : ℝ) < 1 := zero_lt_one
  have hf := integral_sq_le_weilPair_arithmeticSection hN hw0 hw
  refine ⟨(l2SourceCone_riemannRoch_iff_weilPair_ge hc _).mpr ?_,
    l2SourceCone_ample hc _, (scalingSubsurface_hodgeIndex_iff_weilPair_nonneg _).mpr ?_⟩
  · intro f
    simpa only [one_mul] using hf f
  · intro f
    exact (integral_nonneg fun _ => sq_nonneg _).trans (hf f)

#print axioms markovEnergy_arithmeticSection_ge_reserve
#print axioms neg_sectionReserve_le_poleProduct
#print axioms integral_sq_le_weilPair_arithmeticSection
#print axioms arithmeticSections_effectivity

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
