import GaloisForLFunctions.RHTower.ChronologicalHarmonicCharge
import GaloisForLFunctions.HTGeometry.TwistedMobiusLambertWittSeries

/-!
# Zero-charge rows with an exact half-length Möbius prefix

Let `M = ⌊N/2⌋`, `K = M + 1`, and let `a` be a row with `a_k = μ(k)` for `1 ≤ k ≤ M`, `|a_k| ≤ 1`
for `k ≤ N` and zero harmonic charge `Σ_{k ≤ N} a_k/k = 0`.  The Möbius–Lambert identity
`Σ_{k ≥ 1} μ(k)/(e^{kt} - 1) = e^{-t}` turns the actual residual into the tail

  `r_N(t) = Σ_{k ≥ K} μ(k)/(e^{kt} - 1) - Σ_{K ≤ k ≤ N} a_k/(e^{kt} - 1)`,

whence, with `q = e^{-t}`,

* (C) `|r_N(t)| ≤ 2 q^K / ((1 - q)(1 - q^K))`, and (B) `|r_N(t)| ≤ 2 q^K/(1 - q)²`;
* for `t ≥ δ > 0`: `|r_N(t)| ≤ 2 e^{-Kδ}/(1 - e^{-δ})²` and
  `∫_δ^∞ r_N² ≤ 2 e^{-2Kδ}/(K (1 - e^{-δ})⁴)`;
* for `N ≥ 4` and `δ = log N/N`: `∫_δ^∞ r_N² ≤ 64/(log N)²`.

Consequently, for such rows, `‖r_N‖_{L²(0,∞)} → 0` exactly when
`N⁻¹ ∫_0^{log N} r_N(u/N)² du → 0`.
-/

open MeasureTheory Set Filter ArithmeticFunction
open scoped Topology Moebius
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section

namespace RHTower

/-! ### The Möbius–Lambert identity -/

theorem one_div_exp_mul_sub_one_nonneg (k : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ 1 / (Real.exp (k * t) - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have : 1 < Real.exp (k * t) := Real.one_lt_exp_iff.mpr (by positivity)
    exact div_nonneg zero_le_one (by linarith)

/-- `1/(e^{kt} - 1) ≤ e^{-kt}/(1 - e^{-Kt})` for `k ≥ K ≥ 1`. -/
theorem one_div_exp_mul_sub_one_le {K k : ℕ} (hK : 1 ≤ K) (hk : K ≤ k) {t : ℝ} (ht : 0 < t) :
    1 / (Real.exp (k * t) - 1) ≤ Real.exp (-(k * t)) / (1 - Real.exp (-(K * t))) := by
  have hKt : 0 < (K : ℝ) * t := mul_pos (by exact_mod_cast hK) ht
  have hkK : (K : ℝ) * t ≤ k * t := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) ht.le
  have hden : 0 < 1 - Real.exp (-(K * t)) := by
    have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hKt); linarith
  have hexp : 1 < Real.exp (k * t) := Real.one_lt_exp_iff.mpr (hKt.trans_le hkK)
  rw [div_le_div_iff₀ (by linarith) hden, one_mul]
  have hmul : Real.exp (-(k * t)) * Real.exp (k * t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hmono : Real.exp (-(k * t)) ≤ Real.exp (-(K * t)) := Real.exp_le_exp.mpr (by linarith)
  nlinarith [Real.exp_pos (-(k * t))]

theorem summable_one_div_exp_mul_sub_one {t : ℝ} (ht : 0 < t) :
    Summable fun k : ℕ => 1 / (Real.exp (k * t) - 1) := by
  have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  refine Summable.of_nonneg_of_le (fun k => one_div_exp_mul_sub_one_nonneg k ht) (fun k => ?_)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (1 / (1 - Real.exp (-t))))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_mul, Real.exp_zero, sub_self, div_zero, pow_zero, mul_one]
    exact div_nonneg zero_le_one (by linarith)
  · refine (one_div_exp_mul_sub_one_le (le_refl 1) hk ht).trans_eq ?_
    rw [← Real.exp_nat_mul, Nat.cast_one, one_mul]
    ring_nf

theorem abs_moebius_real_le_one (k : ℕ) : |((μ k : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast abs_moebius_le_one

/-- **Möbius–Lambert identity.** `Σ_{k ≥ 1} μ(k)/(e^{kt} - 1) = e^{-t}` for `t > 0`. -/
theorem hasSum_moebius_div_exp_sub_one {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => (μ k : ℝ) / (Real.exp (k * t) - 1)) (Real.exp (-t)) := by
  have hsum : Summable fun k : ℕ => (μ k : ℝ) / (Real.exp (k * t) - 1) := by
    refine Summable.of_norm_bounded (summable_one_div_exp_mul_sub_one ht) fun k => ?_
    have hb := one_div_exp_mul_sub_one_nonneg k ht
    rw [Real.norm_eq_abs, div_eq_mul_one_div, abs_mul, abs_of_nonneg hb]
    exact mul_le_of_le_one_left hb (abs_moebius_real_le_one k)
  refine hsum.hasSum_iff.mpr ?_
  have hz : ‖(Real.exp (-t) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hL := GaloisForLFunctions.HTGeometry.twistedMobiusLambert_zero hz
  rw [GaloisForLFunctions.HTGeometry.twistedMobiusLambert] at hL
  have hterm : ∀ n : ℕ, GaloisForLFunctions.HTGeometry.twistedMobiusWeight 0 n *
      ((Real.exp (-t) : ℂ) ^ n / (1 - (Real.exp (-t) : ℂ) ^ n)) =
      (((μ n : ℝ) / (Real.exp (n * t) - 1) : ℝ) : ℂ) := by
    intro n
    have hq : Real.exp (-t) ^ n / (1 - Real.exp (-t) ^ n) = 1 / (Real.exp (n * t) - 1) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hx : Real.exp (-t) ^ n * Real.exp (n * t) = 1 := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, show (n : ℝ) * -t + n * t = 0 by ring,
            Real.exp_zero]
        have hpos : 1 < Real.exp (n * t) := Real.one_lt_exp_iff.mpr (by positivity)
        have hq1 : Real.exp (-t) ^ n < 1 :=
          pow_lt_one₀ (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith)) hn.ne'
        rw [div_eq_div_iff (by linarith) (by linarith)]
        linear_combination hx
    simp only [GaloisForLFunctions.HTGeometry.twistedMobiusWeight, neg_zero, Real.rpow_zero,
      mul_one]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, hq,
      ← Complex.ofReal_mul, mul_one_div]
  simp only [hterm] at hL
  exact_mod_cast (Complex.ofReal_tsum _).trans hL

/-! ### The tail bound -/

/-- **Bound (C).**  For a zero-charge row with the exact Möbius prefix through `M = ⌊N/2⌋`,
`|r_N(t)| ≤ 2 e^{-Kt}/((1 - e^{-t})(1 - e^{-Kt}))` with `K = M + 1`. -/
theorem abs_heatError_le_of_zeroCharge {a : ℕ → ℝ} {N : ℕ}
    (hpre : ∀ k : ℕ, 1 ≤ k → k ≤ N / 2 → a k = μ k)
    (hbound : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1) (hcharge : chronologicalHarmonicCharge a N = 0)
    {t : ℝ} (ht : 0 < t) :
    |chronologicalHeatError a N t| ≤
      2 * Real.exp (-((N / 2 + 1 : ℕ) * t)) /
        ((1 - Real.exp (-t)) * (1 - Real.exp (-((N / 2 + 1 : ℕ) * t)))) := by
  set M := N / 2 with hM
  set K := M + 1 with hK
  set b : ℕ → ℝ := fun k => 1 / (Real.exp (k * t) - 1) with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k => one_div_exp_mul_sub_one_nonneg k ht
  have hbs : Summable b := summable_one_div_exp_mul_sub_one ht
  have hMN : M ≤ N := Nat.div_le_self N 2
  -- the residual as a Bose sum
  have hr : chronologicalHeatError a N t =
      Real.exp (-t) - ∑ k ∈ Finset.Ioc 0 N, a k * b k := by
    rw [chronologicalHeatError_charge_decomposition a N ht, hcharge, zero_div, zero_add,
      chronologicalBoseSum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [hb, mul_one_div]
  have hμ : HasSum (fun k : ℕ => (μ k : ℝ) * b k) (Real.exp (-t)) := by
    convert hasSum_moebius_div_exp_sub_one ht using 1
    funext k
    rw [hb, mul_one_div]
  have hsplit := hμ.summable.sum_add_tsum_nat_add K
  rw [hμ.tsum_eq] at hsplit
  -- the prefix cancels
  have hhead : ∑ k ∈ Finset.range K, (μ k : ℝ) * b k = ∑ k ∈ Finset.Ioc 0 M, a k * b k := by
    rw [← Finset.sum_subset (s₁ := Finset.Ioc 0 M) (s₂ := Finset.range K)
      (fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hk).2))
      (fun k hk hk' => by
        have : k = 0 := by
          by_contra h0
          exact hk' (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h0,
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)⟩)
        subst this; simp)]
    exact Finset.sum_congr rfl fun k hk => by
      rw [hpre k (Finset.mem_Ioc.mp hk).1 (Finset.mem_Ioc.mp hk).2]
  have htailN : ∑ k ∈ Finset.Ioc 0 N, a k * b k =
      ∑ k ∈ Finset.Ioc 0 M, a k * b k + ∑ k ∈ Finset.Ioc M N, a k * b k :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMN).symm
  have hrep : chronologicalHeatError a N t =
      ∑' j : ℕ, (μ (j + K) : ℝ) * b (j + K) - ∑ k ∈ Finset.Ioc M N, a k * b k := by
    rw [hr, htailN, ← hsplit, hhead]; ring
  -- both tails are dominated by the shifted Bose tail
  have hbKs : Summable fun j : ℕ => b (j + K) := (summable_nat_add_iff K).mpr hbs
  have hterm : ∀ j : ℕ, ‖(μ (j + K) : ℝ) * b (j + K)‖ ≤ b (j + K) := fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 _)]
    exact mul_le_of_le_one_left (hb0 _) (abs_moebius_real_le_one _)
  have hnorm_s : Summable fun j : ℕ => ‖(μ (j + K) : ℝ) * b (j + K)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hbKs
  have h1 : |∑' j : ℕ, (μ (j + K) : ℝ) * b (j + K)| ≤ ∑' j : ℕ, b (j + K) := by
    rw [← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hnorm_s).trans (hnorm_s.tsum_le_tsum hterm hbKs)
  have h2 : |∑ k ∈ Finset.Ioc M N, a k * b k| ≤ ∑' j : ℕ, b (j + K) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.Ioc M N, |a k * b k| ≤ ∑ k ∈ Finset.Ioc M N, b k := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [abs_mul, abs_of_nonneg (hb0 _)]
          exact mul_le_of_le_one_left (hb0 _) (hbound k (Finset.mem_Ioc.mpr
            ⟨Nat.lt_of_le_of_lt (Nat.zero_le M) (Finset.mem_Ioc.mp hk).1,
              (Finset.mem_Ioc.mp hk).2⟩))
      _ = ∑ j ∈ Finset.range (N + 1 - K), b (K + j) := by
          rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range]
      _ ≤ ∑' j : ℕ, b (j + K) := by
          simp only [add_comm K]
          exact hbKs.sum_le_tsum _ fun j _ => hb0 _
  -- the shifted Bose tail
  have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hK1 : 1 ≤ K := Nat.succ_pos M
  have hKden : 0 < 1 - Real.exp (-(K * t)) := by
    have := Real.exp_lt_one_iff.mpr
      (neg_lt_zero.mpr (mul_pos (by exact_mod_cast hK1 : (0:ℝ) < K) ht))
    linarith
  have h3 : ∑' j : ℕ, b (j + K) ≤
      Real.exp (-(K * t)) / ((1 - Real.exp (-t)) * (1 - Real.exp (-(K * t)))) := by
    have hgeo : HasSum (fun j : ℕ => Real.exp (-(K * t)) / (1 - Real.exp (-(K * t))) *
        Real.exp (-t) ^ j)
        (Real.exp (-(K * t)) / (1 - Real.exp (-(K * t))) * (1 - Real.exp (-t))⁻¹) :=
      (hasSum_geometric_of_lt_one hq0 hq1).mul_left _
    refine (hbKs.tsum_le_tsum (fun j => ?_) hgeo.summable).trans_eq ?_
    · refine (one_div_exp_mul_sub_one_le hK1 (Nat.le_add_left K j) ht).trans_eq ?_
      have hsplitexp : Real.exp (-(((j + K : ℕ) : ℝ) * t)) =
          Real.exp (-(K * t)) * Real.exp (-t) ^ j := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
      rw [hsplitexp]; ring
    · rw [hgeo.tsum_eq]
      have h1t : (1 - Real.exp (-t)) ≠ 0 := by linarith
      field_simp
  rw [hrep]
  calc |∑' j : ℕ, (μ (j + K) : ℝ) * b (j + K) - ∑ k ∈ Finset.Ioc M N, a k * b k|
      ≤ |∑' j : ℕ, (μ (j + K) : ℝ) * b (j + K)| + |∑ k ∈ Finset.Ioc M N, a k * b k| :=
        abs_sub _ _
    _ ≤ 2 * ∑' j : ℕ, b (j + K) := by linarith
    _ ≤ _ := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left h3 zero_le_two

/-- **Bound (B).** `|r_N(t)| ≤ 2 e^{-Kt}/(1 - e^{-t})²`. -/
theorem abs_heatError_le_of_zeroCharge' {a : ℕ → ℝ} {N : ℕ}
    (hpre : ∀ k : ℕ, 1 ≤ k → k ≤ N / 2 → a k = μ k)
    (hbound : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1) (hcharge : chronologicalHarmonicCharge a N = 0)
    {t : ℝ} (ht : 0 < t) :
    |chronologicalHeatError a N t| ≤
      2 * Real.exp (-((N / 2 + 1 : ℕ) * t)) / (1 - Real.exp (-t)) ^ 2 := by
  refine (abs_heatError_le_of_zeroCharge hpre hbound hcharge ht).trans ?_
  have hq : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hK : (1 : ℝ) ≤ ((N / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hqK : Real.exp (-((N / 2 + 1 : ℕ) * t)) ≤ Real.exp (-t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  refine div_le_div_of_nonneg_left (by positivity) (by nlinarith) ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- **Uniform decay on `[δ, ∞)`.** -/
theorem abs_heatError_le_of_zeroCharge_of_le {a : ℕ → ℝ} {N : ℕ}
    (hpre : ∀ k : ℕ, 1 ≤ k → k ≤ N / 2 → a k = μ k)
    (hbound : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1) (hcharge : chronologicalHarmonicCharge a N = 0)
    {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) :
    |chronologicalHeatError a N t| ≤
      2 * Real.exp (-((N / 2 + 1 : ℕ) * δ)) / (1 - Real.exp (-δ)) ^ 2 := by
  refine (abs_heatError_le_of_zeroCharge' hpre hbound hcharge (hδ.trans_le ht)).trans ?_
  have hqδ : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hδ)
  have hqt : Real.exp (-t) ≤ Real.exp (-δ) := Real.exp_le_exp.mpr (by linarith)
  have hK : (0 : ℝ) ≤ ((N / 2 + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnum : Real.exp (-((N / 2 + 1 : ℕ) * t)) ≤ Real.exp (-((N / 2 + 1 : ℕ) * δ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc 2 * Real.exp (-((N / 2 + 1 : ℕ) * t)) / (1 - Real.exp (-t)) ^ 2
      ≤ 2 * Real.exp (-((N / 2 + 1 : ℕ) * δ)) / (1 - Real.exp (-t)) ^ 2 := by
        gcongr
    _ ≤ _ := by
        exact div_le_div_of_nonneg_left (by positivity) (by nlinarith)
          (pow_le_pow_left₀ (by linarith) (by linarith) 2)

theorem integrableOn_sq_heatError (a : ℕ → ℝ) (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    IntegrableOn (fun t => chronologicalHeatError a N t ^ 2) (Ioi δ) :=
  (show IntegrableOn (fun t => chronologicalHeatError a N t ^ 2) (Ioi 0) volume from
    (chronologicalHeatError_memLp a N).integrable_sq).mono_set (Ioi_subset_Ioi hδ)

/-- **`L²` decay on `[δ, ∞)`.** -/
theorem integral_sq_heatError_Ioi_le_of_zeroCharge {a : ℕ → ℝ} {N : ℕ}
    (hpre : ∀ k : ℕ, 1 ≤ k → k ≤ N / 2 → a k = μ k)
    (hbound : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1) (hcharge : chronologicalHarmonicCharge a N = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ t in Ioi δ, chronologicalHeatError a N t ^ 2 ≤
      2 * Real.exp (-(2 * (N / 2 + 1 : ℕ) * δ)) / ((N / 2 + 1 : ℕ) * (1 - Real.exp (-δ)) ^ 4) := by
  set K : ℝ := ((N / 2 + 1 : ℕ) : ℝ) with hK
  have hK0 : 0 < K := by rw [hK]; exact_mod_cast Nat.succ_pos _
  have hqδ : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hδ)
  have hd : 0 < 1 - Real.exp (-δ) := by linarith
  set c : ℝ := 4 / (1 - Real.exp (-δ)) ^ 4 with hc
  have hpt : ∀ t ∈ Ioi δ, chronologicalHeatError a N t ^ 2 ≤ c * Real.exp ((-2 * K) * t) := by
    intro t ht
    have ht0 : 0 < t := hδ.trans ht
    have hB := abs_heatError_le_of_zeroCharge' hpre hbound hcharge ht0
    have htδ : δ < t := ht
    have hqt : Real.exp (-t) ≤ Real.exp (-δ) := Real.exp_le_exp.mpr (by linarith)
    have hden : (1 - Real.exp (-δ)) ^ 2 ≤ (1 - Real.exp (-t)) ^ 2 :=
      pow_le_pow_left₀ hd.le (by linarith) 2
    have hB' : |chronologicalHeatError a N t| ≤ 2 * Real.exp (-(K * t)) / (1 - Real.exp (-δ)) ^ 2 :=
      hB.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
    have hsq : chronologicalHeatError a N t ^ 2 ≤
        (2 * Real.exp (-(K * t)) / (1 - Real.exp (-δ)) ^ 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hB' 2
    refine hsq.trans_eq ?_
    rw [hc, div_pow, mul_pow, ← pow_mul, show (-2 * K) * t = -(K * t) + -(K * t) by ring,
      Real.exp_add]
    ring
  have hint := integrableOn_exp_mul_Ioi (by linarith : -2 * K < 0) δ
  refine (setIntegral_mono_on (integrableOn_sq_heatError a N hδ.le) (hint.const_mul c)
    measurableSet_Ioi hpt).trans_eq ?_
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -2 * K < 0), hc]
  field_simp
  norm_num

/-- **The logarithmic window.** For `N ≥ 4`, `∫_{log N/N}^∞ r_N² ≤ 64/(log N)²`. -/
theorem integral_sq_heatError_Ioi_log_le_of_zeroCharge {a : ℕ → ℝ} {N : ℕ}
    (hpre : ∀ k : ℕ, 1 ≤ k → k ≤ N / 2 → a k = μ k)
    (hbound : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1) (hcharge : chronologicalHarmonicCharge a N = 0)
    (hN : 4 ≤ N) :
    ∫ t in Ioi (Real.log N / N), chronologicalHeatError a N t ^ 2 ≤ 64 / Real.log N ^ 2 := by
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  set δ := Real.log N / N with hδ
  have hδ0 : 0 < δ := div_pos hlog hNpos
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one hNpos]; linarith [Real.log_le_sub_one_of_pos hNpos]
  set K : ℝ := ((N / 2 + 1 : ℕ) : ℝ) with hK
  have hKN : (N : ℝ) ≤ 2 * K := by
    rw [hK]
    have : N ≤ 2 * (N / 2 + 1) := by omega
    exact_mod_cast this
  have hK0 : 0 < K := by linarith
  -- `e^{-Kδ} ≤ N^{-1/2}`, so `e^{-2Kδ} ≤ 1/N` and `e^{-Kδ} ≤ 1/2`
  have hKδ : Real.log N / 2 ≤ K * δ := by
    rw [hδ, mul_div_assoc']
    rw [div_le_div_iff₀ (by norm_num) hNpos]
    nlinarith
  have h2Kδ : Real.exp (-(2 * K * δ)) ≤ 1 / N := by
    calc Real.exp (-(2 * K * δ)) ≤ Real.exp (-Real.log N) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / N := by rw [Real.exp_neg, Real.exp_log hNpos, one_div]
  have hKδhalf : Real.exp (-(K * δ)) ≤ 1 / 2 := by
    have hsq : Real.exp (-(K * δ)) ^ 2 ≤ 1 / 4 := by
      rw [← Real.exp_nat_mul]
      calc Real.exp ((2 : ℕ) * -(K * δ)) = Real.exp (-(2 * K * δ)) := by push_cast; ring_nf
        _ ≤ 1 / N := h2Kδ
        _ ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hNr
    nlinarith [Real.exp_pos (-(K * δ))]
  have hδexp : δ / 2 ≤ 1 - Real.exp (-δ) := by
    have h1 : δ + 1 ≤ Real.exp δ := Real.add_one_le_exp δ
    have h2 : Real.exp (-δ) * Real.exp δ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h3 : Real.exp (-δ) ≤ 1 / (1 + δ) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith [Real.exp_pos (-δ)]
    have h4 : 1 - 1 / (1 + δ) = δ / (1 + δ) := by field_simp; ring
    have h5 : δ / 2 ≤ δ / (1 + δ) := div_le_div_of_nonneg_left hδ0.le (by linarith) (by linarith)
    linarith
  -- pointwise bound `|r_N(t)| ≤ 8 e^{-Kt}/δ` on `t ≥ δ`
  have hpt : ∀ t ∈ Ioi δ, chronologicalHeatError a N t ^ 2 ≤
      (64 / δ ^ 2) * Real.exp ((-2 * K) * t) := by
    intro t ht
    have htδ : δ < t := ht
    have ht0 : 0 < t := hδ0.trans htδ
    have hC := abs_heatError_le_of_zeroCharge hpre hbound hcharge ht0
    rw [← hK] at hC
    have hd1 : δ / 2 ≤ 1 - Real.exp (-t) :=
      hδexp.trans (by linarith [Real.exp_le_exp.mpr (show -t ≤ -δ by linarith)])
    have hd2 : 1 / 2 ≤ 1 - Real.exp (-(K * t)) := by
      have : Real.exp (-(K * t)) ≤ Real.exp (-(K * δ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have hden : δ / 2 * (1 / 2) ≤ (1 - Real.exp (-t)) * (1 - Real.exp (-(K * t))) :=
      mul_le_mul hd1 hd2 (by norm_num) (by linarith)
    have hC' : |chronologicalHeatError a N t| ≤ 8 * Real.exp (-(K * t)) / δ := by
      refine hC.trans ((div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans_eq ?_)
      field_simp; ring
    have hsq : chronologicalHeatError a N t ^ 2 ≤ (8 * Real.exp (-(K * t)) / δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hC' 2
    have hexp2 : Real.exp (-(K * t)) ^ 2 = Real.exp ((-2 * K) * t) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    refine hsq.trans_eq ?_
    rw [div_pow, mul_pow, hexp2]
    ring
  have hint := integrableOn_exp_mul_Ioi (by linarith : -2 * K < 0) δ
  refine (setIntegral_mono_on (integrableOn_sq_heatError a N hδ0.le) (hint.const_mul _)
    measurableSet_Ioi hpt).trans ?_
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -2 * K < 0)]
  have hval : -Real.exp (-2 * K * δ) / (-2 * K) = Real.exp (-(2 * K * δ)) / (2 * K) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring_nf
  rw [hval]
  calc 64 / δ ^ 2 * (Real.exp (-(2 * K * δ)) / (2 * K)) ≤ 64 / δ ^ 2 * ((1 / N) / N) := by
        gcongr
    _ = 64 / Real.log N ^ 2 := by rw [hδ]; field_simp

/-- **Full `L²` convergence is equivalent to the rescaled logarithmic window.**  For rows that are
eventually zero-charge, unit-bounded and carry the exact half-length Möbius prefix,
`‖r_N‖_{L²(0,∞)} → 0` if and only if `N⁻¹ ∫_0^{log N} r_N(u/N)² du → 0`. -/
theorem tendsto_L2Norm_iff_logWindow_of_zeroCharge {a : ℕ → ℕ → ℝ}
    (hrow : ∀ᶠ N : ℕ in atTop, (∀ k : ℕ, 1 ≤ k → k ≤ N / 2 → a N k = μ k) ∧
      (∀ k ∈ Finset.Ioc 0 N, |a N k| ≤ 1) ∧ chronologicalHarmonicCharge (a N) N = 0) :
    Tendsto (fun N : ℕ => chronologicalL2Norm (chronologicalHeatError (a N) N)) atTop (𝓝 0) ↔
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
        ∫ u in (0 : ℝ)..Real.log N, chronologicalHeatError (a N) N (u / N) ^ 2) atTop (𝓝 0) := by
  set I : ℕ → ℝ := fun N => ∫ t in Ioi (0 : ℝ), chronologicalHeatError (a N) N t ^ 2 with hI
  set W : ℕ → ℝ := fun N => (N : ℝ)⁻¹ *
    ∫ u in (0 : ℝ)..Real.log N, chronologicalHeatError (a N) N (u / N) ^ 2 with hW
  set T : ℕ → ℝ := fun N =>
    ∫ t in Ioi (Real.log N / N), chronologicalHeatError (a N) N t ^ 2 with hT
  have hI0 : ∀ N, 0 ≤ I N := fun N => setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  have hT0 : ∀ N, 0 ≤ T N := fun N => setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  have hnorm : ∀ N, chronologicalL2Norm (chronologicalHeatError (a N) N) = Real.sqrt (I N) :=
    fun N => chronologicalL2Norm_eq_sqrt
      ((chronologicalHeatError_continuousOn (a N) N).aestronglyMeasurable measurableSet_Ioi)
  -- the split `I = W + T`
  have hsplit : ∀ᶠ N : ℕ in atTop, I N = W N + T N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hδ : 0 ≤ Real.log N / N := (div_pos hlog hNpos).le
    have hint := (chronologicalHeatError_memLp (a N) N).integrable_sq
    have hwin : W N = ∫ t in Ioc (0 : ℝ) (Real.log N / N), chronologicalHeatError (a N) N t ^ 2 := by
      simp only [hW]
      rw [intervalIntegral.integral_comp_div (fun t => chronologicalHeatError (a N) N t ^ 2)
        hNpos.ne', smul_eq_mul, zero_div, ← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul,
        intervalIntegral.integral_of_le hδ]
    simp only [hI, hT, hwin]
    have hint' : IntegrableOn (fun t => chronologicalHeatError (a N) N t ^ 2) (Ioi 0) := hint
    rw [← Ioc_union_Ioi_eq_Ioi hδ, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint'.mono_set Ioc_subset_Ioi_self) (hint'.mono_set (Ioi_subset_Ioi hδ))]
  -- the tail vanishes
  have hTlim : Tendsto T atTop (𝓝 0) := by
    have hbound : ∀ᶠ N : ℕ in atTop, T N ≤ 64 / Real.log N ^ 2 := by
      filter_upwards [hrow, eventually_ge_atTop 4] with N hN h4
      exact integral_sq_heatError_Ioi_log_le_of_zeroCharge hN.1 hN.2.1 hN.2.2 h4
    have hlim : Tendsto (fun N : ℕ => 64 / Real.log N ^ 2) atTop (𝓝 0) := by
      have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hlog)
    exact squeeze_zero' (Eventually.of_forall hT0) hbound hlim
  have hIff : Tendsto (fun N => Real.sqrt (I N)) atTop (𝓝 0) ↔ Tendsto I atTop (𝓝 0) := by
    constructor
    · intro h
      have := h.pow 2
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
      exact this.congr fun N => Real.sq_sqrt (hI0 N)
    · intro h
      simpa using h.sqrt
  simp only [hnorm]
  rw [hIff]
  constructor
  · intro h
    have h' := h.sub hTlim
    rw [sub_zero] at h'
    exact h'.congr' (hsplit.mono fun N hN => by rw [hN]; ring)
  · intro h
    have h' := h.add hTlim
    rw [add_zero] at h'
    exact h'.congr' (hsplit.mono fun N hN => hN.symm)

end RHTower
