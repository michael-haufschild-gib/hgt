import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryCompactProfileHasAnExponentialConductorFloor
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.QuadraticOverlapConductorResiduals

/-!
# Relative conductor weights from exponential spectral floors

Conductors below the overlap pay the exponential floor. Above the overlap their individual
floors are bounded below by a constant. Splitting there keeps the exponential loss separate
from the quadratic cutoff cost.
-/

noncomputable section

open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

set_option autoImplicit false

private theorem weight_le_of_exponential_floor {a b t E m : ℝ}
    (ha : 0 < a) (hm : 0 ≤ m) (hE : a * Real.exp (-b * t) ≤ E) :
    m / E ^ 2 ≤ m * Real.exp (2 * b * t) / a ^ 2 := by
  have hbase : 0 < a * Real.exp (-b * t) := mul_pos ha (Real.exp_pos _)
  calc
    _ ≤ m / (a * Real.exp (-b * t)) ^ 2 :=
      div_le_div_of_nonneg_left hm (sq_pos_of_pos hbase)
        (pow_le_pow_left₀ hbase.le hE 2)
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * (-b * t) = -(2 * b * t) by ring, Real.exp_neg]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

private theorem sum_conductor_cast_le_sq (Q : ℕ) :
    (∑ m ∈ Icc 1 Q, (m : ℝ)) ≤ (Q : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ _m ∈ Icc 1 Q, (Q : ℝ) := sum_le_sum fun m hm => by
      exact_mod_cast (mem_Icc.mp hm).2
    _ = _ := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

private theorem sum_relative_weights_of_exponential_floor {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 1 ≤ c) (E : ℕ → ℝ)
    (hE : ∀ m : ℕ, 0 < m → a * Real.exp (-b * (c / m)) ≤ E m) (Q : ℕ) :
    (∑ m ∈ Icc 1 Q, (m : ℝ) / E m ^ 2) ≤
      ((c + 1) ^ 2 * Real.exp (2 * b * c) + (Q : ℝ) ^ 2 * Real.exp (2 * b)) / a ^ 2 := by
  classical
  let J : ℕ := ⌈c⌉₊
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hJ : (J : ℝ) ≤ c + 1 := (Nat.ceil_lt_add_one hc0.le).le
  have hpoint (m : ℕ) (hm : m ∈ Icc 1 Q) :
      (m : ℝ) / E m ^ 2 ≤
        ((if m ≤ J then (m : ℝ) else 0) * Real.exp (2 * b * c) +
          (m : ℝ) * Real.exp (2 * b)) / a ^ 2 := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := zero_lt_one.trans_le hm1
    by_cases hmJ : m ≤ J
    · rw [if_pos hmJ]
      have hcm : c / m ≤ c := div_le_self hc0.le hm1
      have hlower : a * Real.exp (-b * c) ≤ E m :=
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left hcm (neg_nonpos.mpr hb.le))) ha.le).trans
            (hE m (mem_Icc.mp hm).1)
      exact (weight_le_of_exponential_floor ha hm0.le hlower).trans
        (div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (sq_nonneg a))
    · rw [if_neg hmJ, zero_mul, zero_add]
      have hcm : c ≤ (m : ℝ) := (Nat.le_ceil c).trans (by exact_mod_cast (le_of_not_ge hmJ))
      have hratio : c / m ≤ 1 := (div_le_one hm0).mpr hcm
      have hlower : a * Real.exp (-b * 1) ≤ E m :=
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left hratio (neg_nonpos.mpr hb.le))) ha.le).trans
            (hE m (mem_Icc.mp hm).1)
      simpa only [mul_one] using weight_le_of_exponential_floor ha hm0.le hlower
  have htrunc : (∑ m ∈ Icc 1 Q, if m ≤ J then (m : ℝ) else 0) ≤ (c + 1) ^ 2 := by
    have heq : (∑ m ∈ Icc 1 Q, if m ≤ J then (m : ℝ) else 0) =
        ∑ m ∈ Icc 1 (min Q J), (m : ℝ) := by
      refine (sum_subset (Icc_subset_Icc_right (min_le_left Q J)) ?_).symm.trans ?_
      · intro m hm hout
        have hmJ : ¬ m ≤ J := fun h => hout
          (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, le_min (mem_Icc.mp hm).2 h⟩)
        rw [if_neg hmJ]
      · exact sum_congr rfl fun m hm => if_pos ((mem_Icc.mp hm).2.trans (min_le_right _ _))
    rw [heq]
    have hmin : ((min Q J : ℕ) : ℝ) ≤ J := by exact_mod_cast min_le_right Q J
    exact (sum_conductor_cast_le_sq _).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (hmin.trans hJ) 2)
  calc
    _ ≤ ∑ m ∈ Icc 1 Q,
        ((if m ≤ J then (m : ℝ) else 0) * Real.exp (2 * b * c) +
          (m : ℝ) * Real.exp (2 * b)) / a ^ 2 := sum_le_sum hpoint
    _ = ((∑ m ∈ Icc 1 Q, if m ≤ J then (m : ℝ) else 0) * Real.exp (2 * b * c) +
        (∑ m ∈ Icc 1 Q, (m : ℝ)) * Real.exp (2 * b)) / a ^ 2 := by
      rw [← sum_div, sum_add_distrib, ← sum_mul, ← sum_mul]
    _ ≤ _ := div_le_div_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right htrunc (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_right (sum_conductor_cast_le_sq Q) (Real.exp_pos _).le))
      (sq_nonneg a)

/-- Exponential spectral loss and quadratic conductor-cutoff loss add in the relative weights;
they do not multiply. The exponential rate is universal across compact profiles. -/
theorem exists_universal_exponential_relative_conductor_weight_bound :
    ∃ b : ℝ, 0 < b ∧ ∀ φ : ℝ → ℝ, ContDiff ℝ 2 φ →
      (∀ x : ℝ, x ∉ Set.Icc 0 1 → φ x = 0) → (0 < ∫ x, φ x ^ 2) →
      ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, 1 ≤ c → ∀ Q : ℕ,
        (∑ m ∈ Icc 1 Q, (m : ℝ) / completedConductorEnergy φ c m ^ 2) ≤
          K * ((c + 1) ^ 2 * Real.exp (2 * b * c) + (Q : ℝ) ^ 2) := by
  obtain ⟨b, hb, hfloor⟩ := exists_universal_exponential_completedConductor_floor
  refine ⟨b, hb, ?_⟩
  intro φ hφ hsupp hM
  obtain ⟨a, ha, hE⟩ := hfloor φ hφ hsupp hM
  let K := (1 + Real.exp (2 * b)) / a ^ 2
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro c hc Q
  have hs := sum_relative_weights_of_exponential_floor ha hb hc
    (completedConductorEnergy φ c) (hE c (zero_lt_one.trans_le hc)) Q
  refine hs.trans ?_
  dsimp only [K]
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg a)
  have hx : 0 ≤ Real.exp (2 * b) * ((c + 1) ^ 2 * Real.exp (2 * b * c)) := by positivity
  nlinarith only [hx, sq_nonneg (Q : ℝ)]

/-- Arbitrary compact profiles have an explicit summed relative quasimode budget. The overlap
loss is exponential, while the independent conductor cutoff cost remains quadratic. -/
theorem exists_universal_exponential_relative_residual_budget :
    ∃ b : ℝ, 0 < b ∧ ∀ φ : ℝ → ℝ, ContDiff ℝ 2 φ →
      (∀ x : ℝ, x ∉ Set.Icc 0 1 → φ x = 0) → (0 < ∫ x, φ x ^ 2) →
      ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k →
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.log (N : ℝ) ^ A →
        (∑ m ∈ Icc 1 Q,
          ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N)
            (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 /
              completedConductorEnergy φ c m ^ 2) ≤
          K * ((c + 1) ^ 2 * Real.exp (2 * b * c) + (Q : ℝ) ^ 2) *
            (1 + Real.log Q) ^ 2 *
            (c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
  obtain ⟨b, hb, hweights⟩ := exists_universal_exponential_relative_conductor_weight_bound
  refine ⟨b, hb, ?_⟩
  intro φ hφ hsupp hM
  obtain ⟨Kw, hKw, hsum⟩ := hweights φ hφ hsupp hM
  obtain ⟨Kr, hKr, hres⟩ := exists_completeWeil_quadratic_conductor_residual_variable_rate hφ hsupp hM
  refine ⟨Kr * Kw, mul_pos hKr hKw, ?_⟩
  intro A hA k hk
  filter_upwards [hres A hA k hk] with N hN
  intro c hc hwidth Q hQ
  let r := c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
    c ^ 10 * (Real.log (N : ℝ) / N) ^ 2
  have hr : 0 ≤ r := by
    have hc0 : 0 ≤ c := zero_le_one.trans hc
    have hlog := Real.log_natCast_nonneg N
    have h1c : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc]
    dsimp only [r]
    positivity
  calc
    _ ≤ ∑ m ∈ Icc 1 Q,
        (Kr * (m : ℝ) * (1 + Real.log Q) ^ 2 * r) / completedConductorEnergy φ c m ^ 2 := by
      refine sum_le_sum fun m hm => ?_
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
      have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
      have hlogm : Real.log m ≤ Real.log Q := Real.log_le_log hm0 hmQ
      have hp : (1 + Real.log m) ^ 2 ≤ (1 + Real.log Q) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [hlogm]) 2
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (mul_nonneg hKr.le hm0.le)) hr
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have hNm := hN m (mem_Icc.mp hm).1 (hmQ.trans hQ) c hc hwidth
      change _ ≤ Kr * ((m : ℝ) * (1 + Real.log m) ^ 2) * r at hNm
      exact (hNm.trans_eq (by ring)).trans hmul
    _ = (Kr * (1 + Real.log Q) ^ 2 * r) *
        ∑ m ∈ Icc 1 Q, (m : ℝ) / completedConductorEnergy φ c m ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (Kr * (1 + Real.log Q) ^ 2 * r) *
        (Kw * ((c + 1) ^ 2 * Real.exp (2 * b * c) + (Q : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hsum c hc Q) (by positivity)
    _ = _ := by dsimp only [r]; ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
