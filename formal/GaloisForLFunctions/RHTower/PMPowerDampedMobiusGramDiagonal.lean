import GaloisForLFunctions.RHTower.PMPowerDampedMobiusEndpoint
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusMellin
import GaloisForLFunctions.RHTower.FermiNymanBoundedSpuriousClassification
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact physical Fermi generator geometry: negative parity indicators, norm squared
`log(2)/a`, and summability of the actual power-damped Möbius diagonal for every
positive damping. Contiguous positive blocks rule out a coefficient-independent
diagonal synthesis ceiling. The signed Möbius cross-term bound remains open. -/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

/-- The Fermi generator is exactly a negative parity indicator. -/
theorem pm_fermiNymanGen_eq_zero_or_neg_one (a t : ℝ) :
    fermiNymanGen a t = 0 ∨ fermiNymanGen a t = -1 := by
  let x := (1 / t) / a
  have hx : x / 2 + x / 2 = x := by ring
  have hlo := Int.le_floor_add (x / 2) (x / 2)
  have hhi := Int.le_floor_add_floor (x / 2) (x / 2)
  rw [hx] at hlo hhi
  have hc : 2 * ⌊x / 2⌋ - ⌊x⌋ = 0 ∨ 2 * ⌊x / 2⌋ - ⌊x⌋ = -1 := by omega
  have heq : (1 / (2 * t)) / a = x / 2 := by dsimp [x]; ring
  rw [fermiNymanGen_eq_floor_difference, heq]
  rcases hc with h | h
  · left
    have hr : (2 : ℝ) * (⌊x / 2⌋ : ℝ) - (⌊x⌋ : ℝ) = 0 := by exact_mod_cast h
    rw [hr]
    rfl
  · right
    have hr : (2 : ℝ) * (⌊x / 2⌋ : ℝ) - (⌊x⌋ : ℝ) = -1 := by exact_mod_cast h
    rw [hr]
    norm_num

theorem pm_norm_fermiNymanGen_le_one (a t : ℝ) : ‖fermiNymanGen a t‖ ≤ 1 := by
  rcases pm_fermiNymanGen_eq_zero_or_neg_one a t with h | h <;> simp [h]

theorem pm_fermiNymanGen_norm_sq_eq_neg (a t : ℝ) :
    ((‖fermiNymanGen a t‖ ^ 2 : ℝ) : ℂ) = -fermiNymanGen a t := by
  rcases pm_fermiNymanGen_eq_zero_or_neg_one a t with h | h <;> simp [h]

theorem pm_dyadicLogMean_one : dyadicLogMean (fun _ => (1 : ℂ)) = Real.log 2 := by
  rw [dyadicLogMean]
  simp only [mul_one, ← Complex.ofReal_inv]
  rw [integral_complex_ofReal]
  congr 1
  rw [← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
    integral_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1)]
  norm_num

theorem pm_integral_normSq_fermiNymanGen_one :
    (∫ t in Ioi (0 : ℝ), ‖fermiNymanGen 1 t‖ ^ 2) = Real.log 2 := by
  have h := integral_fermiNymanGen_mul_of_dyadicSelfSimilar
    (w := fun _ => (1 : ℂ)) continuousOn_const (fun _ _ => rfl) (by norm_num : (1 : ℝ) ≤ 1)
  simp only [mul_one, Complex.ofReal_one, inv_one, pm_dyadicLogMean_one, neg_mul, one_mul] at h
  have hIoc : (∫ t in Ioc (0 : ℝ) 1, ‖fermiNymanGen 1 t‖ ^ 2) = Real.log 2 := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simp_rw [pm_fermiNymanGen_norm_sq_eq_neg]
    rw [integral_neg, h, neg_neg]
  rw [← hIoc]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun _ ht => ht.1)
  intro t ht
  have ht1 : 1 < t := by
    have ht0 := ht.1
    have hn := ht.2
    simp only [mem_Ioi, mem_Ioc, not_and] at ht0 hn
    exact lt_of_not_ge (hn ht0)
  rw [fermiNymanGen_eq_zero_of_inv_lt (by norm_num : (0 : ℝ) < 1) (by simpa using ht1)]
  simp

theorem pm_integral_normSq_fermiNymanGen {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), ‖fermiNymanGen a t‖ ^ 2) = Real.log 2 / a := by
  simp_rw [pm_fermiNymanGen_dilate a]
  rw [integral_comp_mul_left_Ioi (fun t : ℝ => ‖fermiNymanGen 1 t‖ ^ 2) 0 ha]
  simp only [mul_zero, smul_eq_mul, pm_integral_normSq_fermiNymanGen_one]
  ring

/-- The actual power-damped Möbius diagonal term in the canonical physical norm. -/
def pmPowerDampedFermiDiagonalTerm (ε : ℝ) (d : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), ‖pmPowerDampedMobiusCoeff ε d * fermiNymanGen (d : ℝ) t‖ ^ 2

theorem pmPowerDampedFermiDiagonalTerm_eq (ε : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    pmPowerDampedFermiDiagonalTerm ε d =
      ‖pmPowerDampedMobiusCoeff ε d‖ ^ 2 * (Real.log 2 / d) := by
  unfold pmPowerDampedFermiDiagonalTerm
  simp_rw [norm_mul, mul_pow]
  rw [integral_const_mul, pm_integral_normSq_fermiNymanGen (by exact_mod_cast hd)]

theorem pmPowerDampedFermiDiagonalTerm_nonneg (ε : ℝ) (d : ℕ) :
    0 ≤ pmPowerDampedFermiDiagonalTerm ε d := by
  apply integral_nonneg
  intro t
  exact sq_nonneg _

theorem pmPowerDampedFermiDiagonalTerm_le (ε : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    pmPowerDampedFermiDiagonalTerm ε d ≤
      Real.log 2 * (d : ℝ) ^ (-(2 * ε + 1)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : ‖pmPowerDampedMobiusCoeff ε d‖ ≤ (d : ℝ) ^ (-ε) := by
    rw [pmPowerDampedMobiusCoeff, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hd0.le _)]
    exact (mul_le_mul_of_nonneg_right (Sieve.abs_moebius_real_le_one d)
      (Real.rpow_nonneg hd0.le _)).trans_eq (one_mul _)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [pmPowerDampedFermiDiagonalTerm_eq ε hd]
  calc
    _ ≤ ((d : ℝ) ^ (-ε)) ^ 2 * (Real.log 2 / d) :=
      mul_le_mul_of_nonneg_right (sq_le_sq₀ (norm_nonneg _)
        (Real.rpow_nonneg hd0.le _) |>.mpr hc) (div_nonneg hlog hd0.le)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd0.le]
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      calc
        _ = Real.log 2 * ((d : ℝ) ^ (-ε * (2 : ℝ)) * (d : ℝ) ^ (-1 : ℝ)) := by
          push_cast
          ring
        _ = _ := by
          rw [← Real.rpow_add hd0]
          congr 2
          ring

theorem pmPowerDampedFermiDiagonalTerm_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (pmPowerDampedFermiDiagonalTerm ε) := by
  have hp : Summable (fun d : ℕ => (d : ℝ) ^ (-(2 * ε + 1))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply (hp.mul_left (Real.log 2)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with d hd
  rw [Real.norm_eq_abs, abs_of_nonneg (pmPowerDampedFermiDiagonalTerm_nonneg ε d)]
  exact pmPowerDampedFermiDiagonalTerm_le ε hd

/-- On its first support band the parity indicator equals minus one. -/
theorem pm_fermiNymanGen_first_band {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hlo : 1 / 2 < a * t) (hhi : a * t ≤ 1) : fermiNymanGen a t = -1 := by
  have hat : 0 < a * t := mul_pos ha ht
  have h1 : 1 ≤ 1 / (a * t) := (le_div_iff₀ hat).mpr (by simpa using hhi)
  have h2 : 1 / (a * t) < 2 := (div_lt_iff₀ hat).mpr (by linarith)
  have hf : ⌊1 / (a * t)⌋ = (1 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    norm_num only [Int.cast_one]
    exact ⟨h1, by linarith⟩
  have hh : ⌊(1 / (a * t)) / 2⌋ = (0 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    norm_num only [Int.cast_zero, zero_add]
    exact ⟨by positivity, by linarith⟩
  rw [fermiNymanGen_eq_floor_difference]
  rw [show (1 / t) / a = 1 / (a * t) by ring,
    show (1 / (2 * t)) / a = (1 / (a * t)) / 2 by ring, hf, hh]
  norm_num

def pmFermiPositiveBlock (N : ℕ) (t : ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc (2 * N) (3 * N), fermiNymanGen (d : ℝ) t

theorem memLp_pmFermiPositiveBlock {N : ℕ} (hN : 1 ≤ N) :
    MemLp (pmFermiPositiveBlock N) 2 (volume.restrict (Ioi 0)) := by
  apply memLp_finsetSum (Finset.Icc (2 * N) (3 * N))
    (f := fun d : ℕ => fermiNymanGen (d : ℝ))
  intro d hd
  apply memLp_pm_fermiNymanGen
  have hd0 : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
  exact_mod_cast hd0

theorem pmFermiPositiveBlock_first_band {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Ioc (1 / (4 * (N : ℝ))) (1 / (3 * (N : ℝ)))) :
    pmFermiPositiveBlock N t = -((N + 1 : ℕ) : ℂ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0 : 0 < t := (by positivity : (0 : ℝ) < 1 / (4 * (N : ℝ))).trans ht.1
  have hlow : 1 < t * (4 * (N : ℝ)) := (div_lt_iff₀ (by positivity)).mp ht.1
  have hupp : t * (3 * (N : ℝ)) ≤ 1 := (le_div_iff₀ (by positivity)).mp ht.2
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc (2 * N) (3 * N)) :
      fermiNymanGen (d : ℝ) t = -1 := by
    have hdlo : 2 * (N : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hdhi : (d : ℝ) ≤ 3 * N := by exact_mod_cast (Finset.mem_Icc.mp hd).2
    apply pm_fermiNymanGen_first_band (by linarith) ht0
    · have := mul_le_mul_of_nonneg_right hdlo ht0.le
      nlinarith
    · have := mul_le_mul_of_nonneg_right hdhi ht0.le
      nlinarith
  have hcard : (Finset.Icc (2 * N) (3 * N)).card = N + 1 := by
    rw [Nat.card_Icc]
    omega
  rw [pmFermiPositiveBlock, Finset.sum_congr rfl hterm, Finset.sum_const, hcard]
  simp

theorem pmFermiPositiveBlock_energy_lower {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) / 12 ≤ ∫ t in Ioi (0 : ℝ), ‖pmFermiPositiveBlock N t‖ ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hband : (1 / (4 * (N : ℝ))) ≤ 1 / (3 * (N : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hint : IntegrableOn (fun t => ‖pmFermiPositiveBlock N t‖ ^ 2) (Ioi (0 : ℝ)) :=
    (memLp_pmFermiPositiveBlock hN).norm.integrable_sq
  have hlocal : (∫ t in Ioc (1 / (4 * (N : ℝ))) (1 / (3 * (N : ℝ))),
      ‖pmFermiPositiveBlock N t‖ ^ 2) = ((N : ℝ) + 1) ^ 2 / (12 * N) := by
    have hval (t : ℝ) (ht : t ∈ Ioc (1 / (4 * (N : ℝ))) (1 / (3 * (N : ℝ)))) :
        ‖pmFermiPositiveBlock N t‖ ^ 2 = ((N : ℝ) + 1) ^ 2 := by
      rw [pmFermiPositiveBlock_first_band hN ht, norm_neg]
      norm_cast
    rw [setIntegral_congr_fun measurableSet_Ioc hval]
    rw [← intervalIntegral.integral_of_le hband, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hle := setIntegral_mono_set
    (s := Ioc (1 / (4 * (N : ℝ))) (1 / (3 * (N : ℝ)))) hint
    (Eventually.of_forall fun t => sq_nonneg ‖pmFermiPositiveBlock N t‖)
    (Eventually.of_forall fun t (ht : t ∈ Ioc (1 / (4 * (N : ℝ))) (1 / (3 * (N : ℝ)))) =>
      (show (0 : ℝ) < 1 / (4 * N) by positivity).trans ht.1)
  rw [hlocal] at hle
  have hbase : (N : ℝ) / 12 ≤ ((N : ℝ) + 1) ^ 2 / (12 * N) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  exact hbase.trans hle

theorem pmFermiPositiveBlock_diagonal_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc (2 * N) (3 * N),
      ∫ t in Ioi (0 : ℝ), ‖fermiNymanGen (d : ℝ) t‖ ^ 2) ≤ Real.log 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcard : (Finset.Icc (2 * N) (3 * N)).card = N + 1 := by
    rw [Nat.card_Icc]
    omega
  calc
    _ ≤ ∑ _d ∈ Finset.Icc (2 * N) (3 * N), Real.log 2 / (2 * N) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdlo : 2 * (N : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      rw [pm_integral_normSq_fermiNymanGen (by linarith : (0 : ℝ) < d)]
      exact div_le_div_of_nonneg_left hlog (by positivity) hdlo
    _ = ((N : ℝ) + 1) * (Real.log 2 / (2 * N)) := by
      rw [Finset.sum_const, hcard]
      simp
    _ ≤ Real.log 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith

/-- Even contiguous positive blocks violate every fixed diagonal-only synthesis ceiling. -/
theorem pmFermiPositiveBlock_no_uniform_diagonal_bound :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      (∫ t in Ioi (0 : ℝ), ‖pmFermiPositiveBlock N t‖ ^ 2) ≤
        C * (∑ d ∈ Finset.Icc (2 * N) (3 * N),
          ∫ t in Ioi (0 : ℝ), ‖fermiNymanGen (d : ℝ) t‖ ^ 2) := by
  rintro ⟨C, hC, hbound⟩
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (12 * C * Real.log 2 + 1)
  have hN1 : 1 ≤ N := by
    have hp : 0 ≤ 12 * C * Real.log 2 := by positivity
    have hn : (1 : ℝ) < N := by linarith
    have : 1 < N := by exact_mod_cast hn
    omega
  have he := (pmFermiPositiveBlock_energy_lower hN1).trans ((hbound N hN1).trans
    (mul_le_mul_of_nonneg_left (pmFermiPositiveBlock_diagonal_le hN1) hC))
  linarith

end RHTower
