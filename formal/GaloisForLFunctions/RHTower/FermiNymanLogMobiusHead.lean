import GaloisForLFunctions.RHTower.FermiNymanRawMobiusTailFloor

/-!
# The exact Chebyshev head of logarithmically smoothed Fermi approximation

For `N ≥ 2`, use the literal coefficients `μ(d) log(N/d)/log N` in the actual Fermi
combination. On `1/(N+1) < t ≤ 1`, its Haar error is exactly
`[2 ψ(1/(2t)) - ψ(1/t)] / log N`.

The arithmetic input is finite logarithmic Möbius floor inversion, extended from
integer cells to real arguments. The reciprocal harmonic term cancels in the Fermi
difference. The full squared error splits exactly into the unchanged small-`t` tail
and the normalized dyadic Chebyshev head energy. Measurability and integrability are
proved for the literal combination before that split.

This is an exact source identity. Neither source-energy term is shown to tend to zero;
no zero-location or zero-simplicity hypothesis is assumed.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.NymanMellin
open ArithmeticFunction
noncomputable section
namespace RHTower

/-- Real floor division is constant throughout each unit cell. -/
theorem real_floor_div_eq_nat_div (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (⌊x / (d : ℝ)⌋ : ℝ) = ((⌊x⌋₊ / d : ℕ) : ℝ) := by
  rw [← Nat.floor_div_natCast]
  exact_mod_cast (Int.natCast_floor_eq_floor (div_nonneg hx (Nat.cast_nonneg d))).symm

/-- Extending the coefficient cutoff beyond the real floor adds only zero terms. -/
theorem sum_mul_floor_truncated (c : ℕ → ℝ) (N : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hN : ⌊x⌋₊ ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, c d * (⌊x / (d : ℝ)⌋ : ℝ)) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * (⌊x / (d : ℝ)⌋ : ℝ) := by
  apply (Finset.sum_subset (Finset.Icc_subset_Icc_right hN) ?_).symm
  intro d hd hnot
  have hdgt : ⌊x⌋₊ < d := by
    by_contra h
    exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, le_of_not_gt h⟩)
  rw [real_floor_div_eq_nat_div d hx, Nat.div_eq_of_lt hdgt]
  simp

/-- Logarithmic Möbius floor inversion at a real argument. -/
theorem sum_moebius_log_mul_floor (N : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hN : ⌊x⌋₊ ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) *
      (⌊x / (d : ℝ)⌋ : ℝ)) = -Chebyshev.psi x := by
  rw [sum_mul_floor_truncated _ N hx hN]
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum mu_log ⌊x⌋₊
  rw [mu_log_mul_zeta] at h
  simp only [ArithmeticFunction.neg_apply, Finset.sum_neg_distrib] at h
  have hsets : Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ := by
    ext d
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  unfold Chebyshev.psi
  rw [hsets] at h ⊢
  rw [h]
  apply Finset.sum_congr rfl
  intro d hd
  rw [real_floor_div_eq_nat_div d hx, mu_log_apply]
  rfl

/-- The linear logarithmic coefficient turns the finite floor transform into Chebyshev mass. -/
theorem sum_moebius_log_div_mul_floor (N : ℕ) (hN0 : 1 ≤ N) {x : ℝ} (hx : 0 ≤ x)
    (hN : ⌊x⌋₊ ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) *
      (⌊x / (d : ℝ)⌋ : ℝ)) = Real.log N * (if 1 ≤ x then 1 else 0) + Chebyshev.psi x := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN0)
  calc
    (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) *
      (⌊x / (d : ℝ)⌋ : ℝ)) =
      Real.log N * ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * (⌊x / (d : ℝ)⌋ : ℝ) -
        ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * Real.log d * (⌊x / (d : ℝ)⌋ : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : (d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hd).1)
      rw [Real.log_div hn hd0]
      ring
    _ = _ := by
      rw [sum_moebius_floor_truncated N hx hN, sum_moebius_log_mul_floor N hx hN]
      ring

/-- The logarithmically smoothed literal Fermi combination. -/
def logMobiusFermiApprox (N : ℕ) (t : ℝ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 N,
    ((((moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) / Real.log N : ℝ) : ℂ) *
      fermiNymanGen (d : ℝ) t)

theorem fermiNymanGen_eq_floor_difference (a t : ℝ) :
    fermiNymanGen a t =
      ((2 * (⌊(1 / (2 * t)) / a⌋ : ℝ) - (⌊(1 / t) / a⌋ : ℝ) : ℝ) : ℂ) := by
  unfold fermiNymanGen nymanGen Int.fract
  rw [show 1 / (a * t) = (1 / t) / a by ring,
    show 1 / (2 * a * t) = (1 / (2 * t)) / a by ring]
  push_cast
  ring

theorem logMobiusFermiApprox_eq_floor_sums (N : ℕ) (t : ℝ) :
    logMobiusFermiApprox N t =
      (((∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) *
          (⌊(1 / t) / d⌋ : ℝ)) -
        2 * (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) *
          (⌊(1 / (2 * t)) / d⌋ : ℝ))) / Real.log N : ℝ) := by
  unfold logMobiusFermiApprox
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_neg_distrib]
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  rw [fermiNymanGen_eq_floor_difference]
  push_cast
  ring

/-- Exact continuous head error of the logarithmically smoothed Fermi sequence. -/
theorem dyadicHaar_sub_logMobiusFermiApprox (N : ℕ) (hN : 2 ≤ N) {t : ℝ}
    (ht : 1 / ((N : ℝ) + 1) < t) (ht1 : t ≤ 1) :
    dyadicHaar t - logMobiusFermiApprox N t =
      (((2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) /
        Real.log N : ℝ) : ℂ) := by
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N + 1 := by positivity
  have ht0 : 0 < t := lt_trans (one_div_pos.mpr hNp) ht
  have hlogR : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlog : (Real.log (N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogR.ne'
  have hcut : ∀ u : ℝ, 1 / ((N : ℝ) + 1) < u → ⌊1 / u⌋₊ ≤ N := by
    intro u hu
    have hu0 : 0 < u := lt_trans (one_div_pos.mpr hNp) hu
    have hx : 0 ≤ 1 / u := by positivity
    have hxN : 1 / u < (N : ℝ) + 1 := by
      apply (div_lt_iff₀ hu0).mpr
      have h := (div_lt_iff₀ hNp).mp hu
      nlinarith
    have h : (⌊1 / u⌋₊ : ℝ) < (N : ℝ) + 1 := lt_of_le_of_lt (Nat.floor_le hx) hxN
    exact Nat.le_of_lt_succ (by exact_mod_cast h)
  rw [logMobiusFermiApprox_eq_floor_sums,
    sum_moebius_log_div_mul_floor N hN1 (by positivity) (hcut t ht),
    sum_moebius_log_div_mul_floor N hN1 (by positivity) (hcut (2 * t) (by linarith))]
  have hx1 : 1 ≤ 1 / t := (le_div_iff₀ ht0).mpr (by simpa using ht1)
  rw [if_pos hx1]
  by_cases hh : t ≤ 1 / 2
  · have hy1 : 1 ≤ 1 / (2 * t) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    rw [dyadicHaar, if_pos hh, if_pos hy1]
    push_cast at hlog ⊢
    field_simp [hlog]
    ring
  · have hy1 : ¬1 ≤ 1 / (2 * t) := by
      rw [le_div_iff₀ (by positivity : 0 < 2 * t)]
      intro h
      apply hh
      linarith
    rw [dyadicHaar, if_neg hh, if_neg hy1]
    push_cast at hlog ⊢
    field_simp [hlog]
    ring

theorem measurable_logMobiusFermiApprox (N : ℕ) : Measurable (logMobiusFermiApprox N) := by
  unfold logMobiusFermiApprox
  exact (Finset.measurable_sum _ (fun d _ =>
    measurable_const.mul (measurable_fermiNymanGen _))).neg

theorem norm_logMobiusFermiApprox_le (N : ℕ) (t : ℝ) :
    ‖logMobiusFermiApprox N t‖ ≤
      ∑ d ∈ Finset.Icc 1 N,
        ‖((((moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) / Real.log N : ℝ) : ℂ)‖ * 3 := by
  unfold logMobiusFermiApprox
  rw [norm_neg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_fermiNymanGen_le _ _) (norm_nonneg _)

theorem integrableOn_normSq_dyadicHaar_sub_logMobiusFermiApprox (N : ℕ) :
    IntegrableOn (fun t => ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2) (Ioc (0 : ℝ) 1) := by
  refine Measure.integrableOn_of_bounded
    (M := (1 + ∑ d ∈ Finset.Icc 1 N,
      ‖((((moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) / Real.log N : ℝ) : ℂ)‖ * 3) ^ 2)
    measure_Ioc_lt_top.ne
    ((measurable_dyadicHaar.sub (measurable_logMobiusFermiApprox N)).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  refine (norm_sub_le _ _).trans ?_
  rw [norm_dyadicHaar]
  exact add_le_add le_rfl (norm_logMobiusFermiApprox_le N t)

def logMobiusFermiErrorEnergy (N : ℕ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2

/-- Exact separation of the unresolved small-`t` tail and the dyadic Chebyshev head energy. -/
theorem logMobiusFermiErrorEnergy_decomposition (N : ℕ) (hN : 2 ≤ N) :
    logMobiusFermiErrorEnergy N =
      (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
        ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2) +
      (1 / Real.log (N : ℝ) ^ 2) *
        ∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
          (2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) ^ 2 := by
  have hc0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hi := integrableOn_normSq_dyadicHaar_sub_logMobiusFermiApprox N
  have hleft := hi.mono_set (Ioc_subset_Ioc le_rfl hc1)
  have hright := hi.mono_set (Ioc_subset_Ioc hc0 le_rfl)
  rw [logMobiusFermiErrorEnergy, ← Ioc_union_Ioc_eq_Ioc hc0 hc1,
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hleft hright]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  change ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2 = _
  rw [dyadicHaar_sub_logMobiusFermiApprox N hN ht.1 ht.2,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
  ring

end RHTower
