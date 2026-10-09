import GaloisForLFunctions.RHTower.WeilLogShiftDomainBoundary
import GaloisForLFunctions.RHTower.WeilLogShiftReflection

/-!
# Arithmetic realization of convergence domains and sharp sampling

Every weight sequence lifts to arithmetic coefficients with the same potential
domain. Nonnegative weights give both zero-deficit majorants and zero-excess
minorants. Thus every finite open or closed symmetric domain is attainable.
Cofinality is exactly the universal sampling condition even for zero excess:
any bounded probe family misses a minorant whose unsampled probes diverge.
-/

open Filter Topology Zeta23 Real

noncomputable section

namespace RHTower

open WeilExcess

/-- Arithmetic coefficients realizing a weight, up to the two forced zero
coordinates of normalized deviation. -/
def weilCoefficientLift (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) + sqrt n * v n

theorem weilDeviation_coefficientLift (v : ℕ → ℝ) (n : ℕ) :
    weilDeviation (weilCoefficientLift v) n = if 2 ≤ n then v n else 0 := by
  by_cases hn : 2 ≤ n
  · have hsqrt : sqrt (n : ℝ) ≠ 0 :=
      (sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))).ne'
    simp only [weilDeviation, weilCoefficientLift, if_pos hn]
    calc ((ArithmeticFunction.vonMangoldt n : ℝ) + sqrt n * v n -
        ArithmeticFunction.vonMangoldt n) / sqrt n = v n * (sqrt n / sqrt n) := by ring
      _ = v n := by rw [div_self hsqrt, mul_one]
  · simp only [weilDeviation, if_neg hn]

/-- The forced finite head has no effect on the real-shift convergence domain. -/
theorem summable_coefficientLift_potential_iff (v : ℕ → ℝ) (y : ℝ) :
    (Summable fun n => weilDeviation (weilCoefficientLift v) n * pairedLogKernel y n) ↔
      Summable (fun n => v n * pairedLogKernel y n) := by
  simp only [weilDeviation_coefficientLift]
  rw [← summable_nat_add_iff 2 (f := fun n => (if 2 ≤ n then v n else 0) *
    pairedLogKernel y n),
    ← summable_nat_add_iff 2 (f := fun n => v n * pairedLogKernel y n)]
  simp

/-- Every nonnegative weight domain is attained by a majorant with zero deficit. -/
theorem exists_majorant_with_weight_potential_domain (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n) :
    ∃ lam : ℕ → ℝ,
      (∀ n, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) ∧
      (∀ n, deviationDeficit lam n = 0) ∧
      ∀ y : ℝ, (Summable fun n => weilDeviation lam n * pairedLogKernel y n) ↔
        Summable (fun n => v n * pairedLogKernel y n) := by
  refine ⟨weilCoefficientLift v, ?_, ?_, summable_coefficientLift_potential_iff v⟩
  · intro n
    exact le_add_of_nonneg_right (mul_nonneg (sqrt_nonneg _) (hv n))
  · intro n
    rw [deviationDeficit, weilDeviation_coefficientLift]
    split_ifs
    · exact max_eq_right (neg_nonpos.mpr (hv n))
    · simp

/-- Every nonnegative weight domain is attained by a minorant with zero excess. -/
theorem exists_minorant_with_weight_potential_domain (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n) :
    ∃ lam : ℕ → ℝ,
      (∀ n, lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) ∧
      (∀ n, deviationExcess lam n = 0) ∧
      ∀ y : ℝ, (Summable fun n => weilDeviation lam n * pairedLogKernel y n) ↔
        Summable (fun n => v n * pairedLogKernel y n) := by
  refine ⟨weilCoefficientLift (fun n => -v n), ?_, ?_, ?_⟩
  · intro n
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos
      (sqrt_nonneg _) (neg_nonpos.mpr (hv n)))
  · intro n
    rw [deviationExcess, weilDeviation_coefficientLift]
    split_ifs
    · exact max_eq_right (neg_nonpos.mpr (hv n))
    · simp
  · intro y
    rw [summable_coefficientLift_potential_iff]
    constructor <;> intro hs <;> simpa only [neg_mul, neg_neg] using hs.neg

/-- Every finite open symmetric potential domain occurs for a zero-excess
arithmetic minorant, including the empty domain at radius zero. -/
theorem exists_minorant_with_open_potential_domain (R : ℝ) (hR : 0 ≤ R) :
    ∃ lam : ℕ → ℝ,
      (∀ n, lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) ∧
      (∀ n, deviationExcess lam n = 0) ∧
      ∀ y : ℝ, (Summable fun n => weilDeviation lam n * pairedLogKernel y n) ↔
        |y| < R := by
  obtain ⟨v, hv, hd⟩ := exists_nonneg_weight_with_open_potential_domain R hR
  obtain ⟨lam, hminor, hexc, hlift⟩ := exists_minorant_with_weight_potential_domain v hv
  exact ⟨lam, hminor, hexc, fun y => (hlift y).trans (hd y)⟩

/-- Every finite closed symmetric potential domain occurs for a zero-excess
arithmetic minorant, including the singleton origin at radius zero. -/
theorem exists_minorant_with_closed_potential_domain (R : ℝ) (hR : 0 ≤ R) :
    ∃ lam : ℕ → ℝ,
      (∀ n, lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) ∧
      (∀ n, deviationExcess lam n = 0) ∧
      ∀ y : ℝ, (Summable fun n => weilDeviation lam n * pairedLogKernel y n) ↔
        |y| ≤ R := by
  obtain ⟨v, hv, hd⟩ := exists_nonneg_weight_with_closed_potential_domain R hR
  obtain ⟨lam, hminor, hexc, hlift⟩ := exists_minorant_with_weight_potential_domain v hv
  exact ⟨lam, hminor, hexc, fun y => (hlift y).trans (hd y)⟩

/-- Every finite open symmetric domain also occurs on the opposite side of
von Mangoldt, with identically zero deficit. -/
theorem exists_majorant_with_open_potential_domain (R : ℝ) (hR : 0 ≤ R) :
    ∃ lam : ℕ → ℝ,
      (∀ n, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) ∧
      (∀ n, deviationDeficit lam n = 0) ∧
      ∀ y : ℝ, (Summable fun n => weilDeviation lam n * pairedLogKernel y n) ↔
        |y| < R := by
  obtain ⟨v, hv, hd⟩ := exists_nonneg_weight_with_open_potential_domain R hR
  obtain ⟨lam, hmajor, hdef, hlift⟩ := exists_majorant_with_weight_potential_domain v hv
  exact ⟨lam, hmajor, hdef, fun y => (hlift y).trans (hd y)⟩

/-- Every finite closed symmetric domain occurs for a zero-deficit majorant. -/
theorem exists_majorant_with_closed_potential_domain (R : ℝ) (hR : 0 ≤ R) :
    ∃ lam : ℕ → ℝ,
      (∀ n, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) ∧
      (∀ n, deviationDeficit lam n = 0) ∧
      ∀ y : ℝ, (Summable fun n => weilDeviation lam n * pairedLogKernel y n) ↔
        |y| ≤ R := by
  obtain ⟨v, hv, hd⟩ := exists_nonneg_weight_with_closed_potential_domain R hR
  obtain ⟨lam, hmajor, hdef, hlift⟩ := exists_majorant_with_weight_potential_domain v hv
  exact ⟨lam, hmajor, hdef, fun y => (hlift y).trans (hd y)⟩

private theorem log_nat_nonneg (m : ℕ) : 0 ≤ log (m : ℝ) := by
  by_cases hm : m = 0
  · simp [hm]
  · exact log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))

private theorem lower_bound_of_real_limit {f : ℝ → ℝ} {d : ℝ}
    (h : Tendsto f atTop (𝓝 d)) :
    ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → b ≤ f k := by
  have ht := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hev := (tendsto_order.mp ht).1 (d - 1) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨d - 1, N, fun k hk => (hN k hk).le⟩

/-- Any bounded family has finite actual-probe limits for a zero-excess
minorant whose potential diverges at another integer log and whose actual
probe there tends to minus infinity. Sampled indices zero and one are allowed. -/
theorem bounded_logShift_family_misses_minorant_divergence
    (m : ℕ → ℕ) (hbounded : ∃ B : ℝ, ∀ j : ℕ, log (m j : ℝ) ≤ B) :
    ∃ lam : ℕ → ℝ,
      (∀ n, lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) ∧
      (∀ n, deviationExcess lam n = 0) ∧
      (∀ j : ℕ, Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference L (log (m j)))
        (logShiftRiemannDifference L (log (m j))))).re) atTop
          (𝓝 (2 * (deviationPotential lam (log (m j)) - deviationPotential lam 0)))) ∧
      (∀ j : ℕ, ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        b ≤ (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference k (log (m j)))
          (logShiftRiemannDifference k (log (m j))))).re) ∧
      ∃ q : ℕ, 2 ≤ q ∧
        (¬ Summable fun n => weilDeviation lam n * pairedLogKernel (log q) n) ∧
        Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference L (log q))
          (logShiftRiemannDifference L (log q)))).re) atTop atBot := by
  obtain ⟨B, hB⟩ := hbounded
  let R := max B 0
  have hR : 0 ≤ R := le_max_right _ _
  obtain ⟨lam, hminor, hexc, hd⟩ := exists_minorant_with_closed_potential_domain R hR
  have hs0 : Summable fun n => weilDeviation lam n * pairedLogKernel 0 n :=
    (hd 0).mpr (by simpa only [abs_zero] using hR)
  have hs (j : ℕ) : Summable fun n =>
      weilDeviation lam n * pairedLogKernel (log (m j)) n := by
    apply (hd _).mpr
    rw [abs_of_nonneg (log_nat_nonneg _)]
    exact (hB j).trans (le_max_left _ _)
  have hlim (j : ℕ) := tendsto_logShift_probe_of_summable_potential (m j) hs0 (hs j)
  refine ⟨lam, hminor, hexc, hlim, fun j => lower_bound_of_real_limit (hlim j), ?_⟩
  obtain ⟨r, hr⟩ := exists_nat_gt R
  let q := ⌊exp (r : ℝ)⌋₊ + 1
  have hq := integer_log_probe_bounds r
  have hlog : R < log (q : ℝ) := hr.trans_le hq.2.1
  have hbad : ¬ Summable fun n => weilDeviation lam n * pairedLogKernel (log q) n := by
    intro hsum
    have hle := (hd (log q)).mp hsum
    rw [abs_of_nonneg (log_nat_nonneg q)] at hle
    exact (not_le_of_gt hlog) hle
  refine ⟨q, hq.1, hbad, ?_⟩
  apply tendsto_logShift_probe_atBot_of_nonsummable_sample_of_local_excess hq.1 _ hbad
  simpa only [hexc, zero_mul] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

/-- Cofinality is necessary and sufficient for universal recovery of the
whole potential domain from eventual lower bounds on sampled actual probes,
already in the class of identically zero positive excess. -/
theorem cofinal_iff_zero_excess_probe_sampling (m : ℕ → ℕ) :
    (∀ R : ℝ, ∃ j : ℕ, R ≤ log (m j : ℝ)) ↔
      ∀ lam : ℕ → ℝ, (∀ n, deviationExcess lam n = 0) →
        (∀ j : ℕ, ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          b ≤ (weilFullFunctional lam (EF.weilTest
            (logShiftRiemannDifference k (log (m j)))
            (logShiftRiemannDifference k (log (m j))))).re) →
        ∀ y : ℝ, Summable fun n => weilDeviation lam n * pairedLogKernel y n := by
  constructor
  · intro hcofinal lam hexc hbounded
    apply (summable_potential_iff_cofinal_local_excess_and_probe_lower_bounds m hcofinal).mpr
    refine ⟨?_, hbounded⟩
    intro y
    simpa only [hexc, zero_mul] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  · intro hsampling
    by_contra hnot
    push Not at hnot
    obtain ⟨B, hB⟩ := hnot
    obtain ⟨lam, _, hexc, _, hbounds, q, _, hbad, _⟩ :=
      bounded_logShift_family_misses_minorant_divergence m ⟨B, fun j => (hB j).le⟩
    exact hbad (hsampling lam hexc hbounds (log q))

end RHTower
