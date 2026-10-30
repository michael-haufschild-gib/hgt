import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilFormIsDiagonalOnFiniteRamanujanPackets

/-!
# A prime-defect certificate must retain low-energy conductors

An omitted Ramanujan conductor supplies actual unit horizon vectors whose
coordinates on the retained family vanish. Their prime defect is bounded
by the conductor's adjunction energy plus a fixed row counterterm. Powers
of two therefore force an exponential cutoff for defect-only certificates.
-/

noncomputable section
open Filter Topology Finset
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open ArithmeticElectrostatics ArithmeticEffectivityTheory ArithmeticIntersectionTheory

/-- The actual Ramanujan vector with unit Euclidean normalization when nonzero. -/
def unitRamanujanHorizonVector (m N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ‖normalizedRamanujanHorizonVector m N‖⁻¹ • normalizedRamanujanHorizonVector m N

private theorem unitRamanujanHorizonVector_norm_of_pos {m N : ℕ}
    (h : 0 < ‖normalizedRamanujanHorizonVector m N‖) :
    ‖unitRamanujanHorizonVector m N‖ = 1 := by
  rw [unitRamanujanHorizonVector, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ h.ne']

private theorem tendsto_unitRamanujanHorizonVector_norm {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N => ‖unitRamanujanHorizonVector m N‖) atTop (𝓝 1) := by
  have hv := tendsto_normalizedRamanujanHorizonVector_norm hm
  have h := (hv.inv₀ one_ne_zero).mul hv
  simpa only [unitRamanujanHorizonVector, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_one, one_mul] using h

private theorem tendsto_unitRamanujanHorizonVector_residual_norm {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N =>
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (unitRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • unitRamanujanHorizonVector m N‖)
      atTop (𝓝 0) := by
  have hv := tendsto_normalizedRamanujanHorizonVector_norm hm
  have hr := tendsto_normalizedRamanujanHorizonVector_residual_norm hm
  have h := (hv.inv₀ one_ne_zero).mul hr
  have he (N : ℕ) :
      Matrix.toEuclideanLin (fullPrimeMatrix N) (unitRamanujanHorizonVector m N) -
          (Real.log N - ramanujanAdjunctionEnergy m) • unitRamanujanHorizonVector m N =
      ‖normalizedRamanujanHorizonVector m N‖⁻¹ •
        (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
          (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N) := by
    rw [unitRamanujanHorizonVector, map_smul,
      smul_comm (Real.log N - ramanujanAdjunctionEnergy m) ‖normalizedRamanujanHorizonVector m N‖⁻¹,
      ← smul_sub]
  simpa only [he, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_one, one_mul] using h

/-- Unit normalization preserves the exact adjunction energy limit. -/
theorem tendsto_unitRamanujanHorizonVector_primeEnergy {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N => renormalizedPrimeEnergy N (unitRamanujanHorizonVector m N))
      atTop (𝓝 (ramanujanAdjunctionEnergy m)) := by
  have hv := tendsto_unitRamanujanHorizonVector_norm hm
  have hp := tendsto_horizon_inner_zero_of_norm
    (fun N => Matrix.toEuclideanLin (fullPrimeMatrix N) (unitRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • unitRamanujanHorizonVector m N)
    (unitRamanujanHorizonVector m) (tendsto_unitRamanujanHorizonVector_residual_norm hm) hv
  have h := ((hv.pow 2).const_mul (ramanujanAdjunctionEnergy m)).sub hp
  have he (N : ℕ) : renormalizedPrimeEnergy N (unitRamanujanHorizonVector m N) =
      ramanujanAdjunctionEnergy m * ‖unitRamanujanHorizonVector m N‖ ^ 2 -
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (unitRamanujanHorizonVector m N) -
          (Real.log N - ramanujanAdjunctionEnergy m) • unitRamanujanHorizonVector m N,
          unitRamanujanHorizonVector m N⟫ := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    unfold renormalizedPrimeEnergy
    ring
  simpa only [← he, one_pow, mul_one, sub_zero] using h

/-- The row counterterm compares the actual defect with renormalized prime energy at every horizon. -/
theorem poleDefect_le_primeEnergy_add_row_cost {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    poleDefect N (primeHorizonExtension x) ≤
      renormalizedPrimeEnergy N x + (Real.log 4 + 4) * ‖x‖ ^ 2 := by
  have hrow : atomicWeilForm N (primeHorizonExtension x) + poleDefect N (primeHorizonExtension x) ≤
      (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, primeHorizonExtension x n ^ 2 := by
    rw [atomicWeilForm_add_poleDefect, mul_sum]
    exact sum_le_sum fun n hn => mul_le_mul_of_nonneg_right
      (row_le (mem_Icc.mp hn).1 (mem_Icc.mp hn).2) (sq_nonneg _)
  rw [sum_primeHorizonExtension_sq, atomicWeilForm_primeHorizonExtension] at hrow
  unfold renormalizedPrimeEnergy
  linarith only [hrow]

/-- Unit conductor vectors retain the identity Gram limit against the logarithmic normalization. -/
theorem tendsto_unitRamanujanHorizonVector_coordinate {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N => ⟪unitRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫)
      atTop (𝓝 (if m = l then 1 else 0)) := by
  have hv := tendsto_normalizedRamanujanHorizonVector_norm hm
  have h := (hv.inv₀ one_ne_zero).mul (tendsto_normalizedRamanujanHorizonVector_gram hm hl)
  simpa only [unitRamanujanHorizonVector, real_inner_smul_left, inv_one, one_mul] using h

/-- Every omitted conductor supplies actual bounded-defect unit vectors escaping the retained coordinates. -/
theorem eventually_exists_unit_vector_escaping_conductors
    (S : Finset ℕ) (hS : ∀ l ∈ S, 0 < l) {m : ℕ} (hm : 0 < m) (hmS : m ∉ S)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ‖x‖ = 1 ∧ poleDefect N (primeHorizonExtension x) ≤
        ramanujanAdjunctionEnergy m + (Real.log 4 + 4) + ε ∧
      (∑ l ∈ S, ⟪x, normalizedRamanujanHorizonVector l N⟫ ^ 2) < ε := by
  have hnorm : ∀ᶠ N : ℕ in atTop, 0 < ‖normalizedRamanujanHorizonVector m N‖ :=
    (tendsto_normalizedRamanujanHorizonVector_norm hm).eventually (lt_mem_nhds zero_lt_one)
  have henergy : ∀ᶠ N : ℕ in atTop,
      renormalizedPrimeEnergy N (unitRamanujanHorizonVector m N) < ramanujanAdjunctionEnergy m + ε :=
    (tendsto_unitRamanujanHorizonVector_primeEnergy hm).eventually
      (gt_mem_nhds (lt_add_of_pos_right _ hε))
  have hcoord : Tendsto (fun N =>
      ∑ l ∈ S, ⟪unitRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ ^ 2)
      atTop (𝓝 0) := by
    have hi : ∀ l ∈ S, Tendsto (fun N =>
        ⟪unitRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ ^ 2)
        atTop (𝓝 0) := by
      intro l hl
      have hml : m ≠ l := fun he => hmS (he.symm ▸ hl)
      simpa only [if_neg hml, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        (tendsto_unitRamanujanHorizonVector_coordinate hm (hS l hl)).pow 2
    simpa only [sum_const_zero] using tendsto_finsetSum S hi
  filter_upwards [hnorm, henergy, hcoord.eventually (gt_mem_nhds hε)] with N hn he hc
  have hunit := unitRamanujanHorizonVector_norm_of_pos hn
  refine ⟨unitRamanujanHorizonVector m N, hunit, ?_, hc⟩
  have hd := poleDefect_le_primeEnergy_add_row_cost (unitRamanujanHorizonVector m N)
  rw [hunit, one_pow, mul_one] at hd
  linarith only [hd, he]

/-- Binary conductor powers have exactly linear adjunction energy in the exponent. -/
theorem ramanujanAdjunctionEnergy_two_pow {k : ℕ} (hk : 1 ≤ k) :
    ramanujanAdjunctionEnergy (2 ^ k) = Real.eulerMascheroniConstant + (k + 1) * Real.log 2 := by
  rw [ramanujanAdjunctionEnergy, tameDifferent_prime_pow Nat.prime_two (by omega),
    Nat.cast_pow, Real.log_pow]
  norm_num
  ring

/-- A cutoff below `2^k` misses unit vectors with prime defect only linear in `k`. -/
theorem eventually_exists_unit_vector_escaping_binary_cutoff {k Q : ℕ}
    (hk : 1 ≤ k) (hQ : Q < 2 ^ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ‖x‖ = 1 ∧ poleDefect N (primeHorizonExtension x) ≤
        Real.eulerMascheroniConstant + (k + 1) * Real.log 2 + Real.log 4 + 5 ∧
      (∑ l ∈ Icc 1 Q, ⟪x, normalizedRamanujanHorizonVector l N⟫ ^ 2) < ε := by
  have hm : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) _
  have hmS : (2 : ℕ) ^ k ∉ Icc 1 Q := by simp only [mem_Icc]; omega
  have h := eventually_exists_unit_vector_escaping_conductors (Icc 1 Q)
    (fun l hl => (mem_Icc.mp hl).1) hm hmS (lt_min hε zero_lt_one)
  filter_upwards [h] with N hN
  obtain ⟨x, hx, hd, hc⟩ := hN
  refine ⟨x, hx, ?_, hc.trans_le (min_le_left _ _)⟩
  rw [ramanujanAdjunctionEnergy_two_pow hk] at hd
  have hmin := min_le_right ε (1 : ℝ)
  linarith only [hd, hmin]

/-- Defect alone cannot give uniform coordinate capture below its exponential conductor scale. -/
theorem not_eventually_defect_coordinate_capture_below_binary_cutoff {k Q : ℕ}
    (hk : 1 ≤ k) (hQ : Q < 2 ^ k) {δ : ℝ} (hδ : 0 < δ) :
    ¬ (∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ‖x‖ = 1 → poleDefect N (primeHorizonExtension x) ≤
        Real.eulerMascheroniConstant + (k + 1) * Real.log 2 + Real.log 4 + 5 →
      δ ≤ ∑ l ∈ Icc 1 Q, ⟪x, normalizedRamanujanHorizonVector l N⟫ ^ 2) := by
  intro hcapture
  obtain ⟨N, hN, x, hx, hd, hc⟩ :=
    (hcapture.and (eventually_exists_unit_vector_escaping_binary_cutoff hk hQ hδ)).exists
  exact (not_lt_of_ge (hN x hx hd)) hc

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.tendsto_unitRamanujanHorizonVector_primeEnergy
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.eventually_exists_unit_vector_escaping_conductors
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.eventually_exists_unit_vector_escaping_binary_cutoff
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.not_eventually_defect_coordinate_capture_below_binary_cutoff
