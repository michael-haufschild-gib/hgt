import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LinearConductorRelativeResiduals

/-!
# Quadratic-overlap complete-Weil conductor residuals

This module sharpens the overlap dependence across all eight channels of the exact complete-Weil
Ramanujan residual decomposition `completeWeilMatrix_ramanujan_residual_eq_at_every_overlap` from
fifth-power `O(c^5)` to quadratic `O(c^2 * (1 + log c)^3 * (log N)^(1/k))` (up to `O(c^10 (log N / N)^2)`):

1. **Separated archimedean cross error (`c^4 → c^2`).**
   For pairs `2c/N < |log j - log n|` in the moderate collar `n ≤ 2j ∧ j ≤ 2n`, integer distance
   exceeds `max 1 ⌈c n / N⌉₊`, so the reciprocal-square tail sums to `O(N / (c n))` rather than `O(1)`,
   saving a factor of `c` in row `L¹` and `c^2` in squared norm.
2. **Polar moment error (`c^4 / log N → c^10 (log N / N)^2`).**
   Factoring the rank-two polar error kernel into `√n ∑ a(j)/j + (1/√n) ∑ a(j)` retains `(c/N)^4`
   against `O(N^2 (1 + log N)^2)` row mass rather than inflating `a(j)/j` to `O(1)`.
3. **Near-center replacement (`c^5 → c^2 (1 + log c)^3`).**
   Pointwise `archLevyDensity |log j - log n| ≤ (1 + e^{1/2}) N / |j - n|` sums harmonically over
   `j ∈ nearRowIndices c N n` to `O(c (1 + log c) / √n)` on the active quotient strip `N / n ≤ R_c`,
   summing via `HTGeometry.sum_sq_le_harmonic_quotient_tail` to `O(m c^2 (1 + log c)^3)`.
4. **Near-Gamma downward source (`c^5 → c^2 (1 + log c)^2`).**
   Bounding `log(N/j) ≤ log R_c` instead of `R_c` gives `O(φ(m)(1 + log m)(1 + log c))` entries, while
   the row-proportional near-collar width `|j - n| ≤ R_c n / N` gives `O(R_c^2 n / N^2)` row squares.
   In the exterior boundary strip `N < ℓ ≤ exteriorPrimeCutoff c N`, keeping `log ℓ / √ℓ ≪ log N / √N`
   suppresses the exterior boundary term to `O(c^3 log N / N)`.
5. **Upward prime source (`c^5 + c^3 (log N)^(1/k) → c^2 (1 + log c) (log N)^(1/k)`).**
   In `shiftedReciprocalUpwardRowError`, `log(2T) = log(4c) + (log N)^(1/k)` avoids `log(4c) ≤ 4c`.
   In `linearizedUpwardCoefficient - reciprocalUpwardCoefficient`, restricting to the exact discrepancy
   set `N ≤ k n + B ∧ k n ≤ N + B` leaves at most `3` indices `k` for `n > B` with `Λ(k)/k ≪ √(n/N)`,
   canceling `1/√n` and reducing the squared norm from `O(c^5)` to `O(c^2 + c^10 (log N / N)^2)`.

Combining the quadratic single-mode residual with `sum_linear_conductor_relative_weights_le` yields the
summed relative residual bound `O((c^14 + Q^2)(1 + log Q)^2 * rate)` with total low-conductor overlap
exponent `14 + 2 = 16`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace Matrix Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence

/-! ## Section 1: Normalization and Elementary Tail Lemmas -/

private theorem abs_mode_le_sqrt_conductor_quad {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |normalizedRamanujanMode m n| ≤ Real.sqrt (m : ℝ) :=
  (SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient hm n).trans
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le m))

private theorem normalized_action_sq_quad (N m : ℕ)
    (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) :
    ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N)‖ ^ 2 =
      ‖Matrix.toEuclideanLin A (ramanujanHorizonVector m N)‖ ^ 2 / Real.log N := by
  rw [normalizedRamanujanHorizonVector, map_smul, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  ring

private theorem normalized_residual_sq_quad (N m : ℕ)
    (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) (e : ℝ) :
    ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
      e • normalizedRamanujanHorizonVector m N‖ ^ 2 =
      ‖Matrix.toEuclideanLin A (ramanujanHorizonVector m N) -
        e • ramanujanHorizonVector m N‖ ^ 2 / Real.log N := by
  simp only [normalizedRamanujanHorizonVector, map_smul]
  rw [smul_comm e (Real.sqrt (Real.log N))⁻¹, ← smul_sub,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (Real.log_natCast_nonneg N)]
  ring

private theorem normalized_mode_norm_sq_le_linear_quad {m N : ℕ}
    (hm : 0 < m) (hlog : 1 ≤ Real.log (N : ℝ)) :
    ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 2 * (m : ℝ) := by
  have hL : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hraw : ‖ramanujanHorizonVector m N‖ ^ 2 ≤ (m : ℝ) * (1 + Real.log N) := by
    rw [ramanujanHorizonVector_norm_sq]
    calc
      _ ≤ ∑ n ∈ Icc 1 N, (m : ℝ) * (1 / (n : ℝ)) := by
        refine sum_le_sum fun n _ => ?_
        rw [ramanujanPoleProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        have hs := mul_self_le_mul_self (abs_nonneg (normalizedRamanujanMode m n))
          (abs_mode_le_sqrt_conductor_quad hm n)
        rw [← sq, sq_abs, ← sq, Real.sq_sqrt (Nat.cast_nonneg m)] at hs
        simpa only [div_eq_mul_inv, one_mul] using
          div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
      _ = (m : ℝ) * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N) (Nat.cast_nonneg m)
  calc
    ‖normalizedRamanujanHorizonVector m N‖ ^ 2 =
        ‖ramanujanHorizonVector m N‖ ^ 2 / Real.log N := by
      rw [normalizedRamanujanHorizonVector, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, inv_pow, Real.sq_sqrt hL.le]
      ring
    _ ≤ (m : ℝ) * (1 + Real.log N) / Real.log N := div_le_div_of_nonneg_right hraw hL.le
    _ ≤ 2 * (m : ℝ) := by
      rw [div_le_iff₀ hL]
      nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sub_nonneg.mpr hlog)]

private theorem sum_range_sub_le_first (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (M : ℕ) :
    (∑ k ∈ range M, (g k - g (k + 1))) ≤ g 0 := by
  have htel : ∀ m : ℕ, (∑ k ∈ range m, (g k - g (k + 1))) = g 0 - g m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih]
      ring
  rw [htel M]
  linarith only [hg M]

/-- Quantitative inverse-square tail starting at integer gap `d ≥ 1`:
`∑_{k = d}^N 1 / k^2 ≤ 2 / d`. -/
private theorem sum_Icc_inv_sq_from_le {d N : ℕ} (hd : 1 ≤ d) :
    (∑ k ∈ Icc d N, 1 / (k : ℝ) ^ 2) ≤ 2 / (d : ℝ) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le hd1
  by_cases hdN : d ≤ N
  · have hsplit : Icc d N = insert d (Ioc d N) := by
      ext k; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
    have hmem : d ∉ Ioc d N := by simp only [mem_Ioc]; omega
    rw [hsplit, sum_insert hmem]
    have hfirst : 1 / (d : ℝ) ^ 2 ≤ 1 / (d : ℝ) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hd0) hd0]
      nlinarith only [hd1]
    have hreindex : (∑ k ∈ Ioc d N, 1 / (k : ℝ) ^ 2) =
        ∑ i ∈ range (N - d), 1 / ((d : ℝ) + (i + 1 : ℕ)) ^ 2 := by
      refine sum_bij (fun k _ => k - (d + 1)) ?_ ?_ ?_ ?_
      · intro k hk; obtain ⟨h1, h2⟩ := mem_Ioc.mp hk; exact mem_range.mpr (by omega)
      · intro k₁ h1 k₂ h2 heq
        obtain ⟨hk1, _⟩ := mem_Ioc.mp h1; obtain ⟨hk2, _⟩ := mem_Ioc.mp h2
        change k₁ - (d + 1) = k₂ - (d + 1) at heq; omega
      · intro i hi
        have hi' := mem_range.mp hi
        exact ⟨d + (i + 1), mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        obtain ⟨hk1, _⟩ := mem_Ioc.mp hk
        have hkeq : (k : ℝ) = (d : ℝ) + ((k - (d + 1) + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show k = d + (k - (d + 1) + 1) by omega)
        rw [hkeq]
    have hstep : ∀ i : ℕ, 1 / ((d : ℝ) + (i + 1 : ℕ)) ^ 2 ≤
        1 / ((d : ℝ) + i) - 1 / ((d : ℝ) + (i + 1 : ℕ)) := by
      intro i
      have ha : 0 < (d : ℝ) + i := by positivity
      have hb : 0 < (d : ℝ) + (i + 1 : ℕ) := by positivity
      have hdiff : 1 / ((d : ℝ) + i) - 1 / ((d : ℝ) + (i + 1 : ℕ)) =
          1 / (((d : ℝ) + i) * ((d : ℝ) + (i + 1 : ℕ))) := by
        field_simp [ha.ne', hb.ne']
        push_cast
        ring
      rw [hdiff, div_le_div_iff₀ (sq_pos_of_pos hb) (mul_pos ha hb)]
      push_cast
      nlinarith only [ha]
    have htail : (∑ k ∈ Ioc d N, 1 / (k : ℝ) ^ 2) ≤ 1 / (d : ℝ) := by
      rw [hreindex]
      calc
        (∑ i ∈ range (N - d), 1 / ((d : ℝ) + (i + 1 : ℕ)) ^ 2) ≤
            ∑ i ∈ range (N - d), (1 / ((d : ℝ) + i) - 1 / ((d : ℝ) + (i + 1 : ℕ))) :=
          sum_le_sum fun i _ => hstep i
        _ ≤ 1 / ((d : ℝ) + (0 : ℕ)) :=
          sum_range_sub_le_first (fun i => 1 / ((d : ℝ) + i)) (fun _ => by positivity) (N - d)
        _ = 1 / (d : ℝ) := by simp
    linarith only [hfirst, htail, (by ring : 1 / (d : ℝ) + 1 / (d : ℝ) = 2 / (d : ℝ))]
  · rw [Icc_eq_empty hdN, sum_empty]
    positivity

/-! ## Section 2: Prime Residual, Self-Error, Cross-Error, Pole-Error, and Near-Center Channels -/

private theorem exists_primeResidual_quad_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ N : ℕ,
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        C * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N := by
  obtain ⟨B, hB, hbound⟩ := SignedArithmeticHodgeTheory.exists_uniform_ramanujanPrimeResidual_family_bound
  refine ⟨16 * B, by positivity, fun m hm N => ?_⟩
  let mpos : ℕ+ := ⟨m, hm⟩
  have hraw := hbound {mpos} (fun _ => 1) N
  simp only [sum_singleton, one_mul, one_pow, mul_one] at hraw
  have hraw' : ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • ramanujanHorizonVector m N‖ ^ 2 ≤
      B * SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m ^ 2 := by
    rw [ramanujanHorizonVector_residual_norm_sq]
    exact hraw
  have hlog0 := Real.log_natCast_nonneg m
  have hfac : (1 + 4 * Real.log (m : ℝ)) ^ 2 ≤ 16 * (1 + Real.log (m : ℝ)) ^ 2 := by
    have h1 : 1 + 4 * Real.log (m : ℝ) ≤ 4 * (1 + Real.log (m : ℝ)) := by linarith only [hlog0]
    exact (pow_le_pow_left₀ (by positivity) h1 2).trans_eq (by ring)
  have htot : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hcost : SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m ^ 2 ≤
      16 * ((m : ℝ) * (1 + Real.log m) ^ 2) := by
    rw [SignedArithmeticHodgeTheory.ramanujanResidualConductorCost, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg m.totient)]
    exact (mul_le_mul htot hfac (sq_nonneg _) (Nat.cast_nonneg m)).trans_eq (by ring)
  rw [normalized_residual_sq_quad]
  exact div_le_div_of_nonneg_right
    (hraw'.trans ((mul_le_mul_of_nonneg_left hcost hB.le).trans_eq (by ring)))
    (Real.log_natCast_nonneg N)

private theorem exists_selfError_quad_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ N : ℕ,
      1 ≤ N → 1 ≤ Real.log N → ∀ c : ℝ, 0 < c → c ≤ (N : ℝ) →
        ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          C * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2 := by
  let B : ℝ := Real.exp (1 / 2) / 2
  refine ⟨2 * B ^ 2, by dsimp only [B]; positivity, fun m hm N hN hlog c hc hcN => ?_⟩
  have hv := normalized_mode_norm_sq_le_linear_quad hm hlog
  have hs := abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM hc hN hcN
  have hsq := mul_self_le_mul_self (abs_nonneg _) hs
  rw [← sq, sq_abs, ← sq] at hsq
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact (mul_le_mul hsq hv (sq_nonneg _) (sq_nonneg _)).trans_eq (by dsimp only [B]; ring)

/-- Quadratic `O(m * c^2 / log N)` bound on `separatedCrossErrorMatrix` via integer-distance
collar tail `|j - n| ≥ max 1 ⌈c n / N⌉₊`. -/
private theorem exists_crossError_quadratic_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → c ^ 2 ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
          C * (m : ℝ) * c ^ 2 / Real.log N := by
  let K₀ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)
  have hK₀0 : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  refine ⟨2080 * K₀ ^ 2, by positivity, ?_⟩
  intro m hm c hc N hN hc2N
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let E_ker : ℕ → ℕ → ℝ := fun n j =>
    if 2 * (c / N) < |Real.log j - Real.log n| then
      atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0
  have hrow_le : ∀ n ∈ Icc 1 N,
      (∑ j ∈ Icc 1 N, E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 ≤
        2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2 +
          32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2 := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    let d : ℕ := max 1 ⌈c * (n : ℝ) / N⌉₊
    have hd1 : 1 ≤ d := le_max_left _ _
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hcd : c * (n : ℝ) / N ≤ (d : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈c * (n : ℝ) / N⌉₊))
    have hinv_d : 1 / (d : ℝ) ≤ (N : ℝ) / (c * n) := by
      have hpos : 0 < c * (n : ℝ) / N := div_pos (mul_pos hc0 hn0) hN0
      exact (one_div_le_one_div_of_le hpos hcd).trans_eq (one_div_div _ _)
    let S_mod := (Icc 1 N).filter (fun j => 2 * (c / N) < |Real.log j - Real.log n| ∧
      (n ≤ 2 * j ∧ j ≤ 2 * n))
    have hterm_pt : ∀ j ∈ Icc 1 N,
        |E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)| ≤
          K₀ * (c / N) ^ 2 * Real.sqrt m *
            ((if j ∈ S_mod then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4) := by
      intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
      have hsj1 : 1 ≤ Real.sqrt (j : ℝ) := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hj1 : (1 : ℝ) ≤ j)
      by_cases hgap : 2 * (c / N) < |Real.log j - Real.log n|
      · have hne : n ≠ j := by
          intro heq; subst heq; simp only [sub_self, abs_zero] at hgap
          linarith only [hgap, div_pos hc0 hN0]
        have hd_pos : 0 < |(n : ℝ) - j| :=
          abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
        have hd2 : 0 < |(n : ℝ) - j| ^ 2 := sq_pos_of_pos hd_pos
        have hm0 : 0 ≤ max (n : ℝ) j := hn0.le.trans (le_max_left _ _)
        have hentry := abs_separatedCrossError_le hφ hsupp hM hc0 hN hn hj
        change |E_ker n j| ≤ K₀ * (c / N) ^ 2 * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 at hentry
        have ha : |normalizedRamanujanMode m j / Real.sqrt j| ≤ Real.sqrt m / Real.sqrt j := by
          rw [abs_div, abs_of_pos hsj]
          exact div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor_quad hm j) hsj.le
        have hprod := mul_le_mul hentry ha (abs_nonneg _) (by positivity)
        rw [← abs_mul] at hprod
        have hrew : K₀ * (c / N) ^ 2 * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 *
            (Real.sqrt m / Real.sqrt j) =
            K₀ * (c / N) ^ 2 * Real.sqrt m *
              ((max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2)) := by ring
        rw [hrew] at hprod
        refine hprod.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        by_cases hnear : n ≤ 2 * j ∧ j ≤ 2 * n
        · rw [if_pos (mem_filter.mpr ⟨hj, hgap, hnear⟩)]
          have hnjR : (n : ℝ) ≤ 2 * j := by exact_mod_cast hnear.1
          have hjnR : (j : ℝ) ≤ 2 * n := by exact_mod_cast hnear.2
          have hs_cmp : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (j : ℝ) := by
            by_contra h
            have hlt : 2 * Real.sqrt (j : ℝ) < Real.sqrt (n : ℝ) := lt_of_not_ge h
            have hp := mul_pos (sub_pos.mpr hlt) (by positivity :
              0 < Real.sqrt (n : ℝ) + 2 * Real.sqrt (j : ℝ))
            nlinarith only [hp, Real.sq_sqrt hn0.le, Real.sq_sqrt hj0.le, hnjR, hj0]
          have hm_le : max (n : ℝ) j ≤ 2 * n := max_le (by linarith only [hn0]) hjnR
          have hm2 : (max (n : ℝ) j) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
            have hsq := mul_self_le_mul_self hm0 hm_le
            nlinarith only [hsq]
          have hnum : (max (n : ℝ) j) ^ 2 ≤ 8 * (n : ℝ) * Real.sqrt n * Real.sqrt j := by
            calc
              _ ≤ 4 * (n : ℝ) ^ 2 := hm2
              _ = (4 * (n : ℝ) * Real.sqrt n) * Real.sqrt n := by
                rw [mul_assoc (4 * (n : ℝ)), ← pow_two, Real.sq_sqrt hn0.le]; ring
              _ ≤ (4 * (n : ℝ) * Real.sqrt n) * (2 * Real.sqrt j) :=
                mul_le_mul_of_nonneg_left hs_cmp (by positivity)
              _ = _ := by ring
          have ht : (max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2) ≤
              8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 := by
            rw [div_le_div_iff₀ (mul_pos hsj hd2) hd2]
            nlinarith only [mul_nonneg (sub_nonneg.mpr hnum) hd2.le]
          linarith only [ht]
        · rw [if_neg (fun h => hnear (mem_filter.mp h).2.2), zero_add]
          have hm_far : max (n : ℝ) j ≤ 2 * |(n : ℝ) - j| := by
            rcases not_and_or.mp hnear with h | h
            · have hnR' : 2 * (j : ℝ) < n := by exact_mod_cast (lt_of_not_ge h)
              rw [max_eq_left (by linarith only [hnR', hj0]),
                abs_of_pos (by linarith only [hnR', hj0])]
              linarith only [hnR']
            · have hjR' : 2 * (n : ℝ) < j := by exact_mod_cast (lt_of_not_ge h)
              rw [max_eq_right (by linarith only [hjR', hn0]),
                abs_of_neg (by linarith only [hjR', hn0])]
              linarith only [hjR']
          have hm2 : (max (n : ℝ) j) ^ 2 ≤ 4 * |(n : ℝ) - j| ^ 2 := by
            have hsq := mul_self_le_mul_self hm0 hm_far
            nlinarith only [hsq]
          rw [div_le_iff₀ (mul_pos hsj hd2)]
          nlinarith only [hm2, mul_nonneg (sub_nonneg.mpr hsj1) hd2.le]
      · have hz : E_ker n j = 0 := by dsimp only [E_ker]; rw [if_neg hgap]
        rw [hz, zero_mul, abs_zero]
        have hif0 : 0 ≤ (if j ∈ S_mod then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4 := by
          split_ifs <;> positivity
        exact mul_nonneg (by positivity) hif0
    -- Every `j ∈ S_mod` satisfies integer distance `≥ d`.
    have hgap_mod : ∀ j ∈ S_mod, c * (n : ℝ) / N < |(n : ℝ) - j| := by
      intro j hjS
      obtain ⟨hj, hgap, hnj2, hjn2⟩ := mem_filter.mp hjS
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
      have hnjR : (n : ℝ) ≤ 2 * j := by exact_mod_cast hnj2
      have hne : j ≠ n := by
        intro heq; subst heq; simp only [sub_self, abs_zero] at hgap
        linarith only [hgap, div_pos hc0 hN0]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hjlt : (j : ℝ) < n := by exact_mod_cast hlt
        have hlog_ub := Real.log_le_sub_one_of_pos (div_pos hn0 hj0)
        rw [Real.log_div hn0.ne' hj0.ne', show (n : ℝ) / j - 1 = ((n : ℝ) - j) / j by
          field_simp [hj0.ne']] at hlog_ub
        have hlog_eq : |Real.log j - Real.log n| = Real.log n - Real.log j := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hj0 hjlt.le))]
        have hfrac : ((n : ℝ) - j) / j ≤ 2 * ((n : ℝ) - j) / n := by
          rw [div_le_div_iff₀ hj0 hn0]
          nlinarith only [hnjR, sub_pos.mpr hjlt]
        have habs_eq : |(n : ℝ) - j| = (n : ℝ) - j := abs_of_pos (sub_pos.mpr hjlt)
        have hlt2 : 2 * (c / N) < 2 * |(n : ℝ) - j| / n := by
          rw [habs_eq]; linarith only [hgap, hlog_eq, hlog_ub, hfrac]
        have hmul := (div_lt_div_iff₀ hN0 hn0).mp (by simpa only [mul_div_assoc] using hlt2)
        exact (div_lt_iff₀ hN0).mpr (by linarith only [hmul])
      · have hngt : (n : ℝ) < j := by exact_mod_cast hgt
        have hlog_ub := Real.log_le_sub_one_of_pos (div_pos hj0 hn0)
        rw [Real.log_div hj0.ne' hn0.ne', show (j : ℝ) / n - 1 = ((j : ℝ) - n) / n by
          field_simp [hn0.ne']] at hlog_ub
        have hlog_eq : |Real.log j - Real.log n| = Real.log j - Real.log n :=
          abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 hngt.le))
        have habs_eq : |(n : ℝ) - j| = (j : ℝ) - n := by
          rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hngt)]
        have hlt2 : 2 * (c / N) < 2 * |(n : ℝ) - j| / n := by
          rw [habs_eq]
          have hpos_diff : 0 < ((j : ℝ) - n) / n := div_pos (sub_pos.mpr hngt) hn0
          linarith only [hgap, hlog_eq, hlog_ub, hpos_diff]
        have hmul := (div_lt_div_iff₀ hN0 hn0).mp (by simpa only [mul_div_assoc] using hlt2)
        exact (div_lt_iff₀ hN0).mpr (by linarith only [hmul])
    -- Tail sum over `S_mod` is at most `4 / d ≤ 4 * N / (c * n)`.
    have hsum_mod : (∑ j ∈ S_mod, 1 / |(n : ℝ) - j| ^ 2) ≤ 4 * (N : ℝ) / (c * n) := by
      let L_set := S_mod.filter (fun j => j < n)
      let R_set := S_mod.filter (fun j => n < j)
      have hsplit_LR : (∑ j ∈ S_mod, 1 / |(n : ℝ) - j| ^ 2) =
          (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) + ∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2 := by
        simp only [L_set, R_set, sum_filter, ← sum_add_distrib]
        refine sum_congr rfl fun j _ => ?_
        rcases lt_trichotomy j n with h | rfl | h
        · rw [if_pos h, if_neg (not_lt_of_ge h.le), add_zero]
        · simp
        · rw [if_neg (not_lt_of_ge h.le), if_pos h, zero_add]
      have hL_bound : (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) ≤ 2 / (d : ℝ) := by
        have hinj : ∀ i ∈ L_set, ∀ j ∈ L_set, n - i = n - j → i = j := by
          intro i hi j hj hij
          have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2
          change n - i = n - j at hij; omega
        have hmap : (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) =
            ∑ k ∈ L_set.image (fun j => n - j), 1 / (k : ℝ) ^ 2 := by
          rw [sum_image hinj]
          refine sum_congr rfl fun j hj => ?_
          have hlt := (mem_filter.mp hj).2
          rw [Nat.cast_sub hlt.le, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le))]
        have hsub_d : L_set.image (fun j => n - j) ⊆ Icc d N := by
          intro k hk
          obtain ⟨j, hjL, rfl⟩ := mem_image.mp hk
          obtain ⟨hjS, hlt⟩ := mem_filter.mp hjL
          have hgj := hgap_mod j hjS
          rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
            ← Nat.cast_sub hlt.le] at hgj
          have hceil : ⌈c * (n : ℝ) / N⌉₊ ≤ n - j := Nat.ceil_le.mpr hgj.le
          have hd_le : d ≤ n - j := max_le (by omega) hceil
          exact mem_Icc.mpr ⟨hd_le, (Nat.sub_le n j).trans hnN⟩
        rw [hmap]
        exact (sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ => 1 / (k : ℝ) ^ 2)
          hsub_d (fun _ _ _ => by positivity)).trans (sum_Icc_inv_sq_from_le hd1)
      have hR_bound : (∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2) ≤ 2 / (d : ℝ) := by
        have hinj : ∀ i ∈ R_set, ∀ j ∈ R_set, i - n = j - n → i = j := by
          intro i hi j hj hij
          have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2
          change i - n = j - n at hij; omega
        have hmap : (∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2) =
            ∑ k ∈ R_set.image (fun j => j - n), 1 / (k : ℝ) ^ 2 := by
          rw [sum_image hinj]
          refine sum_congr rfl fun j hj => ?_
          have hlt := (mem_filter.mp hj).2
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
            Nat.cast_sub hlt.le]
        have hsub_d : R_set.image (fun j => j - n) ⊆ Icc d N := by
          intro k hk
          obtain ⟨j, hjR, rfl⟩ := mem_image.mp hk
          obtain ⟨hjS, hlt⟩ := mem_filter.mp hjR
          have hjN := (mem_Icc.mp (mem_filter.mp hjS).1).2
          have hgj := hgap_mod j hjS
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
            ← Nat.cast_sub hlt.le] at hgj
          have hceil : ⌈c * (n : ℝ) / N⌉₊ ≤ j - n := Nat.ceil_le.mpr hgj.le
          have hd_le : d ≤ j - n := max_le (by omega) hceil
          exact mem_Icc.mpr ⟨hd_le, (Nat.sub_le j n).trans hjN⟩
        rw [hmap]
        exact (sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ => 1 / (k : ℝ) ^ 2)
          hsub_d (fun _ _ _ => by positivity)).trans (sum_Icc_inv_sq_from_le hd1)
      rw [hsplit_LR]
      have h4d : (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) + ∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2 ≤
          4 * (1 / (d : ℝ)) := by linarith only [hL_bound, hR_bound]
      exact h4d.trans ((mul_le_mul_of_nonneg_left hinv_d (by norm_num)).trans_eq (by ring))
    have hrow_abs : |∑ j ∈ Icc 1 N, E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)| ≤
        32 * K₀ * Real.sqrt m * c * Real.sqrt n / N + 4 * K₀ * Real.sqrt m * c ^ 2 / N := by
      have hsub_S : (Icc 1 N).filter (fun j => j ∈ S_mod) = S_mod := by
        ext j; simp only [S_mod, mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
      calc
        |∑ j ∈ Icc 1 N, E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)| ≤
            ∑ j ∈ Icc 1 N, |E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)| :=
          abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Icc 1 N, K₀ * (c / N) ^ 2 * Real.sqrt m *
              ((if j ∈ S_mod then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4) :=
          sum_le_sum hterm_pt
        _ = K₀ * (c / N) ^ 2 * Real.sqrt m *
              ((8 * (n : ℝ) * Real.sqrt n) * (∑ j ∈ S_mod, 1 / |(n : ℝ) - j| ^ 2) + 4 * N) := by
          rw [← mul_sum, sum_add_distrib, ← sum_filter, hsub_S, sum_const, nsmul_eq_mul,
            Nat.card_Icc, Nat.add_sub_cancel, mul_sum]
          congr 2
          · exact sum_congr rfl fun _ _ => by ring
          · ring
        _ ≤ K₀ * (c / N) ^ 2 * Real.sqrt m *
              ((8 * (n : ℝ) * Real.sqrt n) * (4 * (N : ℝ) / (c * n)) + 4 * N) :=
          mul_le_mul_of_nonneg_left
            (add_le_add_right (mul_le_mul_of_nonneg_left hsum_mod (by positivity)) _)
            (by positivity)
        _ = 32 * K₀ * Real.sqrt m * c * Real.sqrt n / N + 4 * K₀ * Real.sqrt m * c ^ 2 / N := by
          field_simp [hc0.ne', hn0.ne', hN0.ne']; ring
    have hsq := mul_self_le_mul_self (abs_nonneg _) hrow_abs
    rw [← sq, sq_abs, ← sq] at hsq
    let u₁ := 32 * K₀ * Real.sqrt m * c * Real.sqrt n / N
    let u₂ := 4 * K₀ * Real.sqrt m * c ^ 2 / N
    have h2sq : (u₁ + u₂) ^ 2 ≤ 2 * u₁ ^ 2 + 2 * u₂ ^ 2 := by
      nlinarith only [sq_nonneg (u₁ - u₂)]
    have hu1 : 2 * u₁ ^ 2 = 2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2 := by
      dsimp only [u₁]
      rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg m), Real.sq_sqrt hn0.le]
      ring
    have hu2 : 2 * u₂ ^ 2 = 32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2 := by
      dsimp only [u₂]
      rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
      ring
    exact hsq.trans (h2sq.trans_eq (by rw [hu1, hu2]))
  have hraw : ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
      (ramanujanHorizonVector m N)‖ ^ 2 ≤ 2080 * K₀ ^ 2 * (m : ℝ) * c ^ 2 := by
    change ‖Matrix.toEuclideanLin (horizonKernelMatrix E_ker N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    change (∑ n ∈ Icc 1 N,
      (∑ j ∈ Icc 1 N, E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2) ≤ _
    have hsum_n : (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ (N : ℝ) ^ 2 := by
      calc
        (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ ∑ _n ∈ Icc 1 N, (N : ℝ) :=
          sum_le_sum fun n hn => by exact_mod_cast (mem_Icc.mp hn).2
        _ = (N : ℝ) ^ 2 := by rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]; ring
    have hs1 : (∑ n ∈ Icc 1 N, 2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2) ≤
        2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 := by
      have heq : (∑ n ∈ Icc 1 N, 2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2) =
          (2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, (n : ℝ) := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      rw [heq]
      exact (mul_le_mul_of_nonneg_left hsum_n (by positivity)).trans_eq
        (by field_simp [hN0.ne'])
    have hs2 : (∑ n ∈ Icc 1 N, 32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2) ≤
        32 * K₀ ^ 2 * (m : ℝ) * c ^ 2 := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      have hc4 : c ^ 4 ≤ c ^ 2 * (N : ℝ) := by
        have : c ^ 4 = c ^ 2 * c ^ 2 := by ring
        rw [this]; exact mul_le_mul_of_nonneg_left hc2N (sq_nonneg c)
      calc
        (N : ℝ) * (32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2) =
            32 * K₀ ^ 2 * (m : ℝ) * (c ^ 4 / N) := by field_simp [hN0.ne']
        _ ≤ 32 * K₀ ^ 2 * (m : ℝ) * c ^ 2 :=
          mul_le_mul_of_nonneg_left ((div_le_iff₀ hN0).mpr hc4) (by positivity)
    calc
      (∑ n ∈ Icc 1 N,
        (∑ j ∈ Icc 1 N, E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2) ≤
          (∑ n ∈ Icc 1 N, 2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2) +
            ∑ n ∈ Icc 1 N, 32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2 := by
        rw [← sum_add_distrib]; exact sum_le_sum hrow_le
      _ ≤ 2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 + 32 * K₀ ^ 2 * (m : ℝ) * c ^ 2 := add_le_add hs1 hs2
      _ = 2080 * K₀ ^ 2 * (m : ℝ) * c ^ 2 := by ring
  rw [normalized_action_sq_quad]
  exact div_le_div_of_nonneg_right hraw (Real.log_natCast_nonneg N)

/-- Sub-power `O(m * c^10 * (log N / N)^2)` bound on `fullWeilPoleErrorMatrix` via rank-two
row factorization `√n * ∑ a(j)/j + (1/√n) * ∑ a(j)`. -/
private theorem exists_poleError_quadratic_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log N → c ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
          C * (m : ℝ) * c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 := by
  let C_p := atomPoleMomentErrorConstant φ
  refine ⟨16 * C_p ^ 2, by positivity, ?_⟩
  intro m hm c hc N hN hlog hcN
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  let S_m := ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j / (j : ℝ)
  let T_m := ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j
  have hS_abs : |S_m| ≤ Real.sqrt m * (1 + Real.log N) := by
    calc
      |S_m| ≤ ∑ j ∈ Icc 1 N, |normalizedRamanujanMode m j / (j : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Icc 1 N, Real.sqrt m * (1 / (j : ℝ)) := by
        refine sum_le_sum fun j hj => ?_
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        rw [abs_div, abs_of_pos hj0, div_eq_mul_inv, one_div]
        exact mul_le_mul_of_nonneg_right (abs_mode_le_sqrt_conductor_quad hm j) (by positivity)
      _ = Real.sqrt m * ∑ j ∈ Icc 1 N, 1 / (j : ℝ) := (mul_sum _ _ _).symm
      _ ≤ Real.sqrt m * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N)
          (Real.sqrt_nonneg m)
  have hS_sq : S_m ^ 2 ≤ (m : ℝ) * (1 + Real.log N) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg _) hS_abs
    rwa [← sq, sq_abs, ← sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] at h
  have hT_abs : |T_m| ≤ Real.sqrt m * (N : ℝ) := by
    calc
      |T_m| ≤ ∑ j ∈ Icc 1 N, |normalizedRamanujanMode m j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Icc 1 N, Real.sqrt m := sum_le_sum fun j _ => abs_mode_le_sqrt_conductor_quad hm j
      _ = Real.sqrt m * (N : ℝ) := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]; ring
  have hT_sq : T_m ^ 2 ≤ (m : ℝ) * (N : ℝ) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg _) hT_abs
    rwa [← sq, sq_abs, ← sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] at h
  have hd := abs_atomPoleErrorCoefficient_le_of_le hφ hsupp hM hc0 hN hcN
  have hs_coef : atomPoleErrorCoefficient φ c N ^ 2 ≤ C_p ^ 2 * (c / N) ^ 4 := by
    have h := mul_self_le_mul_self (abs_nonneg _) hd
    rw [← sq, sq_abs, ← sq] at h
    exact h.trans_eq (by dsimp only [C_p]; ring)
  have hraw : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
      (ramanujanHorizonVector m N)‖ ^ 2 ≤
      4 * C_p ^ 2 * (m : ℝ) * c ^ 4 * (1 + Real.log N) ^ 2 / (N : ℝ) ^ 2 := by
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hrow : ∀ n ∈ Icc 1 N,
        (∑ j ∈ Icc 1 N, atomPoleErrorCoefficient φ c N *
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * ramanujanPoleProfile m j) ^ 2 ≤
          2 * atomPoleErrorCoefficient φ c N ^ 2 * ((n : ℝ) * S_m ^ 2 + (1 / (n : ℝ)) * T_m ^ 2) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      have hid : (∑ j ∈ Icc 1 N, atomPoleErrorCoefficient φ c N *
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * ramanujanPoleProfile m j) =
          atomPoleErrorCoefficient φ c N * (Real.sqrt n * S_m + (1 / Real.sqrt n) * T_m) := by
        dsimp only [S_m, T_m]
        rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun j hj => ?_
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
        simp only [ramanujanPoleProfile]
        field_simp [hsn.ne', hsj.ne']
        rw [Real.sq_sqrt hj0.le]
        ring
      rw [hid, mul_pow]
      have h2 : (Real.sqrt n * S_m + (1 / Real.sqrt n) * T_m) ^ 2 ≤
          2 * ((n : ℝ) * S_m ^ 2 + (1 / (n : ℝ)) * T_m ^ 2) := by
        have h1 : (Real.sqrt n * S_m) ^ 2 = (n : ℝ) * S_m ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hn0.le]
        have h2' : ((1 / Real.sqrt n) * T_m) ^ 2 = (1 / (n : ℝ)) * T_m ^ 2 := by
          rw [mul_pow, one_div_pow, Real.sq_sqrt hn0.le]
        nlinarith only [h1, h2', sq_nonneg (Real.sqrt n * S_m - (1 / Real.sqrt n) * T_m)]
      exact (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)).trans_eq (by ring)
    have hsum_n : (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ (N : ℝ) ^ 2 := by
      calc
        (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ ∑ _n ∈ Icc 1 N, (N : ℝ) :=
          sum_le_sum fun n hn => by exact_mod_cast (mem_Icc.mp hn).2
        _ = (N : ℝ) ^ 2 := by rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]; ring
    have hsum_inv : (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) ≤ (1 + Real.log N) ^ 2 := by
      have h1 : 1 ≤ 1 + Real.log (N : ℝ) := by linarith only [hL0]
      exact (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N).trans
        (by nlinarith only [h1])
    calc
      (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, atomPoleErrorCoefficient φ c N *
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * ramanujanPoleProfile m j) ^ 2) ≤
          ∑ n ∈ Icc 1 N, 2 * atomPoleErrorCoefficient φ c N ^ 2 *
            ((n : ℝ) * S_m ^ 2 + (1 / (n : ℝ)) * T_m ^ 2) := sum_le_sum hrow
      _ = 2 * atomPoleErrorCoefficient φ c N ^ 2 *
            ((∑ n ∈ Icc 1 N, (n : ℝ)) * S_m ^ 2 + (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) * T_m ^ 2) := by
        rw [← mul_sum, sum_add_distrib, ← sum_mul, ← sum_mul]
      _ ≤ 2 * (C_p ^ 2 * (c / N) ^ 4) *
            ((N : ℝ) ^ 2 * ((m : ℝ) * (1 + Real.log N) ^ 2) +
              (1 + Real.log N) ^ 2 * ((m : ℝ) * (N : ℝ) ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs_coef zero_le_two)
          (add_le_add (mul_le_mul hsum_n hS_sq (sq_nonneg _) (sq_nonneg _))
            (mul_le_mul hsum_inv hT_sq (sq_nonneg _) (sq_nonneg _)))
          (by positivity) (by positivity)
      _ = 4 * C_p ^ 2 * (m : ℝ) * c ^ 4 * (1 + Real.log N) ^ 2 / (N : ℝ) ^ 2 := by
        field_simp [hN0.ne']; ring
  rw [normalized_action_sq_quad]
  have h1L : (1 + Real.log (N : ℝ)) ^ 2 ≤ 4 * Real.log (N : ℝ) ^ 2 := by
    have : 1 + Real.log (N : ℝ) ≤ 2 * Real.log (N : ℝ) := by linarith only [hlog]
    exact (pow_le_pow_left₀ (by positivity) this 2).trans_eq (by ring)
  have hc410 : c ^ 4 ≤ c ^ 10 := pow_le_pow_right₀ hc (by norm_num : 4 ≤ 10)
  calc
    ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector m N)‖ ^ 2 /
        Real.log N ≤
        (4 * C_p ^ 2 * (m : ℝ) * c ^ 4 * (1 + Real.log N) ^ 2 / (N : ℝ) ^ 2) / Real.log N :=
      div_le_div_of_nonneg_right hraw hL0.le
    _ ≤ 4 * C_p ^ 2 * (m : ℝ) * c ^ 4 * (1 + Real.log N) ^ 2 / (N : ℝ) ^ 2 :=
      div_le_self (by positivity) hlog
    _ ≤ 4 * C_p ^ 2 * (m : ℝ) * c ^ 10 * (4 * Real.log (N : ℝ) ^ 2) / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hc410 (by positivity)) h1L
          (sq_nonneg _) (by positivity))
        (sq_nonneg _)
    _ = 16 * C_p ^ 2 * (m : ℝ) * c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 := by
      rw [div_pow]; ring

/-- Quadratic `O(m * c^2 * (1 + log c)^3 / log N)` bound on `nearCenterVector φ c N m` via
pointwise `1 / |j - n|` Levy majorant and `HTGeometry.sum_sq_le_harmonic_quotient_tail`. -/
private theorem exists_nearCenter_quadratic_conductor_bound (φ : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → 2 * c ≤ (N : ℝ) →
        ‖nearCenterVector φ c N m‖ ^ 2 ≤
          C * (m : ℝ) * c ^ 2 * (1 + Real.log c) ^ 3 / Real.log N := by
  let A_nc := |completeWeilPoleShift φ 1| * (1 + Real.exp (1 / 2)) * Real.sqrt (Real.exp 1)
  let C_R1 := 2 + Real.log (2 * Real.exp 2)
  let C_R2 := 2 + Real.log (6 * Real.exp 2)
  have hAnc : 0 ≤ A_nc := by dsimp only [A_nc]; positivity
  have hCR1 : 0 ≤ C_R1 := by
    dsimp only [C_R1]
    have : 0 ≤ Real.log (2 * Real.exp 2) :=
      Real.log_nonneg (by have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2); linarith)
    linarith
  have hCR2 : 0 ≤ C_R2 := by
    dsimp only [C_R2]
    have : 0 ≤ Real.log (6 * Real.exp 2) :=
      Real.log_nonneg (by have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2); linarith)
    linarith
  refine ⟨16 * A_nc ^ 2 * C_R1 ^ 2 * C_R2, by positivity, ?_⟩
  intro m hm c hc N hN hcN
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : c / N ≤ 1 := (div_le_one hN0).mpr (by linarith only [hcN, hc0])
  have h1c : 1 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc]
  let R_c := linearNearRowRadius c
  have hRc_ge1 : 1 ≤ R_c := by
    unfold R_c linearNearRowRadius
    have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    nlinarith only [hc, he2]
  have hα : |completeWeilPoleShift φ c| = c * |completeWeilPoleShift φ 1| := by
    have h1 : completeWeilPoleShift φ c = c * completeWeilPoleShift φ 1 := by
      unfold completeWeilPoleShift; ring
    rw [h1, abs_mul, abs_of_pos hc0]
  -- Pointwise entry bound `≤ (A_nc * √m * c / √n) * (1 / |j - n|)` on `nearRowIndices c N n`.
  have hentry : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
      |completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
        normalizedRamanujanMode m j / Real.sqrt j| ≤
        (A_nc * Real.sqrt m * c / Real.sqrt n) * (1 / |(j : ℝ) - n|) := by
    intro n hn j hj
    obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
    have hn1 := (mem_Icc.mp hn).1
    have hj1 := (mem_Icc.mp hjN).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hnN_R : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hjN_R : (j : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hjN).2
    let y := |Real.log j - Real.log n|
    have hkernel : archimedeanCenterKernel n j = _root_.RHTower.archLevyDensity y := by
      unfold archimedeanCenterKernel
      rw [if_neg (by push Not; exact ⟨Ne.symm hjn, by omega, by omega⟩)]
    have hdist_pos : 0 < |(j : ℝ) - n| :=
      abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hjn))
    have hdist_le_N : |(j : ℝ) - n| ≤ (N : ℝ) := by
      rw [abs_le]; exact ⟨by linarith only [hnN_R, hj0], by linarith only [hjN_R, hn0]⟩
    have hgap : |(j : ℝ) - n| / (N : ℝ) ≤ y := by
      rcases lt_or_gt_of_ne hjn with hlt | hgt
      · have hjlt : (j : ℝ) < n := by exact_mod_cast hlt
        have hlog_le := Real.log_le_sub_one_of_pos (div_pos hj0 hn0)
        rw [Real.log_div hj0.ne' hn0.ne', show (1 : ℝ) - (j : ℝ) / n = ((n : ℝ) - j) / n from
          one_sub_div hn0.ne'] at hlog_le
        have hsub : ((n : ℝ) - j) / n ≤ Real.log n - Real.log j := by linarith only [hlog_le]
        have hy_eq : y = Real.log n - Real.log j := by
          dsimp only [y]
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hj0 hjlt.le))]
        have habs_eq : |(j : ℝ) - n| = (n : ℝ) - j := by
          rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hjlt)]
        rw [hy_eq, habs_eq]
        exact (div_le_div_of_nonneg_left (sub_pos.mpr hjlt).le hn0 hnN_R).trans hsub
      · have hngt : (n : ℝ) < j := by exact_mod_cast hgt
        have hlog_le := Real.log_le_sub_one_of_pos (div_pos hn0 hj0)
        rw [Real.log_div hn0.ne' hj0.ne', show (1 : ℝ) - (n : ℝ) / j = ((j : ℝ) - n) / j from
          one_sub_div hj0.ne'] at hlog_le
        have hsub : ((j : ℝ) - n) / j ≤ Real.log j - Real.log n := by linarith only [hlog_le]
        have hy_eq : y = Real.log j - Real.log n := by
          dsimp only [y]
          rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 hngt.le))]
        have habs_eq : |(j : ℝ) - n| = (j : ℝ) - n := abs_of_pos (sub_pos.mpr hngt)
        rw [hy_eq, habs_eq]
        exact (div_le_div_of_nonneg_left (sub_pos.mpr hngt).le hj0 hjN_R).trans hsub
    have hy0 : 0 < y := lt_of_lt_of_le (div_pos hdist_pos hN0) hgap
    have hy1 : y ≤ 1 := hlog.trans ((div_le_one hN0).mpr hcN)
    have hD0 : 0 < _root_.RHTower.archLevyDensity y := _root_.RHTower.archLevyDensity_pos hy0
    have hD_ub : _root_.RHTower.archLevyDensity y ≤
        (1 + Real.exp (1 / 2)) * ((N : ℝ) / |(j : ℝ) - n|) := by
      have h1 := archLevyDensity_le_inv_two_mul_add hy0 hy1
      have h2 : 1 / (2 * y) ≤ (N : ℝ) / (2 * |(j : ℝ) - n|) := by
        have h2gap : 2 * |(j : ℝ) - n| / N ≤ 2 * y := by
          have := mul_le_mul_of_nonneg_left hgap zero_le_two
          rwa [mul_div_assoc] at this
        exact (one_div_le_one_div_of_le (div_pos (by positivity) hN0) h2gap).trans_eq
          (one_div_div _ _)
      have hNdist1 : 1 ≤ (N : ℝ) / |(j : ℝ) - n| := (one_le_div hdist_pos).mpr hdist_le_N
      have he_le : Real.exp (1 / 2) ≤ Real.exp (1 / 2) * ((N : ℝ) / |(j : ℝ) - n|) :=
        le_mul_of_one_le_right (Real.exp_pos _).le hNdist1
      have hhalf_eq : (N : ℝ) / (2 * |(j : ℝ) - n|) = (1 / 2) * ((N : ℝ) / |(j : ℝ) - n|) := by
        ring
      rw [hhalf_eq] at h2
      linarith only [h1, h2, he_le, hNdist1,
        (by ring : (1 + Real.exp (1 / 2)) * ((N : ℝ) / |(j : ℝ) - n|) =
          (N : ℝ) / |(j : ℝ) - n| + Real.exp (1 / 2) * ((N : ℝ) / |(j : ℝ) - n|)),
        div_nonneg hN0.le hdist_pos.le, Real.exp_pos (1 / 2)]
    -- Bound `1 / √j ≤ √e / √n` from `log n - log j ≤ y ≤ 1`.
    have hsqrt_j : 1 / Real.sqrt j ≤ Real.sqrt (Real.exp 1) / Real.sqrt n := by
      have hlog_nj : Real.log n - Real.log j ≤ 1 := by
        have : Real.log n - Real.log j ≤ y := by
          dsimp only [y]; rw [abs_sub_comm]; exact le_abs_self _
        exact this.trans hy1
      have hnj_exp : (n : ℝ) / j ≤ Real.exp 1 := by
        rw [← Real.exp_log (div_pos hn0 hj0), Real.log_div hn0.ne' hj0.ne']
        exact Real.exp_le_exp.mpr hlog_nj
      have hsq_nj : Real.sqrt n ≤ Real.sqrt (Real.exp 1) * Real.sqrt j := by
        have h := Real.sqrt_le_sqrt ((div_le_iff₀ hj0).mp hnj_exp)
        rwa [Real.sqrt_mul (Real.exp_pos 1).le] at h
      exact (div_le_div_iff₀ (Real.sqrt_pos.mpr hj0) (Real.sqrt_pos.mpr hn0)).mpr
        (by linarith only [hsq_nj])
    have hcoef : |completeWeilPoleShift φ c| / N * _root_.RHTower.archLevyDensity y ≤
        |completeWeilPoleShift φ 1| * (1 + Real.exp (1 / 2)) * c * (1 / |(j : ℝ) - n|) := by
      rw [hα]
      calc
        (c * |completeWeilPoleShift φ 1|) / N * _root_.RHTower.archLevyDensity y ≤
            (c * |completeWeilPoleShift φ 1|) / N *
              ((1 + Real.exp (1 / 2)) * ((N : ℝ) / |(j : ℝ) - n|)) :=
          mul_le_mul_of_nonneg_left hD_ub (by positivity)
        _ = |completeWeilPoleShift φ 1| * (1 + Real.exp (1 / 2)) * c * (1 / |(j : ℝ) - n|) := by
          field_simp [hN0.ne']; ring
    rw [hkernel, abs_div, abs_mul, abs_mul, abs_div, abs_of_pos hN0, abs_of_pos hD0,
      abs_of_pos (Real.sqrt_pos.mpr hj0), div_eq_mul_one_div _ (Real.sqrt j)]
    have hm_j := mul_le_mul (abs_mode_le_sqrt_conductor_quad hm j) hsqrt_j
      (by positivity) (Real.sqrt_nonneg m)
    exact (mul_le_mul hcoef hm_j (by positivity) (by positivity)).trans_eq
      (by dsimp only [A_nc]; ring)
  -- Harmonic sum of `1 / |j - n|` over `nearRowIndices c N n` is `≤ 4 * (1 + log R_c)`.
  have hsum_dist : ∀ n ∈ Icc 1 N,
      (∑ j ∈ nearRowIndices c N n, 1 / |(j : ℝ) - n|) ≤ 4 * (1 + Real.log R_c) := by
    intro n hn
    let K_fl : ℕ := ⌊R_c⌋₊
    have hK_le : (K_fl : ℝ) ≤ R_c := Nat.floor_le (by positivity)
    have hhar_K : (∑ d ∈ Icc 1 K_fl, 1 / (d : ℝ)) ≤ 2 * (1 + Real.log R_c) := by
      by_cases hK1 : 1 ≤ K_fl
      · have hlogK : Real.log K_fl ≤ Real.log R_c :=
          Real.log_le_log (by exact_mod_cast hK1) hK_le
        have h1R : 0 ≤ Real.log R_c := Real.log_nonneg hRc_ge1
        exact (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log K_fl).trans
          (by linarith only [hlogK, h1R])
      · rw [Icc_eq_empty hK1, sum_empty]
        have : 0 ≤ Real.log R_c := Real.log_nonneg hRc_ge1
        linarith
    let L_set := (nearRowIndices c N n).filter (fun j => j < n)
    let U_set := (nearRowIndices c N n).filter (fun j => n < j)
    have hsplit : (∑ j ∈ nearRowIndices c N n, 1 / |(j : ℝ) - n|) =
        (∑ j ∈ L_set, 1 / |(j : ℝ) - n|) + ∑ j ∈ U_set, 1 / |(j : ℝ) - n| := by
      simp only [L_set, U_set, sum_filter, ← sum_add_distrib]
      refine sum_congr rfl fun j hj => ?_
      have hjn := (mem_filter.mp hj).2.1
      rcases lt_or_gt_of_ne hjn with h | h
      · rw [if_pos h, if_neg (not_lt_of_ge h.le), add_zero]
      · rw [if_neg (not_lt_of_ge h.le), if_pos h, zero_add]
    have hL : (∑ j ∈ L_set, 1 / |(j : ℝ) - n|) ≤ 2 * (1 + Real.log R_c) := by
      have hinj : ∀ i ∈ L_set, ∀ j ∈ L_set, n - i = n - j → i = j := by
        intro i hi j hj hij
        have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2
        change n - i = n - j at hij; omega
      have hmap : (∑ j ∈ L_set, 1 / |(j : ℝ) - n|) =
          ∑ d ∈ L_set.image (fun j => n - j), 1 / (d : ℝ) := by
        rw [sum_image hinj]
        refine sum_congr rfl fun j hj => ?_
        have hlt := (mem_filter.mp hj).2
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
          Nat.cast_sub hlt.le]
      have hsub : L_set.image (fun j => n - j) ⊆ Icc 1 K_fl := by
        intro d hd
        obtain ⟨j, hjL, rfl⟩ := mem_image.mp hd
        obtain ⟨hj, hlt⟩ := mem_filter.mp hjL
        have hrad := (nearRow_geometry_small_width hc0 hn hj hw).1
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
          ← Nat.cast_sub hlt.le] at hrad
        exact mem_Icc.mpr ⟨by omega, Nat.le_floor hrad⟩
      rw [hmap]
      exact (sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => 1 / (d : ℝ))
        hsub (fun _ _ _ => by positivity)).trans hhar_K
    have hU : (∑ j ∈ U_set, 1 / |(j : ℝ) - n|) ≤ 2 * (1 + Real.log R_c) := by
      have hinj : ∀ i ∈ U_set, ∀ j ∈ U_set, i - n = j - n → i = j := by
        intro i hi j hj hij
        have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2
        change i - n = j - n at hij; omega
      have hmap : (∑ j ∈ U_set, 1 / |(j : ℝ) - n|) =
          ∑ d ∈ U_set.image (fun j => j - n), 1 / (d : ℝ) := by
        rw [sum_image hinj]
        refine sum_congr rfl fun j hj => ?_
        have hlt := (mem_filter.mp hj).2
        rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)), Nat.cast_sub hlt.le]
      have hsub : U_set.image (fun j => j - n) ⊆ Icc 1 K_fl := by
        intro d hd
        obtain ⟨j, hjU, rfl⟩ := mem_image.mp hd
        obtain ⟨hj, hlt⟩ := mem_filter.mp hjU
        have hrad := (nearRow_geometry_small_width hc0 hn hj hw).1
        rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
          ← Nat.cast_sub hlt.le] at hrad
        exact mem_Icc.mpr ⟨by omega, Nat.le_floor hrad⟩
      rw [hmap]
      exact (sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => 1 / (d : ℝ))
        hsub (fun _ _ _ => by positivity)).trans hhar_K
    rw [hsplit]
    linarith only [hL, hU]
  -- Apply `HTGeometry.sum_sq_le_harmonic_quotient_tail` at cutoff `T = R_c + 1`.
  let row_nc : ℕ → ℝ := fun n => ∑ j ∈ nearRowIndices c N n,
    completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
      normalizedRamanujanMode m j / Real.sqrt j
  let B_nc := 4 * A_nc * Real.sqrt m * c * (1 + Real.log R_c)
  have hglobal : ∀ n ∈ Icc 1 N, |row_nc n| ≤ B_nc / Real.sqrt n := by
    intro n hn
    calc
      |row_nc n| ≤ ∑ j ∈ nearRowIndices c N n,
          |completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
            normalizedRamanujanMode m j / Real.sqrt j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ nearRowIndices c N n,
          (A_nc * Real.sqrt m * c / Real.sqrt n) * (1 / |(j : ℝ) - n|) :=
        sum_le_sum (hentry n hn)
      _ = (A_nc * Real.sqrt m * c / Real.sqrt n) *
          ∑ j ∈ nearRowIndices c N n, 1 / |(j : ℝ) - n| := (mul_sum _ _ _).symm
      _ ≤ (A_nc * Real.sqrt m * c / Real.sqrt n) * (4 * (1 + Real.log R_c)) :=
        mul_le_mul_of_nonneg_left (hsum_dist n hn) (by positivity)
      _ = B_nc / Real.sqrt n := by dsimp only [B_nc]; ring
  have hgood : ∀ n ∈ Icc 1 N, R_c + 1 ≤ (N : ℝ) / n → |row_nc n| ≤ 0 / Real.sqrt n := by
    intro n hn hquot
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hemp : nearRowIndices c N n = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      have hle := (nearRow_geometry_small_width hc0 hn hj hw).2.1
      have hq_le : (N : ℝ) / n ≤ R_c := (div_le_iff₀ hn0).mpr hle
      linarith only [hquot, hq_le]
    dsimp only [row_nc]
    rw [hemp, sum_empty, abs_zero, zero_div]
  have htail := HTGeometry.sum_sq_le_harmonic_quotient_tail hN
    (show 1 ≤ R_c + 1 by linarith only [hRc_ge1]) row_nc hglobal hgood
  have hlogRc : 1 + Real.log R_c ≤ C_R1 * (1 + Real.log c) := by
    have heq : R_c = (2 * Real.exp 2) * c := by unfold R_c linearNearRowRadius; ring
    rw [heq, Real.log_mul (by positivity) hc0.ne']
    have hlogc0 := Real.log_nonneg hc
    have hlog2e : 0 ≤ Real.log (2 * Real.exp 2) :=
      Real.log_nonneg (by have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2); linarith)
    dsimp only [C_R1]
    nlinarith only [hlogc0, hlog2e]
  have hlog2T : 1 + Real.log (2 * (R_c + 1)) ≤ C_R2 * (1 + Real.log c) := by
    have h2T_le : 2 * (R_c + 1) ≤ (6 * Real.exp 2) * c := by
      unfold R_c linearNearRowRadius
      have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      nlinarith only [hc, he2]
    have hl1 := Real.log_le_log (by positivity) h2T_le
    rw [Real.log_mul (by positivity) hc0.ne'] at hl1
    have hlogc0 := Real.log_nonneg hc
    have hlog6e : 0 ≤ Real.log (6 * Real.exp 2) :=
      Real.log_nonneg (by have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2); linarith)
    dsimp only [C_R2]
    nlinarith only [hl1, hlogc0, hlog6e]
  have hB_sq : B_nc ^ 2 ≤ 16 * A_nc ^ 2 * C_R1 ^ 2 * (m : ℝ) * c ^ 2 * (1 + Real.log c) ^ 2 := by
    have hB_le : B_nc ≤ 4 * A_nc * Real.sqrt m * c * (C_R1 * (1 + Real.log c)) :=
      mul_le_mul_of_nonneg_left hlogRc (by positivity)
    have hB0 : 0 ≤ B_nc := by
      dsimp only [B_nc]
      have : 0 ≤ Real.log R_c := Real.log_nonneg hRc_ge1
      positivity
    have hsq := mul_self_le_mul_self hB0 hB_le
    rw [← sq, ← sq] at hsq
    refine hsq.trans_eq ?_
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    ring
  rw [nearCenterVector_norm_sq]
  apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
  calc
    (∑ n ∈ Icc 1 N, row_nc n ^ 2) ≤
        0 ^ 2 * (1 + Real.log N) + B_nc ^ 2 * (1 + Real.log (2 * (R_c + 1))) := htail
    _ = B_nc ^ 2 * (1 + Real.log (2 * (R_c + 1))) := by ring
    _ ≤ (16 * A_nc ^ 2 * C_R1 ^ 2 * (m : ℝ) * c ^ 2 * (1 + Real.log c) ^ 2) *
          (C_R2 * (1 + Real.log c)) :=
      mul_le_mul hB_sq hlog2T (by linarith [Real.log_nonneg (show 1 ≤ 2 * (R_c + 1) by linarith)])
        (by positivity)
    _ = (16 * A_nc ^ 2 * C_R1 ^ 2 * C_R2) * (m : ℝ) * c ^ 2 * (1 + Real.log c) ^ 3 := by ring

/-! ## Section 3: Near-Gamma Downward Source Channel -/

private theorem abs_divisorJet_le_totient_log_quad {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |ramanujanLogDivisorJet m n| ≤ 2 * (m.totient : ℝ) * (1 + Real.log m) := by
  have hmangoldt : 0 ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
  have htri := abs_add_le (ramanujanLogDivisorJet m n - ArithmeticFunction.vonMangoldt m)
    (ArithmeticFunction.vonMangoldt m)
  rw [sub_add_cancel, abs_of_nonneg hmangoldt] at htri
  have henvelope := abs_ramanujanLogDivisorJet_sub_mean_le hm n
  have htot1 : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
  have hvm : ArithmeticFunction.vonMangoldt m ≤ Real.log (m : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  have hdiff := mul_le_mul_of_nonneg_left
    (RenormalizedArithmeticPotentialTheory.tameDifferent_le_log hm) (Nat.cast_nonneg m.totient)
  nlinarith only [htri, henvelope, htot1, hlog0, hvm, hdiff]

/-- Row-proportional Cauchy–Schwarz bound on near-pair sums: because `|j - n| ≤ R_c * n / N` and
`1 / j ≤ e^2 / n` on `nearRowIndices c N n`, the squared row sum scales as `O(c^2 * K^2)`
instead of `O(c^3 * K^2)`. -/
private theorem sum_near_div_sqrt_sq_le_quadratic_width {c K : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (hw : c / N ≤ 1) (F : ℕ → ℕ → ℝ)
    (hK0 : 0 ≤ K)
    (hF : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |F n j| ≤ K) :
    (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, F n j / Real.sqrt j) ^ 2) ≤
      4 * Real.exp 2 * linearNearRowRadius c ^ 2 * K ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  have he_gap : Real.exp (2 * c / N) - 1 ≤ linearNearRowRadius c / N := by
    calc
      Real.exp (2 * c / N) - 1 ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
      _ ≤ 2 * c / N * Real.exp 2 :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by
            have h := mul_le_mul_of_nonneg_left hw zero_le_two
            simpa only [mul_div_assoc, mul_one] using h)) (by positivity)
      _ = linearNearRowRadius c / N := by unfold linearNearRowRadius; ring
  have hrow : ∀ n ∈ Icc 1 N,
      (∑ j ∈ nearRowIndices c N n, F n j / Real.sqrt j) ^ 2 ≤
        4 * Real.exp 2 * linearNearRowRadius c ^ 2 * K ^ 2 * (n : ℝ) / (N : ℝ) ^ 2 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    let rad_n := (n : ℝ) * (linearNearRowRadius c / N)
    have hrad0 : 0 ≤ rad_n := by dsimp only [rad_n]; positivity
    have hcard_n : ((nearRowIndices c N n).card : ℝ) ≤ 2 * rad_n := by
      have hsub : nearRowIndices c N n ⊆
          (Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ rad_n) := by
        intro j hj
        obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
        have hdist := (abs_sub_le_of_abs_log_le hj0 hn0 hlog).trans
          (mul_le_mul_of_nonneg_left he_gap hn0.le)
        exact mem_filter.mpr ⟨hjN, hjn, hdist⟩
      exact (show ((nearRowIndices c N n).card : ℝ) ≤
          (((Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ rad_n)).card : ℝ) by
          exact_mod_cast card_le_card hsub).trans (card_near_le (Icc 1 N) n hrad0)
    have hpoint : ∀ j ∈ nearRowIndices c N n,
        (F n j / Real.sqrt j) ^ 2 ≤ Real.exp 2 * K ^ 2 / (n : ℝ) := by
      intro j hj
      obtain ⟨hjN, _, hlog⟩ := mem_filter.mp hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
      have hsq : F n j ^ 2 ≤ K ^ 2 := by
        have h := mul_self_le_mul_self (abs_nonneg _) (hF n hn j hj)
        simpa only [← sq, sq_abs] using h
      have hlog_nj : Real.log n - Real.log j ≤ 2 := by
        have h1 : Real.log n - Real.log j ≤ |Real.log j - Real.log n| := by
          rw [abs_sub_comm]; exact le_abs_self _
        have h2 : 2 * c / N ≤ 2 := by
          have := mul_le_mul_of_nonneg_left hw zero_le_two
          simpa only [mul_div_assoc, mul_one] using this
        exact h1.trans (hlog.trans h2)
      have hnj_exp : (n : ℝ) / j ≤ Real.exp 2 := by
        rw [← Real.exp_log (div_pos hn0 hj0), Real.log_div hn0.ne' hj0.ne']
        exact Real.exp_le_exp.mpr hlog_nj
      have hj_inv : 1 / (j : ℝ) ≤ Real.exp 2 / (n : ℝ) := by
        rw [div_le_div_iff₀ hj0 hn0, one_mul]
        exact (div_le_iff₀ hj0).mp hnj_exp
      rw [div_pow, Real.sq_sqrt hj0.le, div_eq_mul_one_div]
      exact (mul_le_mul hsq hj_inv (by positivity) (sq_nonneg K)).trans_eq (by ring)
    have hsum := sum_le_sum hpoint
    rw [sum_const, nsmul_eq_mul] at hsum
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (nearRowIndices c N n)
      (fun j => F n j / Real.sqrt j) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
    calc
      (∑ j ∈ nearRowIndices c N n, F n j / Real.sqrt j) ^ 2 ≤
          ((nearRowIndices c N n).card : ℝ) *
            ∑ j ∈ nearRowIndices c N n, (F n j / Real.sqrt j) ^ 2 := by
        simpa only [mul_comm] using hcs
      _ ≤ (2 * rad_n) * ((2 * rad_n) * (Real.exp 2 * K ^ 2 / (n : ℝ))) :=
        mul_le_mul hcard_n (hsum.trans (mul_le_mul_of_nonneg_right hcard_n (by positivity)))
          (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = 4 * Real.exp 2 * linearNearRowRadius c ^ 2 * K ^ 2 * (n : ℝ) / (N : ℝ) ^ 2 := by
        dsimp only [rad_n]; field_simp [hn0.ne', hN0.ne']; ring
  have hsum_n : (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ (N : ℝ) ^ 2 := by
    calc
      (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ ∑ _n ∈ Icc 1 N, (N : ℝ) :=
        sum_le_sum fun n hn => by exact_mod_cast (mem_Icc.mp hn).2
      _ = (N : ℝ) ^ 2 := by rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]; ring
  calc
    (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, F n j / Real.sqrt j) ^ 2) ≤
        ∑ n ∈ Icc 1 N,
          4 * Real.exp 2 * linearNearRowRadius c ^ 2 * K ^ 2 * (n : ℝ) / (N : ℝ) ^ 2 :=
      sum_le_sum hrow
    _ = (4 * Real.exp 2 * linearNearRowRadius c ^ 2 * K ^ 2 / (N : ℝ) ^ 2) *
          ∑ n ∈ Icc 1 N, (n : ℝ) := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ ≤ (4 * Real.exp 2 * linearNearRowRadius c ^ 2 * K ^ 2 / (N : ℝ) ^ 2) * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum_n (by positivity)
    _ = 4 * Real.exp 2 * linearNearRowRadius c ^ 2 * K ^ 2 := by
      field_simp [hN0.ne']

/-- Exterior boundary prime-power rows have squared norm `O(φ(m)^2 * c^3 * (log N)^2 / N)`,
retaining `log ℓ / √ℓ ≪ log N / √N` across `N < ℓ ≤ exteriorPrimeCutoff c N`. -/
private theorem sum_actualExteriorDownwardRow_sq_le_subhorizon {g : ℝ → ℝ} (hg : Continuous g)
    {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hN : 1 ≤ N) (hlogN : 1 ≤ Real.log N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0)
    (hG : 0 < ∫ u, g u ^ 2) (hw : c / N ≤ 1) (m : ℕ) :
    (∑ n ∈ Icc 1 N, actualExteriorDownwardRow g N m n ^ 2) ≤
      ((Real.exp 1 + 2) * (5 * m.totient * (Real.exp 1 + 1)) ^ 2) *
        c ^ 3 * Real.log N ^ 2 / (N : ℝ) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcN : c ≤ (N : ℝ) := (div_le_one hN0).mp hw
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  have hB_le : (linearPrimeStrip c : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc
  have hcut_ub : (exteriorPrimeCutoff c N : ℝ) ≤ 5 * (N : ℝ) := by
    have h1 : (exteriorPrimeCutoff c N : ℝ) ≤ (N : ℝ) + linearPrimeStrip c := by
      exact_mod_cast (exteriorPrimeCutoff_bounds_small_width hc0 hN hw).2
    have he1 : Real.exp 1 ≤ 3 := by
      have h := Real.exp_one_lt_d9
      linarith
    nlinarith only [h1, hB_le, hcN, he1, hc0]
  have hterm : ∀ n : ℕ, ∀ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
      |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
        (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| ≤
        5 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
    intro n ℓ hℓ
    obtain ⟨hNℓ, hℓ_hi⟩ := mem_Ioc.mp hℓ
    have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le N) hNℓ)
    have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
    have hsqrt_le : Real.sqrt N ≤ Real.sqrt ℓ :=
      Real.sqrt_le_sqrt (by exact_mod_cast hNℓ.le)
    have hℓ_5N : (ℓ : ℝ) ≤ 5 * (N : ℝ) :=
      (by exact_mod_cast hℓ_hi : (ℓ : ℝ) ≤ exteriorPrimeCutoff c N).trans hcut_ub
    have hlogℓ : Real.log ℓ ≤ 5 * Real.log N := by
      have hl := Real.log_le_log hℓ0 hℓ_5N
      rw [Real.log_mul (by norm_num) hN0.ne'] at hl
      have hl5 : Real.log 5 ≤ 4 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
        linarith
      linarith only [hl, hl5, hlogN]
    have hcorr : |bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2)| ≤ 1 := by
      rw [abs_div, abs_of_pos hG, div_le_one hG]
      exact abs_bumpCorr_le hg hgc _
    have hjet : |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ| ≤
        5 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
      rw [abs_div, abs_of_pos hsℓ]
      calc
        |horizonRamanujanMangoldt m N ℓ| / Real.sqrt ℓ ≤
            ((m.totient : ℝ) * Real.log ℓ) / Real.sqrt ℓ :=
          div_le_div_of_nonneg_right (abs_horizonRamanujanMangoldt_le m N ℓ) hsℓ.le
        _ ≤ ((m.totient : ℝ) * (5 * Real.log N)) / Real.sqrt N := by
          have hnum : (m.totient : ℝ) * Real.log ℓ ≤ (m.totient : ℝ) * (5 * Real.log N) :=
            mul_le_mul_of_nonneg_left hlogℓ (Nat.cast_nonneg _)
          exact (div_le_div_of_nonneg_right hnum hsℓ.le).trans
            (div_le_div_of_nonneg_left (by positivity) hsN hsqrt_le)
        _ = 5 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by ring
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul hjet hcorr (abs_nonneg _) (by positivity)
  have hrow_reg : ∀ n : ℕ, |regroupedExteriorDownwardPrimeRow g c N m n| ≤
      5 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N := by
    intro n
    have hcard : ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) ≤ linearPrimeStrip c := by
      have hbound := (exteriorPrimeCutoff_bounds_small_width hc0 hN hw).2
      rw [Nat.card_Ioc]
      exact_mod_cast (show exteriorPrimeCutoff c N - N ≤ linearPrimeStrip c by omega)
    unfold regroupedExteriorDownwardPrimeRow
    calc
      _ ≤ ∑ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
          |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
            (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
          (5 * (m.totient : ℝ) * Real.log N / Real.sqrt N) := sum_le_sum (hterm n)
      _ ≤ 5 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N := by
        rw [sum_const, nsmul_eq_mul]
        exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq (by ring)
  let S := (Icc 1 N).filter (fun n => N - linearPrimeStrip c ≤ n)
  have hrestrict : (∑ n ∈ Icc 1 N, actualExteriorDownwardRow g N m n ^ 2) =
      ∑ n ∈ S, regroupedExteriorDownwardPrimeRow g c N m n ^ 2 := by
    have heq : (∑ n ∈ Icc 1 N, actualExteriorDownwardRow g N m n ^ 2) =
        ∑ n ∈ Icc 1 N, regroupedExteriorDownwardPrimeRow g c N m n ^ 2 :=
      sum_congr rfl fun n hn => congrArg (fun t : ℝ => t ^ 2)
        (downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp m)
    rw [heq]
    symm
    refine sum_subset (filter_subset _ _) fun n hn hnS => ?_
    have hout : n < N - linearPrimeStrip c := lt_of_not_ge fun h => hnS (mem_filter.mpr ⟨hn, h⟩)
    rw [regroupedExteriorDownwardPrimeRow_eq_zero_small_width hc0 hn hgsupp hw hout m,
      zero_pow (by decide)]
  have hcard_S : (S.card : ℝ) ≤ (linearPrimeStrip c : ℝ) + 1 := by
    have hcontain : S ⊆ Icc (N - linearPrimeStrip c) N := fun n hn =>
      mem_Icc.mpr ⟨(mem_filter.mp hn).2, (mem_Icc.mp (mem_filter.mp hn).1).2⟩
    have hnat : S.card ≤ linearPrimeStrip c + 1 := by
      have h := card_le_card hcontain; rw [Nat.card_Icc] at h; omega
    exact_mod_cast hnat
  have hB1 : (linearPrimeStrip c : ℝ) + 1 ≤ (Real.exp 1 + 2) * c := by
    nlinarith only [hB_le, hc]
  have hcoef : 5 * (m.totient : ℝ) * linearPrimeStrip c ≤
      5 * (m.totient : ℝ) * ((Real.exp 1 + 1) * c) :=
    mul_le_mul_of_nonneg_left hB_le (by positivity)
  rw [hrestrict]
  calc
    (∑ n ∈ S, regroupedExteriorDownwardPrimeRow g c N m n ^ 2) ≤
        ∑ _n ∈ S, (5 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N) ^ 2 := by
      refine sum_le_sum fun n _ => ?_
      have hb := hrow_reg n
      have h := mul_self_le_mul_self (abs_nonneg _) hb
      rwa [← sq, sq_abs, ← sq] at h
    _ ≤ ((linearPrimeStrip c : ℝ) + 1) *
          ((5 * (m.totient : ℝ) * linearPrimeStrip c) ^ 2 * Real.log N ^ 2 / (N : ℝ)) := by
      rw [sum_const, nsmul_eq_mul]
      have hrew : (5 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N) ^ 2 =
          (5 * (m.totient : ℝ) * linearPrimeStrip c) ^ 2 * Real.log N ^ 2 / (N : ℝ) := by
        rw [div_pow, mul_pow, Real.sq_sqrt hN0.le]
      rw [hrew]
      exact mul_le_mul_of_nonneg_right hcard_S (by positivity)
    _ ≤ ((Real.exp 1 + 2) * c) *
          ((5 * (m.totient : ℝ) * ((Real.exp 1 + 1) * c)) ^ 2 * Real.log N ^ 2 / (N : ℝ)) :=
      mul_le_mul hB1
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcoef 2) (sq_nonneg _))
          hN0.le)
        (by positivity) (by positivity)
    _ = ((Real.exp 1 + 2) * (5 * m.totient * (Real.exp 1 + 1)) ^ 2) *
          c ^ 3 * Real.log N ^ 2 / (N : ℝ) := by ring

/-- Quadratic `O(m (1 + log m)^2 * (c^2 (1 + log c)^2 / log N + c^3 log N / N))` bound on the
totient-normalized full downward source. -/
private theorem exists_downward_quadratic_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log N → c / N ≤ 1 / 3 →
        ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m‖ ^ 2 ≤
          C * ((m : ℝ) * (1 + Real.log m) ^ 2) *
            (c ^ 2 * (1 + Real.log c) ^ 2 / Real.log N + c ^ 3 * Real.log N / (N : ℝ)) := by
  obtain ⟨Cp, hCp, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  let R₀ : ℝ := 2 * Real.exp 2
  let E : ℝ := Cp + Real.log R₀ + 4
  have hlogR₀ : 0 ≤ Real.log R₀ :=
    Real.log_nonneg (by dsimp only [R₀]; have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2); linarith)
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  let A_near : ℝ := 4 * Real.exp 2 * R₀ ^ 2 * E ^ 2
  let B_ext : ℝ := (Real.exp 1 + 2) * (5 * (Real.exp 1 + 1)) ^ 2
  have hB_ext : 0 ≤ B_ext := by dsimp only [B_ext]; positivity
  refine ⟨2 * (A_near + B_ext), by dsimp only [A_near]; positivity, ?_⟩
  intro m hm c hc1 N hN hlogN hw1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlogN
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have h1m : 1 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_natCast_nonneg m]
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have h1c : 1 ≤ 1 + Real.log c := by linarith only [hlogc0]
  have hentry : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
      |nearGammaDownwardCoefficient φ c N m n j| ≤
        E * ((m.totient : ℝ) * (1 + Real.log m)) * (1 + Real.log c) := by
    intro n hn j hj
    have hjN := (mem_filter.mp hj).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
    have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
      have h := (mem_filter.mp hj).2.2
      change |Real.log j - Real.log n| ≤ 2 * c / N at h
      simpa only [mul_div_assoc] using h
    let q := shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)
    let a := atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2)
    have hrem : |a - Real.log (1 / (c / N)) * q| ≤ Cp := by
      simpa only [a, q, mul_div_assoc] using hpair (c / N) (div_pos hc0 hN0) hw1 n j hs
    have hq : |q| ≤ 1 := by
      have h := abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp)
        (|Real.log j - Real.log n| / (c / N))
      change |shellAutocorr φ (|Real.log j - Real.log n| / (c / N))| ≤ ∫ u, φ u ^ 2 at h
      dsimp only [q]
      rw [abs_div, abs_of_pos hM, div_le_one hM]
      exact h
    have hcm : |ramanujanLagCoefficient m j| ≤ (m.totient : ℝ) :=
      BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m j
    have hjb : |ramanujanLogDivisorJet m j| ≤ 2 * (m.totient : ℝ) * (1 + Real.log m) :=
      abs_divisorJet_le_totient_log_quad hm j
    have hquot : (N : ℝ) / j ≤ linearNearRowRadius c :=
      (div_le_iff₀ hj0).mpr (nearRow_geometry_small_width hc0 hn hj hw).2.2
    have hloglow : 0 ≤ Real.log N - Real.log j := sub_nonneg.mpr
      (Real.log_le_log hj0 (by exact_mod_cast (mem_Icc.mp hjN).2))
    have hloghigh : Real.log N - Real.log j ≤ Real.log R₀ + Real.log c := by
      have h := Real.log_le_log (div_pos hN0 hj0) hquot
      have hR_eq : linearNearRowRadius c = R₀ * c := by
        unfold linearNearRowRadius; dsimp only [R₀]; ring
      rw [Real.log_div hN0.ne' hj0.ne', hR_eq, Real.log_mul (by dsimp only [R₀]; positivity) hc0.ne'] at h
      exact h
    have hlog : |Real.log (1 / (c / N)) - Real.log j| ≤ Real.log R₀ + 2 * Real.log c := by
      have hlogeq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
        rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
      rw [hlogeq, show Real.log N - Real.log c - Real.log j =
        (Real.log N - Real.log j) - Real.log c by ring]
      exact (abs_sub _ _).trans
        (by rw [abs_of_nonneg hloglow, abs_of_nonneg hlogc0]; linarith only [hloghigh])
    have heq : nearGammaDownwardCoefficient φ c N m n j =
        (a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j +
        (Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j +
        q * ramanujanLogDivisorJet m j := by
      rw [nearGammaDownwardCoefficient, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m
        (mem_Icc.mp hjN).1]
      dsimp only [a, q]; ring
    rw [heq]
    have h1 := mul_le_mul hrem hcm (abs_nonneg _) hCp
    have h2 := mul_le_mul (mul_le_mul hlog hq (abs_nonneg _) (by positivity))
      hcm (abs_nonneg _) (by positivity)
    have h3 := mul_le_mul hq hjb (abs_nonneg _) zero_le_one
    simp only [mul_one, one_mul] at h2 h3
    have htri : |(a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j +
        (Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j +
        q * ramanujanLogDivisorJet m j| ≤
        (Cp + Real.log R₀ + 2 * Real.log c) * (m.totient : ℝ) +
          2 * (m.totient : ℝ) * (1 + Real.log m) := by
      refine (abs_add_three _ _ _).trans ?_
      simp only [abs_mul]
      linarith only [h1, h2, h3,
        (by ring : Cp * (m.totient : ℝ) + (Real.log R₀ + 2 * Real.log c) * (m.totient : ℝ) =
          (Cp + Real.log R₀ + 2 * Real.log c) * (m.totient : ℝ))]
    let M_m := (m.totient : ℝ) * (1 + Real.log m)
    have hMm0 : 0 ≤ M_m := by dsimp only [M_m]; positivity
    have htot_Mm : (m.totient : ℝ) ≤ M_m :=
      le_mul_of_one_le_right htot_pos.le h1m
    have hterm1 : (Cp + Real.log R₀ + 2 * Real.log c) * (m.totient : ℝ) ≤
        (Cp + Real.log R₀ + 2) * M_m * (1 + Real.log c) := by
      have hc_le : Cp + Real.log R₀ + 2 * Real.log c ≤
          (Cp + Real.log R₀ + 2) * (1 + Real.log c) := by
        nlinarith only [hCp, hlogR₀, hlogc0]
      exact (mul_le_mul hc_le htot_Mm htot_pos.le (by positivity)).trans_eq (by ring)
    have hterm2 : 2 * (m.totient : ℝ) * (1 + Real.log m) ≤ 2 * M_m * (1 + Real.log c) := by
      have : 2 * (m.totient : ℝ) * (1 + Real.log m) = 2 * M_m := by dsimp only [M_m]; ring
      rw [this]
      exact le_mul_of_one_le_right (by positivity) h1c
    dsimp only [E]
    linarith only [htri, hterm1, hterm2,
      (by dsimp only [M_m]; ring : (Cp + Real.log R₀ + 4) * ((m.totient : ℝ) * (1 + Real.log m)) *
        (1 + Real.log c) = (Cp + Real.log R₀ + 2) * M_m * (1 + Real.log c) +
          2 * M_m * (1 + Real.log c))]
  have hnear_sq : ‖normalizedNearGammaDownwardVector φ c N m‖ ^ 2 ≤
      A_near * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * c ^ 2 * (1 + Real.log c) ^ 2 /
        Real.log N := by
    rw [normalizedNearGammaDownwardVector_norm_sq]
    apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
    have hb := sum_near_div_sqrt_sq_le_quadratic_width hc0 hN hw
      (nearGammaDownwardCoefficient φ c N m) (by positivity) hentry
    exact hb.trans_eq (by unfold linearNearRowRadius; dsimp only [A_near, R₀]; ring)
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp (div_pos hc0 hN0)
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq (div_pos hc0 hN0)]
    exact mul_pos (div_pos hc0 hN0) hM
  have hext_sq : ‖normalizedExteriorDownwardVector φ c N m‖ ^ 2 ≤
      B_ext * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * (c ^ 3 * Real.log N / (N : ℝ)) := by
    rw [normalizedExteriorDownwardVector_norm_sq]
    have h1m_sq : 1 ≤ (1 + Real.log (m : ℝ)) ^ 2 := one_le_pow₀ h1m
    have hraw := sum_actualExteriorDownwardRow_sq_le_subhorizon hg.continuous hc1 hN hlogN
      hgsupp hG hw m
    calc
      (∑ n ∈ Icc 1 N, actualExteriorDownwardRow (atomDilate φ (c / N)) N m n ^ 2) / Real.log N ≤
          (((Real.exp 1 + 2) * (5 * m.totient * (Real.exp 1 + 1)) ^ 2) *
            c ^ 3 * Real.log N ^ 2 / (N : ℝ)) / Real.log N :=
        div_le_div_of_nonneg_right hraw hL0.le
      _ = B_ext * (m.totient : ℝ) ^ 2 * 1 * (c ^ 3 * Real.log N / (N : ℝ)) := by
        dsimp only [B_ext]; field_simp [hN0.ne', hL0.ne']; ring
      _ ≤ B_ext * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * (c ^ 3 * Real.log N / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1m_sq (by positivity)) (by positivity)
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt htot_pos.le,
    normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc0]
  have htri := norm_sub_le (normalizedNearGammaDownwardVector φ c N m)
    (normalizedExteriorDownwardVector φ c N m)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have h2sq : ‖normalizedNearGammaDownwardVector φ c N m -
      normalizedExteriorDownwardVector φ c N m‖ ^ 2 ≤
      2 * (‖normalizedNearGammaDownwardVector φ c N m‖ ^ 2 +
        ‖normalizedExteriorDownwardVector φ c N m‖ ^ 2) := by
    nlinarith only [hsq, sq_nonneg (‖normalizedNearGammaDownwardVector φ c N m‖ -
      ‖normalizedExteriorDownwardVector φ c N m‖)]
  let r_d := c ^ 2 * (1 + Real.log c) ^ 2 / Real.log N + c ^ 3 * Real.log N / (N : ℝ)
  have hrd1 : c ^ 2 * (1 + Real.log c) ^ 2 / Real.log N ≤ r_d :=
    le_add_of_nonneg_right (by positivity)
  have hrd2 : c ^ 3 * Real.log N / (N : ℝ) ≤ r_d :=
    le_add_of_nonneg_left (by positivity)
  have hn' : ‖normalizedNearGammaDownwardVector φ c N m‖ ^ 2 ≤
      A_near * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * r_d := by
    refine hnear_sq.trans ?_
    rw [show A_near * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * c ^ 2 * (1 + Real.log c) ^ 2 /
        Real.log N = A_near * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 *
          (c ^ 2 * (1 + Real.log c) ^ 2 / Real.log N) by ring]
    exact mul_le_mul_of_nonneg_left hrd1 (by dsimp only [A_near]; positivity)
  have he' : ‖normalizedExteriorDownwardVector φ c N m‖ ^ 2 ≤
      B_ext * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * r_d :=
    hext_sq.trans (mul_le_mul_of_nonneg_left hrd2 (by positivity))
  calc
    (m.totient : ℝ)⁻¹ * ‖normalizedNearGammaDownwardVector φ c N m -
        normalizedExteriorDownwardVector φ c N m‖ ^ 2 ≤
      (m.totient : ℝ)⁻¹ * (2 * (A_near * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * r_d +
        B_ext * (m.totient : ℝ) ^ 2 * (1 + Real.log m) ^ 2 * r_d)) :=
      mul_le_mul_of_nonneg_left (h2sq.trans (mul_le_mul_of_nonneg_left
        (add_le_add hn' he') zero_le_two)) (inv_nonneg.mpr htot_pos.le)
    _ = 2 * (A_near + B_ext) * ((m.totient : ℝ) * (1 + Real.log m) ^ 2) * r_d := by
      field_simp [htot_pos.ne']
    _ ≤ 2 * (A_near + B_ext) * ((m : ℝ) * (1 + Real.log m) ^ 2) * r_d :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htot_le (sq_nonneg _))
          (by dsimp only [A_near]; positivity))
        (by dsimp only [r_d]; positivity)

/-! ## Section 4: Upward Prime Source Channel -/

/-- Shifted reciprocal upward error retaining `c^2 * (1 + log c) * (log N)^(1/k) / log N`
rather than `c^3 * (log N)^(1/k) / log N`. -/
private theorem exists_conductor_quadratic_shiftedReciprocal_variable_rate
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → ∀ shift : ℕ → ℕ,
        (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) / Real.log N ≤
          K * (m.totient : ℝ) ^ 2 * c ^ 2 * (1 + Real.log c) *
            Real.log N ^ (1 / (k : ℝ)) / Real.log N := by
  obtain ⟨C, hC, hsource⟩ :=
    exists_conductor_uniform_affineShellCorrection_linear_log_rate hφ hsupp hM
  let D : ℝ := 4 * (Real.log 4 + 4)
  have hD : 0 ≤ D := by
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [D]; positivity
  let K := 2 * C ^ 2 + 5 * D ^ 2
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro A hA k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hYlim : Tendsto (fun N : ℕ => Real.exp (Real.log N ^ (1 / (k : ℝ)))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / (k : ℝ))).comp hloglim)
  filter_upwards [hYlim.eventually (hsource (A * k) (by positivity) k),
    hloglim.eventually_ge_atTop 1, eventually_ge_atTop 1] with N hsourceN hL hN
  intro m hm hmN c hc shift
  let L := Real.log (N : ℝ)
  let Y := Real.exp (L ^ (1 / (k : ℝ)))
  let T := 2 * c * Y
  let a := C * c / L
  let b := D * (m.totient : ℝ) * c
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have h1c : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc]
  have htot : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have htot2 : (1 : ℝ) ≤ (m.totient : ℝ) ^ 2 := one_le_pow₀ htot
  have hs1 : 1 ≤ L ^ (1 / (k : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  have hs0 : 0 < L ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hsPow : (L ^ (1 / (k : ℝ))) ^ k = L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, one_div_mul_cancel hkR.ne', Real.rpow_one]
  have hY1 : 1 ≤ Y := Real.one_le_exp_iff.mpr hs0.le
  have hT : 1 ≤ T := by dsimp only [T]; nlinarith only [hc, hY1]
  have hmY : (m : ℝ) ≤ Real.log Y ^ (A * k) := by
    dsimp only [Y]
    rw [Real.log_exp, ← Real.rpow_mul hL0.le]
    have heq : (1 / (k : ℝ)) * (A * k) = A := by field_simp [hkR.ne']
    rw [heq]; exact hmN
  have hglobal : ∀ n ∈ Icc 1 N,
      |shiftedReciprocalUpwardRowError φ c shift N m n| ≤ b / Real.sqrt n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hquot : 1 ≤ (N : ℝ) / n := (le_div_iff₀ hn0).mpr (by simpa only [one_mul] using hnN)
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right
      (abs_affineShellCorrection_error_le_linear hm hφ hsupp hM n shift hc0 hquot)
      (Real.sqrt_nonneg _)
  have hgood : ∀ n ∈ Icc 1 N, T ≤ (N : ℝ) / n →
      |shiftedReciprocalUpwardRowError φ c shift N m n| ≤ a / Real.sqrt n := by
    intro n _ ht
    have hb := hsourceN.2 m hm hmY c ((N : ℝ) / n) hc ht shift n
    change |affinePrimeShellCorrectionOfShift m n shift φ c ((N : ℝ) / n) -
      ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m shift| ≤
        C * c / Real.log Y ^ k at hb
    rw [show Real.log Y = L ^ (1 / (k : ℝ)) by exact Real.log_exp _, hsPow] at hb
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right hb (Real.sqrt_nonneg _)
  have hsum := HTGeometry.sum_sq_le_harmonic_quotient_tail hN hT
    (shiftedReciprocalUpwardRowError φ c shift N m) hglobal hgood
  have hhead : a ^ 2 * (1 + L) ≤
      2 * C ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) := by
    have hfrac : (1 + L) / L ^ 2 ≤ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hL0)).mpr; nlinarith only [hL1]
    have hprod1 : (1 : ℝ) ≤ (m.totient : ℝ) ^ 2 * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le htot2 h1c) hs1
    calc
      a ^ 2 * (1 + L) = C ^ 2 * c ^ 2 * ((1 + L) / L ^ 2) := by dsimp only [a]; ring
      _ ≤ 2 * C ^ 2 * c ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ C ^ 2 * c ^ 2 by positivity)
        nlinarith only [h]
      _ ≤ (2 * C ^ 2 * c ^ 2) * ((m.totient : ℝ) ^ 2 * (1 + Real.log c) * (L ^ (1 / (k : ℝ)))) :=
        le_mul_of_one_le_right (by positivity) hprod1
      _ = _ := by ring
  have hlogT : 1 + Real.log (2 * T) ≤ 5 * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) := by
    have hid : 2 * T = 4 * c * Real.exp (L ^ (1 / (k : ℝ))) := by dsimp only [T, Y]; ring
    rw [hid, Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_mul (by norm_num) hc0.ne', Real.log_exp]
    have hl4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    have hlogc0 := Real.log_nonneg hc
    nlinarith only [hl4, hlogc0, h1c, hs1]
  have htail : b ^ 2 * (1 + Real.log (2 * T)) ≤
      5 * D ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) := by
    calc
      b ^ 2 * (1 + Real.log (2 * T)) ≤ b ^ 2 * (5 * (1 + Real.log c) * (L ^ (1 / (k : ℝ)))) :=
        mul_le_mul_of_nonneg_left hlogT (sq_nonneg _)
      _ = _ := by dsimp only [b]; ring
  have hraw : (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) ≤
      K * (m.totient : ℝ) ^ 2 * c ^ 2 * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) := by
    have hb := hsum.trans (add_le_add hhead htail)
    dsimp only [K]
    linarith only [hb,
      (by ring : (2 * C ^ 2 + 5 * D ^ 2) * (m.totient : ℝ) ^ 2 * c ^ 2 *
        (1 + Real.log c) * (L ^ (1 / (k : ℝ))) =
        2 * C ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) +
          5 * D ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 * (1 + Real.log c) * (L ^ (1 / (k : ℝ))))]
  exact div_le_div_of_nonneg_right hraw hL0.le

private theorem exists_conductor_quadratic_reciprocalUpward_variable_rate
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → ∀ B : ℕ, ⌈c⌉₊ ≤ B →
        (∑ n ∈ Icc 1 N,
          ((reciprocalUpwardCoefficient φ c B N m n -
            ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n) ^ 2) / Real.log N ≤
          K * (m.totient : ℝ) ^ 2 * c ^ 2 * (1 + Real.log c) *
            Real.log N ^ (1 / (k : ℝ)) / Real.log N := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_conductor_quadratic_shiftedReciprocal_variable_rate hφ hsupp hM
  refine ⟨K, hK, fun A hA k hk => ?_⟩
  filter_upwards [hbound A hA k hk] with N hN
  intro m hm hmN c hc B hB
  have hc0 := zero_lt_one.trans_le hc
  have hrow (n : ℕ) (hn : 1 ≤ n) :
      (reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n =
      (shiftedReciprocalUpwardRowError φ c id N m n +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n) / 2 := by
    rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc0 hB N m n hn]
    dsimp only [shiftedReciprocalUpwardRowError]
    rw [shellCorrectionOfShift_reflected hm]
    change _ = ((affinePrimeShellCorrectionOfShift m n id φ c ((N : ℝ) / n) -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n + _) / 2
    ring
  have hsum : (∑ n ∈ Icc 1 N,
      ((reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n) ^ 2) ≤
      ∑ n ∈ Icc 1 N, (shiftedReciprocalUpwardRowError φ c id N m n ^ 2 +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n ^ 2) / 2 := by
    refine sum_le_sum fun n hn => ?_
    rw [hrow n (mem_Icc.mp hn).1]
    nlinarith only [sq_nonneg (shiftedReciprocalUpwardRowError φ c id N m n -
      shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n)]
  have hfinal := div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)
  rw [← sum_div, sum_add_distrib, div_right_comm, add_div] at hfinal
  have hp := hN m hm hmN c hc id
  have hn := hN m hm hmN c hc (reflectedAffineShift m)
  linarith only [hfinal, hp, hn]

/-- Exact prime-product discrepancy window `N ≤ k * n + B ∧ k * n ≤ N + B` reduces the
linearized-to-reciprocal cutoff error from `O(φ(m)^2 * B^5)` to
`O(φ(m)^2 * B^2 + φ(m)^2 * B^5 * (log N / N)^2)`. -/
private theorem linearizedUpwardCoefficient_quadratic_boundary_budget {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m N B : ℕ} (hm : 0 < m) (hN : 1 ≤ N)
    (hlogN : 1 ≤ Real.log N) (h2B : 2 * B ≤ N) {c : ℝ} (hc : 0 < c) (hcN : c ≤ (N : ℝ)) :
    (∑ n ∈ Icc 1 N,
      ((linearizedUpwardCoefficient φ c B N m n -
        reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n) ^ 2) ≤
      1152 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 2 +
        4096 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 5 * (Real.log (N : ℝ) / N) ^ 2 := by
  have hm1 : 1 ≤ m := hm
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hBN : B ≤ N := by omega
  -- Pointwise vanishing outside `S_ex n := {k ∈ Icc 1 (N + B) | N ≤ k * n + B ∧ k * n ≤ N + B}`.
  let S_ex : ℕ → Finset ℕ := fun n =>
    (Icc 1 (N + B)).filter (fun k => N ≤ k * n + B ∧ k * n ≤ N + B)
  have hrow_ex : ∀ n ∈ Icc 1 N,
      |linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n| ≤
        4 * (B : ℝ) * m.totient * ∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    let L_val : ℝ := (B : ℝ) * (4 * m.totient * (∫ u, φ u ^ 2))
    have hpoint : ∀ k ∈ Icc 1 (N + B),
        |∑ h ∈ Icc 1 B, (linearizedUpwardOffset φ c N m n k h -
          reciprocalUpwardOffset φ c N m n k h)| ≤
          if N ≤ k * n + B ∧ k * n ≤ N + B then L_val else 0 := by
      intro k hk
      have hk1 := (mem_Icc.mp hk).1
      have hT : 1 ≤ k * n := Nat.mul_pos hk1 hn1
      by_cases hex : N ≤ k * n + B ∧ k * n ≤ N + B
      · rw [if_pos hex]
        have h := (abs_sum_le_sum_abs _ (Icc 1 B)).trans
          (sum_le_sum fun h _ => abs_linearizedUpwardOffset_sub_reciprocal_le hφ hsupp c N m n k h)
        simpa only [L_val, sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] using h
      · rw [if_neg hex]
        have hz : (∑ h ∈ Icc 1 B, (linearizedUpwardOffset φ c N m n k h -
            reciprocalUpwardOffset φ c N m n k h)) = 0 := by
          refine sum_eq_zero fun h hh => ?_
          have hhB := (mem_Icc.mp hh).2
          by_cases hhT : h < k * n
          · have hfar : k * n + B < N ∨ N + B < k * n := by omega
            rcases hfar with hfar | hfar
            · have hp : k * n + h ≤ N := by omega
              have hncut : h < k * n ∧ k * n - h ≤ N := ⟨hhT, by omega⟩
              have hkcut : k * n ≤ N := by omega
              simp only [linearizedUpwardOffset, reciprocalUpwardOffset, if_pos hp, if_pos hncut,
                if_pos hkcut, ramanujanLagCoefficient_sub_eq_reflected hm1 hhT.le, sub_self]
            · have hp : ¬ k * n + h ≤ N := by omega
              have hncut : ¬ (h < k * n ∧ k * n - h ≤ N) := by omega
              have hkcut : ¬ k * n ≤ N := by omega
              simp only [linearizedUpwardOffset, reciprocalUpwardOffset, if_neg hp, if_neg hncut,
                if_neg hkcut, add_zero, sub_self]
          · have hT0 : (0 : ℝ) < (k * n : ℕ) := by exact_mod_cast hT
            have hNc : (1 : ℝ) ≤ (N : ℝ) / c := (one_le_div hc).mpr hcN
            have hhT' : (1 : ℝ) ≤ (h : ℝ) / (k * n : ℕ) :=
              (one_le_div hT0).mpr (by exact_mod_cast (show k * n ≤ h by omega))
            have hzero := shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
              ((one_le_mul_of_one_le_of_one_le hNc hhT').trans (le_abs_self _))
            simp only [linearizedUpwardOffset, reciprocalUpwardOffset, hzero, mul_zero, sub_self]
        rw [hz, abs_zero]
    unfold linearizedUpwardCoefficient reciprocalUpwardCoefficient
    rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hM)]
    calc
      1 / (∫ u, φ u ^ 2) * |∑ k ∈ Icc 1 (N + B),
          ((ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, linearizedUpwardOffset φ c N m n k h -
            (ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, reciprocalUpwardOffset φ c N m n k h)| ≤
        1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
          |(ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, linearizedUpwardOffset φ c N m n k h -
            (ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, reciprocalUpwardOffset φ c N m n k h| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ 1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
          if N ≤ k * n + B ∧ k * n ≤ N + B then
            (ArithmeticFunction.vonMangoldt k : ℝ) / k * L_val else 0 := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun k hk => ?_) (by positivity)
        rw [← mul_sub, ← sum_sub_distrib, abs_mul,
          abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))]
        have hpk := hpoint k hk
        split_ifs at hpk ⊢
        · exact mul_le_mul_of_nonneg_left hpk (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
        · simpa only [mul_zero] using mul_le_mul_of_nonneg_left hpk
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
      _ = 4 * (B : ℝ) * m.totient * ∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k := by
        dsimp only [S_ex, L_val]
        rw [← sum_filter, ← sum_mul]
        field_simp [hM.ne']; ring
  -- Every `S_ex n` lies inside `Icc ((N - B) / n) ((N + B) / n)`, and `N ≤ 2 * (k * n)`.
  have hS_sub : ∀ n : ℕ, 1 ≤ n → S_ex n ⊆ Icc ((N - B) / n) ((N + B) / n) := by
    intro n hn1 k hk
    obtain ⟨_, hlo, hhi⟩ := mem_filter.mp hk
    have ha : (N - B) / n ≤ k :=
      (Nat.div_le_div_right (show N - B ≤ k * n by omega)).trans_eq
        (Nat.mul_div_cancel k (by omega))
    have hb : k ≤ (N + B) / n :=
      (Nat.mul_div_cancel k (by omega)).symm.trans_le (Nat.div_le_div_right hhi)
    exact mem_Icc.mpr ⟨ha, hb⟩
  have hcard_mul : ∀ n : ℕ, 1 ≤ n → ((S_ex n).card : ℝ) * n ≤ 2 * (B : ℝ) + 2 * n := by
    intro n hn1
    let a₀ := (N - B) / n
    let b₀ := (N + B) / n
    have hcard_le : (S_ex n).card ≤ (Icc a₀ b₀).card := card_le_card (hS_sub n hn1)
    by_cases hab : a₀ ≤ b₀
    · have hdiv_lo : N - B < (a₀ + 1) * n := by
        have h1 := Nat.div_add_mod (N - B) n
        have h2 := Nat.mod_lt (N - B) (show 0 < n by omega)
        dsimp only [a₀]
        nlinarith only [h1, h2, Nat.mul_comm n ((N - B) / n)]
      have hdiv_hi : b₀ * n ≤ N + B := Nat.div_mul_le_self (N + B) n
      have hnat : (b₀ + 1 - a₀) * n ≤ 2 * B + 2 * n := by
        have hsub_mul : (b₀ + 1 - a₀) * n = b₀ * n + n - a₀ * n :=
          Nat.sub_mul (b₀ + 1) a₀ n |>.trans (by ring_nf)
        omega
      have h1 : (S_ex n).card * n ≤ 2 * B + 2 * n := by
        have hc_eq : (Icc a₀ b₀).card = b₀ + 1 - a₀ := Nat.card_Icc a₀ b₀
        exact (Nat.mul_le_mul_right n (hcard_le.trans_eq hc_eq)).trans hnat
      exact_mod_cast h1
    · have hemp : Icc a₀ b₀ = ∅ := Icc_eq_empty hab
      rw [hemp, card_empty] at hcard_le
      have h0 : (S_ex n).card = 0 := Nat.eq_zero_of_le_zero hcard_le
      rw [h0, Nat.cast_zero, zero_mul]
      positivity
  -- Split `Icc 1 N` into `Icc 1 B` and `Ioc B N`.
  have hpart : Icc 1 N = Icc 1 B ∪ Ioc B N := by
    ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 B) (Ioc B N) := by
    rw [Finset.disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hpart, sum_union hdisj]
  -- High rows `n ∈ Ioc B N`: `card ≤ 3` and `Λ(k)/k ≤ 2 * √(2n/N)`.
  have hhigh : (∑ n ∈ Ioc B N,
      ((linearizedUpwardCoefficient φ c B N m n -
        reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n) ^ 2) ≤
      1152 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 2 := by
    have hpt : ∀ n ∈ Ioc B N,
        ((linearizedUpwardCoefficient φ c B N m n -
          reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n) ^ 2 ≤
          1152 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 2 / (N : ℝ) := by
      intro n hn
      obtain ⟨hBn, hnN⟩ := mem_Ioc.mp hn
      have hn1 : 1 ≤ n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      have hcard3 : ((S_ex n).card : ℝ) ≤ 3 := by
        have hm_c := hcard_mul n hn1
        have hBn_R : (B : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hBn)
        have hlt4 : ((S_ex n).card : ℝ) * n < 4 * (n : ℝ) := by nlinarith only [hm_c, hBn_R]
        have hnat4 : (S_ex n).card < 4 := by
          have : ((S_ex n).card : ℝ) < 4 := by nlinarith only [hlt4, hn0]
          exact_mod_cast this
        exact_mod_cast (show (S_ex n).card ≤ 3 by omega)
      have hterm_k : ∀ k ∈ S_ex n,
          (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤ 2 * Real.sqrt (2 * (n : ℝ) / N) := by
        intro k hk
        obtain ⟨hkI, hlo, _⟩ := mem_filter.mp hk
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hkI).1
        have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
        have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
        have hN_2kn : (N : ℝ) ≤ 2 * (k : ℝ) * n := by
          exact_mod_cast (show N ≤ 2 * k * n by omega)
        have hinv_k : 1 / (k : ℝ) ≤ 2 * (n : ℝ) / N := by
          rw [div_le_div_iff₀ hk0 hN0, one_mul]
          linarith only [hN_2kn]
        have hinv_sk : 1 / Real.sqrt k ≤ Real.sqrt (2 * (n : ℝ) / N) := by
          have h := Real.sqrt_le_sqrt hinv_k
          rwa [Real.sqrt_div zero_le_one, Real.sqrt_one] at h
        have hvm : (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤ 2 * (1 / Real.sqrt k) := by
          calc
            (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤ Real.log k / k :=
              div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log hk0.le
            _ = (Real.log k * (Real.sqrt k)⁻¹) * (1 / Real.sqrt k) := by
              rw [← Real.sq_sqrt hk0.le]; field_simp [hsk.ne']
            _ ≤ 2 * (1 / Real.sqrt k) :=
              mul_le_mul_of_nonneg_right (_root_.RHTower.WeilAbscissa.log_div_sqrt_le hk1)
                (by positivity)
        exact hvm.trans (mul_le_mul_of_nonneg_left hinv_sk zero_le_two)
      have hsum_k : (∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k) ≤
          6 * Real.sqrt 2 * Real.sqrt n / Real.sqrt N := by
        calc
          (∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k) ≤
              ∑ _k ∈ S_ex n, 2 * Real.sqrt (2 * (n : ℝ) / N) := sum_le_sum hterm_k
          _ = ((S_ex n).card : ℝ) * (2 * Real.sqrt (2 * (n : ℝ) / N)) := by
            rw [sum_const, nsmul_eq_mul]
          _ ≤ 3 * (2 * Real.sqrt (2 * (n : ℝ) / N)) :=
            mul_le_mul_of_nonneg_right hcard3 (by positivity)
          _ = 6 * Real.sqrt 2 * Real.sqrt n / Real.sqrt N := by
            rw [Real.sqrt_div (by positivity), Real.sqrt_mul zero_le_two]; ring
      have habs_div : |(linearizedUpwardCoefficient φ c B N m n -
          reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n| ≤
          24 * Real.sqrt 2 * (m.totient : ℝ) * B / Real.sqrt N := by
        rw [abs_div, abs_of_pos hsn]
        have hb := (div_le_div_of_nonneg_right (hrow_ex n (mem_Icc.mpr ⟨hn1, hnN⟩)) hsn.le).trans
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum_k (by positivity)) hsn.le)
        refine hb.trans_eq ?_
        field_simp [hsn.ne', (Real.sqrt_pos.mpr hN0).ne']; ring
      have hsq := mul_self_le_mul_self (abs_nonneg _) habs_div
      rw [← sq, sq_abs, ← sq] at hsq
      refine hsq.trans_eq ?_
      rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt zero_le_two, Real.sq_sqrt hN0.le]
      ring
    have hcard_hi : ((Ioc B N).card : ℝ) ≤ (N : ℝ) := by
      rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le N B
    calc
      (∑ n ∈ Ioc B N, ((linearizedUpwardCoefficient φ c B N m n -
          reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n) ^ 2) ≤
          ∑ _n ∈ Ioc B N, 1152 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 2 / (N : ℝ) :=
        sum_le_sum hpt
      _ = ((Ioc B N).card : ℝ) * (1152 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 2 / (N : ℝ)) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (1152 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 2 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard_hi (by positivity)
      _ = 1152 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 2 := by field_simp [hN0.ne']
  -- Low rows `n ∈ Icc 1 B`: `card ≤ 4 * B / n` and `Λ(k)/k ≤ 4 * n * log N / N`.
  have hlow : (∑ n ∈ Icc 1 B,
      ((linearizedUpwardCoefficient φ c B N m n -
        reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n) ^ 2) ≤
      4096 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 5 * (Real.log (N : ℝ) / N) ^ 2 := by
    have hpt : ∀ n ∈ Icc 1 B,
        ((linearizedUpwardCoefficient φ c B N m n -
          reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n) ^ 2 ≤
          4096 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 4 * (Real.log (N : ℝ) / N) ^ 2 := by
      intro n hn
      obtain ⟨hn1, hnB⟩ := mem_Icc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hsn1 : 1 ≤ Real.sqrt (n : ℝ) := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hn1 : (1 : ℝ) ≤ n)
      have hnB_R : (n : ℝ) ≤ B := by exact_mod_cast hnB
      have hcard_4B : ((S_ex n).card : ℝ) ≤ 4 * (B : ℝ) / n := by
        rw [le_div_iff₀ hn0]
        linarith only [hcard_mul n hn1, hnB_R]
      have hterm_k : ∀ k ∈ S_ex n,
          (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤ 4 * (n : ℝ) * Real.log N / N := by
        intro k hk
        obtain ⟨hkI, hlo, _⟩ := mem_filter.mp hk
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hkI).1
        have hk_2N : (k : ℝ) ≤ 2 * (N : ℝ) := by
          exact_mod_cast (show k ≤ 2 * N from (mem_Icc.mp hkI).2.trans (by omega))
        have hlogk : Real.log k ≤ 2 * Real.log N := by
          have hl := Real.log_le_log hk0 hk_2N
          rw [Real.log_mul (by norm_num) hN0.ne'] at hl
          have hl2 : Real.log 2 ≤ 1 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
          linarith only [hl, hl2, hlogN]
        have hN_2kn : (N : ℝ) ≤ 2 * (k : ℝ) * n := by
          exact_mod_cast (show N ≤ 2 * k * n by omega)
        have hinv_k : 1 / (k : ℝ) ≤ 2 * (n : ℝ) / N := by
          rw [div_le_div_iff₀ hk0 hN0, one_mul]
          linarith only [hN_2kn]
        calc
          (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤ Real.log k / k :=
            div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log hk0.le
          _ ≤ (2 * Real.log N) * (1 / (k : ℝ)) := by
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_right hlogk (by positivity)
          _ ≤ (2 * Real.log N) * (2 * (n : ℝ) / N) :=
            mul_le_mul_of_nonneg_left hinv_k (by positivity)
          _ = 4 * (n : ℝ) * Real.log N / N := by ring
      have hsum_k : (∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k) ≤
          16 * (B : ℝ) * Real.log N / N := by
        calc
          (∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k) ≤
              ∑ _k ∈ S_ex n, 4 * (n : ℝ) * Real.log N / N := sum_le_sum hterm_k
          _ = ((S_ex n).card : ℝ) * (4 * (n : ℝ) * Real.log N / N) := by
            rw [sum_const, nsmul_eq_mul]
          _ ≤ (4 * (B : ℝ) / n) * (4 * (n : ℝ) * Real.log N / N) :=
            mul_le_mul_of_nonneg_right hcard_4B (by positivity)
          _ = 16 * (B : ℝ) * Real.log N / N := by field_simp [hn0.ne', hN0.ne']; ring
      have habs_div : |(linearizedUpwardCoefficient φ c B N m n -
          reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n| ≤
          64 * (m.totient : ℝ) * (B : ℝ) ^ 2 * (Real.log (N : ℝ) / N) := by
        rw [abs_div, abs_of_pos (zero_lt_one.trans_le hsn1)]
        have h1 : |linearizedUpwardCoefficient φ c B N m n -
            reciprocalUpwardCoefficient φ c B N m n| / Real.sqrt n ≤
            |linearizedUpwardCoefficient φ c B N m n -
              reciprocalUpwardCoefficient φ c B N m n| :=
          div_le_self (abs_nonneg _) hsn1
        exact (h1.trans (hrow_ex n (mem_Icc.mpr ⟨hn1, hnB.trans hBN⟩))).trans
          ((mul_le_mul_of_nonneg_left hsum_k (by positivity)).trans_eq (by ring))
      have hsq := mul_self_le_mul_self (abs_nonneg _) habs_div
      rw [← sq, sq_abs, ← sq] at hsq
      exact hsq.trans_eq (by ring)
    calc
      (∑ n ∈ Icc 1 B, ((linearizedUpwardCoefficient φ c B N m n -
          reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n) ^ 2) ≤
          ∑ _n ∈ Icc 1 B, 4096 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 4 * (Real.log (N : ℝ) / N) ^ 2 :=
        sum_le_sum hpt
      _ = 4096 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 5 * (Real.log (N : ℝ) / N) ^ 2 := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]; ring
  linarith only [hlow, hhigh]

private theorem exists_normalizedUpward_quadratic_conductor_variable_rate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖normalizedUpwardPrimeResidual φ c N m‖ ^ 2 ≤
          K * (m.totient : ℝ) ^ 2 *
            (c ^ 2 * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
  obtain ⟨Ca, hCa, ha⟩ := exists_logarithmicUpward_uniform_conductor_harmonic_bound hφ hsupp hM
  obtain ⟨Cs, hCs, hs⟩ := exists_conductor_quadratic_reciprocalUpward_variable_rate hφ hsupp hM
  let d : ℝ := Real.exp 1 + 2
  let Ca' := Ca * d ^ 6
  let Cb₁ := 1152 * d ^ 2
  let Cb₂ := 4096 * d ^ 5
  let K := 3 * (Ca' + Cb₁ + Cb₂ + Cs)
  refine ⟨K, by dsimp only [K, Ca', Cb₁, Cb₂, d]; positivity, fun A hA k hk => ?_⟩
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hs A hA k hk, eventually_ge_atTop 1, hloglim.eventually_ge_atTop 1]
    with N hsource hN hlog
  intro m hm hmN c hc hlarge
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have h1c : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc]
  have hs1 : 1 ≤ Real.log (N : ℝ) ^ (1 / (k : ℝ)) := Real.one_le_rpow hlog (by positivity)
  let B := linearPrimeStrip c
  have hBc : (B : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc
  have hB1 : (B : ℝ) + 1 ≤ d * c := by dsimp only [d]; nlinarith only [hBc, hc]
  have hBd : (B : ℝ) ≤ d * c := by linarith only [hB1]
  have hc2 : c ≤ c ^ 2 := by nlinarith only [hc]
  have hexp := Real.exp_pos 1
  have hwidth : c / N ≤ 1 := by
    apply (div_le_one hN0).mpr
    have hcoef : 1 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [hlarge, hc2, h]
  have hcN : c ≤ (N : ℝ) := (div_le_one hN0).mp hwidth
  have h2BN : 2 * B ≤ N := by
    have hcoef : 2 * (Real.exp 1 + 1) ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h1 := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ 2 * (Real.exp 1 + 1) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    have h : 2 * (B : ℝ) ≤ N := by nlinarith only [hBc, h1, h2, hlarge]
    exact_mod_cast h
  have hBN : B ≤ N := by omega
  have hkernel : 2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) := by
    have hcoef : 2 * (Real.exp 1 + 3) * (Real.exp 1 + 1) ≤
        4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h1 := mul_le_mul_of_nonneg_left hBc
      (show 0 ≤ 2 * ((Real.exp 1 + 3) * c) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h1, h2, hlarge]
  have hB : ⌈c⌉₊ ≤ B := by
    apply Nat.ceil_le.mpr
    have h := mul_le_mul_of_nonneg_left
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc0.le
    have hce : c ≤ c * Real.exp 1 := by simpa only [mul_one] using h
    exact hce.trans (Nat.le_ceil _)
  let R := c ^ 2 * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
    c ^ 10 * (Real.log (N : ℝ) / N) ^ 2
  have hR1 : c ^ 2 / Real.log N ≤ R := by
    have hprod1 : 1 ≤ (1 + Real.log c) * Real.log (N : ℝ) ^ (1 / (k : ℝ)) :=
      one_le_mul_of_one_le_of_one_le h1c hs1
    have hle : c ^ 2 ≤ c ^ 2 * ((1 + Real.log c) * Real.log (N : ℝ) ^ (1 / (k : ℝ))) :=
      le_mul_of_one_le_right (sq_nonneg c) hprod1
    have hdiv : c ^ 2 / Real.log N ≤
        c ^ 2 * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N :=
      (div_le_div_of_nonneg_right hle hL0.le).trans_eq (by ring)
    exact hdiv.trans (le_add_of_nonneg_right (by positivity))
  have hR2 : c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 ≤ R :=
    le_add_of_nonneg_left (by positivity)
  have hR3 : c ^ 2 * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N ≤ R :=
    le_add_of_nonneg_right (by positivity)
  let a : ℕ → ℝ := fun n =>
    (logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) / Real.sqrt n
  let b : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
  let r : ℕ → ℝ := fun n =>
    (reciprocalUpwardCoefficient φ c B N m n -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n
  have ha' : (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N ≤ Ca' * (m.totient : ℝ) ^ 2 * R := by
    have hp := pow_le_pow_left₀ (show 0 ≤ (B : ℝ) + 1 by positivity) hB1 6
    have hb := (ha m N hN hlog c hc hwidth B hBN hkernel).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (show 0 ≤ Ca * (m.totient : ℝ) ^ 2 * c ^ 4 by positivity))
        (sq_nonneg (Real.log (N : ℝ) / N)))
    have hb_eq : (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N ≤
        Ca' * (m.totient : ℝ) ^ 2 * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) :=
      hb.trans_eq (by dsimp only [Ca']; ring)
    exact hb_eq.trans (mul_le_mul_of_nonneg_left hR2 (by dsimp only [Ca', d]; positivity))
  have hb' : (∑ n ∈ Icc 1 N, b n ^ 2) / Real.log N ≤ (Cb₁ + Cb₂) * (m.totient : ℝ) ^ 2 * R := by
    have hb_raw := linearizedUpwardCoefficient_quadratic_boundary_budget hφ hsupp hM hm
      hN hlog h2BN hc0 hcN
    have hp2 : (B : ℝ) ^ 2 ≤ d ^ 2 * c ^ 2 :=
      (pow_le_pow_left₀ (Nat.cast_nonneg B) hBd 2).trans_eq (by ring)
    have hp5 : (B : ℝ) ^ 5 ≤ d ^ 5 * c ^ 10 := by
      have h1 : (B : ℝ) ^ 5 ≤ d ^ 5 * c ^ 5 :=
        (pow_le_pow_left₀ (Nat.cast_nonneg B) hBd 5).trans_eq (by ring)
      exact h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc (by norm_num : 5 ≤ 10))
        (by dsimp only [d]; positivity))
    have ht1 : 1152 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 2 / Real.log N ≤
        Cb₁ * (m.totient : ℝ) ^ 2 * R := by
      calc
        1152 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 2 / Real.log N ≤
            1152 * (m.totient : ℝ) ^ 2 * (d ^ 2 * c ^ 2) / Real.log N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 (by positivity)) hL0.le
        _ = Cb₁ * (m.totient : ℝ) ^ 2 * (c ^ 2 / Real.log N) := by dsimp only [Cb₁]; ring
        _ ≤ Cb₁ * (m.totient : ℝ) ^ 2 * R :=
          mul_le_mul_of_nonneg_left hR1 (by dsimp only [Cb₁, d]; positivity)
    have ht2 : (4096 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 5 * (Real.log (N : ℝ) / N) ^ 2) /
        Real.log N ≤ Cb₂ * (m.totient : ℝ) ^ 2 * R := by
      calc
        (4096 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 5 * (Real.log (N : ℝ) / N) ^ 2) / Real.log N ≤
            4096 * (m.totient : ℝ) ^ 2 * (B : ℝ) ^ 5 * (Real.log (N : ℝ) / N) ^ 2 :=
          div_le_self (by positivity) hlog
        _ ≤ 4096 * (m.totient : ℝ) ^ 2 * (d ^ 5 * c ^ 10) * (Real.log (N : ℝ) / N) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp5 (by positivity)) (sq_nonneg _)
        _ = Cb₂ * (m.totient : ℝ) ^ 2 * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
          dsimp only [Cb₂]; ring
        _ ≤ Cb₂ * (m.totient : ℝ) ^ 2 * R :=
          mul_le_mul_of_nonneg_left hR2 (by dsimp only [Cb₂, d]; positivity)
    have hdiv := div_le_div_of_nonneg_right hb_raw hL0.le
    rw [add_div] at hdiv
    exact hdiv.trans ((add_le_add ht1 ht2).trans_eq (by ring))
  have hr' : (∑ n ∈ Icc 1 N, r n ^ 2) / Real.log N ≤ Cs * (m.totient : ℝ) ^ 2 * R := by
    have hb := hsource m hm hmN c hc B hB
    calc
      _ ≤ Cs * (m.totient : ℝ) ^ 2 * c ^ 2 * (1 + Real.log c) *
          Real.log N ^ (1 / (k : ℝ)) / Real.log N := hb
      _ = (Cs * (m.totient : ℝ) ^ 2) *
          (c ^ 2 * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N) := by ring
      _ ≤ Cs * (m.totient : ℝ) ^ 2 * R :=
        mul_le_mul_of_nonneg_left hR3 (by positivity)
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) : actualUpwardRowError φ c N m n = a n + b n + r n := by
    have hsqrt : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr
      (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < n)).ne'
    have hu : upwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) =
        logarithmicUpwardCoefficient φ c B N m n / Real.sqrt n := by
      apply (eq_div_iff hsqrt).mpr
      simpa only [mul_comm] using sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width
        hsupp hc0 hn hwidth m
    rw [actualUpwardRowError, hu]
    dsimp only [a, b, r]; ring
  rw [normalizedUpwardPrimeResidual_norm_sq]
  have hsum : (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) ≤
      ∑ n ∈ Icc 1 N, 3 * (a n ^ 2 + b n ^ 2 + r n ^ 2) := by
    refine sum_le_sum fun n hn => ?_
    rw [hrow n hn]
    nlinarith only [sq_nonneg (a n - b n), sq_nonneg (a n - r n), sq_nonneg (b n - r n)]
  have hfinal := div_le_div_of_nonneg_right hsum hL0.le
  rw [← mul_sum, sum_add_distrib, sum_add_distrib, mul_div_assoc, add_div, add_div] at hfinal
  exact hfinal.trans ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha' hb') hr')
    (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by dsimp only [K]; ring))

/-! ## Section 5: Complete-Weil Quadratic Residual Assembly and Summed Relative Budget -/

private theorem norm_eight_signed_sq_le_quad {E : Type*} [SeminormedAddCommGroup E]
    (p s c x q y z u : E) :
    ‖-p + s + c - x + q + (y + z) - u‖ ^ 2 ≤
      8 * (‖p‖ ^ 2 + ‖s‖ ^ 2 + ‖c‖ ^ 2 + ‖x‖ ^ 2 +
        ‖q‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 + ‖u‖ ^ 2) := by
  have h2 : ∀ a b : E, ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := fun a b => by
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    nlinarith only [h, sq_nonneg (‖a‖ - ‖b‖)]
  have h4 : ∀ a b c d : E, ‖a + b + c + d‖ ^ 2 ≤
      4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := fun a b c d => by
    have h := h2 (a + b) (c + d)
    rw [← add_assoc] at h
    linarith only [h, h2 a b, h2 c d]
  have hid : -p + s + c - x + q + (y + z) - u =
      (-p + s + c + -x) + (q + y + z + -u) := by abel
  rw [hid]
  have ha := h2 (-p + s + c + -x) (q + y + z + -u)
  have hb := h4 (-p) s c (-x)
  have hc := h4 q y z (-u)
  rw [norm_neg, norm_neg] at hb
  rw [norm_neg] at hc
  linarith only [ha, hb, hc]

/-- **Quadratic-overlap `O(m (1 + log m)^2)` complete-Weil conductor residual bound.**
Across every logarithmic conductor range `m ≤ (log N)^A` (`A ≥ 0`), the complete Weil residual of
mode `m` has squared norm `O(m (1 + log m)^2 * (c^2 (1 + log c)^3 (log N)^(1/k) / log N + c^10 (log N / N)^2))`,
reducing the leading overlap power from `c^5` to `c^2`. -/
theorem exists_completeWeil_quadratic_conductor_residual_variable_rate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          K * ((m : ℝ) * (1 + Real.log m) ^ 2) *
            (c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_quad_bound
  obtain ⟨Cs, hCs, hs⟩ := exists_selfError_quad_bound hφ hsupp hM
  obtain ⟨Cx, hCx, hx⟩ := exists_crossError_quadratic_conductor_bound hφ hsupp hM
  obtain ⟨Cq, hCq, hq⟩ := exists_poleError_quadratic_conductor_bound hφ hsupp hM
  obtain ⟨Cd, hCd, hdown⟩ := exists_downward_quadratic_conductor_bound hφ hsupp hM
  obtain ⟨Cn, hCn, hnear⟩ := exists_nearCenter_quadratic_conductor_bound φ
  obtain ⟨Cu, hCu, hup⟩ := exists_normalizedUpward_quadratic_conductor_variable_rate hφ hsupp hM
  let Cc := 742 * (completeWeilPoleShift φ 1) ^ 2
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  let K := 8 * (Cp + Cs + Cc + Cx + Cq + 2 * Cd + Cn + Cu) + 1
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro A hA k hk
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall_A : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / (2 * A + 2)) := by
    have hpos : 0 < 1 / (2 * A + 2) := by positivity
    have hsm := tendsto_natCast_atTop_atTop.eventually ((isLittleO_log_rpow_atTop hpos).bound zero_lt_one)
    filter_upwards [hsm, eventually_ge_atTop 1] with N hN _
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have habs : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ (1 / (2 * A + 2)) := by
      simpa only [Function.comp_def, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hN0 _), one_mul] using hN
    exact (le_abs_self _).trans habs
  have hsmall_quarter : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    have hpos : (0 : ℝ) < 1 / 4 := by norm_num
    have hsm := tendsto_natCast_atTop_atTop.eventually ((isLittleO_log_rpow_atTop hpos).bound zero_lt_one)
    filter_upwards [hsm, eventually_ge_atTop 1] with N hN _
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have habs : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      simpa only [Function.comp_def, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hN0 _), one_mul] using hN
    exact (le_abs_self _).trans habs
  filter_upwards [hup A hA k hk, hsmall_A, hsmall_quarter,
    eventually_ge_atTop 2, hloglim.eventually_ge_atTop 1]
    with N hupN hLA hL4 hN2 hlog
  intro m hm hmL c hc hlarge
  have hN1 : 1 ≤ N := by omega
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := zero_le_one.trans hm1R
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have h1m : 1 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_natCast_nonneg m]
  have h1m_sq : 1 ≤ (1 + Real.log (m : ℝ)) ^ 2 := one_le_pow₀ h1m
  have h1c : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc]
  have hs1 : 1 ≤ Real.log (N : ℝ) ^ (1 / (k : ℝ)) := Real.one_le_rpow hlog (by positivity)
  let M_log := (m : ℝ) * (1 + Real.log m) ^ 2
  have hMlog0 : 0 ≤ M_log := by dsimp only [M_log]; positivity
  have hm_le_Mlog : (m : ℝ) ≤ M_log := le_mul_of_one_le_right hm0 h1m_sq
  have hm2_N : m * m ≤ N := by
    have hm_sq : (m : ℝ) ^ 2 ≤ Real.log (N : ℝ) ^ (2 * A + 2) := by
      have hp := pow_le_pow_left₀ hm0 hmL 2
      have he : (Real.log (N : ℝ) ^ A) ^ (2 : ℕ) = Real.log (N : ℝ) ^ (2 * A) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
      exact (hp.trans_eq he).trans
        (Real.rpow_le_rpow_of_exponent_le hlog (by linarith only : 2 * A ≤ 2 * A + 2))
    have hL_N : Real.log (N : ℝ) ^ (2 * A + 2) ≤ (N : ℝ) := by
      have hp := Real.rpow_le_rpow hL0.le hLA (by positivity : 0 ≤ 2 * A + 2)
      have he : ((N : ℝ) ^ (1 / (2 * A + 2))) ^ (2 * A + 2) = (N : ℝ) := by
        rw [← Real.rpow_mul hN0.le, one_div_mul_cancel (by positivity), Real.rpow_one]
      exact hp.trans_eq he
    have hcast : ((m * m : ℕ) : ℝ) ≤ (N : ℝ) := by
      simpa only [sq, Nat.cast_mul] using hm_sq.trans hL_N
    exact_mod_cast hcast
  let R := c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
    c ^ 10 * (Real.log (N : ℝ) / N) ^ 2
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hc2_N : c ^ 2 ≤ (N : ℝ) := by
    have he := Real.exp_pos 1
    have hcoef : 1 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [he]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h, hlarge]
  have hthree : 3 * c ≤ (N : ℝ) := by
    have he := Real.exp_pos 1
    have hcoef : 3 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [he]
    have hc2 : c ≤ c ^ 2 := by nlinarith only [hc]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h, hc2, hlarge]
  have hcN : c ≤ (N : ℝ) := by linarith only [hthree, hc0]
  have htwo : 2 * c ≤ (N : ℝ) := by linarith only [hthree, hc0]
  have hw : c / N ≤ 1 / 3 := (div_le_iff₀ hN0).mpr (by linarith only [hthree])
  -- Monotonicity of `c^2 * (1 + log c)^a / log N ≤ R` for `0 ≤ a ≤ 3`.
  have hrate_c2 : ∀ {a : ℕ}, a ≤ 3 → c ^ 2 * (1 + Real.log c) ^ a / Real.log N ≤ R :=
    fun {a} ha => by
      have ha3 : (1 + Real.log c) ^ a ≤ (1 + Real.log c) ^ 3 := pow_le_pow_right₀ h1c ha
      have hnum : c ^ 2 * (1 + Real.log c) ^ a ≤
          c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) :=
        (mul_le_mul_of_nonneg_left ha3 (sq_nonneg c)).trans
          (le_mul_of_one_le_right (by positivity) hs1)
      exact (div_le_div_of_nonneg_right hnum hL0.le).trans (le_add_of_nonneg_right (by positivity))
  have hrate_base : 1 / Real.log N ≤ R := by
    have h1 : (1 : ℝ) ≤ c ^ 2 * (1 + Real.log c) ^ 0 := by rw [pow_zero, mul_one]; exact one_le_pow₀ hc
    exact (div_le_div_of_nonneg_right h1 hL0.le).trans (hrate_c2 (by norm_num))
  -- Exterior downward rate `c^3 * log N / N ≤ c^2 / log N ≤ R` via `c ≤ √N` and `(log N)^2 ≤ √N`.
  have hrate_ext : c ^ 3 * Real.log N / (N : ℝ) ≤ R := by
    have hc_sqrt : c ≤ Real.sqrt N := by
      have h := Real.sqrt_le_sqrt hc2_N
      rwa [Real.sqrt_sq hc0.le] at h
    have hL2_sqrt : Real.log (N : ℝ) ^ 2 ≤ Real.sqrt N := by
      have hp := pow_le_pow_left₀ hL0.le hL4 2
      have he : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = Real.sqrt N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Real.sqrt_eq_rpow]
        congr 1; norm_num
      exact hp.trans_eq he
    have hcL2 : c * Real.log (N : ℝ) ^ 2 ≤ (N : ℝ) :=
      (mul_le_mul hc_sqrt hL2_sqrt (sq_nonneg _) (Real.sqrt_nonneg _)).trans_eq
        (Real.mul_self_sqrt hN0.le)
    have hstep : c ^ 3 * Real.log N / (N : ℝ) ≤ c ^ 2 * (1 + Real.log c) ^ 0 / Real.log N := by
      rw [pow_zero, mul_one, div_le_div_iff₀ hN0 hL0]
      have hmul := mul_le_mul_of_nonneg_left hcL2 (sq_nonneg c)
      linarith only [hmul, (by ring : c ^ 2 * (c * Real.log (N : ℝ) ^ 2) =
        c ^ 3 * Real.log N * Real.log N)]
    exact hstep.trans (hrate_c2 (by norm_num))
  have hp' : ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cp * M_log * R := by
    have h1 : Cp * M_log / Real.log N = Cp * M_log * (1 / Real.log N) := by ring
    exact (hp m hm N).trans (h1.trans_le
      (mul_le_mul_of_nonneg_left hrate_base (by positivity)))
  have hs' : ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cs * M_log * R := by
    have hc210 := pow_le_pow_right₀ hc (by norm_num : 2 ≤ 10)
    have hL2 : 1 ≤ Real.log (N : ℝ) ^ 2 := one_le_pow₀ hlog
    have hscale := mul_le_mul_of_nonneg_left hL2 (pow_nonneg hc0.le 10)
    have hnum : Cs * (m : ℝ) * c ^ 2 ≤
        Cs * M_log * (c ^ 10 * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm_le_Mlog hCs.le)
        (hc210.trans (by simpa only [mul_one] using hscale)) (sq_nonneg _) (by positivity)
    calc
      _ ≤ Cs * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2 := hs m hm N hN1 hlog c hc0 hcN
      _ ≤ (Cs * M_log * (c ^ 10 * Real.log (N : ℝ) ^ 2)) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ = Cs * M_log * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by rw [div_pow]; ring
      _ ≤ Cs * M_log * R :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
  have hc' : ‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cc * M_log * R := by
    have hcen := fullWeilCenter_residual_linear_conductor_bound (completeWeilPoleShift φ c)
      hm hm2_N hlog
    have hshift : (completeWeilPoleShift φ c) ^ 2 = (completeWeilPoleShift φ 1) ^ 2 * c ^ 2 := by
      unfold completeWeilPoleShift; ring
    have heq : 742 * (completeWeilPoleShift φ c) ^ 2 * M_log / Real.log N =
        Cc * M_log * (c ^ 2 * (1 + Real.log c) ^ 0 / Real.log N) := by
      dsimp only [Cc]; rw [hshift, pow_zero]; ring
    exact hcen.trans (heq.trans_le
      (mul_le_mul_of_nonneg_left (hrate_c2 (by norm_num)) (by positivity)))
  have hx' : ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
      (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤ Cx * M_log * R := by
    have hb := hx m hm c hc N hN1 hc2_N
    calc
      _ ≤ Cx * (m : ℝ) * c ^ 2 / Real.log N := hb
      _ ≤ Cx * M_log * (c ^ 2 * (1 + Real.log c) ^ 0 / Real.log N) := by
        rw [pow_zero, mul_one, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_le_Mlog hCx) (by positivity)
      _ ≤ Cx * M_log * R := mul_le_mul_of_nonneg_left (hrate_c2 (by norm_num)) (by positivity)
  have hq' : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
      (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤ Cq * M_log * R := by
    have hb := hq m hm c hc N hN1 hlog hcN
    calc
      _ ≤ Cq * (m : ℝ) * c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 := hb
      _ ≤ Cq * M_log * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
        rw [mul_assoc (Cq * M_log)]
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_le_Mlog hCq) (by positivity))
          (sq_nonneg _)).trans_eq (by ring)
      _ ≤ Cq * M_log * R :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
  have hd' : ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m‖ ^ 2 ≤
      (2 * Cd) * M_log * R := by
    have hb := hdown m hm c hc N hN1 hlog hw
    have hr_sum : c ^ 2 * (1 + Real.log c) ^ 2 / Real.log N + c ^ 3 * Real.log N / (N : ℝ) ≤
        2 * R := by
      linarith only [hrate_c2 (by norm_num : 2 ≤ 3), hrate_ext]
    exact hb.trans ((mul_le_mul_of_nonneg_left hr_sum (by positivity)).trans_eq (by ring))
  have hn' : ‖nearCenterVector φ c N m‖ ^ 2 ≤ Cn * M_log * R := by
    have hb := hnear m hm c hc N hN1 htwo
    calc
      _ ≤ Cn * (m : ℝ) * c ^ 2 * (1 + Real.log c) ^ 3 / Real.log N := hb
      _ ≤ Cn * M_log * (c ^ 2 * (1 + Real.log c) ^ 3 / Real.log N) := by
        have h1 := mul_le_mul_of_nonneg_left hm_le_Mlog hCn
        have h2 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h1 (sq_nonneg c)) (by positivity : 0 ≤ (1 + Real.log c) ^ 3)
        exact (div_le_div_of_nonneg_right h2 hL0.le).trans_eq (by ring)
      _ ≤ Cn * M_log * R := mul_le_mul_of_nonneg_left (hrate_c2 (by norm_num)) (by positivity)
  have hu' : ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cu * M_log * R := by
    rw [upwardPrimeVector_ramanujan_residual_eq φ c N hm, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg m.totient)]
    have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
    have htot_le : (m.totient : ℝ) ≤ M_log :=
      (by exact_mod_cast Nat.totient_le m : (m.totient : ℝ) ≤ m).trans hm_le_Mlog
    have hup_R : c ^ 2 * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
        c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 ≤ R := by
      apply add_le_add_right
      apply div_le_div_of_nonneg_right _ hL0.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (by simpa only [pow_one] using pow_le_pow_right₀ h1c (by norm_num : 1 ≤ 3))
        (sq_nonneg c)
    calc
      (m.totient : ℝ)⁻¹ * ‖normalizedUpwardPrimeResidual φ c N m‖ ^ 2 ≤
          (m.totient : ℝ)⁻¹ * (Cu * (m.totient : ℝ) ^ 2 *
            (c ^ 2 * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 10 * (Real.log (N : ℝ) / N) ^ 2)) :=
        mul_le_mul_of_nonneg_left (hupN m hm hmL c hc hlarge) (by positivity)
      _ = Cu * (m.totient : ℝ) *
            (c ^ 2 * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
        field_simp [htot_pos.ne']
      _ ≤ Cu * M_log * R :=
        mul_le_mul (mul_le_mul_of_nonneg_left htot_le hCu.le) hup_R (by positivity)
          (by positivity)
  rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN1 hm]
  have hsum := norm_eight_signed_sq_le_quad
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)
    (completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m)
    (nearCenterVector φ c N m)
    (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N)
  have hb := hsum.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add hp' hs') hc') hx') hq') hd') hn') hu')
    (by norm_num : (0 : ℝ) ≤ 8))
  calc
    _ ≤ 8 * (Cp * M_log * R + Cs * M_log * R + Cc * M_log * R + Cx * M_log * R +
          Cq * M_log * R + (2 * Cd) * M_log * R + Cn * M_log * R + Cu * M_log * R) := hb
    _ = (8 * (Cp + Cs + Cc + Cx + Cq + 2 * Cd + Cn + Cu)) * M_log * R := by ring
    _ ≤ K * M_log * R :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith only) hMlog0) hR0

/-- Specialization of `exists_completeWeil_quadratic_conductor_residual_variable_rate` to
`tiltedUnitSpline`. -/
theorem exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          K * ((m : ℝ) * (1 + Real.log m) ^ 2) *
            (c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) :=
  exists_completeWeil_quadratic_conductor_residual_variable_rate contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos

/-- **Summed quadratic-overlap relative residual bound.**
Weighting each conductor residual by its individual seventh-power completed energy floor yields
total relative residual mass `O((c^14 + Q^2) * (1 + log Q)^2 * rate)`, lowering the low-conductor
overlap exponent from `14 + 5 = 19` to `14 + 2 = 16`. -/
theorem exists_tiltedUnitSpline_quadratic_relative_residual_sum_le :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.log (N : ℝ) ^ A →
        (∑ m ∈ Icc 1 Q,
          ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 /
              completedConductorEnergy tiltedUnitSpline c m ^ 2) ≤
          K * (c ^ 14 + (Q : ℝ) ^ 2) * (1 + Real.log Q) ^ 2 *
            (c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
  obtain ⟨K₀, hK₀, hres⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  let κ : ℝ := 2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)
  have hκ : 0 < κ := div_pos (mul_pos zero_lt_two tiltedSplineTailConstant_pos)
    integral_tiltedUnitSpline_sq_pos
  refine ⟨2 * K₀ / κ ^ 2, by positivity, ?_⟩
  intro A hA k hk
  filter_upwards [hres A hA k hk, eventually_ge_atTop 2] with N hN _
  intro c hc hwidth Q hQ
  let r := c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
    c ^ 10 * (Real.log (N : ℝ) / N) ^ 2
  have hr : 0 ≤ r := by
    have hc0 : 0 ≤ c := zero_le_one.trans hc
    have hlog := Real.log_natCast_nonneg N
    have h1c : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc]
    dsimp only [r]
    positivity
  have hsum := sum_linear_conductor_relative_weights_le hc Q
  calc
    _ ≤ ∑ m ∈ Icc 1 Q,
        (K₀ * (m : ℝ) * (1 + Real.log Q) ^ 2 * r) /
          completedConductorEnergy tiltedUnitSpline c m ^ 2 := by
      refine sum_le_sum fun m hm => ?_
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
      have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
      have hlogm : Real.log m ≤ Real.log Q := Real.log_le_log hm0 hmQ
      have hp : (1 + Real.log m) ^ 2 ≤ (1 + Real.log Q) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [hlogm]) 2
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (mul_nonneg hK₀.le hm0.le)) hr
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact (hN m (mem_Icc.mp hm).1 (hmQ.trans hQ) c hc hwidth).trans
        (by simpa only [mul_assoc] using hh)
    _ = (K₀ * (1 + Real.log Q) ^ 2 * r) * ∑ m ∈ Icc 1 Q,
        (m : ℝ) / completedConductorEnergy tiltedUnitSpline c m ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (K₀ * (1 + Real.log Q) ^ 2 * r) * ((2 * c ^ 14 + (Q : ℝ) ^ 2) / κ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (2 * K₀ / κ ^ 2) * (c ^ 14 + (Q : ℝ) ^ 2) * (1 + Real.log Q) ^ 2 * r := by
      have hbase : 2 * c ^ 14 + (Q : ℝ) ^ 2 ≤ 2 * (c ^ 14 + (Q : ℝ) ^ 2) := by
        nlinarith only [sq_nonneg (Q : ℝ)]
      have hh := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hbase (sq_nonneg κ))
        (show 0 ≤ K₀ * (1 + Real.log Q) ^ 2 * r by positivity)
      exact hh.trans_eq (by ring)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_quadratic_conductor_residual_variable_rate
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_quadratic_relative_residual_sum_le
