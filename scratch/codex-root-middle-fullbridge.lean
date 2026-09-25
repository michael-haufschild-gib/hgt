import GaloisForLFunctions.RHTower.MobiusDivisorMiddleReserveEscape

noncomputable section
open Finset Filter Topology
namespace RHTower

private theorem eventually_child_total_arbitrarily_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ, 7 * N ≤ K → K ≤ 8 * N →
      |∑ d ∈ Icc 1 K, mobiusDivisorDilationChannel K d| ≤
        ε * ((N : ℝ) * Real.sqrt N) / Real.log (4 * (N : ℝ)) := by
  have hδ : (0 : ℝ) < ε / 24 := by positivity
  have hs := tendsto_sum_mobiusDivisorDilationChannel_log_normalized.abs.eventually
    (gt_mem_nhds (by simpa using hδ : |(0 : ℝ)| < ε / 24))
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hs
  filter_upwards [eventually_ge_atTop (max K₀ 1)] with N hN
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  intro K hlo hhi
  have hK0 : K₀ ≤ K := by have := (le_max_left K₀ 1).trans hN; omega
  have hs := hK₀ K hK0
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hlogK : 0 < Real.log K := Real.log_pos (by exact_mod_cast (show 1 < K by omega))
  have hlogN : 0 < Real.log (4 * (N : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 4 * N by omega))
  rw [abs_div, abs_mul, abs_of_pos hlogK,
    abs_of_pos (mul_pos hKr (Real.sqrt_pos.mpr hKr))] at hs
  have hsraw := (div_lt_iff₀ (mul_pos hKr (Real.sqrt_pos.mpr hKr))).mp hs
  have hlog : Real.log (4 * (N : ℝ)) ≤ Real.log K := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show 4 * N ≤ K by omega)
  have hslog := mul_le_mul_of_nonneg_left hlog
    (abs_nonneg (∑ d ∈ Icc 1 K, mobiusDivisorDilationChannel K d))
  have hK8 : (K : ℝ) ≤ 8 * N := by exact_mod_cast hhi
  have hroot : Real.sqrt K ≤ 3 * Real.sqrt N := by
    have hsqK := Real.sq_sqrt hKr.le
    have hsqN := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    nlinarith [Real.sqrt_nonneg (K : ℝ), Real.sqrt_nonneg (N : ℝ)]
  have hnum := mul_le_mul hK8 hroot (Real.sqrt_nonneg (K : ℝ))
    (show (0 : ℝ) ≤ 8 * N by positivity)
  have hεnum := mul_le_mul_of_nonneg_left hnum (div_nonneg hε.le (by norm_num : (0 : ℝ) ≤ 24))
  apply (le_div_iff₀ hlogN).mpr
  nlinarith only [hsraw, hslog, hεnum]

private theorem middle_quotient_range_bridge {N p : ℕ} (hN : 1 ≤ N)
    (hp : p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (8 * N) (9 * N)) :
    7 * N ≤ (64 * N ^ (2 : ℕ)) / p ∧
      (64 * N ^ (2 : ℕ)) / p + 1 ≤ 8 * N := by
  obtain ⟨hprime, hlo, hhi⟩ :=
    GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  constructor
  · exact (Nat.le_div_iff_mul_le hprime.pos).mpr (by nlinarith)
  · have h := (Nat.div_lt_iff_lt_mul hprime.pos).mpr
      (show 64 * N ^ (2 : ℕ) < 8 * N * p by nlinarith)
    omega

private theorem source_primes_mono_bridge {a b : ℕ} (hab : a ≤ b) :
    mobiusDivisorSelectionPrimes a ⊆ mobiusDivisorSelectionPrimes b := by
  intro q hq
  obtain ⟨hq, hprime⟩ := mem_filter.mp hq
  exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hq).trans_le hab), hprime⟩

theorem eventually_middle_fibre_after_full_bridge_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ,
      p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (8 * N) (9 * N) →
      |mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
        (mobiusDivisorSelectionPrimes (8 * N)) {p}| ≤
          ε * (N : ℝ) ^ (2 : ℕ) / Real.log (4 * (N : ℝ)) := by
  have hδ : 0 < ε / 3 := by positivity
  filter_upwards [eventually_child_total_arbitrarily_small (ε / 3) hδ,
    eventually_ge_atTop (2 : ℕ)] with N hsmall hN
  intro p hp
  obtain ⟨hprime, hlo, hhi⟩ :=
    GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  have ⟨hKlo, hKhi⟩ := middle_quotient_range_bridge (by omega : 1 ≤ N) hp
  let M := 64 * N ^ (2 : ℕ)
  let P := mobiusDivisorSelectionPrimes (8 * N)
  have hpP : p ∉ P := by
    intro h
    have := mem_range.mp (mem_filter.mp h).1
    omega
  have hcover0 : mobiusDivisorSelectionPrimes (M / p) ⊆ P :=
    source_primes_mono_bridge (by dsimp [M]; omega)
  have hcover1 : mobiusDivisorSelectionPrimes (M / p + 1) ⊆ P :=
    source_primes_mono_bridge (by dsimp [M]; omega)
  have hS0 := hsmall (M / p) (by simpa [M] using hKlo)
    (by
      have hh : M / p + 1 ≤ 8 * N := by simpa [M] using hKhi
      omega)
  have hS1 := hsmall (M / p + 1)
    (by
      have hh : 7 * N ≤ M / p := by simpa [M] using hKlo
      omega)
    (by simpa [M] using hKhi)
  have hF0 := mobiusDivisorSelectionFibre_of_all_source_primes_processed
    (M / p) P ∅ hcover0
  have hF1 := mobiusDivisorSelectionFibre_of_all_source_primes_processed
    (M / p + 1) P ∅ hcover1
  simp only [if_true] at hF0 hF1
  have hbound0 : |mobiusDivisorSelectionFibre (M / p) P ∅| ≤
      (ε / 3) * ((N : ℝ) * Real.sqrt N) / Real.log (4 * (N : ℝ)) := by
    simpa only [hF0] using hS0
  have hbound1 : |mobiusDivisorSelectionFibre (M / p + 1) P ∅| ≤
      (ε / 3) * ((N : ℝ) * Real.sqrt N) / Real.log (4 * (N : ℝ)) := by
    simpa only [hF1] using hS1
  have hw0 := divisorPrimeClipWeight_nonneg M p hprime.pos
  have hw1 : 0 ≤ 1 - divisorPrimeClipWeight M p := by
    have := divisorPrimeClipWeight_lt_one M p hprime.pos
    linarith
  have hinterp : |mobiusDivisorInterpolatedFibre M p P ∅| ≤
      (ε / 3) * ((N : ℝ) * Real.sqrt N) / Real.log (4 * (N : ℝ)) := by
    unfold mobiusDivisorInterpolatedFibre
    calc
      _ ≤ |(1 - divisorPrimeClipWeight M p) *
          mobiusDivisorSelectionFibre (M / p) P ∅| +
          |divisorPrimeClipWeight M p *
          mobiusDivisorSelectionFibre (M / p + 1) P ∅| := abs_add_le _ _
      _ = (1 - divisorPrimeClipWeight M p) *
          |mobiusDivisorSelectionFibre (M / p) P ∅| +
          divisorPrimeClipWeight M p *
          |mobiusDivisorSelectionFibre (M / p + 1) P ∅| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hw1]
      _ ≤ (1 - divisorPrimeClipWeight M p) *
          ((ε / 3) * ((N : ℝ) * Real.sqrt N) / Real.log (4 * (N : ℝ))) +
          divisorPrimeClipWeight M p *
          ((ε / 3) * ((N : ℝ) * Real.sqrt N) / Real.log (4 * (N : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_left hbound0 hw1)
          (mul_le_mul_of_nonneg_left hbound1 hw0)
      _ = _ := by ring
  have hrootp : Real.sqrt p ≤ 3 * Real.sqrt N := by
    have hpr : (p : ℝ) ≤ 9 * N := by exact_mod_cast hhi
    have hsqP := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
    have hsqN := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    nlinarith [Real.sqrt_nonneg (p : ℝ), Real.sqrt_nonneg (N : ℝ)]
  have hlog : 0 < Real.log (4 * (N : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 4 * N by omega))
  have hcoef : 0 ≤ (ε / 3) * ((N : ℝ) * Real.sqrt N) /
      Real.log (4 * (N : ℝ)) := by positivity
  have hprod := mul_le_mul hrootp hinterp (abs_nonneg _)
    (by positivity : 0 ≤ 3 * Real.sqrt (N : ℝ))
  have hF := mobiusDivisorSelectionFibre_prime_interpolation hprime M P ∅ hpP (by simp)
  simp only [insert_empty_eq] at hF
  rw [hF, abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt p * |mobiusDivisorInterpolatedFibre M p P ∅| ≤
        (3 * Real.sqrt N) *
          ((ε / 3) * ((N : ℝ) * Real.sqrt N) / Real.log (4 * (N : ℝ))) := hprod
    _ = ε * (N : ℝ) ^ (2 : ℕ) / Real.log (4 * (N : ℝ)) := by
      calc
        _ = ε * (N : ℝ) * (Real.sqrt N * Real.sqrt N) /
            Real.log (4 * (N : ℝ)) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg N)]; ring

theorem eventually_middle_fibre_full_bridge_contracts
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ,
      p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (8 * N) (9 * N) →
      |mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
        (mobiusDivisorSelectionPrimes (8 * N)) {p}| ≤
        tolerance * |mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
          (mobiusDivisorSelectionPrimes (4 * N)) {p}| := by
  have hδ : 0 < tolerance / 160 := by positivity
  filter_upwards [eventually_middle_fibre_after_full_bridge_small (tolerance / 160) hδ,
    eventually_mobiusDivisorMiddlePrimeFibre_upper,
    eventually_ge_atTop (2 : ℕ)] with N hfinal hinitial hN
  intro p hp
  have hf := hfinal p hp
  have hi := hinitial p hp
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog4 : 0 < Real.log (4 * (N : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 4 * N by omega))
  have hlog8 : 0 < Real.log (8 * (N : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 8 * N by omega))
  have hlogcomp : Real.log (8 * (N : ℝ)) ≤
      2 * Real.log (4 * (N : ℝ)) := by
    have hbase : 8 * (N : ℝ) ≤ (4 * (N : ℝ)) ^ (2 : ℕ) := by
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith [sq_nonneg ((N : ℝ) - 1)]
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 8 * N) hbase
    rw [Real.log_pow] at h
    simpa only [Nat.cast_ofNat] using h
  let a := (N : ℝ) ^ (2 : ℕ) / (80 * Real.log (8 * (N : ℝ)))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have habs : a ≤ |mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
      (mobiusDivisorSelectionPrimes (4 * N)) {p}| := by
    have hh := neg_le_abs
      (mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
        (mobiusDivisorSelectionPrimes (4 * N)) {p})
    have hi' : mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
        (mobiusDivisorSelectionPrimes (4 * N)) {p} ≤ -a := by
      simpa only [a, neg_div] using hi
    simpa only [neg_neg] using (neg_le_neg hi').trans hh
  have hscale : (tolerance / 160) * (N : ℝ) ^ (2 : ℕ) /
      Real.log (4 * (N : ℝ)) ≤ tolerance * a := by
    dsimp [a]
    calc
      _ = (tolerance * (N : ℝ) ^ (2 : ℕ)) /
            (160 * Real.log (4 * (N : ℝ))) := by ring
      _ ≤ (tolerance * (N : ℝ) ^ (2 : ℕ)) /
            (80 * Real.log (8 * (N : ℝ))) := by
        apply (div_le_div_iff₀ (mul_pos (by norm_num) hlog4)
          (mul_pos (by norm_num) hlog8)).mpr
        have hden : 80 * Real.log (8 * (N : ℝ)) ≤
            160 * Real.log (4 * (N : ℝ)) := by linarith only [hlogcomp]
        exact mul_le_mul_of_nonneg_left hden (by positivity)
      _ = _ := by ring
  exact hf.trans (hscale.trans (mul_le_mul_of_nonneg_left habs htolerance.le))

theorem eventually_middle_sector_full_bridge_contracts
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (8 * N) (9 * N),
        (mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
          (mobiusDivisorSelectionPrimes (8 * N)) {p}) ^ (2 : ℕ)) ≤
        tolerance ^ (2 : ℕ) *
          (∑ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (8 * N) (9 * N),
            (mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
              (mobiusDivisorSelectionPrimes (4 * N)) {p}) ^ (2 : ℕ)) := by
  filter_upwards [eventually_middle_fibre_full_bridge_contracts tolerance htolerance] with N hN
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hh := hN p hp
  have hprod := mul_le_mul hh hh (abs_nonneg _)
    (mul_nonneg htolerance.le (abs_nonneg _))
  simpa only [← pow_two, sq_abs, mul_pow] using hprod

end RHTower
