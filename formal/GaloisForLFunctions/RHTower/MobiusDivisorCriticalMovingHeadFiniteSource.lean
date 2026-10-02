import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMovingHeadMellin

/-!
# Exact late-prime source on each integer cell

The all-prime and old-prime sums cancel before taking absolute values.
Prime-square cutoffs and quotient floors are constant on each half-open
integer cell. This supplies an exact source identity across that cell,
without asserting continuity across a prime-square jump.
-/

noncomputable section
open Finset
namespace RHTower

/-- The unprocessed prime indices on the integer cell starting at N. -/
def criticalMovingLatePrimes (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun p => p.Prime ∧ N < p * p)

private theorem primeHead_re_eq_cutoff (x : ℝ) :
    (criticalPrimeAbelHead x).re =
      ∑ p ∈ retainedPrimeCutoff x, Real.sqrt p * criticalContinuousAbel (x / p) := by
  have hN : x ≤ ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_floor_add_one x).le
  rw [criticalPrimeAbelHead_eq_finite x (⌊x⌋₊ + 1) hN, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [Finset.sum_subtype_eq_sum_filter
    (fun p : ℕ => Real.sqrt p * criticalContinuousAbel (x / p))]
  have hs : (range (⌊x⌋₊ + 1)).filter Nat.Prime = retainedPrimeCutoff x := by
    ext p
    simp only [retainedPrimeCutoff, mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨hpN, hp⟩
      exact ⟨⟨by have := hp.pos; omega, by omega⟩, hp⟩
    · rintro ⟨⟨_, hpN⟩, hp⟩
      exact ⟨by omega, hp⟩
  rw [hs]

/-- Exact cancellation of all retained old-prime atoms, leaving the literal
late-prime source. -/
theorem criticalMovingPrimeHead_eq_late_sum {x : ℝ} (hx : 1 < x) :
    criticalMovingPrimeHead x = criticalContinuousAbel x +
      ∑ p ∈ (retainedPrimeCutoff x).filter (fun p : ℕ => x < (p : ℝ) ^ (2 : ℕ)),
        Real.sqrt p * criticalContinuousAbel (x / p) := by
  rw [criticalMovingPrimeHead, primeHead_re_eq_cutoff x, criticalRetainedPrimeHead_eq_finite hx]
  calc
    _ = criticalContinuousAbel x + ∑ p ∈ retainedPrimeCutoff x,
        (Real.sqrt p * criticalContinuousAbel (x / p) - criticalRetainedPrimeHeadAtom p x) := by
      rw [sum_sub_distrib]
      ring
    _ = _ := by
      congr 1
      rw [sum_filter]
      apply sum_congr rfl
      intro p hp
      have hpp := (mem_filter.mp hp).2
      by_cases hs : (p : ℝ) ^ (2 : ℕ) ≤ x
      · simp [criticalRetainedPrimeHeadAtom, hpp, hs, not_lt.mpr hs]
      · simp [criticalRetainedPrimeHeadAtom, hpp, hs, lt_of_not_ge hs]

/-- The late-prime index set is fixed on the entire half-open integer cell. -/
theorem criticalMovingPrimeHead_eq_cell_source {N : ℕ} (hN : 2 ≤ N) {x : ℝ}
    (hNx : (N : ℝ) ≤ x) (hxN : x < (N + 1 : ℕ)) :
    criticalMovingPrimeHead x = criticalContinuousAbel x +
      ∑ p ∈ criticalMovingLatePrimes N, Real.sqrt p * criticalContinuousAbel (x / p) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 < x := by linarith
  have hfloor : ⌊x⌋₊ = N := (Nat.floor_eq_iff (le_of_lt (lt_trans zero_lt_one hx1))).mpr
    ⟨hNx, by exact_mod_cast hxN⟩
  rw [criticalMovingPrimeHead_eq_late_sum hx1]
  congr 1
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  have hs : x < (p : ℝ) ^ (2 : ℕ) ↔ N < p * p := by
    constructor
    · intro hp
      have h : (N : ℝ) < (p : ℝ) ^ (2 : ℕ) := hNx.trans_lt hp
      rw [pow_two] at h
      exact_mod_cast h
    · intro hp
      have h : ((N + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (2 : ℕ) := by
        rw [pow_two]
        exact_mod_cast Nat.succ_le_of_lt hp
      exact hxN.trans_le h
  simp only [retainedPrimeCutoff, hfloor, criticalMovingLatePrimes,
    mem_filter, hs, and_assoc]

/-- Exact real square-root interpolation of the literal Abel source. -/
theorem criticalContinuousAbel_between {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hkx : (k : ℝ) ≤ x) (hxk : x ≤ (k + 1 : ℕ)) :
    criticalContinuousAbel x = criticalContinuousAbel k +
      (Real.sqrt x - Real.sqrt k) * psiDefect k := by
  have h := congrArg Complex.re
    (squareRootSummatoryPrimitive_between criticalSourceCoeff hk hkx hxk)
  rw [criticalSourceCoeff_cumulative _ hk] at h
  simpa only [criticalContinuousAbel, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] using h

private theorem criticalPrime_child_cell {N p : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    {x : ℝ} (hNx : (N : ℝ) ≤ x) (hxN : x < (N + 1 : ℕ)) :
    Real.sqrt p * criticalContinuousAbel (x / p) =
      Real.sqrt p * criticalContinuousAbel ((N : ℝ) / p) +
        (Real.sqrt x - Real.sqrt N) * psiDefect (N / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hk : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hpN)
  have hlow : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
    apply (le_div_iff₀ hp0).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  have hlowx : ((N / p : ℕ) : ℝ) ≤ x / p := hlow.trans (by gcongr)
  have hu : ((N + 1 : ℕ) : ℝ) ≤ ((N / p + 1 : ℕ) : ℝ) * p := by
    exact_mod_cast (by simpa [Nat.mul_comm] using
      Nat.succ_le_of_lt (Nat.lt_mul_div_succ N hp) : N + 1 ≤ (N / p + 1) * p)
  have hupperx : x / (p : ℝ) ≤ (N / p + 1 : ℕ) :=
    (div_le_iff₀ hp0).mpr (hxN.le.trans hu)
  have hupper : (N : ℝ) / p ≤ (N / p + 1 : ℕ) :=
    (div_le_iff₀ hp0).mpr (hNx.trans (hxN.le.trans hu))
  have hAx := criticalContinuousAbel_between hk hlowx hupperx
  have hAN := criticalContinuousAbel_between hk hlow hupper
  have hsx : Real.sqrt p * Real.sqrt (x / p) = Real.sqrt x := by
    rw [← Real.sqrt_mul hp0.le]
    congr 1
    field_simp [hp0.ne']
  have hsN : Real.sqrt p * Real.sqrt ((N : ℝ) / p) = Real.sqrt N := by
    rw [← Real.sqrt_mul hp0.le]
    congr 1
    field_simp [hp0.ne']
  calc
    _ = Real.sqrt p * criticalContinuousAbel ((N : ℝ) / p) +
        (Real.sqrt p * Real.sqrt (x / p) - Real.sqrt p * Real.sqrt ((N : ℝ) / p)) *
          psiDefect (N / p) := by rw [hAx, hAN]; ring
    _ = _ := by rw [hsx, hsN]

/-- Full source identity within a half-open integer cell. The prime-square
jumps at the next endpoint are not suppressed. -/
theorem criticalMovingPrimeHead_cell {N : ℕ} (hN : 2 ≤ N) {x : ℝ}
    (hNx : (N : ℝ) ≤ x) (hxN : x < (N + 1 : ℕ)) :
    criticalMovingPrimeHead x = criticalMovingPrimeHead N +
      (Real.sqrt x - Real.sqrt N) *
        (psiDefect N + ∑ p ∈ criticalMovingLatePrimes N, psiDefect (N / p)) := by
  have hs (p : ℕ) (hp : p ∈ criticalMovingLatePrimes N) :
      Real.sqrt p * criticalContinuousAbel (x / p) =
        Real.sqrt p * criticalContinuousAbel ((N : ℝ) / p) +
          (Real.sqrt x - Real.sqrt N) * psiDefect (N / p) := by
    obtain ⟨hpI, hpP, _⟩ := mem_filter.mp hp
    exact criticalPrime_child_cell hpP.pos (mem_Icc.mp hpI).2 hNx hxN
  rw [criticalMovingPrimeHead_eq_cell_source hN hNx hxN,
    criticalMovingPrimeHead_eq_cell_source hN le_rfl (by exact_mod_cast Nat.lt_succ_self N),
    criticalContinuousAbel_between (by omega : 1 ≤ N) hNx hxN.le,
    sum_congr rfl hs, sum_add_distrib, ← mul_sum]
  ring

end RHTower
