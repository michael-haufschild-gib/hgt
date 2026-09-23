import GaloisForLFunctions.RHTower.Sieve.LevelSetSpacedSample
import GaloisForLFunctions.RHTower.Sieve.LogPolyBlockBridge
import GaloisForLFunctions.RHTower.Sieve.HuxleyDensityBound
import GaloisForLFunctions.RHTower.Sieve.LadderProductDefect

/-!
# Counting one-spaced frequencies in a prime-block level set

`exists_spaced_families_blockProduct_gramRows` reduces the Möbius bilinear block to Gram rows over
one-spaced families of frequencies inside the level sets of the prime block polynomial.  Every
Halász–Montgomery bound charges one term per frequency, so the last quantitative input is the
**cardinality** of such a family, and that is Huxley's large-values theorem applied to the prime
block polynomial itself.

The prime block polynomial is a Dirichlet polynomial in the corpus's `blockPoly` normalisation:
`primeBlockPoly B w = ∑_{p ∈ B} μ(p) e(w log p)` is `logPoly` with Möbius coefficients, and for a
block supported in a dyadic range `[N, 2N)` the bridge `logPoly_eq_blockPoly_of_subset` turns it
into a Gram row against `dyadicDirRow N (−2πw)`.  Rescaling the frequency by `−2π` preserves
one-spacing (it dilates by `2π > 1`) and multiplies the spread by `2π`.

* `primeBlockPoly_eq_logPoly_primeBlockLevelSetCount`, `primeBlockPoly_eq_inner` (reusing the corpus's `moebiusCoeff`);
* `normSq_moebiusBlockCoeff_le`;
* `card_le_of_mem_primeBlockLevelSet` — the large-values count.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace ArithmeticFunction.Moebius

noncomputable section

/-- **The prime block polynomial is a Möbius `logPoly`.** -/
theorem primeBlockPoly_eq_logPoly_primeBlockLevelSetCount (B : Finset ℕ) (w : ℝ) :
    primeBlockPoly B w = logPoly moebiusCoeff B w := by
  simp only [primeBlockPoly, logPoly, moebiusPhase, unitLogPhase, moebiusCoeff]

/-- **The prime block polynomial as a Gram row**, for a block supported in a dyadic range. -/
theorem primeBlockPoly_eq_inner {N : ℕ} {B : Finset ℕ} (hB : B ⊆ Finset.Ico N (2 * N)) (w : ℝ) :
    primeBlockPoly B w
      = ⟪dyadicDirRow N (-(2 * Real.pi * w)),
          blockCoeff N (blockRestrictCoeff moebiusCoeff B) 0⟫_ℂ := by
  rw [inner_dyadicDirRow_blockCoeff, primeBlockPoly_eq_logPoly_primeBlockLevelSetCount,
    logPoly_eq_blockPoly_of_subset hB]

/-- The Hilbert energy of the Möbius block coefficient vector is at most the block size. -/
theorem normSq_moebiusBlockCoeff_le {N : ℕ} {B : Finset ℕ} (hB : B ⊆ Finset.Ico N (2 * N)) :
    ‖blockCoeff N (blockRestrictCoeff moebiusCoeff B) 0‖ ^ 2 ≤ (B.card : ℝ) := by
  classical
  rw [norm_blockCoeff_sq]
  have hterm : ∀ n ∈ Finset.Ico N (2 * N),
      ‖blockRestrictCoeff moebiusCoeff B n‖ ^ 2 * (((n : ℝ) ^ (-(0 : ℝ))) ^ 2)
        = if n ∈ B then ‖moebiusCoeff n‖ ^ 2 else 0 := by
    intro n _
    by_cases hn : n ∈ B
    · simp only [blockRestrictCoeff, if_pos hn, neg_zero, Real.rpow_zero, one_pow, mul_one]
    · simp only [blockRestrictCoeff, if_neg hn, norm_zero]
      simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hB]
  calc ∑ n ∈ B, ‖moebiusCoeff n‖ ^ 2 ≤ ∑ _n ∈ B, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have h := norm_moebiusCoeff_le_one n
        nlinarith [norm_nonneg (moebiusCoeff n)]
    _ = (B.card : ℝ) := by simp

/-- **Huxley's large-values count on a prime-block level set.**  A one-spaced family of frequencies
inside the level set `{ |w| ≤ G : N^{-σ} ≤ ‖primeBlockPoly B w‖ }` has cardinality bounded by
Huxley's two-term density estimate.  This is the last quantitative input of the large-values route:
it converts the level-set discretisation into a genuine saving. -/
theorem card_le_of_mem_primeBlockLevelSet {N : ℕ} (hN : 1 ≤ N) {B : Finset ℕ}
    (hB : B ⊆ Finset.Ico N (2 * N)) {G E sigma : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E)
    (hmass : (B.card : ℝ) ≤ E / (N : ℝ))
    (hthr : 2400 * E ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma))
    (P : Finset ℝ)
    (hPsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (1 : ℝ) ≤ |x - y|)
    (hPmem : ∀ x ∈ P, x ∈ primeBlockLevelSet B G ((N : ℝ) ^ (-sigma))) :
    (P.card : ℝ)
      ≤ (6594624 * (2 * Real.pi * G) * E ^ 3 * (N : ℝ) ^ (6 * sigma - 2)
            + 2 * E * (N : ℝ) ^ (2 * sigma))
          * (1 + 12 * Real.pi * (1 + Real.log (2 * (2 * Real.pi * G) + 1))) := by
  classical
  set a : EuclideanSpace ℂ (Fin N) := blockCoeff N (blockRestrictCoeff moebiusCoeff B) 0 with ha
  set S : Finset ℝ := P.image (fun x => -(2 * Real.pi * x)) with hS
  have hpi : (1 : ℝ) < 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hinj : Set.InjOn (fun x : ℝ => -(2 * Real.pi * x)) P := by
    intro x _ y _ hxy
    simp only [neg_inj] at hxy
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    exact mul_left_cancel₀ h2 hxy
  have hcard : (S.card : ℝ) = (P.card : ℝ) := by
    rw [hS, Finset.card_image_of_injOn hinj]
  have hmem : ∀ y ∈ S, ∃ x ∈ P, y = -(2 * Real.pi * x) := by
    intro y hy
    rw [hS, Finset.mem_image] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨x, hx, hxy.symm⟩
  have hSsep : ∀ y ∈ S, ∀ z ∈ S, y ≠ z → (1 : ℝ) ≤ |y - z| := by
    intro y hy z hz hyz
    obtain ⟨x, hx, rfl⟩ := hmem y hy
    obtain ⟨u, hu, rfl⟩ := hmem z hz
    have hxu : x ≠ u := by
      intro h
      exact hyz (by rw [h])
    have hsep := hPsep x hx u hu hxu
    have hid : -(2 * Real.pi * x) - -(2 * Real.pi * u) = (2 * Real.pi) * (u - x) := by ring
    rw [hid, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi), abs_sub_comm]
    nlinarith [hsep, hpi]
  have hSspread : ∀ y ∈ S, ∀ z ∈ S, |y - z| ≤ 2 * (2 * Real.pi * G) := by
    intro y hy z hz
    obtain ⟨x, hx, rfl⟩ := hmem y hy
    obtain ⟨u, hu, rfl⟩ := hmem z hz
    have hx' := (hPmem x hx).1
    have hu' := (hPmem u hu).1
    rw [Set.mem_Icc] at hx' hu'
    have hid : -(2 * Real.pi * x) - -(2 * Real.pi * u) = (2 * Real.pi) * (u - x) := by ring
    rw [hid, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi), abs_sub_comm]
    have habs : |x - u| ≤ 2 * G := by
      rw [abs_le]
      constructor <;> linarith [hx'.1, hx'.2, hu'.1, hu'.2]
    nlinarith [habs, Real.pi_pos]
  have hSbig : ∀ y ∈ S, (N : ℝ) ^ (-sigma) ≤ ‖⟪dyadicDirRow N y, a⟫_ℂ‖ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hmem y hy
    have hlevel := (hPmem x hx).2
    rw [ha, ← primeBlockPoly_eq_inner hB]
    exact hlevel
  have hmass' : ‖a‖ ^ 2 ≤ E / (N : ℝ) :=
    le_trans (normSq_moebiusBlockCoeff_le hB) hmass
  have hTG : (0 : ℝ) ≤ 2 * Real.pi * G := by positivity
  have hbase := huxley_energy_two_term hN a hTG hE hmass' hthr S hSsep hSspread hSbig
  rwa [hcard] at hbase

end

end RHTower.Sieve
