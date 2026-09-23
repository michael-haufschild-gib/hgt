import GaloisForLFunctions.RHTower.LeakageFloorFromTrace
import GaloisForLFunctions.RHTower.SecularTailSaturation

/-!
# The leakage floor survives a trace-class perturbation

The source lock compares the arithmetic restricted-Weil compression with the free time–band
operator.  The tree already proves that the difference is trace class
(`IsSoninTimeBandTraceIdeal.isTraceClass`, `centralSoninWeightedPrimePowerResidual` Hilbert–Schmidt),
and a trace-class operator has summable eigenvalues.  What the transfer needs from the arithmetic
side is only the *floor* on the leakage, and a floor survives any summable perturbation: the
perturbation tends to zero, so past some index it cannot consume more than half the floor.

This is the spectral content of the source lock, and it is elementary once the trace-class fact is
in hand.
-/

namespace RHTower

/-- **A cofinal floor survives a summable perturbation.**  If `d` is bounded below by `dinf > 0`
past some index and `e` is summable, then `d + e` is bounded below by `dinf/2` past some index. -/
theorem exists_floor_of_summable_perturbation {d e : ℕ → ℝ} {dinf : ℝ} {N : ℕ}
    (hd : ∀ n, N ≤ n → dinf ≤ d n) (he : Summable e) (hpos : 0 < dinf) :
    ∃ M : ℕ, ∀ n, M ≤ n → dinf / 2 ≤ d n + e n := by
  have hzero : Filter.Tendsto e Filter.atTop (nhds 0) := he.tendsto_atTop_zero
  have hev : ∀ᶠ n in Filter.atTop, |e n| < dinf / 2 := by
    have := Metric.tendsto_atTop.mp hzero (dinf / 2) (by linarith)
    obtain ⟨K, hK⟩ := this
    filter_upwards [Filter.eventually_ge_atTop K] with n hn
    simpa [Real.dist_eq] using hK n hn
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N K, fun n hn => ?_⟩
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have hKn : K ≤ n := le_trans (le_max_right _ _) hn
  have h1 : dinf ≤ d n := hd n hN
  have h2 : |e n| < dinf / 2 := hK n hKn
  have h3 : -(dinf / 2) < e n := by
    have := neg_lt_of_abs_lt h2
    linarith
  linarith

/-- **The leakage floor under a summable perturbation.**  Combining with `exists_leakage_floor`: the
free leakage `1 − λ_n` has a cofinal floor `1/2` from the trace alone, so the perturbed leakage has
a cofinal floor `1/4`.  This is the form the secular tail estimate consumes. -/
theorem exists_perturbed_leakage_floor {lam e : ℕ → ℝ} (hnn : ∀ n, 0 ≤ lam n)
    (hanti : Antitone lam) {T : ℝ} (hT : 0 ≤ T)
    (hsum : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), lam k ≤ T)
    (he : Summable e) :
    ∃ M : ℕ, ∀ n, M ≤ n → (1 : ℝ) / 4 ≤ (1 - lam n) + e n := by
  obtain ⟨N, hN⟩ := exists_leakage_floor hnn hanti hT hsum
  obtain ⟨M, hM⟩ := exists_floor_of_summable_perturbation
    (d := fun n => 1 - lam n) (e := e) (dinf := 1 / 2) (N := N)
    (fun n hn => hN n hn) he (by norm_num)
  refine ⟨M, fun n hn => ?_⟩
  have h := hM n hn
  linarith

/-- **The source-lock composition, at the spectral level.**  The free leakage floor of
`LeakageFloorFromTrace` plus summability of the arithmetic perturbation gives a floor for the
arithmetic leakage, which is exactly the hypothesis of `summable_secular_of_floor`.  Nothing beyond
summability of the perturbation is used, and trace-class operators have summable eigenvalues. -/
theorem summable_secular_of_traceClass_perturbation {ell lam e : ℕ → ℝ}
    (hnn : ∀ n, 0 ≤ lam n) (hanti : Antitone lam) {T : ℝ} (hT : 0 ≤ T)
    (hsum : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), lam k ≤ T)
    (he : Summable e) {μ : ℝ} (hμ : μ < 1 / 4)
    (_hbessel : Summable fun j => (ell j) ^ (2 : ℕ)) :
    ∃ M : ℕ, ∀ n, M ≤ n →
      (ell n / (((1 - lam n) + e n) - μ)) ^ (2 : ℕ) ≤ (ell n) ^ (2 : ℕ) / (1 / 4 - μ) ^ (2 : ℕ) := by
  obtain ⟨M, hM⟩ := exists_perturbed_leakage_floor hnn hanti hT hsum he
  exact ⟨M, fun n hn => sq_secular_le_of_floor (ℓ := ell)
    (d := fun k => (1 - lam k) + e k) (j := n) (hM n hn) hμ⟩

end RHTower
