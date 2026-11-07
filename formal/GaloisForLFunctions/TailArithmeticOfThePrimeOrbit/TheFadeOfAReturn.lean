import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheFirstReturnIsAnExtremeValue

/-!
# The fade of a return

At a fixed height `τ ≠ 0` the alignment of the head cannot persist: `ζ(1 + iτ)` is finite and nonzero, so the harmonic
defect `A_τ(N) = Σ_{p≤N} (1 − cos(τ log p))/p` grows like `log log N` (`tendsto_harmonicDefect`). Through the dictionary
`A_τ(N) = log log N − log|ζ(1 + 1/log N + iτ)| + O(1)` the growth has an exact offset:

* **The fade is forced** (`eventually_abs_harmonicDefect_sub_le`). Past a length `N₀(τ)`,
  `|A_τ(N) − log log N + log|ζ(1 + iτ)|| ≤ K + 1`. So the alignment of the primes at height `τ` *fades* at the
  effective length `log y_eff(τ) ≍ |ζ(1 + iτ)|`: the primes up to `y_eff` look aligned in the harmonic metric, the primes
  past it contribute their full `1/p`.
* **The fade length bounds every weak return at that height** (`logLog_le_of_isWeakReturn`). A weak return up to `N`
  with constant `C` at height `τ` has `log log N ≤ C + K + 1 + log|ζ(1 + iτ)|` once `N ≥ N₀(τ)`.
* **The fade is monotone** (`harmonicDefect_mono`): a weak return up to `N'` is one up to every `N ≤ N'`.

So the profile of a return is read from `ζ` on the `1`-line: the head length where the phases fade is `exp(O(|ζ(1+iτ)|))`.
Extreme values of `|ζ(1 + iτ)|` are long heads; Vinogradov–Korobov bounds `|ζ(1 + iτ)|` by `(log τ)^{2/3+o(1)}`, RH by
`2e^γ log log τ`.
-/

open Real Finset Filter Topology

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

/-- The harmonic defect is monotone in the length. -/
theorem harmonicDefect_mono (t : ℝ) {N N' : ℕ} (h : N ≤ N') : harmonicDefect N t ≤ harmonicDefect N' t := by
  unfold harmonicDefect
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => ?_
  · intro p hp
    rw [Nat.primesLE, Nat.mem_primesBelow] at *
    exact ⟨by omega, hp.2⟩
  · exact div_nonneg (by linarith [cos_le_one (t * Real.log p)]) (Nat.cast_nonneg p)

theorem IsWeakReturn.mono {N N' : ℕ} {C t : ℝ} (h : IsWeakReturn N' C t) (hN : N ≤ N') : IsWeakReturn N C t :=
  (harmonicDefect_mono t hN).trans h

/-- The fade length `|ζ(1 + iτ)|`. -/
def fadeLength (τ : ℝ) : ℝ := ‖riemannZeta (1 + (τ : ℂ) * Complex.I)‖

theorem tendsto_spikePoint (τ : ℝ) :
    Tendsto (fun N : ℕ => spikePoint N τ) atTop (𝓝 (1 + (τ : ℂ) * Complex.I)) := by
  have h1 : Tendsto (fun N : ℕ => 1 / Real.log (N : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop.congr fun N => by
      simp [one_div]
  have h2 : Tendsto (fun N : ℕ => (((1 + 1 / Real.log (N : ℝ) : ℝ) : ℂ))) atTop (𝓝 ((1 : ℝ) : ℂ)) := by
    have := (h1.const_add 1)
    rw [add_zero] at this
    exact (Complex.continuous_ofReal.tendsto 1).comp this
  have h3 := h2.add_const ((τ : ℂ) * Complex.I)
  rw [Complex.ofReal_one] at h3
  exact h3

theorem fadeLength_pos {τ : ℝ} (hτ : τ ≠ 0) : 0 < fadeLength τ := by
  unfold fadeLength
  refine norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re ?_)
  simp

/-- `log|ζ(1 + 1/log N + iτ)| → log|ζ(1 + iτ)|`. -/
theorem tendsto_log_norm_zeta_spikePoint {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun N : ℕ => Real.log ‖riemannZeta (spikePoint N τ)‖) atTop (𝓝 (Real.log (fadeLength τ))) := by
  have hne1 : (1 + (τ : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have : ((1 + (τ : ℂ) * Complex.I)).im = (1 : ℂ).im := by rw [h]
    simp at this
    exact hτ this
  have hcont : ContinuousAt riemannZeta (1 + (τ : ℂ) * Complex.I) :=
    (differentiableAt_riemannZeta hne1).continuousAt
  have h1 := (hcont.tendsto.comp (tendsto_spikePoint τ)).norm
  exact (Real.continuousAt_log (fadeLength_pos hτ).ne').tendsto.comp h1

/-- **The fade is forced.** -/
theorem eventually_abs_harmonicDefect_sub_le {τ : ℝ} (hτ : τ ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      |harmonicDefect N τ - RHTower.Sieve.logLog N + Real.log (fadeLength τ)| ≤ harmonicConst + 1 := by
  have h := tendsto_log_norm_zeta_spikePoint hτ
  filter_upwards [h.eventually (Metric.closedBall_mem_nhds _ one_pos), eventually_ge_atTop 3] with N hN hN3
  have hd := abs_harmonicDefect_sub_le hN3 τ
  rw [Metric.mem_closedBall, Real.dist_eq] at hN
  calc |harmonicDefect N τ - RHTower.Sieve.logLog N + Real.log (fadeLength τ)|
      = |(harmonicDefect N τ - (RHTower.Sieve.logLog N - Real.log ‖riemannZeta (spikePoint N τ)‖)) -
          (Real.log ‖riemannZeta (spikePoint N τ)‖ - Real.log (fadeLength τ))| := by ring_nf
    _ ≤ |harmonicDefect N τ - (RHTower.Sieve.logLog N - Real.log ‖riemannZeta (spikePoint N τ)‖)| +
          |Real.log ‖riemannZeta (spikePoint N τ)‖ - Real.log (fadeLength τ)| := abs_sub _ _
    _ ≤ harmonicConst + 1 := add_le_add hd hN

/-- **Every height fades.** At a fixed height `τ ≠ 0` the harmonic defect tends to infinity. -/
theorem tendsto_harmonicDefect {τ : ℝ} (hτ : τ ≠ 0) : Tendsto (fun N : ℕ => harmonicDefect N τ) atTop atTop := by
  have hlim : Tendsto (fun N : ℕ => RHTower.Sieve.logLog N - Real.log (fadeLength τ) - (harmonicConst + 1))
      atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ tendsto_logLog)
  refine tendsto_atTop_mono' atTop ?_ hlim
  filter_upwards [eventually_abs_harmonicDefect_sub_le hτ] with N hN
  linarith [(abs_le.mp hN).1]

/-- **The fade length bounds every weak return at that height.** -/
theorem logLog_le_of_isWeakReturn {τ : ℝ} (hτ : τ ≠ 0) :
    ∀ᶠ N : ℕ in atTop, ∀ C : ℝ, IsWeakReturn N C τ →
      RHTower.Sieve.logLog N ≤ C + harmonicConst + 1 + Real.log (fadeLength τ) := by
  filter_upwards [eventually_abs_harmonicDefect_sub_le hτ] with N hN C hC
  unfold IsWeakReturn at hC
  linarith [(abs_le.mp hN).2, (abs_le.mp hN).1]

/-- **A slow fade is a large value.** Past `N₀(τ)` the harmonic defect is at most `log log N − log|ζ(1 + iτ)| + K + 1`:
the larger `|ζ(1 + iτ)|`, the longer the head stays aligned. -/
theorem eventually_harmonicDefect_le {τ : ℝ} (hτ : τ ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      harmonicDefect N τ ≤ RHTower.Sieve.logLog N - Real.log (fadeLength τ) + harmonicConst + 1 := by
  filter_upwards [eventually_abs_harmonicDefect_sub_le hτ] with N hN
  linarith [(abs_le.mp hN).2]

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
