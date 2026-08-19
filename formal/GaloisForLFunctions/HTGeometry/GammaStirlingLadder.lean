import GaloisForLFunctions.HTGeometry.GammaStirlingLadderStep
import GaloisForLFunctions.HTGeometry.GammaStirlingTelescope
import GaloisForLFunctions.HTGeometry.GammaDigammaStirlingBound

/-!
# The Stirling ladder for the digamma function at every finite order

The four hand-built rungs of the ladder are now replaced by a single theorem valid at every order:
there are coefficients `ladderCoeff m` — *forced*, with no Bernoulli input — such that

`ψ z = log z - ∑_{m<M} c_m z^{-(m+1)} + O(‖z‖^{-(M+1)})`

uniformly on `{Re z > 0, ‖z‖ ≥ 2}`, for every `M`.

The proof is the telescope of `GammaStirlingTelescope` applied to the step bound of
`GammaStirlingLadderStep`, anchored at infinity by the shift limit of `GammaDigammaStirlingBound`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

theorem tendsto_norm_add_natCast_atTop (z : ℂ) :
    Tendsto (fun n : ℕ => ‖z + (n : ℂ)‖) atTop atTop := by
  have hbase : Tendsto (fun n : ℕ => z.re + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop z.re tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono (fun n => ?_) hbase
  have h := Complex.re_le_norm (z + (n : ℂ))
  rwa [Complex.add_re, Complex.natCast_re] at h

theorem tendsto_div_pow_add_natCast (z c : ℂ) (k : ℕ) :
    Tendsto (fun n : ℕ => c / (z + (n : ℂ)) ^ (k + 1)) atTop (nhds 0) := by
  have h1 : Tendsto (fun n : ℕ => ‖z + (n : ℂ)‖ ^ (k + 1)) atTop atTop :=
    (tendsto_pow_atTop (by omega)).comp (tendsto_norm_add_natCast_atTop z)
  have h2 : Tendsto (fun n : ℕ => ‖c‖ / ‖z + (n : ℂ)‖ ^ (k + 1)) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds h1
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [norm_div, norm_pow] using h2

theorem tendsto_ladderDefect_shift_zero (M : ℕ) {z : ℂ} (hz : 0 ≤ z.re) :
    Tendsto (fun n : ℕ => ladderDefect M (z + (n : ℂ))) atTop (nhds 0) := by
  have hdsd := tendsto_digammaStirlingDefect_shift_zero hz
  have hhalf : Tendsto (fun n : ℕ => (1 : ℂ) / (2 * (z + (n : ℂ)))) atTop (nhds 0) := by
    refine (tendsto_div_pow_add_natCast z (1 / 2) 0).congr (fun n => ?_)
    simp only [mul_inv, div_eq_mul_inv]
    ring
  have hsum : Tendsto (fun n : ℕ =>
      ∑ m ∈ Finset.range M, ladderCoeff m / (z + (n : ℂ)) ^ (m + 1)) atTop (nhds 0) := by
    have h := tendsto_finsetSum (Finset.range M)
      (fun m (_ : m ∈ Finset.range M) => tendsto_div_pow_add_natCast z (ladderCoeff m) m)
    simpa using h
  have hcomb := (hdsd.sub hhalf).add hsum
  simp only [sub_zero, add_zero] at hcomb
  refine hcomb.congr (fun n => ?_)
  rw [digammaStirlingDefect, ladderDefect]
  ring

/-- **The Stirling ladder at every finite order.**  For each `M` the digamma function agrees with
`log z - ∑_{m<M} c_m z^{-(m+1)}` to within `O(‖z‖^{-(M+1)})` on the half plane `Re z > 0`,
`‖z‖ ≥ 2`.  The coefficients are the forced ladder coefficients, independent of `M`. -/
theorem exists_norm_ladderDefect_le (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 0 < z.re → 2 ≤ ‖z‖ →
      ‖ladderDefect M z‖ ≤ K / ‖z‖ ^ (M + 1) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_ladderDefect_step_le M
  refine ⟨3 * K, by linarith, fun z hz h2 => ?_⟩
  exact norm_le_of_step_bound hK0 (fun w hw hw2 => hK w hw hw2) hz h2
    (tendsto_ladderDefect_shift_zero M hz.le)

/-- The ladder in expanded form: `ψ z + ∑_{m<M} c_m z^{-(m+1)} - log z` is `O(‖z‖^{-(M+1)})`. -/
theorem exists_norm_digamma_ladder_expansion_le (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 0 < z.re → 2 ≤ ‖z‖ →
      ‖Complex.digamma z - (Complex.log z - ∑ m ∈ Finset.range M, ladderCoeff m / z ^ (m + 1))‖
        ≤ K / ‖z‖ ^ (M + 1) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_ladderDefect_le M
  refine ⟨K, hK0, fun z hz h2 => ?_⟩
  have := hK z hz h2
  rw [ladderDefect] at this
  convert this using 2
  ring

end

end GaloisForLFunctions.HTGeometry
