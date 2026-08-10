import GaloisForLFunctions.RHTower.DeningerDirichletAbel

/-!
# The Dirichlet series equals the Abel average

Passing to the limit in the finite Abel identity: the boundary term vanishes, the left side
converges to the Dirichlet series and the right side to the Abel average of the harmonic partial
sums.  So for every positive exponent

`∑_n μ(n) n^{-1-σ} = ∑_m A_{m+1} w_σ(m)`.

The right side tends to `∑ μ(n)/n` as `σ ↓ 0` by the Abelian limit theorem; the left side is
`ζ(1+σ)⁻¹`, which tends to `0` by the pole.  Equating the two limits is what forces the value.

* `deningerDirichlet_eq_abelAverage` : **the Dirichlet series is the Abel average.**
-/

namespace RHTower

open ArithmeticFunction Filter Topology

noncomputable section

/-- **The Dirichlet series equals the Abel average of the harmonic partial sums.** -/
theorem deningerDirichlet_eq_abelAverage {σ : ℝ} (hσ : 0 < σ) :
    (∑' n : ℕ, deningerDirichletTerm σ n)
      = ∑' m : ℕ, deningerHarmonicPartial (m + 1) * deningerAbelWeight σ m := by
  have hsum := deningerMobiusDirichlet_summable hσ
  have hleft : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 2), deningerDirichletTerm σ n)
      atTop (𝓝 (∑' n : ℕ, deningerDirichletTerm σ n)) :=
    (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 2)
  have hbdry : Tendsto
      (fun N : ℕ => deningerHarmonicPartial (N + 1) * (((N : ℝ) + 1) ^ (-σ))) atTop (𝓝 0) := by
    have hshift := (deningerHarmonicBoundary_tendsto_zero hσ).comp (tendsto_add_atTop_nat 1)
    refine hshift.congr fun N => ?_
    simp only [Function.comp_apply]
    congr 2
    push_cast
    ring
  have hCS : ∃ C : ℝ, ∀ n, |deningerHarmonicPartial (n + 1)| ≤ C := by
    obtain ⟨C, hC⟩ := deningerHarmonicPartial_bounded
    exact ⟨C, fun n => hC (n + 1)⟩
  obtain ⟨C, hC⟩ := hCS
  have hav : Summable fun m : ℕ =>
      deningerHarmonicPartial (m + 1) * deningerAbelWeight σ m :=
    deningerAbelAverage_summable hC hσ
  have hright : Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.range N,
        deningerHarmonicPartial (m + 1) * deningerAbelWeight σ m) atTop
      (𝓝 (∑' m : ℕ, deningerHarmonicPartial (m + 1) * deningerAbelWeight σ m)) :=
    hav.hasSum.tendsto_sum_nat
  have hcomb := hbdry.add hright
  rw [zero_add] at hcomb
  refine tendsto_nhds_unique hleft ?_
  refine hcomb.congr fun N => ?_
  exact (deningerDirichlet_abelSum N).symm

end

end RHTower
