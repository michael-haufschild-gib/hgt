import GaloisForLFunctions.HTGeometry.ArchimedeanProductExponentialBound

/-!
# The lowest power of the archimedean product dominates

After factoring out the lowest surviving power of `G` and its coefficient, what remains is `1` plus
a finite sum of coefficient ratios against positive powers of `G`.  Every such term dies, so the
normalized quotient tends to `1`: this is the card's equation `(28)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **The higher powers are negligible against the lowest.** -/
theorem tendsto_one_add_polyGrowth_mul_archimedeanProduct_pow {d : ℕ} (lam : Fin d → ℝ)
    (μ : Fin d → ℂ) (hlam : ∀ j, 0 < lam j) {σ : ℝ} (hσ : ∀ j, 0 < lam j * σ + (μ j).re)
    (α : ℝ) (hd : 0 < d) {N : ℕ} (g : Fin N → ℝ → ℂ) (Cg : Fin N → ℝ) (mg : Fin N → ℕ)
    (kg : Fin N → ℕ) (hC : ∀ i, 0 ≤ Cg i) (hk : ∀ i, 0 < kg i)
    (hg : ∀ i, ∀ᶠ t : ℝ in atTop, ‖g i t‖ ≤ Cg i * t ^ mg i) :
    Tendsto (fun t : ℝ =>
        1 + ∑ i : Fin N, g i t * (archimedeanProductLine lam μ α σ t) ^ (kg i))
      atTop (nhds 1) := by
  have hterm : ∀ i : Fin N,
      Tendsto (fun t : ℝ => g i t * (archimedeanProductLine lam μ α σ t) ^ (kg i))
        atTop (nhds 0) := fun i =>
    tendsto_polyGrowth_mul_archimedeanProduct_pow_zero lam μ hlam hσ α hd (hC i) (hg i) (hk i)
  have hsum : Tendsto
      (fun t : ℝ => ∑ i : Fin N, g i t * (archimedeanProductLine lam μ α σ t) ^ (kg i))
      atTop (nhds 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin N))
      (f := fun i (t : ℝ) => g i t * (archimedeanProductLine lam μ α σ t) ^ (kg i))
      (a := fun _ => (0 : ℂ)) (fun i _ => hterm i)
    simpa using h
  have hfin := hsum.const_add 1
  rw [add_zero] at hfin
  exact hfin

end

end GaloisForLFunctions.HTGeometry
