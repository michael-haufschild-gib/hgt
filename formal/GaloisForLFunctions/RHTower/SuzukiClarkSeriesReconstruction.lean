import GaloisForLFunctions.RHTower.SuzukiDonoghueSeriesTransform
import GaloisForLFunctions.RHTower.SuzukiClarkFiniteReconstruction
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# The boundary Clark reconstruction for the countable lattice

Above the real axis the Donoghue kernel is bounded by the imaginary height alone, which is what
makes the countable transform converge.  On the real axis that bound degenerates, so the boundary
series needs a different input: the atoms must stay away from the point being evaluated.

For a Suzuki configuration this is automatic — the physical points `x_k = tan u_k` escape to
infinity, so they have no finite accumulation point and every non-atom is separated from all of
them.  Under that separation the boundary series converges absolutely, and the reconstruction is
odd whenever the configuration is symmetric, exactly as in the finite case.

Together with the countable transform this gives the Clark reconstruction for the full lattice, and
fixed-lattice rigidity for it.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The boundary Clark reconstruction of a countable atomic configuration. -/
noncomputable def clarkSeriesReconstruction (p x : ℤ → ℝ) (t : ℝ) : ℝ :=
  ∑' k, p k * donoghueRealKernel (x k) t

/-- **The boundary series converges absolutely away from the atoms.**  Separation from the atoms
replaces the imaginary height as the uniform bound on the kernel. -/
theorem summable_clarkSeries {p x : ℤ → ℝ} (hp : Summable p) (hp0 : ∀ k, 0 ≤ p k)
    {t δ : ℝ} (hδ : 0 < δ) (hsep : ∀ k, δ ≤ |x k - t|) :
    Summable (fun k => p k * donoghueRealKernel (x k) t) := by
  refine Summable.of_norm_bounded (hp.mul_right (|t| + (t ^ 2 + 1) / δ)) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 k)]
  refine mul_le_mul_of_nonneg_left ?_ (hp0 k)
  rw [donoghueRealKernel]
  have htri : |t + (t ^ 2 + 1) / (x k - t)| ≤ |t| + |(t ^ 2 + 1) / (x k - t)| := by
    simpa [Real.norm_eq_abs] using norm_add_le t ((t ^ 2 + 1) / (x k - t))
  have habs : |(t ^ 2 + 1) / (x k - t)| ≤ (t ^ 2 + 1) / δ := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < t ^ 2 + 1)]
    exact div_le_div_of_nonneg_left (by positivity) hδ (hsep k)
  linarith

/-- **A symmetric countable configuration has an odd boundary reconstruction.** -/
theorem clarkSeriesReconstruction_odd {p x : ℤ → ℝ}
    (σ : Equiv.Perm ℤ) (hx : ∀ k, x (σ k) = -x k) (hp : ∀ k, p (σ k) = p k) (t : ℝ) :
    clarkSeriesReconstruction p x (-t) = -clarkSeriesReconstruction p x t := by
  rw [clarkSeriesReconstruction, clarkSeriesReconstruction, ← tsum_neg,
    ← Equiv.tsum_eq σ (fun k => p k * donoghueRealKernel (x k) (-t))]
  refine tsum_congr fun k => ?_
  rw [hp, hx, donoghueRealKernel_neg]
  ring

/-- The reconstruction depends on nothing but the jets. -/
theorem clarkSeriesReconstruction_congr {p₁ x₁ p₂ x₂ : ℤ → ℝ}
    (hp : p₁ = p₂) (hx : x₁ = x₂) :
    clarkSeriesReconstruction p₁ x₁ = clarkSeriesReconstruction p₂ x₂ := by
  rw [hp, hx]

/-- The complement of a countable subset of the line is dense. -/
theorem dense_compl_of_countable {s : Set ℝ} (hs : s.Countable) : Dense sᶜ :=
  hs.dense_compl ℝ

/-- **`(19)` for the countable Clark class.**  The lattice is indexed by `ZZ`, so the atom set is
countable; its complement is still dense, and the phase equation off the atoms suffices. -/
theorem suzuki_fixedLattice_rigidity_countable_offAtoms
    {φ₁ φ₂ : ℝ → ℝ} {p₁ x₁ p₂ x₂ : ℤ → ℝ}
    (hc₁ : Continuous φ₁) (hc₂ : Continuous φ₂)
    (hr₁ : ∀ t, φ₁ (-t) = 2 * Real.pi - φ₁ t) (hr₂ : ∀ t, φ₂ (-t) = 2 * Real.pi - φ₂ t)
    (hl₁ : ∀ t, (∀ k, x₁ k ≠ t) → Complex.exp ((φ₁ t : ℂ) * Complex.I)
      = cayleyOfHerglotz ((clarkSeriesReconstruction p₁ x₁ t : ℝ) : ℂ))
    (hl₂ : ∀ t, (∀ k, x₂ k ≠ t) → Complex.exp ((φ₂ t : ℂ) * Complex.I)
      = cayleyOfHerglotz ((clarkSeriesReconstruction p₂ x₂ t : ℝ) : ℂ))
    (hp : p₁ = p₂) (hx : x₁ = x₂) : φ₁ = φ₂ := by
  have hcount : (Set.range x₁ ∪ Set.range x₂).Countable :=
    (Set.countable_range x₁).union (Set.countable_range x₂)
  refine phase_eq_of_boundaryHerglotz_eq_off (dense_compl_of_countable hcount) hc₁ hc₂ hr₁ hr₂
    ?_ ?_ (clarkSeriesReconstruction_congr hp hx)
  · intro t ht
    exact hl₁ t fun k hk => ht (Or.inl ⟨k, hk⟩)
  · intro t ht
    exact hl₂ t fun k hk => ht (Or.inr ⟨k, hk⟩)

end GaloisForLFunctions.RHTower
