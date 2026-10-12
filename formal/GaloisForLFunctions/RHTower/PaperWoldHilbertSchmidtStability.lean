import GaloisForLFunctions.RHTower.PaperWoldSharpHilbertSchmidt
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTruncation

/-! # Stability of the exact full Wold energy domain

Arbitrary entrywise phases and Hilbert–Schmidt corrections preserve the sharp
threshold. In particular, deleting any finite block cannot repair its endpoint.
These are Hilbert–Schmidt statements, not assertions about all compact operators.
-/

namespace RHTower
noncomputable section
open Filter Topology
open scoped BigOperators

/-- The literal finite composite energies diverge at and above the boundary. -/
theorem paperWoldDirectedKernel_composite_energy_atTop
    (t : {t : ℝ // 1 / 2 ≤ t}) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, ∑ k ∈ Finset.range (m + 1),
      ‖paperWoldDirectedKernel t (2 * k + 2, 2 * m + 4)‖ ^ 2) atTop atTop :=
  tendsto_atTop_mono (paperWoldDirectedKernel_composite_triangle_lower t)
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 144))

/-- Even arbitrary coordinate-dependent phases retain the exact energy domain. -/
theorem paperWoldDirectedKernel_phase_isHS_iff (t : ℝ)
    (u : ℕ × ℕ → {z : ℂ // ‖z‖ = 1}) :
    HilbertSchmidt.IsHS (fun q => (u q : ℂ) * paperWoldDirectedKernel t q) ↔ t < 1 / 2 := by
  have he : HilbertSchmidt.IsHS (fun q => (u q : ℂ) * paperWoldDirectedKernel t q) ↔
      HilbertSchmidt.IsHS (paperWoldDirectedKernel t) := by
    simp only [HilbertSchmidt.IsHS, norm_mul, (u _).property, one_mul]
  exact he.trans (paperWoldDirectedKernel_isHS_iff t)

/-- Any square-summable correction preserves the exponent classification. -/
theorem paperWoldDirectedKernel_hsPerturbation_iff (t : ℝ)
    (J : {K : ℕ × ℕ → ℂ // HilbertSchmidt.IsHS K}) :
    HilbertSchmidt.IsHS (paperWoldDirectedKernel t + J.val) ↔ t < 1 / 2 := by
  constructor
  · intro h
    apply (paperWoldDirectedKernel_isHS_iff t).mp
    simpa only [add_sub_cancel_right] using HilbertSchmidt.isHS_sub h J.property
  · intro h
    exact ((paperWoldDirectedKernel_isHS_iff t).mpr h).add J.property

/-- Every literal finite cutoff is square summable, independently of the full domain. -/
theorem paperWoldDirectedKernel_finite_isHS (t : ℝ) (s : Finset ℕ) :
    HilbertSchmidt.IsHS (HilbertSchmidt.truncKernel (paperWoldDirectedKernel t) s) := by
  apply HilbertSchmidt.isHS_of_support_subset (s ×ˢ s)
  intro q hq
  simpa only [HilbertSchmidt.truncKernel, Finset.mem_product] using
    (if_neg (by simpa only [Finset.mem_product] using hq) :
      (if q.1 ∈ s ∧ q.2 ∈ s then paperWoldDirectedKernel t q else 0) = 0)

/-- Removing an arbitrary finite block leaves precisely the same admission boundary. -/
theorem paperWoldDirectedKernel_finite_tail_isHS_iff (t : ℝ) (s : Finset ℕ) :
    HilbertSchmidt.IsHS (paperWoldDirectedKernel t -
      HilbertSchmidt.truncKernel (paperWoldDirectedKernel t) s) ↔ t < 1 / 2 := by
  have h := paperWoldDirectedKernel_hsPerturbation_iff t
    ⟨-HilbertSchmidt.truncKernel (paperWoldDirectedKernel t) s,
      HilbertSchmidt.isHS_neg (paperWoldDirectedKernel_finite_isHS t s)⟩
  simpa only [sub_eq_add_neg] using h

end
end RHTower
