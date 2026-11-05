import GaloisForLFunctions.FiniteFreeProbability.KernelJensenRoots

/-!
# Almost all Jensen roots of `Ξ` are real and simple, unconditionally

**Theorem.** For every `η > 0` and all large `d`, the reversed Jensen polynomial `R_d(Ξ)` has at least
`(1 − η) d` distinct real roots. So the proportion of non-real roots tends to `0`, whether or not RH holds.
(RH is the statement that this proportion is `0` for every `d`.)

This is the instance `g = Φ` of the theorem on hyperbolic kernels (`KernelJensenRoots`).
-/

open Polynomial Filter Topology Complex
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace FiniteFreeProbability

noncomputable section

theorem mk_xiShiftCoeff_half : PowerSeries.mk (xiShiftCoeff (1 / 2)) = xiSeries := by
  ext k
  rw [PowerSeries.coeff_mk]
  exact xiShiftCoeff_half k

/-- `R_d(ξ(1/2 + i·))` is the Jensen polynomial of the kernel `Φ`. -/
theorem xiJensen_half_eq_kernelJensen (d : ℕ) :
    xiJensen (1 / 2) d = kernelJensen riemannKernelReal d := by
  refine Polynomial.funext fun w => ?_
  rw [eval_xiJensen_eq_integral, hyperbolicKernel_riemann.eval_kernelJensen]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp

theorem jensenRev_xiSeries_eq_kernelJensen (d : ℕ) :
    jensenRev d xiSeries = kernelJensen riemannKernelReal d := by
  rw [← xiJensen_half_eq_kernelJensen, xiJensen, mk_xiShiftCoeff_half]

/-- **Almost all roots of the Jensen polynomials of `Ξ` are real and simple, unconditionally.** For every
`η > 0` and all large `d`, `R_d(Ξ)` has at least `(1 − η) d` distinct real roots. -/
theorem eventually_exists_real_roots_xiSeries {η : ℝ} (hη : 0 < η) :
    ∀ᶠ d : ℕ in atTop, ∃ S : Finset ℝ, (1 - η) * d ≤ S.card ∧
      ∀ x ∈ S, (jensenRev d xiSeries).IsRoot (x : ℂ) := by
  simp_rw [jensenRev_xiSeries_eq_kernelJensen]
  exact hyperbolicKernel_riemann.eventually_exists_real_roots hη

/-- The proportion of non-real roots of `R_d(Ξ)`, with multiplicity, tends to `0`. -/
theorem tendsto_card_nonreal_roots_div :
    Tendsto (fun d : ℕ =>
      (Multiset.card ((jensenRev d xiSeries).roots.filter fun x => x.im ≠ 0) : ℝ) / d)
      atTop (𝓝 0) := by
  simp_rw [jensenRev_xiSeries_eq_kernelJensen]
  exact hyperbolicKernel_riemann.tendsto_card_nonreal_roots_div

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eventually_exists_real_roots_xiSeries
#print axioms FiniteFreeProbability.tendsto_card_nonreal_roots_div
