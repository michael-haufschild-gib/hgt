import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGamma

/-!
# Finite-nome exhaustion of the infinite-order product

Finite nome sets retain every occupation supported on those nomes.  Their canonical products
converge along the directed set of all finite nome subsets to the full infinite-order product.
The result is independent of an enumeration or exhaustion sequence.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

noncomputable def finiteNomeSection {ι : Type*}
    (g : ℕ) (p : ι → ℂ) (S : Finset ι) (x : ℂ) : ℂ := by
  classical
  exact ∏' ν : ι →₀ ℕ,
    if ν.support ⊆ S then primaryFactor g (x * nomeMonomial p ν) else 1

theorem tendsto_finiteNomeSection {ι : Type*}
    (g : ℕ) (p : ι → ℂ) (hp_ne : ∀ a, p a ≠ 0)
    (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (x : ℂ) :
    Tendsto (fun S : Finset ι => finiteNomeSection g p S x) atTop
      (𝓝 (infiniteMultipleEllipticGamma g p x)) := by
  classical
  let q : (ι →₀ ℕ) → ℂ := nomeMonomial p
  let d : (ι →₀ ℕ) → ℂ :=
    fun ν => primaryFactor g (x * q ν) - 1
  let f : Finset ι → (ι →₀ ℕ) → ℂ :=
    fun S ν => if ν.support ⊆ S then d ν else 0
  have hq_ne : ∀ ν, q ν ≠ 0 := nomeMonomial_ne_zero p hp_ne
  have hq_sum : Summable (fun ν => ‖q ν‖ ^ (g + 1)) :=
    (summable_nomeMonomial_pow_iff g p hp_lt).2 hsum
  have hdom : Summable (fun ν => ‖d ν‖) := by
    simpa only [d, q] using
      canonicalWeightProduct_sub_one_norm_summable g q hq_ne hq_sum x
  have hpoint : ∀ ν, Tendsto (fun S : Finset ι => f S ν) atTop (𝓝 (d ν)) := by
    intro ν
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ν.support] with S hS
    have hsub : ν.support ⊆ S := hS
    simp [f, hsub]
  have hbound : ∀ᶠ S : Finset ι in atTop, ∀ ν, ‖f S ν‖ ≤ ‖d ν‖ := by
    refine Eventually.of_forall fun S ν => ?_
    by_cases hν : ν.support ⊆ S
    · simp [f, hν]
    · simp [f, hν]
  have hlim := tendsto_tprod_one_add_of_dominated_convergence hdom hpoint hbound
  convert hlim using 1
  · funext S
    rw [finiteNomeSection]
    apply tprod_congr
    intro ν
    by_cases hν : ν.support ⊆ S
    · simp [f, d, q, hν]
    · simp [f, hν]
  · simp only [infiniteMultipleEllipticGamma, canonicalWeightProduct, d, q]
    congr 1
    apply tprod_congr
    intro ν
    ring

end HTGeometry
