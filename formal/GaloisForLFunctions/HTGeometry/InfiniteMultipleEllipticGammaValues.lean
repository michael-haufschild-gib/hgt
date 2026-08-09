import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGamma

/-!
# Values and nonconstancy of the infinite-order multiple elliptic gamma product

The empty occupation contributes the factor `E_g(x)`, so the infinite product takes the value one
at the origin and vanishes at one.  Both facts are exact, not asymptotic: the vanishing comes from a
single factor of the convergent product.

Consequently the shifted product appearing in the coface recursion is nonconstant for every nome,
so no nome is redundant, and the limit itself is nonconstant — the forward half collapsing to one
does not trivialize what remains.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

@[simp] theorem nomeMonomial_zero {ι : Type*} (p : ι → ℂ) :
    nomeMonomial p 0 = 1 := by
  rw [nomeMonomial]
  simp

@[simp] theorem infiniteMultipleEllipticGamma_at_zero {ι : Type*} (g : ℕ) (p : ι → ℂ) :
    infiniteMultipleEllipticGamma g p 0 = 1 := by
  rw [infiniteMultipleEllipticGamma, canonicalWeightProduct]
  simp

/-- **The limit vanishes at one.**  The empty occupation contributes the factor `E_g(1) = 0`. -/
theorem infiniteMultipleEllipticGamma_at_one {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) :
    infiniteMultipleEllipticGamma g p 1 = 0 := by
  classical
  have hprod :=
    (infiniteMultipleEllipticGamma_hasProdLocallyUniformlyOn g p hp_ne hp_lt hsum).hasProd
      (Set.mem_univ (1 : ℂ))
  have hzero : primaryFactor g ((1 : ℂ) * nomeMonomial p 0) = 0 := by
    rw [nomeMonomial_zero, mul_one, primaryFactor]
    simp
  have htend : Tendsto
      (fun s : Finset (ι →₀ ℕ) => ∏ ν ∈ s, primaryFactor g ((1 : ℂ) * nomeMonomial p ν))
      atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop ({0} : Finset (ι →₀ ℕ))] with s hs
    exact (Finset.prod_eq_zero (hs (Finset.mem_singleton_self 0)) hzero).symm
  exact tendsto_nhds_unique hprod htend

/-- **Every nome contributes.**  The shifted product occurring in the coface recursion separates the
origin from the reciprocal nome, so it is nonconstant for each nome. -/
theorem infiniteMultipleEllipticGamma_shift_nonconstant {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (a : ι) :
    infiniteMultipleEllipticGamma g p (p a * 0) ≠
      infiniteMultipleEllipticGamma g p (p a * (p a)⁻¹) := by
  rw [mul_zero, infiniteMultipleEllipticGamma_at_zero, mul_inv_cancel₀ (hp_ne a),
    infiniteMultipleEllipticGamma_at_one g p hp_ne hp_lt hsum]
  exact one_ne_zero

/-- The infinite-order product is nonconstant at every admissible genus. -/
theorem infiniteMultipleEllipticGamma_nonconstant {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) :
    infiniteMultipleEllipticGamma g p 0 ≠ infiniteMultipleEllipticGamma g p 1 := by
  rw [infiniteMultipleEllipticGamma_at_zero,
    infiniteMultipleEllipticGamma_at_one g p hp_ne hp_lt hsum]
  exact one_ne_zero

end HTGeometry
