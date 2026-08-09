import GaloisForLFunctions.HTGeometry.PiGeometricSeries
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGamma

/-!
# The occupation Euler product

Occupations supported on a fixed finite nome set are exactly the functions on that set, so the
finite-index geometric identity gives the Euler product over any finite set.  Letting the set grow
is dominated convergence for sums, since the whole occupation family is absolutely summable as soon
as the nome family is.

The limit is the Euler product itself: the total occupation sum equals the infinite product of the
individual geometric sums, over an arbitrary index set and with no countability assumption.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

theorem nomeMonomial_supportedOccupationEquiv {ι : Type*} (u : ι → ℂ) (S : Finset ι) (f : S → ℕ) :
    nomeMonomial u ((supportedOccupationEquiv S) f).1 = ∏ a : S, u a ^ f a := by
  classical
  rw [nomeMonomial]
  change
    (Finsupp.embDomain (finsetSubtypeEmbedding S)
      (Finsupp.equivFunOnFinite.symm f)).prod (fun a n => u a ^ n) = _
  rw [Finsupp.prod_embDomain, Finsupp.prod_fintype]
  · rfl
  · intro
    simp

/-- **The Euler product over a finite nome set.** -/
theorem hasSum_supported_nomeMonomial {ι : Type*} (u : ι → ℂ) (hu : ∀ a, ‖u a‖ < 1)
    (S : Finset ι) :
    HasSum (fun ν : {ν : ι →₀ ℕ // ν.support ⊆ S} => nomeMonomial u ν.1)
      (∏ a ∈ S, (1 - u a)⁻¹) := by
  classical
  have hfin : HasSum (fun f : S → ℕ => ∏ a : S, (u a) ^ f a) (∏ a : S, (1 - u a)⁻¹) :=
    hasSum_pi_geometric (fun a : S => u a) (fun a => hu a)
  have hval : ∏ a : S, (1 - u a)⁻¹ = ∏ a ∈ S, (1 - u a)⁻¹ :=
    (Finset.prod_subtype S (fun _ => by simp) (fun a => (1 - u a)⁻¹)).symm
  rw [hval] at hfin
  have hfun : (fun f : S → ℕ => ∏ a : S, (u a) ^ f a)
      = (fun ν : {ν : ι →₀ ℕ // ν.support ⊆ S} => nomeMonomial u ν.1) ∘
        (supportedOccupationEquiv S) := by
    funext f
    rw [Function.comp_apply]
    exact (nomeMonomial_supportedOccupationEquiv u S f).symm
  rw [hfun] at hfin
  exact (Equiv.hasSum_iff (supportedOccupationEquiv S)).mp hfin

/-- **The occupation Euler product.**  For an absolutely summable family of contracting nomes the
total occupation sum is the infinite product of the individual geometric sums. -/
theorem hasProd_inv_one_sub_nome {ι : Type*} (u : ι → ℂ)
    (hu_lt : ∀ a, ‖u a‖ < 1) (hu_sum : Summable (fun a => ‖u a‖)) :
    HasProd (fun a => (1 - u a)⁻¹) (∑' ν : ι →₀ ℕ, nomeMonomial u ν) := by
  classical
  have hbound : Summable (fun ν : ι →₀ ℕ => ‖nomeMonomial u ν‖) := by
    have h := (summable_nomeMonomial_pow_iff 0 u hu_lt).2 (by simpa using hu_sum)
    simpa using h
  have hindicator : ∀ S : Finset ι,
      HasSum (Set.indicator {ν : ι →₀ ℕ | ν.support ⊆ S} (nomeMonomial u))
        (∏ a ∈ S, (1 - u a)⁻¹) :=
    fun S => hasSum_subtype_iff_indicator.mp (hasSum_supported_nomeMonomial u hu_lt S)
  have hpoint : ∀ ν : ι →₀ ℕ,
      Tendsto (fun S : Finset ι =>
        Set.indicator {ν : ι →₀ ℕ | ν.support ⊆ S} (nomeMonomial u) ν) atTop
        (𝓝 (nomeMonomial u ν)) := by
    intro ν
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ν.support] with S hS
    have hmem : ν ∈ {ν : ι →₀ ℕ | ν.support ⊆ S} := hS
    rw [Set.indicator_of_mem hmem]
  have hdom : ∀ᶠ S : Finset ι in atTop, ∀ ν : ι →₀ ℕ,
      ‖Set.indicator {ν : ι →₀ ℕ | ν.support ⊆ S} (nomeMonomial u) ν‖
        ≤ ‖nomeMonomial u ν‖ := by
    refine Eventually.of_forall fun S ν => ?_
    by_cases hν : ν ∈ {ν : ι →₀ ℕ | ν.support ⊆ S}
    · rw [Set.indicator_of_mem hν]
    · rw [Set.indicator_of_notMem hν, norm_zero]
      exact norm_nonneg _
  have hlim := tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  have hval : ∀ S : Finset ι,
      (∑' ν : ι →₀ ℕ, Set.indicator {ν : ι →₀ ℕ | ν.support ⊆ S} (nomeMonomial u) ν)
        = ∏ a ∈ S, (1 - u a)⁻¹ := fun S => (hindicator S).tsum_eq
  rw [funext hval] at hlim
  exact hlim

/-- The Euler product in `tsum`/`tprod` form. -/
theorem tsum_nomeMonomial_eq_tprod {ι : Type*} (u : ι → ℂ)
    (hu_lt : ∀ a, ‖u a‖ < 1) (hu_sum : Summable (fun a => ‖u a‖)) :
    (∑' ν : ι →₀ ℕ, nomeMonomial u ν) = ∏' a, (1 - u a)⁻¹ :=
  (hasProd_inv_one_sub_nome u hu_lt hu_sum).tprod_eq.symm

end HTGeometry
