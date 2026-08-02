import GaloisForLFunctions.HTGeometry.GradedSullivanAugmented
import GaloisForLFunctions.HTGeometry.GradedGCAIndependence

/-!
# The cohomology comparison, degreewise

Over an infinite field the weight decomposition of a free graded-commutative algebra is direct, so a
class splits into homogeneous components and the components are determined by the class.  If the
tower's generator values are homogeneous the differential carries components to components, and if
the target carries a matching weight action so does the augmentation.  The cohomology comparison of
the relative tower is then injective on every class, not only on the homogeneous ones — and in that
form it needs no parity hypothesis and no invertibility of `2`.

* `DeningerGCAAugStage.omega_isCoboundary_of_graded` : clause 3 degreewise, for every class.
-/

namespace HTGeometry

namespace DeningerGCAAugStage

universe u w

variable {k : Type u} [Field k] {K : Type w} [Ring K] [Algebra k K]

/-- **Clause 3 degreewise, for every class.**  Over an infinite field, if the tower's generator
values are homogeneous and the target carries a weight action matching the augmentation on the base
generators, then every cocycle of the limit dying in the target is a coboundary — with no parity
hypothesis and no invertibility of `2`.

The proof decomposes the class into its homogeneous components.  Independence of distinct weights
forces each component to be a cocycle, because the differential raises weight by one; the same
independence in the target forces each component to die there; and each component is then a
coboundary by the homogeneous form. -/
theorem omega_isCoboundary_of_graded [Infinite k] (B : DeningerGCAAugStage k K)
    (sigma : k → (K →ₐ[k] K))
    (hsig : ∀ (t : k) (x : B.toStage.gen), sigma t (B.eps (deningerGCAι k B.toStage.deg x)) =
      (t ^ B.toStage.deg x) • B.eps (deningerGCAι k B.toStage.deg x))
    (hhom : ∀ u : omegaGen B,
      DeningerGCAHomogeneous k (omegaDeg B) (omegaDeg B u + 1) (omegaPhi B u))
    {z : DeningerFreeGCA k (omegaGen B) (omegaDeg B)} (hz : (omega B).d z = 0)
    (hzero : epsOmega B z = 0) :
    ∃ y, (omega B).d y = z := by
  classical
  obtain ⟨m, f, hf, hf0, rfl⟩ := deningerGCA_exists_homogeneous_components z
  -- every component is a cocycle
  have hdsum : ∑ i ∈ Finset.range m, (omega B).d (f i) = 0 := by
    rw [← map_sum]
    exact hz
  set g : ℕ → DeningerFreeGCA k (omegaGen B) (omegaDeg B) :=
    fun j => match j with | 0 => 0 | i + 1 => (omega B).d (f i) with hgdef
  have hg : ∀ j, DeningerGCAHomogeneous k (omegaDeg B) j (g j) := by
    intro j
    cases j with
    | zero => exact deningerGCAHomogeneous_zero 0
    | succ i => exact DeningerGCAStage.d_homogeneous (omega B) hhom (hf i)
  have hgsum : ∑ j ∈ Finset.range (m + 1), g j = 0 := by
    rw [Finset.sum_range_succ']
    show (∑ i ∈ Finset.range m, (omega B).d (f i)) + 0 = 0
    rw [add_zero]
    exact hdsum
  have hdf : ∀ i, i < m → (omega B).d (f i) = 0 := by
    intro i hi
    exact deningerGCAHomogeneous_eq_zero_of_sum_eq_zero g hg hgsum (i + 1) (by omega)
  -- every component dies in the target
  have heps : ∀ i, i < m → epsOmega B (f i) = 0 := by
    refine fun i hi => eq_zero_of_forall_sum_pow_smul_eq_zero (k := k)
      (fun j => epsOmega B (f j)) (fun t => ?_) i hi
    have hzt : sigma t (epsOmega B (∑ j ∈ Finset.range m, f j)) = 0 := by
      rw [hzero, map_zero]
    rw [map_sum, map_sum] at hzt
    rw [← hzt]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← epsOmega_weight B sigma hsig t (f j), hf j t, map_smul]
  -- assemble
  have hcb : ∀ i ∈ Finset.range m, ∃ y, (omega B).d y = f i := by
    intro i hi
    exact omega_isCoboundary_of_homogeneous_weight B i (hdf i (Finset.mem_range.1 hi)) (hf i)
      (heps i (Finset.mem_range.1 hi))
  choose! y hy using hcb
  refine ⟨∑ i ∈ Finset.range m, y i, ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun i hi => hy i hi

end DeningerGCAAugStage

end HTGeometry
