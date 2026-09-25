import GaloisForLFunctions.RHTower.DivisorCoreMellinInverseGeometricNoGo

/-!
# Compact-band amplification of the literal processed divisor Mellin core

The inverse-geometric factorization gives pointwise divergence at every nonzero
Mellin frequency and monotonicity under core growth.  Continuity and compactness
upgrade these to uniform divergence on every compact band avoiding frequency zero.
Thus a fixed spectral packet away from zero cannot be uniformly controlled by
the growing core's zero-frequency residue.  This does not rule out signed
Fourier-integral cancellation or resolve the physical moving cutoff.
-/

open Filter Set
open scoped Topology

namespace RHTower

/-- Norm of the literal finite-core Euler multiplier relative to its residue factor. -/
noncomputable def divisorCoreMellinNormalizedCoreNorm (t : ℝ) (s : Finset Nat.Primes) : ℝ :=
  ‖divisorCoreMellinEuler (s.image (fun p : Nat.Primes => (p : ℕ)))
    ((t : ℂ) * Complex.I) /
    divisorCoreMellinEuler (s.image (fun p : Nat.Primes => (p : ℕ))) 0‖

private theorem continuous_normalizedCoreNorm (s : Finset Nat.Primes) :
    Continuous (fun t : ℝ => divisorCoreMellinNormalizedCoreNorm t s) := by
  have harg : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) := by fun_prop
  have hnum : Continuous (fun t : ℝ =>
      divisorCoreMellinEuler (s.image (fun p : Nat.Primes => (p : ℕ)))
        ((t : ℂ) * Complex.I)) :=
    (differentiable_divisorCoreMellinEuler _).continuous.comp harg
  exact (hnum.div_const _).norm

/-- Pointwise inverse smoothing is uniformly unbounded on any compact
nonzero-frequency band, even before the arithmetic source is inserted. -/
theorem exists_uniform_large_divisorCoreMellinEuler_ratio_on_compact
    {K : Set ℝ} (hK : IsCompact K) (h0 : 0 ∉ K) (B : ℝ) :
    ∃ s : Finset Nat.Primes, ∀ t ∈ K,
      B < divisorCoreMellinNormalizedCoreNorm t s := by
  classical
  let U : Finset Nat.Primes → Set ℝ := fun s =>
    {t | B < divisorCoreMellinNormalizedCoreNorm t s}
  have hopen : ∀ s : Finset Nat.Primes, IsOpen (U s) := by
    intro s
    exact isOpen_lt continuous_const (continuous_normalizedCoreNorm s)
  have hcover : K ⊆ ⋃ s : Finset Nat.Primes, U s := by
    intro t ht
    have ht0 : t ≠ 0 := by
      intro heq
      exact h0 (heq ▸ ht)
    have hpoint := tendsto_divisorCoreMellinEuler_ratio_norm_atTop ht0
    have hevent : ∀ᶠ s : Finset Nat.Primes in atTop,
        B < divisorCoreMellinNormalizedCoreNorm t s :=
      hpoint.eventually (eventually_gt_atTop B)
    obtain ⟨s, hs⟩ := hevent.exists
    exact Set.mem_iUnion.mpr ⟨s, hs⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover U hopen hcover
  refine ⟨T.biUnion id, ?_⟩
  intro t ht
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (hT ht)
  obtain ⟨hsT, hsB⟩ := Set.mem_iUnion.mp hs
  exact lt_of_lt_of_le hsB
    (norm_divisorCoreMellinEuler_ratio_mono t
      (Finset.subset_biUnion_of_mem (fun s : Finset Nat.Primes => s) hsT))

end RHTower
