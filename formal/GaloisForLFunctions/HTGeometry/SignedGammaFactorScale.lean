import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance

/-!
# General-scale single signed-Gamma factor carriers are hypertranscendental

The `d = 1`, single-orbit case of the signed-archimedean orbit-charge dichotomy (§3), at *arbitrary*
commensurable scale `c ≠ 0` (not only unit scale): a nonzero scalar multiple of a rescaled shifted
Gamma factor `a·Γ(c·s + d)`, and of its logarithmic-derivative carrier `a·ψ(c·s + d)`, is
hypertranscendental.  For a single Gamma orbit factor `Γ(c·s + d)^m` with charge `m ≠ 0` the
logarithmic derivative is `G'/G = m·c·ψ(c·s + d)`, so `hypertranscendental_smul_digamma_affine` is
exactly the statement that this single-orbit charge-`m` carrier satisfies no algebraic differential
equation.  These extend the unit-scale `hypertranscendental_smul_gamma_add_const` /
`hypertranscendental_smul_digamma_add_const` to genuine rescaling, using the unconditional
argument-scaling invariance of hypertranscendence.
-/

namespace GaloisForLFunctions

/-- **A nonzero multiple of a rescaled shifted Gamma factor is hypertranscendental.**  `a·Γ(c·s + d)`
(`a ≠ 0`, `c ≠ 0`) — the single common-scale Gamma orbit factor with leading coefficient, at genuine
scale. -/
theorem hypertranscendental_smul_gamma_affine {a c d : ℂ} (ha : a ≠ 0) (hc : c ≠ 0) :
    Hypertranscendental (fun s => a * Complex.Gamma (c * s + d)) := by
  rw [hypertranscendental_const_mul_iff ha]
  exact hypertranscendental_gamma_affine hc d

/-- **A nonzero rescaled single-orbit digamma carrier is hypertranscendental.**  `a·ψ(c·s + d)`
(`a ≠ 0`, `c ≠ 0`) is the logarithmic-derivative carrier `G'/G` of a single common-scale Gamma orbit
factor `Γ(c·s + d)^m` (with `a = m·c`, charge `m ≠ 0`), at genuine scale — the `d = 1`, single-orbit,
nonzero-charge case of the hypertranscendental direction of the dichotomy. -/
theorem hypertranscendental_smul_digamma_affine {a c d : ℂ} (ha : a ≠ 0) (hc : c ≠ 0) :
    Hypertranscendental (fun s => a * Complex.digamma (c * s + d)) := by
  rw [hypertranscendental_const_mul_iff ha]
  exact hypertranscendental_digamma_affine hc d

end GaloisForLFunctions
