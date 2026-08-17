import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Context anomaly rank law

A positive `k`-context principal block spans a `k d`-dimensional nonnegative sector.  Any strictly
negative sector meets it only at zero, so the negative sector fits in the complementary
`(n-k)d` dimensions.  This proves the anomaly-rank mechanism without eigenvalue ordering or
numerical diagonalization.
-/

open Matrix
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

/-- Intrinsic data needed to count negative modes of an `n`-context, `d`-internal-dimensional
Hermitian kernel after one `k`-context sector has been certified nonnegative.  The context count
`k` is carried as `Fin (n+1)`, so `k ≤ n` is intrinsic. -/
structure ContextAnomalyRankDatum (n d : ℕ) where
  observedContexts : Fin (n + 1)
  kernel : Matrix (Fin (n * d)) (Fin (n * d)) ℂ
  nonnegativeSector : Submodule ℂ (Fin (n * d) → ℂ)
  negativeSector : Submodule ℂ (Fin (n * d) → ℂ)
  nonnegativeSector_finrank :
    Module.finrank ℂ nonnegativeSector = observedContexts * d
  nonnegative_on_sector : ∀ x ∈ nonnegativeSector,
    0 ≤ (star x ⬝ᵥ kernel.mulVec x).re
  negative_on_sector : ∀ x ∈ negativeSector, x ≠ 0 →
    (star x ⬝ᵥ kernel.mulVec x).re < 0

/-- An `m`-dimensional nonnegative sector leaves room for at most ambient-dimension minus `m`
negative directions. -/
theorem complexNegativeSector_finrank_add_nonnegativeSector_le
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (q : V → ℝ) (P N : Submodule ℂ V)
    (hP : ∀ x ∈ P, 0 ≤ q x)
    (hN : ∀ x ∈ N, x ≠ 0 → q x < 0) :
    Module.finrank ℂ N + Module.finrank ℂ P ≤ Module.finrank ℂ V := by
  have hdisj : Disjoint N P := by
    rw [disjoint_iff]
    refine Submodule.eq_bot_iff _ |>.mpr fun x hx => ?_
    by_contra hx0
    have hneg := hN x hx.1 hx0
    have hnonneg := hP x hx.2
    linarith
  have hsup : Module.finrank ℂ (N ⊔ P : Submodule ℂ V) ≤ Module.finrank ℂ V :=
    Submodule.finrank_le _
  have hadd : Module.finrank ℂ N + Module.finrank ℂ P =
      Module.finrank ℂ (N ⊔ P : Submodule ℂ V) := by
    rw [← Submodule.finrank_sup_add_finrank_inf_eq N P, disjoint_iff.mp hdisj]
    simp
  rwa [hadd]

/-- Exact anomaly-rank law.  If a `k d`-dimensional sector is nonnegative, every strictly negative
sector has dimension at most `(n-k)d`.  All admissibility information is carried by `D`; the
theorem has no external premises. -/
theorem ContextAnomalyRankDatum.negativeSector_finrank_le
    {n d : ℕ} (D : ContextAnomalyRankDatum n d) :
    Module.finrank ℂ D.negativeSector ≤ (n - D.observedContexts) * d := by
  have h := complexNegativeSector_finrank_add_nonnegativeSector_le
    (fun x => (star x ⬝ᵥ D.kernel.mulVec x).re)
    D.nonnegativeSector D.negativeSector
    D.nonnegative_on_sector D.negative_on_sector
  rw [D.nonnegativeSector_finrank, Module.finrank_fin_fun ℂ] at h
  rw [Nat.sub_mul]
  exact Nat.le_sub_of_add_le h

end GaloisForLFunctions.HTGeometry
