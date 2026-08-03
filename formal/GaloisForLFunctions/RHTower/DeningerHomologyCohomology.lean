import GaloisForLFunctions.RHTower.DeningerKerRangeCongr

/-!
# Vanishing homology forces vanishing cohomology, for trivial coefficients over a field

Over a field the cochain complex computing group cohomology with trivial coefficients is the dual
of the chain complex computing group homology: degreewise the dual of finitely supported functions
on tuples is all functions on tuples, and under that identification the two differentials
correspond.  Dualizing preserves exactness in the middle, so a degree in which the chain complex is
exact is a degree in which the cochain complex is exact.  In positive degrees this says that group
homology vanishing forces group cohomology vanishing.

* `deningerIsZero_cohomology_of_homology` : the transfer.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

/-- **Vanishing homology forces vanishing cohomology** in positive degrees, for trivial
coefficients over a field, the cochain complex being the dual of the chain complex. -/
theorem deningerIsZero_cohomology_of_homology (k G : Type u) [Field k] [Group G] (n : ℕ)
    (h : IsZero (groupHomology (Rep.trivial k G k) (n + 1))) :
    IsZero (groupCohomology (Rep.trivial k G k) (n + 1)) := by
  have hzero : IsZero
      ((groupHomology.inhomogeneousChains (Rep.trivial k G k)).homology (n + 1)) := h
  have hEx : (groupHomology.inhomogeneousChains (Rep.trivial k G k)).ExactAt (n + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hzero
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
  have hEx' : LinearMap.ker (groupHomology.inhomogeneousChains.d (Rep.trivial k G k) n).hom =
      LinearMap.range (groupHomology.inhomogeneousChains.d (Rep.trivial k G k) (n + 1)).hom := by
    rw [← groupHomology.inhomogeneousChains.d_def, ← groupHomology.inhomogeneousChains.d_def]
    exact hEx.symm
  have hdual := deningerExact_dualMap
    (groupHomology.inhomogeneousChains.d (Rep.trivial k G k) (n + 1)).hom
    (groupHomology.inhomogeneousChains.d (Rep.trivial k G k) n).hom hEx'
  have hco : LinearMap.ker (inhomogeneousCochains.d (Rep.trivial k G k) (n + 1)).hom =
      LinearMap.range (inhomogeneousCochains.d (Rep.trivial k G k) n).hom :=
    deningerKer_eq_range_congr _ _ _ _
      (deningerFinsuppDual k (Fin n → G)) (deningerFinsuppDual k (Fin (n + 1) → G))
      (deningerFinsuppDual k (Fin (n + 1 + 1) → G))
      (deningerCochain_d_dual_map k G n) (deningerCochain_d_dual_map k G (n + 1)) hdual
  show IsZero ((groupCohomology.inhomogeneousCochains (Rep.trivial k G k)).homology (n + 1))
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 ?_
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  have hgoal : LinearMap.range
        ((groupCohomology.inhomogeneousCochains (Rep.trivial k G k)).d n (n + 1)).hom =
      LinearMap.ker
        ((groupCohomology.inhomogeneousCochains (Rep.trivial k G k)).d (n + 1) (n + 1 + 1)).hom := by
    rw [groupCohomology.inhomogeneousCochains.d_def, groupCohomology.inhomogeneousCochains.d_def]
    exact hco.symm
  exact hgoal

end RHTower
