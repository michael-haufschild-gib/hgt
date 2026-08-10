import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Generalized eigenspaces under sign reversal
-/

namespace GaloisForLFunctions.HTGeometry

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Negating an endomorphism and its spectral parameter leaves the generalized eigenspace
unchanged. -/
theorem maxGenEigenspace_neg_neg (f : Module.End R V) (mu : R) :
    (-f).maxGenEigenspace (-mu) = f.maxGenEigenspace mu := by
  ext x
  simp only [Module.End.mem_maxGenEigenspace]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hshift : -f - -mu • (1 : Module.End R V) = -(f - mu • 1) := by
      ext y
      simp only [LinearMap.neg_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        neg_smul]
      abel
    rw [hshift, neg_pow] at hn
    rcases neg_one_pow_eq_or (Module.End R V) n with hcoef | hcoef <;>
      simpa [hcoef] using hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hshift : -f - -mu • (1 : Module.End R V) = -(f - mu • 1) := by
      ext y
      simp only [LinearMap.neg_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        neg_smul]
      abel
    rw [hshift, neg_pow]
    rcases neg_one_pow_eq_or (Module.End R V) n with hcoef | hcoef <;>
      simpa [hcoef] using hn

end GaloisForLFunctions.HTGeometry
