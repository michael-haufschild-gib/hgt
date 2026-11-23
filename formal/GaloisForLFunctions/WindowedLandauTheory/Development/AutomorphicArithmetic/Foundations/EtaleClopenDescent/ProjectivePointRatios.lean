import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveRatios
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineRationalPoints
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveFormAvoidance

/-! Point evaluation on a projective chart detects vanishing of the
numerator, and a prescribed finite set of points admits a common chart. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

open UpperTheory.Cb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of K)} {N : ℕ}

private abbrev Grade := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

theorem affinePointEval_projectiveRatio_eq_zero_iff {d : ℕ} (i : X ⟶ PSpace K N)
    {u v : MvPolynomial (Fin (N + 1)) K}
    (hu : u ∈ Grade (K := K) (N := N) d) (hv : v ∈ Grade (K := K) (N := N) d)
    (z : X.BaseFieldPointOver K s)
    (hz : z.hom default ∈ i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) u) :
    affinePointEval z hz (projectiveRatio i hu hv) = 0 ↔
      z.hom default ∉ i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) v := by
  have hne := pointEval_ne_zero_iff z.hom _ hz (projectiveRatio i hu hv)
  rw [basicOpen_projectiveRatio] at hne
  exact ⟨fun h hv' => (hne.mpr ⟨hz, hv'⟩) h, fun h => by
    by_contra hn
    exact h (hne.mp hn).2⟩

/-- A homogeneous denominator can be chosen to be nonzero at all prescribed
points and at the generic point. -/
theorem exists_form_chart_of_points [Infinite K] [IrreducibleSpace X] (i : X ⟶ PSpace K N)
    (d : ℕ) (S : Finset (X.BaseFieldPointOver K s)) :
    ∃ u : MvPolynomial (Fin (N + 1)) K, u.IsHomogeneous d ∧
      genericPoint X ∈ i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) u ∧
      ∀ z ∈ S, z.hom default ∈ i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) u := by
  classical
  let p (z : X.BaseFieldPointOver K s) := i (z.hom default)
  let T := insert (i (genericPoint X)) (S.image p)
  obtain ⟨u, hu, hz⟩ := PSpace.exists_form_nonvanishing N d T
  refine ⟨u, hu, hz _ (Finset.mem_insert_self _ _), fun z hz' => ?_⟩
  exact hz (p z) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem p hz'))

end GlobalTheory.SchemeCohomology
