import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveSpaceDimension
import Mathlib.GroupTheory.CosetCover

/-! Over an infinite field, a prescribed finite set of projective points
lies in one homogeneous basic open of any prescribed degree. -/

noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace UpperTheory.Cb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem PSpace.exists_form_nonvanishing {K : Type*} [Field K] [Infinite K] (N d : ℕ)
    (S : Finset (PSpace K N)) :
    ∃ f : MvPolynomial (Fin (N + 1)) K, f.IsHomogeneous d ∧
      ∀ x ∈ S, x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K
  let L (x : S) : Submodule K (𝒜 d) :=
    (x.1.asHomogeneousIdeal.toIdeal.restrictScalars K).comap (𝒜 d).subtype
  have hproper (x : S) : L x ≠ ⊤ := by
    have hx : x.1 ∈ ⨆ i, PSpace.coordinateOpen K N i := by
      rw [PSpace.iSup_coordinateOpen]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    change MvPolynomial.X i ∉ x.1.asHomogeneousIdeal at hi
    have hXi : MvPolynomial.X i ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X K i
    let z : 𝒜 d := ⟨MvPolynomial.X i ^ d, by
      simpa only [nsmul_eq_mul, mul_one] using SetLike.pow_mem_graded d hXi⟩
    intro htop
    have hz : z ∈ L x := htop.symm ▸ Submodule.mem_top
    change MvPolynomial.X i ^ d ∈ x.1.asHomogeneousIdeal.toIdeal at hz
    exact hi (x.1.isPrime.mem_of_pow_mem d hz)
  have hne : (⋃ x : S, (L x : Set (𝒜 d))) ≠ Set.univ := by
    intro h
    obtain ⟨x, hx⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ h
    exact hproper x hx
  obtain ⟨f, hf⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨f.1, f.2, fun x hx => ?_⟩
  intro h
  exact hf (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, h⟩)

end UpperTheory.Cb
