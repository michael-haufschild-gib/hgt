import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedChartPoints
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverFunctionField

/-! Evaluation on intersecting normalized projective charts. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GaloisForLFunctions.HTGeometry GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} [Algebra K X.functionField]

/-- Evaluation on a smaller open agrees with evaluation on its larger chart. -/
theorem IsAffCover.chartPointEquiv_inclusion {ι : Type} {U : ι → X.Opens}
    {B : Finset ι → Subalgebra K X.functionField} (h : IsAffCover s U B)
    {I J : Finset ι} (hI : I.Nonempty) (hIJ : I ⊆ J)
    (y : X.BaseFieldPointOver K s) (hy : y.hom default ∈ J.inf U) (b : B I) :
    h.chartPointEquiv J (hI.mono hIJ) ⟨y, hy⟩ (Subalgebra.inclusion (h.algebra_le hI hIJ) b) =
      h.chartPointEquiv I hI
        ⟨y, SetLike.le_def.mp (show J.inf U ≤ I.inf U from Finset.inf_mono hIJ) hy⟩ b := by
  obtain ⟨a, rfl⟩ := (h.sectionEquiv I hI).surjective b
  let ρ : J.inf U ⟶ I.inf U := homOfLE (Finset.inf_mono hIJ)
  have hg : Subalgebra.inclusion (h.algebra_le hI hIJ) (h.sectionEquiv I hI a) =
      h.sectionEquiv J (hI.mono hIJ) (sectionRes s ρ a) := by
    apply Subtype.ext
    change (h.sectionEquiv I hI a : X.functionField) =
      (h.sectionEquiv J (hI.mono hIJ) (sectionRes s ρ a) : X.functionField)
    rw [h.sectionEquiv_apply_coe, h.sectionEquiv_apply_coe]
    exact (X.presheaf.germ_res_apply ρ (genericPoint X) (h.ne J) a).symm
  rw [hg, h.chartPointEquiv_eval, h.chartPointEquiv_eval]
  exact pointEval_res y.hom (Finset.inf_mono hIJ) hy a

variable {F : Type} [Field F] [Algebra K F] [Algebra F X.functionField]
  [IsScalarTower K F X.functionField] {d : ℕ} (x : Fin (d + 1) → F)

/-- Any coordinate ratio with its denominator in the index set belongs to
the normalized chart algebra. -/
theorem rB_ratio_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)}
    (hi : i ∈ I) (j : Fin (d + 1)) :
    algebraMap F X.functionField (x j / x i) ∈ rB K X.functionField x I :=
  isIntegral_algebraMap (x := (⟨_, Algebra.subset_adjoin ⟨i, hi, j, rfl⟩⟩ : rA K x I))

/-- The coordinate ratio from chart `i` to chart `j` is nonzero at a
rational point on their intersection. -/
theorem IsAffCover.eval_ratio_ne_zero {U : Fin (d + 1) → X.Opens}
    (h : IsAffCover s U (rB K X.functionField x)) (hx : IsPd K x)
    (i j : Fin (d + 1)) (y : X.BaseFieldPointOver K s)
    (hi : y.hom default ∈ ({i} : Finset (Fin (d + 1))).inf U)
    (hj : y.hom default ∈ ({j} : Finset (Fin (d + 1))).inf U) :
    h.chartPointEquiv {i} (Finset.singleton_nonempty i) ⟨y, hi⟩
      ⟨_, rB_ratio_mem x (Finset.mem_singleton_self i) j⟩ ≠ 0 := by
  let I : Finset (Fin (d + 1)) := {i}
  let J : Finset (Fin (d + 1)) := {i, j}
  have hIJ : I ⊆ J := Finset.singleton_subset_iff.mpr (by simp [J])
  have hI : I.Nonempty := Finset.singleton_nonempty i
  have hJ : J.Nonempty := hI.mono hIJ
  have hy : y.hom default ∈ J.inf U := by
    have hi' : y.hom default ∈ U i := by simpa using hi
    have hj' : y.hom default ∈ U j := by simpa using hj
    simpa [J] using (show y.hom default ∈ U i ⊓ U j from ⟨hi', hj'⟩)
  let a : rB K X.functionField x I := ⟨_, rB_ratio_mem x (Finset.mem_singleton_self i) j⟩
  let b : rB K X.functionField x J := ⟨_, rB_ratio_mem x (i := j) (by simp [J]) i⟩
  let ρ := Subalgebra.inclusion (h.algebra_le hI hIJ)
  have hu : ρ a * b = 1 := by
    apply Subtype.ext
    change algebraMap F X.functionField (x j / x i) * algebraMap F X.functionField (x i / x j) = 1
    rw [← map_mul, ← map_one (algebraMap F X.functionField)]
    congr 1
    field_simp [hx.ne i, hx.ne j]
  let e := h.chartPointEquiv J hJ ⟨y, hy⟩
  have he : e (ρ a) = h.chartPointEquiv I hI ⟨y, hi⟩ a :=
    h.chartPointEquiv_inclusion hI hIJ y hy a
  intro hzero
  have hunit := congrArg e hu
  rw [map_mul, he, hzero, zero_mul, map_one] at hunit
  exact zero_ne_one hunit

end GlobalTheory.PD
