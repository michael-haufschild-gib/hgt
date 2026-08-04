import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The arithmetic three-term complex in the topological ambient

The arithmetic coefficient takes values in topological modules and its differentials are
continuous, so the three-term complex it totalizes to lives in the category of topological modules
over the reals, where kernels and cokernels — and hence homology — exist.  The complex has no terms
above degree two, so its homology vanishes there; in the surviving degrees the topological kernel of
the residue is the fibre and the topological cokernel of the residue is the endpoint.

* `deningerTopThreeTermCochain` : the totalization in the topological ambient.
* `deningerTopThreeTermCochain_isZero_homology` : vanishing above degree two.
* `deningerTopResidueFibre`, `deningerTopResidueFibre_isLimit` : the fibre as a topological kernel.
* `deningerTopResidueEndpoint`, `deningerTopResidueEndpoint_isColimit` : the topological endpoint.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

section TopThreeTerm

variable {A0 A1 A2 : Type}
variable [AddCommGroup A0] [Module ℝ A0] [TopologicalSpace A0] [IsTopologicalAddGroup A0]
  [ContinuousSMul ℝ A0]
variable [AddCommGroup A1] [Module ℝ A1] [TopologicalSpace A1] [IsTopologicalAddGroup A1]
  [ContinuousSMul ℝ A1]
variable [AddCommGroup A2] [Module ℝ A2] [TopologicalSpace A2] [IsTopologicalAddGroup A2]
  [ContinuousSMul ℝ A2]

/-- The zero object of the topological ambient. -/
noncomputable abbrev deningerTopZero : TopModuleCat.{0} ℝ := TopModuleCat.of ℝ PUnit

theorem deningerTopZero_isZero : IsZero deningerTopZero := by
  refine ⟨fun Y => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun Y => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · refine ConcreteCategory.hom_ext_iff.2 (fun x => ?_)
    rw [show x = 0 from Subsingleton.elim _ _]
    simp
  · refine ConcreteCategory.hom_ext_iff.2 (fun x => ?_)
    exact Subsingleton.elim _ _

/-- **The arithmetic three-term complex in the topological ambient.** -/
noncomputable def deningerTopThreeTermCochain (d0 : A0 →L[ℝ] A1) (d1 : A1 →L[ℝ] A2)
    (h : d1.comp d0 = 0) : CochainComplex (TopModuleCat.{0} ℝ) ℕ :=
  CochainComplex.mk (TopModuleCat.of ℝ A0) (TopModuleCat.of ℝ A1) (TopModuleCat.of ℝ A2)
    (TopModuleCat.ofHom d0) (TopModuleCat.ofHom d1)
    (by
      refine ConcreteCategory.hom_ext_iff.2 (fun x => ?_)
      exact congrArg (fun φ : A0 →L[ℝ] A2 => φ x) h)
    (fun _ => ⟨deningerTopZero, 0, by simp⟩)

theorem deningerTopThreeTermCochain_X_zero (d0 : A0 →L[ℝ] A1) (d1 : A1 →L[ℝ] A2)
    (h : d1.comp d0 = 0) :
    (deningerTopThreeTermCochain d0 d1 h).X 0 = TopModuleCat.of ℝ A0 := rfl

theorem deningerTopThreeTermCochain_X_one (d0 : A0 →L[ℝ] A1) (d1 : A1 →L[ℝ] A2)
    (h : d1.comp d0 = 0) :
    (deningerTopThreeTermCochain d0 d1 h).X 1 = TopModuleCat.of ℝ A1 := rfl

theorem deningerTopThreeTermCochain_X_two (d0 : A0 →L[ℝ] A1) (d1 : A1 →L[ℝ] A2)
    (h : d1.comp d0 = 0) :
    (deningerTopThreeTermCochain d0 d1 h).X 2 = TopModuleCat.of ℝ A2 := rfl

/-- **The complex has no terms above degree two.** -/
theorem deningerTopThreeTermCochain_X_add_three (d0 : A0 →L[ℝ] A1) (d1 : A1 →L[ℝ] A2)
    (h : d1.comp d0 = 0) (k : ℕ) :
    (deningerTopThreeTermCochain d0 d1 h).X (k + 3) = deningerTopZero := rfl

theorem deningerTopThreeTermCochain_isZero_X (d0 : A0 →L[ℝ] A1) (d1 : A1 →L[ℝ] A2)
    (h : d1.comp d0 = 0) {n : ℕ} (hn : 3 ≤ n) :
    IsZero ((deningerTopThreeTermCochain d0 d1 h).X n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [deningerTopThreeTermCochain_X_add_three]
  exact deningerTopZero_isZero

/-- **Arithmetic cohomology in the topological ambient vanishes outside degrees `0, 1, 2`.** -/
theorem deningerTopThreeTermCochain_isZero_homology (d0 : A0 →L[ℝ] A1) (d1 : A1 →L[ℝ] A2)
    (h : d1.comp d0 = 0) {n : ℕ} (hn : 3 ≤ n) :
    IsZero ((deningerTopThreeTermCochain d0 d1 h).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ ((deningerTopThreeTermCochain d0 d1 h).sc n)
    (deningerTopThreeTermCochain_isZero_X d0 d1 h hn)

theorem deningerTopThreeTermCochain_d_zero_one (d0 : A0 →L[ℝ] A1) (d1 : A1 →L[ℝ] A2)
    (h : d1.comp d0 = 0) :
    (deningerTopThreeTermCochain d0 d1 h).d 0 1 = TopModuleCat.ofHom d0 :=
  CochainComplex.mk_d_1_0 _ _ _ _ _ _ _

theorem deningerTopThreeTermCochain_d_one_two (d0 : A0 →L[ℝ] A1) (d1 : A1 →L[ℝ] A2)
    (h : d1.comp d0 = 0) :
    (deningerTopThreeTermCochain d0 d1 h).d 1 2 = TopModuleCat.ofHom d1 :=
  CochainComplex.mk_d_2_0 _ _ _ _ _ _ _

end TopThreeTerm

section TopFibre

variable {G D : TopModuleCat.{0} ℝ}

/-- **The fibre of a continuous residue morphism**: the topological kernel. -/
noncomputable abbrev deningerTopResidueFibre (r : G ⟶ D) : TopModuleCat.{0} ℝ :=
  TopModuleCat.ker r

/-- **The fibre is a kernel**: it has the universal property of the kernel of the residue. -/
noncomputable def deningerTopResidueFibre_isLimit (r : G ⟶ D) :
    IsLimit (KernelFork.ofι (TopModuleCat.kerι r) (TopModuleCat.kerι_comp r)) :=
  TopModuleCat.isLimitKer r

/-- **The topological endpoint of a continuous residue morphism**: the topological cokernel. -/
noncomputable abbrev deningerTopResidueEndpoint (r : G ⟶ D) : TopModuleCat.{0} ℝ :=
  TopModuleCat.coker r

/-- **The endpoint is a cokernel.** -/
noncomputable def deningerTopResidueEndpoint_isColimit (r : G ⟶ D) :
    IsColimit (CokernelCofork.ofπ (TopModuleCat.cokerπ r) (TopModuleCat.comp_cokerπ r)) :=
  TopModuleCat.isColimitCoker r

end TopFibre

end RHTower

namespace RHTower

open CategoryTheory CategoryTheory.Limits

section Strictness

variable {D : Type} [AddCommGroup D] [Module ℝ D] [TopologicalSpace D] [IsTopologicalAddGroup D]

omit [IsTopologicalAddGroup D] in
/-- **A Hausdorff quotient forces a closed image**: if the quotient of a topological module by a
submodule is separated, that submodule is closed.  For the arithmetic residue this says that the
endpoint is separated only when the boundary is strict. -/
theorem deningerQuotient_isClosed_of_t2 (S : Submodule ℝ D) [T2Space (D ⧸ S)] :
    IsClosed ((S : Set D)) := by
  have hpre : (S : Set D) = (fun x : D => (Submodule.Quotient.mk x : D ⧸ S)) ⁻¹' {0} := by
    ext x
    simp [Submodule.Quotient.mk_eq_zero]
  have h0 : IsClosed ({(0 : D ⧸ S)} : Set (D ⧸ S)) := isClosed_singleton
  rw [hpre]
  exact h0.preimage continuous_quot_mk

/-- **A closed image gives a Hausdorff quotient.** -/
theorem deningerQuotient_t2_of_isClosed (S : Submodule ℝ D) (h : IsClosed ((S : Set D))) :
    T2Space (D ⧸ S) := by
  exact instT2SpaceOfR1SpaceOfT0Space

/-- **Strictness of the boundary is exactly separatedness of the endpoint.** -/
theorem deningerQuotient_t2_iff_isClosed (S : Submodule ℝ D) :
    Nonempty (T2Space (D ⧸ S)) ↔ IsClosed ((S : Set D)) := by
  constructor
  · rintro ⟨h⟩
    haveI := h
    exact deningerQuotient_isClosed_of_t2 S
  · intro h
    exact ⟨deningerQuotient_t2_of_isClosed S h⟩

end Strictness

end RHTower
