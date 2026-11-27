import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.DegreeZeroCechSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ProjectiveLineBundleCechModel
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleCechBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalBasisChartCoordinates
import Mathlib.LinearAlgebra.Dimension.Finite

/-! The scalar-linear degree-zero Čech comparison gives finite global sections on a
projective scheme over a Noetherian base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite HTGeometry TopologicalSpace
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi UpperTheory.Cb

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The equivalence between global sections and the kernel of the first Čech differential
is linear over the base. -/
def globalSectionsLinearEquivKernel (F : X.Modules)
    {ι : Type} [DecidableEq ι] [LinearOrder ι] (U : ι → X.Opens) (hc : ⊤ ≤ ⨆ i, U i) :
    letI := sectionBaseModule f F ⊤
    Γ(F, ⊤) ≃ₗ[R] LinearMap.ker ((cech f F U).d 0 1).hom := by
  letI := sectionBaseModule f F ⊤
  let E := globalSectionsEquivKernel f F U hc
  have he (x : Γ(F, ⊤)) (s : Finset ι) (hs : s.card ≠ 1) : (E x).1.1 s = 0 :=
    (E x).1.2 s hs
  refine { E with map_add' := ?_, map_smul' := ?_ }
  · intro x y
    apply Subtype.ext
    apply Subtype.ext
    funext s
    change (E (x + y)).1.1 s = (E x).1.1 s + (E y).1.1 s
    by_cases hs : s.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
      simp only [E, globalSectionsEquivKernel_singleton, map_add] <;> rfl
    · rw [he _ s hs, he _ s hs, he _ s hs, add_zero]
  · intro r x
    apply Subtype.ext
    apply Subtype.ext
    funext s
    letI := sectionDatumModule f F U s
    change (E (r • x)).1.1 s = r • (E x).1.1 s
    by_cases hs : s.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
      simp only [E, globalSectionsEquivKernel_singleton]
      let V := coverInter ⊤ U ({i} : Finset ι)
      let iV : V ⟶ (⊤ : X.Opens) := homOfLE le_top
      letI := sectionAlgebra f (⊤ : X.Opens)
      letI := sectionAlgebra f V
      change F.presheaf.map iV.op ((algebraMap R Γ(X, ⊤) r) • x) =
        (algebraMap R Γ(X, V) r) • F.presheaf.map iV.op x
      rw [F.map_smul]
      exact congrArg (fun z : Γ(X, V) => z • F.presheaf.map iV.op x) ((sectionRes f iV).commutes r)
    · rw [he _ s hs, he _ s hs, smul_zero]

/-- Global sections of a line bundle on a projective scheme are finite over its
Noetherian coefficient ring. -/
theorem moduleFinite_globalSections [IsNoetherianRing R] (hf : IsProjOver f)
    {L : LB X} (hL : L.IsLB) :
    letI := sectionBaseModule f (toMod L) ⊤
    Module.Finite R Γ(toMod L, ⊤) := by
  letI := sectionBaseModule f (toMod L) ⊤
  obtain ⟨n, i, hi, hif⟩ := hf
  letI := hi
  let U := PSpace.coordinateOpen R n
  let V (j : Fin (n + 1)) := i ⁻¹ᵁ U j
  have hc : ⊤ ≤ ⨆ j, V j := (i.iSup_preimage_eq_top (PSpace.iSup_coordinateOpen R n)).ge
  have ha (s : Finset (Fin (n + 1))) (hs : s.Nonempty) : IsAffineOpen (coverInter ⊤ V s) :=
    (coverInter_pull (π := i) U s).symm ▸ (PSpace.isAffineOpen_coordinateInter R n hs).preimage i
  let C := cech f (toMod L) V
  haveI : Module.Finite R (C.homology 0) := cech_homology_finite f hL V hc ha ⟨n, i, hi, hif⟩ 0
  let H := LinearMap.ker (C.d 0 1).hom
  have h := GlobalTheory.finite_ker_quotient_of_finite_homology C 0 0 1 (by simp) (by simp)
  have hd : C.d 0 0 = 0 := C.shape 0 0 (by simp [ComplexShape.up])
  have hbot : (LinearMap.range (C.d 0 0).hom).comap H.subtype = ⊥ := by
    rw [hd]
    change (LinearMap.range (0 : C.X 0 →ₗ[R] C.X 0)).comap H.subtype = ⊥
    rw [LinearMap.range_zero]
    exact LinearMap.ker_eq_bot.mpr H.injective_subtype
  rw [hbot] at h
  letI : Module.Finite R (H ⧸ (⊥ : Submodule R H)) := h
  let e : H ⧸ (⊥ : Submodule R H) →ₗ[R] H := (⊥ : Submodule R H).liftQ (LinearMap.id) (by simp)
  haveI : Module.Finite R H := Module.Finite.of_surjective e fun x =>
    ⟨(⊥ : Submodule R H).mkQ x, rfl⟩
  exact Module.Finite.of_surjective (globalSectionsLinearEquivKernel f (toMod L) V hc).symm.toLinearMap
    (globalSectionsLinearEquivKernel f (toMod L) V hc).symm.surjective

section Field

variable {K : Type} [Field K] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of K)) {L : LB Y}

/-- In any sufficiently long list of global sections there is a nonzero relation that
holds in every bundle chart. -/
theorem exists_chartwise_linear_dependence (hg : IsProjOver g) (hL : L.IsLB) :
    ∃ n : ℕ, ∀ s : Fin n → L.Sec, ∃ c : Fin n → K, c ≠ 0 ∧
      ∀ i, letI := sectionAlgebra g (L.U i)
        ∑ k, algebraMap K Γ(Y, L.U i) (c k) * (s k).f i = 0 := by
  classical
  let F := Γ(toMod L, ⊤)
  letI : Module K F := sectionBaseModule g (toMod L) ⊤
  letI : Module.Finite K F := moduleFinite_globalSections g hg hL
  let n := Module.finrank K F + 1
  refine ⟨n, fun s => ?_⟩
  let v (k : Fin n) : F := globalCoordinates.symm (s k)
  have h : ¬ LinearIndependent K v := by
    intro hv
    have hcard := hv.fintype_card_le_finrank
    simp only [Fintype.card_fin, n] at hcard
    exact Nat.not_succ_le_self _ hcard
  rw [Fintype.linearIndependent_iff] at h
  push Not at h
  obtain ⟨c, hc, k, hk⟩ := h
  refine ⟨c, fun hz => hk (congrFun hz k), fun i => ?_⟩
  letI := sectionAlgebra g (L.U i)
  let ρ := globalChartLinearMap (L := L) g i
  have hρ (k : Fin n) : ρ (v k) = (s k).f i := by
    change (globalCoordinates (globalCoordinates.symm (s k))).f i = _
    rw [Equiv.apply_symm_apply]
  have e := congrArg ρ hc
  simpa only [map_sum, map_smul, map_zero, hρ, Algebra.smul_def] using e

end Field

end GlobalTheory.LineBundleSections
