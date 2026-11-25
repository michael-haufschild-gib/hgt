import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ProjectiveLineBundleCechModel
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleCechBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FirstTwoDegreesOfQuasiIso
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ProjectiveCochainMatrices
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.DegreeZeroCechSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineCechExactness

/-! A three-term matrix model for sections of a line bundle after arbitrary affine base change. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HTGeometry
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi TensorProduct
open UpperTheory.Cb
open scoped ChangeOfRings

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X)

/-- The matrix kernel computes global sections with specified coordinates on a cover.
Exactness at the middle matrix follows from vanishing of first cohomology. -/
structure PerfectSections where
  a : ℕ
  b : ℕ
  c : ℕ
  d₀ : Matrix (Fin b) (Fin a) R
  d₁ : Matrix (Fin c) (Fin b) R
  comp : d₁ * d₀ = 0
  I : Type
  W : I → X.Opens
  chart : I → L.ι
  le_chart : ∀ i, W i ≤ L.U (chart i)
  cover : ⨆ i, W i = ⊤
  coeff : Fin a → ∀ i, Γ(X, W i)
  compare : ∀ (S : Type) [CommRing S] (α : R →+* S) (Y : Scheme.{0})
    (π : Y ⟶ X) (g : Y ⟶ Spec (CommRingCat.of S)),
    IsPullback π g f (Spec.map (CommRingCat.ofHom α)) →
      (∃ e : {v : Fin a → S // (d₀.map α).mulVec v = 0} ≃ Γ(toMod (L.pull π), ⊤),
        ∀ v i,
          letI := sectionAlgebra g (π ⁻¹ᵁ W i)
          resG Y (le_inf le_top ((π.preimage_mono (le_chart i)).trans
            (pull_chart L π (chart i)).ge)) (coord (e v) (fun _ => chart i)) =
            ∑ k, algebraMap S Γ(Y, π ⁻¹ᵁ W i) (v.1 k) * π.app (W i) (coeff k i)) ∧
      (Subsingleton (CohomologyOn (toMod (L.pull π)) ⊤ 1) →
        ∀ w : Fin b → S, (d₁.map α).mulVec w = 0 → ∃ v, (d₀.map α).mulVec v = w)

variable {L} (hL : L.IsLB)
  {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (U : ι → X.Opens)
  (hcov : ⊤ ≤ ⨆ i, U i) (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (coverInter ⊤ U s))

include hL hcov hU

/-- A perfect Čech model valid after every scalar extension gives the section matrices. -/
theorem nonempty_perfectSections_of_cech
    {K : CochainComplex (ModuleCat R) ℕ} (φ : K ⟶ cech f (toMod L) U)
    (hK : ∀ n, Module.Finite R (K.X n) ∧ Module.Projective R (K.X n))
    (hφ : ∀ (S : Type) [CommRing S] [Algebra R S],
      QuasiIso (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (ComplexShape.up ℕ)).map φ)) :
    Nonempty (PerfectSections f L) := by
  haveI (n : ℕ) : Module.Finite R (K.X n) := (hK n).1
  haveI (n : ℕ) : Module.Projective R (K.X n) := (hK n).2
  obtain ⟨a, b, c, d₀, d₁, u, hcomp, hm⟩ := GlobalTheory.exists_matrices_of_projective_complex
    R (K.X 0) (K.X 1) (K.X 2) (K.d 0 1).hom (K.d 1 2).hom
    (LinearMap.ext fun x => GlobalTheory.cochain_d_d_apply K 0 1 2 x)
  let W (i : ι × L.ι) := coverInter ⊤ U {i.1} ⊓ L.U i.2
  let coeff (k : Fin a) (i : ι × L.ι) : Γ(X, W i) :=
    coord (((φ.f 0).hom (u k)).1 {i.1}) i.2
  have hW : iSup W = ⊤ := top_unique fun x _ => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov (Set.mem_univ x))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ j, L.U j by rw [hL.cover]; trivial)
    refine Opens.mem_iSup.mpr ⟨(i, j), ?_⟩
    exact ⟨mem_coverInter.mpr ⟨trivial, fun k hk => by simpa [Finset.mem_singleton.mp hk] using hi⟩, hj⟩
  refine ⟨{
    a := a
    b := b
    c := c
    d₀ := d₀
    d₁ := d₁
    comp := hcomp
    I := ι × L.ι
    W := W
    chart := Prod.snd
    le_chart := fun _ => inf_le_right
    cover := hW
    coeff := coeff
    compare := ?_ }⟩
  intro S _ α Y π g H
  letI : Algebra R S := α.toAlgebra
  let V (i : ι) := π ⁻¹ᵁ U i
  let G := toMod (L.pull π)
  let T := (ModuleCat.extendScalars α).mapHomologicalComplex (ComplexShape.up ℕ)
  let e := cechBaseChangeIso L U hL α H hU
  let ψ : T.obj K ⟶ cech g G V := T.map φ ≫ e.hom
  haveI : QuasiIso (T.map φ) := hφ S
  haveI : QuasiIso ψ := inferInstanceAs (QuasiIso (T.map φ ≫ e.hom))
  have hV : ⊤ ≤ ⨆ i, V i := by
    change ⊤ ≤ ⨆ i, π ⁻¹ᵁ U i
    rw [← π.preimage_iSup, top_le_iff.mp hcov, π.preimage_top]
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hAffine (s : Finset ι) (hs : s.Nonempty) : IsAffineOpen (coverInter ⊤ V s) :=
    (coverInter_pull (π := π) U s).symm ▸ (hU s hs).preimage π
  let q := GlobalTheory.bijOn_ker_and_exact_of_quasiIso ψ
  let Q : Set.BijOn (fun v : Fin a → S => (ψ.f 0).hom (∑ k, v k ⊗ₜ[R] u k))
      {v | (d₀.map α).mulVec v = 0} (LinearMap.ker ((cech g G V).d 0 1).hom) :=
    q.1.comp (hm S).1
  let A := globalSectionsEquivKernel g G V hV
  let E := (Q.equiv _).trans A.symm
  refine ⟨⟨E, ?_⟩, ?_⟩
  · intro v i
    let j : (L.pull π).ι := fun _ => i.2
    let s : Finset ι := {i.1}
    let J := coverInter ⊤ V s
    let J₀ := coverInter ⊤ U s
    have hJ : J = π ⁻¹ᵁ J₀ := coverInter_pull (π := π) U s
    let w := π ⁻¹ᵁ W i
    have h₁ : w ≤ J := (π.preimage_mono inf_le_left).trans hJ.ge
    have h₂ : w ≤ (L.pull π).U j := (π.preimage_mono inf_le_right).trans (pull_chart L π i.2).ge
    let h := le_inf h₁ h₂
    letI := sectionAlgebra g w
    letI := sectionAlgebra g J
    have he : (A (E v)).1.1 s = ((ψ.f 0).hom (∑ k, v.1 k ⊗ₜ[R] u k)).1 s := by
      have eh := A.apply_symm_apply (Q.equiv _ v)
      exact congrArg (fun z : LinearMap.ker ((cech g G V).d 0 1).hom => z.1.1 s) eh
    let det : (cech g G V).X 0 →+ Γ(Y, w) :=
      { toFun := fun x => resG Y h (coord (x.1 s) j)
        map_zero' := map_zero _
        map_add' := fun x y => map_add _ _ _ }
    have hdet : resG Y (le_inf le_top h₂) (coord (E v) j) =
        det ((ψ.f 0).hom (∑ k, v.1 k ⊗ₜ[R] u k)) := by
      change _ = resG Y h (coord (((ψ.f 0).hom _).1 s) j)
      rw [← he]
      change _ = resG Y h (coord ((globalSectionsEquivKernel g G V hV (E v)).1.1 {i.1}) j)
      rw [globalSectionsEquivKernel_singleton, coord_map, resG_resG]
    have hterm (k : Fin a) :
        det ((ψ.f 0).hom (v.1 k ⊗ₜ[R] u k)) =
          algebraMap S Γ(Y, w) (v.1 k) * π.app (W i) (coeff k i) := by
      let x := (φ.f 0).hom (u k)
      have hp : ((ψ.f 0).hom (v.1 k ⊗ₜ[R] u k)).1 s =
          algebraMap S Γ(Y, J) (v.1 k) • pullSection (ChartPull.pull L π) hJ.le (x.1 s) := by
        change ((e.hom.f 0) ((ModuleCat.extendScalars α).map (φ.f 0)
          (v.1 k ⊗ₜ[R,α] u k))).1 s = _
        rw [ModuleCat.ExtendScalars.map_tmul]
        exact cechBaseChangeIso_hom_f_tmul L U hL α H hU 0 (v.1 k) x s
      change resG Y h (coord (((ψ.f 0).hom (_ ⊗ₜ[R] _)).1 s) j) = _
      rw [hp, coord_smul, map_mul, resG_resG, coord_pullSection, resG_appLE]
      rw [show resG Y h₁ (algebraMap S Γ(Y, J) (v.1 k)) = algebraMap S Γ(Y, w) (v.1 k) from
        (sectionRes g (homOfLE h₁)).commutes (v.1 k), Scheme.Hom.app_eq_appLE]
      rfl
    change resG Y (le_inf le_top h₂) (coord (E v) j) = _
    rw [hdet, map_sum, map_sum]
    exact Finset.sum_congr rfl fun k _ => hterm k
  · intro hz
    letI : G.IsQuasicoherent := isQuasicoherent_toMod (hL.pull π)
    exact (hm S).2 (q.2 (cech_exact_of_H1_zero g G V hV hAffine hz))

/-- The perfect Čech model gives a finite free presentation in degrees zero through two. -/
theorem nonempty_perfectSections [IsNoetherianRing R] [Flat f] (hf : IsProjOver f) :
    Nonempty (PerfectSections f L) := by
  obtain ⟨K, φ, _, hK, _, hφ⟩ := exists_perfect_cech f hL U hcov hU hf
  exact nonempty_perfectSections_of_cech f hL U hcov hU φ hK hφ

omit hcov hU in
/-- A closed embedding supplies the affine cover by pulling back the coordinate charts. -/
theorem nonempty_perfectSections_of_projective [IsNoetherianRing R] [Flat f] (hf : IsProjOver f) :
    Nonempty (PerfectSections f L) := by
  obtain ⟨N, i, hi, he⟩ := hf
  letI := hi
  let U₀ := PSpace.coordinateOpen R N
  let V₀ (j : Fin (N + 1)) := i ⁻¹ᵁ U₀ j
  have hcov₀ : ⊤ ≤ ⨆ j, V₀ j := (i.iSup_preimage_eq_top (PSpace.iSup_coordinateOpen R N)).ge
  have ha₀ (s : Finset (Fin (N + 1))) (hs : s.Nonempty) : IsAffineOpen (coverInter ⊤ V₀ s) :=
    (coverInter_pull (π := i) U₀ s).symm ▸ (PSpace.isAffineOpen_coordinateInter R N hs).preimage i
  exact nonempty_perfectSections f hL V₀ hcov₀ ha₀ ⟨N, i, hi, he⟩

end GlobalTheory.LineBundleSections
