import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineJoinedCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.JoinedCechCohomology

/-! Gluing a second cover shifts the cohomology of a supported Čech complex
when the sections on each augmented slice are exact. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace HTGeometry
open HTGeometry.FinsetCechDatum GlobalTheory.WH GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (.of K)) (F : X.Modules)

/-- The Čech complex supported on the indicated intersections. -/
def cechOnSupport {ι : Type} [LinearOrder ι] (U : ι → X.Opens) (P : Set (Finset ι))
    (hP : P.OrdConnected) : CochainComplex (ModuleCat K) ℕ :=
  letI (s : Finset ι) := sectionDatumModule f F U s
  ((sectionDatum F U).truncate (R := K) P hP).linearComplex
    ((sectionDatum F U).truncate_linear P hP (res_base_smul f F U))

theorem cechOnSupport_congr {ι : Type} [LinearOrder ι] (U : ι → X.Opens)
    {P Q : Set (Finset ι)} (hP : P.OrdConnected) (hQ : Q.OrdConnected) (h : P = Q) :
    cechOnSupport f F U P hP = cechOnSupport f F U Q hQ := by
  subst Q
  rfl

/-- The usual Čech cochain terms only use nonempty intersections. -/
def cechOnNonemptyIso {ι : Type} [LinearOrder ι] (U : ι → X.Opens) :
    cechOnSupport f F U (nonemptyIntersections ι) (nonemptyIntersections_ordConnected ι) ≅
      cech f F U := by
  let D := sectionDatum F U
  letI (s : Finset ι) := sectionDatumModule f F U s
  let P := nonemptyIntersections ι
  let hP := nonemptyIntersections_ordConnected ι
  let T := D.truncate (R := K) P hP
  let hD {s t : Finset ι} (h : s ⊆ t) (r : K) (x : D.obj s) :=
    res_base_smul f F U h r x
  let hT {s t : Finset ι} (h : s ⊆ t) (r : K) (x : T.obj s) :=
    D.truncate_linear P hP hD h r x
  let φ : T.Hom D :=
    { app s := (D.supportCoeff (R := K) P s).subtype.toAddMonoidHom
      comm := fun {s t} h x => by
        change D.res h x.1 = (T.res h x).1
        rw [D.truncate_res_value (R := K)]
        by_cases ht : t ∈ P
        · rw [if_pos ht]
        · rw [if_neg ht, x.2 (fun hs => ht (hs.mono h)), map_zero] }
  have hφ (s : Finset ι) (r : K) (x : T.obj s) :
      φ.app s (r • x) = r • φ.app s x := rfl
  have hbij (s : Finset ι) (hs : s.Nonempty) : Function.Bijective (φ.app s) :=
    ⟨Subtype.val_injective, fun x => ⟨⟨x, fun hn => (hn hs).elim⟩, rfl⟩⟩
  let I : T.linearComplex hT ⟶ D.linearComplex hD := linearCochainMap hT hD φ hφ
  have hI : IsIso I := isIso_linearCochainMap hT hD φ hφ hbij
  exact @asIso _ _ _ _ I hI

theorem nonempty_homology_equiv_cechSlice {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    (U : ι → X.Opens) (V : κ → X.Opens)
    (m : Finset κ → Finset ι) (hm : Monotone m) (P : Set (Finset ι))
    (hP : P.OrdConnected) (e : ∀ s, coverInter (⊤ : X.Opens) U (m s) = coverInter ⊤ V s) (n : ℕ) :
    letI (s : Finset ι) := sectionDatumModule f F U s
    let D := sectionDatum F U
    let T := (D.truncate (R := K) P hP).comap m hm
    Nonempty ((cechOnSupport f F V (m ⁻¹' P) (hP.preimage_mono hm)).homology n ≃ₗ[K]
      (T.linearComplex (fun h r x => D.truncate_linear P hP (res_base_smul f F U) (hm h) r x)).homology n) := by
  letI (s : Finset ι) := sectionDatumModule f F U s
  letI (s : Finset κ) := sectionDatumModule f F V s
  let D := sectionDatum F U
  let B := sectionDatum F V
  let B' := B.truncate (R := K) (m ⁻¹' P) (hP.preimage_mono hm)
  let hB {s t : Finset κ} (h : s ⊆ t) (r : K) (x : B'.obj s) :=
    B.truncate_linear (m ⁻¹' P) (hP.preimage_mono hm) (res_base_smul f F V) h r x
  let T := (D.truncate (R := K) P hP).comap m hm
  have hT {s t : Finset κ} (h : s ⊆ t) (r : K) (x : T.obj s) :
      T.res h (r • x) = r • T.res h x :=
    D.truncate_linear P hP (res_base_smul f F U) (hm h) r x
  obtain ⟨φ, hbij, hφ⟩ := exists_slice_hom f F U ⊤ V m hm P hP e
  let I := linearCochainMap hB hT φ hφ
  letI : IsIso I := isIso_linearCochainMap hB hT φ hφ fun s _ => hbij s
  exact ⟨(HomologicalComplex.homologyMapIso (asIso I) n).toLinearEquiv⟩

variable [HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X)] [F.IsQuasicoherent]
  {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ]
  (U : ι → X.Opens) (V : κ → X.Opens)

/-- Appending a right cover shifts supported left cohomology by one. -/
theorem nonempty_homology_equiv_affine_leftJoin (P : Set (Finset ι)) (hP : P.OrdConnected) (h₀ : ∅ ∉ P)
    (hPaff : ∀ I ∈ P, IsAffineOpen (I.inf U))
    (hV : ∀ j W, IsAffineOpen W → IsAffineOpen (V j ⊓ W)) (hcov : ⨆ j, V j = ⊤) (n : ℕ) :
    Nonempty ((cechOnSupport f F U P hP).homology n ≃ₗ[K]
      (cechOnSupport f F (joinedCover U V) (joinedSupport P (nonemptyIntersections κ))
        (joinedSupport_ordConnected hP (nonemptyIntersections_ordConnected κ))).homology (n + 1)) := by
  let E := joinedCover U V
  let D := sectionDatum F E
  letI (s : Finset (ι ⊕ₗ κ)) := sectionDatumModule f F E s
  let Q := (@lft ι κ) ⁻¹' P
  let T := joinedSupport P (nonemptyIntersections κ)
  let hQ : Q.OrdConnected := hP.preimage_mono lft_monotone
  let hS := supportDiff_ordConnected hQ (left_join_upper P)
  let m (I : Finset ι) := uni I (∅ : Finset κ)
  have hm : Monotone m := fun _ _ h => uni_mono h (Finset.Subset.refl _)
  have hp : m ⁻¹' (Q \ T) = P := by
    ext i
    simp [m, Q, T, joinedSupport, nonemptyIntersections]
  obtain ⟨A⟩ := nonempty_homology_equiv_cechSlice f F E U m hm (Q \ T) hS
    (fun I => by simp [E, m, coverInter, inf_joinedCover]) n
  obtain ⟨B⟩ := D.nonempty_homology_equiv_leftJoin_succ (res_base_smul f F E) P hP
    (acyclic_joined_of_affine_left f F U V P hP h₀ hPaff hV hcov) n
  rw [← cechOnSupport_congr f F U (hS.preimage_mono hm) hP hp]
  exact ⟨A.trans B⟩

/-- Prepending a left cover shifts supported right cohomology by one. -/
theorem nonempty_homology_equiv_affine_rightJoin (P : Set (Finset κ)) (hP : P.OrdConnected) (h₀ : ∅ ∉ P)
    (hPaff : ∀ J ∈ P, IsAffineOpen (J.inf V))
    (hU : ∀ i W, IsAffineOpen W → IsAffineOpen (U i ⊓ W)) (hcov : ⨆ i, U i = ⊤) (n : ℕ) :
    Nonempty ((cechOnSupport f F V P hP).homology n ≃ₗ[K]
      (cechOnSupport f F (joinedCover U V) (joinedSupport (nonemptyIntersections ι) P)
        (joinedSupport_ordConnected (nonemptyIntersections_ordConnected ι) hP)).homology (n + 1)) := by
  let E := joinedCover U V
  let D := sectionDatum F E
  letI (s : Finset (ι ⊕ₗ κ)) := sectionDatumModule f F E s
  let Q := (@rgt ι κ) ⁻¹' P
  let T := joinedSupport (nonemptyIntersections ι) P
  let hQ : Q.OrdConnected := hP.preimage_mono rgt_monotone
  let hS := supportDiff_ordConnected hQ (right_join_upper P)
  let m (J : Finset κ) := uni (∅ : Finset ι) J
  have hm : Monotone m := fun _ _ h => uni_mono (Finset.Subset.refl _) h
  have hp : m ⁻¹' (Q \ T) = P := by
    ext j
    simp [m, Q, T, joinedSupport, nonemptyIntersections]
  obtain ⟨A⟩ := nonempty_homology_equiv_cechSlice f F E V m hm (Q \ T) hS
    (fun J => by simp [E, m, coverInter, inf_joinedCover]) n
  obtain ⟨B⟩ := D.nonempty_homology_equiv_rightJoin_succ (res_base_smul f F E) P hP
    (acyclic_joined_of_affine_right f F U V P hP h₀ hPaff hU hcov) n
  rw [← cechOnSupport_congr f F V (hS.preimage_mono hm) hP hp]
  exact ⟨A.trans B⟩

end GlobalTheory.LineBundleSections
