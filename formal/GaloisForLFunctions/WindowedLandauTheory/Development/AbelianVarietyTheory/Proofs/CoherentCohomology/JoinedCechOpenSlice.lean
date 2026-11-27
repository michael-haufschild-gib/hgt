import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.OpenRestrictionCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineCechJoinComparison

/-! A left slice of a supported joined Čech complex computes sections on
the corresponding right intersection. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace HTGeometry GlobalTheory.WH
open HTGeometry.FinsetCechDatum GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

/-- Keeping every nonempty intersection preserves the unaugmented complex. -/
private def truncateIso {K T : Type} [Field K] [LinearOrder T]
    (D : FinsetCechDatum.{0} T) [∀ s, Module K (D.obj s)]
    (hD : ∀ {s t : Finset T} (h : s ⊆ t) (r : K) (x : D.obj s), D.res h (r • x) = r • D.res h x)
    (P : Set (Finset T)) (hP : P.OrdConnected) (hpos : ∀ s, s.Nonempty → s ∈ P) :
    (D.truncate (R := K) P hP).linearComplex (D.truncate_linear P hP hD) ≅ D.linearComplex hD := by
  let A := D.truncate (R := K) P hP
  let φ : A.Hom D :=
    { app s := (D.supportCoeff (R := K) P s).subtype.toAddMonoidHom
      comm := fun {s t} h x => by
        change D.res h x.1 = (A.res h x).1
        rw [D.truncate_res_value]
        by_cases ht : t ∈ P
        · rw [if_pos ht]
        · have hse : s = ∅ := by
            by_contra hn
            exact ht (hpos t ((Finset.nonempty_iff_ne_empty.mpr hn).mono h))
          have hte : t = ∅ := by
            by_contra hn
            exact ht (hpos t (Finset.nonempty_iff_ne_empty.mpr hn))
          have hst := hse.trans hte.symm
          rw [if_neg ht, x.2 (fun hs => ht (hst ▸ hs)), map_zero] }
  have hφ (s : Finset T) (r : K) (x : A.obj s) : φ.app s (r • x) = r • φ.app s x := rfl
  let a := linearCochainMap (D.truncate_linear P hP hD) hD φ hφ
  letI : IsIso a := isIso_linearCochainMap _ _ φ hφ fun s hs =>
    ⟨Subtype.val_injective, fun x => ⟨⟨x, fun hn => (hn (hpos s hs)).elim⟩, rfl⟩⟩
  exact asIso a

/-- For a fixed right index set, the left slice restricts the left cover
to its right intersection. -/
theorem nonempty_openCechIsoLeftSlice {K : Type} [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of K)) (F : X.Modules) {I J : Type} [LinearOrder I] [LinearOrder J]
    (U : I → X.Opens) (V : J → X.Opens) (T : Finset J) (P : Set (Finset (I ⊕ₗ J)))
    (hP : P.OrdConnected) (hs : ∀ s : Finset I, s.Nonempty → uni s T ∈ P) :
    let D := sectionDatum F (joinedCover U V)
    letI (s : Finset (I ⊕ₗ J)) := sectionDatumModule f F (joinedCover U V) s
    let B := D.truncate (R := K) P hP
    Nonempty ((B.leftSlice T).linearComplex (B.leftSlice_linear (D.truncate_linear P hP
      (res_base_smul f F (joinedCover U V))) T) ≅ cechOverOpen f F (T.inf V) U) := by
  let E := joinedCover U V
  let D := sectionDatum F E
  letI (s : Finset (I ⊕ₗ J)) := sectionDatumModule f F E s
  let W := T.inf V
  let A := openSectionDatum F W U
  letI (s : Finset I) := openSectionDatumModule f F W U s
  let B := D.truncate (R := K) P hP
  let m (I₀ : Finset I) := uni I₀ T
  let hm : Monotone m := fun _ _ h => uni_mono h (Finset.Subset.refl _)
  let Q := m ⁻¹' P
  let hQ := hP.preimage_mono hm
  have e (s : Finset I) : coverInter (⊤ : X.Opens) E (m s) = coverInter W U s := by
    simp only [E, m, W, coverInter, top_inf_eq, inf_joinedCover, lft_uni, rgt_uni]
    exact inf_comm _ _
  obtain ⟨φ, hbij, hlin⟩ := exists_slice_hom f F E W U m hm P hP e
  have hA {s t : Finset I} (h : s ⊆ t) (r : K) (x : A.obj s) :
      A.res h (r • x) = r • A.res h x := open_res_base_smul f F W U h r x
  have hB {s t : Finset I} (h : s ⊆ t) (r : K) (x : (B.leftSlice T).obj s) :
      (B.leftSlice T).res h (r • x) = r • (B.leftSlice T).res h x :=
    B.leftSlice_linear (D.truncate_linear P hP (res_base_smul f F E)) T h r x
  let u := linearCochainMap (A.truncate_linear Q hQ hA) hB φ hlin
  letI : IsIso u := isIso_linearCochainMap _ _ φ hlin fun s _ => hbij s
  exact ⟨(asIso u).symm ≪≫ truncateIso A hA Q hQ hs⟩

end GlobalTheory.LineBundleSections
