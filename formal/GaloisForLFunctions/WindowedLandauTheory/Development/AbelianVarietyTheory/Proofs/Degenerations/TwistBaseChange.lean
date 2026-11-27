import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.Degenerations.PolarizedDegenerationData
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.NormalizedTwistCoordinateExpansion

/-! The normalized powers of degeneration data have section bases over a
local base that persist on every affine base change. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology

namespace ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

/-- One vector of base section coefficients gives the same expansion in all charts. -/
def IsSecBasis {T Y : Scheme.{0}} (p : Y ⟶ T) {N : LB Y} {m : ℕ} (b : Fin m → N.Sec) : Prop :=
  ∀ s : N.Sec, ∃! r : Fin m → Γ(T, ⊤), ∀ j,
    s.f j = ∑ i, resG Y le_top (p.appTop (r i)) * (b i).f j

/-- Chart coordinates of the pullback are the restricted pulled-back coordinates of the section. -/
def IsPullSecLC {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Y' ⟶ Y) (s : (LB.LinComb L φ ε).Sec)
    (t : (LB.LinComb L (fun k => p ≫ φ k) ε).Sec) : Prop :=
  ∀ j, t.f j = (pullSec s p).f j

private theorem sectionAlgebra_apply {R : Type} [CommRing R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (.of R)) (U : Y.Opens) (r : R) :
    letI := sectionAlgebra p U
    algebraMap R Γ(Y, U) r = resG Y le_top (p.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) :=
  rfl

private theorem isSecBasis_of_ring_coefficients {R : Type} [CommRing R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (.of R)) {N : LB Y} {m : ℕ} (b : Fin m → N.Sec)
    (h : ∀ s : N.Sec, ∃! r : Fin m → R, ∀ j : N.ι,
      letI := sectionAlgebra p (N.U j)
      s.f j = ∑ i, algebraMap R Γ(Y, N.U j) (r i) * (b i).f j) : IsSecBasis p b := by
  intro s
  obtain ⟨r, hr, hu⟩ := h s
  let e := Scheme.ΓSpecIso (.of R)
  refine ⟨fun i => e.inv (r i), fun j => ?_, fun t ht => ?_⟩
  · exact (hr j).trans (Finset.sum_congr rfl fun i _ =>
      congrArg (· * (b i).f j) (sectionAlgebra_apply p (N.U j) (r i)))
  · let r' (i : Fin m) : R := e.hom (t i)
    have he (i : Fin m) : e.inv (r' i) = t i := Iso.hom_inv_id_apply e (t i)
    have hr' (j : N.ι) :
        letI := sectionAlgebra p (N.U j)
        s.f j = ∑ i, algebraMap R Γ(Y, N.U j) (r' i) * (b i).f j := by
      refine (ht j).trans (Finset.sum_congr rfl fun i _ => ?_)
      exact congrArg (· * (b i).f j)
        ((congrArg (fun u : Γ(Spec (.of R), ⊤) => resG Y le_top (p.appTop u)) (he i)).symm.trans
          (sectionAlgebra_apply p (N.U j) (r' i)).symm)
    have h := hu r' hr'
    funext i
    exact (he i).symm.trans (congrArg (fun u : R => e.inv u) (congrFun h i))

/-- The base-change statement for the chart sections of a normalized power. -/
def TwistBaseChangeStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R)
    (j : ℕ), 1 ≤ j → ∀ α : D.X,
      ∃ (m : ℕ) (b : Fin m → D.SecB j α), m = j ^ D.P.g ∧
        ∀ (R' : Type) [CommRing R'] (φ : R →+* R'),
          let T := Over.mk (Spec.map (CommRingCat.ofHom φ))
          let π := (snd T D.P.A).left
          ∀ b' : Fin m → (LB.LinComb D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε j)).Sec,
            (∀ i, IsPullSecLC D.P.L (D.famφB α) (DegPre.famε j) π (b i) (b' i)) →
              IsSecBasis (fst T D.P.A).left b'

/-- Normalized powers of degeneration data have a basis stable under arbitrary affine base change. -/
theorem twistBaseChange : TwistBaseChangeStatement := by
  intro R _ _ _ _ D j hj α
  letI := D.P.smoothDim
  obtain ⟨b, hb⟩ := GlobalTheory.PrincipalSections.exists_normalized_twist_unique_expansion
    D.P.isAb D.P.isLB D.P.ample D.P.ktriv D.P.rigid D.P.sym D.P.g (D.c α) j hj
  let b₀ : Fin (j ^ D.P.g) → D.SecB j α := b
  refine ⟨j ^ D.P.g, b₀, rfl, fun R' _ φ => ?_⟩
  dsimp only
  intro b' hpb
  let T := Over.mk (Spec.map (CommRingCat.ofHom φ))
  let π := (snd T D.P.A).left
  let p := (fst T D.P.A).left
  have W : IsPullback π p D.P.A.hom (Spec.map (CommRingCat.ofHom φ)) :=
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom φ)) D.P.A.hom).flip
  change IsSecBasis p b'
  refine isSecBasis_of_ring_coefficients p b' fun s => ?_
  let N := LB.LinComb D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε j)
  let bπ (k : Fin (j ^ D.P.g)) : N.Sec := pullSec (b₀ k) π
  have hbase : ∃! r : Fin (j ^ D.P.g) → R', ∀ i : N.ι,
      letI := sectionAlgebra p (N.U i)
      s.f i = ∑ k, algebraMap R' Γ((T ⊗ D.P.A).left, N.U i) (r k) * (bπ k).f i :=
    hb R' φ (π := π) (g := p) W s
  refine (existsUnique_congr fun r => ?_).mp hbase
  constructor
  · intro h i
    exact (h i).trans (Finset.sum_congr rfl fun k _ => congrArg (_ * ·) (hpb k i).symm)
  · intro h i
    exact (h i).trans (Finset.sum_congr rfl fun k _ => congrArg (_ * ·) (hpb k i))

/-- Each section over a local base change is a linear combination of sections from the original base. -/
def TwistBCSpanStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R)
    (j : ℕ), 1 ≤ j → ∀ (α : D.X) (R' : Type) [CommRing R'] [IsLocalRing R'] (φ : R →+* R'),
      IsLocalHom φ →
        let T := Over.mk (Spec.map (CommRingCat.ofHom φ))
        let π := (snd T D.P.A).left
        let N := LB.LinComb D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε j)
        ∀ s : N.Sec,
          ∃ (m : ℕ) (r : Fin m → Γ(T.left, ⊤)) (b : Fin m → D.SecB j α),
            ∀ i : N.ι, s.f i = ∑ k,
              resG (T ⊗ D.P.A).left (show N.U i ≤ ⊤ from le_top) ((fst T D.P.A).left.appTop (r k)) *
                (pullSec (b k) π).f i

theorem twistBCSpan : TwistBCSpanStatement := by
  intro R _ _ _ _ D j hj α R' _ _ φ _
  dsimp only
  intro s
  obtain ⟨m, b, -, hb⟩ := twistBaseChange R D j hj α
  let T := Over.mk (Spec.map (CommRingCat.ofHom φ))
  let π := (snd T D.P.A).left
  have h := hb R' φ (fun k => pullSec (b k) π) (fun _ _ => rfl)
  obtain ⟨r, hr, -⟩ := h s
  exact ⟨m, r, b, hr⟩

end ReciprocityTheory.ChartRestriction.G.DVR
