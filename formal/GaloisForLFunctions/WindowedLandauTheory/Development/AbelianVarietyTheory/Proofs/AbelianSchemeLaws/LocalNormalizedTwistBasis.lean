import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GeometricTwistFibre
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeSquare
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LocalSectionBasis

/-! The constant factors in the normalized twist have generators over a
local base, so the geometric fibre has the cohomology of the translated power. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace HTGeometry
open GlobalTheory.LineBundleSections GlobalTheory.ProjectiveSections GlobalTheory.SchemeCohomology
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Cb
open scoped CategoryTheory.Obj

namespace GlobalTheory.PrincipalSections

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] [IsLocalRing R]
  {A : Over (Spec (.of R))} [GrpObj A] {L : LB A.left}

private theorem normalized_twist_iso (hL : L.IsLB) (x : 𝟙_ (Over (Spec (.of R))) ⟶ A) (j : ℕ) :
    let τ : A ⟶ A := (toUnit A ≫ x) * 𝟙 A
    let M := LB.LinComb L ![𝟙 A.left, τ.left] ![(j : ℤ) - 1, 1]
    let N := LB.LinComb L ![𝟙 A.left, τ.left, A.hom ≫ x.left, A.hom ≫ η[A].left] ![(j : ℤ) - 1, 1, -1, 1]
    LBIso M N := by
  let τ : A ⟶ A := (toUnit A ≫ x) * 𝟙 A
  let u : Fin 2 → (Spec (.of R) ⟶ A.left) := ![x.left, η[A].left]
  let c (i : Fin 2) := A.hom ≫ u i
  let a : Fin 2 → (A.left ⟶ A.left) := ![𝟙 A.left, τ.left]
  let b : Fin 4 → (A.left ⟶ A.left) := ![𝟙 A.left, τ.left, c 0, c 1]
  let d : Fin 2 → ℤ := ![(j : ℤ) - 1, 1]
  let e : Fin 4 → ℤ := ![(j : ℤ) - 1, 1, -1, 1]
  let d₀ : Fin 2 → ℤ := ![-1, 1]
  choose i hi using fun k : Fin 2 => exists_chart hL ((u k) (IsLocalRing.closedPoint R))
  have hc (y : A.left) : y ∈ LB.wchart L c i := by
    refine Set.mem_iInter.2 fun k => ?_
    change A.hom y ∈ (u k) ⁻¹ᵁ L.U (i k)
    rw [Scheme.preimage_eq_top_of_closedPoint_mem (u k) (hi k)]
    trivial
  obtain ⟨s, hs⟩ := AbLaw.Cube.exists_gen_of_chart hL c d₀ i hc
  refine exists_iso_of_formal_difference_gen hL b a e d (fun G _ χ => ?_) s hs
  let p := χ (𝟙 A.left) ^ ((j : ℤ) - 1)
  let q := χ τ.left
  let r := (χ (c 0))⁻¹
  let s := χ (c 1)
  simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_four, Sum.elim_inl,
    Sum.elim_inr, b, a, d, e, d₀, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    zpow_one, zpow_neg]
  change r * s = (p * q * r * s) * (p⁻¹ * q⁻¹)
  calc
    _ = (p * p⁻¹) * (q * q⁻¹) * (r * s) := by simp only [mul_inv_cancel, _root_.one_mul]
    _ = _ := by ac_rfl

/-- A normalized power with a translated factor has a basis of size `j^d`
over the local ring, and the pulled-back sections are a basis after base change. -/
theorem exists_normalized_local_twist_basis (hA : IsAbelianScheme A) (hL : L.IsLB)
    (hAmp : RelAmple A L) (hK : KTriv A L)
    (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : Spec (.of R), ∃ U : (Spec (.of R)).Opens, s ∈ U ∧
      ∃ t : (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    (x : 𝟙_ (Over (Spec (.of R))) ⟶ A) (j : ℕ) (hj : 1 ≤ j) :
    let τ : A ⟶ A := (toUnit A ≫ x) * 𝟙 A
    let N := LB.LinComb L
      ![𝟙 A.left, τ.left, A.hom ≫ x.left, A.hom ≫ η[A].left] ![(j : ℤ) - 1, 1, -1, 1]
    ∃ b : Fin (j ^ d) → Γ(toMod N, ⊤),
      ∀ (S : Type) [CommRing S] (α : R →+* S) {Y : Scheme.{0}} {π : Y ⟶ A.left}
        {g : Y ⟶ Spec (.of S)}, IsPullback π g A.hom (Spec.map (CommRingCat.ofHom α)) →
        letI := sectionBaseModule g (toMod (N.pull π)) ⊤
        ∃ e : (Fin (j ^ d) → S) ≃ₗ[S] Γ(toMod (N.pull π), ⊤),
          ∀ k, e (Pi.single k 1) =
            pullSection (ChartPull.pull N π) (U := ⊤) (V := ⊤) (by simp) (b k) := by
  letI := hA.smooth
  let τ : A ⟶ A := (toUnit A ≫ x) * 𝟙 A
  let M := LB.LinComb L ![𝟙 A.left, τ.left] ![(j : ℤ) - 1, 1]
  let N := LB.LinComb L
    ![𝟙 A.left, τ.left, A.hom ≫ x.left, A.hom ≫ η[A].left] ![(j : ℤ) - 1, 1, -1, 1]
  have hM : M.IsLB := hL.linComb _ _
  have hN : N.IsLB := hL.linComb _ _
  have hp := isProjOver_of_relAmple hL hAmp
  refine exists_local_basis_of_geometric_closed_fibre A.hom hN hp (j ^ d) ?_
  let k := IsLocalRing.ResidueField R
  let K := AlgebraicClosure k
  let α₀ : R →+* K := (algebraMap k K).comp (IsLocalRing.residue R)
  let t := Spec.map (CommRingCat.ofHom α₀)
  let π₀ := pullback.fst A.hom t
  let f₀ := pullback.snd A.hom t
  letI := sectionBaseModule f₀ (toMod (M.pull π₀)) ⊤
  letI := sectionBaseModule f₀ (toMod (N.pull π₀)) ⊤
  have h := geometric_twist_finrank_and_vanishing hA hL hAmp hK hrig hsym d t x j hj
  have H : IsPullback π₀ f₀ A.hom t := IsPullback.of_hasPullback _ _
  obtain ⟨m, a, ha, haf⟩ := isProjOver_baseChange α₀ H hp
  letI := ha
  let U (i : Fin (m + 1)) := a ⁻¹ᵁ PSpace.coordinateOpen K m i
  have cU : ⨆ i, U i = ⊤ := a.iSup_preimage_eq_top (PSpace.iSup_coordinateOpen K m)
  have hU (I : Finset (Fin (m + 1))) (hI : I.Nonempty) : IsAffineOpen (coverInter ⊤ U I) :=
    (coverInter_pull (π := a) (PSpace.coordinateOpen K m) I).symm ▸
      (PSpace.isAffineOpen_coordinateInter K m hI).preimage a
  obtain ⟨v, hv⟩ := LBIso.pull (normalized_twist_iso hL x j) π₀
  let D := cechIsoOfIsGen f₀ U (hM.pull π₀) (hN.pull π₀) hv
  constructor
  · let e := (cechHomologyZeroEquiv f₀ (toMod (M.pull π₀)) U cU).symm.trans
      ((HomologicalComplex.homologyMapIso D 0).toLinearEquiv.trans
        (cechHomologyZeroEquiv f₀ (toMod (N.pull π₀)) U cU))
    exact e.finrank_eq.symm.trans h.1
  · have he := (exactAt_cech_iff_subsingleton_cohomology f₀ (hM.pull π₀) U cU.ge hU 1).mpr (h.2 0)
    exact (exactAt_cech_iff_subsingleton_cohomology f₀ (hN.pull π₀) U cU.ge hU 1).mp (he.of_iso D)

end GlobalTheory.PrincipalSections
