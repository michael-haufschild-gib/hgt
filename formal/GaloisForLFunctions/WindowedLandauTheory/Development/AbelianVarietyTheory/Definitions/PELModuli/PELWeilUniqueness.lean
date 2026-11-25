import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.ThetaCommutatorValues

/-! The theta commutator determines a unique scalar on a one-point base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

/-- Global units on an affine spectrum are exactly the units of its ring. -/
theorem unitOn_bijective {R : Type} [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ}

/-- Evaluate both commutators on the identity section to recover their scalar. -/
theorem commIsOf_scalar_unique (hL : L.IsLB) {x y : ThetaGrp A L k T} {a b : Γ(T.left, ⊤)ˣ}
    (ha : CommIsOf A L k x y a) (hb : CommIsOf A L k x y b) : a = b := by
  let u : T.left ⟶ (T ⊗ A).left := (lift (𝟙 T) (1 : T ⟶ A)).left
  have hu : u ≫ (fst T A).left = 𝟙 T.left := congrArg Over.Hom.left (lift_fst (𝟙 T) (1 : T ⟶ A))
  apply unit_ext
  intro z hz
  choose J hJ using fun r : T.left ⟶ A.left => exists_chart hL (r z)
  have ea := (commIsOf_iff hL x y a).mp ha T.left u z J hJ
  have eb := (commIsOf_iff hL x y b).mp hb T.left u z J hJ
  have eq := mul_left_cancel (ea.symm.trans eb)
  exact (congrArg (fun f : T.left ⟶ T.left => gm f z ⊤ a) hu).symm.trans
    (eq.trans (congrArg (fun f : T.left ⟶ T.left => gm f z ⊤ b) hu))

/-- On a one-point base all nonempty open neighbourhoods are the whole base. -/
theorem weilIs_unique_singleton (hL : L.IsLB) [Unique T.left] {x y : T ⟶ A} {a b : Γ(T.left, ⊤)ˣ}
    (ha : WeilIs A L k x y a) (hb : WeilIs A L k x y b) : a = b := by
  let z : T.left := default
  obtain ⟨U, hzU, ⟨θx, θy, hx, hy⟩, hU⟩ := ha z
  obtain ⟨V, hzV, -, hV⟩ := hb z
  have ht (W : T.left.Opens) (h : z ∈ W) : W = ⊤ :=
    top_le_iff.mp fun t _ => Subsingleton.elim z t ▸ h
  have hVU : V = U := (ht V hzV).trans (ht U hzU).symm
  subst V
  have eq := commIsOf_scalar_unique hL (hU θx θy hx hy) (hV θx θy hx hy)
  obtain rfl : U = ⊤ := ht U hzU
  letI : IsIso (⊤ : T.left.Opens).ι := inferInstanceAs (IsIso T.left.topIso.hom)
  letI : IsIso ((⊤ : T.left.Opens).ι.appTop) :=
    inferInstanceAs (IsIso ((⊤ : T.left.Opens).ι.app ⊤))
  apply Units.ext
  apply (ConcreteCategory.bijective_of_isIso ((⊤ : T.left.Opens).ι.appTop)).1
  exact congrArg Units.val eq

/-- Two field-valued scalars giving the same theta commutator are equal. -/
theorem weilIs_unique_field (hL : L.IsLB) {K : Type} [Field K] {f : Sp K ⟶ S}
    {x y : Over.mk f ⟶ A} {a b : Kˣ}
    (ha : WeilIs A L k x y (unitOn a)) (hb : WeilIs A L k x y (unitOn b)) : a = b := by
  letI : Unique (Over.mk f).left := inferInstanceAs (Unique (PrimeSpectrum K))
  exact unitOn_bijective.1 (weilIs_unique_singleton hL ha hb)

end GlobalTheory.CommPairing
