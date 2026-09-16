import GaloisForLFunctions.RHTower.SelbergMaassRationalMackeyBlockSource
import GaloisForLFunctions.RHTower.SelbergMaassPositiveRationalHeckePair
import GaloisForLFunctions.RHTower.SelbergMaassRationalHeckeDoubleCoset
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.NumberTheory.HeckeRing.Defs

/-!
# Mackey orbit labels as double cosets

The orbit index in the finite Maass Mackey formula has a canonical double-coset
label.  A relative coset represented by `r` is sent to the double coset of
`a * r⁻¹`.  The source relation changes this element on the left, and the
Mackey acting subgroup changes it on the right.  This is the exact reindexing
map required before the finite Mackey sum can be aggregated by Hecke cosets.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint MulAction Subgroup
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

variable {A : Type*} [Group A]

/-- Forgetting that a representative belongs to a correspondence submonoid
maps a Hecke coset to the corresponding ambient double coset. -/
noncomputable def heckeCosetToDoubleCoset
    (Δ : Submonoid A) (K₁ K₂ : Subgroup A) :
    HeckeCoset Δ K₁ K₂ → DoubleCoset.Quotient (K₁ : Set A) (K₂ : Set A) :=
  Quotient.lift (fun d => DoubleCoset.mk K₁ K₂ d.val) (by
    intro d e hde
    apply (DoubleCoset.eq'' K₁ K₂).mpr
    exact hde)

/-- The ambient-double-coset map is injective on Hecke cosets: its defining
relation is precisely the ambient double-coset relation restricted to `Δ`. -/
theorem heckeCosetToDoubleCoset_injective
    (Δ : Submonoid A) (K₁ K₂ : Subgroup A) :
    Function.Injective (heckeCosetToDoubleCoset Δ K₁ K₂) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      change DoubleCoset.mk K₁ K₂ x.val = DoubleCoset.mk K₁ K₂ y.val at hxy
      apply Quotient.sound
      apply (DoubleCoset.eq'' K₁ K₂).mp
      exact hxy

/-- Formula for forgetting the monoid membership of a literal Hecke-coset
representative. -/
@[simp] theorem heckeCosetToDoubleCoset_mk
    (Δ : Submonoid A) (K₁ K₂ : Subgroup A) (d : Δ) :
    heckeCosetToDoubleCoset Δ K₁ K₂ (HeckeCoset.mk K₁ K₂ d) =
      DoubleCoset.mk K₁ K₂ d.val := rfl

/-- A finite sum can be reindexed by the finite image of any label map.  The
target carrier itself need not be finite; this is the form needed for Mackey
orbits labelled by the generally infinite Hecke-coset carrier. -/
theorem sum_by_image_fibers
    {Ω D M : Type*} [Fintype Ω] [DecidableEq D] [AddCommMonoid M]
    (label : Ω → D) (F : Ω → M) :
    (∑ q : Ω, F q) =
      ∑ d ∈ (Finset.univ.image label), ∑ q ∈ Finset.univ with label q = d, F q := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun q hq => Finset.mem_image_of_mem label hq) F

/-- A relative coset has a double-coset label whenever conjugating the inverse
of every source element by `a` lands in the outer subgroup. -/
noncomputable def mackeyRelativeCosetToDoubleCoset
    (G H K : Subgroup A) (a : A)
    (hconj : ∀ c : H, c ∈ G.subgroupOf H → a * c.val⁻¹ * a⁻¹ ∈ K) :
    H ⧸ G.subgroupOf H → DoubleCoset.Quotient (K : Set A) (K : Set A) :=
  Quotient.lift (fun r => DoubleCoset.mk K K (a * r.val⁻¹)) (by
    intro x y hxy
    have hxy' : x⁻¹ * y ∈ G.subgroupOf H := by
      simpa only [QuotientGroup.leftRel_apply] using hxy
    let c : H := x⁻¹ * y
    have hc : c ∈ G.subgroupOf H := hxy'
    have hy : y = x * c := by
      dsimp [c]
      group
    rw [DoubleCoset.eq]
    refine ⟨a * c.val⁻¹ * a⁻¹, hconj c hc, 1, K.one_mem, ?_⟩
    rw [hy]
    dsimp [c]
    group)

/-- Formula for the relative-coset double-coset label on a literal
representative. -/
@[simp] theorem mackeyRelativeCosetToDoubleCoset_mk
    (G H K : Subgroup A) (a : A)
    (hconj : ∀ c : H, c ∈ G.subgroupOf H → a * c.val⁻¹ * a⁻¹ ∈ K)
    (r : H) :
    mackeyRelativeCosetToDoubleCoset G H K a hconj (QuotientGroup.mk r) =
      DoubleCoset.mk K K (a * r.val⁻¹) := rfl

/-- Writing a relative coset through its canonical quotient representative
does not alter its double-coset label. -/
theorem mackeyRelativeCosetToDoubleCoset_eq_out
    (G H K : Subgroup A) (a : A)
    (hconj : ∀ c : H, c ∈ G.subgroupOf H → a * c.val⁻¹ * a⁻¹ ∈ K)
    (q : H ⧸ G.subgroupOf H) :
    mackeyRelativeCosetToDoubleCoset G H K a hconj q =
      DoubleCoset.mk K K (a * q.out.val⁻¹) := by
  calc
    mackeyRelativeCosetToDoubleCoset G H K a hconj q =
        mackeyRelativeCosetToDoubleCoset G H K a hconj (Quotient.mk'' q.out) :=
      congrArg _ (Quotient.out_eq' q).symm
    _ = DoubleCoset.mk K K (a * q.out.val⁻¹) :=
      mackeyRelativeCosetToDoubleCoset_mk G H K a hconj q.out

/-- The relative-coset label is constant on every orbit of an acting subgroup
whose image lies in the outer subgroup. -/
theorem mackeyRelativeCosetToDoubleCoset_smul
    (G H K : Subgroup A) (a : A)
    (hconj : ∀ c : H, c ∈ G.subgroupOf H → a * c.val⁻¹ * a⁻¹ ∈ K)
    (J : Subgroup H) (hJK : J.map H.subtype ≤ K)
    (j : J) (q : H ⧸ G.subgroupOf H) :
    mackeyRelativeCosetToDoubleCoset G H K a hconj (j • q) =
      mackeyRelativeCosetToDoubleCoset G H K a hconj q := by
  induction q using Quotient.inductionOn with
  | h r =>
    change mackeyRelativeCosetToDoubleCoset G H K a hconj
      (QuotientGroup.mk (j.val * r)) =
      mackeyRelativeCosetToDoubleCoset G H K a hconj (QuotientGroup.mk r)
    rw [mackeyRelativeCosetToDoubleCoset_mk,
      mackeyRelativeCosetToDoubleCoset_mk, DoubleCoset.eq]
    refine ⟨1, K.one_mem, j.val.val, hJK ⟨j, j.2, rfl⟩, ?_⟩
    simp only [one_mul]
    change a * r.val⁻¹ = a * (j.val.val * r.val)⁻¹ * j.val.val
    group

/-- The double-coset label descends from relative cosets to the Mackey orbit
index used by the finite trace product formula. -/
noncomputable def mackeyOrbitToDoubleCoset
    (G H K : Subgroup A) (a : A)
    (hconj : ∀ c : H, c ∈ G.subgroupOf H → a * c.val⁻¹ * a⁻¹ ∈ K)
    (J : Subgroup H) (hJK : J.map H.subtype ≤ K) :
    Quotient (orbitRel J (H ⧸ G.subgroupOf H)) →
      DoubleCoset.Quotient (K : Set A) (K : Set A) :=
  Quotient.lift (mackeyRelativeCosetToDoubleCoset G H K a hconj) (by
    intro q q' hqq'
    change q ∈ MulAction.orbit J q' at hqq'
    rcases hqq' with ⟨j, rfl⟩
    exact mackeyRelativeCosetToDoubleCoset_smul G H K a hconj J hJK j q')

/-- Formula for the Mackey-orbit double-coset label. -/
@[simp] theorem mackeyOrbitToDoubleCoset_mk
    (G H K : Subgroup A) (a : A)
    (hconj : ∀ c : H, c ∈ G.subgroupOf H → a * c.val⁻¹ * a⁻¹ ∈ K)
    (J : Subgroup H) (hJK : J.map H.subtype ≤ K)
    (q : H ⧸ G.subgroupOf H) :
    mackeyOrbitToDoubleCoset G H K a hconj J hJK (Quotient.mk _ q) =
      mackeyRelativeCosetToDoubleCoset G H K a hconj q := rfl

/-- Writing a Mackey orbit through its canonical quotient representative
does not alter its descended double-coset label. -/
theorem mackeyOrbitToDoubleCoset_eq_out
    (G H K : Subgroup A) (a : A)
    (hconj : ∀ c : H, c ∈ G.subgroupOf H → a * c.val⁻¹ * a⁻¹ ∈ K)
    (J : Subgroup H) (hJK : J.map H.subtype ≤ K)
    (q : Quotient (orbitRel J (H ⧸ G.subgroupOf H))) :
    mackeyOrbitToDoubleCoset G H K a hconj J hJK q =
      mackeyRelativeCosetToDoubleCoset G H K a hconj q.out := by
  calc
    mackeyOrbitToDoubleCoset G H K a hconj J hJK q =
        mackeyOrbitToDoubleCoset G H K a hconj J hJK (Quotient.mk'' q.out) :=
      congrArg _ (Quotient.out_eq' q).symm
    _ = mackeyRelativeCosetToDoubleCoset G H K a hconj q.out :=
      mackeyOrbitToDoubleCoset_mk G H K a hconj J hJK q.out

/-- In the rational principal product, conjugating the inverse of an inner
source element by the product matrix returns to the principal source. -/
theorem rationalMackey_conjugate_inv_mem_principal
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (c : rationalConjugateGroup N h)
    (hc : c ∈ (rationalPullbackConjugateGroup (rationalConjugateGroup N g) h).subgroupOf
      (rationalConjugateGroup N h)) :
    (g * h).map (algebraMap ℚ ℝ) * c.val⁻¹ *
        ((g * h).map (algebraMap ℚ ℝ))⁻¹ ∈ principalCongruenceGL N := by
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let a : GL (Fin 2) ℝ := (g * h).map (algebraMap ℚ ℝ)
  have hcG : c.val ∈ G := hc
  have hGprod : G = rationalPullbackConjugateGroup (principalCongruenceGL N) (g * h) := by
    simpa only [G] using rationalPullbackConjugateGroup_mul (principalCongruenceGL N) g h
  rw [hGprod] at hcG
  have hcGinv : c.val⁻¹ ∈ rationalPullbackConjugateGroup
      (principalCongruenceGL N) (g * h) :=
    (rationalPullbackConjugateGroup (principalCongruenceGL N) (g * h)).inv_mem hcG
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hcGinv
  change a * c.val⁻¹ * a⁻¹ ∈ principalCongruenceGL N
  simpa only [a, ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul] using hcGinv

/-- The actual rational Mackey orbit index maps canonically to principal
double cosets in the ambient real group. -/
noncomputable def rationalMackeyOrbitToDoubleCoset
    (N : ℕ) (g h : GL (Fin 2) ℚ) :
    let P := principalCongruenceGL N
    let G := rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
    let H := rationalConjugateGroup N h
    let J := P.subgroupOf H
    Quotient (orbitRel J (H ⧸ G.subgroupOf H)) →
      DoubleCoset.Quotient (P : Set (GL (Fin 2) ℝ)) (P : Set (GL (Fin 2) ℝ)) := by
  dsimp only
  let P : Subgroup (GL (Fin 2) ℝ) := principalCongruenceGL N
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let J : Subgroup H := P.subgroupOf H
  let a : GL (Fin 2) ℝ := (g * h).map (algebraMap ℚ ℝ)
  have hconj : ∀ c : H, c ∈ G.subgroupOf H → a * c.val⁻¹ * a⁻¹ ∈ P := by
    intro c hc
    simpa only [P, G, H, a] using rationalMackey_conjugate_inv_mem_principal N g h c hc
  have hJ : J.map H.subtype ≤ P := by
    simp only [J, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  exact mackeyOrbitToDoubleCoset G H P a hconj J hJ

/-- Inversion preserves positivity of the real determinant of a rational
invertible matrix. -/
theorem rationalGL_map_det_inv_pos (b : GL (Fin 2) ℚ)
    (hb : 0 < (b.map (algebraMap ℚ ℝ)).val.det) :
    0 < ((b⁻¹).map (algebraMap ℚ ℝ)).val.det := by
  rw [Matrix.GeneralLinearGroup.map_inv]
  let B : GL (Fin 2) ℝ := b.map (algebraMap ℚ ℝ)
  have hprod : (B⁻¹).val.det * B.val.det = 1 := by
    rw [← Matrix.det_mul]
    change (B⁻¹ * B).val.det = 1
    rw [show B⁻¹ * B = 1 from inv_mul_cancel B, Units.val_one, Matrix.det_one]
  apply pos_of_mul_pos_left (b := B.val.det) ?_ (le_of_lt hb)
  rw [hprod]
  exact zero_lt_one

/-- A fixed positive rational lift of a rational-conjugate principal group
element, used to label a Mackey block by a positive correspondence. -/
noncomputable def rationalMackeyRepresentativeLift
    (N : ℕ) (h : GL (Fin 2) ℚ) (r : rationalConjugateGroup N h) : GL (Fin 2) ℚ :=
  (rationalConjugateGroup_exists_positive_rational_lift N h r).choose

theorem rationalMackeyRepresentativeLift_map
    (N : ℕ) (h : GL (Fin 2) ℚ) (r : rationalConjugateGroup N h) :
    (rationalMackeyRepresentativeLift N h r).map (algebraMap ℚ ℝ) = r.val :=
  (rationalConjugateGroup_exists_positive_rational_lift N h r).choose_spec.1

theorem rationalMackeyRepresentativeLift_det_pos
    (N : ℕ) (h : GL (Fin 2) ℚ) (r : rationalConjugateGroup N h) :
    0 < ((rationalMackeyRepresentativeLift N h r).map (algebraMap ℚ ℝ)).val.det :=
  (rationalConjugateGroup_exists_positive_rational_lift N h r).choose_spec.2

/-- The rational product label carried by a literal Mackey representative. -/
noncomputable def rationalMackeyRepresentativeProduct
    (N : ℕ) (g h : GL (Fin 2) ℚ) (r : rationalConjugateGroup N h) : GL (Fin 2) ℚ :=
  g * h * (rationalMackeyRepresentativeLift N h r)⁻¹

theorem rationalMackeyRepresentativeProduct_det_pos
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det)
    (r : rationalConjugateGroup N h) :
    0 < ((rationalMackeyRepresentativeProduct N g h r).map (algebraMap ℚ ℝ)).val.det := by
  unfold rationalMackeyRepresentativeProduct
  apply rationalGL_map_det_mul_pos
  · exact rationalGL_map_det_mul_pos g h hg hh
  · exact rationalGL_map_det_inv_pos _ (rationalMackeyRepresentativeLift_det_pos N h r)

theorem rationalMackeyRepresentativeProduct_map
    (N : ℕ) (g h : GL (Fin 2) ℚ) (r : rationalConjugateGroup N h) :
    (rationalMackeyRepresentativeProduct N g h r).map (algebraMap ℚ ℝ) =
      (g * h).map (algebraMap ℚ ℝ) * r.val⁻¹ := by
  unfold rationalMackeyRepresentativeProduct
  rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
    Matrix.GeneralLinearGroup.map_inv, rationalMackeyRepresentativeLift_map]

/-- A descended positive-rational Hecke trace agrees with the literal
rational trace of any rational lift of its real correspondence matrix. -/
theorem rationalPrincipalHeckeTrace_eq_rationalTrace_of_map
    (N : ℕ) (d : positiveRationalGLRealImage) (u : GL (Fin 2) ℚ)
    (hu : u.map (algebraMap ℚ ℝ) = d.val)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    letI : (rationalConjugateGroup N u).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N u
    rationalPrincipalHeckeTrace N d f =
      maassTraceFunction (H := principalCongruenceGL N)
        (rationalMaassPullbackInvariant_general (principalCongruenceGL N) u f) := by
  let v : GL (Fin 2) ℚ := positiveRationalHeckeLift d
  have hv : v.map (algebraMap ℚ ℝ) = d.val := by
    simpa only [v] using positiveRationalHeckeLift_map d
  have hdouble : DoubleCoset.setoid (principalCongruenceGL N : Set (GL (Fin 2) ℝ))
      (principalCongruenceGL N) (v.map (algebraMap ℚ ℝ))
      (u.map (algebraMap ℚ ℝ)) := by
    rw [hv, hu]
  simpa only [rationalPrincipalHeckeTrace, v] using
    (rationalPrincipalTrace_eq_of_principal_doubleCoset N v u hdouble f).symm

/-- The positive rational Hecke-pair element attached to a literal Mackey
representative, when both input correspondences preserve orientation. -/
noncomputable def rationalMackeyRepresentativeHeckeElement
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det)
    (r : rationalConjugateGroup N h) : positiveRationalGLRealImage :=
  positiveRationalHeckeElement (rationalMackeyRepresentativeProduct N g h r)
    (rationalMackeyRepresentativeProduct_det_pos N g h hg hh r)

@[simp] theorem rationalMackeyRepresentativeHeckeElement_val
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det)
    (r : rationalConjugateGroup N h) :
    (rationalMackeyRepresentativeHeckeElement N g h hg hh r).val =
      (rationalMackeyRepresentativeProduct N g h r).map (algebraMap ℚ ℝ) := rfl

/-- For orientation-preserving input correspondences, every actual rational
Mackey orbit has a principal positive-rational Hecke-coset label. -/
noncomputable def rationalMackeyOrbitToHeckeCoset
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det) :
    let P := principalCongruenceGL N
    let G := rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
    let H := rationalConjugateGroup N h
    let J := P.subgroupOf H
    Quotient (orbitRel J (H ⧸ G.subgroupOf H)) →
      HeckeCoset positiveRationalGLRealImage P P := by
  dsimp only
  let P : Subgroup (GL (Fin 2) ℝ) := principalCongruenceGL N
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let J : Subgroup H := P.subgroupOf H
  exact fun q => HeckeCoset.mk P P
    (rationalMackeyRepresentativeHeckeElement N g h hg hh q.out.out)

/-- Forgetting the positive-rational Hecke label recovers the canonical real
double-coset label of the same Mackey orbit. -/
theorem rationalMackeyOrbitToHeckeCoset_toDoubleCoset
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det) :
    let P := principalCongruenceGL N
    let G := rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
    let H := rationalConjugateGroup N h
    let J := P.subgroupOf H
    ∀ q : Quotient (orbitRel J (H ⧸ G.subgroupOf H)),
      heckeCosetToDoubleCoset positiveRationalGLRealImage P P
        (rationalMackeyOrbitToHeckeCoset N g h hg hh q) =
      rationalMackeyOrbitToDoubleCoset N g h q := by
  dsimp only
  let P : Subgroup (GL (Fin 2) ℝ) := principalCongruenceGL N
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let J : Subgroup H := P.subgroupOf H
  let a : GL (Fin 2) ℝ := (g * h).map (algebraMap ℚ ℝ)
  have hconj : ∀ c : H, c ∈ G.subgroupOf H → a * c.val⁻¹ * a⁻¹ ∈ P := by
    intro c hc
    simpa only [P, G, H, a] using rationalMackey_conjugate_inv_mem_principal N g h c hc
  have hJ : J.map H.subtype ≤ P := by
    simp only [J, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  intro q
  change DoubleCoset.mk P P
      ((rationalMackeyRepresentativeProduct N g h q.out.out).map (algebraMap ℚ ℝ)) =
    mackeyOrbitToDoubleCoset G H P a hconj J hJ q
  rw [rationalMackeyRepresentativeProduct_map]
  calc
    DoubleCoset.mk P P (a * q.out.out.val⁻¹) =
        mackeyRelativeCosetToDoubleCoset G H P a hconj q.out :=
      (mackeyRelativeCosetToDoubleCoset_eq_out G H P a hconj q.out).symm
    _ = mackeyOrbitToDoubleCoset G H P a hconj J hJ q :=
      (mackeyOrbitToDoubleCoset_eq_out G H P a hconj J hJ q).symm

end

end GaloisForLFunctions.RHTower
