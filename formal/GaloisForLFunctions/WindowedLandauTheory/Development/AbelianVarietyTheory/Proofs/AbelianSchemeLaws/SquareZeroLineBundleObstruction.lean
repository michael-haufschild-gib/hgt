import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AffineQuotientSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.RefinedLineBundleGenerators
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionPullback
import Mathlib.Tactic.Ring

/-! Local unit lifts of a trivialization differ by an additive defect multiplied by the
square-zero parameter. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.SchemeCohomology GlobalTheory.LineBundleSections

namespace GlobalTheory.AbLaw.SmallExtension

variable {R : Type} [CommRing R] {X Y : Scheme.{0}} {L : LB X}
  {p : X ⟶ Spec (CommRingCat.of R)} {ε : R}
  {π : Y ⟶ X} {f : Y ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}

private theorem exists_relative_defect {A : Type} [CommRing A] {x y e d : A}
    (hy : IsUnit y) (h : x - y = e * d) : ∃ a : A, x = y * (1 + e * a) := by
  obtain ⟨v, hv⟩ := hy.exists_right_inv
  exact ⟨v * d, by linear_combination h - (e * d) * hv⟩

/-- The error in gluing the lifted units is the indicated multiple of the parameter. -/
def LiftDefect {I : Type} (W : I → X.Opens) (c : I → L.ι) (hle : ∀ i, W i ≤ L.U (c i))
    (u : ∀ i, Γ(X, W i)) (α : ∀ i j, Γ(X, W i ⊓ W j)) : Prop :=
  ∀ i j,
    let V := W i ⊓ W j
    letI := sectionAlgebra p V
    resG X inf_le_left (u i) =
      resG X (inf_le_inf (hle i) (hle j)) (L.g (c i) (c j)).val *
        resG X inf_le_right (u j) * (1 + algebraMap R Γ(X, V) ε * α i j)

/-- On affine charts refining the bundle charts, lift a quotient trivialization to units.
Their ratios on overlaps have the form `1 + ε * α i j`. -/
theorem exists_local_lifts (H : IsPullback π f p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    (hε : ε * ε = 0) [X.IsSeparated] (t : (L.pull π).Gen) (ht : t.IsGen)
    {I : Type} (W : I → X.Opens) (c : I → L.ι) (hle : ∀ i, W i ≤ L.U (c i))
    (haff : ∀ i, IsAffineOpen (W i)) :
    ∃ (u : ∀ i, Γ(X, W i)) (α : ∀ i j, Γ(X, W i ⊓ W j)),
      (∀ i, IsUnit (u i)) ∧ LiftDefect (p := p) (ε := ε) W c hle u α := by
  let M := L.pull π
  let k (i : I) : M.ι := fun _ => c i
  have hπ (i : I) : π ⁻¹ᵁ W i ≤ M.U (k i) :=
    (π.preimage_mono (hle i)).trans (pull_chart L π (c i)).ge
  choose u hu using fun i => app_surjective_of_quotient H (haff i)
    (resG Y (hπ i) (t.s (k i)).val)
  have hunit (i : I) : IsUnit (u i) :=
    isUnit_of_app_of_square_zero H (haff i) hε (by
      rw [hu i]
      exact (t.s (k i)).isUnit.map (resG Y (hπ i)))
  suffices key : ∀ i j, ∃ α : Γ(X, W i ⊓ W j),
      let V := W i ⊓ W j
      letI := sectionAlgebra p V
      resG X inf_le_left (u i) =
        resG X (inf_le_inf (hle i) (hle j)) (L.g (c i) (c j)).val *
          resG X inf_le_right (u j) * (1 + algebraMap R Γ(X, V) ε * α) by
    choose α hα using key
    exact ⟨u, α, hunit, hα⟩
  intro i j
  let V := W i ⊓ W j
  let V' := π ⁻¹ᵁ V
  letI := sectionAlgebra p V
  have hi : V' ≤ π ⁻¹ᵁ L.U (c i) := π.preimage_mono (inf_le_left.trans (hle i))
  have hj : V' ≤ π ⁻¹ᵁ L.U (c j) := π.preimage_mono (inf_le_right.trans (hle j))
  let g := resG X (inf_le_inf (hle i) (hle j)) (L.g (c i) (c j)).val
  have he (a : I) (h : V ≤ W a) :
      π.appLE (W a) V' (π.preimage_mono h) (u a) =
        resG Y ((π.preimage_mono h).trans (hπ a)) (t.s (k a)).val := by
    have e := congrArg (resG Y (π.preimage_mono h)) (hu a)
    simpa only [Scheme.Hom.app_eq_appLE, resG_appLE, resG_resG] using e
  have hz : π.app V (resG X inf_le_left (u i) - g * resG X inf_le_right (u j)) = 0 := by
    rw [Scheme.Hom.app_eq_appLE, map_sub, map_mul, sub_eq_zero]
    dsimp only [g]
    rw [appLE_resG, appLE_resG, appLE_resG, he i inf_le_left, he j inf_le_right]
    exact pulledGenerator_compat ht hi hj
  obtain ⟨d, hd⟩ := exists_eq_mul_of_app_eq_zero H ((haff i).inf (haff j)) hz
  exact exists_relative_defect
    (((L.g (c i) (c j)).isUnit.map _).mul ((hunit j).map _)) hd

section Cocycle

variable {I : Type} {W : I → X.Opens} {c : I → L.ι} {hle : ∀ i, W i ≤ L.U (c i)}
  {u : ∀ i, Γ(X, W i)} {α : ∀ i j, Γ(X, W i ⊓ W j)}

theorem LiftDefect.restrict (h : LiftDefect (p := p) (ε := ε) W c hle u α)
    {i j : I} {V : X.Opens} (hi : V ≤ W i) (hj : V ≤ W j) :
    letI := sectionAlgebra p V
    resG X hi (u i) =
      resG X (le_inf (hi.trans (hle i)) (hj.trans (hle j))) (L.g (c i) (c j)).val *
        resG X hj (u j) * (1 + algebraMap R Γ(X, V) ε * resG X (le_inf hi hj) (α i j)) := by
  have e := congrArg (resG X (le_inf hi hj)) (h i j)
  simp only [map_mul, map_add, map_one, resG_resG] at e
  letI := sectionAlgebra p (W i ⊓ W j)
  letI := sectionAlgebra p V
  have hc : resG X (le_inf hi hj) (algebraMap R Γ(X, W i ⊓ W j) ε) =
      algebraMap R Γ(X, V) ε :=
    (sectionRes p (homOfLE (le_inf hi hj))).commutes ε
  rwa [hc] at e

private theorem mul_add_sub_eq_zero_of_defects {A : Type} [CommRing A]
    {e x y z g g' g'' a b d : A} (he : e * e = 0)
    (hxy : x = g * y * (1 + e * a)) (hyz : y = g' * z * (1 + e * b))
    (hxz : x = g'' * z * (1 + e * d)) (hg : g * g' = g'') (hu : IsUnit (g'' * z)) :
    e * (a + b - d) = 0 := by
  have h : g'' * z * ((1 + e * a) * (1 + e * b) - (1 + e * d)) = 0 := by
    rw [mul_sub, ← hxz, sub_eq_zero, hxy, hyz, ← hg]
    ring
  have h' := hu.mul_right_eq_zero.1 h
  linear_combination h' - (a * b) * he

/-- On the closed fibre of a flat family the overlap defects satisfy the additive
Čech cocycle equation. -/
theorem LiftDefect.cocycle_on_closed_fibre [IsLocalRing R] [Flat p] [X.IsSeparated]
    (h : LiftDefect (p := p) (ε := ε) W c hle u α) (hL : L.IsLB)
    (haff : ∀ i, IsAffineOpen (W i)) (hunit : ∀ i, IsUnit (u i))
    (hne : ε ≠ 0) (hm : ε ∈ IsLocalRing.maximalIdeal R)
    (hann : ∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0)
    {Z : Scheme.{0}} {q : Z ⟶ X} {s : Z ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}
    (H : IsPullback q s p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (i j k : I) :
    let V := W i ⊓ W j ⊓ W k
    q.app V (resG X inf_le_left (α i j)) +
      q.app V (resG X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (α j k)) =
        q.app V (resG X (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (α i k)) := by
  let V := W i ⊓ W j ⊓ W k
  letI := sectionAlgebra p V
  have hi : V ≤ W i := inf_le_left.trans inf_le_left
  have hj : V ≤ W j := inf_le_left.trans inf_le_right
  have hk : V ≤ W k := inf_le_right
  let e := algebraMap R Γ(X, V) ε
  have he : e * e = 0 := by rw [← map_mul, hann ε hm, map_zero]
  have hg := cocycle_on hL (hi.trans (hle i)) (hj.trans (hle j)) (hk.trans (hle k))
  have hu : IsUnit
      (resG X (le_inf (hi.trans (hle i)) (hk.trans (hle k))) (L.g (c i) (c k)).val *
        resG X hk (u k)) :=
    ((L.g (c i) (c k)).isUnit.map _).mul ((hunit k).map _)
  have hz := mul_add_sub_eq_zero_of_defects he (h.restrict hi hj) (h.restrict hj hk)
    (h.restrict hi hk) hg hu
  have hz' := (mul_scalar_eq_zero_iff H (((haff i).inf (haff j)).inf (haff k))
    hne hann _).1 hz
  simpa only [map_sub, map_add, sub_eq_zero] using hz'

private theorem corrected_defect {A : Type} [CommRing A] {e x y g a b d : A}
    (he : e * e = 0) (h : x = g * y * (1 + e * a)) (hzero : e * (a - (b - d)) = 0) :
    x * (1 - e * b) = g * (y * (1 - e * d)) := by
  rw [h]
  calc
    _ = g * (y * (1 - e * d)) + g * y * (e * (a - (b - d)) - e * e * (a * b)) := by
      ring
    _ = _ := by simp only [hzero, he, zero_mul, sub_zero, mul_zero, add_zero]

/-- A coboundary on the closed fibre can be lifted to corrections of the local units. -/
theorem LiftDefect.exists_gen_of_coboundary [IsLocalRing R] [Flat p] [X.IsSeparated]
    (h : LiftDefect (p := p) (ε := ε) W c hle u α) (hL : L.IsLB)
    (hcov : ⨆ i, W i = ⊤) (haff : ∀ i, IsAffineOpen (W i)) (hunit : ∀ i, IsUnit (u i))
    (hne : ε ≠ 0) (hm : ε ∈ IsLocalRing.maximalIdeal R)
    (hann : ∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0)
    {Z : Scheme.{0}} {q : Z ⟶ X} {s : Z ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}
    (H : IsPullback q s p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (β : ∀ i, Γ(Z, q ⁻¹ᵁ W i))
    (hβ : ∀ i j, q.app (W i ⊓ W j) (α i j) =
      resG Z (q.preimage_mono inf_le_left) (β i) -
        resG Z (q.preimage_mono inf_le_right) (β j)) :
    ∃ t : L.Gen, t.IsGen := by
  choose b hb using fun i => app_surjective_of_quotient H (haff i) (β i)
  let u' (i : I) : Γ(X, W i) :=
    letI := sectionAlgebra p (W i)
    u i * (1 - algebraMap R Γ(X, W i) ε * b i)
  have hε : ε * ε = 0 := hann ε hm
  have hu (i : I) : IsUnit (u' i) := by
    letI := sectionAlgebra p (W i)
    let e := algebraMap R Γ(X, W i) ε
    have he : e * e = 0 := by rw [← map_mul, hε, map_zero]
    refine (hunit i).mul (IsUnit.of_mul_eq_one (1 + e * b i) ?_)
    linear_combination -(b i * b i) * he
  refine exists_gen_of_refinement hL W hcov c hle u' hu fun i j => ?_
  let V := W i ⊓ W j
  letI := sectionAlgebra p V
  have hzero : q.app V (α i j - (resG X inf_le_left (b i) - resG X inf_le_right (b j))) = 0 := by
    have hres (a : I) (h : V ≤ W a) :
        q.app V (resG X h (b a)) = resG Z (q.preimage_mono h) (β a) := by
      rw [← hb a]
      simp only [Scheme.Hom.app_eq_appLE, appLE_resG, resG_appLE]
    rw [map_sub, map_sub, hres, hres, hβ, sub_self]
  have hz := (mul_scalar_eq_zero_iff H ((haff i).inf (haff j)) hne hann _).2 hzero
  let e := algebraMap R Γ(X, V) ε
  have he : e * e = 0 := by rw [← map_mul, hε, map_zero]
  letI := sectionAlgebra p (W i)
  letI := sectionAlgebra p (W j)
  have hleft : resG X (inf_le_left : V ≤ W i) (algebraMap R Γ(X, W i) ε) = e :=
    (sectionRes p (homOfLE (inf_le_left : V ≤ W i))).commutes ε
  have hright : resG X (inf_le_right : V ≤ W j) (algebraMap R Γ(X, W j) ε) = e :=
    (sectionRes p (homOfLE (inf_le_right : V ≤ W j))).commutes ε
  simp only [u', map_mul, map_sub, map_one, hleft, hright]
  exact corrected_defect he (h i j) hz

end Cocycle

end GlobalTheory.AbLaw.SmallExtension
