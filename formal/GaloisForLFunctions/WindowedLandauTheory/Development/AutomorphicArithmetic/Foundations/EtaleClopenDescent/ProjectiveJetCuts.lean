import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ClosedCutsDimension
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveFirstJets

/-! Prescribed first jets can be retained while cutting the complement of
the chosen denominator chart down to the prescribed points. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace
open UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [Infinite K] {X : Scheme.{0}} [IsIntegral X] [NoetherianSpace X]
  {s : X ⟶ Spec (CommRingCat.of K)} {N d : ℕ}
  {l : MvPolynomial (Fin (N + 1)) K}

private abbrev Grade := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

/-- Choose a denominator that vanishes to second order at each prescribed
point. Then d numerators can realize their prescribed jets and have no
other common zero outside the denominator chart. -/
theorem exists_forms_cutting_outside_chart (i : X ⟶ PSpace K N) [IsClosedImmersion i]
    (hi : i ≫ PSpace.str K N = s) (hl : l.IsHomogeneous 1)
    (S : Finset (X.BaseFieldPointOver K s)) (hS : ∀ y ∈ S, y.hom default ∈ formBasicOpen i l)
    (hgen : ∀ y ∈ S, genericPoint X ≠ y.hom default)
    (hd : topologicalKrullDim X < (d + 1 : ℕ))
    (t : Fin d → S → SectionRing s (formBasicOpen i l)) :
    ∃ (n : ℕ) (h : Grade (K := K) (N := N) n) (g : Fin d → Grade (K := K) (N := N) n),
      0 < n ∧ genericPoint X ∈ formBasicOpen i h.1 ∧
      (∀ y : S, projectivePowerRatio i hl n h.1 h.2 ∈
        RingHom.ker (affinePointEval y.1 (hS y.1 y.2)).toRingHom ^ 2) ∧
      (∀ j (y : S), let r : SectionRing s (formBasicOpen i l) :=
          projectivePowerRatio i hl n (g j).1 (g j).2
        r - t j y ∈ RingHom.ker (affinePointEval y.1 (hS y.1 y.2)).toRingHom ^ 2) ∧
      ∀ x : X, x ∉ formBasicOpen i h.1 → (∀ j, x ∉ formBasicOpen i (g j).1) →
        ∃ y ∈ S, x = y.hom default := by
  classical
  obtain ⟨b, hb⟩ := exists_homogeneous_firstJets i hl S hS t
  let n := max b (2 * S.card) + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnb : b ≤ n := le_trans (le_max_left _ _) (Nat.le_succ _)
  have hnS : 2 * S.card ≤ n := le_trans (le_max_right _ _) (Nat.le_succ _)
  choose g₀ hg₀ using hb n hnb
  obtain ⟨h, hh, hjet⟩ := exists_form_zero_firstJets_avoiding i hi hl S hS n hnS (genericPoint X) hgen
  let V := formBasicOpen i h.1
  let C := (V : Set X)ᶜ
  have hC : topologicalKrullDim C < d := by
    apply topologicalKrullDim_closedCut_lt V.isOpen.isClosed_compl _ d hd
    intro Z hZ hle
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    exact (hle (hZ.symm ▸ Set.mem_univ (genericPoint X))) hh
  let D : Set C := {x | ∀ y ∈ S, x.1 ≠ y.hom default}
  have hD : topologicalKrullDim D < d := (topologicalKrullDim_subspace_le C D).trans_lt hC
  let F := Grade (K := K) (N := N) n
  let A := SectionRing s (formBasicOpen i l)
  let J (j : Fin d) : Set F :=
    {f | ∀ y : S, let r : A := projectivePowerRatio i hl n f.1 f.2
      r - t j y ∈ RingHom.ker (affinePointEval y.1 (hS y.1 y.2)).toRingHom ^ 2}
  let π (x : D) : X := x.1.1
  let Z (f : F) : Set D := π ⁻¹' (formBasicOpen i f.1 : Set X)ᶜ
  have hZ (f : F) : IsClosed (Z f) :=
    (formBasicOpen i f.1).isOpen.isClosed_compl.preimage
      (continuous_subtype_val.comp continuous_subtype_val)
  have hav (j : Fin d) (T : Finset D) : ∃ f ∈ J j, ∀ x ∈ T, x ∉ Z f := by
    have hT (x : X) (hx : x ∈ T.image π) : ∀ y ∈ S, x ≠ y.hom default := by
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
      exact z.2
    obtain ⟨f, hf, hfg⟩ := exists_form_firstJets_avoiding i hi hl S hS hnS hn
      (g₀ j) (T.image π) hT
    refine ⟨f, fun y => ?_, fun x hx hzero => hzero (hf (π x) (Finset.mem_image_of_mem π hx))⟩
    let a : A := projectivePowerRatio i hl n f.1 f.2
    let a₀ : A := projectivePowerRatio i hl n (g₀ j).1 (g₀ j).2
    have he : a - t j y = (a - a₀) + (a₀ - t j y) := by ring
    change a - t j y ∈ _
    rw [he]
    exact Ideal.add_mem _ (hfg y) (hg₀ j y)
  obtain ⟨g, hg, hgz⟩ := exists_cuts_empty_intersection d J Z hZ hD hav
  refine ⟨n, h, g, hn, hh, hjet, hg, fun x hx hgx => ?_⟩
  by_contra! hy
  obtain ⟨j, hj⟩ := hgz ⟨⟨x, hx⟩, hy⟩
  exact hj (hgx j)

end GlobalTheory.SchemeCohomology
