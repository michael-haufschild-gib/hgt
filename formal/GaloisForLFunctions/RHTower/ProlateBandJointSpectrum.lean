import GaloisForLFunctions.RHTower.ProlateSeparationSimplicity
import GaloisForLFunctions.RHTower.ProlateSeparationEnergy
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Ordered joint spectrum inside a live even Slepian eigenspace

Every nonzero Slepian band eigenspace is finite dimensional.  Its even part is invariant under the
prolate Sturm--Liouville action, and that restricted action is symmetric.  Mathlib therefore gives
an ordered orthonormal eigenbasis.  Regular-even ODE uniqueness, already expressed by
`finrank_prolateOnEvenEigenspace_eigenspace_le_one`, rules out every repeated separation value.

Thus each live even band eigenspace carries a canonical finite, strictly decreasing list of
separation values.  This does not assume simplicity of the Slepian eigenvalue: any such
multiplicity is resolved into distinct joint prolate lines.
-/

noncomputable section

open Module

namespace RHTower

/-- The even part of every nonzero Slepian band eigenspace is finite dimensional. -/
theorem finiteDimensional_evenBandEigenspace {c lam : ℝ} (hlam : lam ≠ 0) :
    FiniteDimensional ℝ (evenBandEigenspace c lam) := by
  letI : FiniteDimensional ℝ
      (GaloisForLFunctions.RHTower.bandEigenspace c lam) :=
    GaloisForLFunctions.RHTower.finiteDimensional_bandEigenspace hlam
  let inclusion : evenBandEigenspace c lam →ₗ[ℝ]
      GaloisForLFunctions.RHTower.bandEigenspace c lam :=
    { toFun := fun f => ⟨f.1, f.2.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective inclusion fun f g hfg => by
    apply Subtype.ext
    exact congrArg
      (fun h : GaloisForLFunctions.RHTower.bandEigenspace c lam => h.1) hfg

/-- Ordered separation values carried by one live even band eigenspace. -/
noncomputable def evenBandSeparationValues
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    Fin (finrank ℝ (evenBandEigenspace c lam)) → ℝ := by
  letI : FiniteDimensional ℝ (evenBandEigenspace c lam) :=
    finiteDimensional_evenBandEigenspace hlam
  exact (isSymmetric_prolateOnEvenEigenspace hc hlam).eigenvalues rfl

/-- Canonical orthonormal joint-eigenvector basis inside one live even band eigenspace. -/
noncomputable def evenBandJointEigenbasis
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    OrthonormalBasis (Fin (finrank ℝ (evenBandEigenspace c lam))) ℝ
      (evenBandEigenspace c lam) := by
  letI : FiniteDimensional ℝ (evenBandEigenspace c lam) :=
    finiteDimensional_evenBandEigenspace hlam
  exact (isSymmetric_prolateOnEvenEigenspace hc hlam).eigenvectorBasis rfl

/-- Every vector of the canonical basis is an eigenvector of the restricted prolate action with
the correspondingly ordered separation value. -/
theorem prolateOnEvenEigenspace_evenBandJointEigenbasis
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (i : Fin (finrank ℝ (evenBandEigenspace c lam))) :
    prolateOnEvenEigenspace hc hlam (evenBandJointEigenbasis hc hlam i) =
      evenBandSeparationValues hc hlam i • evenBandJointEigenbasis hc hlam i := by
  letI : FiniteDimensional ℝ (evenBandEigenspace c lam) :=
    finiteDimensional_evenBandEigenspace hlam
  exact (isSymmetric_prolateOnEvenEigenspace hc hlam).apply_eigenvectorBasis rfl i

/-- Regular-even ODE uniqueness makes the ordered separation list injective. -/
theorem evenBandSeparationValues_injective
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    Function.Injective (evenBandSeparationValues hc hlam) := by
  letI : FiniteDimensional ℝ (evenBandEigenspace c lam) :=
    finiteDimensional_evenBandEigenspace hlam
  let A := prolateOnEvenEigenspace hc hlam
  let hA := isSymmetric_prolateOnEvenEigenspace hc hlam
  intro i j hij
  have hcard :
      Finset.card {k | hA.eigenvalues rfl k = hA.eigenvalues rfl i} ≤ 1 := by
    have heq := hA.card_filter_eigenvalues_eq rfl (hA.eigenvalues rfl i)
    exact (le_of_eq heq).trans
      (finrank_prolateOnEvenEigenspace_eigenspace_le_one
        hc hlam (hA.eigenvalues rfl i))
  apply Finset.card_le_one.mp hcard i
  · simp
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change evenBandSeparationValues hc hlam j = evenBandSeparationValues hc hlam i
    exact hij.symm

/-- The joint separation ladder inside a live even band eigenspace is strictly decreasing. -/
theorem evenBandSeparationValues_strictAnti
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    StrictAnti (evenBandSeparationValues hc hlam) := by
  letI : FiniteDimensional ℝ (evenBandEigenspace c lam) :=
    finiteDimensional_evenBandEigenspace hlam
  exact
    ((isSymmetric_prolateOnEvenEigenspace hc hlam).eigenvalues_antitone rfl).strictAnti_of_injective
      (evenBandSeparationValues_injective hc hlam)

/-- Smooth global representative of one canonical joint separation line. -/
noncomputable def evenBandJointProfile
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (i : Fin (finrank ℝ (evenBandEigenspace c lam))) : ℝ → ℝ :=
  let v := evenBandJointEigenbasis hc hlam i
  let f : GaloisForLFunctions.RHTower.bandEigenspace c lam := ⟨v.1, v.2.1⟩
  GaloisForLFunctions.RHTower.eigenRep c lam f

/-- The canonical joint profile is smooth, nonzero, even, and solves both eigenvalue equations
globally. -/
theorem evenBandJointProfile_spec
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (i : Fin (finrank ℝ (evenBandEigenspace c lam))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (evenBandJointProfile hc hlam i) ∧
      evenBandJointProfile hc hlam i ≠ 0 ∧
      Function.Even (evenBandJointProfile hc hlam i) ∧
      (∀ x : ℝ, bandTransform c (evenBandJointProfile hc hlam i) x =
        lam * evenBandJointProfile hc hlam i x) ∧
      ∀ x : ℝ, prolateSLAction c (evenBandJointProfile hc hlam i) x =
        evenBandSeparationValues hc hlam i * evenBandJointProfile hc hlam i x := by
  letI : FiniteDimensional ℝ (evenBandEigenspace c lam) :=
    finiteDimensional_evenBandEigenspace hlam
  let v : evenBandEigenspace c lam := evenBandJointEigenbasis hc hlam i
  let f : GaloisForLFunctions.RHTower.bandEigenspace c lam := ⟨v.1, v.2.1⟩
  let Phi : ℝ → ℝ := GaloisForLFunctions.RHTower.eigenRep c lam f
  have hvne : v ≠ 0 := (evenBandJointEigenbasis hc hlam).orthonormal.ne_zero i
  have hPhiNe : Phi ≠ 0 := by
    intro hzero
    have hclassZero : GaloisForLFunctions.RHTower.bandClass Phi
        (GaloisForLFunctions.RHTower.continuous_eigenRep c lam f) = 0 := by
      have hstep := GaloisForLFunctions.RHTower.bandClass_congr
        (GaloisForLFunctions.RHTower.continuous_eigenRep c lam f)
        continuous_const hzero
      rw [hstep]
      exact GaloisForLFunctions.RHTower.bandClass_zero _
    apply hvne
    apply Subtype.ext
    change f.1 = 0
    rw [← GaloisForLFunctions.RHTower.bandClass_eigenRep hlam f]
    exact hclassZero
  have hrestricted := prolateOnEvenEigenspace_evenBandJointEigenbasis hc hlam i
  have hbandRestricted :
      GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam f =
        evenBandSeparationValues hc hlam i • f := by
    apply Subtype.ext
    exact congrArg (fun w : evenBandEigenspace c lam => w.1) hrestricted
  have hrep := congrArg
    (fun w : GaloisForLFunctions.RHTower.bandEigenspace c lam =>
      GaloisForLFunctions.RHTower.eigenRep c lam w) hbandRestricted
  rw [eigenRep_prolateOnEigenspace hc hlam] at hrep
  have hprolate : ∀ x : ℝ, prolateSLAction c Phi x =
      evenBandSeparationValues hc hlam i * Phi x := by
    intro x
    have hx := congrFun hrep x
    have hsmul : GaloisForLFunctions.RHTower.eigenRep c lam
        (evenBandSeparationValues hc hlam i • f) x =
          evenBandSeparationValues hc hlam i *
            GaloisForLFunctions.RHTower.eigenRep c lam f x :=
      GaloisForLFunctions.RHTower.eigenExtension_smul c lam
        (evenBandSeparationValues hc hlam i) f x
    rw [hsmul] at hx
    exact hx
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
    (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      ∀ x : ℝ, prolateSLAction c Phi x = evenBandSeparationValues hc hlam i * Phi x
  exact ⟨GaloisForLFunctions.RHTower.contDiff_eigenRep hc hlam f, hPhiNe, v.2.2,
    GaloisForLFunctions.RHTower.bandTransform_eigenRep hlam f, hprolate⟩

/-- Every member of the ordered joint separation ladder is nonpositive. -/
theorem evenBandSeparationValues_nonpos
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (i : Fin (finrank ℝ (evenBandEigenspace c lam))) :
    evenBandSeparationValues hc hlam i ≤ 0 := by
  obtain ⟨hsm, hne, _heven, hband, heig⟩ := evenBandJointProfile_spec hc hlam i
  exact GaloisForLFunctions.RHTower.prolateSeparation_nonpos_of_global_joint
    hlam hsm hne hband heig

end RHTower

end
