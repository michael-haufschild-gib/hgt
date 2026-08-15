import GaloisForLFunctions.RHTower.ProlateGlobalBandEigen

/-!
# Every even Slepian eigenfunction is a finite sum of joint prolate modes

The even part of a Slepian band eigenspace is finite dimensional and carries the prolate
Sturm--Liouville action as a symmetric endomorphism.  The finite-dimensional spectral theorem
therefore supplies an orthonormal eigenbasis, and expanding an arbitrary even band eigenfunction in
that basis writes it as a finite real combination of smooth even functions that solve the prolate
differential equation.

This removes the spectral simplicity hypothesis from the passage between the band equation and the
differential equation: instead of a single mode one obtains a finite sum of modes, which is all the
downstream radial estimates require.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Real

namespace RHTower

/-- The even part of a live band eigenspace is finite dimensional. -/
theorem finiteDimensional_evenBandEigenspace {c lam : ℝ} (hlam : lam ≠ 0) :
    FiniteDimensional ℝ (evenBandEigenspace c lam) := by
  letI : FiniteDimensional ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam) :=
    GaloisForLFunctions.RHTower.finiteDimensional_bandEigenspace hlam
  let inclusion : evenBandEigenspace c lam →ₗ[ℝ]
      GaloisForLFunctions.RHTower.bandEigenspace c lam :=
    { toFun := fun f => ⟨f.1, f.2.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective inclusion ?_
  intro f g hfg
  apply Subtype.ext
  exact congrArg (fun h : GaloisForLFunctions.RHTower.bandEigenspace c lam => h.1) hfg

/-- A continuous even global band eigenfunction has its band class in the even eigenspace. -/
theorem bandClass_mem_evenBandEigenspace {c lam : ℝ} (hlam : lam ≠ 0) {ψ : ℝ → ℝ}
    (hψc : Continuous ψ) (hψeven : Function.Even ψ)
    (hψband : ∀ x : ℝ, bandTransform c ψ x = lam * ψ x) :
    GaloisForLFunctions.RHTower.bandClass ψ hψc ∈ evenBandEigenspace c lam := by
  have htransform : Continuous (bandTransform c ψ) :=
    GaloisForLFunctions.RHTower.continuous_bandTransform c hψc
  have hmul : Continuous fun x => lam * ψ x := continuous_const.mul hψc
  refine mem_evenBandEigenspace_iff.mpr ⟨?_, ?_⟩
  · have hclassEig :
        GaloisForLFunctions.RHTower.bandClass (bandTransform c ψ) htransform =
          GaloisForLFunctions.RHTower.bandClass (fun x => lam * ψ x) hmul := by
      apply Lp.ext
      filter_upwards [GaloisForLFunctions.RHTower.coeFn_bandClass (bandTransform c ψ) htransform,
        GaloisForLFunctions.RHTower.coeFn_bandClass (fun x => lam * ψ x) hmul] with x hx₁ hx₂
      rw [hx₁, hx₂]
      exact hψband x
    rw [GaloisForLFunctions.RHTower.bandOperatorL2_bandClass, hclassEig,
      GaloisForLFunctions.RHTower.bandClass_smul]
  · rw [eigenExtension_bandClass_eq_self_of_bandEigen hlam hψc hψband]
    exact hψeven

/-- **Finite joint-mode decomposition.**  A continuous even global Slepian eigenfunction is a finite
real combination of smooth even joint band/prolate eigenfunctions sharing its band eigenvalue. -/
theorem exists_joint_prolate_decomposition_of_even_bandEigen
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) {ψ : ℝ → ℝ}
    (hψc : Continuous ψ) (hψeven : Function.Even ψ)
    (hψband : ∀ x : ℝ, bandTransform c ψ x = lam * ψ x) :
    ∃ (m : ℕ) (coef eta : Fin m → ℝ) (Phi : Fin m → ℝ → ℝ),
      (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Phi j)) ∧
        (∀ j, Function.Even (Phi j)) ∧
        (∀ j x, bandTransform c (Phi j) x = lam * Phi j x) ∧
        (∀ j x, prolateSLAction c (Phi j) x = eta j * Phi j x) ∧
        (∀ x, ψ x = ∑ j, coef j * Phi j x) := by
  letI : FiniteDimensional ℝ (evenBandEigenspace c lam) :=
    finiteDimensional_evenBandEigenspace hlam
  set T := prolateOnEvenEigenspace hc hlam with hT
  have hsym : T.IsSymmetric := isSymmetric_prolateOnEvenEigenspace hc hlam
  set m : ℕ := Module.finrank ℝ (evenBandEigenspace c lam) with hm
  have hn : Module.finrank ℝ (evenBandEigenspace c lam) = m := rfl
  set basis := hsym.eigenvectorBasis hn with hbasis
  set eta : Fin m → ℝ := hsym.eigenvalues hn with heta
  set v : evenBandEigenspace c lam :=
    ⟨GaloisForLFunctions.RHTower.bandClass ψ hψc,
      bandClass_mem_evenBandEigenspace hlam hψc hψeven hψband⟩ with hv
  set bf : Fin m → GaloisForLFunctions.RHTower.bandEigenspace c lam :=
    fun j => ⟨(basis j).1, (basis j).2.1⟩ with hbf
  refine ⟨m, fun j => basis.repr v j, eta,
    fun j => GaloisForLFunctions.RHTower.eigenRep c lam (bf j), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j => GaloisForLFunctions.RHTower.contDiff_eigenRep hc hlam (bf j)
  · intro j
    exact (basis j).2.2
  · exact fun j x => GaloisForLFunctions.RHTower.bandTransform_eigenRep hlam (bf j) x
  · intro j x
    have hveq : T (basis j) = eta j • basis j := hsym.apply_eigenvectorBasis hn j
    have hvaleq :
        GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam (bf j) = eta j • bf j := by
      apply Subtype.ext
      exact congrArg (fun w : evenBandEigenspace c lam => w.1) hveq
    have hrepeq := congrArg
      (fun w : GaloisForLFunctions.RHTower.bandEigenspace c lam =>
        GaloisForLFunctions.RHTower.eigenRep c lam w) hvaleq
    rw [eigenRep_prolateOnEigenspace hc hlam] at hrepeq
    have hx := congrFun hrepeq x
    have hsmul : GaloisForLFunctions.RHTower.eigenRep c lam (eta j • bf j) x =
        eta j * GaloisForLFunctions.RHTower.eigenRep c lam (bf j) x :=
      GaloisForLFunctions.RHTower.eigenExtension_smul c lam (eta j) (bf j) x
    rw [hsmul] at hx
    exact hx
  · intro x
    have hrep : ψ = GaloisForLFunctions.RHTower.eigenExtension c lam
        (GaloisForLFunctions.RHTower.bandClass ψ hψc) :=
      (eigenExtension_bandClass_eq_self_of_bandEigen hlam hψc hψband).symm
    have hrepr : v = ∑ j, basis.repr v j • basis j := (basis.sum_repr v).symm
    have hsum : (v : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
        = ∑ j, basis.repr v j • ((basis j : evenBandEigenspace c lam) :
            GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) := by
      calc (v : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
          = ((∑ j, basis.repr v j • basis j : evenBandEigenspace c lam) :
              GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) := by rw [← hrepr]
        _ = ∑ j, basis.repr v j • ((basis j : evenBandEigenspace c lam) :
              GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) := by
              rw [Submodule.coe_sum]
              exact Finset.sum_congr rfl fun j _ => rfl
    have hmapsum : eigenExtensionLinearMap c lam
        (v : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
        = ∑ j, basis.repr v j •
            eigenExtensionLinearMap c lam
              ((basis j : evenBandEigenspace c lam) :
                GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) := by
      rw [hsum, map_sum]
      exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
    have hval := congrFun hmapsum x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hval
    exact (congrFun hrep x).trans hval

end RHTower
