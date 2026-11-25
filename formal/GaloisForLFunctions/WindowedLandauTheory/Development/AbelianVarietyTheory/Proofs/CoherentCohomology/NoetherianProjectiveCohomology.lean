import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.RingProjectiveTwistFiniteness
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveCoherentPresentation
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BiproductCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BiproductSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CoherentKernels
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CohomologyExactSequence

/-! A finite presentation by negative twists and descending induction on
cohomological degree give finiteness for coherent modules on projective space. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HTGeometry
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.SchemeCohomology.RingPolynomialCech

open UpperTheory.Cb

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type) [CommRing K] [IsNoetherianRing K] (N : ℕ)

private abbrev X := PSpace K N
private abbrev U := PSpace.coordinateOpen K N
private abbrev twist (m : ℕ) := pspaceTwist K N (-(m : ℤ))

private theorem twist_finite_sections (m : ℕ) (i : Fin (N + 1)) :
    Module.Finite Γ(X K N, U K N i) Γ(twist K N m, U K N i) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K
  have hv : MvPolynomial.X i ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X K i
  let V := U K N i
  let s := (twist K N m).presheaf.map (homOfLE (le_refl V)).op
    (ProjTwist.coordinatePower hv (-(m : ℤ)))
  let f : Γ(X K N, V) →ₗ[Γ(X K N, V)] Γ(twist K N m, V) :=
    { toFun := fun a => a • s
      map_add' := fun a b => add_smul a b s
      map_smul' := fun a b => mul_smul a b s }
  exact Module.Finite.of_surjective f (ProjTwist.coordinatePower_basis hv (-(m : ℤ)) (le_refl V)).2

private abbrev finiteCohomology (F : (X K N).Modules) (q : ℕ) : Prop :=
  letI := sectionAlgebra (PSpace.str K N) ⊤
  letI := Module.compHom (CohomologyOn F ⊤ q) (algebraMap K Γ(X K N, ⊤))
  Module.Finite K (CohomologyOn F ⊤ q)

private theorem twistBiproduct_finiteCohomology {I : Type} [Fintype I] (m : I → ℕ) (q : ℕ) :
    finiteCohomology K N (⨁ fun i => twist K N (m i)) q := by
  letI := sectionAlgebra (PSpace.str K N) ⊤
  let f (i : I) := twist K N (m i)
  let A := CohomologyOn (⨁ f) ⊤ q
  let B (i : I) := CohomologyOn (f i) ⊤ q
  letI : Module K A := Module.compHom A (algebraMap K Γ(X K N, ⊤))
  letI (i : I) : Module K (B i) := Module.compHom (B i) (algebraMap K Γ(X K N, ⊤))
  haveI (i : I) : Module.Finite K (B i) := pspaceTwist_cohomologyFinite K N (m i) q
  let e := CohomologyOn.biproductEquiv f ⊤ q
  let L : A →ₗ[K] (∀ i, B i) :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro r a
        exact e.map_smul (algebraMap K Γ(X K N, ⊤) r) a }
  exact Module.Finite.of_injective L e.injective

private theorem finiteCohomology_of_shortExact {S : ShortComplex (X K N).Modules}
    (hS : S.ShortExact) (q : ℕ)
    (h₂ : finiteCohomology K N S.X₂ q) (h₁ : finiteCohomology K N S.X₁ (q + 1)) :
    finiteCohomology K N S.X₃ q := by
  letI := sectionAlgebra (PSpace.str K N) ⊤
  let A := CohomologyOn S.X₂ ⊤ q
  let B := CohomologyOn S.X₃ ⊤ q
  let C := CohomologyOn S.X₁ ⊤ (q + 1)
  letI : Module K A := Module.compHom A (algebraMap K Γ(X K N, ⊤))
  letI : Module K B := Module.compHom B (algebraMap K Γ(X K N, ⊤))
  letI : Module K C := Module.compHom C (algebraMap K Γ(X K N, ⊤))
  letI : Module.Finite K A := h₂
  letI : Module.Finite K C := h₁
  let g := CohomologyOn.map S.g ⊤ q
  let δ := CohomologyOn.boundary hS ⊤ q
  let gK : A →ₗ[K] B :=
    { g.toAddMonoidHom with map_smul' := fun r x => g.map_smul (algebraMap K Γ(X K N, ⊤) r) x }
  let δK : B →ₗ[K] C :=
    { δ.toAddMonoidHom with map_smul' := fun r x => δ.map_smul (algebraMap K Γ(X K N, ⊤) r) x }
  exact finite_of_exact_noetherian gK δK (CohomologyOn.exact_map_boundary hS ⊤ q)

/-- A quasi-coherent module with finite sections on the coordinate charts
has finite cohomology over the Noetherian base. -/
theorem pspace_cohomologyFinite (F : (X K N).Modules) [F.IsQuasicoherent]
    (hF : ∀ i, Module.Finite Γ(X K N, U K N i) Γ(F, U K N i)) (q : ℕ) :
    letI := sectionAlgebra (PSpace.str K N) ⊤
    letI := Module.compHom (CohomologyOn F ⊤ q) (algebraMap K Γ(X K N, ⊤))
    Module.Finite K (CohomologyOn F ⊤ q) := by
  letI : IsLocallyNoetherian (X K N) := PSpace.isLocallyNoetherian K N
  suffices h : ∀ (b n : ℕ), N + 1 ≤ b + n → ∀ (M : (X K N).Modules) [M.IsQuasicoherent],
      (∀ i, Module.Finite Γ(X K N, U K N i) Γ(M, U K N i)) → finiteCohomology K N M n by
    exact h (N + 1) q (by omega) F hF
  intro b
  induction b with
  | zero =>
    intro n hn M _ _
    obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
    let H := CohomologyOn M ⊤ (d + 1)
    letI := sectionAlgebra (PSpace.str K N) ⊤
    letI := Module.compHom H (algebraMap K Γ(X K N, ⊤))
    letI : Subsingleton H :=
      ⟨fun x y => (pspaceCohomology_eq_zero_above K N M d (by omega) x).trans
        (pspaceCohomology_eq_zero_above K N M d (by omega) y).symm⟩
    change Module.Finite K H
    infer_instance
  | succ b ih =>
    intro n hn M _ hM
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K
    have hv (i : Fin (N + 1)) : MvPolynomial.X i ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X K i
    obtain ⟨I, hI, m, φ, hφ⟩ := exists_epi_twistCoproduct hv
      (PSpace.iSup_coordinateOpen K N) M hM
    letI := hI
    let f (i : I) := twist K N (m i)
    let e := biproduct.isoCoproduct f
    let π : (⨁ f) ⟶ M := e.hom ≫ φ
    have he : Epi e.hom := @IsIso.epi_of_iso _ _ _ _ e.hom e.isIso_hom
    have hπ : Epi π := @epi_comp _ _ _ _ _ e.hom he φ hφ
    let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel (kernelIsKernel π))
        (inferInstanceAs (Mono (kernel.ι π))) hπ
    letI : (⨁ f).IsQuasicoherent := biproduct_isQuasicoherent f
      (fun i => pspaceTwist_isQuasicoherent K N (-(m i : ℤ)))
    letI : (kernel π).IsQuasicoherent := kernel_isQuasicoherent π
    have hk (i : Fin (N + 1)) : Module.Finite Γ(X K N, U K N i) Γ(kernel π, U K N i) := by
      letI := biproduct_sections_finite f (U K N i) (fun j => twist_finite_sections K N (m j) i)
      have ha := PSpace.isAffineOpen_coordinateInter K N (Finset.singleton_nonempty i)
      rw [coverInter_singleton, top_inf_eq] at ha
      exact kernel_sections_finite π ha
    exact finiteCohomology_of_shortExact K N hS n (twistBiproduct_finiteCohomology K N m n)
      (ih (n + 1) (by omega) (kernel π) hk)

end GlobalTheory.SchemeCohomology.RingPolynomialCech
