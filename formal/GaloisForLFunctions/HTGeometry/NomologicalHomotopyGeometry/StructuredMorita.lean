import GaloisForLFunctions.HTGeometry.CochainComplexCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Structured Morita invariance

Strict connection-preserving equivalence conjugates curvature and every covariant curvature jet.
This file also proves the associated kernel/range rank invariance, fibrewise injectivity of
pullback along a surjection, and invariance of Spencer-type complexes and their cohomology under a
degreewise chain equivalence.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.StructuredMorita

open Module

section Curvature

variable {k E₁ E₂ : Type*} [Field k]
variable [AddCommGroup E₁] [Module k E₁] [AddCommGroup E₂] [Module k E₂]

/-- Algebraic content of an intertwining structured bundle equivalence. -/
def Intertwines (Φ : E₁ ≃ₗ[k] E₂) (A : Module.End k E₁) (B : Module.End k E₂) : Prop :=
  Φ.toLinearMap.comp A = B.comp Φ.toLinearMap

/-- Intertwining is preserved by composition. -/
theorem intertwines_comp (Φ : E₁ ≃ₗ[k] E₂) {A C : Module.End k E₁}
    {B D : Module.End k E₂} (hA : Intertwines Φ A B) (hC : Intertwines Φ C D) :
    Intertwines Φ (A.comp C) (B.comp D) := by
  unfold Intertwines at *
  ext x
  have hAx := LinearMap.congr_fun hA (C x)
  have hCx := LinearMap.congr_fun hC x
  simp only [LinearMap.comp_apply] at hAx hCx ⊢
  rw [hAx, hCx]

/-- Intertwining is preserved by subtraction. -/
theorem intertwines_sub (Φ : E₁ ≃ₗ[k] E₂) {A C : Module.End k E₁}
    {B D : Module.End k E₂} (hA : Intertwines Φ A B) (hC : Intertwines Φ C D) :
    Intertwines Φ (A - C) (B - D) := by
  unfold Intertwines at *
  ext x
  have hAx := LinearMap.congr_fun hA x
  have hCx := LinearMap.congr_fun hC x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub] at hAx hCx ⊢
  rw [hAx, hCx]

/-- Curvature of a connection operator. -/
def curvature (N : Module.End k E₁) : Module.End k E₁ :=
  N.comp N

/-- Induced covariant derivative on endomorphism-valued curvature data. -/
def covariantDerivative (N R : Module.End k E₁) : Module.End k E₁ :=
  N.comp R - R.comp N

/-- Full covariant curvature-jet tower. -/
def curvatureJet (N R : Module.End k E₁) : ℕ → Module.End k E₁
  | 0 => R
  | n + 1 => covariantDerivative N (curvatureJet N R n)

/-- Squaring a connection-intertwining equation gives curvature conjugacy. -/
theorem curvature_intertwines (Φ : E₁ ≃ₗ[k] E₂) (N₁ : Module.End k E₁)
    (N₂ : Module.End k E₂) (h : Intertwines Φ N₁ N₂) :
    Intertwines Φ (curvature N₁) (curvature N₂) :=
  intertwines_comp Φ h h

/-- Covariant differentiation respects a structured equivalence. -/
theorem covariantDerivative_intertwines (Φ : E₁ ≃ₗ[k] E₂) {N₁ R₁ : Module.End k E₁}
    {N₂ R₂ : Module.End k E₂} (hN : Intertwines Φ N₁ N₂)
    (hR : Intertwines Φ R₁ R₂) :
    Intertwines Φ (covariantDerivative N₁ R₁) (covariantDerivative N₂ R₂) :=
  intertwines_sub Φ (intertwines_comp Φ hN hR) (intertwines_comp Φ hR hN)

/-- Every covariant curvature jet is conjugate on the common refinement. -/
theorem curvatureJet_intertwines (Φ : E₁ ≃ₗ[k] E₂) {N₁ R₁ : Module.End k E₁}
    {N₂ R₂ : Module.End k E₂} (hN : Intertwines Φ N₁ N₂)
    (hR : Intertwines Φ R₁ R₂) :
    ∀ n, Intertwines Φ (curvatureJet N₁ R₁ n) (curvatureJet N₂ R₂ n) := by
  intro n
  induction n with
  | zero => exact hR
  | succ n ih => exact covariantDerivative_intertwines Φ hN ih

/-- Strict structured cover equivalence data retained by the card: connection, differential,
filtration, cyclic pairing, and source marking. -/
structure StructuredEquiv
    (N₁ Q₁ : Module.End k E₁) (N₂ Q₂ : Module.End k E₂)
    (F₁ : ℕ → Submodule k E₁) (F₂ : ℕ → Submodule k E₂)
    (pair₁ : E₁ →ₗ[k] E₁ →ₗ[k] k) (pair₂ : E₂ →ₗ[k] E₂ →ₗ[k] k)
    (source₁ : E₁) (source₂ : E₂) where
  Φ : E₁ ≃ₗ[k] E₂
  connection : Intertwines Φ N₁ N₂
  differential : Intertwines Φ Q₁ Q₂
  filtration : ∀ n x, x ∈ F₁ n ↔ Φ x ∈ F₂ n
  pairing : ∀ x y, pair₂ (Φ x) (Φ y) = pair₁ x y
  source : Φ source₁ = source₂

/-- Structured curvature descent, equation `(SM.6)`. -/
theorem StructuredEquiv.curvature_intertwines
    {N₁ Q₁ : Module.End k E₁} {N₂ Q₂ : Module.End k E₂}
    {F₁ : ℕ → Submodule k E₁} {F₂ : ℕ → Submodule k E₂}
    {pair₁ : E₁ →ₗ[k] E₁ →ₗ[k] k} {pair₂ : E₂ →ₗ[k] E₂ →ₗ[k] k}
    {source₁ : E₁} {source₂ : E₂}
    (S : StructuredEquiv N₁ Q₁ N₂ Q₂ F₁ F₂ pair₁ pair₂ source₁ source₂) :
    Intertwines S.Φ (curvature N₁) (curvature N₂) :=
  HTGeometry.NomologicalHomotopyGeometry.StructuredMorita.curvature_intertwines
    S.Φ N₁ N₂ S.connection

/-- Structured curvature-jet descent, equation `(SM.7)`. -/
theorem StructuredEquiv.curvatureJet_intertwines
    {N₁ Q₁ : Module.End k E₁} {N₂ Q₂ : Module.End k E₂}
    {F₁ : ℕ → Submodule k E₁} {F₂ : ℕ → Submodule k E₂}
    {pair₁ : E₁ →ₗ[k] E₁ →ₗ[k] k} {pair₂ : E₂ →ₗ[k] E₂ →ₗ[k] k}
    {source₁ : E₁} {source₂ : E₂}
    (S : StructuredEquiv N₁ Q₁ N₂ Q₂ F₁ F₂ pair₁ pair₂ source₁ source₂) :
    ∀ n, Intertwines S.Φ (curvatureJet N₁ (curvature N₁) n)
      (curvatureJet N₂ (curvature N₂) n) :=
  HTGeometry.NomologicalHomotopyGeometry.StructuredMorita.curvatureJet_intertwines
    S.Φ S.connection S.curvature_intertwines

/-- Equivalence induced on kernels of conjugate endomorphisms. -/
def kernelEquiv (Φ : E₁ ≃ₗ[k] E₂) (A : Module.End k E₁) (B : Module.End k E₂)
    (h : Intertwines Φ A B) : LinearMap.ker A ≃ₗ[k] LinearMap.ker B where
  toFun x := ⟨Φ x, by
    have hx := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply] at hx
    change B (Φ.toLinearMap x) = 0
    calc
      B (Φ.toLinearMap x) = Φ.toLinearMap (A x) := hx.symm
      _ = 0 := by rw [x.2, map_zero]⟩
  invFun y := ⟨Φ.symm y, by
    change A (Φ.symm y) = 0
    apply Φ.injective
    have hy := LinearMap.congr_fun h (Φ.symm y)
    simp only [LinearMap.comp_apply] at hy
    change Φ.toLinearMap (A (Φ.symm y)) = Φ.toLinearMap 0
    calc
      Φ.toLinearMap (A (Φ.symm y)) = B (Φ.toLinearMap (Φ.symm y)) := hy
      _ = B y := congrArg B (Φ.apply_symm_apply y)
      _ = 0 := y.2
      _ = Φ.toLinearMap 0 := (map_zero Φ.toLinearMap).symm⟩
  left_inv x := Subtype.ext (Φ.symm_apply_apply x)
  right_inv y := Subtype.ext (Φ.apply_symm_apply y)
  map_add' _ _ := Subtype.ext (map_add Φ _ _)
  map_smul' _ _ := Subtype.ext (map_smul Φ _ _)

/-- Equivalence induced on ranges of conjugate endomorphisms. -/
def rangeEquiv (Φ : E₁ ≃ₗ[k] E₂) (A : Module.End k E₁) (B : Module.End k E₂)
    (h : Intertwines Φ A B) : LinearMap.range A ≃ₗ[k] LinearMap.range B where
  toFun x := ⟨Φ x, by
    rcases x with ⟨x, z, hz⟩
    refine ⟨Φ z, ?_⟩
    change B (Φ.toLinearMap z) = Φ.toLinearMap x
    calc
      B (Φ.toLinearMap z) = Φ.toLinearMap (A z) := (LinearMap.congr_fun h z).symm
      _ = Φ.toLinearMap x := by rw [hz]⟩
  invFun y := ⟨Φ.symm y, by
    rcases y with ⟨y, z, hz⟩
    refine ⟨Φ.symm z, ?_⟩
    change A (Φ.symm z) = Φ.symm y
    apply Φ.injective
    change Φ.toLinearMap (A (Φ.symm z)) = Φ.toLinearMap (Φ.symm y)
    calc
      Φ.toLinearMap (A (Φ.symm z)) = B (Φ.toLinearMap (Φ.symm z)) :=
        LinearMap.congr_fun h (Φ.symm z)
      _ = B z := congrArg B (Φ.apply_symm_apply z)
      _ = y := hz
      _ = Φ.toLinearMap (Φ.symm y) := (Φ.apply_symm_apply y).symm⟩
  left_inv x := Subtype.ext (Φ.symm_apply_apply x)
  right_inv y := Subtype.ext (Φ.apply_symm_apply y)
  map_add' _ _ := Subtype.ext (map_add Φ _ _)
  map_smul' _ _ := Subtype.ext (map_smul Φ _ _)

/-- Kernel ranks are invariant under structured conjugacy. -/
theorem finrank_kernel_eq [FiniteDimensional k E₁] [FiniteDimensional k E₂]
    (Φ : E₁ ≃ₗ[k] E₂) (A : Module.End k E₁) (B : Module.End k E₂)
    (h : Intertwines Φ A B) :
    finrank k (LinearMap.ker A) = finrank k (LinearMap.ker B) :=
  LinearEquiv.finrank_eq (kernelEquiv Φ A B h)

/-- Image ranks are invariant under structured conjugacy. -/
theorem finrank_range_eq [FiniteDimensional k E₁] [FiniteDimensional k E₂]
    (Φ : E₁ ≃ₗ[k] E₂) (A : Module.End k E₁) (B : Module.End k E₂)
    (h : Intertwines Φ A B) :
    finrank k (LinearMap.range A) = finrank k (LinearMap.range B) :=
  LinearEquiv.finrank_eq (rangeEquiv Φ A B h)

end Curvature

section MapRanks

variable {k V₁ V₂ W₁ W₂ : Type*} [Field k]
variable [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
variable [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]

/-- Intertwining square for maps with different source and target spaces. -/
def MapIntertwines (Φ : V₁ ≃ₗ[k] V₂) (Ψ : W₁ ≃ₗ[k] W₂)
    (A : V₁ →ₗ[k] W₁) (B : V₂ →ₗ[k] W₂) : Prop :=
  Ψ.toLinearMap.comp A = B.comp Φ.toLinearMap

/-- A commuting equivalence square identifies the two kernels. -/
def mapKernelEquiv (Φ : V₁ ≃ₗ[k] V₂) (Ψ : W₁ ≃ₗ[k] W₂)
    (A : V₁ →ₗ[k] W₁) (B : V₂ →ₗ[k] W₂) (h : MapIntertwines Φ Ψ A B) :
    LinearMap.ker A ≃ₗ[k] LinearMap.ker B where
  toFun x := ⟨Φ x, by
    have hx := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply] at hx
    change B (Φ.toLinearMap x) = 0
    calc
      B (Φ.toLinearMap x) = Ψ.toLinearMap (A x) := hx.symm
      _ = 0 := by rw [x.2, map_zero]⟩
  invFun y := ⟨Φ.symm y, by
    change A (Φ.symm y) = 0
    apply Ψ.injective
    have hy := LinearMap.congr_fun h (Φ.symm y)
    simp only [LinearMap.comp_apply] at hy
    change Ψ.toLinearMap (A (Φ.symm y)) = Ψ.toLinearMap 0
    calc
      Ψ.toLinearMap (A (Φ.symm y)) = B (Φ.toLinearMap (Φ.symm y)) := hy
      _ = B y := congrArg B (Φ.apply_symm_apply y)
      _ = 0 := y.2
      _ = Ψ.toLinearMap 0 := (map_zero Ψ.toLinearMap).symm⟩
  left_inv x := Subtype.ext (Φ.symm_apply_apply x)
  right_inv y := Subtype.ext (Φ.apply_symm_apply y)
  map_add' _ _ := Subtype.ext (map_add Φ _ _)
  map_smul' _ _ := Subtype.ext (map_smul Φ _ _)

/-- A commuting equivalence square identifies the two images. -/
def mapRangeEquiv (Φ : V₁ ≃ₗ[k] V₂) (Ψ : W₁ ≃ₗ[k] W₂)
    (A : V₁ →ₗ[k] W₁) (B : V₂ →ₗ[k] W₂) (h : MapIntertwines Φ Ψ A B) :
    LinearMap.range A ≃ₗ[k] LinearMap.range B where
  toFun x := ⟨Ψ x, by
    rcases x with ⟨x, z, hz⟩
    refine ⟨Φ z, ?_⟩
    change B (Φ.toLinearMap z) = Ψ.toLinearMap x
    calc
      B (Φ.toLinearMap z) = Ψ.toLinearMap (A z) := (LinearMap.congr_fun h z).symm
      _ = Ψ.toLinearMap x := by rw [hz]⟩
  invFun y := ⟨Ψ.symm y, by
    rcases y with ⟨y, z, hz⟩
    refine ⟨Φ.symm z, ?_⟩
    change A (Φ.symm z) = Ψ.symm y
    apply Ψ.injective
    change Ψ.toLinearMap (A (Φ.symm z)) = Ψ.toLinearMap (Ψ.symm y)
    calc
      Ψ.toLinearMap (A (Φ.symm z)) = B (Φ.toLinearMap (Φ.symm z)) :=
        LinearMap.congr_fun h (Φ.symm z)
      _ = B z := congrArg B (Φ.apply_symm_apply z)
      _ = y := hz
      _ = Ψ.toLinearMap (Ψ.symm y) := (Ψ.apply_symm_apply y).symm⟩
  left_inv x := Subtype.ext (Ψ.symm_apply_apply x)
  right_inv y := Subtype.ext (Ψ.apply_symm_apply y)
  map_add' _ _ := Subtype.ext (map_add Ψ _ _)
  map_smul' _ _ := Subtype.ext (map_smul Ψ _ _)

/-- Kernel-rank invariance for a commuting equivalence square. -/
theorem map_finrank_kernel_eq [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    (Φ : V₁ ≃ₗ[k] V₂) (Ψ : W₁ ≃ₗ[k] W₂)
    (A : V₁ →ₗ[k] W₁) (B : V₂ →ₗ[k] W₂) (h : MapIntertwines Φ Ψ A B) :
    finrank k (LinearMap.ker A) = finrank k (LinearMap.ker B) :=
  LinearEquiv.finrank_eq (mapKernelEquiv Φ Ψ A B h)

/-- Image-rank invariance for a commuting equivalence square. -/
theorem map_finrank_range_eq [FiniteDimensional k W₁] [FiniteDimensional k W₂]
    (Φ : V₁ ≃ₗ[k] V₂) (Ψ : W₁ ≃ₗ[k] W₂)
    (A : V₁ →ₗ[k] W₁) (B : V₂ →ₗ[k] W₂) (h : MapIntertwines Φ Ψ A B) :
    finrank k (LinearMap.range A) = finrank k (LinearMap.range B) :=
  LinearEquiv.finrank_eq (mapRangeEquiv Φ Ψ A B h)

end MapRanks

section Pullback

/-- Fibrewise pullback of a vector-valued form; multilinearity is not needed for injectivity. -/
def pullback {X Y V ι : Type*} (p : X → Y) (ω : (ι → Y) → V) : (ι → X) → V :=
  fun v => ω (p ∘ v)

/-- Surjective tangent maps detect vanishing of pulled-back vector-valued forms. -/
theorem pullback_injective_of_surjective {X Y V ι : Type*}
    (p : X → Y) (hp : Function.Surjective p) :
    Function.Injective (pullback (V := V) (ι := ι) p) := by
  intro ω η h
  funext v
  choose w hw using fun i => hp (v i)
  have hv : p ∘ w = v := funext hw
  calc
    ω v = pullback p ω w := by simp [pullback, hv]
    _ = pullback p η w := congrFun h w
    _ = η v := by simp [pullback, hv]

/-- Pullback along a surjection vanishes exactly when the original form vanishes. -/
theorem pullback_eq_zero_iff_of_surjective {X Y V ι : Type*} [Zero V]
    (p : X → Y) (hp : Function.Surjective p) (ω : (ι → Y) → V) :
    pullback p ω = 0 ↔ ω = 0 := by
  constructor
  · intro h
    apply pullback_injective_of_surjective p hp
    have h0 : pullback p (0 : (ι → Y) → V) = 0 := by
      funext v
      rfl
    exact h.trans h0.symm
  · rintro rfl
    rfl

end Pullback

section Spencer

variable {k : Type*} [Field k]
variable {M N : ℕ → Type*}
variable [∀ n, AddCommGroup (M n)] [∀ n, Module k (M n)]
variable [∀ n, AddCommGroup (N n)] [∀ n, Module k (N n)]

/-- Degreewise equivalence of Spencer/cochain towers intertwining their differentials. -/
structure ComplexEquiv (C : HTGeometry.DeningerCochainComplex k M)
    (D : HTGeometry.DeningerCochainComplex k N) where
  iso : ∀ n, M n ≃ₗ[k] N n
  comm : ∀ n, (iso (n + 1)).toLinearMap.comp (C.d n) =
    (D.d n).comp (iso n).toLinearMap

namespace ComplexEquiv

variable {C : HTGeometry.DeningerCochainComplex k M}
variable {D : HTGeometry.DeningerCochainComplex k N}

/-- Forward cochain map of a complex equivalence. -/
def toMap (F : ComplexEquiv C D) : HTGeometry.DeningerCochainMap C D where
  f n := (F.iso n).toLinearMap
  comm := F.comm

/-- Inverse cochain map of a complex equivalence. -/
def symmMap (F : ComplexEquiv C D) : HTGeometry.DeningerCochainMap D C where
  f n := (F.iso n).symm.toLinearMap
  comm n := by
    ext y
    apply (F.iso (n + 1)).injective
    have h := LinearMap.congr_fun (F.comm n) ((F.iso n).symm y)
    simp only [LinearMap.comp_apply] at h ⊢
    simpa using h.symm

/-- Inverse law on cohomology. -/
theorem cohomologyMap_leftInverse (F : ComplexEquiv C D) (n : ℕ) :
    Function.LeftInverse ((F.symmMap).cohomologyMap n) ((F.toMap).cohomologyMap n) := by
  intro q
  obtain ⟨x, rfl⟩ := C.cohomologyMk_surjective n q
  change C.cohomologyMk _ = C.cohomologyMk x
  congr 1
  apply Subtype.ext
  exact (F.iso n).symm_apply_apply x

/-- Inverse law on target cohomology. -/
theorem cohomologyMap_rightInverse (F : ComplexEquiv C D) (n : ℕ) :
    Function.RightInverse ((F.symmMap).cohomologyMap n) ((F.toMap).cohomologyMap n) := by
  intro q
  obtain ⟨x, rfl⟩ := D.cohomologyMk_surjective n q
  change D.cohomologyMk _ = D.cohomologyMk x
  congr 1
  apply Subtype.ext
  exact (F.iso n).apply_symm_apply x

/-- Isomorphism on every Spencer cohomology group. -/
noncomputable def cohomologyEquiv (F : ComplexEquiv C D) (n : ℕ) :
    C.cohomology n ≃ₗ[k] D.cohomology n :=
  LinearEquiv.ofBijective ((F.toMap).cohomologyMap n)
    ⟨(F.cohomologyMap_leftInverse n).injective,
      (F.cohomologyMap_rightInverse n).surjective⟩

/-- Spencer cohomology ranks agree in every degree. -/
theorem finrank_cohomology_eq {n : ℕ} [FiniteDimensional k (C.cohomology n)]
    [FiniteDimensional k (D.cohomology n)] (F : ComplexEquiv C D) :
    finrank k (C.cohomology n) = finrank k (D.cohomology n) :=
  LinearEquiv.finrank_eq (F.cohomologyEquiv n)

/-- Degreewise tower ranks agree. -/
theorem finrank_object_eq {n : ℕ} [FiniteDimensional k (M n)]
    [FiniteDimensional k (N n)] (F : ComplexEquiv C D) :
    finrank k (M n) = finrank k (N n) :=
  LinearEquiv.finrank_eq (F.iso n)

/-- Spencer-symbol kernel ranks agree in every degree. -/
theorem finrank_differential_kernel_eq {n : ℕ} [FiniteDimensional k (M n)]
    [FiniteDimensional k (N n)] (F : ComplexEquiv C D) :
    finrank k (LinearMap.ker (C.d n)) = finrank k (LinearMap.ker (D.d n)) :=
  map_finrank_kernel_eq (F.iso n) (F.iso (n + 1)) (C.d n) (D.d n) (F.comm n)

/-- Spencer-symbol image ranks agree in every degree. -/
theorem finrank_differential_range_eq {n : ℕ} [FiniteDimensional k (M (n + 1))]
    [FiniteDimensional k (N (n + 1))] (F : ComplexEquiv C D) :
    finrank k (LinearMap.range (C.d n)) = finrank k (LinearMap.range (D.d n)) :=
  map_finrank_range_eq (F.iso n) (F.iso (n + 1)) (C.d n) (D.d n) (F.comm n)

/-- Equality of every sufficiently large rank value forces equality of eventual dimension
functions, hence of any chosen eventual polynomial representation. -/
theorem eventualDimensionFunction_eq (_F : ComplexEquiv C D)
    (rankM rankN : ℕ → ℕ) (h : ∀ n, rankM n = rankN n) : rankM = rankN :=
  funext h

end ComplexEquiv

end Spencer

end HTGeometry.NomologicalHomotopyGeometry.StructuredMorita
