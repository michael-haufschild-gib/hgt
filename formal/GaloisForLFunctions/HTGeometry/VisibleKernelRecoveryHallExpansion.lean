import GaloisForLFunctions.HTGeometry.LinearFamilyDefectSupermodularity
import GaloisForLFunctions.HTGeometry.SubspaceRelativeDimension

/-!
# Hall expansion by visible rank and hidden-kernel recovery

A source layer may send some directions visibly into a disjoint target layer
while the remaining directions are hidden inside output already supplied by
the target input.  Hall expansion does not require paying for the entire
forward-image overlap.  It is enough to recover the kernel of the visible
detector injectively into the source layer.

This is the abstract rank mechanism behind two-step Casimir recovery: visible
edge images contribute the rank of a quotient detector, while a quadratic
Casimir sends its hidden kernel back to the singlet layer.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Quadratic return operator of a finite endomorphism family. -/
def linearFamilySquare
    {K X J : Type*}
    [Semiring K]
    [AddCommMonoid X] [Module K X]
    [Fintype J]
    (A : J → X →ₗ[K] X) : X →ₗ[K] X :=
  ∑ j, (A j).comp (A j)

@[simp] theorem linearFamilySquare_apply
    {K X J : Type*}
    [Semiring K]
    [AddCommMonoid X] [Module K X]
    [Fintype J]
    (A : J → X →ₗ[K] X) (x : X) :
    linearFamilySquare A x = ∑ j, A j (A j x) := by
  simp [linearFamilySquare]

/-- If every first image of `x` lies in `U`, its quadratic return lies in
the one-step family shadow of `U`. -/
theorem linearFamilySquare_mem_shadow_of_images_mem
    {K X J : Type*}
    [DivisionRing K]
    [AddCommGroup X] [Module K X]
    [Fintype J]
    (A : J → X →ₗ[K] X) (U : Submodule K X) (x : X)
    (h : ∀ j, A j x ∈ U) :
    linearFamilySquare A x ∈ linearFamilyShadow A U := by
  classical
  rw [linearFamilySquare_apply]
  exact Submodule.sum_mem (linearFamilyShadow A U) fun j _ =>
    (le_iSup (fun k => U.map (A k)) j) ⟨A j x, h j, rfl⟩

/-- An invariant finite-dimensional subspace is reproduced by a family once
the quadratic family return is injective on that subspace. -/
theorem invariantSubspace_le_shadow_of_linearFamilySquare_injective
    {K X J : Type*}
    [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [Fintype J]
    (A : J → X →ₗ[K] X) (U : Submodule K X)
    (hAU : ∀ j x, x ∈ U → A j x ∈ U)
    (hKinj : Function.Injective
      ((linearFamilySquare A).domRestrict U)) :
    U ≤ linearFamilyShadow A U := by
  have hshadowU : linearFamilyShadow A U ≤ U := by
    apply iSup_le
    intro j
    rintro _ ⟨x, hx, rfl⟩
    exact hAU j x hx
  let K_U : U →ₗ[K] U :=
    ((linearFamilySquare A).domRestrict U).codRestrict U fun x => by
      apply hshadowU
      exact linearFamilySquare_mem_shadow_of_images_mem A U x (fun j =>
        hAU j x x.property)
  have hK_U_inj : Function.Injective K_U := by
    intro x y hxy
    apply hKinj
    simpa [K_U] using congrArg Subtype.val hxy
  have hK_U_surj : Function.Surjective K_U :=
    LinearMap.injective_iff_surjective.mp hK_U_inj
  intro x hx
  obtain ⟨y, hy⟩ := hK_U_surj ⟨x, hx⟩
  have hKy : linearFamilySquare A (y : X) ∈ linearFamilyShadow A U :=
    linearFamilySquare_mem_shadow_of_images_mem A U y (fun j =>
      hAU j y y.property)
  have hval : linearFamilySquare A (y : X) = x := by
    simpa [K_U] using congrArg Subtype.val hy
  rw [← hval]
  exact hKy

/-- A detector landing in the quotient of visible output by occupied target
input automatically satisfies the visible-rank inequality. -/
theorem visibleQuotientDetector_finrank
    {K X Z : Type*}
    [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Z] [Module K Z]
    (Uₛ U_w C : Submodule K X)
    (F : Uₛ →ₗ[K] Z)
    (ι : LinearMap.range F →ₗ[K] (X ⧸ U_w))
    (hιinj : Function.Injective ι)
    (hιrange : LinearMap.range ι ≤
      (U_w ⊔ C).map U_w.mkQ) :
    Module.finrank K (LinearMap.range F) + Module.finrank K U_w ≤
      Module.finrank K ((U_w ⊔ C) : Submodule K X) := by
  have hιrank : Module.finrank K (LinearMap.range F) =
      Module.finrank K (LinearMap.range ι) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofInjective ι hιinj)
  have hrange : Module.finrank K (LinearMap.range ι) ≤
      quotDim U_w (U_w ⊔ C) := by
    change Module.finrank K (LinearMap.range ι) ≤
      Module.finrank K ((U_w ⊔ C).map U_w.mkQ)
    exact Submodule.finrank_mono hιrange
  have hsum := finrank_add_quotDim
    (K := K) (V := X) (show U_w ≤ U_w ⊔ C from le_sup_left)
  omega

/-- Quadratic recovery restricted to kernel of a visible detector. -/
def linearFamilySquareKernelRecovery
    {K X Z J : Type*}
    [Semiring K]
    [AddCommMonoid X] [Module K X]
    [AddCommMonoid Z] [Module K Z]
    [Fintype J]
    (A : J → X →ₗ[K] X) (Uₛ : Submodule K X)
    (F : Uₛ →ₗ[K] Z) : LinearMap.ker F →ₗ[K] X :=
  (linearFamilySquare A).comp
    (Uₛ.subtype.comp (LinearMap.ker F).subtype)

/-- A visible quotient detector together with an injective recovery of its
kernel in a disjoint layer proves Hall expansion.  The visible-rank hypothesis
allows the visible output to contain additional directions; the recovery map
needs to recover only `ker F`, not the full visible-output overlap. -/
theorem visibleKernelRecovery_subspace_finrank
    {K X Z : Type*}
    [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Z] [Module K Z]
    (S W Uₛ U_w C Yout : Submodule K X)
    (F : Uₛ →ₗ[K] Z)
    (R : LinearMap.ker F →ₗ[K] X)
    (hSW : Disjoint S W)
    (hUₛS : Uₛ ≤ S)
    (hUwW : U_w ≤ W)
    (hCW : C ≤ W)
    (hRrangeS : LinearMap.range R ≤ S)
    (hRinj : Function.Injective R)
    (hvisible : Module.finrank K (LinearMap.range F) +
        Module.finrank K U_w ≤
      Module.finrank K ((U_w ⊔ C) : Submodule K X))
    (hout : (U_w ⊔ C) ⊔ LinearMap.range R ≤ Yout) :
    Module.finrank K ((Uₛ ⊔ U_w) : Submodule K X) ≤
      Module.finrank K Yout := by
  have hinputDisjoint : Disjoint Uₛ U_w := hSW.mono hUₛS hUwW
  have hvisibleW : U_w ⊔ C ≤ W := sup_le hUwW hCW
  have houtputDisjoint : Disjoint (U_w ⊔ C) (LinearMap.range R) :=
    hSW.symm.mono hvisibleW hRrangeS
  have hinput := Submodule.finrank_sup_add_finrank_inf_eq Uₛ U_w
  have houtput := Submodule.finrank_sup_add_finrank_inf_eq
    (U_w ⊔ C) (LinearMap.range R)
  rw [disjoint_iff.mp hinputDisjoint, finrank_bot] at hinput
  rw [disjoint_iff.mp houtputDisjoint, finrank_bot] at houtput
  have hrecover : Module.finrank K (LinearMap.ker F) =
      Module.finrank K (LinearMap.range R) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofInjective R hRinj)
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker F
  have houtRank : Module.finrank K
      (((U_w ⊔ C) ⊔ LinearMap.range R) : Submodule K X) ≤
      Module.finrank K Yout :=
    Submodule.finrank_mono hout
  omega

/-- Quadratic hidden-kernel recovery for one endomorphism family.  If the
target input reproduces itself under the family, visible source rank lands in
the disjoint target layer, and every detector-kernel direction has all first
images in target input, then injectivity of the quadratic return closes Hall
for the mixed input. -/
theorem quadraticHiddenKernelRecovery_subspace_finrank
    {K X Z J : Type*}
    [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Z] [Module K Z]
    [Fintype J]
    (A : J → X →ₗ[K] X)
    (S W Uₛ U_w : Submodule K X)
    (F : Uₛ →ₗ[K] Z)
    (hSW : Disjoint S W)
    (hUₛS : Uₛ ≤ S)
    (hUwW : U_w ≤ W)
    (hsourceShadowW : linearFamilyShadow A Uₛ ≤ W)
    (hUwReproduced : U_w ≤ linearFamilyShadow A U_w)
    (hhidden : ∀ x : LinearMap.ker F, ∀ j,
      A j (((x : LinearMap.ker F) : Uₛ) : X) ∈ U_w)
    (hrecoveryS : LinearMap.range
      (linearFamilySquareKernelRecovery A Uₛ F) ≤ S)
    (hrecoveryInj : Function.Injective
      (linearFamilySquareKernelRecovery A Uₛ F))
    (hvisible : Module.finrank K (LinearMap.range F) +
        Module.finrank K U_w ≤
      Module.finrank K
        ((U_w ⊔ linearFamilyShadow A Uₛ) : Submodule K X)) :
    Module.finrank K ((Uₛ ⊔ U_w) : Submodule K X) ≤
      Module.finrank K (linearFamilyShadow A (Uₛ ⊔ U_w)) := by
  let R := linearFamilySquareKernelRecovery A Uₛ F
  have hRshadow : LinearMap.range R ≤ linearFamilyShadow A U_w := by
    rintro _ ⟨x, rfl⟩
    change linearFamilySquare A (((x : LinearMap.ker F) : Uₛ) : X) ∈
      linearFamilyShadow A U_w
    exact linearFamilySquare_mem_shadow_of_images_mem A U_w _ (hhidden x)
  have hout :
      (U_w ⊔ linearFamilyShadow A Uₛ) ⊔ LinearMap.range R ≤
        linearFamilyShadow A (Uₛ ⊔ U_w) := by
    rw [linearFamilyShadow_sup]
    exact sup_le
      (sup_le (hUwReproduced.trans le_sup_right) le_sup_left)
      (hRshadow.trans le_sup_right)
  exact visibleKernelRecovery_subspace_finrank
    S W Uₛ U_w (linearFamilyShadow A Uₛ)
      (linearFamilyShadow A (Uₛ ⊔ U_w)) F R
      hSW hUₛS hUwW hsourceShadowW hrecoveryS
      hrecoveryInj hvisible hout

/-- Quotient-detector form of quadratic hidden-kernel recovery.  An injective
assembly of detector range into visible output modulo occupied target input
discharges the visible-rank hypothesis automatically. -/
theorem quadraticHiddenKernelRecovery_of_visibleQuotient
    {K X Z J : Type*}
    [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Z] [Module K Z]
    [Fintype J]
    (A : J → X →ₗ[K] X)
    (S W Uₛ U_w : Submodule K X)
    (F : Uₛ →ₗ[K] Z)
    (ι : LinearMap.range F →ₗ[K] (X ⧸ U_w))
    (hιinj : Function.Injective ι)
    (hιrange : LinearMap.range ι ≤
      (U_w ⊔ linearFamilyShadow A Uₛ).map U_w.mkQ)
    (hSW : Disjoint S W)
    (hUₛS : Uₛ ≤ S)
    (hUwW : U_w ≤ W)
    (hsourceShadowW : linearFamilyShadow A Uₛ ≤ W)
    (hUwReproduced : U_w ≤ linearFamilyShadow A U_w)
    (hhidden : ∀ x : LinearMap.ker F, ∀ j,
      A j (((x : LinearMap.ker F) : Uₛ) : X) ∈ U_w)
    (hrecoveryS : LinearMap.range
      (linearFamilySquareKernelRecovery A Uₛ F) ≤ S)
    (hrecoveryInj : Function.Injective
      (linearFamilySquareKernelRecovery A Uₛ F)) :
    Module.finrank K ((Uₛ ⊔ U_w) : Submodule K X) ≤
      Module.finrank K (linearFamilyShadow A (Uₛ ⊔ U_w)) := by
  apply quadraticHiddenKernelRecovery_subspace_finrank
    A S W Uₛ U_w F hSW hUₛS hUwW hsourceShadowW
      hUwReproduced hhidden hrecoveryS hrecoveryInj
  exact visibleQuotientDetector_finrank
    Uₛ U_w (linearFamilyShadow A Uₛ) F ι hιinj hιrange

end

end GaloisForLFunctions.HTGeometry
