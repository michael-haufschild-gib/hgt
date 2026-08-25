import GaloisForLFunctions.HTGeometry.CompactHyperplanePerturbation

open Module Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def linearPMapShiftLinearMap (T : H →ₗ.[ℂ] H) (z : ℂ) : T.domain →ₗ[ℂ] H :=
  T.toFun - z • T.domain.subtype

def linearPMapEigenspace (T : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H :=
  (LinearMap.ker (linearPMapShiftLinearMap T z)).map T.domain.subtype

theorem mem_linearPMapEigenspace_iff (T : H →ₗ.[ℂ] H) (z : ℂ) (x : H) :
    x ∈ linearPMapEigenspace T z ↔ ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = z • x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    have hzero := LinearMap.mem_ker.mp hy
    change T y - z • (y : H) = 0 at hzero
    exact sub_eq_zero.mp hzero
  · rintro ⟨hx, heq⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change T ⟨x, hx⟩ - z • x = 0
    exact sub_eq_zero.mpr heq

def linearPMapWindowRootSubspace (T : H →ₗ.[ℂ] H) (D : Set ℂ) : Submodule ℂ H :=
  sSup (linearPMapEigenspace T '' D)

theorem linearPMapEigenspace_le_windowRootSubspace
    (T : H →ₗ.[ℂ] H) (D : Set ℂ) {z : ℂ} (hz : z ∈ D) :
    linearPMapEigenspace T z ≤ linearPMapWindowRootSubspace T D := by
  apply le_sSup
  exact ⟨z, hz, rfl⟩

def linearPMapWindowRieszRangeProjection (T : H →ₗ.[ℂ] H) (D : Set ℂ) : H →L[ℂ] H :=
  let K := (linearPMapWindowRootSubspace T D).topologicalClosure
  K.subtypeL ∘L K.orthogonalProjectionOnto

theorem linearPMapWindowRieszRangeProjection_eq_zero_iff
    (T : H →ₗ.[ℂ] H) (D : Set ℂ) :
    linearPMapWindowRieszRangeProjection T D = 0 ↔
      ∀ z ∈ D, linearPMapEigenspace T z = ⊥ := by
  constructor
  · intro hP z hz
    apply le_antisymm
    · intro x hx
      have hxroot : x ∈ linearPMapWindowRootSubspace T D :=
        linearPMapEigenspace_le_windowRootSubspace T D hz hx
      have hxclosure : x ∈ (linearPMapWindowRootSubspace T D).topologicalClosure :=
        Submodule.le_topologicalClosure _ hxroot
      have hfix := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
        (⟨x, hxclosure⟩ : (linearPMapWindowRootSubspace T D).topologicalClosure)
      have hfix' := congrArg Subtype.val hfix
      change linearPMapWindowRieszRangeProjection T D x = x at hfix'
      rw [hP, ContinuousLinearMap.zero_apply] at hfix'
      simpa [hfix'.symm]
    · exact bot_le
  · intro heig
    have hroot : linearPMapWindowRootSubspace T D = ⊥ := by
      rw [linearPMapWindowRootSubspace]
      apply sSup_eq_bot.mpr
      intro E hE
      rcases hE with ⟨z, hz, rfl⟩
      exact heig z hz
    have hclosure : (linearPMapWindowRootSubspace T D).topologicalClosure = ⊥ := by
      simp [hroot]
    ext x
    let y : H :=
      ((linearPMapWindowRootSubspace T D).topologicalClosure.orthogonalProjectionOnto x :
        (linearPMapWindowRootSubspace T D).topologicalClosure)
    change y = 0
    have hy : y ∈
        (linearPMapWindowRootSubspace T D).topologicalClosure :=
      ((linearPMapWindowRootSubspace T D).topologicalClosure.orthogonalProjectionOnto x).property
    have hybot : y ∈ (⊥ : Submodule ℂ H) := hclosure ▸ hy
    simpa using hybot

/-- Bounded analytic Fredholm pencil obtained from one compact resolvent of a closed operator. -/
def compactResolventCharacteristicOperator (R : H →L[ℂ] H) (z₀ z : ℂ) : H →L[ℂ] H :=
  1 - (z - z₀) • R

/-- Exact compact-resolvent Fredholm alternative: the bounded characteristic pencil is invertible
at `z` exactly when the closed operator has no eigenvector at `z`. -/
theorem isUnit_compactResolventCharacteristicOperator_iff_eigenspace_eq_bot
    (T : H →ₗ.[ℂ] H) (z₀ : ℂ) (R : H →L[ℂ] H)
    (hRcompact : IsCompactOperator R)
    (hRdom : ∀ x : H, R x ∈ T.domain)
    (hleft : ∀ x : H, T ⟨R x, hRdom x⟩ - z₀ • R x = x)
    (hright : ∀ x : T.domain, R (T x - z₀ • (x : H)) = (x : H))
    (z : ℂ) :
    IsUnit (compactResolventCharacteristicOperator R z₀ z) ↔
      linearPMapEigenspace T z = ⊥ := by
  constructor
  · intro hunit
    apply le_antisymm
    · intro x hx
      obtain ⟨hxdom, hTx⟩ := (mem_linearPMapEigenspace_iff T z x).mp hx
      have hRx : R ((z - z₀) • x) = x := by
        have h := hright ⟨x, hxdom⟩
        rw [hTx] at h
        simpa [sub_smul] using h
      have hSx : compactResolventCharacteristicOperator R z₀ z x = 0 := by
        have hsmul : (z - z₀) • R x = x := by simpa using hRx
        change x - (z - z₀) • R x = 0
        rw [hsmul, sub_self]
      have hinj : Function.Injective (compactResolventCharacteristicOperator R z₀ z) :=
        (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
      have hx0 : x = 0 := hinj (by simpa using hSx)
      simpa [hx0]
    · exact bot_le
  · intro heig
    let C : H →L[ℂ] H := -(z - z₀) • R
    have hCcompact : IsCompactOperator C := hRcompact.smul _
    have hS : compactResolventCharacteristicOperator R z₀ z = 1 + C := by
      simp [compactResolventCharacteristicOperator, C, sub_eq_add_neg]
    have hinj : Function.Injective (compactResolventCharacteristicOperator R z₀ z) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have hxEq : x = (z - z₀) • R x := by
        change x - (z - z₀) • R x = 0 at hx
        exact sub_eq_zero.mp hx
      have hyEig : R x ∈ linearPMapEigenspace T z := by
        rw [mem_linearPMapEigenspace_iff]
        refine ⟨hRdom x, ?_⟩
        have hL := hleft x
        have hT : T ⟨R x, hRdom x⟩ = x + z₀ • R x :=
          (sub_eq_iff_eq_add).mp hL
        calc
          T ⟨R x, hRdom x⟩ = x + z₀ • R x := hT
          _ = (z - z₀) • R x + z₀ • R x :=
            congrArg (fun y => y + z₀ • R x) hxEq
          _ = z • R x := by module
      have hRx0 : R x = 0 := by
        rw [heig] at hyEig
        simpa using hyEig
      rw [hxEq, hRx0, smul_zero]
    have hsurj : Function.Surjective (compactResolventCharacteristicOperator R z₀ z) := by
      rw [hS]
      exact compactPerturbation_one_surjective_of_injective C hCcompact (by
        rw [← hS]
        exact hinj)
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩

/-- For every closed operator with one compact resolvent, a canonical bounded Fredholm pencil reads
window Riesz-range vanishing exactly. -/
theorem exists_compactResolventCharacteristicOperator_window_equivalence
    (T : H →ₗ.[ℂ] H) (z₀ : ℂ) (hcompact : LinearPMap.HasCompactResolventAt T z₀)
    (D : Set ℂ) :
    ∃ R : H →L[ℂ] H, IsCompactOperator R ∧
      ((∀ z ∈ D, IsUnit (compactResolventCharacteristicOperator R z₀ z)) ↔
        linearPMapWindowRieszRangeProjection T D = 0) := by
  rcases hcompact with ⟨R, hRc, ⟨hRdom, hleft⟩, hright⟩
  refine ⟨R, hRc, ?_⟩
  rw [linearPMapWindowRieszRangeProjection_eq_zero_iff]
  exact forall_congr' fun z => forall_congr' fun _ =>
    isUnit_compactResolventCharacteristicOperator_iff_eigenspace_eq_bot
      T z₀ R hRc hRdom hleft hright z

end

end GaloisForLFunctions.HTGeometry
