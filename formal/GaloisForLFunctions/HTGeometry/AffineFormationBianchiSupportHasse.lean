import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality
import GaloisForLFunctions.HTGeometry.AffineFormationCurrent

/-!
# Hasse support rigidity for affine-formation Bianchi currents

The five current channels in the affine-formation Bianchi identity define a finite-support profile
of linear maps.  Its sum vanishes, so a nonzero Bianchi defect cannot occupy exactly one channel.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.HTGeometry.ABHN

/-- Five signed channels of the affine-formation current Bianchi identity. -/
noncomputable def affineFormationBianchiCurrentProfile
    {K X Vj Vk Vl : Type*}
    [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Vj] [Module K Vj]
    [AddCommGroup Vk] [Module K Vk] [AddCommGroup Vl] [Module K Vl]
    (aji : X →ₗ[K] Vj) (akj : X →ₗ[K] Vk) (aki : X →ₗ[K] Vk)
    (alk : X →ₗ[K] Vl) (alj : X →ₗ[K] Vl) (ali : X →ₗ[K] Vl)
    (Lkj : Vj →ₗ[K] Vk) (Llk : Vk →ₗ[K] Vl) (Llj : Vj →ₗ[K] Vl) :
    Fin 5 →₀ (X →ₗ[K] Vl) :=
  Finsupp.equivFunOnFinite.symm ![
    Llk.comp (akj + Lkj.comp aji - aki),
    alk + Llk.comp aki - ali,
    -(alk + Llk.comp akj - alj),
    -(Llk.comp Lkj - Llj).comp aji,
    -(alj + Llj.comp aji - ali)]

@[simp]
theorem affineFormationBianchiCurrentProfile_zero
    {K X Vj Vk Vl : Type*}
    [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Vj] [Module K Vj] [AddCommGroup Vk] [Module K Vk]
    [AddCommGroup Vl] [Module K Vl]
    (aji : X →ₗ[K] Vj) (akj : X →ₗ[K] Vk) (aki : X →ₗ[K] Vk)
    (alk : X →ₗ[K] Vl) (alj : X →ₗ[K] Vl) (ali : X →ₗ[K] Vl)
    (Lkj : Vj →ₗ[K] Vk) (Llk : Vk →ₗ[K] Vl) (Llj : Vj →ₗ[K] Vl) :
    affineFormationBianchiCurrentProfile aji akj aki alk alj ali Lkj Llk Llj 0 =
      Llk.comp (akj + Lkj.comp aji - aki) := rfl

@[simp]
theorem affineFormationBianchiCurrentProfile_one
    {K X Vj Vk Vl : Type*}
    [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Vj] [Module K Vj] [AddCommGroup Vk] [Module K Vk]
    [AddCommGroup Vl] [Module K Vl]
    (aji : X →ₗ[K] Vj) (akj : X →ₗ[K] Vk) (aki : X →ₗ[K] Vk)
    (alk : X →ₗ[K] Vl) (alj : X →ₗ[K] Vl) (ali : X →ₗ[K] Vl)
    (Lkj : Vj →ₗ[K] Vk) (Llk : Vk →ₗ[K] Vl) (Llj : Vj →ₗ[K] Vl) :
    affineFormationBianchiCurrentProfile aji akj aki alk alj ali Lkj Llk Llj 1 =
      alk + Llk.comp aki - ali := rfl

@[simp]
theorem affineFormationBianchiCurrentProfile_two
    {K X Vj Vk Vl : Type*}
    [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Vj] [Module K Vj] [AddCommGroup Vk] [Module K Vk]
    [AddCommGroup Vl] [Module K Vl]
    (aji : X →ₗ[K] Vj) (akj : X →ₗ[K] Vk) (aki : X →ₗ[K] Vk)
    (alk : X →ₗ[K] Vl) (alj : X →ₗ[K] Vl) (ali : X →ₗ[K] Vl)
    (Lkj : Vj →ₗ[K] Vk) (Llk : Vk →ₗ[K] Vl) (Llj : Vj →ₗ[K] Vl) :
    affineFormationBianchiCurrentProfile aji akj aki alk alj ali Lkj Llk Llj 2 =
      -(alk + Llk.comp akj - alj) := rfl

@[simp]
theorem affineFormationBianchiCurrentProfile_three
    {K X Vj Vk Vl : Type*}
    [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Vj] [Module K Vj] [AddCommGroup Vk] [Module K Vk]
    [AddCommGroup Vl] [Module K Vl]
    (aji : X →ₗ[K] Vj) (akj : X →ₗ[K] Vk) (aki : X →ₗ[K] Vk)
    (alk : X →ₗ[K] Vl) (alj : X →ₗ[K] Vl) (ali : X →ₗ[K] Vl)
    (Lkj : Vj →ₗ[K] Vk) (Llk : Vk →ₗ[K] Vl) (Llj : Vj →ₗ[K] Vl) :
    affineFormationBianchiCurrentProfile aji akj aki alk alj ali Lkj Llk Llj 3 =
      -(Llk.comp Lkj - Llj).comp aji := rfl

@[simp]
theorem affineFormationBianchiCurrentProfile_four
    {K X Vj Vk Vl : Type*}
    [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Vj] [Module K Vj] [AddCommGroup Vk] [Module K Vk]
    [AddCommGroup Vl] [Module K Vl]
    (aji : X →ₗ[K] Vj) (akj : X →ₗ[K] Vk) (aki : X →ₗ[K] Vk)
    (alk : X →ₗ[K] Vl) (alj : X →ₗ[K] Vl) (ali : X →ₗ[K] Vl)
    (Lkj : Vj →ₗ[K] Vk) (Llk : Vk →ₗ[K] Vl) (Llj : Vj →ₗ[K] Vl) :
    affineFormationBianchiCurrentProfile aji akj aki alk alj ali Lkj Llk Llj 4 =
      -(alj + Llj.comp aji - ali) := rfl

/-- The affine-formation Bianchi profile has total current zero. -/
theorem affineFormationBianchiCurrentProfile_sum_eq_zero
    {K X Vj Vk Vl : Type*}
    [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Vj] [Module K Vj]
    [AddCommGroup Vk] [Module K Vk] [AddCommGroup Vl] [Module K Vl]
    (aji : X →ₗ[K] Vj) (akj : X →ₗ[K] Vk) (aki : X →ₗ[K] Vk)
    (alk : X →ₗ[K] Vl) (alj : X →ₗ[K] Vl) (ali : X →ₗ[K] Vl)
    (Lkj : Vj →ₗ[K] Vk) (Llk : Vk →ₗ[K] Vl) (Llj : Vj →ₗ[K] Vl) :
    (affineFormationBianchiCurrentProfile aji akj aki alk alj ali Lkj Llk Llj).sum
      (fun _ z => z) = 0 := by
  rw [Finsupp.sum_fintype _ _ (by intro; rfl)]
  change ∑ i : Fin 5, (![Llk.comp (akj + Lkj.comp aji - aki),
    alk + Llk.comp aki - ali, -(alk + Llk.comp akj - alj),
    -(Llk.comp Lkj - Llj).comp aji,
    -(alj + Llj.comp aji - ali)] : Fin 5 → (X →ₗ[K] Vl)) i = 0
  simp [Fin.sum_univ_succ]
  have h := bianchi_current (Vi := X) aji akj aki alk alj ali Lkj Llk Llj
  have hzero :
      (Llk.comp (akj + Lkj.comp aji - aki) + (alk + Llk.comp aki - ali)) -
        ((alk + Llk.comp akj - alj) + (Llk.comp Lkj - Llj).comp aji +
          (alj + Llj.comp aji - ali)) = 0 := sub_eq_zero.mpr h
  abel_nf at hzero ⊢
  exact hzero

/-- Every nonzero Bianchi current channel has a distinct nonzero companion channel. -/
theorem affineFormationBianchiCurrentProfile_exists_other_nonzero_channel
    {K X Vj Vk Vl : Type*}
    [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Vj] [Module K Vj] [AddCommGroup Vk] [Module K Vk]
    [AddCommGroup Vl] [Module K Vl]
    (aji : X →ₗ[K] Vj) (akj : X →ₗ[K] Vk) (aki : X →ₗ[K] Vk)
    (alk : X →ₗ[K] Vl) (alj : X →ₗ[K] Vl) (ali : X →ₗ[K] Vl)
    (Lkj : Vj →ₗ[K] Vk) (Llk : Vk →ₗ[K] Vl) (Llj : Vj →ₗ[K] Vl)
    {i : Fin 5}
    (hi : affineFormationBianchiCurrentProfile
      aji akj aki alk alj ali Lkj Llk Llj i ≠ 0) :
    ∃ j : Fin 5, j ≠ i ∧
      affineFormationBianchiCurrentProfile
        aji akj aki alk alj ali Lkj Llk Llj j ≠ 0 :=
  finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (affineFormationBianchiCurrentProfile aji akj aki alk alj ali Lkj Llk Llj)
    (affineFormationBianchiCurrentProfile_sum_eq_zero
      aji akj aki alk alj ali Lkj Llk Llj) hi

/-- A nonzero Bianchi current profile occupies at least two channels. -/
theorem affineFormationBianchiCurrentProfile_two_le_support_card
    {K X Vj Vk Vl : Type*}
    [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Vj] [Module K Vj] [AddCommGroup Vk] [Module K Vk]
    [AddCommGroup Vl] [Module K Vl]
    (aji : X →ₗ[K] Vj) (akj : X →ₗ[K] Vk) (aki : X →ₗ[K] Vk)
    (alk : X →ₗ[K] Vl) (alj : X →ₗ[K] Vl) (ali : X →ₗ[K] Vl)
    (Lkj : Vj →ₗ[K] Vk) (Llk : Vk →ₗ[K] Vl) (Llj : Vj →ₗ[K] Vl)
    (hne : affineFormationBianchiCurrentProfile
      aji akj aki alk alj ali Lkj Llk Llj ≠ 0) :
    2 ≤ (affineFormationBianchiCurrentProfile
      aji akj aki alk alj ali Lkj Llk Llj).support.card :=
  finsupp_two_le_support_card_of_sum_eq_zero
    (affineFormationBianchiCurrentProfile aji akj aki alk alj ali Lkj Llk Llj)
    (affineFormationBianchiCurrentProfile_sum_eq_zero
      aji akj aki alk alj ali Lkj Llk Llj) hne

end GaloisForLFunctions.HTGeometry
