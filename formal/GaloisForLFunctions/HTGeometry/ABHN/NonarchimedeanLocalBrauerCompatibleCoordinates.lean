/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicSubgroupCompatibleCoordinates
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalBrauerFactorialTower

/-!
# Compatible coordinates on the factorial local Brauer tower

The factorial unramified cyclic slices exhaust the local Brauer group.  Here their arbitrary
finite cyclic coordinates are recursively normalized so every subgroup inclusion is carried to
the canonical finite-torsion transition inside `ℚ/ℤ`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

theorem localBrauerFactorialDegree_succ (n : ℕ) :
    localBrauerFactorialDegree n * (n + 2) =
      localBrauerFactorialDegree (n + 1) := by
  simp only [localBrauerFactorialDegree, Nat.factorial_succ]
  ring

noncomputable def localBrauerFactorialTransition {m n : ℕ} (hmn : m ≤ n) :
    ZMod (localBrauerFactorialDegree m) →+
      ZMod (localBrauerFactorialDegree n) :=
  zmodRatModIntTransition
    (localBrauerFactorialDegree_ne_zero m)
    (localBrauerFactorialDegree_ne_zero n)
    (localBrauerFactorialDegree_dvd_of_le hmn)

theorem localBrauerFactorialTransition_self (n : ℕ) :
    localBrauerFactorialTransition (le_refl n) =
      AddMonoidHom.id (ZMod (localBrauerFactorialDegree n)) := by
  exact zmodRatModIntTransition_self _ (localBrauerFactorialDegree_ne_zero n)

theorem localBrauerFactorialTransition_comp {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    (localBrauerFactorialTransition hmn).comp
        (localBrauerFactorialTransition hlm) =
      localBrauerFactorialTransition (hlm.trans hmn) := by
  exact zmodRatModIntTransition_comp
    (localBrauerFactorialDegree_ne_zero l)
    (localBrauerFactorialDegree_ne_zero m)
    (localBrauerFactorialDegree_ne_zero n)
    (localBrauerFactorialDegree_dvd_of_le hlm)
    (localBrauerFactorialDegree_dvd_of_le hmn)

noncomputable def localBrauerFactorialInclusion
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {m n : ℕ} (hmn : m ≤ n) :
    localBrauerFactorialSlice K m →+ localBrauerFactorialSlice K n :=
  AddSubgroup.inclusion (localBrauerFactorialSlice_mono K hmn)

noncomputable def localBrauerFactorialCompatibleAddEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (n : ℕ) → ZMod (localBrauerFactorialDegree n) ≃+
      localBrauerFactorialSlice K n
  | 0 => Classical.choice (localBrauerFactorialSlice_addEquiv K 0)
  | n + 1 => Classical.choose (exists_zmod_addEquiv_of_subgroup_extension
      (localBrauerFactorialSlice K n) (localBrauerFactorialSlice K (n + 1))
      (localBrauerFactorialSlice_mono K (Nat.le_succ n))
      (localBrauerFactorialDegree_ne_zero n)
      (localBrauerFactorialDegree_ne_zero (n + 1))
      (by omega)
      (localBrauerFactorialDegree_succ n)
      (localBrauerFactorialCompatibleAddEquiv K n)
      (Classical.choice (localBrauerFactorialSlice_addEquiv K (n + 1))))

theorem localBrauerFactorialCompatibleAddEquiv_succ
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    (localBrauerFactorialInclusion K (Nat.le_succ n)).comp
        (localBrauerFactorialCompatibleAddEquiv K n).toAddMonoidHom =
      (localBrauerFactorialCompatibleAddEquiv K (n + 1)).toAddMonoidHom.comp
        (localBrauerFactorialTransition (Nat.le_succ n)) := by
  simpa only [localBrauerFactorialInclusion, localBrauerFactorialTransition,
    localBrauerFactorialCompatibleAddEquiv] using
    Classical.choose_spec (exists_zmod_addEquiv_of_subgroup_extension
      (localBrauerFactorialSlice K n) (localBrauerFactorialSlice K (n + 1))
      (localBrauerFactorialSlice_mono K (Nat.le_succ n))
      (localBrauerFactorialDegree_ne_zero n)
      (localBrauerFactorialDegree_ne_zero (n + 1))
      (by omega)
      (localBrauerFactorialDegree_succ n)
      (localBrauerFactorialCompatibleAddEquiv K n)
      (Classical.choice (localBrauerFactorialSlice_addEquiv K (n + 1))))

theorem zmodSubgroupTowerCompatible_of_succ
    {A : Type*} [AddGroup A] (S : ℕ → AddSubgroup A) (d : ℕ → ℕ)
    (τ : ∀ {m n : ℕ}, m ≤ n → ZMod (d m) →+ ZMod (d n))
    (hτself : ∀ n, τ (le_refl n) = AddMonoidHom.id (ZMod (d n)))
    (hτcomp : ∀ {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n),
      (τ hmn).comp (τ hlm) = τ (hlm.trans hmn))
    (e : ∀ n, ZMod (d n) ≃+ S n)
    (hmono : ∀ {m n : ℕ}, m ≤ n → S m ≤ S n)
    (hsucc : ∀ n,
      (AddSubgroup.inclusion (hmono (Nat.le_succ n))).comp (e n).toAddMonoidHom =
        (e (n + 1)).toAddMonoidHom.comp (τ (Nat.le_succ n)))
    {m n : ℕ} (hmn : m ≤ n) (x : ZMod (d m)) :
    AddSubgroup.inclusion (hmono hmn) (e m x) = e n (τ hmn x) := by
  induction n with
  | zero =>
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      rw [hτself]
      rfl
  | succ n ih =>
      by_cases hmeq : m = n + 1
      · subst m
        rw [hτself]
        rfl
      · have hmn' : m ≤ n := by omega
        have ihx := ih hmn'
        have hs := DFunLike.congr_fun
          (hsucc n) (τ hmn' x)
        apply Subtype.ext
        have ihval := congrArg Subtype.val ihx
        have hsval := congrArg Subtype.val hs
        change (e m x : A) = (e (n + 1) (τ hmn x) : A)
        change (e m x : A) = (e n (τ hmn' x) : A) at ihval
        change (e n (τ hmn' x) : A) =
          (e (n + 1) (τ (Nat.le_succ n) (τ hmn' x)) : A) at hsval
        rw [ihval, hsval]
        congr 1
        have hcomp := DFunLike.congr_fun
          (hτcomp hmn' (Nat.le_succ n)) x
        exact congrArg (e (n + 1)) hcomp

theorem localBrauerFactorialCompatibleAddEquiv_of_le
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {m n : ℕ} (hmn : m ≤ n)
    (x : ZMod (localBrauerFactorialDegree m)) :
    localBrauerFactorialInclusion K hmn
        (localBrauerFactorialCompatibleAddEquiv K m x) =
      localBrauerFactorialCompatibleAddEquiv K n
        (localBrauerFactorialTransition hmn x) := by
  exact zmodSubgroupTowerCompatible_of_succ
    (localBrauerFactorialSlice K) localBrauerFactorialDegree
    (@localBrauerFactorialTransition)
    localBrauerFactorialTransition_self
    (@localBrauerFactorialTransition_comp)
    (localBrauerFactorialCompatibleAddEquiv K)
    (localBrauerFactorialSlice_mono K)
    (localBrauerFactorialCompatibleAddEquiv_succ K)
    hmn x

end

end GaloisForLFunctions.HTGeometry.ABHN
