import GaloisForLFunctions.HTGeometry.SteinbergFinFourWeylTorusTransport
import GaloisForLFunctions.HTGeometry.SteinbergTWTWeylKernel
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Rank-four simple-Weyl Coxeter kernel

This closes the finite type-`A₃` step in Milnor's Steinberg-symbol argument.  Modulo the
full torus, unit Weyl factors satisfy the adjacent-transposition Coxeter relations.  A closed
normal-form proof shows that a simple-Weyl element with diagonal matrix image has trivial
quotient class.  Together with the existing torus normal form, this yields `K₂ =` the
Steinberg-symbol subgroup at rank four.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {F : Type*} [Field F]

abbrev fin4WeylSubgroup : Subgroup (SteinbergGroup F (Fin 4)) :=
  steinbergWeylWordSubgroup (F := F) (n := Fin 4)

theorem fin4TorusSubgroup_le_weyl :
    fin4TorusSubgroup (F := F) ≤ fin4WeylSubgroup (F := F) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨i, j, hij, u, rfl⟩
  rw [steinbergTorus]
  exact (fin4WeylSubgroup (F := F)).mul_mem
    (Subgroup.subset_closure ⟨i, j, hij, u, rfl⟩)
    (Subgroup.subset_closure ⟨i, j, hij, (-1 : Fˣ), rfl⟩)

theorem fin4WeylSubgroup_le_normalizer_torus :
    fin4WeylSubgroup (F := F) ≤ Subgroup.normalizer (fin4TorusSubgroup (F := F)) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx t ht
  obtain ⟨word, rfl⟩ := SteinbergWeylWord.exists_of_mem_subgroup hx
  exact fin4_weylWord_conj_torusSubgroup_mem word ht

local instance steinbergFinFourSimpleWeylCoxeterLocalInst1 : ((fin4TorusSubgroup (F := F)).subgroupOf (fin4WeylSubgroup (F := F))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer fin4TorusSubgroup_le_weyl).mpr
    fin4WeylSubgroup_le_normalizer_torus

abbrev fin4WeylTorusQuotient :=
  (fin4WeylSubgroup (F := F)) ⧸
    (fin4TorusSubgroup (F := F)).subgroupOf (fin4WeylSubgroup (F := F))

def fin4WeylTorusMk (x : SteinbergGroup F (Fin 4))
    (hx : x ∈ fin4WeylSubgroup (F := F)) : fin4WeylTorusQuotient (F := F) :=
  QuotientGroup.mk ⟨x, hx⟩

theorem fin4WeylTorusMk_eq_one_iff {x : SteinbergGroup F (Fin 4)}
    (hx : x ∈ fin4WeylSubgroup (F := F)) :
    fin4WeylTorusMk x hx = 1 ↔ x ∈ fin4TorusSubgroup (F := F) := by
  exact QuotientGroup.eq_one_iff _

theorem fin4WeylTorusMk_eq_iff {x y : SteinbergGroup F (Fin 4)}
    (hx : x ∈ fin4WeylSubgroup (F := F)) (hy : y ∈ fin4WeylSubgroup (F := F)) :
    fin4WeylTorusMk x hx = fin4WeylTorusMk y hy ↔
      x * y⁻¹ ∈ fin4TorusSubgroup (F := F) := by
  change QuotientGroup.mk (⟨x, hx⟩ : fin4WeylSubgroup (F := F))
      = QuotientGroup.mk (⟨y, hy⟩ : fin4WeylSubgroup (F := F)) ↔
        (⟨x, hx⟩ : fin4WeylSubgroup (F := F)) * (⟨y, hy⟩ : fin4WeylSubgroup (F := F))⁻¹
          ∈ (fin4TorusSubgroup (F := F)).subgroupOf (fin4WeylSubgroup (F := F))
  simpa only [div_eq_mul_inv] using (@QuotientGroup.eq_iff_div_mem
    (fin4WeylSubgroup (F := F)) _
    ((fin4TorusSubgroup (F := F)).subgroupOf (fin4WeylSubgroup (F := F))) _
    ⟨x, hx⟩ ⟨y, hy⟩)

theorem fin4_weyl_mem_weylSubgroup {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    steinbergWeyl hij u ∈ fin4WeylSubgroup (F := F) :=
  Subgroup.subset_closure ⟨i, j, hij, u, rfl⟩

def fin4WeylTorusWeyl {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    fin4WeylTorusQuotient (F := F) :=
  fin4WeylTorusMk (steinbergWeyl hij u) (fin4_weyl_mem_weylSubgroup hij u)

theorem fin4WeylTorusMk_mul {x y : SteinbergGroup F (Fin 4)}
    (hx : x ∈ fin4WeylSubgroup (F := F)) (hy : y ∈ fin4WeylSubgroup (F := F)) :
    fin4WeylTorusMk (x * y) ((fin4WeylSubgroup (F := F)).mul_mem hx hy)
      = fin4WeylTorusMk x hx * fin4WeylTorusMk y hy := by
  rfl

theorem fin4WeylTorusMk_eq_of_eq {x y : SteinbergGroup F (Fin 4)}
    (hx : x ∈ fin4WeylSubgroup (F := F)) (hy : y ∈ fin4WeylSubgroup (F := F))
    (hxy : x = y) : fin4WeylTorusMk x hx = fin4WeylTorusMk y hy := by
  subst y
  rfl

theorem fin4WeylTorusMk_torus_eq_one {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    fin4WeylTorusMk (steinbergTorus hij u) (fin4TorusSubgroup_le_weyl
      (Subgroup.subset_closure ⟨i, j, hij, u, rfl⟩)) = 1 := by
  exact fin4WeylTorusMk_eq_one_iff _ |>.2 (Subgroup.subset_closure ⟨i, j, hij, u, rfl⟩)

theorem fin4WeylTorusWeyl_sq {i j : Fin 4} (hij : i ≠ j) :
    fin4WeylTorusWeyl hij (1 : Fˣ) * fin4WeylTorusWeyl hij (1 : Fˣ) = 1 := by
  have hneg : steinbergWeyl hij (-1 : Fˣ) = (steinbergWeyl hij (1 : Fˣ))⁻¹ := by
    simpa using steinbergWeyl_neg hij (1 : Fˣ)
  have hsq : steinbergWeyl hij (1 : Fˣ) * steinbergWeyl hij (1 : Fˣ)
      = (steinbergTorus hij (-1 : Fˣ))⁻¹ := by
    rw [steinbergTorus, hneg, mul_inv_rev]
    simp
  change fin4WeylTorusMk (steinbergWeyl hij (1 : Fˣ)) _
    * fin4WeylTorusMk (steinbergWeyl hij (1 : Fˣ)) _ = 1
  rw [← fin4WeylTorusMk_mul]
  apply fin4WeylTorusMk_eq_one_iff _ |>.2
  rw [hsq]
  exact (fin4TorusSubgroup (F := F)).inv_mem
    (Subgroup.subset_closure ⟨i, j, hij, (-1 : Fˣ), rfl⟩)

theorem fin4WeylTorusWeyl_neg_eq {i j : Fin 4} (hij : i ≠ j) :
    fin4WeylTorusWeyl hij (-1 : Fˣ) = fin4WeylTorusWeyl hij (1 : Fˣ) := by
  have hneg : steinbergWeyl hij (1 : Fˣ) = (steinbergWeyl hij (-1 : Fˣ))⁻¹ := by
    simpa using steinbergWeyl_neg hij (-1 : Fˣ)
  have hprod : fin4WeylTorusWeyl hij (-1 : Fˣ)
      * fin4WeylTorusWeyl hij (1 : Fˣ) = 1 := by
    change fin4WeylTorusMk (steinbergWeyl hij (-1 : Fˣ)) _
      * fin4WeylTorusMk (steinbergWeyl hij (1 : Fˣ)) _ = 1
    rw [← fin4WeylTorusMk_mul]
    change fin4WeylTorusMk
      (steinbergWeyl hij (-1 : Fˣ) * steinbergWeyl hij (1 : Fˣ)) _ = 1
    apply fin4WeylTorusMk_eq_one_iff _ |>.2
    rw [hneg, mul_inv_cancel]
    exact Subgroup.one_mem _
  calc fin4WeylTorusWeyl hij (-1 : Fˣ)
      = (fin4WeylTorusWeyl hij (1 : Fˣ))⁻¹ := eq_inv_of_mul_eq_one_left hprod
    _ = fin4WeylTorusWeyl hij (1 : Fˣ) :=
      (eq_inv_of_mul_eq_one_left (fin4WeylTorusWeyl_sq hij)).symm

theorem fin4WeylTorusWeyl_reverse {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    fin4WeylTorusWeyl hij (1 : Fˣ) = fin4WeylTorusWeyl (Ne.symm hij) (1 : Fˣ) := by
  calc fin4WeylTorusWeyl hij (1 : Fˣ)
      = fin4WeylTorusWeyl (Ne.symm hij) (-1 : Fˣ) :=
        fin4WeylTorusMk_eq_of_eq _ _ (steinbergWeyl_reverse hij hik hjk (1 : Fˣ))
    _ = fin4WeylTorusWeyl (Ne.symm hij) (1 : Fˣ) :=
      fin4WeylTorusWeyl_neg_eq (Ne.symm hij)

theorem fin4WeylTorusWeyl_triangle {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    fin4WeylTorusWeyl hij (1 : Fˣ)
      = fin4WeylTorusWeyl hik (1 : Fˣ)
        * fin4WeylTorusWeyl (Ne.symm hjk) (1 : Fˣ)
        * fin4WeylTorusWeyl hik (1 : Fˣ) := by
  let hx := fin4_weyl_mem_weylSubgroup hij (1 : Fˣ)
  let hy := fin4_weyl_mem_weylSubgroup hik (1 : Fˣ)
  let hz := fin4_weyl_mem_weylSubgroup (Ne.symm hjk) (1 : Fˣ)
  let hn := fin4_weyl_mem_weylSubgroup hik (-1 : Fˣ)
  have htri := steinbergWeyl_triangle hij hik hjk (1 : Fˣ)
  calc
    fin4WeylTorusWeyl hij (1 : Fˣ)
        = fin4WeylTorusMk
            (steinbergWeyl hik (1 : Fˣ) * steinbergWeyl (Ne.symm hjk) (1 : Fˣ)
              * steinbergWeyl hik (-1 : Fˣ))
            ((fin4WeylSubgroup (F := F)).mul_mem
              ((fin4WeylSubgroup (F := F)).mul_mem hy hz) hn) :=
          fin4WeylTorusMk_eq_of_eq hx _ htri.symm
    _ = (fin4WeylTorusWeyl hik (1 : Fˣ)
          * fin4WeylTorusWeyl (Ne.symm hjk) (1 : Fˣ))
        * fin4WeylTorusWeyl hik (-1 : Fˣ) := by
          rw [fin4WeylTorusMk_mul, fin4WeylTorusMk_mul]
          · rfl
          · exact (fin4WeylSubgroup (F := F)).mul_mem hy hz
    _ = fin4WeylTorusWeyl hik (1 : Fˣ)
        * fin4WeylTorusWeyl (Ne.symm hjk) (1 : Fˣ)
        * fin4WeylTorusWeyl hik (1 : Fˣ) := by
          rw [fin4WeylTorusWeyl_neg_eq]

theorem steinbergWeyl_commute_disjoint {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l)
    (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) (u v : Fˣ) :
    steinbergWeyl hij u * steinbergWeyl hkl v
      = steinbergWeyl hkl v * steinbergWeyl hij u := by
  have hcomm₁ : steinbergWeyl hij u * steinbergX hkl (v : F)
      = steinbergX hkl (v : F) * steinbergWeyl hij u := by
    have hswap_k : Equiv.swap i j k = k :=
      Equiv.swap_apply_of_ne_of_ne hki hkj
    have hswap_l : Equiv.swap i j l = l :=
      Equiv.swap_apply_of_ne_of_ne hli hlj
    have hconj : steinbergWeyl hij u * steinbergX hkl (v : F) * (steinbergWeyl hij u)⁻¹
        = steinbergX hkl (v : F) := by
      simpa [steinbergWeylRootScale, hki, hkj, hli, hlj, hswap_k, hswap_l] using
        (steinbergWeyl_conj_root_disjoint hij hkl hki hkj hli hlj u (v : F))
    calc steinbergWeyl hij u * steinbergX hkl (v : F)
        = (steinbergWeyl hij u * steinbergX hkl (v : F)
          * (steinbergWeyl hij u)⁻¹) * steinbergWeyl hij u := by group
      _ = steinbergX hkl (v : F) * steinbergWeyl hij u := by rw [hconj]
  have hcomm₂ : steinbergWeyl hij u
      * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
      = steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F)) * steinbergWeyl hij u := by
    have hswap_k : Equiv.swap i j k = k :=
      Equiv.swap_apply_of_ne_of_ne hki hkj
    have hswap_l : Equiv.swap i j l = l :=
      Equiv.swap_apply_of_ne_of_ne hli hlj
    have hconj : steinbergWeyl hij u
        * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F)) * (steinbergWeyl hij u)⁻¹
        = steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F)) := by
      simpa [steinbergWeylRootScale, hki, hkj, hli, hlj, hswap_k, hswap_l] using
        (steinbergWeyl_conj_root_disjoint hij (Ne.symm hkl)
          hli hlj hki hkj u (-((v⁻¹ : Fˣ) : F)))
    calc steinbergWeyl hij u * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
        = (steinbergWeyl hij u * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
          * (steinbergWeyl hij u)⁻¹) * steinbergWeyl hij u := by group
      _ = steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F)) * steinbergWeyl hij u := by rw [hconj]
  rw [steinbergWeyl, steinbergWeyl]
  calc
    (steinbergX hij (u : F) * steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F))
        * steinbergX hij (u : F))
      * (steinbergX hkl (v : F) * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
        * steinbergX hkl (v : F))
      = steinbergX hkl (v : F) * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
        * steinbergX hkl (v : F)
        * (steinbergX hij (u : F) * steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F))
          * steinbergX hij (u : F)) := by
          change steinbergWeyl hij u * steinbergWeyl hkl v
            = steinbergWeyl hkl v * steinbergWeyl hij u
          rw [steinbergWeyl]
          calc steinbergWeyl hij u
                * (steinbergX hkl (v : F)
                  * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
                  * steinbergX hkl (v : F))
              = (steinbergWeyl hij u * steinbergX hkl (v : F))
                * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
                * steinbergX hkl (v : F) := by group
            _ = (steinbergX hkl (v : F) * steinbergWeyl hij u)
                * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
                * steinbergX hkl (v : F) := by rw [hcomm₁]
            _ = steinbergX hkl (v : F)
                * (steinbergWeyl hij u
                  * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F)))
                * steinbergX hkl (v : F) := by group
            _ = steinbergX hkl (v : F)
                * (steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
                  * steinbergWeyl hij u)
                * steinbergX hkl (v : F) := by rw [hcomm₂]
            _ = steinbergX hkl (v : F)
                * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
                * (steinbergWeyl hij u * steinbergX hkl (v : F)) := by group
            _ = steinbergX hkl (v : F)
                * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
                * (steinbergX hkl (v : F) * steinbergWeyl hij u) := by rw [hcomm₁]
            _ = _ := by
              change steinbergX hkl (v : F)
                  * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
                  * (steinbergX hkl (v : F)
                    * (steinbergX hij (u : F)
                      * steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F))
                      * steinbergX hij (u : F)))
                = (steinbergX hkl (v : F)
                    * steinbergX (Ne.symm hkl) (-((v⁻¹ : Fˣ) : F))
                    * steinbergX hkl (v : F))
                  * (steinbergX hij (u : F)
                    * steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F))
                    * steinbergX hij (u : F))
              group

abbrev fin4q01 : fin4WeylTorusQuotient (F := F) :=
  fin4WeylTorusWeyl (by decide : (0 : Fin 4) ≠ 1) (1 : Fˣ)

abbrev fin4q12 : fin4WeylTorusQuotient (F := F) :=
  fin4WeylTorusWeyl (by decide : (1 : Fin 4) ≠ 2) (1 : Fˣ)

abbrev fin4q23 : fin4WeylTorusQuotient (F := F) :=
  fin4WeylTorusWeyl (by decide : (2 : Fin 4) ≠ 3) (1 : Fˣ)

theorem fin4q01_sq : fin4q01 (F := F) * fin4q01 (F := F) = 1 :=
  fin4WeylTorusWeyl_sq (by decide : (0 : Fin 4) ≠ 1)

theorem fin4q12_sq : fin4q12 (F := F) * fin4q12 (F := F) = 1 :=
  fin4WeylTorusWeyl_sq (by decide : (1 : Fin 4) ≠ 2)

theorem fin4q23_sq : fin4q23 (F := F) * fin4q23 (F := F) = 1 :=
  fin4WeylTorusWeyl_sq (by decide : (2 : Fin 4) ≠ 3)

theorem fin4q01_braid_q12 :
    fin4q01 (F := F) * fin4q12 (F := F) * fin4q01 (F := F)
      = fin4q12 (F := F) * fin4q01 (F := F) * fin4q12 (F := F) := by
  have h02 := fin4WeylTorusWeyl_triangle
    (F := F) (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (2 : Fin 4) ≠ 1)
  have h20 := fin4WeylTorusWeyl_triangle
    (F := F) (by decide : (2 : Fin 4) ≠ 0) (by decide : (2 : Fin 4) ≠ 1)
      (by decide : (0 : Fin 4) ≠ 1)
  have h02_20 := fin4WeylTorusWeyl_reverse
    (F := F) (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (2 : Fin 4) ≠ 1)
  have h12_21 := fin4WeylTorusWeyl_reverse
    (F := F) (by decide : (1 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 0)
      (by decide : (2 : Fin 4) ≠ 0)
  have h01_10 := fin4WeylTorusWeyl_reverse
    (F := F) (by decide : (0 : Fin 4) ≠ 1) (by decide : (0 : Fin 4) ≠ 2)
      (by decide : (1 : Fin 4) ≠ 2)
  have h21 : fin4WeylTorusWeyl (by decide : (2 : Fin 4) ≠ 1) (1 : Fˣ)
      = fin4q12 (F := F) := by
    simpa [fin4q12] using h12_21.symm
  have h10 : fin4WeylTorusWeyl (by decide : (1 : Fin 4) ≠ 0) (1 : Fˣ)
      = fin4q01 (F := F) := by
    simpa [fin4q01] using h01_10.symm
  calc
    fin4q01 (F := F) * fin4q12 (F := F) * fin4q01 (F := F)
      = fin4WeylTorusWeyl (by decide : (0 : Fin 4) ≠ 2) (1 : Fˣ) := by
          simpa [fin4q01, fin4q12] using h02.symm
    _ = fin4WeylTorusWeyl (by decide : (2 : Fin 4) ≠ 0) (1 : Fˣ) := h02_20
    _ = fin4q12 (F := F) * fin4q01 (F := F) * fin4q12 (F := F) := by
      calc _ = fin4WeylTorusWeyl (by decide : (2 : Fin 4) ≠ 1) (1 : Fˣ)
            * fin4WeylTorusWeyl (by decide : (1 : Fin 4) ≠ 0) (1 : Fˣ)
            * fin4WeylTorusWeyl (by decide : (2 : Fin 4) ≠ 1) (1 : Fˣ) := h20
        _ = fin4q12 (F := F) * fin4q01 (F := F) * fin4q12 (F := F) := by
          rw [h21, h10]

theorem fin4q12_braid_q23 :
    fin4q12 (F := F) * fin4q23 (F := F) * fin4q12 (F := F)
      = fin4q23 (F := F) * fin4q12 (F := F) * fin4q23 (F := F) := by
  have h13 := fin4WeylTorusWeyl_triangle
    (F := F) (by decide : (1 : Fin 4) ≠ 3) (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (3 : Fin 4) ≠ 2)
  have h31 := fin4WeylTorusWeyl_triangle
    (F := F) (by decide : (3 : Fin 4) ≠ 1) (by decide : (3 : Fin 4) ≠ 2)
      (by decide : (1 : Fin 4) ≠ 2)
  have h13_31 := fin4WeylTorusWeyl_reverse
    (F := F) (by decide : (1 : Fin 4) ≠ 3) (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (3 : Fin 4) ≠ 2)
  have h23_32 := fin4WeylTorusWeyl_reverse
    (F := F) (by decide : (2 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 1)
      (by decide : (3 : Fin 4) ≠ 1)
  have h12_21 := fin4WeylTorusWeyl_reverse
    (F := F) (by decide : (1 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3)
      (by decide : (2 : Fin 4) ≠ 3)
  have h32 : fin4WeylTorusWeyl (by decide : (3 : Fin 4) ≠ 2) (1 : Fˣ)
      = fin4q23 (F := F) := by
    simpa [fin4q23] using h23_32.symm
  have h21 : fin4WeylTorusWeyl (by decide : (2 : Fin 4) ≠ 1) (1 : Fˣ)
      = fin4q12 (F := F) := by
    simpa [fin4q12] using h12_21.symm
  calc
    fin4q12 (F := F) * fin4q23 (F := F) * fin4q12 (F := F)
      = fin4WeylTorusWeyl (by decide : (1 : Fin 4) ≠ 3) (1 : Fˣ) := by
          simpa [fin4q12, fin4q23] using h13.symm
    _ = fin4WeylTorusWeyl (by decide : (3 : Fin 4) ≠ 1) (1 : Fˣ) := h13_31
    _ = fin4q23 (F := F) * fin4q12 (F := F) * fin4q23 (F := F) := by
      calc _ = fin4WeylTorusWeyl (by decide : (3 : Fin 4) ≠ 2) (1 : Fˣ)
            * fin4WeylTorusWeyl (by decide : (2 : Fin 4) ≠ 1) (1 : Fˣ)
            * fin4WeylTorusWeyl (by decide : (3 : Fin 4) ≠ 2) (1 : Fˣ) := h31
        _ = fin4q23 (F := F) * fin4q12 (F := F) * fin4q23 (F := F) := by
          rw [h32, h21]

theorem fin4q01_comm_q23 :
    fin4q01 (F := F) * fin4q23 (F := F)
      = fin4q23 (F := F) * fin4q01 (F := F) := by
  apply fin4WeylTorusMk_eq_of_eq
  exact steinbergWeyl_commute_disjoint
    (by decide : (0 : Fin 4) ≠ 1) (by decide : (2 : Fin 4) ≠ 3)
    (by decide : (2 : Fin 4) ≠ 0) (by decide : (2 : Fin 4) ≠ 1)
    (by decide : (3 : Fin 4) ≠ 0) (by decide : (3 : Fin 4) ≠ 1) 1 1

section A3Normal

variable {Q : Type*} [Group Q] {a b c : Q}

def a3P (a b : Q) : Set Q := {1, a, b, a * b, b * a, a * b * a}

def a3R (a b c : Q) : Set Q := {1, c, c * b, c * b * a}

def a3Normal (a b c x : Q) : Prop :=
  ∃ p ∈ a3P a b, ∃ r ∈ a3R a b c, x = p * r

theorem a3P_mul_a {p : Q} (hp : p ∈ a3P a b) (ha : a * a = 1) :
    p * a ∈ a3P a b := by
  simp only [a3P, Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp [ha]
  · simp
  · simp
  · simp [mul_assoc, ha]
  · simp [mul_assoc, ha]

theorem a3P_mul_b {p : Q} (hp : p ∈ a3P a b) (hb : b * b = 1)
    (hab : a * b * a = b * a * b) : p * b ∈ a3P a b := by
  simp only [a3P, Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp [hb]
  · simp [mul_assoc, hb]
  · simp [hab]
  · simp [hab, mul_assoc, hb]

theorem a3Normal_mul_a {x : Q} (hx : a3Normal a b c x) (ha : a * a = 1)
    (hac : a * c = c * a) : a3Normal a b c (x * a) := by
  obtain ⟨p, hp, r, hr, rfl⟩ := hx
  simp only [a3R, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with hr | hr | hr | hr
  · refine ⟨p * a, a3P_mul_a hp ha, 1, by simp [a3R], ?_⟩
    subst r
    group
  · refine ⟨p * a, a3P_mul_a hp ha, c, by simp [a3R], ?_⟩
    subst r
    calc p * c * a = p * (c * a) := by group
      _ = p * (a * c) := by rw [hac]
      _ = (p * a) * c := by group
  · refine ⟨p, hp, c * b * a, by simp [a3R], ?_⟩
    subst r
    group
  · refine ⟨p, hp, c * b, by simp [a3R], ?_⟩
    subst r
    calc p * (c * b * a) * a = p * (c * b) * (a * a) := by group
      _ = p * (c * b) := by rw [ha, mul_one]

theorem a3Normal_mul_b {x : Q} (hx : a3Normal a b c x) (ha : a * a = 1)
    (hb : b * b = 1)
    (hab : a * b * a = b * a * b) (hac : a * c = c * a) :
    a3Normal a b c (x * b) := by
  obtain ⟨p, hp, r, hr, rfl⟩ := hx
  simp only [a3R, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with hr | hr | hr | hr
  · refine ⟨p * b, a3P_mul_b hp hb hab, 1, by simp [a3R], ?_⟩
    subst r
    group
  · refine ⟨p, hp, c * b, by simp [a3R], ?_⟩
    subst r
    group
  · refine ⟨p, hp, c, by simp [a3R], ?_⟩
    subst r
    calc p * (c * b) * b = p * c * (b * b) := by group
      _ = p * c := by rw [hb, mul_one]
  · refine ⟨p * a, a3P_mul_a hp ha, c * b * a, by simp [a3R], ?_⟩
    subst r
    calc p * (c * b * a) * b = p * c * (b * a * b) := by group
      _ = p * c * (a * b * a) := by rw [← hab]
      _ = p * (c * a) * (b * a) := by group
      _ = p * (a * c) * (b * a) := by rw [hac]
      _ = p * a * (c * b * a) := by group

theorem a3Normal_mul_c {x : Q} (hx : a3Normal a b c x) (hb : b * b = 1)
    (hc : c * c = 1)
    (hab : a * b * a = b * a * b) (hbc : b * c * b = c * b * c)
    (hac : a * c = c * a) :
    a3Normal a b c (x * c) := by
  obtain ⟨p, hp, r, hr, rfl⟩ := hx
  simp only [a3R, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with hr | hr | hr | hr
  · refine ⟨p, hp, c, by simp [a3R], ?_⟩
    subst r
    group
  · refine ⟨p, hp, 1, by simp [a3R], ?_⟩
    subst r
    simp [mul_assoc, hc]
  · refine ⟨p * b, a3P_mul_b hp hb hab, c * b, by simp [a3R], ?_⟩
    subst r
    calc p * (c * b) * c = p * (c * b * c) := by group
      _ = p * (b * c * b) := by rw [← hbc]
      _ = (p * b) * (c * b) := by group
  · refine ⟨p * b, a3P_mul_b hp hb hab, c * b * a, by simp [a3R], ?_⟩
    subst r
    calc p * (c * b * a) * c = p * (c * b) * (a * c) := by group
      _ = p * (c * b) * (c * a) := by rw [hac]
      _ = p * (c * b * c) * a := by group
      _ = p * (b * c * b) * a := by rw [← hbc]
      _ = (p * b) * (c * b * a) := by group

theorem a3Normal_of_mem_monoid_closure {x : Q}
    (hx : x ∈ Submonoid.closure ({a, b, c} : Set Q))
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b * a = b * a * b) (hbc : b * c * b = c * b * c)
    (hac : a * c = c * a) : a3Normal a b c x := by
  induction hx using Submonoid.closure_induction_right with
  | one => exact ⟨1, by simp [a3P], 1, by simp [a3R], by simp⟩
  | mul_right x _ y hy ih =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact a3Normal_mul_a ih ha hac
    · exact a3Normal_mul_b ih ha hb hab hac
    · exact a3Normal_mul_c ih hb hc hab hbc hac

theorem a3Normal_of_mem_subgroup_closure {x : Q}
    (hx : x ∈ Subgroup.closure ({a, b, c} : Set Q))
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b * a = b * a * b) (hbc : b * c * b = c * b * c)
    (hac : a * c = c * a) : a3Normal a b c x := by
  let M : Submonoid Q := Submonoid.closure ({a, b, c} : Set Q)
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hM_inv : ∀ z, z ∈ M → z⁻¹ ∈ M := by
    intro z hz
    induction hz using Submonoid.closure_induction_left with
    | one => simp [M]
    | mul_left y hy z hz ih =>
      rw [mul_inv_rev]
      apply M.mul_mem ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · rw [ha_inv]
        exact Submonoid.subset_closure (by simp)
      · rw [hb_inv]
        exact Submonoid.subset_closure (by simp)
      · rw [hc_inv]
        exact Submonoid.subset_closure (by simp)
  let H : Subgroup Q :=
    { carrier := M
      one_mem' := M.one_mem
      mul_mem' := M.mul_mem
      inv_mem' := by
        intro z hz
        exact hM_inv z hz }
  have hgens : ({a, b, c} : Set Q) ⊆ H := by
    intro z hz
    change z ∈ M
    exact Submonoid.subset_closure hz
  have hclosure : Subgroup.closure ({a, b, c} : Set Q) ≤ H :=
    (Subgroup.closure_le H).2 hgens
  have hxM : x ∈ M := hclosure hx
  exact a3Normal_of_mem_monoid_closure (by simpa [M] using hxM) ha hb hc hab hbc hac

end A3Normal

theorem fin4WeylTorusWeyl_reverse_any {i j : Fin 4} (hij : i ≠ j) :
    fin4WeylTorusWeyl hij (1 : Fˣ)
      = fin4WeylTorusWeyl (Ne.symm hij) (1 : Fˣ) := by
  obtain ⟨k, hki, hkj⟩ := exists_third_index
    (by decide : Fintype.card (Fin 4) ≥ 3) i j
  exact fin4WeylTorusWeyl_reverse hij hki.symm hkj.symm

abbrev fin4A3Subgroup : Subgroup (fin4WeylTorusQuotient (F := F)) :=
  Subgroup.closure ({fin4q01 (F := F), fin4q12 (F := F), fin4q23 (F := F)} : Set _)

theorem fin4q01_mem_A3Subgroup : fin4q01 (F := F) ∈ fin4A3Subgroup (F := F) :=
  Subgroup.subset_closure (by simp)

theorem fin4q12_mem_A3Subgroup : fin4q12 (F := F) ∈ fin4A3Subgroup (F := F) :=
  Subgroup.subset_closure (by simp)

theorem fin4q23_mem_A3Subgroup : fin4q23 (F := F) ∈ fin4A3Subgroup (F := F) :=
  Subgroup.subset_closure (by simp)

theorem fin4WeylTorusWeyl_mem_A3Subgroup {i j : Fin 4} (hij : i ≠ j) :
    fin4WeylTorusWeyl hij (1 : Fˣ) ∈ fin4A3Subgroup (F := F) := by
  have hsymm {r s : Fin 4} (hrs : r ≠ s) :
      fin4WeylTorusWeyl hrs (1 : Fˣ) ∈ fin4A3Subgroup (F := F) →
        fin4WeylTorusWeyl (Ne.symm hrs) (1 : Fˣ) ∈ fin4A3Subgroup (F := F) := by
    intro h
    rw [← fin4WeylTorusWeyl_reverse_any hrs]
    exact h
  have h02 : fin4WeylTorusWeyl (by decide : (0 : Fin 4) ≠ 2) (1 : Fˣ)
      ∈ fin4A3Subgroup (F := F) := by
    rw [fin4WeylTorusWeyl_triangle
      (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (2 : Fin 4) ≠ 1)]
    exact (fin4A3Subgroup (F := F)).mul_mem
      ((fin4A3Subgroup (F := F)).mul_mem fin4q01_mem_A3Subgroup fin4q12_mem_A3Subgroup)
      fin4q01_mem_A3Subgroup
  have h13 : fin4WeylTorusWeyl (by decide : (1 : Fin 4) ≠ 3) (1 : Fˣ)
      ∈ fin4A3Subgroup (F := F) := by
    rw [fin4WeylTorusWeyl_triangle
      (by decide : (1 : Fin 4) ≠ 3) (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (3 : Fin 4) ≠ 2)]
    exact (fin4A3Subgroup (F := F)).mul_mem
      ((fin4A3Subgroup (F := F)).mul_mem fin4q12_mem_A3Subgroup fin4q23_mem_A3Subgroup)
      fin4q12_mem_A3Subgroup
  have h03 : fin4WeylTorusWeyl (by decide : (0 : Fin 4) ≠ 3) (1 : Fˣ)
      ∈ fin4A3Subgroup (F := F) := by
    rw [fin4WeylTorusWeyl_triangle
      (by decide : (0 : Fin 4) ≠ 3) (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (3 : Fin 4) ≠ 1)]
    exact (fin4A3Subgroup (F := F)).mul_mem
      ((fin4A3Subgroup (F := F)).mul_mem fin4q01_mem_A3Subgroup h13)
      fin4q01_mem_A3Subgroup
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact fin4q01_mem_A3Subgroup
  · exact h02
  · exact h03
  · exact hsymm (by decide : (0 : Fin 4) ≠ 1) fin4q01_mem_A3Subgroup
  · exact (hij rfl).elim
  · exact fin4q12_mem_A3Subgroup
  · exact h13
  · exact hsymm (by decide : (0 : Fin 4) ≠ 2) h02
  · exact hsymm (by decide : (1 : Fin 4) ≠ 2) fin4q12_mem_A3Subgroup
  · exact (hij rfl).elim
  · exact fin4q23_mem_A3Subgroup
  · exact hsymm (by decide : (0 : Fin 4) ≠ 3) h03
  · exact hsymm (by decide : (1 : Fin 4) ≠ 3) h13
  · exact hsymm (by decide : (2 : Fin 4) ≠ 3) fin4q23_mem_A3Subgroup
  · exact (hij rfl).elim

theorem fin4SimpleWeylSubgroup_le_weyl :
    fin4SimpleWeylSubgroup (F := F) ≤ fin4WeylSubgroup (F := F) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨i, j, hij, rfl⟩
  exact fin4_weyl_mem_weylSubgroup hij (1 : Fˣ)

theorem fin4WeylTorusMk_mem_A3Subgroup_of_mem_simpleWeyl
    {s : SteinbergGroup F (Fin 4)} (hs : s ∈ fin4SimpleWeylSubgroup (F := F)) :
    fin4WeylTorusMk s (fin4SimpleWeylSubgroup_le_weyl hs)
      ∈ fin4A3Subgroup (F := F) := by
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, j, hij, rfl⟩ := hx
    exact fin4WeylTorusWeyl_mem_A3Subgroup hij
  | one =>
    change (1 : fin4WeylTorusQuotient (F := F)) ∈ fin4A3Subgroup (F := F)
    exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    have hxW := fin4SimpleWeylSubgroup_le_weyl hx
    have hyW := fin4SimpleWeylSubgroup_le_weyl hy
    change fin4WeylTorusMk (x * y) ((fin4WeylSubgroup (F := F)).mul_mem hxW hyW)
      ∈ fin4A3Subgroup (F := F)
    rw [fin4WeylTorusMk_mul hxW hyW]
    exact (fin4A3Subgroup (F := F)).mul_mem ihx ihy
  | inv x hx ih =>
    have hxW := fin4SimpleWeylSubgroup_le_weyl hx
    change (fin4WeylTorusMk x hxW)⁻¹
      ∈ fin4A3Subgroup (F := F)
    exact (fin4A3Subgroup (F := F)).inv_mem ih

theorem signedMonomial_perm_eq_id_of_isDiag {n : Type*} [DecidableEq n]
    (σ : Equiv.Perm n) (d : n → Fˣ)
    (hdiag : (signedMonomialMatrix σ d).IsDiag) : σ = 1 := by
  apply Equiv.ext
  intro p
  by_contra hp
  have hzero : signedMonomialMatrix σ d (σ p) p = 0 := hdiag hp
  simp [signedMonomialMatrix] at hzero

theorem Matrix.IsDiag.mul {n : Type*} [DecidableEq n] [Fintype n]
    {A B : Matrix n n F} (hA : A.IsDiag) (hB : B.IsDiag) : (A * B).IsDiag := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i = k
  · subst k
    rw [hB hij, mul_zero]
  · rw [hA hik, zero_mul]

theorem Matrix.IsDiag.inv_unit {n : Type*} [DecidableEq n] [Fintype n]
    (A : (Matrix n n F)ˣ) (hA : (A : Matrix n n F).IsDiag) :
    ((A⁻¹ : (Matrix n n F)ˣ) : Matrix n n F).IsDiag := by
  intro i j hij
  have hleft : ((A⁻¹ : (Matrix n n F)ˣ) : Matrix n n F) i i
      * (A : Matrix n n F) i i = 1 := by
    have h := congrFun (congrFun A.inv_val i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
    · simpa using h
    · intro k _ hki
      rw [hA hki, mul_zero]
    · simp
  have hAii : (A : Matrix n n F) i i ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hleft
    exact zero_ne_one hleft
  have hright : (A : Matrix n n F) i i
      * ((A⁻¹ : (Matrix n n F)ˣ) : Matrix n n F) i j = 0 := by
    have h := congrFun (congrFun A.val_inv i) j
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
    · simpa [Matrix.one_apply, hij] using h
    · intro k _ hki
      rw [hA (Ne.symm hki), zero_mul]
    · simp
  exact (mul_eq_zero.mp hright).resolve_left hAii

theorem Matrix.isDiag_single_diag {n : Type*} [DecidableEq n] (i : n) (a : F) :
    (Matrix.single i i a : Matrix n n F).IsDiag := by
  intro p q hpq
  by_cases hpi : p = i
  · subst p
    by_cases hqi : q = i
    · subst q
      exact (hpq rfl).elim
    · simp [Ne.symm hqi]
  · simp [Ne.symm hpi]

theorem diagUnit_isDiag {n : Type*} [DecidableEq n] [Fintype n]
    {i j : n} (hij : i ≠ j) (u : Fˣ) :
    ((diagUnit hij u : (Matrix n n F)ˣ) : Matrix n n F).IsDiag := by
  change (diagMatrix i j u).IsDiag
  exact (Matrix.isDiag_one.add (Matrix.isDiag_single_diag i ((u : F) - 1))).add
    (Matrix.isDiag_single_diag j (((u⁻¹ : Fˣ) : F) - 1))

theorem fin4Torus_matrix_isDiag {t : SteinbergGroup F (Fin 4)}
    (ht : t ∈ fin4TorusSubgroup (F := F)) :
    ((steinbergToGL t : (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F).IsDiag := by
  induction ht using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, j, hij, u, rfl⟩ := hx
    rw [steinbergToGL_torus]
    exact diagUnit_isDiag hij u
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [map_mul, Units.val_mul]
    exact Matrix.IsDiag.mul ihx ihy
  | inv x hx ih =>
    rw [map_inv]
    exact Matrix.IsDiag.inv_unit (steinbergToGL x) ih

namespace SteinbergWeylWord

theorem perm_append {n : Type*} [DecidableEq n] (w v : SteinbergWeylWord F n) :
    (append w v).perm = v.perm.trans w.perm := by
  induction v generalizing w with
  | one => simp [append, perm]
  | snoc v i j hij u ih =>
    simp only [append, perm, ih]
    rw [Equiv.trans_assoc]

end SteinbergWeylWord

abbrev fin4w01 : SteinbergGroup F (Fin 4) :=
  steinbergWeyl (by decide : (0 : Fin 4) ≠ 1) (1 : Fˣ)

abbrev fin4w12 : SteinbergGroup F (Fin 4) :=
  steinbergWeyl (by decide : (1 : Fin 4) ≠ 2) (1 : Fˣ)

abbrev fin4w23 : SteinbergGroup F (Fin 4) :=
  steinbergWeyl (by decide : (2 : Fin 4) ≠ 3) (1 : Fˣ)

def fin4Word01 : SteinbergWeylWord F (Fin 4) :=
  .snoc .one 0 1 (by decide) 1

def fin4Word12 : SteinbergWeylWord F (Fin 4) :=
  .snoc .one 1 2 (by decide) 1

def fin4Word23 : SteinbergWeylWord F (Fin 4) :=
  .snoc .one 2 3 (by decide) 1

theorem fin4A3P_exists_word {p : SteinbergGroup F (Fin 4)}
    (hp : p ∈ a3P fin4w01 fin4w12) :
    ∃ w : SteinbergWeylWord F (Fin 4), w.eval = p ∧ w.perm 3 = 3 ∧
      (w.perm = 1 → p = 1) := by
  simp only [a3P, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp | hp | hp | hp | hp
  · subst p
    exact ⟨.one, by simp [SteinbergWeylWord.eval], by simp [SteinbergWeylWord.perm],
      fun _ => rfl⟩
  · subst p
    refine ⟨fin4Word01, ?_, ?_, ?_⟩
    · rfl
    · change (Equiv.swap 0 1) (3 : Fin 4) = 3
      decide
    · intro h
      exfalso
      have hzero := congrArg (fun e : Equiv.Perm (Fin 4) => e 0) h
      simp [fin4Word01, SteinbergWeylWord.perm] at hzero
  · subst p
    refine ⟨fin4Word12, ?_, ?_, ?_⟩
    · rfl
    · change (Equiv.swap 1 2) (3 : Fin 4) = 3
      decide
    · intro h
      exfalso
      have hone := congrArg (fun e : Equiv.Perm (Fin 4) => e 1) h
      simp [fin4Word12, SteinbergWeylWord.perm] at hone
  · subst p
    refine ⟨SteinbergWeylWord.append fin4Word01 fin4Word12, ?_, ?_, ?_⟩
    · simp [fin4Word01, fin4Word12, SteinbergWeylWord.eval_append,
        SteinbergWeylWord.eval]
    · change (Equiv.swap 0 1) ((Equiv.swap 1 2) (3 : Fin 4)) = 3
      decide
    · intro h
      exfalso
      have hzero := congrArg (fun e : Equiv.Perm (Fin 4) => e 0) h
      simp [SteinbergWeylWord.perm_append, fin4Word01, fin4Word12,
        SteinbergWeylWord.perm] at hzero
      change (1 : Fin 4) = 0 at hzero
      exact (by decide : (1 : Fin 4) ≠ 0) hzero
  · subst p
    refine ⟨SteinbergWeylWord.append fin4Word12 fin4Word01, ?_, ?_, ?_⟩
    · simp [fin4Word01, fin4Word12, SteinbergWeylWord.eval_append,
        SteinbergWeylWord.eval]
    · change (Equiv.swap 1 2) ((Equiv.swap 0 1) (3 : Fin 4)) = 3
      decide
    · intro h
      exfalso
      have hzero := congrArg (fun e : Equiv.Perm (Fin 4) => e 0) h
      simp [SteinbergWeylWord.perm_append, fin4Word01, fin4Word12,
        SteinbergWeylWord.perm] at hzero
  · subst p
    refine ⟨SteinbergWeylWord.append
      (SteinbergWeylWord.append fin4Word01 fin4Word12) fin4Word01, ?_, ?_, ?_⟩
    · simp [fin4Word01, fin4Word12, SteinbergWeylWord.eval_append,
        SteinbergWeylWord.eval]
    · change (Equiv.swap 0 1) ((Equiv.swap 1 2) ((Equiv.swap 0 1) (3 : Fin 4))) = 3
      decide
    · intro h
      exfalso
      have hzero := congrArg (fun e : Equiv.Perm (Fin 4) => e 0) h
      simp [SteinbergWeylWord.perm_append, fin4Word01, fin4Word12,
        SteinbergWeylWord.perm] at hzero
      change (2 : Fin 4) = 0 at hzero
      exact (by decide : (2 : Fin 4) ≠ 0) hzero

theorem fin4A3R_exists_word {r : SteinbergGroup F (Fin 4)}
    (hr : r ∈ a3R fin4w01 fin4w12 fin4w23) :
    ∃ w : SteinbergWeylWord F (Fin 4), w.eval = r ∧ (w.perm 3 = 3 → r = 1) := by
  simp only [a3R, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with hr | hr | hr | hr
  · subst r
    exact ⟨.one, by simp [SteinbergWeylWord.eval], fun _ => rfl⟩
  · subst r
    refine ⟨fin4Word23, rfl, ?_⟩
    intro h
    exfalso
    change (2 : Fin 4) = 3 at h
    exact (by decide : (2 : Fin 4) ≠ 3) h
  · subst r
    refine ⟨SteinbergWeylWord.append fin4Word23 fin4Word12, ?_, ?_⟩
    · simp [fin4Word12, fin4Word23, SteinbergWeylWord.eval_append,
        SteinbergWeylWord.eval]
    · intro h
      exfalso
      change (2 : Fin 4) = 3 at h
      exact (by decide : (2 : Fin 4) ≠ 3) h
  · subst r
    refine ⟨SteinbergWeylWord.append
      (SteinbergWeylWord.append fin4Word23 fin4Word12) fin4Word01, ?_, ?_⟩
    · simp [fin4Word01, fin4Word12, fin4Word23, SteinbergWeylWord.eval_append,
        SteinbergWeylWord.eval]
    · intro h
      exfalso
      change (2 : Fin 4) = 3 at h
      exact (by decide : (2 : Fin 4) ≠ 3) h

theorem steinbergWeylWord_perm_eq_one_of_matrix_isDiag
    (w : SteinbergWeylWord F (Fin 4))
    (hdiag : ((steinbergToGL w.eval : (Matrix (Fin 4) (Fin 4) F)ˣ)
      : Matrix (Fin 4) (Fin 4) F).IsDiag) : w.perm = 1 := by
  apply signedMonomial_perm_eq_id_of_isDiag w.perm w.scale
  rw [← steinbergWeylWord_matrix w]
  exact hdiag

theorem fin4WeylTorusMk_eq_one_of_a3Normal_matrix_isDiag
    {z : SteinbergGroup F (Fin 4)} (hzW : z ∈ fin4WeylSubgroup (F := F))
    (hz : a3Normal fin4w01 fin4w12 fin4w23 z)
    (hdiag : ((steinbergToGL z : (Matrix (Fin 4) (Fin 4) F)ˣ)
      : Matrix (Fin 4) (Fin 4) F).IsDiag) :
    fin4WeylTorusMk z hzW = 1 := by
  obtain ⟨p, hp, r, hr, rfl⟩ := hz
  obtain ⟨wp, hwp, hwpFix, hwpId⟩ := fin4A3P_exists_word hp
  obtain ⟨wr, hwr, hwrCharacter⟩ := fin4A3R_exists_word hr
  let w := SteinbergWeylWord.append wp wr
  have hwdiag : ((steinbergToGL w.eval : (Matrix (Fin 4) (Fin 4) F)ˣ)
      : Matrix (Fin 4) (Fin 4) F).IsDiag := by
    rw [show w = SteinbergWeylWord.append wp wr from rfl,
      SteinbergWeylWord.eval_append, hwp, hwr]
    exact hdiag
  have hwperm : w.perm = 1 := steinbergWeylWord_perm_eq_one_of_matrix_isDiag w hwdiag
  have hcomposition : wp.perm (wr.perm 3) = 3 := by
    have h := congrArg (fun e : Equiv.Perm (Fin 4) => e 3) hwperm
    simpa [w, SteinbergWeylWord.perm_append] using h
  have hwrFix : wr.perm 3 = 3 :=
    wp.perm.injective (hcomposition.trans hwpFix.symm)
  have hrOne : r = 1 := hwrCharacter hwrFix
  have hpdiag : ((steinbergToGL p : (Matrix (Fin 4) (Fin 4) F)ˣ)
      : Matrix (Fin 4) (Fin 4) F).IsDiag := by
    simpa [hrOne] using hdiag
  have hwpdiag : ((steinbergToGL wp.eval : (Matrix (Fin 4) (Fin 4) F)ˣ)
      : Matrix (Fin 4) (Fin 4) F).IsDiag := by
    rw [hwp]
    exact hpdiag
  have hpOne : p = 1 := hwpId (steinbergWeylWord_perm_eq_one_of_matrix_isDiag wp hwpdiag)
  apply (fin4WeylTorusMk_eq_one_iff hzW).2
  simp [hpOne, hrOne]

theorem fin4w01_mem_simpleWeyl : fin4w01 (F := F) ∈ fin4SimpleWeylSubgroup (F := F) :=
  Subgroup.subset_closure ⟨0, 1, by decide, rfl⟩

theorem fin4w12_mem_simpleWeyl : fin4w12 (F := F) ∈ fin4SimpleWeylSubgroup (F := F) :=
  Subgroup.subset_closure ⟨1, 2, by decide, rfl⟩

theorem fin4w23_mem_simpleWeyl : fin4w23 (F := F) ∈ fin4SimpleWeylSubgroup (F := F) :=
  Subgroup.subset_closure ⟨2, 3, by decide, rfl⟩

theorem fin4A3P_mem_simpleWeyl {p : SteinbergGroup F (Fin 4)}
    (hp : p ∈ a3P fin4w01 fin4w12) : p ∈ fin4SimpleWeylSubgroup (F := F) := by
  simp only [a3P, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact fin4w01_mem_simpleWeyl
  · exact fin4w12_mem_simpleWeyl
  · exact (fin4SimpleWeylSubgroup (F := F)).mul_mem fin4w01_mem_simpleWeyl
      fin4w12_mem_simpleWeyl
  · exact (fin4SimpleWeylSubgroup (F := F)).mul_mem fin4w12_mem_simpleWeyl
      fin4w01_mem_simpleWeyl
  · exact (fin4SimpleWeylSubgroup (F := F)).mul_mem
      ((fin4SimpleWeylSubgroup (F := F)).mul_mem fin4w01_mem_simpleWeyl
        fin4w12_mem_simpleWeyl) fin4w01_mem_simpleWeyl

theorem fin4A3R_mem_simpleWeyl {r : SteinbergGroup F (Fin 4)}
    (hr : r ∈ a3R fin4w01 fin4w12 fin4w23) : r ∈ fin4SimpleWeylSubgroup (F := F) := by
  simp only [a3R, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact fin4w23_mem_simpleWeyl
  · exact (fin4SimpleWeylSubgroup (F := F)).mul_mem fin4w23_mem_simpleWeyl
      fin4w12_mem_simpleWeyl
  · exact (fin4SimpleWeylSubgroup (F := F)).mul_mem
      ((fin4SimpleWeylSubgroup (F := F)).mul_mem fin4w23_mem_simpleWeyl
        fin4w12_mem_simpleWeyl) fin4w01_mem_simpleWeyl

theorem fin4A3P_lift {p : fin4WeylTorusQuotient (F := F)}
    (hp : p ∈ a3P (fin4q01 (F := F)) (fin4q12 (F := F))) :
    ∃ (P : SteinbergGroup F (Fin 4)) (hP : P ∈ a3P fin4w01 fin4w12),
      p = fin4WeylTorusMk P
        (fin4SimpleWeylSubgroup_le_weyl (fin4A3P_mem_simpleWeyl hP)) := by
  have h01W := fin4_weyl_mem_weylSubgroup (F := F) (by decide : (0 : Fin 4) ≠ 1) (1 : Fˣ)
  have h12W := fin4_weyl_mem_weylSubgroup (F := F) (by decide : (1 : Fin 4) ≠ 2) (1 : Fˣ)
  simp only [a3P, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨1, by simp [a3P], ?_⟩
    rfl
  · refine ⟨fin4w01, by simp [a3P], ?_⟩
    rfl
  · refine ⟨fin4w12, by simp [a3P], ?_⟩
    rfl
  · refine ⟨fin4w01 * fin4w12, by simp [a3P], ?_⟩
    rw [fin4WeylTorusMk_mul h01W h12W]
    rfl
  · refine ⟨fin4w12 * fin4w01, by simp [a3P], ?_⟩
    rw [fin4WeylTorusMk_mul h12W h01W]
    rfl
  · refine ⟨fin4w01 * fin4w12 * fin4w01, by simp [a3P], ?_⟩
    rw [fin4WeylTorusMk_mul ((fin4WeylSubgroup (F := F)).mul_mem h01W h12W) h01W,
      fin4WeylTorusMk_mul h01W h12W]
    rfl

theorem fin4A3R_lift {r : fin4WeylTorusQuotient (F := F)}
    (hr : r ∈ a3R (fin4q01 (F := F)) (fin4q12 (F := F)) (fin4q23 (F := F))) :
    ∃ (R : SteinbergGroup F (Fin 4)) (hR : R ∈ a3R fin4w01 fin4w12 fin4w23),
      r = fin4WeylTorusMk R
        (fin4SimpleWeylSubgroup_le_weyl (fin4A3R_mem_simpleWeyl hR)) := by
  have h01W := fin4_weyl_mem_weylSubgroup (F := F) (by decide : (0 : Fin 4) ≠ 1) (1 : Fˣ)
  have h12W := fin4_weyl_mem_weylSubgroup (F := F) (by decide : (1 : Fin 4) ≠ 2) (1 : Fˣ)
  have h23W := fin4_weyl_mem_weylSubgroup (F := F) (by decide : (2 : Fin 4) ≠ 3) (1 : Fˣ)
  simp only [a3R, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨1, by simp [a3R], ?_⟩
    rfl
  · refine ⟨fin4w23, by simp [a3R], ?_⟩
    rfl
  · refine ⟨fin4w23 * fin4w12, by simp [a3R], ?_⟩
    rw [fin4WeylTorusMk_mul h23W h12W]
    rfl
  · refine ⟨fin4w23 * fin4w12 * fin4w01, by simp [a3R], ?_⟩
    rw [fin4WeylTorusMk_mul ((fin4WeylSubgroup (F := F)).mul_mem h23W h12W) h01W,
      fin4WeylTorusMk_mul h23W h12W]
    rfl

theorem fin4SimpleWeyl_quotient_a3Normal {s : SteinbergGroup F (Fin 4)}
    (hs : s ∈ fin4SimpleWeylSubgroup (F := F)) :
    a3Normal (fin4q01 (F := F)) (fin4q12 (F := F)) (fin4q23 (F := F))
      (fin4WeylTorusMk s (fin4SimpleWeylSubgroup_le_weyl hs)) := by
  apply a3Normal_of_mem_subgroup_closure
  · change fin4WeylTorusMk s (fin4SimpleWeylSubgroup_le_weyl hs)
      ∈ fin4A3Subgroup (F := F)
    exact fin4WeylTorusMk_mem_A3Subgroup_of_mem_simpleWeyl hs
  · exact fin4q01_sq
  · exact fin4q12_sq
  · exact fin4q23_sq
  · exact fin4q01_braid_q12
  · exact fin4q12_braid_q23
  · exact fin4q01_comm_q23

theorem fin4SimpleWeyl_quotient_a3Normal_lift {s : SteinbergGroup F (Fin 4)}
    (hs : s ∈ fin4SimpleWeylSubgroup (F := F)) :
    ∃ (z : SteinbergGroup F (Fin 4)) (hz : z ∈ fin4SimpleWeylSubgroup (F := F)),
      a3Normal fin4w01 fin4w12 fin4w23 z ∧
      fin4WeylTorusMk s (fin4SimpleWeylSubgroup_le_weyl hs)
        = fin4WeylTorusMk z (fin4SimpleWeylSubgroup_le_weyl hz) := by
  obtain ⟨p, hp, r, hr, hsr⟩ := fin4SimpleWeyl_quotient_a3Normal hs
  obtain ⟨P, hP, hpq⟩ := fin4A3P_lift hp
  obtain ⟨R, hR, hrq⟩ := fin4A3R_lift hr
  refine ⟨P * R, (fin4SimpleWeylSubgroup (F := F)).mul_mem
    (fin4A3P_mem_simpleWeyl hP) (fin4A3R_mem_simpleWeyl hR), ⟨P, hP, R, hR, rfl⟩, ?_⟩
  calc
    fin4WeylTorusMk s (fin4SimpleWeylSubgroup_le_weyl hs) = p * r := hsr
    _ = fin4WeylTorusMk P
        (fin4SimpleWeylSubgroup_le_weyl (fin4A3P_mem_simpleWeyl hP))
        * fin4WeylTorusMk R
          (fin4SimpleWeylSubgroup_le_weyl (fin4A3R_mem_simpleWeyl hR)) := by
          rw [← hpq, ← hrq]
    _ = fin4WeylTorusMk (P * R)
        (fin4SimpleWeylSubgroup_le_weyl
          ((fin4SimpleWeylSubgroup (F := F)).mul_mem
            (fin4A3P_mem_simpleWeyl hP) (fin4A3R_mem_simpleWeyl hR))) := by
          rw [fin4WeylTorusMk_mul]

theorem fin4_simpleWeyl_mem_torus_of_matrix_isDiag {s : SteinbergGroup F (Fin 4)}
    (hs : s ∈ fin4SimpleWeylSubgroup (F := F))
    (hdiag : ((steinbergToGL s : (Matrix (Fin 4) (Fin 4) F)ˣ)
      : Matrix (Fin 4) (Fin 4) F).IsDiag) :
    s ∈ fin4TorusSubgroup (F := F) := by
  obtain ⟨z, hz, hnormal, hqeq⟩ := fin4SimpleWeyl_quotient_a3Normal_lift hs
  have hsW := fin4SimpleWeylSubgroup_le_weyl hs
  have hzW := fin4SimpleWeylSubgroup_le_weyl hz
  have htorus : s * z⁻¹ ∈ fin4TorusSubgroup (F := F) :=
    (fin4WeylTorusMk_eq_iff hsW hzW).1 hqeq
  have htorusDiag := fin4Torus_matrix_isDiag htorus
  have hzinvUnit : (steinbergToGL z)⁻¹
      = (steinbergToGL s)⁻¹ * steinbergToGL (s * z⁻¹) := by
    rw [map_mul, map_inv]
    group
  have hzInvDiag : (((steinbergToGL z)⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ)
      : Matrix (Fin 4) (Fin 4) F).IsDiag := by
    rw [hzinvUnit]
    exact Matrix.IsDiag.mul (Matrix.IsDiag.inv_unit (steinbergToGL s) hdiag) htorusDiag
  have hzDiag : ((steinbergToGL z : (Matrix (Fin 4) (Fin 4) F)ˣ)
      : Matrix (Fin 4) (Fin 4) F).IsDiag := by
    simpa using Matrix.IsDiag.inv_unit ((steinbergToGL z)⁻¹) hzInvDiag
  have hqzOne : fin4WeylTorusMk z hzW = 1 :=
    fin4WeylTorusMk_eq_one_of_a3Normal_matrix_isDiag hzW hnormal hzDiag
  exact (fin4WeylTorusMk_eq_one_iff hsW).1 (hqeq.trans hqzOne)

theorem fin4_simpleWeyl_mem_torus_of_mem_KTwo {s : SteinbergGroup F (Fin 4)}
    (hs : s ∈ fin4SimpleWeylSubgroup (F := F)) (hK : s ∈ KTwo F (Fin 4)) :
    s ∈ fin4TorusSubgroup (F := F) := by
  apply fin4_simpleWeyl_mem_torus_of_matrix_isDiag hs
  rw [(mem_KTwo_iff s).1 hK]
  exact Matrix.isDiag_one

theorem fin4_KTwo_le_torusSubgroup :
    KTwo F (Fin 4) ≤ fin4TorusSubgroup (F := F) := by
  intro x hx
  have hxW : x ∈ fin4WeylSubgroup (F := F) := fin4_KTwo_le_weylWordSubgroup hx
  obtain ⟨t, ht, s, hs, hxs⟩ := fin4_weylWordSubgroup_torus_simple_normal hxW
  have htDiag := fin4Torus_matrix_isDiag ht
  have hxImage : steinbergToGL x = 1 := (mem_KTwo_iff x).1 hx
  have hsImage : steinbergToGL s = (steinbergToGL t)⁻¹ := by
    rw [hxs, map_mul] at hxImage
    calc
      steinbergToGL s = 1 * steinbergToGL s := by simp
      _ = (steinbergToGL t)⁻¹ * (steinbergToGL t * steinbergToGL s) := by group
      _ = (steinbergToGL t)⁻¹ * 1 := by rw [hxImage]
      _ = (steinbergToGL t)⁻¹ := by group
  have hsDiag : ((steinbergToGL s : (Matrix (Fin 4) (Fin 4) F)ˣ)
      : Matrix (Fin 4) (Fin 4) F).IsDiag := by
    rw [hsImage]
    exact Matrix.IsDiag.inv_unit (steinbergToGL t) htDiag
  have hsT : s ∈ fin4TorusSubgroup (F := F) :=
    fin4_simpleWeyl_mem_torus_of_matrix_isDiag hs hsDiag
  rw [hxs]
  exact (fin4TorusSubgroup (F := F)).mul_mem ht hsT

theorem fin4_KTwo_le_steinbergSymbolSubgroup :
    KTwo F (Fin 4) ≤ steinbergSymbolSubgroup F (Fin 4) := by
  intro x hx
  have hxT := fin4_KTwo_le_torusSubgroup hx
  rw [fin4TorusSubgroup_eq_base] at hxT
  exact fin4BaseTorusSubgroup_mem_symbol_of_mem_KTwo hxT hx

theorem fin4_KTwo_eq_steinbergSymbolSubgroup :
    KTwo F (Fin 4) = steinbergSymbolSubgroup F (Fin 4) :=
  le_antisymm fin4_KTwo_le_steinbergSymbolSubgroup steinbergSymbolSubgroup_le_KTwo

end GaloisForLFunctions.HTGeometry
