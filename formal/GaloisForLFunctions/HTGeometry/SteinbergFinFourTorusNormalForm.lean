import GaloisForLFunctions.HTGeometry.SteinbergFinFourTorusKernel
import GaloisForLFunctions.HTGeometry.SteinbergGroupFiniteGeneration
import GaloisForLFunctions.HTGeometry.SteinbergTorusIndexTransport

/-!
# Rank-four torus normal form modulo Steinberg symbols

Milnor's Theorem 9.11 ends by collecting torus factors at a base index. Quotienting by the central
symbol subgroup makes the three base families commuting homomorphisms.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

theorem fin4_steinbergSymbolSubgroup_le_center :
    steinbergSymbolSubgroup F (Fin 4) ≤ Subgroup.center (SteinbergGroup F (Fin 4)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨i, j, hij, u, v, rfl⟩
  obtain ⟨k, hki, hkj⟩ := exists_third_index (by decide) i j
  exact steinbergSymbol_mem_center hij u v hki hkj

theorem fin4_steinbergSymbolSubgroup_normal :
    (steinbergSymbolSubgroup F (Fin 4)).Normal := by
  constructor
  intro x hx g
  have hcenter := fin4_steinbergSymbolSubgroup_le_center hx
  have hcomm := Subgroup.mem_center_iff.1 hcenter g
  convert hx using 1
  rw [hcomm]
  group

local instance : (steinbergSymbolSubgroup F (Fin 4)).Normal :=
  fin4_steinbergSymbolSubgroup_normal

abbrev fin4SymbolQuotient :=
  SteinbergGroup F (Fin 4) ⧸ steinbergSymbolSubgroup F (Fin 4)

def fin4SymbolQuotientMk (x : SteinbergGroup F (Fin 4)) : fin4SymbolQuotient (F := F) :=
  QuotientGroup.mk x

theorem fin4SymbolQuotientMk_torus_mul {i j : Fin 4} (hij : i ≠ j) (u v : Fˣ) :
    fin4SymbolQuotientMk (steinbergTorus hij (u * v))
      = fin4SymbolQuotientMk (steinbergTorus hij u)
        * fin4SymbolQuotientMk (steinbergTorus hij v) := by
  have qtorRev (a b : Fˣ) :
      fin4SymbolQuotientMk (steinbergTorus hij (a * b))
        = fin4SymbolQuotientMk (steinbergTorus hij b)
          * fin4SymbolQuotientMk (steinbergTorus hij a) := by
    rw [steinbergTorus_mul hij a b]
    change QuotientGroup.mk (_ * _ * _) = QuotientGroup.mk _ * QuotientGroup.mk _
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    rw [show QuotientGroup.mk (steinbergSymbol hij a b) = 1 by
      exact (QuotientGroup.eq_one_iff _).mpr (steinbergSymbol_mem_symbolSubgroup hij a b)]
    simp
  calc fin4SymbolQuotientMk (steinbergTorus hij (u * v))
      = fin4SymbolQuotientMk (steinbergTorus hij (v * u)) := by rw [mul_comm]
    _ = fin4SymbolQuotientMk (steinbergTorus hij u)
        * fin4SymbolQuotientMk (steinbergTorus hij v) := qtorRev v u

theorem fin4SymbolQuotientMk_base_comm {i j : Fin 4} (h0i : (0 : Fin 4) ≠ i)
    (h0j : (0 : Fin 4) ≠ j) (hij : i ≠ j) (u v : Fˣ) :
    fin4SymbolQuotientMk (steinbergTorus h0i u) * fin4SymbolQuotientMk (steinbergTorus h0j v)
      = fin4SymbolQuotientMk (steinbergTorus h0j v)
        * fin4SymbolQuotientMk (steinbergTorus h0i u) := by
  apply (QuotientGroup.eq_iff_div_mem).mpr
  change steinbergTorus h0i u * steinbergTorus h0j v
      / (steinbergTorus h0j v * steinbergTorus h0i u)
        ∈ steinbergSymbolSubgroup F (Fin 4)
  convert torusCommutator_mem_symbolSubgroup h0i h0j hij u v using 1
  unfold torusCommutator
  rw [div_eq_mul_inv, mul_inv_rev]
  group

theorem fin4SymbolQuotientMk_spine_mul (u₁ u₂ u₃ v₁ v₂ v₃ : Fˣ) :
    fin4SymbolQuotientMk (fin4TorusSpine u₁ u₂ u₃)
      * fin4SymbolQuotientMk (fin4TorusSpine v₁ v₂ v₃)
      = fin4SymbolQuotientMk (fin4TorusSpine (u₁ * v₁) (u₂ * v₂) (u₃ * v₃)) := by
  let h01 : (0 : Fin 4) ≠ 1 := by decide
  let h02 : (0 : Fin 4) ≠ 2 := by decide
  let h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have c21 := fin4SymbolQuotientMk_base_comm h02 h01 (Ne.symm h12) u₂ v₁
  have c31 := fin4SymbolQuotientMk_base_comm h03 h01 (Ne.symm h13) u₃ v₁
  have c32 := fin4SymbolQuotientMk_base_comm h03 h02 (Ne.symm h23) u₃ v₂
  let A₁ := fin4SymbolQuotientMk (steinbergTorus h01 u₁)
  let A₂ := fin4SymbolQuotientMk (steinbergTorus h02 u₂)
  let A₃ := fin4SymbolQuotientMk (steinbergTorus h03 u₃)
  let B₁ := fin4SymbolQuotientMk (steinbergTorus h01 v₁)
  let B₂ := fin4SymbolQuotientMk (steinbergTorus h02 v₂)
  let B₃ := fin4SymbolQuotientMk (steinbergTorus h03 v₃)
  change A₂ * B₁ = B₁ * A₂ at c21
  change A₃ * B₁ = B₁ * A₃ at c31
  change A₃ * B₂ = B₂ * A₃ at c32
  have hspine :
      fin4SymbolQuotientMk (fin4TorusSpine (u₁ * v₁) (u₂ * v₂) (u₃ * v₃))
        = A₁ * B₁ * (A₂ * B₂) * (A₃ * B₃) := by
    change fin4SymbolQuotientMk
      (steinbergTorus h01 (u₁ * v₁) * steinbergTorus h02 (u₂ * v₂)
        * steinbergTorus h03 (u₃ * v₃)) = _
    change QuotientGroup.mk
      (steinbergTorus h01 (u₁ * v₁) * steinbergTorus h02 (u₂ * v₂)
        * steinbergTorus h03 (u₃ * v₃)) = _
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    change fin4SymbolQuotientMk (steinbergTorus h01 (u₁ * v₁))
      * fin4SymbolQuotientMk (steinbergTorus h02 (u₂ * v₂))
      * fin4SymbolQuotientMk (steinbergTorus h03 (u₃ * v₃)) = _
    rw [fin4SymbolQuotientMk_torus_mul h01 u₁ v₁,
      fin4SymbolQuotientMk_torus_mul h02 u₂ v₂,
      fin4SymbolQuotientMk_torus_mul h03 u₃ v₃]
  change (A₁ * A₂ * A₃) * (B₁ * B₂ * B₃) = _
  calc (A₁ * A₂ * A₃) * (B₁ * B₂ * B₃)
      = A₁ * A₂ * (A₃ * B₁) * B₂ * B₃ := by group
    _ = A₁ * A₂ * (B₁ * A₃) * B₂ * B₃ := by rw [c31]
    _ = A₁ * (A₂ * B₁) * A₃ * B₂ * B₃ := by group
    _ = A₁ * (B₁ * A₂) * A₃ * B₂ * B₃ := by rw [c21]
    _ = A₁ * B₁ * A₂ * (A₃ * B₂) * B₃ := by group
    _ = A₁ * B₁ * A₂ * (B₂ * A₃) * B₃ := by rw [c32]
    _ = A₁ * B₁ * (A₂ * B₂) * (A₃ * B₃) := by group
    _ = fin4SymbolQuotientMk
        (fin4TorusSpine (u₁ * v₁) (u₂ * v₂) (u₃ * v₃)) := hspine.symm

theorem fin4SymbolQuotientMk_spine_one :
    fin4SymbolQuotientMk (fin4TorusSpine (1 : Fˣ) 1 1) = 1 := by
  rw [fin4TorusSpine, steinbergTorus_one, steinbergTorus_one, steinbergTorus_one]
  rfl

theorem fin4SymbolQuotientMk_spine_inv (u₁ u₂ u₃ : Fˣ) :
    fin4SymbolQuotientMk (fin4TorusSpine u₁⁻¹ u₂⁻¹ u₃⁻¹)
      = (fin4SymbolQuotientMk (fin4TorusSpine u₁ u₂ u₃))⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  calc fin4SymbolQuotientMk (fin4TorusSpine u₁ u₂ u₃)
      * fin4SymbolQuotientMk (fin4TorusSpine u₁⁻¹ u₂⁻¹ u₃⁻¹)
      = fin4SymbolQuotientMk
          (fin4TorusSpine (u₁ * u₁⁻¹) (u₂ * u₂⁻¹) (u₃ * u₃⁻¹)) :=
          fin4SymbolQuotientMk_spine_mul u₁ u₂ u₃ u₁⁻¹ u₂⁻¹ u₃⁻¹
    _ = 1 := by simpa using fin4SymbolQuotientMk_spine_one (F := F)

/-- The three base-index torus families used in Milnor's rank-four reduction. -/
def fin4BaseTorusSubgroup : Subgroup (SteinbergGroup F (Fin 4)) :=
  Subgroup.closure {x | ∃ u : Fˣ,
    x = steinbergTorus (by decide : (0 : Fin 4) ≠ 1) u
      ∨ x = steinbergTorus (by decide : (0 : Fin 4) ≠ 2) u
      ∨ x = steinbergTorus (by decide : (0 : Fin 4) ≠ 3) u}

/-- The subgroup generated by all oriented torus factors in rank four. -/
def fin4TorusSubgroup : Subgroup (SteinbergGroup F (Fin 4)) :=
  Subgroup.closure {x | ∃ (i j : Fin 4) (hij : i ≠ j) (u : Fˣ),
    x = steinbergTorus hij u}

theorem fin4BaseTorusSubgroup_le_torus :
    fin4BaseTorusSubgroup (F := F) ≤ fin4TorusSubgroup (F := F) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨u, rfl | rfl | rfl⟩
  · exact Subgroup.subset_closure ⟨0, 1, by decide, u, rfl⟩
  · exact Subgroup.subset_closure ⟨0, 2, by decide, u, rfl⟩
  · exact Subgroup.subset_closure ⟨0, 3, by decide, u, rfl⟩

theorem fin4BaseTorus_mem {j : Fin 4} (h0j : (0 : Fin 4) ≠ j) (u : Fˣ) :
    steinbergTorus h0j u ∈ fin4BaseTorusSubgroup (F := F) := by
  fin_cases j
  · exact (h0j rfl).elim
  · have hh : h0j = (by decide : (0 : Fin 4) ≠ 1) := Subsingleton.elim _ _
    subst h0j
    exact Subgroup.subset_closure ⟨u, Or.inl rfl⟩
  · have hh : h0j = (by decide : (0 : Fin 4) ≠ 2) := Subsingleton.elim _ _
    subst h0j
    exact Subgroup.subset_closure ⟨u, Or.inr (Or.inl rfl)⟩
  · have hh : h0j = (by decide : (0 : Fin 4) ≠ 3) := Subsingleton.elim _ _
    subst h0j
    exact Subgroup.subset_closure ⟨u, Or.inr (Or.inr rfl)⟩

/-- Milnor 9.10 collapses every rank-four torus edge to the base-index torus subgroup. -/
theorem fin4TorusSubgroup_le_base :
    fin4TorusSubgroup (F := F) ≤ fin4BaseTorusSubgroup (F := F) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨i, j, hij, u, rfl⟩
  by_cases hi : i = 0
  · subst i
    exact fin4BaseTorus_mem hij u
  by_cases hj : j = 0
  · subst j
    obtain ⟨k, hki, hk0⟩ := exists_third_index (by decide) i 0
    have hrev := steinbergTorus_reverse_mul hki hij hk0 u
    have heq : steinbergTorus hij u = (steinbergTorus (Ne.symm hij) u)⁻¹ :=
      eq_inv_of_mul_eq_one_left hrev
    rw [heq]
    exact (fin4BaseTorusSubgroup (F := F)).inv_mem
      (fin4BaseTorus_mem (Ne.symm hij) u)
  · have h0i : (0 : Fin 4) ≠ i := Ne.symm hi
    have h0j : (0 : Fin 4) ≠ j := Ne.symm hj
    rw [steinbergTorus_triangle_exact h0i hij h0j u]
    exact (fin4BaseTorusSubgroup (F := F)).mul_mem
      (fin4BaseTorus_mem h0j u)
      ((fin4BaseTorusSubgroup (F := F)).inv_mem (fin4BaseTorus_mem h0i u))

theorem fin4TorusSubgroup_eq_base :
    fin4TorusSubgroup (F := F) = fin4BaseTorusSubgroup (F := F) :=
  le_antisymm fin4TorusSubgroup_le_base fin4BaseTorusSubgroup_le_torus

/-- A group element has a base-torus spine normal form modulo Steinberg symbols. -/
def fin4TorusSpineNormal (x : SteinbergGroup F (Fin 4)) : Prop :=
  ∃ u₁ u₂ u₃ : Fˣ, x * (fin4TorusSpine u₁ u₂ u₃)⁻¹
    ∈ steinbergSymbolSubgroup F (Fin 4)

theorem fin4BaseTorusSubgroup_normal {x : SteinbergGroup F (Fin 4)}
    (hx : x ∈ fin4BaseTorusSubgroup (F := F)) :
    fin4TorusSpineNormal x := by
  apply Subgroup.closure_induction (p := fun x _ => fin4TorusSpineNormal x)
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨u, rfl | rfl | rfl⟩
    · refine ⟨u, 1, 1, ?_⟩
      simp [fin4TorusSpine, steinbergTorus_one]
    · refine ⟨1, u, 1, ?_⟩
      simp [fin4TorusSpine, steinbergTorus_one]
    · refine ⟨1, 1, u, ?_⟩
      simp [fin4TorusSpine, steinbergTorus_one]
  · refine ⟨1, 1, 1, ?_⟩
    rw [fin4TorusSpine, steinbergTorus_one, steinbergTorus_one, steinbergTorus_one]
    exact Subgroup.one_mem _
  · rintro x y _ _ ⟨u₁, u₂, u₃, hx⟩ ⟨v₁, v₂, v₃, hy⟩
    refine ⟨u₁ * v₁, u₂ * v₂, u₃ * v₃, ?_⟩
    have hxq : fin4SymbolQuotientMk x = fin4SymbolQuotientMk (fin4TorusSpine u₁ u₂ u₃) := by
      apply (QuotientGroup.eq_iff_div_mem).mpr
      simpa [div_eq_mul_inv] using hx
    have hyq : fin4SymbolQuotientMk y = fin4SymbolQuotientMk (fin4TorusSpine v₁ v₂ v₃) := by
      apply (QuotientGroup.eq_iff_div_mem).mpr
      simpa [div_eq_mul_inv] using hy
    have hq : fin4SymbolQuotientMk (x * y)
        = fin4SymbolQuotientMk
          (fin4TorusSpine (u₁ * v₁) (u₂ * v₂) (u₃ * v₃)) := by
      change QuotientGroup.mk (x * y) = _
      rw [QuotientGroup.mk_mul]
      change fin4SymbolQuotientMk x * fin4SymbolQuotientMk y = _
      rw [hxq, hyq]
      exact fin4SymbolQuotientMk_spine_mul u₁ u₂ u₃ v₁ v₂ v₃
    exact (QuotientGroup.eq_iff_div_mem).mp hq
  · rintro x _ ⟨u₁, u₂, u₃, hx⟩
    refine ⟨u₁⁻¹, u₂⁻¹, u₃⁻¹, ?_⟩
    have hxq : fin4SymbolQuotientMk x = fin4SymbolQuotientMk (fin4TorusSpine u₁ u₂ u₃) := by
      apply (QuotientGroup.eq_iff_div_mem).mpr
      simpa [div_eq_mul_inv] using hx
    have hq : fin4SymbolQuotientMk x⁻¹
        = fin4SymbolQuotientMk (fin4TorusSpine u₁⁻¹ u₂⁻¹ u₃⁻¹) := by
      change QuotientGroup.mk x⁻¹ = _
      rw [QuotientGroup.mk_inv (steinbergSymbolSubgroup F (Fin 4)) x]
      change (fin4SymbolQuotientMk x)⁻¹ = _
      rw [hxq, fin4SymbolQuotientMk_spine_inv]
    exact (QuotientGroup.eq_iff_div_mem).mp hq

theorem fin4BaseTorusSubgroup_mem_symbol_of_mem_KTwo {x : SteinbergGroup F (Fin 4)}
    (hx : x ∈ fin4BaseTorusSubgroup (F := F)) (hK : x ∈ KTwo F (Fin 4)) :
    x ∈ steinbergSymbolSubgroup F (Fin 4) := by
  obtain ⟨u₁, u₂, u₃, hnormal⟩ := fin4BaseTorusSubgroup_normal hx
  have hnormalK : x * (fin4TorusSpine u₁ u₂ u₃)⁻¹ ∈ KTwo F (Fin 4) :=
    steinbergSymbolSubgroup_le_KTwo hnormal
  have hspineK : fin4TorusSpine u₁ u₂ u₃ ∈ KTwo F (Fin 4) := by
    have hproduct := (KTwo F (Fin 4)).mul_mem
      ((KTwo F (Fin 4)).inv_mem hnormalK) hK
    convert hproduct using 1
    group
  have hspineS : fin4TorusSpine u₁ u₂ u₃ ∈ steinbergSymbolSubgroup F (Fin 4) :=
    fin4TorusSpine_mem_symbolSubgroup_of_mem_KTwo u₁ u₂ u₃ hspineK
  rw [show x = (x * (fin4TorusSpine u₁ u₂ u₃)⁻¹) * fin4TorusSpine u₁ u₂ u₃ by group]
  exact (steinbergSymbolSubgroup F (Fin 4)).mul_mem hnormal hspineS

end GaloisForLFunctions.HTGeometry
