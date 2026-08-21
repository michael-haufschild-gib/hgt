import GaloisForLFunctions.HTGeometry.HLSSuperchargeBasis

/-!
# The Haag--Łopuszański--Sohnius theorem

The capstone: every `ℤ₂`-graded symmetry of a Coleman--Mandula even algebra with a real form
and a positive odd sector is the super-Poincaré algebra with central charges.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {B : Type*} [LieRing B] [LieAlgebra ℂ B]

/-- The invariant `ε` tensor on undotted spinor indices. -/
def hlsEps : Fin 2 → Fin 2 → ℂ := ![![0, 1], ![-1, 0]]

@[simp] theorem hlsEps_00 : hlsEps 0 0 = 0 := rfl
@[simp] theorem hlsEps_01 : hlsEps 0 1 = 1 := rfl
@[simp] theorem hlsEps_10 : hlsEps 1 0 = -1 := rfl
@[simp] theorem hlsEps_11 : hlsEps 1 1 = 0 := rfl

theorem hlsF_mul_momUnit_zero_zero :
    (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * hlsMomUnit 0 0 = hlsMomUnit 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlsMomUnit, Matrix.single_apply, Matrix.mul_apply]

theorem hlsMomUnit_zero_zero_mul_Ft :
    hlsMomUnit 0 0 * (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = hlsMomUnit 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlsMomUnit, Matrix.single_apply, Matrix.mul_apply]

theorem hlsMomUnit_one_zero_mul_Ft :
    hlsMomUnit 1 0 * (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = hlsMomUnit 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlsMomUnit, Matrix.single_apply, Matrix.mul_apply]


@[simp] theorem hlsInt_add (b c : B) : (hlsInt (b + c) : HLSEven B) = hlsInt b + hlsInt c := by
  simp [hlsInt]

@[simp] theorem hlsInt_neg (b : B) : (hlsInt (-b) : HLSEven B) = -hlsInt b := by
  simp [hlsInt]

@[simp] theorem hlsInt_smul (c : ℂ) (b : B) : (hlsInt (c • b) : HLSEven B) = c • hlsInt b := by
  simp [hlsInt, Prod.smul_mk]


namespace HLSGradedSymmetry

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (S : HLSGradedSymmetry B V)
variable [FiniteDimensional ℂ V]

theorem fL_zero_on_wt_dotPos {v : V} (hv : v ∈ S.wt 0 1) :
    S.act (hlsLorL hlsSl2F) v = 0 :=
  S.fL_zero_of_bot hv (S.wt_eq_bot (by norm_num))

theorem fR_zero_on_wt_pos {v : V} (hv : v ∈ S.wt 1 0) :
    S.act (hlsLorR hlsSl2F) v = 0 :=
  S.fR_zero_of_bot hv (S.wt_eq_bot (by norm_num))

theorem fL_zero_on_wt_neg {v : V} (hv : v ∈ S.wt (-1) 0) :
    S.act (hlsLorL hlsSl2F) v = 0 :=
  S.fL_zero_of_bot hv (S.wt_eq_bot (by norm_num))

theorem fR_zero_on_wt_neg {v : V} (hv : v ∈ S.wt (-1) 0) :
    S.act (hlsLorR hlsSl2F) v = 0 :=
  S.fR_zero_of_bot hv (S.wt_eq_bot (by norm_num))

theorem fR_zero_on_wt_dotNeg {v : V} (hv : v ∈ S.wt 0 (-1)) :
    S.act (hlsLorR hlsSl2F) v = 0 :=
  S.fR_zero_of_bot hv (S.wt_eq_bot (by norm_num))

theorem fL_zero_on_wt_dotNeg {v : V} (hv : v ∈ S.wt 0 (-1)) :
    S.act (hlsLorL hlsSl2F) v = 0 :=
  S.fL_zero_of_bot hv (S.wt_eq_bot (by norm_num))

/-- Lowering the undotted index of a mixed bracket. -/
theorem br_lower_left {u w : V} (hw : w ∈ S.wt 0 1) (c : ℂ)
    (h : S.br u w = hlsMom (c • hlsMomUnit 0 0)) :
    S.br (S.fL u) w = hlsMom (c • hlsMomUnit 1 0) := by
  have hj := S.act_br (hlsLorL hlsSl2F) u w
  rw [h, hlsEvenBr_lorL_mom, hlsSl2Mat_F, Matrix.mul_smul, hlsF_mul_momUnit_zero_zero,
    S.fL_zero_on_wt_dotPos hw, map_zero, add_zero] at hj
  exact hj.symm

/-- Lowering the dotted index of a mixed bracket. -/
theorem br_lower_right {u w : V} (hu : u ∈ S.wt 1 0) (c : ℂ)
    (h : S.br u w = hlsMom (c • hlsMomUnit 0 0)) :
    S.br u (S.fR w) = hlsMom (c • hlsMomUnit 0 1) := by
  have hj := S.act_br (hlsLorR hlsSl2F) u w
  rw [h, hlsEvenBr_lorR_mom, hlsSl2Mat_F, Matrix.smul_mul, hlsMomUnit_zero_zero_mul_Ft,
    S.fR_zero_on_wt_pos hu, map_zero, LinearMap.zero_apply, zero_add] at hj
  exact hj.symm

theorem br_lower_right' {u w : V} (hu : u ∈ S.wt (-1) 0) (c : ℂ)
    (h : S.br u w = hlsMom (c • hlsMomUnit 1 0)) :
    S.br u (S.fR w) = hlsMom (c • hlsMomUnit 1 1) := by
  have hj := S.act_br (hlsLorR hlsSl2F) u w
  rw [h, hlsEvenBr_lorR_mom, hlsSl2Mat_F, Matrix.smul_mul, hlsMomUnit_one_zero_mul_Ft,
    S.fR_zero_on_wt_neg hu, map_zero, LinearMap.zero_apply, zero_add] at hj
  exact hj.symm


theorem map_fL_wt_pos : Submodule.map S.fL (S.wt 1 0) = S.wt (-1) 0 := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact S.fL_mem_wt_pos hy
  · intro v hv
    exact ⟨S.eL v, S.eL_mem_wt_neg hv, S.fL_eL_id_neg hv⟩

theorem map_oddConj_wt_pos : Submodule.map S.oddConj (S.wt 1 0) = S.wt 0 1 := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact S.oddConj_mem_wt_pos hy
  · intro v hv
    exact ⟨S.oddConj v, S.oddConj_mem_wt_dotPos hv, S.oddConj_conj v⟩

theorem map_oddConj_wt_neg : Submodule.map S.oddConj (S.wt (-1) 0) = S.wt 0 (-1) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact S.oddConj_mem_wt_neg hy
  · intro v hv
    exact ⟨S.oddConj v, S.oddConj_mem_wt_dotNeg hv, S.oddConj_conj v⟩


/-- **The Haag--Łopuszański--Sohnius theorem.**

Every `ℤ₂`-graded symmetry algebra whose even part is a Coleman--Mandula algebra
(Lorentz `⊕` translations `⊕` internal), whose odd part is finite-dimensional, which carries a
real form, and whose odd sector is positive in a state of strictly timelike momentum, is the
super-Poincaré algebra with central charges:

there are `N` Weyl supercharges `Q^I_α` (`α = 1, 2`), with conjugates `Q̄^I_α̇`, such that

* `{Q^I_α, Q̄^J_β̇} = 2 δ^{IJ} P_{α β̇}`,
* `{Q^I_α, Q^J_β} = ε_{αβ} Z^{IJ}` with `Z^{IJ} = -Z^{JI}` internal and central,
* `[P_μ, Q^I_α] = 0`,

and the odd part is spanned by the supercharges together with the Lorentz-scalar sector. -/
theorem haag_lopuszanski_sohnius :
    ∃ (N : ℕ) (Q : Fin N → Fin 2 → V) (Z : Fin N → Fin N → B),
      (∀ I, Q I 0 ∈ S.wt 1 0) ∧
      (∀ I, Q I 1 ∈ S.wt (-1) 0) ∧
      (∀ I J α β, S.br (Q I α) (S.oddConj (Q J β))
          = hlsMom ((if I = J then (2 : ℂ) else 0) • hlsMomUnit α β)) ∧
      (∀ I J α β, S.br (Q I α) (Q J β) = hlsEps α β • hlsInt (Z I J)) ∧
      (∀ I J, Z I J = -Z J I) ∧
      (∀ I J, S.act (hlsInt (Z I J)) = 0) ∧
      (∀ P : Matrix (Fin 2) (Fin 2) ℂ, S.act (hlsMom P) = 0) ∧
      (S.wt 0 0 ⊔ (Submodule.span ℂ (Set.range fun p : Fin N × Fin 2 => Q p.1 p.2)
          ⊔ Submodule.span ℂ (Set.range fun p : Fin N × Fin 2 => S.oddConj (Q p.1 p.2))) = ⊤) := by
  classical
  obtain ⟨N, Q₀, hmem, hbr, hspan⟩ := S.exists_supercharge_basis
  set Qf : Fin N → Fin 2 → V := fun I => ![Q₀ I, S.fL (Q₀ I)] with hQf
  have hQ0 : ∀ I, Qf I 0 = Q₀ I := fun I => rfl
  have hQ1 : ∀ I, Qf I 1 = S.fL (Q₀ I) := fun I => rfl
  have hmem0 : ∀ I, Qf I 0 ∈ S.wt 1 0 := fun I => hmem I
  have hmem1 : ∀ I, Qf I 1 ∈ S.wt (-1) 0 := fun I => S.fL_mem_wt_pos (hmem I)
  -- the central charges
  have hZex : ∀ I J : Fin N, ∃ z : B, S.br (Qf I 0) (Qf J 1) = hlsInt z := fun I J =>
    S.br_pos_neg_is_int (hmem0 I) (hmem1 J)
  choose Z hZ using hZex
  -- (ii) the mixed brackets
  have h00 : ∀ I J, S.br (Qf I 0) (S.oddConj (Qf J 0))
      = hlsMom ((if I = J then (2 : ℂ) else 0) • hlsMomUnit 0 0) := fun I J => hbr I J
  have h10 : ∀ I J, S.br (Qf I 1) (S.oddConj (Qf J 0))
      = hlsMom ((if I = J then (2 : ℂ) else 0) • hlsMomUnit 1 0) := fun I J =>
    S.br_lower_left (S.oddConj_mem_wt_pos (hmem J)) _ (h00 I J)
  have hconjfL : ∀ I, S.oddConj (Qf I 1) = S.fR (S.oddConj (Qf I 0)) := fun I =>
    (S.oddConj_fL (Q₀ I))
  have h01 : ∀ I J, S.br (Qf I 0) (S.oddConj (Qf J 1))
      = hlsMom ((if I = J then (2 : ℂ) else 0) • hlsMomUnit 0 1) := by
    intro I J
    rw [hconjfL J]
    exact S.br_lower_right (hmem0 I) _ (h00 I J)
  have h11 : ∀ I J, S.br (Qf I 1) (S.oddConj (Qf J 1))
      = hlsMom ((if I = J then (2 : ℂ) else 0) • hlsMomUnit 1 1) := by
    intro I J
    rw [hconjfL J]
    exact S.br_lower_right' (hmem1 I) _ (h10 I J)
  -- (iii) the same-chirality brackets
  have hanti : ∀ I J, Z I J = -Z J I := by
    intro I J
    have h := S.br_central_antisymm (hmem I) (hmem J)
    rw [show S.br (Q₀ I) (S.fL (Q₀ J)) = hlsInt (Z I J) from hZ I J,
      show S.br (Q₀ J) (S.fL (Q₀ I)) = hlsInt (Z J I) from hZ J I, ← hlsInt_add] at h
    have := (hlsInt_eq_zero_iff (B := B) (Z I J + Z J I)).mp h
    linear_combination (norm := abel) this
  have hbb : ∀ I J α β, S.br (Qf I α) (Qf J β) = hlsEps α β • hlsInt (Z I J) := by
    intro I J α β
    fin_cases α <;> fin_cases β
    · show S.br (Qf I 0) (Qf J 0) = hlsEps 0 0 • hlsInt (Z I J)
      rw [S.br_pos_pos_eq_zero (hmem0 I) (hmem0 J), hlsEps_00, zero_smul]
    · show S.br (Qf I 0) (Qf J 1) = hlsEps 0 1 • hlsInt (Z I J)
      rw [hZ I J, hlsEps_01, one_smul]
    · show S.br (Qf I 1) (Qf J 0) = hlsEps 1 0 • hlsInt (Z I J)
      rw [S.br_symm, hZ J I, hlsEps_10, hanti J I, hlsInt_neg, neg_one_smul]
    · show S.br (Qf I 1) (Qf J 1) = hlsEps 1 1 • hlsInt (Z I J)
      rw [S.br_neg_neg_eq_zero (hmem1 I) (hmem1 J), hlsEps_11, zero_smul]
  -- (v) centrality
  have hcentral : ∀ I J, S.act (hlsInt (Z I J)) = 0 := by
    intro I J
    have := S.act_br_pos_neg_eq_zero (hmem0 I) (hmem1 J)
    rwa [hZ I J] at this
  refine ⟨N, Qf, Z, hmem0, hmem1, ?_, hbb, hanti, hcentral, S.act_mom_eq_zero, ?_⟩
  · intro I J α β
    fin_cases α <;> fin_cases β
    · exact h00 I J
    · exact h01 I J
    · exact h10 I J
    · exact h11 I J
  · -- (vii) spanning
    have hrangeU : (Set.range fun p : Fin N × Fin 2 => Qf p.1 p.2)
        = Set.range Q₀ ∪ Set.range (fun I => S.fL (Q₀ I)) := by
      ext x
      constructor
      · rintro ⟨⟨I, α⟩, rfl⟩
        fin_cases α
        · exact Or.inl ⟨I, rfl⟩
        · exact Or.inr ⟨I, rfl⟩
      · rintro (⟨I, rfl⟩ | ⟨I, rfl⟩)
        · exact ⟨(I, 0), rfl⟩
        · exact ⟨(I, 1), rfl⟩
    have hrangeD : (Set.range fun p : Fin N × Fin 2 => S.oddConj (Qf p.1 p.2))
        = Set.range (fun I => S.oddConj (Q₀ I)) ∪
          Set.range (fun I => S.oddConj (S.fL (Q₀ I))) := by
      ext x
      constructor
      · rintro ⟨⟨I, α⟩, rfl⟩
        fin_cases α
        · exact Or.inl ⟨I, rfl⟩
        · exact Or.inr ⟨I, rfl⟩
      · rintro (⟨I, rfl⟩ | ⟨I, rfl⟩)
        · exact ⟨(I, 0), rfl⟩
        · exact ⟨(I, 1), rfl⟩
    have hfL : Submodule.span ℂ (Set.range fun I => S.fL (Q₀ I)) = S.wt (-1) 0 := by
      have himg : (Set.range fun I => S.fL (Q₀ I)) = (S.fL : V → V) '' Set.range Q₀ := by
        rw [← Set.range_comp]; rfl
      rw [himg, ← Submodule.map_span, hspan, S.map_fL_wt_pos]
    have hcU : Submodule.span ℂ (Set.range fun I => S.oddConj (Q₀ I)) = S.wt 0 1 := by
      have himg : (Set.range fun I => S.oddConj (Q₀ I))
          = (S.oddConj : V → V) '' Set.range Q₀ := by
        rw [← Set.range_comp]; rfl
      rw [himg, ← Submodule.map_span, hspan, S.map_oddConj_wt_pos]
    have hcD : Submodule.span ℂ (Set.range fun I => S.oddConj (S.fL (Q₀ I))) = S.wt 0 (-1) := by
      have himg : (Set.range fun I => S.oddConj (S.fL (Q₀ I)))
          = (S.oddConj : V → V) '' Set.range (fun I => S.fL (Q₀ I)) := by
        rw [← Set.range_comp]; rfl
      rw [himg, ← Submodule.map_span, hfL, S.map_oddConj_wt_neg]
    rw [hrangeU, hrangeD, Submodule.span_union, Submodule.span_union, hspan, hfL, hcU, hcD]
    have := S.wt_sectors_eq_top
    rw [← this]
    ac_rfl

/-- **The supercharges are linearly independent**, so `N` counts them. -/
theorem supercharge_linearIndependent {N : ℕ} {Q : Fin N → V}
    (hbr : ∀ I J, S.br (Q I) (S.oddConj (Q J))
        = hlsMom ((if I = J then (2 : ℂ) else 0) • hlsMomUnit 0 0)) :
    LinearIndependent ℂ Q := by
  classical
  let φ : HLSEven B →ₗ[ℂ] ℂ :=
    { toFun := fun X => X.2.2.1 0 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [linearIndependent_iff']
  intro s c hsum J hJ
  have h0 : (∑ i ∈ s, S.br (c i • Q i) (S.oddConj (Q J))) = 0 := by
    have h := congrArg (fun u : V => S.br u (S.oddConj (Q J))) hsum
    simpa [map_sum, LinearMap.sum_apply] using h
  have hterm : ∀ i : Fin N, S.br (c i • Q i) (S.oddConj (Q J))
      = hlsMom ((c i * (if i = J then (2 : ℂ) else 0)) • hlsMomUnit 0 0) := by
    intro i
    rw [map_smul, LinearMap.smul_apply, hbr i J, ← hlsMom_smul, smul_smul]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)] at h0
  have h1 := congrArg φ h0
  rw [map_sum, map_zero] at h1
  have hval : ∀ i : Fin N, φ (hlsMom ((c i * (if i = J then (2 : ℂ) else 0)) • hlsMomUnit 0 0))
      = c i * (if i = J then (2 : ℂ) else 0) := by
    intro i
    show ((c i * (if i = J then (2 : ℂ) else 0)) • hlsMomUnit 0 0) 0 0
      = c i * (if i = J then (2 : ℂ) else 0)
    simp [hlsMomUnit, Matrix.single_apply]
  rw [Finset.sum_congr rfl (fun i _ => hval i)] at h1
  simp only [mul_ite, mul_zero] at h1
  rw [Finset.sum_ite_eq' s J (fun i => c i * 2), if_pos hJ] at h1
  exact by
    have : c J * 2 = 0 := h1
    simpa using this


end HLSGradedSymmetry


end GaloisForLFunctions.HTGeometry
