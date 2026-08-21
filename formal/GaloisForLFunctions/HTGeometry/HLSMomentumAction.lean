import GaloisForLFunctions.HTGeometry.HLSOddWeights
import Mathlib.Data.Matrix.Basis

/-!
# The supercharges commute with translations

This module proves the second half of the Haag--Łopuszański--Sohnius classification for the
even--odd bracket: every translation generator acts as zero on the odd part,

  `[P_μ, Q] = 0`.

The proof is the graded Jacobi argument of Haag--Łopuszański--Sohnius, run in the
weight language of `HLSOddWeights`:

* by weights, `[P_{0 α̇}, Q_1] = 0` and `[P_{1 α̇}, Q̄_1̇] = 0`;
* `[P, P] = 0` then forces `[P_{01̇}, [P_{10̇}, Q_1]] = 0`, i.e. `U² = 0` for the antilinear
  map `U = ★ ∘ [P_{10̇}, ·]` on the highest-weight sector;
* the graded Jacobi identity applied to `{Q, Q★}` (a translation, hence commuting with `P`)
  forces `{U Q, Q} = 0`;
* combining the two with positivity gives `{U Q, (U Q)★} = 0`, hence `U Q = 0`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {B : Type*} [LieRing B] [LieAlgebra ℂ B]

/-- Components of the `adL`-eigenvalue equation on `𝔤₀`. -/
theorem hlsEven_adL_components {c : ℂ} {X : HLSEven B} (h : hlsEvenAdL B X = c • X) :
    hlsSl2Br hlsSl2H X.1 = c • X.1 ∧ (0 : HLSSl2) = c • X.2.1 ∧
      hlsSl2Mat hlsSl2H * X.2.2.1 = c • X.2.2.1 ∧ (0 : B) = c • X.2.2.2 := by
  rw [hlsEvenAdL_apply] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using congrArg Prod.fst h
  · simpa using congrArg Prod.fst (congrArg Prod.snd h)
  · simpa using congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
  · simpa using congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h))

/-- An even element whose undotted weight avoids `{0, 2, -2}` is a pure translation. -/
theorem hlsEven_eq_mom_of_adL_eigen {c : ℂ} {X : HLSEven B} (h : hlsEvenAdL B X = c • X)
    (h0 : c ≠ 0) (h2 : c ≠ 2) (hm2 : c ≠ -2) : X = hlsMom X.2.2.1 := by
  obtain ⟨hc1, hc2, -, hc4⟩ := hlsEven_adL_components h
  have hX2 : X.2.1 = 0 := by
    rcases smul_eq_zero.mp hc2.symm with h' | h'
    · exact absurd h' h0
    · exact h'
  have hX4 : X.2.2.2 = 0 := by
    rcases smul_eq_zero.mp hc4.symm with h' | h'
    · exact absurd h' h0
    · exact h'
  have hX1 : X.1 = 0 := by
    have e0 := congr_fun hc1 0
    have e1 := congr_fun hc1 1
    have e2 := congr_fun hc1 2
    simp only [hlsSl2Br, hlsSl2H, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.smul_apply, smul_eq_mul] at e0 e1 e2
    funext i
    fin_cases i
    · show X.1 0 = 0
      have : (2 - c) * X.1 0 = 0 := by linear_combination e0
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd (by linear_combination -h' : c = 2) h2
      · exact h'
    · show X.1 1 = 0
      have : (-2 - c) * X.1 1 = 0 := by linear_combination e1
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd (by linear_combination -h' : c = -2) hm2
      · exact h'
    · show X.1 2 = 0
      have : c * X.1 2 = 0 := by linear_combination -e2
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' h0
      · exact h'
  refine Prod.ext hX1 (Prod.ext hX2 (Prod.ext rfl hX4))

/-- Matrix unit `E_{α β̇}` of the translation sector. -/
def hlsMomUnit (α β : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single α β 1

theorem hlsMomUnit_conjTranspose (α β : Fin 2) : (hlsMomUnit α β)ᴴ = hlsMomUnit β α := by
  ext i j
  simp [hlsMomUnit, Matrix.single, Matrix.conjTranspose_apply, Matrix.of_apply]
  aesop


/-- Undotted weight of the translation matrix unit `E_{α β̇}`. -/
def hlsSign : Fin 2 → ℂ := ![1, -1]

@[simp] theorem hlsSign_zero : hlsSign 0 = 1 := rfl
@[simp] theorem hlsSign_one : hlsSign 1 = -1 := rfl

theorem hlsMomUnit_row (α β : Fin 2) :
    hlsSl2Mat hlsSl2H * hlsMomUnit α β = hlsSign α • hlsMomUnit α β := by
  ext i j
  fin_cases α <;> fin_cases β <;> fin_cases i <;> fin_cases j <;>
    simp [hlsMomUnit, hlsSl2Mat_H, Matrix.single, Matrix.mul_apply, Matrix.of_apply, hlsSign]

theorem hlsMomUnit_col (α β : Fin 2) :
    hlsMomUnit α β * (hlsSl2Mat hlsSl2H)ᵀ = hlsSign β • hlsMomUnit α β := by
  ext i j
  fin_cases α <;> fin_cases β <;> fin_cases i <;> fin_cases j <;>
    simp [hlsMomUnit, hlsSl2Mat_H, Matrix.single, Matrix.mul_apply, Matrix.of_apply, hlsSign]

theorem hlsEvenAdL_momUnit (α β : Fin 2) :
    hlsEvenAdL B (hlsMom (hlsMomUnit α β)) = hlsSign α • hlsMom (B := B) (hlsMomUnit α β) := by
  have h : hlsEvenAdL B (hlsMom (hlsMomUnit α β)) = hlsMom (hlsSl2Mat hlsSl2H * hlsMomUnit α β) :=
    hlsEvenBr_lorL_mom _ _
  rw [h, hlsMomUnit_row]
  simp [hlsMom, Prod.smul_mk]

theorem hlsEvenAdR_momUnit (α β : Fin 2) :
    hlsEvenAdR B (hlsMom (hlsMomUnit α β)) = hlsSign β • hlsMom (B := B) (hlsMomUnit α β) := by
  have h : hlsEvenAdR B (hlsMom (hlsMomUnit α β))
      = hlsMom (hlsMomUnit α β * (hlsSl2Mat hlsSl2H)ᵀ) := hlsEvenBr_lorR_mom _ _
  rw [h, hlsMomUnit_col]
  simp [hlsMom, Prod.smul_mk]

@[simp] theorem hlsMom_add (P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (hlsMom (P + Q) : HLSEven B) = hlsMom P + hlsMom Q := by
  simp [hlsMom]

@[simp] theorem hlsMom_smul (c : ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    (hlsMom (c • P) : HLSEven B) = c • hlsMom P := by
  simp [hlsMom, Prod.smul_mk]

/-- Bracketing a translation with the undotted lowering generator. -/
theorem hlsEvenBr_lorF_mom (P : Matrix (Fin 2) (Fin 2) ℂ) :
    hlsEvenBr (hlsLorL hlsSl2F) (hlsMom P : HLSEven B) = hlsMom (hlsSl2Mat hlsSl2F * P) :=
  hlsEvenBr_lorL_mom _ _

theorem hlsMomUnit_lorRF : (hlsMomUnit 1 0) * (hlsSl2Mat hlsSl2F)ᵀ = hlsMomUnit 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlsMomUnit, hlsSl2Mat, hlsSl2F, Matrix.single, Matrix.mul_apply, Matrix.of_apply]

/-- Every translation is a combination of the four matrix units. -/
theorem hlsMom_eq_sum_units (P : Matrix (Fin 2) (Fin 2) ℂ) :
    (hlsMom P : HLSEven B) = ∑ i : Fin 2, ∑ j : Fin 2, (P i j) • hlsMom (hlsMomUnit i j) := by
  have hP : P = ∑ i : Fin 2, ∑ j : Fin 2, (P i j) • hlsMomUnit i j := by
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [hlsMomUnit, Matrix.single_apply, Fin.sum_univ_two, Matrix.sum_apply]
  calc (hlsMom P : HLSEven B)
      = hlsMom (∑ i : Fin 2, ∑ j : Fin 2, (P i j) • hlsMomUnit i j) := by rw [← hP]
    _ = ∑ i : Fin 2, ∑ j : Fin 2, (P i j) • hlsMom (hlsMomUnit i j) := by
        simp only [Fin.sum_univ_two, hlsMom_add, hlsMom_smul]

namespace HLSGradedSymmetry

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (S : HLSGradedSymmetry B V)

/-- If every matrix unit annihilates `v`, so does every translation. -/
theorem act_mom_of_units {v : V} (h : ∀ α β : Fin 2, S.act (hlsMom (hlsMomUnit α β)) v = 0)
    (P : Matrix (Fin 2) (Fin 2) ℂ) : S.act (hlsMom P) v = 0 := by
  rw [hlsMom_eq_sum_units P]
  simp only [Fin.sum_univ_two, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    h, smul_zero, add_zero]

theorem mem_wt_of_eigen {a b : ℂ} {v : V} (ha : S.hL v = a • v) (hb : S.hR v = b • v) :
    v ∈ S.wt a b := by
  rw [mem_wt]
  refine ⟨⟨1, ?_⟩, ⟨1, ?_⟩⟩ <;> simp [ha, hb]

/-- The action of an even weight vector shifts weights additively. -/
theorem act_eigen {c₁ c₂ a b : ℂ} {X : HLSEven B} {v : V}
    (hX1 : hlsEvenAdL B X = c₁ • X) (hX2 : hlsEvenAdR B X = c₂ • X)
    (ha : S.hL v = a • v) (hb : S.hR v = b • v) :
    S.hL (S.act X v) = (c₁ + a) • S.act X v ∧ S.hR (S.act X v) = (c₂ + b) • S.act X v := by
  constructor
  · rw [S.hL_act X v, hX1, ha, map_smul, LinearMap.smul_apply, map_smul, add_smul]
  · rw [S.hR_act X v, hX2, hb, map_smul, LinearMap.smul_apply, map_smul, add_smul]

/-- If the shifted weight carries no odd generator, the translation acts as zero. -/
theorem act_momUnit_eq_zero {a b : ℂ} {v : V} (ha : S.hL v = a • v) (hb : S.hR v = b • v)
    (α β : Fin 2) (h : S.wt (hlsSign α + a) (hlsSign β + b) = ⊥) :
    S.act (hlsMom (hlsMomUnit α β)) v = 0 := by
  obtain ⟨h1, h2⟩ := S.act_eigen (hlsEvenAdL_momUnit α β) (hlsEvenAdR_momUnit α β) ha hb
  have := S.mem_wt_of_eigen h1 h2
  rw [h, Submodule.mem_bot] at this
  exact this


theorem br_adL_eigen {a a' : ℂ} {u v : V} (hu : S.hL u = a • u) (hv : S.hL v = a' • v) :
    hlsEvenAdL B (S.br u v) = (a + a') • S.br u v := by
  rw [S.adL_br u v, hu, hv, map_smul, LinearMap.smul_apply, map_smul, add_smul]

theorem oddConj_hL_eigen {a : ℂ} {v : V} (h : S.hR v = a • v) :
    S.hL (S.oddConj v) = (starRingEnd ℂ a) • S.oddConj v := by
  rw [← S.oddConj_hR v, h, map_smulₛₗ]

theorem oddConj_hR_eigen {a : ℂ} {v : V} (h : S.hL v = a • v) :
    S.hR (S.oddConj v) = (starRingEnd ℂ a) • S.oddConj v := by
  rw [← S.oddConj_hL v, h, map_smulₛₗ]

section MomentumVanishing

/-- Translations with a raised undotted index annihilate the undotted highest-weight sector. -/
theorem act_momUnit_zero_zero_pos {v : V} (hv : v ∈ S.wt 1 0) :
    S.act (hlsMom (hlsMomUnit 0 0)) v = 0 := by
  refine S.act_momUnit_eq_zero (a := 1) (b := 0) ?_ ?_ 0 0 ?_
  · rw [S.hL_eq_on_wt_pos hv, one_smul]
  · rw [S.hR_zero_on_wt_pos hv, zero_smul]
  · refine S.wt_eq_bot ?_
    simp only [hlsSign_zero]
    norm_num

theorem act_momUnit_zero_one_pos {v : V} (hv : v ∈ S.wt 1 0) :
    S.act (hlsMom (hlsMomUnit 0 1)) v = 0 := by
  refine S.act_momUnit_eq_zero (a := 1) (b := 0) ?_ ?_ 0 1 ?_
  · rw [S.hL_eq_on_wt_pos hv, one_smul]
  · rw [S.hR_zero_on_wt_pos hv, zero_smul]
  · refine S.wt_eq_bot ?_
    simp only [hlsSign_zero, hlsSign_one]
    norm_num

/-- Translations with a lowered undotted index annihilate the dotted highest-weight sector. -/
theorem act_momUnit_one_zero_dotPos {v : V} (hv : v ∈ S.wt 0 1) :
    S.act (hlsMom (hlsMomUnit 1 0)) v = 0 := by
  refine S.act_momUnit_eq_zero (a := 0) (b := 1) ?_ ?_ 1 0 ?_
  · rw [S.hL_zero_on_wt_dotPos hv, zero_smul]
  · rw [S.hR_eq_on_wt_pos hv, one_smul]
  · refine S.wt_eq_bot ?_
    simp only [hlsSign_zero, hlsSign_one]
    norm_num

theorem act_momUnit_zero_zero_dotPos {v : V} (hv : v ∈ S.wt 0 1) :
    S.act (hlsMom (hlsMomUnit 0 0)) v = 0 := by
  refine S.act_momUnit_eq_zero (a := 0) (b := 1) ?_ ?_ 0 0 ?_
  · rw [S.hL_zero_on_wt_dotPos hv, zero_smul]
  · rw [S.hR_eq_on_wt_pos hv, one_smul]
  · refine S.wt_eq_bot ?_
    simp only [hlsSign_zero]
    norm_num

/-- The image of the undotted highest-weight sector under `[P_{1 0̇}, ·]`. -/
theorem act_momUnit_one_zero_mem {v : V} (hv : v ∈ S.wt 1 0) :
    S.act (hlsMom (hlsMomUnit 1 0)) v ∈ S.wt 0 1 := by
  have h1 : S.hL v = (1 : ℂ) • v := by rw [S.hL_eq_on_wt_pos hv, one_smul]
  have h2 : S.hR v = (0 : ℂ) • v := by rw [S.hR_zero_on_wt_pos hv, zero_smul]
  obtain ⟨e1, e2⟩ := S.act_eigen (hlsEvenAdL_momUnit 1 0) (hlsEvenAdR_momUnit 1 0) h1 h2
  refine S.mem_wt_of_eigen ?_ ?_
  · rw [e1]; norm_num
  · rw [e2]; norm_num

/-- `{Q, Q★}` is a pure translation. -/
theorem br_oddConj_is_mom {v : V} (hv : v ∈ S.wt 1 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℂ, S.br v (S.oddConj v) = hlsMom P := by
  have h1 : S.hL v = (1 : ℂ) • v := by rw [S.hL_eq_on_wt_pos hv, one_smul]
  have h2 : S.hL (S.oddConj v) = (0 : ℂ) • S.oddConj v := by
    rw [S.oddConj_hL_eigen (a := 0) (by rw [S.hR_zero_on_wt_pos hv, zero_smul])]
    simp
  have := S.br_adL_eigen h1 h2
  rw [show (1 : ℂ) + 0 = 1 by norm_num] at this
  exact ⟨_, hlsEven_eq_mom_of_adL_eigen this one_ne_zero (by norm_num) (by norm_num)⟩

/-- **Translations act trivially on the undotted highest-weight sector.**
The key Haag--Łopuszański--Sohnius step: `[P_{1 0̇}, Q_1] = 0`. -/
theorem act_momUnit_one_zero_pos {v : V} (hv : v ∈ S.wt 1 0) :
    S.act (hlsMom (hlsMomUnit 1 0)) v = 0 := by
  set T : V := S.act (hlsMom (hlsMomUnit 1 0)) v with hT
  set U : V := S.oddConj T with hU
  -- `T` lies in the dotted highest-weight sector.
  have hTmem : T ∈ S.wt 0 1 := S.act_momUnit_one_zero_mem hv
  -- `[P, P] = 0` forces `[P_{01̇}, T] = 0`.
  have hA01T : S.act (hlsMom (hlsMomUnit 0 1)) T = 0 := by
    have hcomm := S.act_lie (hlsMom (hlsMomUnit 0 1)) (hlsMom (hlsMomUnit 1 0)) v
    rw [hlsEvenBr_mom_mom, map_zero] at hcomm
    have hz : (0 : V →ₗ[ℂ] V) v = 0 := rfl
    rw [hz] at hcomm
    have h0 : S.act (hlsMom (hlsMomUnit 0 1)) v = 0 := S.act_momUnit_zero_one_pos hv
    rw [h0, map_zero] at hcomm
    have := sub_eq_zero.mp hcomm.symm
    rw [this]
  -- hence `T ∘ U = 0`.
  have hTU : S.act (hlsMom (hlsMomUnit 1 0)) U = 0 := by
    have h := S.oddConj_act (hlsMom (hlsMomUnit 0 1)) T
    rw [hA01T, map_zero, hlsEvenConj_mom, hlsMomUnit_conjTranspose] at h
    exact h.symm
  -- the graded Jacobi identity for `{Q, Q★}` gives `{U, Q} = 0`.
  have hstar : S.br U v = 0 := by
    obtain ⟨P, hP⟩ := S.br_oddConj_is_mom hv
    have h := S.act_br (hlsMom (hlsMomUnit 1 0)) v (S.oddConj v)
    rw [hP, hlsEvenBr_mom_mom] at h
    have hzero : S.act (hlsMom (hlsMomUnit 1 0)) (S.oddConj v) = 0 :=
      S.act_momUnit_one_zero_dotPos (S.oddConj_mem_wt_pos hv)
    rw [hzero, map_zero, add_zero] at h
    have hconj := S.oddConj_br T (S.oddConj v)
    rw [S.oddConj_conj v] at hconj
    rw [← h] at hconj
    have hz0 : hlsEvenConj S.internal (0 : HLSEven B) = 0 := by
      simpa using hlsEvenConj_smul S.internal 0 (0 : HLSEven B)
    rw [hz0] at hconj
    exact hconj
  -- combining, `{T, T★} = 0`, so `T = 0` by positivity.
  have hfinal : S.br T U = 0 := by
    have h := S.act_br (hlsMom (hlsMomUnit 1 0)) v U
    have hvU : S.br v U = 0 := by rw [S.br_symm]; exact hstar
    rw [hvU, hlsEvenBr_zero_right, hTU, map_zero] at h
    have : S.br T U + 0 = 0 := h.symm
    simpa using this
  by_contra hne
  exact S.br_oddConj_ne_zero hne hfinal


theorem act_momUnit_one_one_pos {v : V} (hv : v ∈ S.wt 1 0) :
    S.act (hlsMom (hlsMomUnit 1 1)) v = 0 := by
  have hfR : S.act (hlsLorR hlsSl2F) v = 0 :=
    S.fR_zero_of_bot hv (S.wt_eq_bot (by norm_num))
  have hbr : hlsEvenBr (hlsLorR hlsSl2F) (hlsMom (hlsMomUnit 1 0) : HLSEven B)
      = hlsMom (hlsMomUnit 1 1) := by
    rw [hlsEvenBr_lorR_mom, hlsMomUnit_lorRF]
  have h := S.act_lie (hlsLorR hlsSl2F) (hlsMom (hlsMomUnit 1 0)) v
  rw [hbr, S.act_momUnit_one_zero_pos hv, map_zero, hfR, map_zero, sub_zero] at h
  exact h

/-- All translations annihilate the undotted highest-weight sector. -/
theorem act_mom_pos {v : V} (hv : v ∈ S.wt 1 0) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    S.act (hlsMom P) v = 0 := by
  refine S.act_mom_of_units ?_ P
  intro α β
  fin_cases α <;> fin_cases β
  · exact S.act_momUnit_zero_zero_pos hv
  · exact S.act_momUnit_zero_one_pos hv
  · exact S.act_momUnit_one_zero_pos hv
  · exact S.act_momUnit_one_one_pos hv

/-- All translations annihilate the Lorentz-scalar sector. -/
theorem act_mom_scalar {v : V} (hv : v ∈ S.wt 0 0) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    S.act (hlsMom P) v = 0 := by
  have h1 : S.hL v = (0 : ℂ) • v := by rw [S.hL_zero_on_wt_scalar hv, zero_smul]
  have h2 : S.hR v = (0 : ℂ) • v := by rw [S.hR_zero_on_wt_scalar hv, zero_smul]
  refine S.act_mom_of_units ?_ P
  intro α β
  refine S.act_momUnit_eq_zero h1 h2 α β ?_
  refine S.wt_eq_bot ?_
  fin_cases α <;> fin_cases β <;> simp only [hlsSign] <;> norm_num

/-- Translations annihilate the undotted lowest-weight sector. -/
theorem act_mom_neg {v : V} (hv : v ∈ S.wt (-1) 0) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    S.act (hlsMom P) v = 0 := by
  have hu : S.eL v ∈ S.wt 1 0 := S.eL_mem_wt_neg hv
  have hfe : S.fL (S.eL v) = v := S.fL_eL_id_neg hv
  have h := S.act_lie (hlsLorL hlsSl2F) (hlsMom P) (S.eL v)
  rw [hlsEvenBr_lorF_mom, S.act_mom_pos hu (hlsSl2Mat hlsSl2F * P), S.act_mom_pos hu P,
    map_zero] at h
  have hfe' : S.act (hlsLorL hlsSl2F) (S.eL v) = v := hfe
  rw [hfe'] at h
  have h' : (0 : V) = 0 - S.act (hlsMom P) v := h
  simpa using h'.symm

/-- Translations annihilate the dotted sectors, by conjugation. -/
theorem act_mom_dotPos {v : V} (hv : v ∈ S.wt 0 1) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    S.act (hlsMom P) v = 0 := by
  have hy : S.oddConj v ∈ S.wt 1 0 := S.oddConj_mem_wt_dotPos hv
  have h := S.oddConj_act (hlsMom Pᴴ) (S.oddConj v)
  rw [S.act_mom_pos hy Pᴴ, map_zero, hlsEvenConj_mom, Matrix.conjTranspose_conjTranspose,
    S.oddConj_conj v] at h
  exact h.symm

theorem act_mom_dotNeg {v : V} (hv : v ∈ S.wt 0 (-1)) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    S.act (hlsMom P) v = 0 := by
  have hy : S.oddConj v ∈ S.wt (-1) 0 := S.oddConj_mem_wt_dotNeg hv
  have h := S.oddConj_act (hlsMom Pᴴ) (S.oddConj v)
  rw [S.act_mom_neg hy Pᴴ, map_zero, hlsEvenConj_mom, Matrix.conjTranspose_conjTranspose,
    S.oddConj_conj v] at h
  exact h.symm

/-- **`[P_μ, Q] = 0`.**  Translations act as zero on the entire odd part. -/
theorem act_mom_eq_zero [FiniteDimensional ℂ V] (P : Matrix (Fin 2) (Fin 2) ℂ) :
    S.act (hlsMom P) = 0 := by
  ext w
  have hker : ∀ x : V, x ∈ S.wt 0 0 ⊔ (S.wt 1 0 ⊔ (S.wt (-1) 0 ⊔ (S.wt 0 1 ⊔ S.wt 0 (-1)))) →
      S.act (hlsMom P) x = 0 := by
    have h5 : S.wt 0 (-1) ≤ LinearMap.ker (S.act (hlsMom P)) := fun x hx =>
      S.act_mom_dotNeg hx P
    have h4 : S.wt 0 1 ≤ LinearMap.ker (S.act (hlsMom P)) := fun x hx => S.act_mom_dotPos hx P
    have h3 : S.wt (-1) 0 ≤ LinearMap.ker (S.act (hlsMom P)) := fun x hx => S.act_mom_neg hx P
    have h2 : S.wt 1 0 ≤ LinearMap.ker (S.act (hlsMom P)) := fun x hx => S.act_mom_pos hx P
    have h1 : S.wt 0 0 ≤ LinearMap.ker (S.act (hlsMom P)) := fun x hx => S.act_mom_scalar hx P
    intro x hx
    exact sup_le h1 (sup_le h2 (sup_le h3 (sup_le h4 h5))) hx
  have : w ∈ S.wt 0 0 ⊔ (S.wt 1 0 ⊔ (S.wt (-1) 0 ⊔ (S.wt 0 1 ⊔ S.wt 0 (-1)))) := by
    rw [S.wt_sectors_eq_top]
    trivial
  simpa using hker w this


end MomentumVanishing


end HLSGradedSymmetry

end GaloisForLFunctions.HTGeometry

