import GaloisForLFunctions.HTGeometry.HLSMomentumAction

/-!
# Normal form of the odd--odd bracket

With `[P, Q] = 0` in hand (`HLSMomentumAction`), the graded Jacobi identity pins down the
whole odd--odd bracket of an `HLSGradedSymmetry`:

* `{Q_α, Q_β}` has no Lorentz component: the same-chirality bracket lands in the internal
  algebra, `{Q^I_α, Q^J_β} = ε_{αβ} Z^{IJ}`;
* `Z` is antisymmetric and commutes with the whole superalgebra except possibly with the
  internal algebra, where it spans an abelian ideal;
* `{Q_α, Q̄_β̇}` is a translation.

Only the even weight spaces of `𝔤₀` and the graded Jacobi identity are used.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {B : Type*} [LieRing B] [LieAlgebra ℂ B]

/-- Components of the `adR`-eigenvalue equation on `𝔤₀`. -/
theorem hlsEven_adR_components {c : ℂ} {X : HLSEven B} (h : hlsEvenAdR B X = c • X) :
    (0 : HLSSl2) = c • X.1 ∧ hlsSl2Br hlsSl2H X.2.1 = c • X.2.1 ∧
      X.2.2.1 * (hlsSl2Mat hlsSl2H)ᵀ = c • X.2.2.1 ∧ (0 : B) = c • X.2.2.2 := by
  rw [hlsEvenAdR_apply] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using congrArg Prod.fst h
  · simpa using congrArg Prod.fst (congrArg Prod.snd h)
  · simpa using congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
  · simpa using congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h))

/-- The joint weight-`(2, 0)` space of `𝔤₀` is the line spanned by the undotted raising
generator. -/
theorem hlsEven_eq_lorL_E {X : HLSEven B} (h1 : hlsEvenAdL B X = (2 : ℂ) • X) :
    ∃ c : ℂ, X = hlsLorL (c • hlsSl2E) := by
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hlsEven_adL_components h1
  have hX2 : X.2.1 = 0 := by
    rcases smul_eq_zero.mp hc2.symm with h' | h'
    · exact absurd h' two_ne_zero
    · exact h'
  have hX4 : X.2.2.2 = 0 := by
    rcases smul_eq_zero.mp hc4.symm with h' | h'
    · exact absurd h' two_ne_zero
    · exact h'
  have hX3 : X.2.2.1 = 0 := by
    have hmat : (hlsSl2Mat hlsSl2H - (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        * X.2.2.1 = 0 := by
      rw [sub_mul, Matrix.smul_mul, Matrix.one_mul, hc3, sub_eq_zero]
    have hdet : IsUnit (Matrix.det (hlsSl2Mat hlsSl2H
        - (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
      have he : hlsSl2Mat hlsSl2H - (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
          = !![(-1 : ℂ), 0; 0, -3] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hlsSl2Mat_H] <;> norm_num
      rw [he, Matrix.det_fin_two_of]
      exact (isUnit_iff_ne_zero).mpr (by norm_num)
    calc X.2.2.1 = 1 * X.2.2.1 := (Matrix.one_mul _).symm
      _ = ((hlsSl2Mat hlsSl2H - (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹
            * (hlsSl2Mat hlsSl2H - (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) * X.2.2.1 := by
          rw [Matrix.nonsing_inv_mul _ hdet]
      _ = (hlsSl2Mat hlsSl2H - (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹
            * ((hlsSl2Mat hlsSl2H - (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * X.2.2.1) :=
          Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hmat, Matrix.mul_zero]
  refine ⟨X.1 0, ?_⟩
  refine Prod.ext ?_ (Prod.ext hX2 (Prod.ext hX3 hX4))
  have e1 := congr_fun hc1 1
  have e2 := congr_fun hc1 2
  simp only [hlsSl2Br, hlsSl2H, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Pi.smul_apply, smul_eq_mul] at e1 e2
  have h1' : X.1 1 = 0 := by linear_combination -e1 / 4
  have h2' : X.1 2 = 0 := by linear_combination -e2 / 2
  funext i
  fin_cases i
  · show X.1 0 = _
    simp [hlsLorL, hlsSl2E]
  · show X.1 1 = _
    rw [h1']
    simp [hlsLorL, hlsSl2E]
  · show X.1 2 = _
    rw [h2']
    simp [hlsLorL, hlsSl2E]

/-- The joint weight-`(0, 0)` space of `𝔤₀` is the Cartan plus the internal algebra. -/
theorem hlsEven_zero_zero {X : HLSEven B} (h1 : hlsEvenAdL B X = 0) (h2 : hlsEvenAdR B X = 0) :
    ∃ (c₁ c₂ : ℂ) (b : B),
      X = hlsLorL (c₁ • hlsSl2H) + hlsLorR (c₂ • hlsSl2H) + hlsInt b := by
  have h1' : hlsEvenAdL B X = (0 : ℂ) • X := by rw [h1, zero_smul]
  have h2' : hlsEvenAdR B X = (0 : ℂ) • X := by rw [h2, zero_smul]
  obtain ⟨ha1, -, ha3, -⟩ := hlsEven_adL_components h1'
  obtain ⟨-, hb2, -, -⟩ := hlsEven_adR_components h2'
  have hX3 : X.2.2.1 = 0 := by
    have hmat : hlsSl2Mat hlsSl2H * X.2.2.1 = 0 := by rw [ha3, zero_smul]
    have hdet : IsUnit (Matrix.det (hlsSl2Mat hlsSl2H)) := by
      rw [hlsSl2Mat_H, Matrix.det_fin_two_of]
      exact (isUnit_iff_ne_zero).mpr (by norm_num)
    calc X.2.2.1 = 1 * X.2.2.1 := (Matrix.one_mul _).symm
      _ = ((hlsSl2Mat hlsSl2H)⁻¹ * hlsSl2Mat hlsSl2H) * X.2.2.1 := by
          rw [Matrix.nonsing_inv_mul _ hdet]
      _ = (hlsSl2Mat hlsSl2H)⁻¹ * (hlsSl2Mat hlsSl2H * X.2.2.1) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hmat, Matrix.mul_zero]
  have key : ∀ x : HLSSl2, hlsSl2Br hlsSl2H x = 0 → x = x 2 • hlsSl2H := by
    intro x hx
    have e0 := congr_fun hx 0
    have e1 := congr_fun hx 1
    simp only [hlsSl2Br, hlsSl2H, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply] at e0 e1
    have h0' : x 0 = 0 := by linear_combination e0 / 2
    have h1'' : x 1 = 0 := by linear_combination -e1 / 2
    funext i
    fin_cases i
    · show x 0 = _
      rw [h0']; simp [hlsSl2H]
    · show x 1 = _
      rw [h1'']; simp [hlsSl2H]
    · show x 2 = _
      simp [hlsSl2H]
  have hA : X.1 = X.1 2 • hlsSl2H := key _ (by rw [ha1, zero_smul])
  have hB : X.2.1 = X.2.1 2 • hlsSl2H := key _ (by rw [hb2, zero_smul])
  refine ⟨X.1 2, X.2.1 2, X.2.2.2, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · show X.1 = _
    simpa [hlsLorL, hlsLorR, hlsInt] using hA
  · show X.2.1 = _
    simpa [hlsLorL, hlsLorR, hlsInt] using hB
  · show X.2.2.1 = _
    simpa [hlsLorL, hlsLorR, hlsInt] using hX3
  · show X.2.2.2 = _
    simp [hlsLorL, hlsLorR, hlsInt]


theorem hlsSl2Mat_E : hlsSl2Mat hlsSl2E = !![0, 1; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hlsSl2Mat, hlsSl2E]

theorem hlsSl2Mat_F : hlsSl2Mat hlsSl2F = !![0, 0; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hlsSl2Mat, hlsSl2F]

theorem hlsE_mul_momUnit_one_zero :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * hlsMomUnit 1 0 = hlsMomUnit 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlsMomUnit, Matrix.single_apply, Matrix.mul_apply]

theorem hlsF_mul_momUnit_zero_one :
    (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * hlsMomUnit 0 1 = hlsMomUnit 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlsMomUnit, Matrix.single_apply, Matrix.mul_apply]

theorem hlsMom_eq_zero_iff (P : Matrix (Fin 2) (Fin 2) ℂ) :
    (hlsMom P : HLSEven B) = 0 ↔ P = 0 := by
  constructor
  · intro h
    simpa [hlsMom] using congrArg (fun X : HLSEven B => X.2.2.1) h
  · intro h; rw [h]; simp [hlsMom]

theorem hlsMomUnit_ne_zero (α β : Fin 2) : hlsMomUnit α β ≠ 0 := by
  intro h
  have := congr_fun (congr_fun h α) β
  simp [hlsMomUnit] at this

/-- Bracket of a translation with an undotted Lorentz generator. -/
theorem hlsEvenBr_mom_lorL (P : Matrix (Fin 2) (Fin 2) ℂ) (x : HLSSl2) :
    hlsEvenBr (hlsMom P) (hlsLorL x : HLSEven B) = -hlsMom (hlsSl2Mat x * P) := by
  rw [hlsEvenBr_skew, hlsEvenBr_lorL_mom]

theorem hlsEvenBr_mom_lorR (P : Matrix (Fin 2) (Fin 2) ℂ) (x : HLSSl2) :
    hlsEvenBr (hlsMom P) (hlsLorR x : HLSEven B) = -hlsMom (P * (hlsSl2Mat x)ᵀ) := by
  rw [hlsEvenBr_skew, hlsEvenBr_lorR_mom]


/-- The joint weight-`(-2, 0)` space of `𝔤₀` is the line spanned by the undotted lowering
generator. -/
theorem hlsEven_eq_lorL_F {X : HLSEven B} (h1 : hlsEvenAdL B X = (-2 : ℂ) • X) :
    ∃ c : ℂ, X = hlsLorL (c • hlsSl2F) := by
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hlsEven_adL_components h1
  have hne : (-2 : ℂ) ≠ 0 := by norm_num
  have hX2 : X.2.1 = 0 := (smul_eq_zero.mp hc2.symm).resolve_left hne
  have hX4 : X.2.2.2 = 0 := (smul_eq_zero.mp hc4.symm).resolve_left hne
  have hX3 : X.2.2.1 = 0 := by
    have hmat : (hlsSl2Mat hlsSl2H - (-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        * X.2.2.1 = 0 := by
      rw [sub_mul, Matrix.smul_mul, Matrix.one_mul, hc3, sub_eq_zero]
    have hdet : IsUnit (Matrix.det (hlsSl2Mat hlsSl2H
        - (-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
      have he : hlsSl2Mat hlsSl2H - (-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
          = !![(3 : ℂ), 0; 0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hlsSl2Mat_H] <;> norm_num
      rw [he, Matrix.det_fin_two_of]
      exact (isUnit_iff_ne_zero).mpr (by norm_num)
    calc X.2.2.1 = 1 * X.2.2.1 := (Matrix.one_mul _).symm
      _ = ((hlsSl2Mat hlsSl2H - (-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹
            * (hlsSl2Mat hlsSl2H - (-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) * X.2.2.1 := by
          rw [Matrix.nonsing_inv_mul _ hdet]
      _ = (hlsSl2Mat hlsSl2H - (-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹
            * ((hlsSl2Mat hlsSl2H - (-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * X.2.2.1) :=
          Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hmat, Matrix.mul_zero]
  refine ⟨X.1 1, ?_⟩
  refine Prod.ext ?_ (Prod.ext hX2 (Prod.ext hX3 hX4))
  have e0 := congr_fun hc1 0
  have e2 := congr_fun hc1 2
  simp only [hlsSl2Br, hlsSl2H, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Pi.smul_apply, smul_eq_mul] at e0 e2
  have h0' : X.1 0 = 0 := by linear_combination e0 / 4
  have h2' : X.1 2 = 0 := by linear_combination e2 / 2
  funext i
  fin_cases i
  · show X.1 0 = _
    rw [h0']; simp [hlsLorL, hlsSl2F]
  · show X.1 1 = _
    simp [hlsLorL, hlsSl2F]
  · show X.1 2 = _
    rw [h2']; simp [hlsLorL, hlsSl2F]

/-- An even element whose weights are those of no generator of `𝔤₀` vanishes. -/
theorem hlsEven_eq_zero_of_weights {c₁ c₂ : ℂ} {X : HLSEven B}
    (h1 : hlsEvenAdL B X = c₁ • X) (h2 : hlsEvenAdR B X = c₂ • X)
    (h0 : c₁ ≠ 0) (ht : c₁ ≠ 2) (hmt : c₁ ≠ -2) (hu : c₂ ≠ 1) (hmu : c₂ ≠ -1) : X = 0 := by
  have hmom : X = hlsMom X.2.2.1 := hlsEven_eq_mom_of_adL_eigen h1 h0 ht hmt
  obtain ⟨-, -, hb3, -⟩ := hlsEven_adR_components h2
  have hmat : X.2.2.1 * ((hlsSl2Mat hlsSl2H)ᵀ - c₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hb3, sub_eq_zero]
  have hdet : IsUnit (Matrix.det ((hlsSl2Mat hlsSl2H)ᵀ
      - c₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    have he : (hlsSl2Mat hlsSl2H)ᵀ - c₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        = !![1 - c₂, 0; 0, -1 - c₂] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hlsSl2Mat_H]
    rw [he, Matrix.det_fin_two_of]
    refine (isUnit_iff_ne_zero).mpr ?_
    have h1' : (1 : ℂ) - c₂ ≠ 0 := fun hh => hu (by linear_combination -hh)
    have h2' : (-1 : ℂ) - c₂ ≠ 0 := fun hh => hmu (by linear_combination -hh)
    simpa using mul_ne_zero h1' h2'
  have hP : X.2.2.1 = 0 := by
    calc X.2.2.1 = X.2.2.1 * 1 := (Matrix.mul_one _).symm
      _ = X.2.2.1 * (((hlsSl2Mat hlsSl2H)ᵀ - c₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
            * ((hlsSl2Mat hlsSl2H)ᵀ - c₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet]
      _ = (X.2.2.1 * ((hlsSl2Mat hlsSl2H)ᵀ - c₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ)))
            * ((hlsSl2Mat hlsSl2H)ᵀ - c₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ :=
          (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [hmat, Matrix.zero_mul]
  rw [hmom, hP]
  simp [hlsMom]

theorem hlsEvenBr_int_mom (b : B) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    hlsEvenBr (hlsInt b) (hlsMom P : HLSEven B) = 0 := by
  rw [hlsEvenBr_skew, hlsEvenBr_mom_int, neg_zero]

/-- The joint weight-`(1, 1)` space of `𝔤₀` is the line spanned by `P_{1 1̇}`. -/
theorem hlsEven_weight_one_one {X : HLSEven B} (h1 : hlsEvenAdL B X = (1 : ℂ) • X)
    (h2 : hlsEvenAdR B X = (1 : ℂ) • X) :
    ∃ c : ℂ, X = hlsMom (c • hlsMomUnit 0 0) := by
  have hmom : X = hlsMom X.2.2.1 := hlsEven_eq_mom_of_adL_eigen h1 one_ne_zero
    (by norm_num) (by norm_num)
  obtain ⟨-, -, ha3, -⟩ := hlsEven_adL_components h1
  obtain ⟨-, -, hb3, -⟩ := hlsEven_adR_components h2
  refine ⟨X.2.2.1 0 0, ?_⟩
  rw [hmom]
  congr 1
  ext i j
  have hrow := congr_fun (congr_fun ha3 1) j
  have hcol := congr_fun (congr_fun hb3 i) 1
  simp only [hlsSl2Mat_H, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul] at hrow hcol
  have hr : X.2.2.1 1 j = 0 := by linear_combination -hrow / 2
  have hc : X.2.2.1 i 1 = 0 := by linear_combination -hcol / 2
  fin_cases i <;> fin_cases j <;>
    simp [hlsMomUnit, Matrix.single_apply, Matrix.smul_apply] <;>
    first
      | rfl
      | (exact hc)
      | (exact hr)

theorem hlsEvenBr_int_lorL (b : B) (x : HLSSl2) :
    hlsEvenBr (hlsInt b) (hlsLorL x : HLSEven B) = 0 := by
  rw [hlsEvenBr_skew, hlsEvenBr_lorL_int, neg_zero]

theorem hlsEvenAdL_int (b : B) : hlsEvenAdL B (hlsInt b) = 0 := hlsEvenBr_lorL_int _ _

theorem hlsEvenAdR_int (b : B) : hlsEvenAdR B (hlsInt b) = 0 := hlsEvenBr_lorR_int _ _

theorem hlsInt_eq_zero_iff (b : B) : (hlsInt b : HLSEven B) = 0 ↔ b = 0 := by
  constructor
  · intro h
    simpa [hlsInt] using congrArg (fun X : HLSEven B => X.2.2.2) h
  · intro h; rw [h]; simp [hlsInt]


namespace HLSGradedSymmetry

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (S : HLSGradedSymmetry B V)

theorem br_adR_eigen {a a' : ℂ} {u v : V} (hu : S.hR u = a • u) (hv : S.hR v = a' • v) :
    hlsEvenAdR B (S.br u v) = (a + a') • S.br u v := by
  rw [S.adR_br u v, hu, hv, map_smul, LinearMap.smul_apply, map_smul, add_smul]

variable [FiniteDimensional ℂ V]

theorem act_mom_apply_eq_zero (P : Matrix (Fin 2) (Fin 2) ℂ) (v : V) :
    S.act (hlsMom P) v = 0 := by
  rw [S.act_mom_eq_zero P]
  rfl

/-- **Same-chirality highest-weight brackets vanish**: `{Q^I_1, Q^J_1} = 0`. -/
theorem br_pos_pos_eq_zero {u v : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt 1 0) :
    S.br u v = 0 := by
  have h1 : S.hL u = (1 : ℂ) • u := by rw [S.hL_eq_on_wt_pos hu, one_smul]
  have h2 : S.hL v = (1 : ℂ) • v := by rw [S.hL_eq_on_wt_pos hv, one_smul]
  have hadL : hlsEvenAdL B (S.br u v) = (2 : ℂ) • S.br u v := by
    have h := S.br_adL_eigen h1 h2
    rwa [show (1 : ℂ) + 1 = 2 by norm_num] at h
  obtain ⟨c, hc⟩ := hlsEven_eq_lorL_E hadL
  have hjac := S.act_br (hlsMom (hlsMomUnit 1 0)) u v
  simp only [S.act_mom_apply_eq_zero, map_zero, LinearMap.zero_apply, add_zero] at hjac
  rw [hc] at hjac
  rw [hlsEvenBr_mom_lorL, hlsSl2Mat_smul, hlsSl2Mat_E, Matrix.smul_mul,
    hlsE_mul_momUnit_one_zero] at hjac
  have hzero : (hlsMom (c • hlsMomUnit 0 0) : HLSEven B) = 0 := by
    have := neg_eq_zero.mp hjac
    exact this
  have hc0 : c = 0 := by
    have hP := (hlsMom_eq_zero_iff (B := B) (c • hlsMomUnit 0 0)).mp hzero
    rcases smul_eq_zero.mp hP with h' | h'
    · exact h'
    · exact absurd h' (hlsMomUnit_ne_zero 0 0)
  rw [hc, hc0, zero_smul]
  simp [hlsLorL]

/-- **The mixed-chirality highest-weight bracket is internal**: `{Q^I_1, Q^J_2} = Z^{IJ}`. -/
theorem br_pos_neg_is_int {u v : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt (-1) 0) :
    ∃ z : B, S.br u v = hlsInt z := by
  have h1 : S.hL u = (1 : ℂ) • u := by rw [S.hL_eq_on_wt_pos hu, one_smul]
  have h2 : S.hL v = (-1 : ℂ) • v := by rw [S.hL_eq_on_wt_neg hv, neg_one_smul]
  have h3 : S.hR u = (0 : ℂ) • u := by rw [S.hR_zero_on_wt_pos hu, zero_smul]
  have h4 : S.hR v = (0 : ℂ) • v := by rw [S.hR_zero_on_wt_neg hv, zero_smul]
  have hadL : hlsEvenAdL B (S.br u v) = 0 := by
    have h := S.br_adL_eigen h1 h2
    rw [show (1 : ℂ) + -1 = 0 by norm_num, zero_smul] at h
    exact h
  have hadR : hlsEvenAdR B (S.br u v) = 0 := by
    have h := S.br_adR_eigen h3 h4
    rw [show (0 : ℂ) + 0 = 0 by norm_num, zero_smul] at h
    exact h
  obtain ⟨c₁, c₂, b, hb⟩ := hlsEven_zero_zero hadL hadR
  have hjac : ∀ P : Matrix (Fin 2) (Fin 2) ℂ,
      hlsEvenBr (hlsMom P) (S.br u v) = 0 := by
    intro P
    have h := S.act_br (hlsMom P) u v
    simp only [S.act_mom_apply_eq_zero, map_zero, LinearMap.zero_apply, add_zero] at h
    exact h
  have hkey : ∀ P : Matrix (Fin 2) (Fin 2) ℂ,
      c₁ • (hlsSl2Mat hlsSl2H * P) + c₂ • (P * (hlsSl2Mat hlsSl2H)ᵀ) = 0 := by
    intro P
    have h := hjac P
    rw [hb, hlsEvenBr_add_right, hlsEvenBr_add_right, hlsEvenBr_mom_lorL, hlsEvenBr_mom_lorR,
      hlsEvenBr_mom_int, hlsSl2Mat_smul, hlsSl2Mat_smul, Matrix.smul_mul,
      Matrix.transpose_smul, Matrix.mul_smul, add_zero,
      ← neg_add, ← hlsMom_add] at h
    have := neg_eq_zero.mp h
    exact (hlsMom_eq_zero_iff (B := B) _).mp this
  have e1 := hkey (hlsMomUnit 0 0)
  have e2 := hkey (hlsMomUnit 0 1)
  rw [hlsMomUnit_row, hlsMomUnit_col, hlsSign_zero, one_smul, ← add_smul] at e1
  rw [hlsMomUnit_row, hlsMomUnit_col, hlsSign_zero, hlsSign_one, one_smul, smul_smul] at e2
  have hsum : c₁ + c₂ = 0 := by
    rcases smul_eq_zero.mp e1 with h' | h'
    · exact h'
    · exact absurd h' (hlsMomUnit_ne_zero 0 0)
  have hdiff : c₁ + c₂ * (-1) = 0 := by
    rw [← add_smul] at e2
    rcases smul_eq_zero.mp e2 with h' | h'
    · exact h'
    · exact absurd h' (hlsMomUnit_ne_zero 0 1)
  have hc1 : c₁ = 0 := by linear_combination (hsum + hdiff) / 2
  have hc2 : c₂ = 0 := by linear_combination (hsum - hdiff) / 2
  refine ⟨b, ?_⟩
  rw [hb, hc1, hc2, zero_smul]
  simp [hlsLorL, hlsLorR, hlsInt]


/-- **Same-chirality lowest-weight brackets vanish**: `{Q^I_2, Q^J_2} = 0`. -/
theorem br_neg_neg_eq_zero {u v : V} (hu : u ∈ S.wt (-1) 0) (hv : v ∈ S.wt (-1) 0) :
    S.br u v = 0 := by
  have h1 : S.hL u = (-1 : ℂ) • u := by rw [S.hL_eq_on_wt_neg hu, neg_one_smul]
  have h2 : S.hL v = (-1 : ℂ) • v := by rw [S.hL_eq_on_wt_neg hv, neg_one_smul]
  have hadL : hlsEvenAdL B (S.br u v) = (-2 : ℂ) • S.br u v := by
    have h := S.br_adL_eigen h1 h2
    rwa [show (-1 : ℂ) + -1 = -2 by norm_num] at h
  obtain ⟨c, hc⟩ := hlsEven_eq_lorL_F hadL
  have hjac := S.act_br (hlsMom (hlsMomUnit 0 1)) u v
  simp only [S.act_mom_apply_eq_zero, map_zero, LinearMap.zero_apply, add_zero] at hjac
  rw [hc] at hjac
  rw [hlsEvenBr_mom_lorL, hlsSl2Mat_smul, hlsSl2Mat_F, Matrix.smul_mul,
    hlsF_mul_momUnit_zero_one] at hjac
  have hzero : (hlsMom (c • hlsMomUnit 1 1) : HLSEven B) = 0 := neg_eq_zero.mp hjac
  have hc0 : c = 0 := by
    have hP := (hlsMom_eq_zero_iff (B := B) (c • hlsMomUnit 1 1)).mp hzero
    exact (smul_eq_zero.mp hP).resolve_right (hlsMomUnit_ne_zero 1 1)
  rw [hc, hc0, zero_smul]
  simp [hlsLorL]

/-- The internal algebra preserves every joint weight space of the odd part. -/
theorem act_int_eigen {a b' : ℂ} {v : V} (b : B) (ha : S.hL v = a • v) (hb : S.hR v = b' • v) :
    S.hL (S.act (hlsInt b) v) = a • S.act (hlsInt b) v ∧
      S.hR (S.act (hlsInt b) v) = b' • S.act (hlsInt b) v := by
  have h1 : hlsEvenAdL B (hlsInt b) = (0 : ℂ) • hlsInt b := by
    rw [hlsEvenAdL_int, zero_smul]
  have h2 : hlsEvenAdR B (hlsInt b) = (0 : ℂ) • hlsInt b := by
    rw [hlsEvenAdR_int, zero_smul]
  obtain ⟨e1, e2⟩ := S.act_eigen h1 h2 ha hb
  rw [zero_add] at e1 e2
  exact ⟨e1, e2⟩

/-- Central charges annihilate the dotted highest-weight sector. -/
theorem act_br_pos_neg_dotPos {u v w : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt (-1) 0)
    (hw : w ∈ S.wt 0 1) : S.act (S.br u v) w = 0 := by
  have hu1 : S.hL u = (1 : ℂ) • u := by rw [S.hL_eq_on_wt_pos hu, one_smul]
  have hv1 : S.hL v = (-1 : ℂ) • v := by rw [S.hL_eq_on_wt_neg hv, neg_one_smul]
  have hw1 : S.hL w = (0 : ℂ) • w := by rw [S.hL_zero_on_wt_dotPos hw, zero_smul]
  have hvw : ∃ P, S.br v w = hlsMom P := by
    have h := S.br_adL_eigen hv1 hw1
    rw [show (-1 : ℂ) + 0 = -1 by norm_num] at h
    exact ⟨_, hlsEven_eq_mom_of_adL_eigen h (by norm_num) (by norm_num) (by norm_num)⟩
  have hwu : ∃ P, S.br w u = hlsMom P := by
    have h := S.br_adL_eigen hw1 hu1
    rw [show (0 : ℂ) + 1 = 1 by norm_num] at h
    exact ⟨_, hlsEven_eq_mom_of_adL_eigen h one_ne_zero (by norm_num) (by norm_num)⟩
  obtain ⟨P₁, h₁⟩ := hvw
  obtain ⟨P₂, h₂⟩ := hwu
  have hj := S.jacobi u v w
  rw [h₁, h₂, S.act_mom_apply_eq_zero, S.act_mom_apply_eq_zero, add_zero, add_zero] at hj
  exact hj

/-- Central charges annihilate the dotted lowest-weight sector. -/
theorem act_br_pos_neg_dotNeg {u v w : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt (-1) 0)
    (hw : w ∈ S.wt 0 (-1)) : S.act (S.br u v) w = 0 := by
  have hu1 : S.hL u = (1 : ℂ) • u := by rw [S.hL_eq_on_wt_pos hu, one_smul]
  have hv1 : S.hL v = (-1 : ℂ) • v := by rw [S.hL_eq_on_wt_neg hv, neg_one_smul]
  have hw1 : S.hL w = (0 : ℂ) • w := by rw [S.hL_zero_on_wt_dotNeg hw, zero_smul]
  obtain ⟨P₁, h₁⟩ : ∃ P, S.br v w = hlsMom P := by
    have h := S.br_adL_eigen hv1 hw1
    rw [show (-1 : ℂ) + 0 = -1 by norm_num] at h
    exact ⟨_, hlsEven_eq_mom_of_adL_eigen h (by norm_num) (by norm_num) (by norm_num)⟩
  obtain ⟨P₂, h₂⟩ : ∃ P, S.br w u = hlsMom P := by
    have h := S.br_adL_eigen hw1 hu1
    rw [show (0 : ℂ) + 1 = 1 by norm_num] at h
    exact ⟨_, hlsEven_eq_mom_of_adL_eigen h one_ne_zero (by norm_num) (by norm_num)⟩
  have hj := S.jacobi u v w
  rw [h₁, h₂, S.act_mom_apply_eq_zero, S.act_mom_apply_eq_zero, add_zero, add_zero] at hj
  exact hj

/-- Central charges annihilate the Lorentz-scalar sector. -/
theorem act_br_pos_neg_scalar {u v w : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt (-1) 0)
    (hw : w ∈ S.wt 0 0) : S.act (S.br u v) w = 0 := by
  have hu1 : S.hL u = (1 : ℂ) • u := by rw [S.hL_eq_on_wt_pos hu, one_smul]
  have hu2 : S.hR u = (0 : ℂ) • u := by rw [S.hR_zero_on_wt_pos hu, zero_smul]
  have hv1 : S.hL v = (-1 : ℂ) • v := by rw [S.hL_eq_on_wt_neg hv, neg_one_smul]
  have hv2 : S.hR v = (0 : ℂ) • v := by rw [S.hR_zero_on_wt_neg hv, zero_smul]
  have hw1 : S.hL w = (0 : ℂ) • w := by rw [S.hL_zero_on_wt_scalar hw, zero_smul]
  have hw2 : S.hR w = (0 : ℂ) • w := by rw [S.hR_zero_on_wt_scalar hw, zero_smul]
  have h₁ : S.br v w = 0 := by
    have ha := S.br_adL_eigen hv1 hw1
    have hb := S.br_adR_eigen hv2 hw2
    rw [show (-1 : ℂ) + 0 = -1 by norm_num] at ha
    rw [show (0 : ℂ) + 0 = 0 by norm_num] at hb
    exact hlsEven_eq_zero_of_weights ha hb (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have h₂ : S.br w u = 0 := by
    have ha := S.br_adL_eigen hw1 hu1
    have hb := S.br_adR_eigen hw2 hu2
    rw [show (0 : ℂ) + 1 = 1 by norm_num] at ha
    rw [show (0 : ℂ) + 0 = 0 by norm_num] at hb
    exact hlsEven_eq_zero_of_weights ha hb one_ne_zero (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hj := S.jacobi u v w
  rw [h₁, h₂, map_zero, LinearMap.zero_apply, LinearMap.zero_apply, add_zero, add_zero] at hj
  exact hj

/-- Central charges annihilate the undotted highest-weight sector. -/
theorem act_br_pos_neg_pos {u v w : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt (-1) 0)
    (hw : w ∈ S.wt 1 0) : S.act (S.br u v) w = 0 := by
  obtain ⟨z, hz⟩ := S.br_pos_neg_is_int hu hv
  set Y : V := S.act (hlsInt z) w with hY
  have hw1 : S.hL w = (1 : ℂ) • w := by rw [S.hL_eq_on_wt_pos hw, one_smul]
  have hw2 : S.hR w = (0 : ℂ) • w := by rw [S.hR_zero_on_wt_pos hw, zero_smul]
  obtain ⟨hY1, hY2⟩ := S.act_int_eigen z hw1 hw2
  have hYmem : Y ∈ S.wt 1 0 := S.mem_wt_of_eigen hY1 hY2
  have hcY : S.oddConj Y ∈ S.wt 0 1 := S.oddConj_mem_wt_pos hYmem
  have hkill : S.act (hlsInt z) (S.oddConj Y) = 0 := by
    have := S.act_br_pos_neg_dotPos hu hv hcY
    rwa [hz] at this
  have hmom : ∃ P, S.br w (S.oddConj Y) = hlsMom P := by
    have hcY1 : S.hL (S.oddConj Y) = (0 : ℂ) • S.oddConj Y := by
      rw [S.hL_zero_on_wt_dotPos hcY, zero_smul]
    have h := S.br_adL_eigen hw1 hcY1
    rw [show (1 : ℂ) + 0 = 1 by norm_num] at h
    exact ⟨_, hlsEven_eq_mom_of_adL_eigen h one_ne_zero (by norm_num) (by norm_num)⟩
  obtain ⟨P, hP⟩ := hmom
  have hstep := S.act_br (hlsInt z) w (S.oddConj Y)
  rw [hP, hlsEvenBr_int_mom, hkill, map_zero, add_zero] at hstep
  have hYzero : Y = 0 := by
    by_contra hne
    exact S.br_oddConj_ne_zero hne hstep.symm
  rw [hz]
  exact hYzero

/-- Central charges annihilate the undotted lowest-weight sector. -/
theorem act_br_pos_neg_neg {u v w : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt (-1) 0)
    (hw : w ∈ S.wt (-1) 0) : S.act (S.br u v) w = 0 := by
  obtain ⟨z, hz⟩ := S.br_pos_neg_is_int hu hv
  have hew : S.eL w ∈ S.wt 1 0 := S.eL_mem_wt_neg hw
  have hfe : S.fL (S.eL w) = w := S.fL_eL_id_neg hw
  have hcomm := S.act_lie (hlsInt z) (hlsLorL hlsSl2F) (S.eL w)
  rw [hlsEvenBr_int_lorL, map_zero, LinearMap.zero_apply] at hcomm
  have hkill : S.act (hlsInt z) (S.eL w) = 0 := by
    have := S.act_br_pos_neg_pos hu hv hew
    rwa [hz] at this
  have hfe' : S.act (hlsLorL hlsSl2F) (S.eL w) = w := hfe
  rw [hfe', hkill, map_zero, sub_zero] at hcomm
  rw [hz]
  exact hcomm.symm

/-- **The central charges are central**: they annihilate the entire odd part. -/
theorem act_br_pos_neg_eq_zero {u v : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt (-1) 0) :
    S.act (S.br u v) = 0 := by
  ext w
  have hle : S.wt 0 0 ⊔ (S.wt 1 0 ⊔ (S.wt (-1) 0 ⊔ (S.wt 0 1 ⊔ S.wt 0 (-1))))
      ≤ LinearMap.ker (S.act (S.br u v)) :=
    sup_le (fun x hx => S.act_br_pos_neg_scalar hu hv hx)
      (sup_le (fun x hx => S.act_br_pos_neg_pos hu hv hx)
        (sup_le (fun x hx => S.act_br_pos_neg_neg hu hv hx)
          (sup_le (fun x hx => S.act_br_pos_neg_dotPos hu hv hx)
            (fun x hx => S.act_br_pos_neg_dotNeg hu hv hx))))
  have hw : w ∈ S.wt 0 0 ⊔ (S.wt 1 0 ⊔ (S.wt (-1) 0 ⊔ (S.wt 0 1 ⊔ S.wt 0 (-1)))) := by
    rw [S.wt_sectors_eq_top]; trivial
  simpa using hle hw

/-- **Antisymmetry of the central charge**: `Z^{IJ} = -Z^{JI}`. -/
theorem br_central_antisymm {u v : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt 1 0) :
    S.br u (S.fL v) + S.br v (S.fL u) = 0 := by
  have h := S.act_br (hlsLorL hlsSl2F) u v
  rw [S.br_pos_pos_eq_zero hu hv, hlsEvenBr_zero_right] at h
  have h' : S.br (S.fL u) v + S.br u (S.fL v) = 0 := h.symm
  rw [S.br_symm (S.fL u) v] at h'
  linear_combination (norm := abel) h'



/-- The central charges commute with one another. -/
theorem central_charge_commute {u v u' v' : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt (-1) 0)
    (hu' : u' ∈ S.wt 1 0) (hv' : v' ∈ S.wt (-1) 0) :
    hlsEvenBr (S.br u v) (S.br u' v') = 0 := by
  have hz := S.act_br_pos_neg_eq_zero hu hv
  have h := S.act_br (S.br u v) u' v'
  have e1 : S.act (S.br u v) u' = 0 := by rw [hz]; rfl
  have e2 : S.act (S.br u v) v' = 0 := by rw [hz]; rfl
  simp only [e1, e2, map_zero, LinearMap.zero_apply, add_zero, zero_add] at h
  exact h

/-- The central charges span an ideal of the internal algebra. -/
theorem central_charge_ideal {u v : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt (-1) 0) (b : B) :
    ∃ z : B, hlsEvenBr (hlsInt b) (S.br u v) = hlsInt z := by
  have hu1 : S.hL u = (1 : ℂ) • u := by rw [S.hL_eq_on_wt_pos hu, one_smul]
  have hu2 : S.hR u = (0 : ℂ) • u := by rw [S.hR_zero_on_wt_pos hu, zero_smul]
  have hv1 : S.hL v = (-1 : ℂ) • v := by rw [S.hL_eq_on_wt_neg hv, neg_one_smul]
  have hv2 : S.hR v = (0 : ℂ) • v := by rw [S.hR_zero_on_wt_neg hv, zero_smul]
  obtain ⟨hu1', hu2'⟩ := S.act_int_eigen b hu1 hu2
  obtain ⟨hv1', hv2'⟩ := S.act_int_eigen b hv1 hv2
  obtain ⟨z₁, hz₁⟩ := S.br_pos_neg_is_int (S.mem_wt_of_eigen hu1' hu2') hv
  obtain ⟨z₂, hz₂⟩ := S.br_pos_neg_is_int hu (S.mem_wt_of_eigen hv1' hv2')
  refine ⟨z₁ + z₂, ?_⟩
  rw [S.act_br (hlsInt b) u v, hz₁, hz₂]
  simp [hlsInt, Prod.ext_iff]

/-- The mixed-chirality bracket `{Q_1, Q̄_1̇}` is a translation along `P_{1 1̇}`. -/
theorem br_pos_dotPos_mom {u w : V} (hu : u ∈ S.wt 1 0) (hw : w ∈ S.wt 0 1) :
    ∃ c : ℂ, S.br u w = hlsMom (c • hlsMomUnit 0 0) := by
  have hu1 : S.hL u = (1 : ℂ) • u := by rw [S.hL_eq_on_wt_pos hu, one_smul]
  have hu2 : S.hR u = (0 : ℂ) • u := by rw [S.hR_zero_on_wt_pos hu, zero_smul]
  have hw1 : S.hL w = (0 : ℂ) • w := by rw [S.hL_zero_on_wt_dotPos hw, zero_smul]
  have hw2 : S.hR w = (1 : ℂ) • w := by rw [S.hR_eq_on_wt_pos hw, one_smul]
  have ha := S.br_adL_eigen hu1 hw1
  have hb := S.br_adR_eigen hu2 hw2
  rw [show (1 : ℂ) + 0 = 1 by norm_num] at ha
  rw [show (0 : ℂ) + 1 = 1 by norm_num] at hb
  exact hlsEven_weight_one_one ha hb


end HLSGradedSymmetry


end GaloisForLFunctions.HTGeometry
