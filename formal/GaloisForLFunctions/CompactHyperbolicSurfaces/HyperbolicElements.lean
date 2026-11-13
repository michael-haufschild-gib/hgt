import GaloisForLFunctions.CompactHyperbolicSurfaces.CocompactGroups
import GaloisForLFunctions.RHTower.HyperbolicOrbitalIntegral
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# Hyperbolic elements of `SL(2, ℝ)`

* `exists_conj_dilSL`: if `|tr g| > 2` then `g = ±σ · dil(N) · σ⁻¹` with `N > 0`, `N ≠ 1`, where
  `dil(N) = diag(√N, 1/√N)` acts by `z ↦ Nz`.
* `eq_dilSL_of_commute`: an element commuting with `dil(N)`, `N ≠ 1`, is `±dil(M)`.
* `dist_I_dilSL_smul_I`: `d(i, M i) = |log M|`.
* `hypLen_conj_dilSL`: the length `hypLen g = 2 arcosh(|tr g|/2)` of `±σ dil(M) σ⁻¹` is `|log M|`.
-/

open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry RHTower

noncomputable section

/-- The trace `g₀₀ + g₁₁`. -/
def trSL (g : SL(2, ℝ)) : ℝ := g 0 0 + g 1 1

/-- The translation length `2 arcosh(|tr g|/2)`. -/
def hypLen (g : SL(2, ℝ)) : ℝ := 2 * Real.arcosh (|trSL g| / 2)

theorem det_SL (g : SL(2, ℝ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe g
  rwa [Matrix.det_fin_two] at h

theorem neg_smul_SL (g : SL(2, ℝ)) (z : ℍ) : (-g) • z = g • z := by
  ext1
  rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Complex.ofReal_neg]
  rw [show -(((g 0 0 : ℝ) : ℂ)) * (z : ℂ) + -((g 0 1 : ℝ) : ℂ) =
      -((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) by ring,
    show -(((g 1 0 : ℝ) : ℂ)) * (z : ℂ) + -((g 1 1 : ℝ) : ℂ) =
      -((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) by ring, neg_div_neg_eq]

theorem trSL_neg (g : SL(2, ℝ)) : trSL (-g) = -trSL g := by
  simp only [trSL, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]; ring

theorem trSL_inv (g : SL(2, ℝ)) : trSL g⁻¹ = trSL g := by
  simp only [trSL, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  ring

theorem trSL_mul_comm (g h : SL(2, ℝ)) : trSL (g * h) = trSL (h * g) := by
  simp only [trSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem trSL_conj (σ g : SL(2, ℝ)) : trSL (σ * g * σ⁻¹) = trSL g := by
  rw [trSL_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

/-! ### Dilations -/

theorem dilSL_apply {l : ℝ} (hl : 0 < l) :
    ((dilSL l hl : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![√l, 0; 0, (√l)⁻¹] := rfl

theorem dilSL_mul {M M' : ℝ} (hM : 0 < M) (hM' : 0 < M') :
    dilSL M hM * dilSL M' hM' = dilSL (M * M') (mul_pos hM hM') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilSL_apply, Matrix.mul_apply, Fin.sum_univ_two, Real.sqrt_mul hM.le, mul_comm]

theorem dilSL_one : dilSL 1 one_pos = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dilSL_apply]

theorem dilSL_inv {M : ℝ} (hM : 0 < M) : (dilSL M hM)⁻¹ = dilSL M⁻¹ (inv_pos.mpr hM) := by
  rw [inv_eq_iff_mul_eq_one, dilSL_mul, ← dilSL_one]
  congr 1
  exact mul_inv_cancel₀ hM.ne'

/-- `t ↦ dil(eᵗ)` as a homomorphism. -/
def dilHom : Multiplicative ℝ →* SL(2, ℝ) where
  toFun t := dilSL (Real.exp (Multiplicative.toAdd t)) (Real.exp_pos _)
  map_one' := by simp only [toAdd_one, Real.exp_zero]; exact dilSL_one
  map_mul' x y := by
    rw [dilSL_mul]; congr 1; rw [toAdd_mul, Real.exp_add]

theorem dilSL_eq_dilHom {M : ℝ} (hM : 0 < M) :
    dilSL M hM = dilHom (Multiplicative.ofAdd (Real.log M)) := by
  simp only [dilHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  congr 1
  exact (Real.exp_log hM).symm

theorem dilSL_zpow {M : ℝ} (hM : 0 < M) (k : ℤ) :
    dilSL M hM ^ k = dilSL (Real.exp (k * Real.log M)) (Real.exp_pos _) := by
  rw [dilSL_eq_dilHom, ← map_zpow, ← ofAdd_zsmul, zsmul_eq_mul]
  simp only [dilHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]

theorem trSL_dilSL {M : ℝ} (hM : 0 < M) : trSL (dilSL M hM) = √M + (√M)⁻¹ := by
  simp [trSL, dilSL_apply]

/-! ### Conjugation to a dilation -/

/-- Positive trace `t > 2`: `g σ = σ dil(N)` for some `σ`, `N ≠ 1`.  The columns of `σ` are
eigenvectors: `(1, 0), (b, d − a)` if `c = 0`, and `(l − d, c), (l⁻¹ − d, c)` otherwise, where
`l² − t l + 1 = 0`. -/
theorem exists_mul_eq_mul_dilSL {g : SL(2, ℝ)} (ht : 2 < trSL g) :
    ∃ (σ : SL(2, ℝ)) (N : ℝ) (hN : 0 < N), N ≠ 1 ∧ g * σ = σ * dilSL N hN := by
  have hdet := det_SL g
  have ht' : 2 < g 0 0 + g 1 1 := ht
  by_cases hc : g 1 0 = 0
  · have had : g 0 0 * g 1 1 = 1 := by rw [hc] at hdet; linarith
    have ha : 0 < g 0 0 := by
      by_contra h
      have h' : g 0 0 ≤ 0 := not_lt.mp h
      have : g 1 1 ≤ 0 := by nlinarith
      linarith
    have hda : g 1 1 - g 0 0 ≠ 0 := by
      intro h
      have e : g 1 1 = g 0 0 := by linarith
      rw [e] at had ht'
      nlinarith
    have hd : g 1 1 = (g 0 0)⁻¹ := by field_simp; linarith
    refine ⟨⟨!![1 / (g 1 1 - g 0 0), g 0 1; 0, g 1 1 - g 0 0], by
      rw [Matrix.det_fin_two_of, mul_zero, sub_zero, one_div_mul_cancel hda]⟩,
      g 0 0 ^ 2, by positivity, ?_, ?_⟩
    · intro h
      have : g 0 0 = 1 := by nlinarith
      rw [this] at had ht'
      linarith
    · have hsq : √(g 0 0 ^ 2) = g 0 0 := Real.sqrt_sq ha.le
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, dilSL_apply, hsq, hc]
      all_goals first
        | ring1
        | (rw [hd])
        | linear_combination (g 1 1 - g 0 0) * hd
  · obtain ⟨l, hldef⟩ : ∃ l : ℝ, l = (g 0 0 + g 1 1 + √((g 0 0 + g 1 1) ^ 2 - 4)) / 2 :=
      ⟨_, rfl⟩
    have hD : 0 < √((g 0 0 + g 1 1) ^ 2 - 4) := Real.sqrt_pos.mpr (by nlinarith)
    have hD2 : √((g 0 0 + g 1 1) ^ 2 - 4) ^ 2 = (g 0 0 + g 1 1) ^ 2 - 4 :=
      Real.sq_sqrt (by nlinarith)
    have hl : 1 < l := by rw [hldef]; linarith
    have hl0 : 0 < l := by linarith
    have hquad : l ^ 2 - (g 0 0 + g 1 1) * l + 1 = 0 := by rw [hldef]; nlinarith [hD2]
    have hlinv : l⁻¹ = g 0 0 + g 1 1 - l := by
      field_simp
      nlinarith [hquad]
    have hquad' : (l⁻¹) ^ 2 - (g 0 0 + g 1 1) * l⁻¹ + 1 = 0 := by
      rw [hlinv]; linear_combination hquad
    have hll : l - l⁻¹ ≠ 0 := by
      rw [hlinv]; intro h; nlinarith
    have hδ : g 1 0 * (l - l⁻¹) ≠ 0 := mul_ne_zero hc hll
    refine ⟨⟨!![(l - g 1 1) / (g 1 0 * (l - l⁻¹)), l⁻¹ - g 1 1;
      g 1 0 / (g 1 0 * (l - l⁻¹)), g 1 0], ?_⟩, l ^ 2, by positivity, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      have : (l - g 1 1) / (g 1 0 * (l - l⁻¹)) * g 1 0 - (l⁻¹ - g 1 1) *
          (g 1 0 / (g 1 0 * (l - l⁻¹))) = (g 1 0 * (l - l⁻¹)) / (g 1 0 * (l - l⁻¹)) := by ring
      rw [this, div_self hδ]
    · intro h
      have : l = 1 := by nlinarith
      linarith
    · have hsq : √(l ^ 2) = l := Real.sqrt_sq hl0.le
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, dilSL_apply, hsq]
      · linear_combination (-1 / (g 1 0 * (l - l⁻¹))) * hquad +
          (-1 / (g 1 0 * (l - l⁻¹))) * hdet
      · linear_combination -hquad' - hdet
      · ring
      · ring

/-- **Hyperbolic elements are conjugate to dilations.**  If `|tr g| > 2` then
`g = ±σ · dil(N) · σ⁻¹` with `N ≠ 1`. -/
theorem exists_conj_dilSL {g : SL(2, ℝ)} (hg : 2 < |trSL g|) :
    ∃ (σ : SL(2, ℝ)) (N : ℝ) (hN : 0 < N), N ≠ 1 ∧
      (g = σ * dilSL N hN * σ⁻¹ ∨ g = -(σ * dilSL N hN * σ⁻¹)) := by
  rcases lt_abs.mp hg with h | h
  · obtain ⟨σ, N, hN, hN1, he⟩ := exists_mul_eq_mul_dilSL h
    exact ⟨σ, N, hN, hN1, Or.inl (by rw [← he, mul_inv_cancel_right])⟩
  · have h' : 2 < trSL (-g) := by rw [trSL_neg]; linarith
    obtain ⟨σ, N, hN, hN1, he⟩ := exists_mul_eq_mul_dilSL h'
    refine ⟨σ, N, hN, hN1, Or.inr ?_⟩
    rw [← he, mul_inv_cancel_right, neg_neg]

/-! ### The commutant of a dilation -/

/-- **What commutes with `dil(N)`, `N ≠ 1`, is `±dil(M)`.** -/
theorem eq_dilSL_of_commute {N : ℝ} (hN : 0 < N) (hN1 : N ≠ 1) {δ : SL(2, ℝ)}
    (h : δ * dilSL N hN = dilSL N hN * δ) :
    ∃ (M : ℝ) (hM : 0 < M), δ = dilSL M hM ∨ δ = -dilSL M hM := by
  have hs : 0 < √N := Real.sqrt_pos.mpr hN
  have hne : √N - (√N)⁻¹ ≠ 0 := by
    intro h0
    have : √N * √N = 1 := by field_simp at h0; nlinarith
    rw [Real.mul_self_sqrt hN.le] at this
    exact hN1 this
  have e01 : δ 0 1 = 0 := by
    have := congrFun (congrFun (congrArg Subtype.val h) 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, dilSL_apply] at this
    have h2 : δ 0 1 * ((√N)⁻¹ - √N) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (by linarith) hne
  have e10 : δ 1 0 = 0 := by
    have := congrFun (congrFun (congrArg Subtype.val h) 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, dilSL_apply] at this
    have h2 : δ 1 0 * (√N - (√N)⁻¹) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd h3 hne
  have hdet := det_SL δ
  rw [e01, zero_mul, sub_zero] at hdet
  have h00 : δ 0 0 ≠ 0 := fun h0 => by rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
  refine ⟨δ 0 0 ^ 2, by positivity, ?_⟩
  have hinv : δ 1 1 = (δ 0 0)⁻¹ := by field_simp; linarith
  rcases lt_or_gt_of_ne h00 with hneg | hpos
  · right
    have hsq : √(δ 0 0 ^ 2) = -δ 0 0 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_neg hneg]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dilSL_apply, hsq, e01, e10, hinv]
  · left
    have hsq : √(δ 0 0 ^ 2) = δ 0 0 := Real.sqrt_sq hpos.le
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dilSL_apply, hsq, e01, e10, hinv]

/-! ### Displacement and length -/

theorem cosh_half_log {M : ℝ} (hM : 0 < M) : Real.cosh (Real.log M / 2) = (√M + (√M)⁻¹) / 2 := by
  have hs : Real.exp (Real.log M / 2) = √M := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hM]; ring_nf
  rw [Real.cosh_eq, Real.exp_neg, hs]

/-- **The displacement of a dilation.**  `d(i, M i) = |log M|`. -/
theorem dist_I_dilSL_smul_I {M : ℝ} (hM : 0 < M) : dist I (dilSL M hM • I) = |Real.log M| := by
  have hu := pairU_dilSL_smul hM I
  simp only [UpperHalfPlane.coe_I, Complex.I_re, Complex.I_im, zero_div, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_one] at hu
  rw [pairU_eq_cosh] at hu
  have hcl : Real.cosh (Real.log M) = (M + M⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, Real.exp_log hM]
  have hc : Real.cosh (dist I (dilSL M hM • I)) = Real.cosh (Real.log M) := by
    have h2 : Real.cosh (dist I (dilSL M hM • I)) = 2 * ((M - 1) ^ 2 / (4 * M)) + 1 := by
      linarith
    rw [h2, hcl]
    field_simp
    ring
  have h1 := Real.arcosh_cosh (dist_nonneg (x := I) (y := dilSL M hM • I))
  rw [hc, ← Real.cosh_abs, Real.arcosh_cosh (abs_nonneg _)] at h1
  exact h1.symm

/-- **The length of a conjugated dilation.**  `hypLen (±σ dil(M) σ⁻¹) = |log M|`. -/
theorem hypLen_conj_dilSL {M : ℝ} (hM : 0 < M) (σ : SL(2, ℝ)) {g : SL(2, ℝ)}
    (hg : g = σ * dilSL M hM * σ⁻¹ ∨ g = -(σ * dilSL M hM * σ⁻¹)) :
    hypLen g = |Real.log M| := by
  have htr : |trSL g| = √M + (√M)⁻¹ := by
    have hs : 0 < √M + (√M)⁻¹ := by positivity
    rcases hg with rfl | rfl
    · rw [trSL_conj, trSL_dilSL, abs_of_pos hs]
    · rw [trSL_neg, trSL_conj, trSL_dilSL, abs_neg, abs_of_pos hs]
  rw [hypLen, htr, ← cosh_half_log hM, ← Real.cosh_abs, Real.arcosh_cosh (abs_nonneg _), abs_div,
    abs_two]
  ring

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
