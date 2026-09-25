import GaloisForLFunctions.RHTower.GL3InvariantMeasure
import GaloisForLFunctions.HTGeometry.JacobiSignFlip
import GaloisForLFunctions.HTGeometry.JacobiUniqueness
import GaloisForLFunctions.HTGeometry.SiegelFiniteness
import GaloisForLFunctions.HTGeometry.GaussianShiftInformation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals


/-!
# Reduction theory for `SL₃(ℤ)` on `h³`: the Siegel set

The reversed Gram matrix `w₀ · gram z · w₀` has Jacobi decomposition `Uᵀ diag(d) U` with
`U = [[1, x₁, x₃], [0, 1, x₂], [0, 0, 1]]` and `d = (1, y₁², y₁²y₂²)` (`jac_form`). The Siegel
conditions `dᵢ ≤ 2dᵢ₊₁`, `|Uᵢⱼ| ≤ 1` therefore cut out
`siegelSet = {|x₁|, |x₂|, |x₃| ≤ 1, y₁, y₂ ≥ 1/√2}` (`isSiegel_jac_iff`), and they are invariant under
rescaling the form, so only the point of `h³` matters (`mem_siegelSet_of_form_eq`).

The integral congruence `A ↦ gᵀAg` on reversed forms is the action of `γ = w₀ gᵀ w₀` on `h³`, so
the Siegel reduction theorem for positive definite forms gives the covering
(`exists_smul_mem_siegelSet`), and the finiteness half of Siegel's property gives
`finite_siegelTransitions`: only finitely many `γ ∈ SL₃(ℤ)` map a point of the Siegel set into it.
In coordinates the Siegel set lies in `[-1,1]³ × [1/2, ∞)²`, where `(y₁y₂)⁻³` is a product of
integrable factors, so it has finite volume (`volume_siegelSet_lt_top`).
-/

open Matrix MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

/-! ### The reversed Gram matrix and its Jacobi data -/

/-- The long Weyl element `w₀` (the order reversal). -/
def rev : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem rev_mul_rev : rev * rev = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rev, Matrix.mul_apply, Fin.sum_univ_three]

theorem rev_mul_rev_mul (X : Matrix (Fin 3) (Fin 3) ℝ) : rev * (rev * X) = X := by
  rw [← Matrix.mul_assoc, rev_mul_rev, Matrix.one_mul]

theorem rev_transpose : revᵀ = rev := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rev]

theorem det_rev : rev.det = -1 := by simp [rev, Matrix.det_fin_three]

/-- The Jacobi data `(U, d)` of `w₀ · gram z · w₀ = Uᵀ diag(d) U`:
`U = [[1, x₁, x₃], [0, 1, x₂], [0, 0, 1]]`, `d = (1, y₁², y₁²y₂²)`. -/
noncomputable def jac (z : H3) : JacobiData 3 where
  U := !![1, z.x1, z.x3; 0, 1, z.x2; 0, 0, 1]
  d := ![1, z.y1 ^ 2, z.y1 ^ 2 * z.y2 ^ 2]
  pos i := by
    have := z.y1_pos; have := z.y2_pos
    fin_cases i <;> simp <;> positivity
  upper i j h := by
    fin_cases i <;> fin_cases j <;> simp at h ⊢
  unit i := by fin_cases i <;> simp

theorem jac_form (z : H3) : (jac z).form = rev * z.gram * rev := by
  rw [gram_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [JacobiData.form, jac, rev, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] <;> ring

/-- Rescaling the diagonal of Jacobi data by `c > 0` rescales the form. -/
noncomputable def jacScale (J : JacobiData 3) {c : ℝ} (hc : 0 < c) : JacobiData 3 where
  U := J.U
  d := c • J.d
  pos i := mul_pos hc (J.pos i)
  upper := J.upper
  unit := J.unit

theorem jacScale_form (J : JacobiData 3) {c : ℝ} (hc : 0 < c) :
    (jacScale J hc).form = c • J.form := by
  ext i j
  rw [JacobiData.form_apply, Matrix.smul_apply, JacobiData.form_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [jacScale, smul_eq_mul, mul_assoc]

/-! ### The Siegel set in Iwasawa coordinates -/

/-- **The Siegel set** `|xᵢ| ≤ 1`, `y₁, y₂ ≥ 1/√2`. -/
def siegelSet : Set H3 :=
  {z | 1 ≤ 2 * z.y1 ^ 2 ∧ 1 ≤ 2 * z.y2 ^ 2 ∧ |z.x1| ≤ 1 ∧ |z.x2| ≤ 1 ∧ |z.x3| ≤ 1}

theorem isSiegel_jac_iff (z : H3) : (jac z).IsSiegel 2 1 ↔ z ∈ siegelSet := by
  have h1 := z.y1_pos
  constructor
  · rintro ⟨hd, hU⟩
    have e0 := hd 0 1 rfl
    have e1 := hd 1 2 rfl
    simp only [jac, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at e0 e1
    refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
    · have : 0 < z.y1 ^ 2 := by positivity
      nlinarith
    · simpa [jac] using hU 0 1
    · simpa [jac] using hU 1 2
    · simpa [jac] using hU 0 2
  · rintro ⟨hy1, hy2, hx1, hx2, hx3⟩
    refine ⟨fun i j hij => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp at hij <;> simp [jac] <;> nlinarith [sq_nonneg z.y1]
    · fin_cases i <;> fin_cases j <;> simp [jac, hx1, hx2, hx3]

/-- The Siegel conditions only see the Jacobi data up to rescaling of the form. -/
theorem mem_siegelSet_of_form_eq {J : JacobiData 3} {z : H3} {c : ℝ} (hc : 0 < c)
    (h : J.form = c • (jac z).form) (hS : J.IsSiegel 2 1) : z ∈ siegelSet := by
  rw [← isSiegel_jac_iff]
  have hf : J.form = (jacScale (jac z) hc).form := by rw [jacScale_form, h]
  have hU : J.U = (jacScale (jac z) hc).U := JacobiData.U_unique hf
  have hd : J.d = (jacScale (jac z) hc).d := JacobiData.d_unique hf
  refine ⟨fun i j hij => ?_, fun i j => ?_⟩
  · have := hS.1 i j hij
    rw [hd] at this
    simp only [jacScale, Pi.smul_apply, smul_eq_mul] at this
    nlinarith
  · have h2 := hS.2 i j
    rw [hU] at h2
    exact h2

/-! ### Every orbit meets the Siegel set -/

/-- `w₀` as an integral matrix. -/
def revZ : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem revZ_map : revZ.map (Int.castRingHom ℝ) = rev := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [revZ, rev]

theorem det_revZ : revZ.det = -1 := by simp [revZ, Matrix.det_fin_three]

theorem posDef_rev_gram (z : H3) : (rev * z.gram * rev).PosDef := by
  have hinj : Function.Injective rev.mulVec :=
    Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_iff_isUnit_det _ |>.2 (by
      rw [det_rev]; exact isUnit_one.neg))
  have := z.posDef_gram.conjTranspose_mul_mul_same hinj
  simpa [conjTranspose_eq_transpose_of_trivial, rev_transpose] using this

/-- **Siegel covering in `h³`.** Every `SL₃(ℤ)`-orbit meets the Siegel set. -/
theorem exists_smul_mem_siegelSet (z : H3) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 3) ℤ, γ • z ∈ siegelSet := by
  obtain ⟨g, J, hdet, hform, hS⟩ := exists_siegel_inOrbit_det_one (posDef_rev_gram z)
  have hγdet : (revZ * gᵀ * revZ).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet, det_revZ]; ring
  let γ : Matrix.SpecialLinearGroup (Fin 3) ℤ := ⟨revZ * gᵀ * revZ, hγdet⟩
  refine ⟨γ, ?_⟩
  set gR : Matrix (Fin 3) (Fin 3) ℝ := g.map (fun t : ℤ => (t : ℝ))
  set γR : Matrix (Fin 3) (Fin 3) ℝ := rev * gRᵀ * rev
  have hγR : ((slToGL γ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = γR := by
    show (revZ * gᵀ * revZ).map (Int.castRingHom ℝ) = γR
    rw [Matrix.map_mul, Matrix.map_mul, revZ_map, Matrix.transpose_map]
    rfl
  set M := γR * z.gram * γRᵀ
  have hMpd : M.PosDef := by
    have := posDef_conj (slToGL γ) z
    rwa [hγR] at this
  have hsmul : γ • z = ofMat M := by
    rw [sl_smul_def, smul_def, hγR]
  have hgram : (ofMat M).gram = (M 2 2)⁻¹ • M := gram_ofMat_of_posDef hMpd
  rw [hsmul]
  refine mem_siegelSet_of_form_eq (hMpd.diag_pos (i := 2)) ?_ hS
  rw [jac_form, hgram, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ (hMpd.diag_pos (i := 2)).ne',
    one_smul, hform]
  simp only [M, γR, Matrix.transpose_mul, rev_transpose, Matrix.transpose_transpose,
    Matrix.mul_assoc, rev_mul_rev_mul, rev_mul_rev, Matrix.mul_one]

/-! ### Finiteness of Siegel transitions -/

theorem isSiegel_jacScale (J : JacobiData 3) {c : ℝ} (hc : 0 < c) {t u : ℝ} :
    (jacScale J hc).IsSiegel t u ↔ J.IsSiegel t u := by
  constructor
  · rintro ⟨hd, hU⟩
    refine ⟨fun i j hij => ?_, hU⟩
    have := hd i j hij
    simp only [jacScale, Pi.smul_apply, smul_eq_mul] at this
    nlinarith
  · rintro ⟨hd, hU⟩
    refine ⟨fun i j hij => ?_, hU⟩
    have := hd i j hij
    simp only [jacScale, Pi.smul_apply, smul_eq_mul]
    nlinarith

/-- The real matrix `w₀ γᵀ w₀` through which `SL₃(ℤ)` acts on reversed forms. -/
noncomputable def revT (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rev * ((slToGL γ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * rev

theorem coe_slToGL (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
    ((slToGL γ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      (γ : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℝ) := rfl

theorem revT_injective : Function.Injective revT := by
  intro γ γ' h
  have h' : rev * (revT γ) * rev = rev * (revT γ') * rev := by rw [h]
  simp only [revT, Matrix.mul_assoc, rev_mul_rev_mul, rev_mul_rev, Matrix.mul_one] at h'
  have h2 := congrArg Matrix.transpose h'
  simp only [Matrix.transpose_transpose, coe_slToGL] at h2
  ext a b
  have := congrFun (congrFun h2 a) b
  simpa using this

/-- **Siegel finiteness in `h³`.** Only finitely many `γ ∈ SL₃(ℤ)` carry a point of the Siegel set
back into it. -/
theorem finite_siegelTransitions :
    {γ : Matrix.SpecialLinearGroup (Fin 3) ℤ | ∃ z ∈ siegelSet, γ • z ∈ siegelSet}.Finite := by
  refine ((siegel_finiteness 3 2 1 (by norm_num)).preimage revT_injective.injOn).subset ?_
  rintro γ ⟨z, hz, hγz⟩
  set A := ((slToGL γ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
  set M := A * z.gram * Aᵀ
  have hMpd : M.PosDef := posDef_conj (slToGL γ) z
  have hc := hMpd.diag_pos (i := 2)
  have hsmul : γ • z = ofMat M := by rw [sl_smul_def, smul_def]
  refine ⟨⟨revZ * (γ : Matrix (Fin 3) (Fin 3) ℤ)ᵀ * revZ, ?_, fun a b => ?_⟩, jac z,
    jacScale (jac (γ • z)) hc, (isSiegel_jac_iff z).2 hz,
    (isSiegel_jacScale _ hc).2 ((isSiegel_jac_iff _).2 hγz), ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      γ.2, det_revZ]
    norm_num
  · have : revT γ = (revZ * (γ : Matrix (Fin 3) (Fin 3) ℤ)ᵀ * revZ).map (Int.castRingHom ℝ) := by
      rw [Matrix.map_mul, Matrix.map_mul, revZ_map, Matrix.transpose_map]; rfl
    rw [this]; rfl
  · rw [jacScale_form, jac_form, hsmul, gram_ofMat_of_posDef hMpd, jac_form, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    simp only [M, revT, Matrix.transpose_mul, rev_transpose, Matrix.transpose_transpose,
      Matrix.mul_assoc, rev_mul_rev_mul]
    rfl

/-! ### The Siegel set has finite volume -/

/-- **The Siegel set has finite volume**: `∫_{|x|≤1} ∫_{y ≥ 1/√2} dx dy / (y₁y₂)³ < ∞`. -/
theorem volume_siegelSet_lt_top : volume siegelSet < ⊤ := by
  rw [volume_eq_lintegral]
  let I : Fin 5 → Set ℝ := fun i => if (i : ℕ) < 3 then Set.Icc (-1) 1 else Set.Ici (1 / 2)
  let f : Fin 5 → ℝ → ENNReal := fun i t =>
    if (i : ℕ) < 3 then 1 else ENNReal.ofReal ((t ^ 3)⁻¹)
  have hf : ∀ i, Measurable (f i) := by
    intro i
    by_cases hi : (i : ℕ) < 3
    · simp only [f, hi, if_true]; exact measurable_const
    · simp only [f, hi, if_false]; fun_prop
  have hI : MeasurableSet (Set.univ.pi I) := by
    refine MeasurableSet.univ_pi fun i => ?_
    by_cases hi : (i : ℕ) < 3
    · simp only [I, hi, if_true]; exact measurableSet_Icc
    · simp only [I, hi, if_false]; exact measurableSet_Ici
  have hsub : coords '' siegelSet ⊆ Set.univ.pi I := by
    rintro _ ⟨z, ⟨hy1, hy2, hx1, hx2, hx3⟩, rfl⟩ i -
    have h1 := z.y1_pos; have h2 := z.y2_pos
    fin_cases i <;> simp [I, coords, abs_le] at * <;> first
      | exact hx1 | exact hx2 | exact hx3 | nlinarith
  calc ∫⁻ p in coords '' siegelSet, rho p ≤ ∫⁻ p in Set.univ.pi I, rho p := lintegral_mono_set hsub
    _ = ∫⁻ p in Set.univ.pi I, ∏ i, f i (p i) := by
        refine setLIntegral_congr_fun hI fun p hp => ?_
        have h3 : (1 / 2 : ℝ) ≤ p 3 := by simpa [I] using hp 3 (Set.mem_univ _)
        have h4 : (1 / 2 : ℝ) ≤ p 4 := by simpa [I] using hp 4 (Set.mem_univ _)
        simp only [rho, f, Fin.prod_univ_five]
        simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
        norm_num
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ = ∏ i, ∫⁻ t in I i, f i t := by
        rw [volume_pi, Measure.restrict_pi_pi, lintegral_pi_prod _ hf]
    _ < ⊤ := by
        refine ENNReal.prod_lt_top fun i _ => ?_
        by_cases hi : (i : ℕ) < 3
        · simp only [I, f, hi, if_true, setLIntegral_const, one_mul, Real.volume_Icc]
          exact ENNReal.ofReal_lt_top
        · simp only [I, f, hi, if_false]
          rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
          have hint := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1)
            (by norm_num : (0 : ℝ) < 1 / 2)
          refine lt_of_eq_of_lt ?_ hint.setLIntegral_lt_top
          refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
          have ht0 : 0 < t := lt_trans (by norm_num) (Set.mem_Ioi.1 ht)
          rw [Real.rpow_neg ht0.le]
          norm_cast

end H3
end GaloisForLFunctions.RHTower.GL3
