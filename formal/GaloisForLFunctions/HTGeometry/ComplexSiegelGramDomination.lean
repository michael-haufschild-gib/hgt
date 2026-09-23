import GaloisForLFunctions.HTGeometry.ComplexJacobiLeadingMinors
import GaloisForLFunctions.HTGeometry.ComplexSiegelQuasiDiagonal

/-!
# Hermitian projected norms and determinant domination

The complex projected Jacobi norm is the exact squared Hermitian distance to the span of earlier
coordinates.  This intrinsic description transfers pointwise domination of Hermitian forms through
an injective rectangular congruence and then to determinants.  It is the Hermitian counterpart of
`SiegelGramDomination` needed for simultaneous real/complex number-field reduction.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

noncomputable section

variable {n k : ℕ}

/-- Complex vectors supported on coordinates before `i`. -/
def complexLowerSupport (i : Fin n) : Submodule ℂ (Fin n → ℂ) where
  carrier := {w | ∀ p : Fin n, i ≤ p → w p = 0}
  add_mem' := by
    intro a b ha hb p hp
    show a p + b p = 0
    rw [ha p hp, hb p hp, add_zero]
  zero_mem' := by intro p _; rfl
  smul_mem' := by
    intro c a ha p hp
    show c * a p = 0
    rw [ha p hp, mul_zero]

theorem mem_complexLowerSupport {i : Fin n} {w : Fin n → ℂ} :
    w ∈ complexLowerSupport i ↔ ∀ p : Fin n, i ≤ p → w p = 0 := Iff.rfl

/-- Hermitian squared norm after projecting away Jacobi coordinates below `i`. -/
def ComplexJacobiData.projNorm (J : ComplexJacobiData n)
    (i : Fin n) (v : Fin n → ℂ) : ℝ :=
  ∑ m ∈ Finset.univ.filter (fun m : Fin n => i ≤ m),
    J.d m * ‖J.U.mulVec v m‖ ^ (2 : ℕ)

theorem ComplexJacobiData.projNorm_nonneg (J : ComplexJacobiData n)
    (i : Fin n) (v : Fin n → ℂ) : 0 ≤ J.projNorm i v :=
  Finset.sum_nonneg fun m _ => mul_nonneg (J.pos m).le (sq_nonneg _)

theorem ComplexJacobiData.mulVec_single (J : ComplexJacobiData n) (j m : Fin n) :
    J.U.mulVec (Pi.single j (1 : ℂ)) m = J.U m j := by
  rw [Matrix.mulVec_single]
  simp

/-- Projected Hermitian norm of the `i`-th coordinate vector. -/
theorem ComplexJacobiData.projNorm_self (J : ComplexJacobiData n) (i : Fin n) :
    J.projNorm i (Pi.single i (1 : ℂ)) = J.d i := by
  classical
  rw [ComplexJacobiData.projNorm]
  refine (Finset.sum_eq_single i (fun m hm hmi => ?_) (fun hcon => ?_)).trans ?_
  · rw [Finset.mem_filter] at hm
    have hlt : i < m := lt_of_le_of_ne hm.2 (Ne.symm hmi)
    rw [J.mulVec_single, J.upper m i hlt, norm_zero]
    ring
  · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ i, le_refl i⟩) hcon
  · rw [J.mulVec_single, J.unit i, norm_one, one_pow, mul_one]

/-- An upper triangular complex matrix preserves lower coordinate support. -/
theorem ComplexJacobiData.mulVec_lower (J : ComplexJacobiData n)
    {i : Fin n} {w : Fin n → ℂ} (hw : w ∈ complexLowerSupport i)
    {m : Fin n} (hm : i ≤ m) : J.U.mulVec w m = 0 := by
  classical
  show ∑ p, J.U m p * w p = 0
  refine Finset.sum_eq_zero fun p _ => ?_
  rcases lt_or_ge p m with hpm | hpm
  · rw [J.upper m p hpm, zero_mul]
  · rw [hw p (le_trans hm hpm), mul_zero]

/-- Projected Hermitian norm is at most distance to any lower-supported vector. -/
theorem ComplexJacobiData.projNorm_le_form_sub (J : ComplexJacobiData n)
    (i : Fin n) (v : Fin n → ℂ) {w : Fin n → ℂ} (hw : w ∈ complexLowerSupport i) :
    J.projNorm i v ≤
      (star (v - w) ⬝ᵥ J.form.mulVec (v - w)).re := by
  classical
  rw [J.quadForm_eq (v - w)]
  have hcoord : ∀ m : Fin n, i ≤ m →
      J.U.mulVec (v - w) m = J.U.mulVec v m := by
    intro m hm
    rw [Matrix.mulVec_sub]
    show J.U.mulVec v m - J.U.mulVec w m = J.U.mulVec v m
    rw [J.mulVec_lower hw hm, sub_zero]
  rw [ComplexJacobiData.projNorm]
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (fun m : Fin n => i ≤ m) Finset.univ)
    fun m _ _ => mul_nonneg (J.pos m).le (sq_nonneg _))
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_filter] at hm
  rw [hcoord m hm.2]

/-- A lower-supported complex vector with zero transformed lower coordinates is zero. -/
theorem ComplexJacobiData.eq_zero_of_mulVec_lower (J : ComplexJacobiData n)
    {i : Fin n} {w : Fin n → ℂ} (hw : w ∈ complexLowerSupport i)
    (h : ∀ m : Fin n, m < i → J.U.mulVec w m = 0) : w = 0 := by
  classical
  have key : ∀ q : ℕ, ∀ p : Fin n,
      p < i → (i : ℕ) - (p : ℕ) ≤ q → w p = 0 := by
    intro q
    induction q with
    | zero =>
        intro p hp hq
        exact absurd (Fin.lt_def.1 hp) (by omega)
    | succ q ih =>
        intro p hp hq
        have hexp : J.U.mulVec w p = w p +
            ∑ r ∈ Finset.univ.filter (fun r : Fin n => p < r), J.U p r * w r := by
          show ∑ r, J.U p r * w r = _
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : Fin n => p < r)]
          rw [add_comm]
          congr 1
          refine (Finset.sum_eq_single p (fun r hr hrp => ?_) (fun hcon => ?_)).trans ?_
          · rw [Finset.mem_filter] at hr
            have hrlt : r < p := lt_of_le_of_ne (not_lt.1 hr.2) hrp
            rw [J.upper p r hrlt, zero_mul]
          · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ p, lt_irrefl p⟩) hcon
          · rw [J.unit p, one_mul]
        have htail : (∑ r ∈ Finset.univ.filter (fun r : Fin n => p < r),
            J.U p r * w r) = 0 := by
          refine Finset.sum_eq_zero fun r hr => ?_
          rw [Finset.mem_filter] at hr
          rcases lt_or_ge r i with hri | hri
          · rw [ih r hri (by
              have h1 := Fin.lt_def.1 hr.2
              omega), mul_zero]
          · rw [hw r hri, mul_zero]
        have hp0 := h p hp
        rw [hexp, htail, add_zero] at hp0
        exact hp0
  funext p
  rcases lt_or_ge p i with hp | hp
  · exact key ((i : ℕ) - (p : ℕ)) p hp (le_refl _)
  · exact hw p hp

def complexTruncLower (i : Fin n) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun m => if m < i then x m else 0

theorem complexTruncLower_mem (i : Fin n) (x : Fin n → ℂ) :
    complexTruncLower i x ∈ complexLowerSupport i := by
  intro p hp
  simp [complexTruncLower, not_lt.2 hp]

def ComplexJacobiData.lowerMap (J : ComplexJacobiData n) (i : Fin n) :
    complexLowerSupport i →ₗ[ℂ] complexLowerSupport i where
  toFun w := ⟨complexTruncLower i (J.U.mulVec (w : Fin n → ℂ)),
    complexTruncLower_mem i _⟩
  map_add' := by
    intro a b
    refine Subtype.ext ?_
    funext m
    show complexTruncLower i (J.U.mulVec ((a : Fin n → ℂ) + b)) m =
      complexTruncLower i (J.U.mulVec (a : Fin n → ℂ)) m +
        complexTruncLower i (J.U.mulVec (b : Fin n → ℂ)) m
    rw [Matrix.mulVec_add]
    by_cases hm : m < i <;> simp [complexTruncLower, hm]
  map_smul' := by
    intro c a
    refine Subtype.ext ?_
    funext m
    show complexTruncLower i (J.U.mulVec (c • (a : Fin n → ℂ))) m =
      c * complexTruncLower i (J.U.mulVec (a : Fin n → ℂ)) m
    rw [Matrix.mulVec_smul]
    by_cases hm : m < i <;> simp [complexTruncLower, hm]

theorem ComplexJacobiData.lowerMap_injective (J : ComplexJacobiData n) (i : Fin n) :
    Function.Injective (J.lowerMap i) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  refine Subtype.ext ?_
  refine J.eq_zero_of_mulVec_lower w.2 fun m hm => ?_
  have hwm := congrFun (congrArg Subtype.val hw) m
  show J.U.mulVec (w : Fin n → ℂ) m = 0
  simpa [ComplexJacobiData.lowerMap, complexTruncLower, hm] using hwm

/-- Intrinsic Hermitian projection onto the lower-coordinate span exists. -/
theorem ComplexJacobiData.exists_proj (J : ComplexJacobiData n)
    (i : Fin n) (v : Fin n → ℂ) :
    ∃ w : Fin n → ℂ, w ∈ complexLowerSupport i ∧
      ∀ m : Fin n, m < i → J.U.mulVec w m = J.U.mulVec v m := by
  classical
  have hsurj : Function.Surjective (J.lowerMap i) :=
    LinearMap.injective_iff_surjective.1 (J.lowerMap_injective i)
  obtain ⟨w, hw⟩ := hsurj
    ⟨complexTruncLower i (J.U.mulVec v), complexTruncLower_mem i _⟩
  refine ⟨(w : Fin n → ℂ), w.2, fun m hm => ?_⟩
  have hwm := congrFun (congrArg Subtype.val hw) m
  simpa [ComplexJacobiData.lowerMap, complexTruncLower, hm] using hwm

/-- Complex projected norm is exact squared Hermitian distance to lower support. -/
theorem ComplexJacobiData.projNorm_eq_form_sub (J : ComplexJacobiData n)
    (i : Fin n) (v : Fin n → ℂ) :
    ∃ w : Fin n → ℂ, w ∈ complexLowerSupport i ∧
      J.projNorm i v = (star (v - w) ⬝ᵥ J.form.mulVec (v - w)).re := by
  classical
  obtain ⟨w, hw, hmatch⟩ := J.exists_proj i v
  refine ⟨w, hw, ?_⟩
  have hall : ∀ m : Fin n,
      J.d m * ‖J.U.mulVec (v - w) m‖ ^ (2 : ℕ) =
        if i ≤ m then J.d m * ‖J.U.mulVec v m‖ ^ (2 : ℕ) else 0 := by
    intro m
    by_cases hm : i ≤ m
    · rw [if_pos hm]
      have hcoord : J.U.mulVec (v - w) m = J.U.mulVec v m := by
        rw [Matrix.mulVec_sub]
        show J.U.mulVec v m - J.U.mulVec w m = J.U.mulVec v m
        rw [J.mulVec_lower hw hm, sub_zero]
      rw [hcoord]
    · rw [if_neg hm]
      have hmi : m < i := not_le.1 hm
      have hz : J.U.mulVec (v - w) m = 0 := by
        rw [Matrix.mulVec_sub]
        show J.U.mulVec v m - J.U.mulVec w m = 0
        rw [hmatch m hmi, sub_self]
      rw [hz, norm_zero]
      ring
  have hmain : (star (v - w) ⬝ᵥ J.form.mulVec (v - w)).re = J.projNorm i v := by
    rw [J.quadForm_eq (v - w), ComplexJacobiData.projNorm,
      Finset.sum_congr rfl (fun m (_ : m ∈ (Finset.univ : Finset (Fin n))) => hall m),
      Finset.sum_ite, Finset.sum_const_zero, add_zero]
  exact hmain.symm

/-- Moving a rectangular complex matrix across the Hermitian pairing gives its adjoint. -/
theorem star_mulVec_dotProduct_rect
    (C : Matrix (Fin n) (Fin k) ℂ) (x : Fin k → ℂ) (y : Fin n → ℂ) :
    star (C.mulVec x) ⬝ᵥ y = star x ⬝ᵥ (Matrix.conjTranspose C).mulVec y := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, map_sum, map_mul,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring

/-- Hermitian congruence evaluates the source form on the image vector. -/
theorem star_dotProduct_complex_congr_mulVec
    (M : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin k) ℂ)
    (x : Fin k → ℂ) :
    star x ⬝ᵥ (Matrix.conjTranspose C * M * C).mulVec x =
      star (C.mulVec x) ⬝ᵥ M.mulVec (C.mulVec x) := by
  have h1 : (Matrix.conjTranspose C * M * C).mulVec x =
      (Matrix.conjTranspose C).mulVec (M.mulVec (C.mulVec x)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [h1, ← star_mulVec_dotProduct_rect C x]

/-- Congruence by an injective complex frame preserves positive definiteness. -/
theorem complex_posDef_congr {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef)
    {C : Matrix (Fin n) (Fin k) ℂ} (hC : Function.Injective C.mulVec) :
    (Matrix.conjTranspose C * M * C).PosDef := by
  exact hM.conjTranspose_mul_mul_same hC

/-- Pointwise Hermitian-form domination gives determinant domination after rectangular congruence. -/
theorem complex_det_congr_ge
    {A D₀ : Matrix (Fin n) (Fin n) ℂ} {c : ℝ} (hc : 0 < c)
    (hcmp : ∀ v : Fin n → ℂ,
      c * (star v ⬝ᵥ D₀.mulVec v).re ≤ (star v ⬝ᵥ A.mulVec v).re)
    {C : Matrix (Fin n) (Fin k) ℂ} {JG JG₀ : ComplexJacobiData k}
    (hJG : JG.form = Matrix.conjTranspose C * A * C)
    (hJG₀ : JG₀.form = Matrix.conjTranspose C * D₀ * C) :
    c ^ k * (Matrix.conjTranspose C * D₀ * C).det.re ≤
      (Matrix.conjTranspose C * A * C).det.re := by
  have hstep : ∀ l : Fin k, c * JG₀.d l ≤ JG.d l := by
    intro l
    obtain ⟨w, hw, hval⟩ := JG.projNorm_eq_form_sub l (Pi.single l 1)
    have hdl : JG.d l =
        (star (Pi.single l (1 : ℂ) - w) ⬝ᵥ
          JG.form.mulVec (Pi.single l (1 : ℂ) - w)).re := by
      rw [← hval, JG.projNorm_self l]
    have h0 : JG₀.d l ≤
        (star (Pi.single l (1 : ℂ) - w) ⬝ᵥ
          JG₀.form.mulVec (Pi.single l (1 : ℂ) - w)).re := by
      have h := JG₀.projNorm_le_form_sub l (Pi.single l 1) hw
      rwa [JG₀.projNorm_self l] at h
    set x : Fin k → ℂ := Pi.single l (1 : ℂ) - w with hx
    have hA : (star x ⬝ᵥ JG.form.mulVec x).re =
        (star (C.mulVec x) ⬝ᵥ A.mulVec (C.mulVec x)).re := by
      rw [hJG]
      exact congrArg Complex.re (star_dotProduct_complex_congr_mulVec A C x)
    have hD : (star x ⬝ᵥ JG₀.form.mulVec x).re =
        (star (C.mulVec x) ⬝ᵥ D₀.mulVec (C.mulVec x)).re := by
      rw [hJG₀]
      exact congrArg Complex.re (star_dotProduct_complex_congr_mulVec D₀ C x)
    have hkey := hcmp (C.mulVec x)
    rw [← hA, ← hD] at hkey
    calc
      c * JG₀.d l ≤ c * (star x ⬝ᵥ JG₀.form.mulVec x).re :=
        mul_le_mul_of_nonneg_left h0 hc.le
      _ ≤ (star x ⬝ᵥ JG.form.mulVec x).re := hkey
      _ = JG.d l := hdl.symm
  have hdet : (Matrix.conjTranspose C * A * C).det.re = ∏ l, JG.d l := by
    calc
      (Matrix.conjTranspose C * A * C).det.re = JG.form.det.re := by rw [hJG]
      _ = (((∏ l, JG.d l : ℝ) : ℂ)).re := congrArg Complex.re JG.det_form
      _ = ∏ l, JG.d l := rfl
  have hdet₀ : (Matrix.conjTranspose C * D₀ * C).det.re = ∏ l, JG₀.d l := by
    calc
      (Matrix.conjTranspose C * D₀ * C).det.re = JG₀.form.det.re := by rw [hJG₀]
      _ = (((∏ l, JG₀.d l : ℝ) : ℂ)).re := congrArg Complex.re JG₀.det_form
      _ = ∏ l, JG₀.d l := rfl
  have hprod : (∏ l : Fin k, (c * JG₀.d l)) = c ^ k * ∏ l, JG₀.d l := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hdet, hdet₀, ← hprod]
  exact Finset.prod_le_prod (fun l _ => (mul_pos hc (JG₀.pos l)).le)
    (fun l _ => hstep l)

end

end GaloisForLFunctions.HTGeometry
