import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Quantitative interference from a nilpotent contraction

Finite telescoping controls displacement by a contraction whose N-th power vanishes.
This yields a numerical-range deficit and a strict operator-norm improvement for
positive combinations of two contractions when their product is nilpotent and the
first is symmetric. The actual prime-aperture application supplies the nilpotence
identity from support, rather than assuming a source sign.
-/

open Complex
open scoped InnerProduct
noncomputable section
namespace HTGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Finite telescoping bounds the displacement of any iterate of a contraction. -/
theorem contraction_norm_sub_pow_apply_le (C : E →L[ℂ] E) (hC : ‖C‖ ≤ 1)
    (n : ℕ) (x : E) : ‖x - (C^n) x‖ ≤ (n : ℝ) * ‖x-C x‖ := by
  have hcontract : ∀ y, ‖C y‖ ≤ ‖y‖ := fun y =>
    (C.le_opNorm y).trans (by nlinarith [norm_nonneg y])
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : x - (C^(n+1)) x = (x-C x) + C (x-(C^n) x) := by
      rw [pow_succ', mul_apply_eq_comp, map_sub]
      abel
    rw [heq]
    calc
      _ ≤ ‖x-C x‖ + ‖C (x-(C^n) x)‖ := norm_add_le _ _
      _ ≤ ‖x-C x‖ + (n : ℝ)*‖x-C x‖ := add_le_add (le_refl _)
        ((hcontract _).trans ih)
      _ = _ := by push_cast; ring

/-- A nilpotent contraction has a quantitative numerical-range gap, in denominator-free form. -/
theorem nilpotent_contraction_real_inner_gap (C : E →L[ℂ] E) (hC : ‖C‖ ≤ 1)
    (N : ℕ) (hN : C^N = 0) (x : E) :
    2*(N : ℝ)^(2 : ℕ) * (inner ℂ x (C x)).re ≤
      (2*(N : ℝ)^(2 : ℕ)-1)*‖x‖^(2 : ℕ) := by
  have htel := contraction_norm_sub_pow_apply_le C hC N x
  rw [hN, zero_apply, sub_zero] at htel
  have hCx : ‖C x‖ ≤ ‖x‖ := (C.le_opNorm x).trans (by
    nlinarith [norm_nonneg x])
  have hsq : ‖x‖^(2 : ℕ) ≤ (N : ℝ)^(2 : ℕ) * ‖x-C x‖^(2 : ℕ) := by
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [norm_nonneg x, norm_nonneg (x-C x)]
  have hdiff := norm_sub_sq (𝕜 := ℂ) x (C x)
  change ‖x-C x‖^(2 : ℕ) = ‖x‖^(2 : ℕ)-2*(inner ℂ x (C x)).re+‖C x‖^(2 : ℕ) at hdiff
  rw [hdiff] at hsq
  have hcxsq : ‖C x‖^(2 : ℕ) ≤ ‖x‖^(2 : ℕ) := by
    nlinarith [norm_nonneg x, norm_nonneg (C x)]
  have hmul := mul_le_mul_of_nonneg_left hcxsq (sq_nonneg (N : ℝ))
  nlinarith

/-- Two self-adjoint contractions with nilpotent product cannot align at their separate maxima. -/
theorem selfAdjoint_pair_sq_bound_of_nilpotent_product
    (A B : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (hAn : ‖A‖ ≤ 1) (hBn : ‖B‖ ≤ 1)
    (N : ℕ) (hN : (A*B)^N = 0)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (x : E) :
    (N : ℝ)^(2 : ℕ) * ‖(u : ℂ) • A x + (v : ℂ) • B x‖^(2 : ℕ) ≤
      ((N : ℝ)^(2 : ℕ) * (u+v)^(2 : ℕ)-u*v)*‖x‖^(2 : ℕ) := by
  have hAB : ‖A*B‖ ≤ 1 :=
    (norm_mul_le A B).trans (by nlinarith [norm_nonneg A, norm_nonneg B])
  have hgap := nilpotent_contraction_real_inner_gap (A*B) hAB N hN x
  have hinner : inner ℂ (A x) (B x) = inner ℂ x ((A*B) x) := hA x (B x)
  have hAx : ‖A x‖ ≤ ‖x‖ := (A.le_opNorm x).trans (by nlinarith [norm_nonneg x])
  have hBx : ‖B x‖ ≤ ‖x‖ := (B.le_opNorm x).trans (by nlinarith [norm_nonneg x])
  have hAsq : ‖A x‖^(2 : ℕ) ≤ ‖x‖^(2 : ℕ) := by nlinarith [norm_nonneg (A x), norm_nonneg x]
  have hBsq : ‖B x‖^(2 : ℕ) ≤ ‖x‖^(2 : ℕ) := by nlinarith [norm_nonneg (B x), norm_nonneg x]
  have hid : ‖(u : ℂ) • A x + (v : ℂ) • B x‖^(2 : ℕ) =
      u^(2 : ℕ)*‖A x‖^(2 : ℕ)+v^(2 : ℕ)*‖B x‖^(2 : ℕ)+2*(u*v)*(inner ℂ x ((A*B) x)).re := by
    rw [norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hu, abs_of_nonneg hv,
      inner_smul_left, inner_smul_right, hinner]
    simp only [Complex.conj_ofReal]
    change (u*‖A x‖)^(2 : ℕ)+2*((u : ℂ)*((v : ℂ)*inner ℂ x ((A*B) x))).re+(v*‖B x‖)^(2 : ℕ) = _
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero]
    ring
  rw [hid]
  have ha := mul_le_mul_of_nonneg_left hAsq (mul_nonneg (sq_nonneg (N : ℝ)) (sq_nonneg u))
  have hb := mul_le_mul_of_nonneg_left hBsq (mul_nonneg (sq_nonneg (N : ℝ)) (sq_nonneg v))
  have hc := mul_le_mul_of_nonneg_left hgap (mul_nonneg hu hv)
  nlinarith

/-- The numerical-range gap gives an explicit operator-norm improvement for a positive pair. -/
theorem selfAdjoint_pair_opNorm_sq_bound_of_nilpotent_product
    (A B : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (hAn : ‖A‖ ≤ 1) (hBn : ‖B‖ ≤ 1)
    (N : ℕ) (hNpos : 0 < N) (hN : (A*B)^N = 0)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (N : ℝ)^(2 : ℕ) * ‖(u : ℂ) • A + (v : ℂ) • B‖^(2 : ℕ) ≤
      (N : ℝ)^(2 : ℕ) * (u+v)^(2 : ℕ)-u*v := by
  let H : E →L[ℂ] E := (u : ℂ) • A + (v : ℂ) • B
  let R : ℝ := (N : ℝ)^(2 : ℕ)*(u+v)^(2 : ℕ)-u*v
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hn1 : 1 ≤ (N : ℝ) := by exact_mod_cast hNpos
  have hn2 : 1 ≤ (N : ℝ)^(2 : ℕ) := by nlinarith
  have hR : 0 ≤ R := by
    have hm := mul_le_mul_of_nonneg_right hn2 (sq_nonneg (u+v))
    dsimp [R]
    nlinarith [sq_nonneg u, sq_nonneg v, mul_nonneg hu hv]
  have hsqrt : Real.sqrt R ^ (2 : ℕ) = R := Real.sq_sqrt hR
  have hbound : ∀ x : E, ‖H x‖ ≤ (Real.sqrt R / (N : ℝ))*‖x‖ := by
    intro x
    have hb := selfAdjoint_pair_sq_bound_of_nilpotent_product A B hA hAn hBn N hN u v hu hv x
    change (N : ℝ)^(2 : ℕ)*‖H x‖^(2 : ℕ) ≤ R*‖x‖^(2 : ℕ) at hb
    have hnprod : 0 ≤ (N : ℝ)*‖H x‖ := mul_nonneg hn.le (norm_nonneg _)
    have hsprod : 0 ≤ Real.sqrt R*‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hlin : (N : ℝ)*‖H x‖ ≤ Real.sqrt R*‖x‖ := by
      have hsq : ((N : ℝ)*‖H x‖)^(2 : ℕ) ≤ (Real.sqrt R*‖x‖)^(2 : ℕ) := by
        nlinarith
      nlinarith
    have heq : (N : ℝ)*((Real.sqrt R/(N : ℝ))*‖x‖) = Real.sqrt R*‖x‖ := by
      field_simp
    nlinarith
  have hop : ‖H‖ ≤ Real.sqrt R / (N : ℝ) :=
    ContinuousLinearMap.opNorm_le_bound H (div_nonneg (Real.sqrt_nonneg _) hn.le) hbound
  have hnH : (N : ℝ)*‖H‖ ≤ Real.sqrt R := by
    have hmul := mul_le_mul_of_nonneg_left hop hn.le
    have heq : (N : ℝ)*(Real.sqrt R/(N : ℝ)) = Real.sqrt R := by field_simp
    nlinarith
  change (N : ℝ)^(2 : ℕ) * ‖H‖^(2 : ℕ) ≤ R
  have hprod : 0 ≤ (N : ℝ)*‖H‖ := mul_nonneg hn.le (norm_nonneg _)
  nlinarith [Real.sqrt_nonneg R]

/-- Strict subadditivity for positive weights; a nilpotent product rules out aligned maxima. -/
theorem selfAdjoint_pair_norm_lt_sum_of_nilpotent_product
    (A B : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (hAn : ‖A‖ ≤ 1) (hBn : ‖B‖ ≤ 1)
    (N : ℕ) (hNpos : 0 < N) (hN : (A*B)^N = 0)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    ‖(u : ℂ) • A + (v : ℂ) • B‖ < u+v := by
  have hb := selfAdjoint_pair_opNorm_sq_bound_of_nilpotent_product
    A B hA hAn hBn N hNpos hN u v hu.le hv.le
  by_contra hn
  have hs : u+v ≤ ‖(u : ℂ) • A + (v : ℂ) • B‖ := le_of_not_gt hn
  have hsq : (u+v)^(2 : ℕ) ≤ ‖(u : ℂ) • A + (v : ℂ) • B‖^(2 : ℕ) := by
    nlinarith [norm_nonneg ((u : ℂ) • A + (v : ℂ) • B)]
  have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg (N : ℝ))
  nlinarith [mul_pos hu hv]

end HTGeometry
