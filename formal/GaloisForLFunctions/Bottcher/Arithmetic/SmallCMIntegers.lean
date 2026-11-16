import GaloisForLFunctions.HTGeometry.AlgebraicIntegerSeparation
import Mathlib.NumberTheory.NumberField.CMField

/-!
# The small-integer gap in a CM field

An algebraic integer in a CM field whose complex embeddings all have modulus
less than `√2` is zero or a root of unity. For a nonzero integer `x`, every
embedding of `x * conjugate x - 1` has modulus less than one. The integral norm
forces this difference to vanish, and Kronecker's theorem applies to `x`.

This is Theorem 1.4 of Sano, arXiv:2611.16354, expressed as an exact classification.
-/

noncomputable section

open NumberField NumberField.IsCMField
open scoped BigOperators ComplexConjugate

namespace Bottcher.Arithmetic

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

omit [IsCMField K] in
/-- Every nonzero integral norm prevents all embedding moduli from being below one. -/
private theorem integral_eq_zero_of_embeddings_lt_one (x : 𝓞 K)
    (h : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ < 1) : x = 0 := by
  classical
  by_contra hx
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx
  have hp : (∏ φ : K →+* ℂ, ‖φ (x : K)‖) < 1 := by
    simpa only [Finset.prod_const_one] using
      Finset.prod_lt_prod_of_nonempty
        (fun φ _ => norm_pos_iff.mpr ((map_ne_zero φ).mpr hxK))
        (fun φ _ => h φ) Finset.univ_nonempty
  exact (not_lt_of_ge (GaloisForLFunctions.HTGeometry.one_le_prod_norm_embeddings x hx)) hp

/-- The `√2` bound forces the CM norm to equal one. -/
private theorem small_cm_integer_mul_conj (x : 𝓞 K) (hx : x ≠ 0)
    (h : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ < Real.sqrt 2) :
    x * ringOfIntegersComplexConj K x = 1 := by
  apply sub_eq_zero.mp
  apply integral_eq_zero_of_embeddings_lt_one
  intro φ
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx
  have hn : 0 < ‖φ (x : K)‖ := norm_pos_iff.mpr ((map_ne_zero φ).mpr hxK)
  have hs := h φ
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt0 := Real.sqrt_nonneg (2 : ℝ)
  change ‖φ ((x : K) * complexConj K (x : K) - 1)‖ < 1
  rw [map_sub, map_mul, map_one, complexEmbedding_complexConj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_lt]
  constructor <;> nlinarith only [hn, hs, hsqrt, hsqrt0]

/-- Small CM integers are exactly zero and roots of unity; all conjugate bounds
are part of the classified property, with no additional arithmetic premise. -/
theorem small_cm_integer_iff (x : 𝓞 K) :
    (∀ φ : K →+* ℂ, ‖φ (x : K)‖ < Real.sqrt 2) ↔ x = 0 ∨ IsOfFinOrder x := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      have hm := small_cm_integer_mul_conj x hx h
      have hnorm (φ : K →+* ℂ) : ‖φ (x : K)‖ = 1 := by
        have heq := congrArg (fun z : 𝓞 K => φ (z : K)) hm
        change φ ((x : K) * complexConj K (x : K)) = φ 1 at heq
        rw [map_one, map_mul, complexEmbedding_complexConj, Complex.mul_conj,
          Complex.normSq_eq_norm_sq] at heq
        have hs : ‖φ (x : K)‖ ^ 2 = 1 := by exact_mod_cast heq
        nlinarith only [hs, norm_nonneg (φ (x : K))]
      obtain ⟨n, hn, hpow⟩ :=
        Embeddings.pow_eq_one_of_norm_eq_one K ℂ x.isIntegral_coe hnorm
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, by exact_mod_cast hpow⟩
  · rintro (rfl | hx) φ
    · simp only [map_zero, norm_zero]
      positivity
    · have hh : IsOfFinOrder (φ (x : K)) :=
        (φ.toMonoidHom.comp (algebraMap (𝓞 K) K).toMonoidHom).isOfFinOrder hx
      rw [hh.norm_eq_one]
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

/-- A CM integer outside zero and the roots of unity has an embedding of modulus
at least `√2`. This is an arithmetic gap, independent of the field degree. -/
theorem cm_integer_gap (x : 𝓞 K) :
    (x ≠ 0 ∧ ¬ IsOfFinOrder x) ↔
      ∃ φ : K →+* ℂ, Real.sqrt 2 ≤ ‖φ (x : K)‖ := by
  simpa only [not_forall, not_lt, not_or] using not_congr (small_cm_integer_iff x).symm

end Bottcher.Arithmetic
