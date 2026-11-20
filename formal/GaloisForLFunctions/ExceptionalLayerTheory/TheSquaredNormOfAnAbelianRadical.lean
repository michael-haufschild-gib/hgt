import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic

/-!
# Radicals in abelian extensions of the rationals

All conjugates of an n-th root of a rational have the same complex norm.
In an abelian extension, complex conjugation commutes with every
automorphism, so the squared norm is rational. For an odd exponent, this
recovers an n-th root in the rationals themselves.
-/
noncomputable section
open scoped IsMulCommutative
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The squared complex norm of a radical in an abelian extension is
rational. Its n-th power is the square of the rational radicand. -/
theorem rational_squared_norm_of_abelian_radical {K : Type*} [Field K] [CharZero K]
    [IsAbelianGalois ℚ K] (e : K →ₐ[ℚ] ℂ) {n : ℕ} (hn : 0<n) (x : K) (a : ℚ)
    (hx : x^n=(a:K)) : ∃ b : ℚ, (b:ℝ)=‖e x‖^2 ∧ b^n=a^2 := by
  letI : Algebra K ℂ := e.toRingHom.toAlgebra
  let C := (Complex.conjAe.restrictScalars ℚ).restrictNormal K
  have hc (y : K) : e (C y)=(starRingEnd ℂ) (e y) :=
    AlgEquiv.restrictNormal_commutes (Complex.conjAe.restrictScalars ℚ) K y
  have he (σ : K ≃ₐ[ℚ] K) : ‖e (σ x)‖=‖e x‖ := by
    apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hn.ne').mp
    simp only [←norm_pow,←map_pow,hx,map_ratCast]
  have hfix (σ : K ≃ₐ[ℚ] K) : σ (x*C x)=x*C x := by
    have hσ : σ (C x)=C (σ x) := DFunLike.congr_fun (mul_comm σ C) x
    apply e.injective
    change e (σ (x * C x)) = e (x * C x)
    rw [map_mul σ,hσ,map_mul e,map_mul e,hc,hc,Complex.mul_conj,Complex.mul_conj,
      Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,he]
  obtain ⟨b,hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (x*C x)).mpr hfix
  have hnorm := congrArg e hb
  change e (b:K)=e (x*C x) at hnorm
  rw [map_ratCast,map_mul,hc,Complex.mul_conj,Complex.normSq_eq_norm_sq] at hnorm
  have hbR : (b:ℝ)=‖e x‖^2 := by exact_mod_cast hnorm
  refine ⟨b,hbR,?_⟩
  have habs : ‖e x‖^n=|(a:ℝ)| := by
    rw [←norm_pow,←map_pow,hx,map_ratCast]
    exact Complex.norm_ratCast a
  have hh : (b:ℝ)^n=(a:ℝ)^2 := by
    rw [hbR,←pow_mul,Nat.mul_comm, pow_mul,habs,sq_abs]
  exact_mod_cast hh

/-- If a square is an odd power, its unsquared element is an odd
power over the same field. The exponent identity is 2k+1−2k=1. -/
theorem root_of_odd_power_square {K : Type*} [Field K] {n : ℕ} (hn : Odd n)
    {a b : K} (hb : b^n=a^2) : ∃ q : K, q^n=a := by
  obtain ⟨k,hk⟩ := hn
  have hn0 : 0<n := by omega
  by_cases ha : a=0
  · exact ⟨0,by rw [ha,zero_pow hn0.ne']⟩
  have hb0 : b≠0 := by
    intro h; rw [h,zero_pow hn0.ne'] at hb
    exact pow_ne_zero 2 ha hb.symm
  refine ⟨a/b^k,?_⟩
  have hden : (b^k)^n=(a^2)^k := by rw [←pow_mul,Nat.mul_comm,pow_mul,hb]
  have hnum : a^n=a*(a^2)^k := by rw [hk,pow_succ,pow_mul,mul_comm]
  rw [div_pow,hden,hnum,mul_div_cancel_right₀ _ (pow_ne_zero _ (pow_ne_zero _ ha))]

/-- An odd root of a rational appearing in an abelian extension exists
already over the rationals, even when the degree shares factors with n. -/
theorem odd_radical_descends_from_abelian_field {K : Type*} [Field K] [CharZero K]
    [IsAbelianGalois ℚ K] (e : K →ₐ[ℚ] ℂ) {n : ℕ} (hn : Odd n) (a : ℚ) :
    (∃ x : K, x^n=(a:K)) ↔ ∃ q : ℚ, q^n=a := by
  constructor
  · rintro ⟨x,hx⟩
    have hn0 : 0<n := by obtain ⟨k,hk⟩ := hn; omega
    obtain ⟨b,_,hb⟩ := rational_squared_norm_of_abelian_radical e hn0 x a hx
    exact root_of_odd_power_square hn hb
  · rintro ⟨q,hq⟩
    exact ⟨q,by exact_mod_cast hq⟩

#print axioms rational_squared_norm_of_abelian_radical
#print axioms odd_radical_descends_from_abelian_field
end GaloisForLFunctions.ExceptionalLayerTheory
