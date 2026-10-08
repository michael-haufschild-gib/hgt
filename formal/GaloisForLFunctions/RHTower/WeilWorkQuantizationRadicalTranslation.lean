import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Perfect

/-!
# Positive radical translation rigidity

A positive real number whose power and whose translated power are rational
is itself rational. Conjugates lie on two tangent circles and hence coincide.
This classical bridge is used by the actual phase-period argument.
-/

open Polynomial Complex
namespace RHTower.WeilSpectral

theorem quantization_radical_translate_rational {x : ℝ} (hx : 0 < x)
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) {q s : ℚ}
    (hq : x ^ N = q) (hs : (x + 1) ^ M = s) :
    ∃ a : ℚ, (a : ℝ) = x := by
  have hqC : (x : ℂ) ^ N = q := by exact_mod_cast hq
  have hsC : ((x : ℂ) + 1) ^ M = s := by exact_mod_cast hs
  have hxi : IsIntegral ℚ (x : ℂ) := IsIntegral.of_pow hN (by
    rw [hqC]
    exact isIntegral_algebraMap)
  have hsep : IsSeparable ℚ (x : ℂ) := (minpoly.irreducible hxi).separable
  by_contra hrat
  have hn : (x : ℂ) ∉ (⊥ : Subalgebra ℚ ℂ) := by
    rintro ⟨a, ha⟩
    apply hrat ⟨a, ?_⟩
    change (a : ℂ) = (x : ℂ) at ha
    exact_mod_cast ha
  obtain ⟨z, hne, hz⟩ :=
    (notMem_iff_exists_ne_and_isConjRoot hsep (IsAlgClosed.splits _)).mp hn
  have transfer {u v : ℂ} (h : IsConjRoot ℚ u v) (n : ℕ) (a : ℚ)
      (hu : u ^ n = a) : v ^ n = a := by
    have hd : minpoly ℚ u ∣ (X ^ n - C a : ℚ[X]) :=
      minpoly.dvd ℚ u (by simp [hu])
    rw [show minpoly ℚ u = minpoly ℚ v from h] at hd
    simpa [sub_eq_zero] using (minpoly.dvd_iff.mp hd)
  have hzN := transfer hz N q hqC
  have hzM : (z + 1) ^ M = (s : ℂ) := by
    simpa using transfer (hz.add_algebraMap 1) M s (by simpa using hsC)
  have hnz : ‖z‖ = x := by
    apply (pow_left_inj₀ (norm_nonneg z) hx.le hN.ne').mp
    have he := congrArg norm (hzN.trans hqC.symm)
    simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] using he
  have hnz1 : ‖z + 1‖ = x + 1 := by
    apply (pow_left_inj₀ (norm_nonneg (z + 1)) (by linarith) hM.ne').mp
    have he := congrArg norm (hzM.trans hsC.symm)
    rw [norm_pow, norm_pow] at he
    have hr : ((x : ℂ) + 1) = ((x + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at he
    exact he
  have he₀ := Complex.normSq_eq_norm_sq z
  have he₁ := Complex.normSq_eq_norm_sq (z + 1)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, add_zero, hnz, hnz1] at he₀ he₁
  have hzre : z.re = x := by nlinarith
  have hzim : z.im = 0 := by nlinarith [sq_nonneg z.im]
  apply hne
  apply Complex.ext
  · exact hzre.symm
  · exact hzim.symm

end RHTower.WeilSpectral
