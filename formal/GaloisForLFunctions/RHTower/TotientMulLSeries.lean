import GaloisForLFunctions.RHTower.TotientMulMoebius
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

open ArithmeticFunction Complex LSeries
open scoped ArithmeticFunction.Moebius LSeries.notation

/-!
# The Dirichlet series of `φ(Mn)`

`L(n ↦ n, w) = ζ(w - 1)` (`LSeries_id_eq`), `H_M = (μχ_M) ⍟ id` (`H_eq_conv`), so for `M ≥ 1` and `Re w > 2`
`Σ_n φ(Mn) n^{-w} = φ(M) L(μχ_M, w) ζ(w - 1)` (`LSeries_totient_mul`), where `L(μχ_M, w)` converges absolutely on
`Re w > 1` (`summable_muChi`). With `M = N²` this is the Dirichlet series of the constant term of the `Γ(N)`
Eisenstein series; its only pole on `Re w > 1` comes from `ζ(w - 1)` at `w = 2`.
-/

namespace GaloisForLFunctions.RHTower.TotientMulLSeries
open GaloisForLFunctions.RHTower.TotientMulMoebius

theorem term_id_eq (w : ℂ) (n : ℕ) : LSeries.term (fun n : ℕ => (n : ℂ)) w n = LSeries.term 1 (w - 1) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', Pi.one_apply, cpow_sub _ _ hn0, cpow_one]
    field_simp

theorem LSeries_id_eq {w : ℂ} (hw : 2 < w.re) : LSeries (fun n : ℕ => (n : ℂ)) w = riemannZeta (w - 1) := by
  rw [← LSeries_zeta_eq_riemannZeta (by simp; linarith), LSeries_zeta_eq]
  unfold LSeries
  exact tsum_congr (term_id_eq w)

theorem summable_id {w : ℂ} (hw : 2 < w.re) : LSeriesSummable (fun n : ℕ => (n : ℂ)) w := by
  have h : LSeriesSummable 1 (w - 1) := LSeriesSummable_one_iff.mpr (by simp; linarith)
  unfold LSeriesSummable at h ⊢
  exact h.congr (fun n => (term_id_eq w n).symm)

/-- The Möbius series restricted to integers coprime to `M`. -/
noncomputable def muChi (M : ℕ) : ℕ → ℂ := fun n => (((μ : ArithmeticFunction ℤ).pmul (chi M) n : ℤ) : ℂ)

theorem norm_muChi_le (M n : ℕ) : ‖muChi M n‖ ≤ 1 := by
  unfold muChi
  rw [ArithmeticFunction.pmul_apply, Complex.norm_intCast]
  simp only [chi, ArithmeticFunction.coe_mk]
  split_ifs
  · rw [mul_one]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp

theorem summable_muChi (M : ℕ) {w : ℂ} (hw : 1 < w.re) : LSeriesSummable (muChi M) w :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) hw ⟨1, fun n _ => by
    rw [sub_self, Real.rpow_zero, mul_one]; exact norm_muChi_le M n⟩

theorem H_eq_conv (M n : ℕ) : (H M n : ℂ) = (muChi M ⍟ fun n : ℕ => (n : ℂ)) n := by
  rw [LSeries.convolution_def, ← Hf_eq]
  unfold Hf
  rw [ArithmeticFunction.mul_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro p _
  simp [muChi]

/-- **`L(H_M, w) = L(μχ_M, w) · ζ(w - 1)`** for `Re w > 2`. -/
theorem LSeries_H (M : ℕ) {w : ℂ} (hw : 2 < w.re) :
    LSeries (fun n => (H M n : ℂ)) w = LSeries (muChi M) w * riemannZeta (w - 1) := by
  have e : (fun n => (H M n : ℂ)) = (muChi M ⍟ fun n : ℕ => (n : ℂ)) := funext (H_eq_conv M)
  rw [e, LSeries_convolution' (summable_muChi M (by linarith)) (summable_id hw), LSeries_id_eq hw]

/-- **`Σ_n φ(Mn) n^{-w} = φ(M) · L(μχ_M, w) · ζ(w - 1)`** for `M ≥ 1`, `Re w > 2`. -/
theorem LSeries_totient_mul (M : ℕ) (hM : 0 < M) {w : ℂ} (hw : 2 < w.re) :
    LSeries (fun n => ((M * n).totient : ℂ)) w = M.totient * (LSeries (muChi M) w * riemannZeta (w - 1)) := by
  rw [← LSeries_H M hw]
  have e : (fun n => ((M * n).totient : ℂ)) = fun n => (M.totient : ℂ) * (H M n : ℂ) := by
    funext n
    have := totient_mul_eq M hM n
    exact_mod_cast this
  rw [e]
  unfold LSeries
  rw [← tsum_mul_left]
  apply tsum_congr; intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']; ring

end GaloisForLFunctions.RHTower.TotientMulLSeries
