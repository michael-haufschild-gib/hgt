import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGaussianStripRegularization
import Mathlib.Analysis.PSeries

/-! # A common summable majorant for Gaussian contour blocks

The existing entire-source Gaussian regularization supplies every polynomial
weight. The same summable sequence then controls all fixed source gauges,
with a gauge-dependent finite initial exception.
-/

open Complex Set Filter Topology

namespace RHTower
noncomputable section

theorem deningerGaussianLinear_weighted_bound {ε : ℝ} (hε : 0 < ε)
    (B : ℝ) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      (1+t^2)^K * Real.exp (B*t-ε*t^2) ≤ C := by
  let F : ℂ → ℂ := fun s => Complex.exp (-I*(B : ℂ)*s)
  have hF : Differentiable ℂ F := by dsimp [F]; fun_prop
  have hV : DeningerVerticalExponential F := by
    intro a b
    refine ⟨1, |B|, zero_le_one, abs_nonneg _, fun s _ _ => ?_⟩
    change ‖Complex.exp (-I*(B : ℂ)*s)‖ ≤ _
    rw [Complex.norm_exp, one_mul]
    have he : (-I*(B : ℂ)*s).re = B*s.im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [he]
    apply Real.exp_le_exp.mpr
    calc B*s.im ≤ |B*s.im| := le_abs_self _
      _ = |B| * |s.im| := abs_mul _ _
  have hreg := deningerGaussianMellinRegularization_entireRegular hF hV hε
  obtain ⟨C, hC⟩ := (hreg (-1) 1).decay 0 0 (by norm_num) (by norm_num) K
  refine ⟨|C|, abs_nonneg _, fun t => ?_⟩
  have he : ‖deningerGaussianMellinRegularization ε F ((t : ℂ)*I)‖ =
      Real.exp (B*t-ε*t^2) := by
    rw [deningerGaussianMellinRegularization, norm_mul, Complex.norm_exp]
    change Real.exp _ * ‖Complex.exp (-I*(B : ℂ)*((t : ℂ)*I))‖ = _
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  have h := hC ((t : ℂ)*I) (by simp) (by simp)
  rw [he] at h
  have h' : Real.exp (B*t-ε*t^2) ≤ C/(1+t^2)^K := by simpa using h
  have hw := (le_div_iff₀ (by positivity : 0 < (1+t^2)^K)).mp h'
  simpa only [mul_comm] using hw.trans (le_abs_self _)

def deningerMeyerContourMajorant (n : ℕ) : ℝ := 1/((n : ℝ)+1)^2

theorem deningerMeyerContourMajorant_summable : Summable deningerMeyerContourMajorant := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  change Summable (fun n : ℕ => 1/((n : ℝ)+1)^2)
  simpa only [Nat.cast_add, Nat.cast_one] using! h

/-- Every fixed polynomial contour cost is eventually paid by one common
summable majorant along any heights lying above their index. -/
theorem deningerGaussianContourMass_eventually {ε : ℝ} (hε : 0 < ε)
    (B A : ℝ) (hA : 0 ≤ A) (M K : ℕ) (t : ℕ → ℝ)
    (ht : ∀ n : ℕ, (n : ℝ) ≤ t n) :
    ∀ᶠ n in atTop,
      A*(t n+5)^M*(1+(t n+6)^2)^K*Real.exp (B*t n-ε*(t n)^2) ≤
        deningerMeyerContourMajorant n := by
  obtain ⟨D, hD, hbound⟩ := deningerGaussianLinear_weighted_bound hε B (M+K+2)
  let E := A*6^M*74^K*D
  have hE : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (2*E))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have ht₀ : 0 ≤ t n := (Nat.cast_nonneg n).trans (ht n)
  have ht₁ : 1 ≤ t n := by linarith [le_max_left 1 (2*E), ht n]
  let L := 1+(t n)^2
  let v := A*(t n+5)^M*(1+(t n+6)^2)^K*Real.exp (B*t n-ε*(t n)^2)
  have hL : 0 < L := by dsimp [L]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hP : t n+5 ≤ 6*L := by
    dsimp [L]
    nlinarith [sq_nonneg (t n-1)]
  have hQ : 1+(t n+6)^2 ≤ 74*L := by
    dsimp [L]
    nlinarith [sq_nonneg (t n-6), sq_nonneg (t n)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ t n+5) hP M
  have hq := pow_le_pow_left₀ (by positivity : 0 ≤ 1+(t n+6)^2) hQ K
  rw [mul_pow] at hp hq
  have hvL : v*L^2 ≤ E := by
    calc
      v*L^2 ≤ (A*(6^M*L^M)*(74^K*L^K)*Real.exp (B*t n-ε*(t n)^2))*L^2 := by
        dsimp [v]
        gcongr
      _ = (A*6^M*74^K)*(L^(M+K+2)*Real.exp (B*t n-ε*(t n)^2)) := by
        simp only [pow_add]
        ring
      _ ≤ (A*6^M*74^K)*D := mul_le_mul_of_nonneg_left (hbound (t n)) (by positivity)
      _ = E := rfl
  have hEL : 2*E ≤ L := by
    dsimp [L]
    have hEt : 2*E ≤ t n := by linarith [le_max_right 1 (2*E), ht n]
    nlinarith
  have hsmall : v*(2*L) ≤ 1 := by
    apply (mul_le_mul_iff_left₀ hL).mp
    nlinarith [hvL, hEL]
  have hnL : ((n : ℝ)+1)^2 ≤ 2*L := by
    dsimp [L]
    have hn₀ := Nat.cast_nonneg (α := ℝ) n
    have hnt := ht n
    nlinarith [sq_nonneg (t n-1)]
  change v ≤ 1/((n : ℝ)+1)^2
  apply (le_div_iff₀ (by positivity : 0 < ((n : ℝ)+1)^2)).mpr
  exact (mul_le_mul_of_nonneg_left hnL hv).trans hsmall

end
end RHTower
