import GaloisForLFunctions.HTGeometry.GammaMonomialAnalytic
import GaloisForLFunctions.HTGeometry.SignedShiftProductLogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The logarithmic derivative of a gamma monomial

`M(s) = ∏_k Γ(s + λ_k)^{g_k}` satisfies `M' = L·M` with `L(s) = ∑_k g_k ψ(s + λ_k)`, the shifted
digamma sum whose asymptotic expansion the Stirling ladder provides to every order.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

theorem gamma_shift_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z ≠ -(m : ℂ) := by
  intro h
  rw [h] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- The logarithmic derivative of an integer power of `Γ`. -/
theorem logDeriv_Gamma_zpow (n : ℤ) {z : ℂ} (hz : 0 < z.re) :
    logDeriv (fun x : ℂ => Complex.Gamma x ^ n) z = (n : ℂ) * Complex.digamma z := by
  have hne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (fun m => gamma_shift_ne_zero_of_re_pos hz m)
  have hd : DifferentiableAt ℂ Complex.Gamma z :=
    Complex.differentiableAt_Gamma _ (fun m => gamma_shift_ne_zero_of_re_pos hz m)
  have hcomp := logDeriv_comp (f := fun x : ℂ => x ^ n) (g := Complex.Gamma) (x := z)
    (differentiableAt_zpow.mpr (Or.inl hne)) hd
  have hrw : ((fun x : ℂ => x ^ n) ∘ Complex.Gamma) = fun u : ℂ => Complex.Gamma u ^ n := by
    funext u; rfl
  rw [hrw] at hcomp
  rw [hcomp, logDeriv_zpow, Complex.digamma_def, logDeriv_apply]
  field_simp

theorem logDeriv_Gamma_shift_zpow (lam : ℂ) (n : ℤ) {w : ℂ} (h : 0 < (w + lam).re) :
    logDeriv (fun u : ℂ => Complex.Gamma (u + lam) ^ n) w
      = (n : ℂ) * Complex.digamma (w + lam) := by
  have hg : DifferentiableAt ℂ (fun u : ℂ => u + lam) w :=
    (differentiable_id.add_const lam).differentiableAt
  have hne : Complex.Gamma (w + lam) ≠ 0 :=
    Complex.Gamma_ne_zero (fun m => gamma_shift_ne_zero_of_re_pos h m)
  have hΓ : DifferentiableAt ℂ Complex.Gamma (w + lam) :=
    Complex.differentiableAt_Gamma _ (fun m => gamma_shift_ne_zero_of_re_pos h m)
  have hzp : DifferentiableAt ℂ (fun x : ℂ => x ^ n) (Complex.Gamma (w + lam)) :=
    differentiableAt_zpow.mpr (Or.inl hne)
  have hf : DifferentiableAt ℂ (fun x : ℂ => Complex.Gamma x ^ n) ((fun u : ℂ => u + lam) w) := by
    have := hzp.comp (w + lam) hΓ
    have hrw : ((fun x : ℂ => x ^ n) ∘ Complex.Gamma) = fun u : ℂ => Complex.Gamma u ^ n := by
      funext u; rfl
    rwa [hrw] at this
  have hcomp := logDeriv_comp (f := fun x : ℂ => Complex.Gamma x ^ n)
    (g := fun u : ℂ => u + lam) (x := w) hf hg
  have hrw2 : ((fun x : ℂ => Complex.Gamma x ^ n) ∘ (fun u : ℂ => u + lam))
      = fun u : ℂ => Complex.Gamma (u + lam) ^ n := by
    funext u; rfl
  rw [hrw2] at hcomp
  have hd : deriv (fun u : ℂ => u + lam) w = 1 := by
    simp
  rw [hcomp, logDeriv_Gamma_zpow n h, hd, mul_one]

theorem differentiableAt_Gamma_shift_zpow (lam : ℂ) (n : ℤ) {w : ℂ} (h : 0 < (w + lam).re) :
    DifferentiableAt ℂ (fun u : ℂ => Complex.Gamma (u + lam) ^ n) w :=
  (analyticAt_Gamma_shift_zpow (lam := lam) n h).differentiableAt

/-- **`logDeriv M = ∑ g_k ψ(· + λ_k)`.** -/
theorem logDeriv_gammaMonomial {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) {s : ℂ}
    (h : ∀ k, 0 < (s + lam k).re) :
    logDeriv (gammaMonomial lam g) s = ∑ k, (g k : ℂ) * Complex.digamma (s + lam k) := by
  have hne : ∀ k : Fin r, Complex.Gamma (s + lam k) ^ (g k) ≠ 0 := fun k =>
    zpow_ne_zero _ (Complex.Gamma_ne_zero (fun m => gamma_shift_ne_zero_of_re_pos (h k) m))
  have hfun : gammaMonomial lam g = fun u : ℂ => ∏ k, Complex.Gamma (u + lam k) ^ (g k) := by
    funext u; rfl
  rw [hfun]
  rw [logDeriv_prod (s := (Finset.univ : Finset (Fin r)))
    (f := fun k => fun u : ℂ => Complex.Gamma (u + lam k) ^ (g k)) (x := s)
    (fun k _ => hne k)
    (fun k _ => differentiableAt_Gamma_shift_zpow (lam k) (g k) (h k))]
  exact Finset.sum_congr rfl fun k _ => logDeriv_Gamma_shift_zpow (lam k) (g k) (h k)

/-- **`M' = L·M`.** -/
theorem deriv_gammaMonomial {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) {s : ℂ}
    (hs : (∑ j, |(lam j).re|) < s.re) :
    deriv (gammaMonomial lam g) s
      = (∑ k, (g k : ℂ) * Complex.digamma (s + lam k)) * gammaMonomial lam g s := by
  have hre : ∀ k, 0 < (s + lam k).re := fun k => re_pos_of_gt_sum_abs lam hs k
  have hne : gammaMonomial lam g s ≠ 0 := gammaMonomial_ne_zero lam g (fun k => hre k)
  have hlog := logDeriv_gammaMonomial lam g hre
  rw [logDeriv_apply] at hlog
  field_simp at hlog
  linear_combination hlog

end

end GaloisForLFunctions.HTGeometry
