import GaloisForLFunctions.RHTower.SoninFunctionalEquation
import GaloisForLFunctions.RHTower.ArchimedeanPrimeCrossTerm
import GaloisForLFunctions.RHTower.HeatEchoCompleted

/-!
# Burnol's `χ`-factor is Riemann's `χ`

Burnol writes the functional-equation factor as `Γ(1-s)(2π)^{s-1}·2cos(π(s-1)/2)`, while the corpus
carries the completed-zeta form `χ(s) = Γ_ℝ(1-s)/Γ_ℝ(s)`.  They are the same function, by Legendre
duplication at `(1-s)/2` and Euler reflection at `s/2`:

`Γ((1-s)/2)/Γ(s/2) = Γ((1-s)/2)Γ(1-s/2)·sin(πs/2)/π = 2^s√π·Γ(1-s)·sin(πs/2)/π`,

so `π^{s-1/2}·Γ((1-s)/2)/Γ(s/2) = 2^s π^{s-1} sin(πs/2) Γ(1-s)`, which is Burnol's factor once
`cos(π(s-1)/2) = sin(πs/2)` and `(2π)^{s-1} = 2^{s-1}π^{s-1}` are used.

## Main results

* `cos_pi_mul_sub_one_div_two`
* `burnolChiFactor_eq_zetaChi`
-/

noncomputable section

open Complex

namespace RHTower

theorem cos_pi_mul_sub_one_div_two (s : ℂ) :
    Complex.cos ((Real.pi : ℂ) * (s - 1) / 2) = Complex.sin ((Real.pi : ℂ) * (s / 2)) := by
  have hshift : (Real.pi : ℂ) * (s - 1) / 2
      = -((Real.pi : ℂ) / 2 - (Real.pi : ℂ) * (s / 2)) := by ring
  rw [hshift, Complex.cos_neg, Complex.cos_pi_div_two_sub]

theorem gamma_one_sub_half_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    Complex.Gamma (1 - s / 2) ≠ 0 := by
  refine Complex.Gamma_ne_zero (fun m hm => ?_)
  have him : ((1 : ℂ) - s / 2).im = -(s.im / 2) := by simp
  have h0 : ((1 : ℂ) - s / 2).im = 0 := by rw [hm]; simp
  rw [him] at h0
  exact hs (by linarith)

theorem gamma_half_ne_zero_of_im_ne {s : ℂ} (hs : s.im ≠ 0) : Complex.Gamma (s / 2) ≠ 0 := by
  refine Complex.Gamma_ne_zero (fun m hm => ?_)
  have him : (s / 2).im = s.im / 2 := by simp
  have h0 : (s / 2).im = 0 := by rw [hm]; simp
  rw [him] at h0
  exact hs (by linarith)

/-- **Burnol's `χ`-factor is Riemann's `χ`.** -/
theorem burnolChiFactor_eq_zetaChi {s : ℂ} (hs : s.im ≠ 0) :
    burnolChiFactor s = zetaChi s := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hGne : Complex.Gamma (s / 2) ≠ 0 := gamma_half_ne_zero_of_im_ne hs
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (s / 2)
  have hdup := gamma_duplication_one_sub (s := s)
  -- the Gamma quotient
  have hkey : Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2)
      = (Complex.Gamma (1 - s) * (2 : ℂ) ^ s * ((Real.sqrt Real.pi : ℝ) : ℂ))
        * Complex.sin ((Real.pi : ℂ) * (s / 2)) / ((Real.pi : ℝ) : ℂ) := by
    rw [← hdup, div_eq_div_iff hGne hpi]
    have hsinne : Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 := by
      rw [Complex.sin_ne_zero_iff]
      intro k hk
      have h0 : ((Real.pi : ℂ) * (s / 2)).im = 0 := by rw [hk]; simp
      have him : ((Real.pi : ℂ) * (s / 2)).im = Real.pi * (s.im / 2) := by
        simp [Complex.mul_im]
      rw [him] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact Real.pi_ne_zero h
      · exact hs (by linarith)
    have hsinne' : Complex.sin ((Real.pi : ℂ) * s / 2) ≠ 0 := by
      rw [mul_div_assoc]
      exact hsinne
    have hmul : Complex.Gamma (s / 2) * Complex.Gamma (1 - s / 2)
        * Complex.sin ((Real.pi : ℂ) * (s / 2)) = ((Real.pi : ℝ) : ℂ) := by
      rw [hrefl]
      field_simp
    calc Complex.Gamma ((1 - s) / 2) * ((Real.pi : ℝ) : ℂ)
        = Complex.Gamma ((1 - s) / 2) * (Complex.Gamma (s / 2) * Complex.Gamma (1 - s / 2)
            * Complex.sin ((Real.pi : ℂ) * (s / 2))) := by rw [hmul]
      _ = Complex.Gamma ((1 - s) / 2) * Complex.Gamma (1 - s / 2)
            * Complex.sin ((Real.pi : ℂ) * (s / 2)) * Complex.Gamma (s / 2) := by ring
  -- the two powers
  have hsqrt : ((Real.sqrt Real.pi : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
  have htwo : (((2 * Real.pi : ℝ)) : ℂ) ^ (s - 1)
      = ((2 : ℝ) : ℂ) ^ (s - 1) * ((Real.pi : ℝ) : ℂ) ^ (s - 1) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
  have hzeta : zetaChi s = ((Real.pi : ℝ) : ℂ) ^ (s - 1 / 2)
      * ((Complex.Gamma (1 - s) * (2 : ℂ) ^ s * ((Real.sqrt Real.pi : ℝ) : ℂ))
        * Complex.sin ((Real.pi : ℂ) * (s / 2)) / ((Real.pi : ℝ) : ℂ)) := by
    rw [zetaChi_eq_pi_cpow_mul_gamma_ratio, mul_div_assoc, hkey]
  rw [burnolChiFactor, hzeta, cos_pi_mul_sub_one_div_two, htwo, hsqrt]
  -- pure power algebra
  have h2 : ((2 : ℝ) : ℂ) ^ (s - 1) * 2 = ((2 : ℝ) : ℂ) ^ s := by
    have h2ne : ((2 : ℝ) : ℂ) ≠ 0 := by norm_num
    rw [Complex.cpow_sub _ _ h2ne, Complex.cpow_one]
    field_simp
    norm_num
  have h2cast : ((2 : ℝ) : ℂ) ^ s = (2 : ℂ) ^ s := by norm_num
  have hpow1 : ((Real.pi : ℝ) : ℂ) ^ (s - 1 / 2) * ((Real.pi : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
      = ((Real.pi : ℝ) : ℂ) ^ s := by
    rw [← Complex.cpow_add _ _ hpi]
    congr 1
    push_cast
    ring
  have hpow2 : ((Real.pi : ℝ) : ℂ) ^ (s - 1) * ((Real.pi : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) ^ s := by
    rw [Complex.cpow_sub _ _ hpi, Complex.cpow_one]
    field_simp
  set X : ℂ := Complex.Gamma (1 - s) * ((2 : ℝ) : ℂ) ^ (s - 1) * 2
    * Complex.sin ((Real.pi : ℂ) * (s / 2)) with hXdef
  have hXs : Complex.Gamma (1 - s) * (2 : ℂ) ^ s * Complex.sin ((Real.pi : ℂ) * (s / 2)) = X := by
    rw [hXdef, ← h2cast, ← h2]
    ring
  have hL : Complex.Gamma (1 - s) * (((2 : ℝ) : ℂ) ^ (s - 1) * ((Real.pi : ℝ) : ℂ) ^ (s - 1))
      * (2 * Complex.sin ((Real.pi : ℂ) * (s / 2))) = X * ((Real.pi : ℝ) : ℂ) ^ (s - 1) := by
    rw [hXdef]
    ring
  have hR : ((Real.pi : ℝ) : ℂ) ^ (s - 1 / 2)
      * (Complex.Gamma (1 - s) * (2 : ℂ) ^ s * ((Real.pi : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
        * Complex.sin ((Real.pi : ℂ) * (s / 2)) / ((Real.pi : ℝ) : ℂ))
      = X * ((Real.pi : ℝ) : ℂ) ^ (s - 1) := by
    calc ((Real.pi : ℝ) : ℂ) ^ (s - 1 / 2)
          * (Complex.Gamma (1 - s) * (2 : ℂ) ^ s * ((Real.pi : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
            * Complex.sin ((Real.pi : ℂ) * (s / 2)) / ((Real.pi : ℝ) : ℂ))
        = (Complex.Gamma (1 - s) * (2 : ℂ) ^ s * Complex.sin ((Real.pi : ℂ) * (s / 2)))
          * (((Real.pi : ℝ) : ℂ) ^ (s - 1 / 2) * ((Real.pi : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
            / ((Real.pi : ℝ) : ℂ)) := by ring
      _ = X * (((Real.pi : ℝ) : ℂ) ^ s / ((Real.pi : ℝ) : ℂ)) := by rw [hXs, hpow1]
      _ = X * ((Real.pi : ℝ) : ℂ) ^ (s - 1) := by
          rw [← hpow2]
          field_simp
  rw [hL, hR]

end RHTower

end
