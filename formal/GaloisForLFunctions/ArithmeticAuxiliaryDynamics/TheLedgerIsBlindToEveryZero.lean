import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheUncertaintyLawOfAProducer

/-!
# The ledger is blind to every zero

The ledger of a stencil reads `Σ_d Λ(d) g(⌊n/d⌋) = Σ_r g(r) (ψ(n/r) − ψ(n/(r+1)))`. A zero `ρ` of `ζ`
enters `ψ` through the mode `x^ρ/ρ`. Summed over all `r`, the mode contributes
`(n^ρ/ρ) D_c(ρ) ζ(ρ) = 0`: it is annihilated, for every balanced stencil and at every `n`. Only the
truncation at `r ≤ n` survives, and its size is at most `w / β`, uniformly in `n`.

So a single off-line zero of any depth changes every ledger of a stencil by `O(w/β)`, while the main
term is `slope · n`. The exact integer identity at a finite alphabet does not see a one-off zero. A
contradiction needs what the rate law measures: a family of stencils, with `w` and `T` under control.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The mode of a zero read through a ledger up to `r ≤ N`. -/
def ledgerMode (c : ℕ →₀ ℤ) (ρ : ℂ) (n : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ range N, (stepWeight c (j + 1) : ℂ) *
    (((n : ℂ) ^ ρ / ρ) * abelStep ρ j)

/-- **The mode is annihilated.** The complete ledger of the mode of a zero vanishes. -/
theorem hasSum_ledgerMode_eq_zero {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hβ : 0 < ρ.re) (n : ℝ) :
    HasSum (fun j : ℕ => (stepWeight c (j + 1) : ℂ) * (((n : ℂ) ^ ρ / ρ) * abelStep ρ j)) 0 := by
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero hρ
  have h := (hasSum_mellin hc0 hbal hβ hρ1).mul_left ((n : ℂ) ^ ρ / ρ)
  rw [hρ, mul_zero, mul_zero] at h
  have hfun : (fun j : ℕ => (stepWeight c (j + 1) : ℂ) * (((n : ℂ) ^ ρ / ρ) * abelStep ρ j)) =
      fun j : ℕ => ((n : ℂ) ^ ρ / ρ) * ((stepWeight c (j + 1) : ℂ) * abelStep ρ j) := by
    funext j
    ring
  rw [hfun]
  exact h

/-- The real telescoping weight has total mass `1`. -/
theorem hasSum_realStep {σ : ℝ} (hσ : 0 < σ) : HasSum (realStep σ) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (realStep_nonneg hσ.le)]
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact (tendsto_rpow_neg_atTop hσ).comp h1
  have h2 := hlim.const_sub 1
  rw [sub_zero] at h2
  refine h2.congr fun n => ?_
  rw [sum_range_realStep]

/-- The tail of the real telescoping weight. -/
theorem hasSum_realStep_shift {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    HasSum (fun j => realStep σ (j + N)) (((N : ℝ) + 1) ^ (-σ)) := by
  have h := (hasSum_nat_add_iff' N).mpr (hasSum_realStep hσ)
  rw [sum_range_realStep, sub_sub_cancel] at h
  exact h

namespace IsProducer

variable {c : ℕ →₀ ℤ} {m B : ℕ}

/-- **The truncated mode is bounded by the peak.** At a zero of `ζ` with `β > 0`, the mode truncated
at `N` is at most `w n^β (N + 1)^{-β} / β`. -/
theorem norm_ledgerMode_le (hP : IsProducer c m B) {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hβ : 0 < ρ.re) {n : ℝ} (hn : 0 < n) (N : ℕ) :
    ‖ledgerMode c ρ n N‖ ≤ (peak c : ℝ) * n ^ ρ.re * ((N : ℝ) + 1) ^ (-ρ.re) / ρ.re := by
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    simp at hβ
  have hnorm : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hw := hP.peak_pos
  have hsum := hasSum_ledgerMode_eq_zero hP.zero hP.balanced hρ hβ n
  have htail := (hasSum_nat_add_iff' N).mpr hsum
  rw [zero_sub] at htail
  have hbound : HasSum (fun j => (peak c : ℝ) * n ^ ρ.re / ρ.re * realStep ρ.re (j + N))
      ((peak c : ℝ) * n ^ ρ.re / ρ.re * ((N : ℝ) + 1) ^ (-ρ.re)) :=
    (hasSum_realStep_shift hβ N).mul_left _
  have hterm : ∀ j : ℕ, ‖(stepWeight c (j + N + 1) : ℂ) *
      (((n : ℂ) ^ ρ / ρ) * abelStep ρ (j + N))‖ ≤
      (peak c : ℝ) * n ^ ρ.re / ρ.re * realStep ρ.re (j + N) := by
    intro j
    have hg : ‖(stepWeight c (j + N + 1) : ℂ)‖ ≤ (peak c : ℝ) := by
      rw [Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast hP.nonneg _)]
      exact_mod_cast hP.stepWeight_le_peak _
    have hn' : ‖(n : ℂ) ^ ρ‖ = n ^ ρ.re := Complex.norm_cpow_eq_rpow_re_of_pos hn ρ
    have hstep := norm_abelStep_le hβ (j + N)
    have hR := realStep_nonneg hβ.le (j + N)
    have hnp : 0 < n ^ ρ.re := Real.rpow_pos_of_pos hn _
    rw [norm_mul, norm_mul, norm_div, hn']
    calc ‖(stepWeight c (j + N + 1) : ℂ)‖ * (n ^ ρ.re / ‖ρ‖ * ‖abelStep ρ (j + N)‖)
        ≤ (peak c : ℝ) * (n ^ ρ.re / ‖ρ‖ * (‖ρ‖ * (realStep ρ.re (j + N) / ρ.re))) := by
          gcongr
      _ = _ := by field_simp
  have hle := htail.norm_le_of_bounded hbound hterm
  rw [norm_neg] at hle
  calc ‖ledgerMode c ρ n N‖ ≤ _ := hle
    _ = _ := by ring

/-- **A zero moves a ledger by at most `w / β`, at every `n`.** For an integer `n ≥ 1`, the mode of a
zero, truncated at `r ≤ n` as in the ledger, has size at most `w / β`. -/
theorem norm_ledgerMode_self_le (hP : IsProducer c m B) {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hβ : 0 < ρ.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖ledgerMode c ρ (n : ℝ) n‖ ≤ (peak c : ℝ) / ρ.re := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := hP.norm_ledgerMode_le hρ hβ hn0 n
  refine h.trans ?_
  have hw := hP.peak_pos
  have hprod : (n : ℝ) ^ ρ.re * ((n : ℝ) + 1) ^ (-ρ.re) ≤ 1 := by
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, div_le_one (by positivity)]
    exact Real.rpow_le_rpow hn0.le (by linarith) hβ.le
  have hdiv : (peak c : ℝ) * (n : ℝ) ^ ρ.re * ((n : ℝ) + 1) ^ (-ρ.re) / ρ.re =
      (peak c : ℝ) * ((n : ℝ) ^ ρ.re * ((n : ℝ) + 1) ^ (-ρ.re)) / ρ.re := by ring
  rw [hdiv]
  refine div_le_div_of_nonneg_right ?_ hβ.le
  calc _ ≤ (peak c : ℝ) * 1 := mul_le_mul_of_nonneg_left hprod hw.le
    _ = _ := mul_one _

end IsProducer

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
