import GaloisForLFunctions.RHTower.DeningerCriticalFloquetVonMangoldtWall

/-!
# The universal diagonal sign wall

A source supported in an interval of diameter less than `log 3 - log 2` produces two-bump witnesses
one `log 2`-period apart whose supports still fit inside every circle of circumference at least
`log 3`.  Consequently every prime circle other than `2` contributes nothing to the renormalized
diagonal form, while the circle of `2` contributes `+‖u₊‖²` for the coherent bump and `-‖u₋‖²` for
the anti-coherent one.  So for every nonnegative prime weighting that sees the prime `2`, the
renormalized diagonal form takes both signs.

* `deningerFloquetTwoBump_support` : the two-bump support.
* `deningerFloquetDiagonalDefect_two` : **the circle of `2` gives `±` the mass.**
* `deningerFloquetDiagonalDefect_of_three_le` : **every larger prime circle gives zero.**
* `deningerFloquetTwoBumpMinus_eq_floquetDefect` : **the negative witness is a Floquet Euler
  coboundary.**
-/

namespace RHTower

open Complex MeasureTheory Set

noncomputable section

/-! ## Support and mass of the two-bump witnesses -/

theorem deningerMeyerStrongLogTranslate_support {L : ℝ} (hL : 0 ≤ L)
    (v : DeningerMeyerStrongLogTarget) {a b : ℝ}
    (hsupport : Function.support (v : ℝ → ℂ) ⊆ Icc a b) :
    Function.support ((deningerMeyerStrongLogTranslate L v :
      DeningerMeyerStrongLogTarget) : ℝ → ℂ) ⊆ Icc (a - L) b := by
  intro x hx
  rw [Function.mem_support, deningerMeyerStrongLogTranslate_apply] at hx
  have hmem := hsupport hx
  exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

theorem deningerFloquetTwoBump_support {L : ℝ} (hL : 0 ≤ L)
    (v : DeningerMeyerStrongLogTarget) {a b : ℝ}
    (hsupport : Function.support (v : ℝ → ℂ) ⊆ Icc a b) :
    Function.support ((deningerFloquetTwoBumpPlus L v :
        DeningerMeyerStrongLogTarget) : ℝ → ℂ) ⊆ Icc (a - L) b
      ∧ Function.support ((deningerFloquetTwoBumpMinus L v :
        DeningerMeyerStrongLogTarget) : ℝ → ℂ) ⊆ Icc (a - L) b := by
  have hbase : Icc a b ⊆ Icc (a - L) b := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have htr := deningerMeyerStrongLogTranslate_support hL v hsupport
  constructor
  · intro x hx
    rw [Function.mem_support, deningerFloquetTwoBumpPlus_apply] at hx
    by_cases h0 : (v : ℝ → ℂ) x = 0
    · have hne : (v : ℝ → ℂ) (x + L) ≠ 0 := by
        intro h
        exact hx (by rw [h0, h, add_zero])
      exact htr (by rw [Function.mem_support, deningerMeyerStrongLogTranslate_apply]; exact hne)
    · exact hbase (hsupport h0)
  · intro x hx
    rw [Function.mem_support, deningerFloquetTwoBumpMinus_apply] at hx
    by_cases h0 : (v : ℝ → ℂ) x = 0
    · have hne : (v : ℝ → ℂ) (x + L) ≠ 0 := by
        intro h
        exact hx (by rw [h0, h, sub_zero])
      exact htr (by rw [Function.mem_support, deningerMeyerStrongLogTranslate_apply]; exact hne)
    · exact hbase (hsupport h0)

/-! ## The circle of two -/

/-- **The circle of `2` gives `±` the two-bump mass.**  This is the same-prime part of `(14)`. -/
theorem deningerFloquetDiagonalDefect_two (v : DeningerMeyerStrongLogTarget) {a b : ℝ}
    (hsupport : Function.support (v : ℝ → ℂ) ⊆ Icc a b) (hshort : b - a < Real.log 2) :
    (deningerPrimeCircleEnergy (Real.log 2) (deningerFloquetTwoBumpPlus (Real.log 2) v)
        - deningerMeyerStrongLogAutocorrelation (deningerFloquetTwoBumpPlus (Real.log 2) v) 0
      = deningerMeyerStrongLogAutocorrelation (deningerFloquetTwoBumpPlus (Real.log 2) v) 0)
    ∧ (deningerPrimeCircleEnergy (Real.log 2) (deningerFloquetTwoBumpMinus (Real.log 2) v)
        - deningerMeyerStrongLogAutocorrelation (deningerFloquetTwoBumpMinus (Real.log 2) v) 0
      = -deningerMeyerStrongLogAutocorrelation
          (deningerFloquetTwoBumpMinus (Real.log 2) v) 0) := by
  have hLpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hbase := deningerPrimeCircleEnergy_eq_autocorrelation_zero_of_short_support v hLpos
    hsupport hshort
  obtain ⟨hplus, hminus⟩ := deningerMeyerStrongLogAutocorrelation_twoBump_zero hLpos v hsupport
    hshort
  constructor
  · rw [deningerPrimeCircleEnergy_twoBumpPlus hLpos v, hbase, hplus]
    ring
  · rw [deningerPrimeCircleEnergy_twoBumpMinus hLpos v, hminus]
    ring

/-! ## Every larger prime circle -/

/-- **Every prime circle of circumference at least `log 3` gives zero defect.** -/
theorem deningerFloquetDiagonalDefect_of_three_le (v : DeningerMeyerStrongLogTarget) {a b : ℝ}
    (hsupport : Function.support (v : ℝ → ℂ) ⊆ Icc a b)
    (hshort : b - a < Real.log 3 - Real.log 2) {L : ℝ} (hL : Real.log 3 ≤ L) :
    deningerPrimeCircleEnergy L (deningerFloquetTwoBumpPlus (Real.log 2) v)
        = deningerMeyerStrongLogAutocorrelation (deningerFloquetTwoBumpPlus (Real.log 2) v) 0
      ∧ deningerPrimeCircleEnergy L (deningerFloquetTwoBumpMinus (Real.log 2) v)
        = deningerMeyerStrongLogAutocorrelation
            (deningerFloquetTwoBumpMinus (Real.log 2) v) 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog3 : Real.log 2 < Real.log 3 := Real.log_lt_log two_pos (by norm_num)
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith) hL
  obtain ⟨hsp, hsm⟩ := deningerFloquetTwoBump_support hlog2.le v hsupport
  have hdiam : b - (a - Real.log 2) < L := by
    have : b - a + Real.log 2 < Real.log 3 := by linarith
    linarith
  exact ⟨deningerPrimeCircleEnergy_eq_autocorrelation_zero_of_short_support _ hLpos hsp hdiam,
    deningerPrimeCircleEnergy_eq_autocorrelation_zero_of_short_support _ hLpos hsm hdiam⟩

/-! ## Positivity of the two-bump mass -/

/-- The zero-lag autocorrelation is the real energy. -/
theorem deningerMeyerStrongLogAutocorrelation_zero_re (v : DeningerMeyerStrongLogTarget) :
    (deningerMeyerStrongLogAutocorrelation v 0).re = ∫ x : ℝ, ‖(v : ℝ → ℂ) x‖ ^ 2 := by
  rw [deningerMeyerStrongLogAutocorrelation]
  have hfun : (fun x : ℝ => (v : ℝ → ℂ) x * (starRingEnd ℂ) ((v : ℝ → ℂ) (x + 0)))
      = fun x : ℝ => ((‖(v : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [add_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hfun, integral_complex_ofReal, Complex.ofReal_re]

/-- **A nonzero source has positive zero-lag mass.** -/
theorem deningerMeyerStrongLogAutocorrelation_zero_re_pos {v : DeningerMeyerStrongLogTarget}
    (hv : (v : ℝ → ℂ) ≠ 0) : 0 < (deningerMeyerStrongLogAutocorrelation v 0).re := by
  have hint := integrable_deningerMeyerStrongLogAutocorrelationIntegrand v 0
  have hintSq : Integrable (fun x : ℝ => ‖(v : ℝ → ℂ) x‖ ^ 2) := by
    have hre := hint.re
    have hfun : (fun x : ℝ =>
        RCLike.re ((v : ℝ → ℂ) x * (starRingEnd ℂ) ((v : ℝ → ℂ) (x + 0))))
        = fun x : ℝ => ‖(v : ℝ → ℂ) x‖ ^ 2 := by
      funext x
      rw [add_zero, Complex.mul_conj]
      simp [Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]
    rwa [hfun] at hre
  rw [deningerMeyerStrongLogAutocorrelation_zero_re]
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hv
  have hcont : Continuous fun x : ℝ => ‖(v : ℝ → ℂ) x‖ ^ 2 :=
    ((v.2.smooth.continuous).norm.pow 2)
  have hpos : 0 < ‖(v : ℝ → ℂ) x₀‖ ^ 2 := by
    have : 0 < ‖(v : ℝ → ℂ) x₀‖ := norm_pos_iff.2 (by simpa using hx₀)
    positivity
  rw [integral_pos_iff_support_of_nonneg (fun x => by positivity) hintSq]
  have hUopen : IsOpen ((fun x : ℝ => ‖(v : ℝ → ℂ) x‖ ^ 2) ⁻¹' Ioi 0) :=
    hcont.isOpen_preimage _ isOpen_Ioi
  have hUne : ((fun x : ℝ => ‖(v : ℝ → ℂ) x‖ ^ 2) ⁻¹' Ioi 0).Nonempty := ⟨x₀, hpos⟩
  have hUsub : (fun x : ℝ => ‖(v : ℝ → ℂ) x‖ ^ 2) ⁻¹' Ioi 0
      ⊆ Function.support fun x : ℝ => ‖(v : ℝ → ℂ) x‖ ^ 2 := fun x hx => ne_of_gt hx
  exact lt_of_lt_of_le (hUopen.measure_pos volume hUne) (measure_mono hUsub)

/-! ## The negative witness is a Floquet Euler coboundary -/

/-- **`(15)`: the anti-coherent witness is the half-density Floquet Euler coboundary.**  Applying
the twisted defect `1 - 2^{1/2}τ_{log 2}` to the half-density profile of `v` returns the
half-density profile of the anti-coherent two-bump. -/
theorem deningerFloquetTwoBumpMinus_eq_floquetDefect (v : DeningerMeyerStrongLogTarget) (t : ℝ) :
    ((Real.exp (-(t / 2)) : ℝ) : ℂ)
        * (deningerFloquetTwoBumpMinus (Real.log 2) v : ℝ → ℂ) t
      = ((Real.exp (-(t / 2)) : ℝ) : ℂ) * (v : ℝ → ℂ) t
        - ((Real.exp (Real.log 2 / 2) : ℝ) : ℂ)
          * (((Real.exp (-((t + Real.log 2) / 2)) : ℝ) : ℂ) * (v : ℝ → ℂ) (t + Real.log 2)) := by
  rw [deningerFloquetTwoBumpMinus_apply]
  have hkR : Real.exp (Real.log 2 / 2) * Real.exp (-((t + Real.log 2) / 2))
      = Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hk : ((Real.exp (Real.log 2 / 2) : ℝ) : ℂ)
      * ((Real.exp (-((t + Real.log 2) / 2)) : ℝ) : ℂ)
      = ((Real.exp (-(t / 2)) : ℝ) : ℂ) := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hkR
  linear_combination ((v : ℝ → ℂ) (t + Real.log 2)) * hk

end

end RHTower
