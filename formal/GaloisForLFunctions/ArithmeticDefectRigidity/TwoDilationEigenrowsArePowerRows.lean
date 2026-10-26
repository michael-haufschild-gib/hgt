import GaloisForLFunctions.ArithmeticDefectRigidity.TwistedOnePrimeLawsForceTiedExponents
import GaloisForLFunctions.ArithmeticDefectRigidity.TwoEulerFactorsDetermineThePoleTrace

/-!
# Approximate joint eigenrows of two dilations are tied power rows

A complex row `w` is an approximate eigenrow of the dilation `D_p w(n) = w(⌊n/p⌋)` with exponent
`s` when `w − p^s D_p w` has finite pronic energy (`cEulerLaw`). Above the critical line:

* `exists_cPronicEnergy_sub_cpow_ne_top`: if `w` is an approximate eigenrow of `D₂` with exponent
  `s₂` and of `D₃` with exponent `s₃`, `Re s₂ = Re s₃ ∈ (1/2, 1]`, then `w − c n^s` has finite pronic
  energy, and unless `c = 0` the exponent is tied: `2^s = 2^{s₂}` and `3^s = 3^{s₃}`.
* `cPronicEnergy_ne_top_of_untied`: if no exponent is tied to both, `w` itself has finite energy.
* `exists_cPronicEnergy_sub_cpow_ne_top_same`: with `s₂ = s₃ = s` the power is `n^s` itself.

So at the level of rows, rank-one escape is power-like and its exponent is tied across primes.
The proof runs on the log scale `g(u) = e^{-u/2} w(⌊e^u⌋)`, where the law at `p` is the twisted
one-prime law with period `log p` (`twistedDefect_cLogProfile`), and applies
`exists_lintegral_sub_const_mul_cexp_ne_top` with the incommensurable periods `log 2`, `log 3`.
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The full pronic energy of a complex row. -/
def cPronicEnergy (w : ℕ → ℂ) : ENNReal := pronicEnergy fun n => ‖w n‖

/-- The complex log-scale profile `e^{-u/2} w(⌊e^u⌋)`. -/
def cLogProfile (w : ℕ → ℂ) (u : ℝ) : ℂ := (Real.exp (-(u / 2)) : ℂ) * w ⌊Real.exp u⌋₊

/-- The Euler law of exponent `s` at `p`: `w − p^s D_p w`. -/
def cEulerLaw (p : ℕ) (s : ℂ) (w : ℕ → ℂ) (n : ℕ) : ℂ := w n - (p : ℂ) ^ s * w (n / p)

theorem measurable_cLogProfile (w : ℕ → ℂ) : Measurable (cLogProfile w) :=
  (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_id.div_const 2).neg)).mul
    (measurable_from_nat.comp (Nat.measurable_floor.comp Real.measurable_exp))

theorem norm_cLogProfile (w : ℕ → ℂ) (u : ℝ) :
    ‖cLogProfile w u‖ = logProfile (fun n => ‖w n‖) u := by
  rw [cLogProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    logProfile]

/-- **The complex pronic energy is the log-scale energy.** -/
theorem lintegral_cLogProfile_sq {w : ℕ → ℂ} (hw0 : w 0 = 0) :
    ∫⁻ u, ENNReal.ofReal (‖cLogProfile w u‖ ^ 2) = cPronicEnergy w := by
  simp_rw [norm_cLogProfile]
  exact lintegral_logProfile_sq (by simp [hw0])

/-- The law at `p` with exponent `s = κ + 1/2 + iγ` is the twisted one-prime law with period
`log p`. -/
theorem twistedDefect_cLogProfile {p : ℕ} (hp : 0 < p) (κ γ : ℝ) (w : ℕ → ℂ) (u : ℝ) :
    twistedDefect κ γ (Real.log p) (cLogProfile w) u =
      cLogProfile (cEulerLaw p ((κ + 1 / 2 : ℝ) + γ * I) w) u := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hfl : ⌊Real.exp (u - Real.log p)⌋₊ = ⌊Real.exp u⌋₊ / p := by
    rw [Real.exp_sub, Real.exp_log hp0, Nat.floor_div_natCast]
  have hpow : (p : ℂ) ^ (((κ + 1 / 2 : ℝ) : ℂ) + γ * I) =
      Complex.exp ((κ + γ * I) * Real.log p) * (Real.exp (Real.log p / 2) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), Complex.ofReal_exp,
      ← Complex.exp_add, ← Complex.ofReal_natCast, ← Complex.ofReal_log hp0.le]
    congr 1; push_cast; ring
  have hexp : (Real.exp (-((u - Real.log p) / 2)) : ℂ) =
      (Real.exp (Real.log p / 2) : ℂ) * (Real.exp (-(u / 2)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
  rw [twistedDefect, cLogProfile, cLogProfile, hfl, hexp, cLogProfile, cEulerLaw, hpow]
  ring

theorem cEulerLaw_zero {p : ℕ} (s : ℂ) {w : ℕ → ℂ} (hw0 : w 0 = 0) : cEulerLaw p s w 0 = 0 := by
  simp [cEulerLaw, hw0]

theorem cpow_add_half_eq (p : ℕ) (hp : 0 < p) (z : ℂ) :
    (p : ℂ) ^ (z + 1 / 2) = Complex.exp (z * Real.log p) * (Real.exp (Real.log p / 2) : ℂ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.ofReal_natCast, ← Complex.ofReal_log hp0.le]
  congr 1; push_cast; ring

/-- On the log scale the power row `c n^s` is `c e^{(s−1/2)u}` up to `‖c‖‖s‖ e^{-u/2}` on `u ≥ 0`. -/
theorem norm_cLogProfile_sub_cpow_le {s : ℂ} (hs : s.re ≤ 1) (w : ℕ → ℂ) (c : ℂ) {u : ℝ}
    (hu : 0 ≤ u) :
    ‖cLogProfile (fun n => w n - c * (n : ℂ) ^ s) u -
        (cLogProfile w u - c * Complex.exp ((s - 1 / 2) * u))‖ ≤
      ‖c‖ * ‖s‖ * Real.exp (-(u / 2)) := by
  set x := Real.exp u with hxdef
  have hx : 1 ≤ x := Real.one_le_exp hu
  set m : ℕ := ⌊x⌋₊ with hmdef
  have hm1 : (1 : ℝ) ≤ m := by
    rw [hmdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rw [Ne, Nat.floor_eq_zero]; linarith)
  have hmx : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxm : x ≤ (m : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have hexp : Complex.exp ((s - 1 / 2) * u) = (Real.exp (-(u / 2)) : ℂ) * ((x : ℝ) : ℂ) ^ s := by
    rw [hxdef, Complex.ofReal_exp, Complex.ofReal_exp, Complex.cpow_def_of_ne_zero
      (Complex.exp_ne_zero _), Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]), ← Complex.exp_add]
    congr 1; push_cast; ring
  have hid : cLogProfile (fun n => w n - c * (n : ℂ) ^ s) u -
      (cLogProfile w u - c * Complex.exp ((s - 1 / 2) * u)) =
      c * (Real.exp (-(u / 2)) : ℂ) * (((x : ℝ) : ℂ) ^ s - (((m : ℝ)) : ℂ) ^ s) := by
    rw [hexp, cLogProfile, cLogProfile, ← hmdef, Complex.ofReal_natCast]
    ring
  rw [hid, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hmv := norm_ofReal_cpow_sub_le hs (by linarith : (0 : ℝ) < m) le_rfl hmx
  have hpow : (m : ℝ) ^ (s.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)
  have hgap : x - m ≤ 1 := by linarith
  have hbound : ‖((x : ℝ) : ℂ) ^ s - (((m : ℝ)) : ℂ) ^ s‖ ≤ ‖s‖ := by
    calc _ ≤ ‖s‖ * (m : ℝ) ^ (s.re - 1) * (x - m) := hmv
      _ ≤ ‖s‖ * 1 * 1 := by
          have h0 : 0 ≤ x - m := by linarith
          have hA : ‖s‖ * (m : ℝ) ^ (s.re - 1) ≤ ‖s‖ * 1 :=
            mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
          exact mul_le_mul hA hgap h0 (by positivity)
      _ = ‖s‖ := by ring
  have := Real.exp_pos (-(u / 2))
  calc ‖c‖ * Real.exp (-(u / 2)) * ‖((x : ℝ) : ℂ) ^ s - (((m : ℝ)) : ℂ) ^ s‖
      ≤ ‖c‖ * Real.exp (-(u / 2)) * ‖s‖ :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ‖c‖ * ‖s‖ * Real.exp (-(u / 2)) := by ring

/-- **Approximate joint eigenrows of `D₂` and `D₃` are tied power rows.** For
`Re s₂ = Re s₃ ∈ (1/2, 1]` and `w(0) = 0`: if `w − 2^{s₂}D₂w` and `w − 3^{s₃}D₃w` have finite
pronic energy, then `w − c n^s` has finite pronic energy with `Re s = Re s₂`, and unless `c = 0` the
exponent is tied: `2^s = 2^{s₂}`, `3^s = 3^{s₃}`. -/
theorem exists_cPronicEnergy_sub_cpow_ne_top {s₂ s₃ : ℂ} (hre : s₂.re = s₃.re)
    (h12 : 1 / 2 < s₂.re) (h1 : s₂.re ≤ 1) {w : ℕ → ℂ} (hw0 : w 0 = 0)
    (h2 : cPronicEnergy (cEulerLaw 2 s₂ w) ≠ ⊤) (h3 : cPronicEnergy (cEulerLaw 3 s₃ w) ≠ ⊤) :
    ∃ c s : ℂ, s.re = s₂.re ∧ (c ≠ 0 → (2 : ℂ) ^ s = 2 ^ s₂ ∧ (3 : ℂ) ^ s = 3 ^ s₃) ∧
      cPronicEnergy (fun n => w n - c * (n : ℂ) ^ s) ≠ ⊤ := by
  set κ : ℝ := s₂.re - 1 / 2 with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  have hs₂ : s₂ = ((κ + 1 / 2 : ℝ) : ℂ) + (s₂.im : ℂ) * I := by
    apply Complex.ext <;> simp [hκdef]
  have hs₃ : s₃ = ((κ + 1 / 2 : ℝ) : ℂ) + (s₃.im : ℂ) * I := by
    apply Complex.ext <;> simp [hκdef, hre]
  have hlaw : ∀ p : ℕ, 0 < p → ∀ γ : ℝ,
      cPronicEnergy (cEulerLaw p (((κ + 1 / 2 : ℝ) : ℂ) + γ * I) w) ≠ ⊤ →
        ∫⁻ u, ENNReal.ofReal (‖twistedDefect κ γ (Real.log p) (cLogProfile w) u‖ ^ 2) ≠ ⊤ := by
    intro p hp γ h
    simp_rw [twistedDefect_cLogProfile hp]
    rw [lintegral_cLogProfile_sq (cEulerLaw_zero _ hw0)]
    exact h
  have h2' := hlaw 2 (by norm_num) s₂.im (by rw [← hs₂]; exact h2)
  have h3' := hlaw 3 (by norm_num) s₃.im (by rw [← hs₃]; exact h3)
  rw [Nat.cast_ofNat] at h2' h3'
  obtain ⟨c, z, hzre, htied, hfin⟩ := exists_lintegral_sub_const_mul_cexp_ne_top hκ
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (Real.log_pos (by norm_num : (1 : ℝ) < 3))
    addOrderOf_log_two_in_log_three (measurable_cLogProfile w) h2' h3'
  have hsre : (z + 1 / 2).re = s₂.re := by simp [hzre, hκdef]
  refine ⟨c, z + 1 / 2, hsre, fun hc => ?_, ?_⟩
  · obtain ⟨t2, t3⟩ := htied hc
    have e2 := cpow_add_half_eq 2 (by norm_num) z
    have e3 := cpow_add_half_eq 3 (by norm_num) z
    have f2 := cpow_add_half_eq 2 (by norm_num) ((κ : ℂ) + s₂.im * I)
    have f3 := cpow_add_half_eq 3 (by norm_num) ((κ : ℂ) + s₃.im * I)
    simp only [Nat.cast_ofNat] at e2 e3 f2 f3
    have hs₂' : s₂ = (κ : ℂ) + s₂.im * I + 1 / 2 := by
      apply Complex.ext <;> simp [hκdef]
    have hs₃' : s₃ = (κ : ℂ) + s₃.im * I + 1 / 2 := by
      apply Complex.ext <;> simp [hκdef, hre]
    exact ⟨by rw [e2, hs₂', f2, t2], by rw [e3, hs₃', f3, t3]⟩
  · have hs1 : (z + 1 / 2).re ≤ 1 := by rw [hsre]; exact h1
    have hs0 : z + 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
    have hrow0 : (fun n : ℕ => w n - c * (n : ℂ) ^ (z + 1 / 2)) 0 = 0 := by
      show w 0 - c * ((0 : ℕ) : ℂ) ^ (z + 1 / 2) = 0
      rw [Nat.cast_zero, Complex.zero_cpow hs0, hw0]; ring
    rw [← lintegral_cLogProfile_sq hrow0]
    set K := ‖c‖ * ‖z + 1 / 2‖
    have hbound : ∀ u : ℝ, ENNReal.ofReal (‖cLogProfile (fun n => w n - c * (n : ℂ) ^ (z + 1 / 2)) u‖ ^ 2)
        ≤ 2 * ENNReal.ofReal (‖cLogProfile w u - c * Complex.exp (z * u)‖ ^ 2) +
          2 * (Ici (0 : ℝ)).indicator (fun u => ENNReal.ofReal (K ^ 2 * Real.exp (-u))) u := by
      intro u
      rcases lt_or_ge u 0 with hu | hu
      · have hfl : ⌊Real.exp u⌋₊ = 0 := Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr hu)
        have h0 : cLogProfile (fun n => w n - c * (n : ℂ) ^ (z + 1 / 2)) u = 0 := by
          rw [cLogProfile, hfl]
          show _ * (w 0 - c * ((0 : ℕ) : ℂ) ^ (z + 1 / 2)) = 0
          rw [Nat.cast_zero, Complex.zero_cpow hs0, hw0]; ring
        rw [h0, norm_zero]; simp
      · rw [indicator_of_mem (Set.mem_Ici.mpr hu)]
        have herr := norm_cLogProfile_sub_cpow_le hs1 w c hu
        rw [show z + 1 / 2 - 1 / 2 = z by ring] at herr
        set L := cLogProfile (fun n => w n - c * (n : ℂ) ^ (z + 1 / 2)) u
        set A := cLogProfile w u - c * Complex.exp (z * u)
        have hsq : ‖L - A‖ ^ 2 ≤ K ^ 2 * Real.exp (-u) := by
          have he : (K * Real.exp (-(u / 2))) ^ 2 = K ^ 2 * Real.exp (-u) := by
            rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
          rw [← he]
          exact pow_le_pow_left₀ (norm_nonneg _) herr 2
        have := norm_sub_sq_le A (-(L - A))
        rw [sub_neg_eq_add, add_sub_cancel, norm_neg] at this
        calc ENNReal.ofReal (‖L‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖A‖ ^ 2 + 2 * (K ^ 2 * Real.exp (-u))) :=
              ENNReal.ofReal_le_ofReal (by linarith)
          _ = _ := by
              rw [ENNReal.ofReal_add (by positivity) (by positivity),
                ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_mul (p := 2) (by norm_num),
                ENNReal.ofReal_ofNat]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hbound)
    have hmA : Measurable fun u => 2 * ENNReal.ofReal (‖cLogProfile w u - c * Complex.exp (z * u)‖ ^ 2) :=
      (ENNReal.measurable_ofReal.comp (((measurable_cLogProfile w).sub (measurable_const.mul
        (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)))).norm.pow_const
          2)).const_mul 2
    have hme : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-u)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg)
    rw [lintegral_add_left hmA, lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num), lintegral_indicator measurableSet_Ici]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hfin,
      ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) ?_⟩
    simp_rw [ENNReal.ofReal_mul (sq_nonneg K)]
    rw [lintegral_const_mul _ hme]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top lintegral_Ici_exp_neg_ne_top

/-- **Untied laws admit only finite-energy rows.** -/
theorem cPronicEnergy_ne_top_of_untied {s₂ s₃ : ℂ} (hre : s₂.re = s₃.re) (h12 : 1 / 2 < s₂.re)
    (h1 : s₂.re ≤ 1) {w : ℕ → ℂ} (hw0 : w 0 = 0)
    (h2 : cPronicEnergy (cEulerLaw 2 s₂ w) ≠ ⊤) (h3 : cPronicEnergy (cEulerLaw 3 s₃ w) ≠ ⊤)
    (huntied : ∀ s : ℂ, ¬((2 : ℂ) ^ s = 2 ^ s₂ ∧ (3 : ℂ) ^ s = 3 ^ s₃)) :
    cPronicEnergy w ≠ ⊤ := by
  obtain ⟨c, s, -, htied, hfin⟩ := exists_cPronicEnergy_sub_cpow_ne_top hre h12 h1 hw0 h2 h3
  by_cases hc : c = 0
  · simpa [hc] using hfin
  · exact absurd (htied hc) (huntied s)

/-- Exponents tied to the same `s` at `2` and `3` are equal to `s`. -/
theorem eq_of_two_three_cpow_eq {s s' : ℂ} (h2 : (2 : ℂ) ^ s' = 2 ^ s) (h3 : (3 : ℂ) ^ s' = 3 ^ s) :
    s' = s := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  rw [Complex.cpow_def_of_ne_zero (by norm_num), Complex.cpow_def_of_ne_zero (by norm_num),
    Complex.exp_eq_exp_iff_exists_int] at h2 h3
  obtain ⟨n, hn⟩ := h2
  obtain ⟨m, hm⟩ := h3
  have hlog2 : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
  have hlog3 : Complex.log 3 = (Real.log 3 : ℂ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
  rw [hlog2] at hn
  rw [hlog3] at hm
  -- `(s' − s) log 2 = 2πin` and `(s' − s) log 3 = 2πim`
  have hcross : ((m : ℝ) * Real.log 2 : ℂ) = ((n : ℝ) * Real.log 3 : ℂ) := by
    have hI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    apply mul_left_cancel₀ hI
    linear_combination (Real.log 2 : ℂ) * hm - (Real.log 3 : ℂ) * hn
  have hreal : (m : ℝ) * Real.log 2 = (n : ℝ) * Real.log 3 := by exact_mod_cast hcross
  have hm0 := int_eq_zero_of_two_zpow_eq_three_zpow hreal
  rw [hm0, Int.cast_zero, zero_mul, add_zero] at hm
  have hne : (Real.log 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl3.ne'
  have := mul_right_cancel₀ hne (by linear_combination hm : s' * (Real.log 3 : ℂ) = s * Real.log 3)
  exact this

/-- **Approximate joint eigenrows with one exponent are multiples of `n^s`.** -/
theorem exists_cPronicEnergy_sub_cpow_ne_top_same {s : ℂ} (h12 : 1 / 2 < s.re) (h1 : s.re ≤ 1)
    {w : ℕ → ℂ} (hw0 : w 0 = 0) (h2 : cPronicEnergy (cEulerLaw 2 s w) ≠ ⊤)
    (h3 : cPronicEnergy (cEulerLaw 3 s w) ≠ ⊤) :
    ∃ c : ℂ, cPronicEnergy (fun n => w n - c * (n : ℂ) ^ s) ≠ ⊤ := by
  obtain ⟨c, s', -, htied, hfin⟩ := exists_cPronicEnergy_sub_cpow_ne_top rfl h12 h1 hw0 h2 h3
  by_cases hc : c = 0
  · exact ⟨0, by simpa [hc] using hfin⟩
  · obtain ⟨t2, t3⟩ := htied hc
    rw [eq_of_two_three_cpow_eq t2 t3] at hfin
    exact ⟨c, hfin⟩

end GaloisForLFunctions.ArithmeticDefectRigidity
