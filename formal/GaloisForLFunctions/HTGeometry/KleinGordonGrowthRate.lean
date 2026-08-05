import GaloisForLFunctions.HTGeometry.KleinGordonRadiusAnnulus

/-!
# The true growth rate of a periodically driven clock

Statement 300 bounds the state after `n` periods by `e^{nb|T|}`, the estimate's rate. The true rate is
the spectral radius, and Gelfand's formula says so: `‖Mⁿ‖^{1/n} → r`, so for every tolerance `ε` the
powers are eventually below `(r+ε)ⁿ`.

mathlib has the formula but not this consequence — statement 329 extracted the special case `r < 1`;
here it is proved for an arbitrary finite spectral radius, and applied to the monodromy, whose radius
is finite because the annulus of statement 406 bounds it by `e^{b|T|}`.

**After enough periods a clock grows no faster than its spectral radius, to any prescribed accuracy.**
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

/-! ## Powers below the spectral radius -/

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **The powers are eventually below any rate exceeding the spectral radius.** -/
theorem eventually_norm_pow_le_of_spectralRadius {a : A}
    (hfin : spectralRadius ℂ a ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ ((spectralRadius ℂ a).toReal + ε) ^ n := by
  set r : ℝ≥0∞ := spectralRadius ℂ a with hrdef
  set q : ℝ := r.toReal + ε with hqdef
  have hr0 : (0 : ℝ) ≤ r.toReal := ENNReal.toReal_nonneg
  have hq0 : 0 < q := by rw [hqdef]; linarith
  have hrq : r < ENNReal.ofReal q := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt hfin, hqdef]
    linarith
  have hgel := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (A := A) a
  have hev : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ)) < ENNReal.ofReal q :=
    hgel.eventually_lt_const hrq
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hlt : ‖a ^ n‖ ^ (1 / n : ℝ) < q := (ENNReal.ofReal_lt_ofReal_iff hq0).mp hn
  rw [one_div] at hlt
  have hn0 : n ≠ 0 := by omega
  have hbase : (0 : ℝ) ≤ ‖a ^ n‖ ^ ((n : ℝ))⁻¹ := Real.rpow_nonneg (norm_nonneg _) _
  have hkey : ‖a ^ n‖ = (‖a ^ n‖ ^ ((n : ℝ))⁻¹) ^ n :=
    (Real.rpow_inv_natCast_pow (norm_nonneg _) hn0).symm
  rw [hkey]
  gcongr

end BanachAlgebra

/-! ## The clock's true rate -/

section ClockRate

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- The spectral radius of a monodromy is finite. -/
theorem spectralRadius_kgMonodromy_ne_top (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) :
    spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) ≠ ⊤ := by
  obtain ⟨_, hup⟩ := spectralRadius_kgMonodromy_mem_annulus hb0 hWb hWs hper
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup

set_option maxHeartbeats 1000000 in
/-- **After enough periods a clock grows no faster than its spectral radius**, to any prescribed
accuracy. -/
theorem eventually_norm_kgFieldStateT_le_of_spectralRadius (hb0 : 0 ≤ b)
    (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) {ε : ℝ} (hε : 0 < ε)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    ∀ᶠ n : ℕ in atTop, ‖kgFieldStateT W g h (n * T)‖
      ≤ ((spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε) ^ n
        * ‖kgPair E (g, h)‖ := by
  have hpow := eventually_norm_pow_le_of_spectralRadius
    (spectralRadius_kgMonodromy_ne_top hb0 hWb hWs hper) hε
  filter_upwards [hpow] with n hn
  have hval : ‖kgFieldStateT W g h (n * T)‖
      ≤ ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ * ‖kgPair E (g, h)‖ := by
    rw [kgFieldStateT_monodromy_pow hb0 hWb hWs hper g h n]
    exact (kgMonodromy W b hb0 hWb hWs T ^ n).le_opNorm _
  exact hval.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

end ClockRate

end GaloisForLFunctions.HTGeometry
