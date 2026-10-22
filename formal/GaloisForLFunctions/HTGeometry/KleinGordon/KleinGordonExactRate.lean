import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonGrowthRate

/-!
# The spectral radius is the exact growth rate

Statement 409 bounds the growth of a clock above by its spectral radius. The bound below is the same
inequality that confines the multipliers: `kⁿ` is a spectral value of `Mⁿ`, so `|k|ⁿ ≤ ‖Mⁿ‖` for every
multiplier `k`.

The spectral radius of a monodromy is *attained* by a multiplier (statement 342), so the lower bound
holds with `r` itself and needs no tolerance:

`rⁿ ≤ ‖Mⁿ‖ ≤ (r+ε)ⁿ` eventually, for every `ε > 0`.

The growth of a periodically driven clock is exactly its spectral radius — the estimate's rate `e^{b|T|}`
of statement 300 is an upper bound for `r`, never the truth unless the two coincide.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

/-! ## A multiplier bounds the growth from below -/

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Every spectral value grows no faster than the powers.** -/
theorem norm_pow_le_norm_pow_of_mem_spectrum {a : A} (h1 : ‖(1 : A)‖ ≤ 1) {k : ℂ}
    (hk : k ∈ spectrum ℂ a) (n : ℕ) : ‖k‖ ^ n ≤ ‖a ^ n‖ := by
  have hmem : k ^ n ∈ spectrum ℂ (a ^ n) := spectrum.pow_mem_pow _ n hk
  have hle := spectrum.norm_le_norm_mul_of_mem hmem
  have hstep : ‖a ^ n‖ * ‖(1 : A)‖ ≤ ‖a ^ n‖ * 1 :=
    mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  rw [mul_one] at hstep
  rw [← norm_pow]
  exact hle.trans hstep

end BanachAlgebra

/-! ## The exact rate of a clock -/

section ExactRate

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **The powers of a monodromy grow at least like its spectral radius.** -/
theorem spectralRadius_pow_le_norm_pow_kgMonodromy (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (n : ℕ) :
    ((spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal) ^ n
      ≤ ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ := by
  obtain ⟨k, hk, hval⟩ := exists_multiplier_eq_spectralRadius (T := T) hb0 hWb hWs
  have hknorm : ‖k‖ = (spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal := by
    have h := congrArg ENNReal.toReal hval
    simpa using h
  rw [← hknorm]
  exact norm_pow_le_norm_pow_of_mem_spectrum (le_of_eq norm_one_kgEnergy) hk n

/-- **The growth of a clock is exactly its spectral radius**: bounded below by `rⁿ` always, and above
by `(r+ε)ⁿ` eventually, for every tolerance. -/
theorem norm_pow_kgMonodromy_sandwich (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal) ^ n
          ≤ ‖kgMonodromy W b hb0 hWb hWs T ^ n‖
        ∧ ‖kgMonodromy W b hb0 hWb hWs T ^ n‖
          ≤ ((spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε) ^ n := by
  have hup := eventually_norm_pow_le_of_spectralRadius
    (spectralRadius_kgMonodromy_ne_top hb0 hWb hWs hper) hε
  filter_upwards [hup] with n hn
  exact ⟨spectralRadius_pow_le_norm_pow_kgMonodromy hb0 hWb hWs n, hn⟩

end ExactRate

end GaloisForLFunctions.HTGeometry
