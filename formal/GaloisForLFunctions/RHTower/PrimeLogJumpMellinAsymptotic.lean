import GaloisForLFunctions.RHTower.PrimeLogJumpMellinRemainder
import GaloisForLFunctions.RHTower.PrimeLogJumpPacket

/-!
# The exact first Mellin boundary trace of the jump packet

The positive-ray Mellin evaluation of the jump packet is

```text
M_κ(s) = ∫_A^B x^{-s} (cos (κ x) − μ_κ) dx,
```

and one integration by parts, together with `κ μ_κ (B − A) = sin (κ B) − sin (κ A)`, turns it into

```text
κ M_κ(s) = B^{-s} sin (κ B) − A^{-s} sin (κ A) − (sin (κ B) − sin (κ A)) H(s) + R_κ(s),
```

where `H` is the shell average and the residual `R_κ(s) = s ∫_A^B x^{-s-1} sin (κ x) dx` is
`O(1/κ)`.  The endpoint jumps are therefore the entire leading behaviour: the discontinuous packet
is exactly first order at the Mellin boundary.
-/

namespace GaloisForLFunctions.RHTower

open Complex intervalIntegral Filter
open scoped Topology

variable {A B κ : ℝ}

/-- The positive-ray Mellin evaluation of the jump packet. -/
noncomputable def jumpMellin (A B κ : ℝ) (s : ℂ) : ℂ :=
  ∫ x in A..B, (x : ℂ) ^ (-s) * ((jumpPacket A B κ x : ℝ) : ℂ)

/-- The Mellin kernel is interval integrable against any continuous real weight. -/
theorem intervalIntegrable_cpow_mul (hA : 0 < A) (hAB : A < B) (w : ℂ) {f : ℝ → ℝ}
    (hf : Continuous f) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ w * ((f x : ℝ) : ℂ)) MeasureTheory.volume A B := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx0 : 0 < x := by
    rw [Set.uIcc_of_le (le_of_lt hAB)] at hx
    linarith [hx.1]
  exact ((continuousAt_cpow_ofReal hx0).mul
    (Complex.continuous_ofReal.continuousAt.comp hf.continuousAt)).continuousWithinAt

/-- The Mellin kernel alone is interval integrable. -/
theorem intervalIntegrable_cpow (hA : 0 < A) (hAB : A < B) (w : ℂ) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ w) MeasureTheory.volume A B := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx0 : 0 < x := by
    rw [Set.uIcc_of_le (le_of_lt hAB)] at hx
    linarith [hx.1]
  exact (continuousAt_cpow_ofReal hx0).continuousWithinAt

/-- On the open shell the packet is the modulated cosine. -/
theorem jumpMellin_eq (hA : 0 < A) (hAB : A < B) (κ : ℝ) (s : ℂ) :
    jumpMellin A B κ s
      = (∫ x in A..B, (x : ℂ) ^ (-s) * ((Real.cos (κ * x) : ℝ) : ℂ))
        - ((jumpMean A B κ : ℝ) : ℂ) * ∫ x in A..B, (x : ℂ) ^ (-s) := by
  have hpack : ∀ x ∈ Set.Ioo A B,
      (x : ℂ) ^ (-s) * ((jumpPacket A B κ x : ℝ) : ℂ)
        = (x : ℂ) ^ (-s) * ((Real.cos (κ * x) : ℝ) : ℂ)
          - ((jumpMean A B κ : ℝ) : ℂ) * (x : ℂ) ^ (-s) := by
    intro x hx
    have hmem : x ∈ jumpShellSet A B := Or.inr hx
    have hval : jumpPacket A B κ x = Real.cos (κ * x) - jumpMean A B κ := by
      simp [jumpPacket, jumpShell, Set.indicator_of_mem hmem]
    rw [hval]
    push_cast
    ring
  have hcongr : jumpMellin A B κ s
      = ∫ x in A..B, ((x : ℂ) ^ (-s) * ((Real.cos (κ * x) : ℝ) : ℂ)
          - ((jumpMean A B κ : ℝ) : ℂ) * (x : ℂ) ^ (-s)) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : ∀ᵐ x : ℝ, x ∈ Set.uIoc A B → x ∈ Set.Ioo A B ∨ x = B := by
      filter_upwards with x hx
      rw [Set.uIoc_of_le (le_of_lt hAB)] at hx
      rcases lt_or_eq_of_le hx.2 with h | h
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr h
    have hB : ∀ᵐ x : ℝ, x ≠ B := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hsub, hB] with x hx hxB hmem
    rcases hx hmem with h | h
    · exact hpack x h
    · exact absurd h hxB
  rw [hcongr, intervalIntegral.integral_sub
    (intervalIntegrable_cpow_mul (f := fun x : ℝ => Real.cos (κ * x)) hA hAB (-s)
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    ((intervalIntegrable_cpow hA hAB (-s)).const_mul ((jumpMean A B κ : ℝ) : ℂ)),
    intervalIntegral.integral_const_mul]

/-- **`(16)`.**  The exact first Mellin boundary trace, with residual. -/
theorem jumpMellin_trace (hA : 0 < A) (hAB : A < B) (hκ : κ ≠ 0) (s : ℂ) :
    (κ : ℂ) * jumpMellin A B κ s
      = (B : ℂ) ^ (-s) * ((Real.sin (κ * B) : ℝ) : ℂ)
        - (A : ℂ) ^ (-s) * ((Real.sin (κ * A) : ℝ) : ℂ)
        - ((Real.sin (κ * B) - Real.sin (κ * A) : ℝ) : ℂ) * shellAverage A B s
        + s * ∫ x in A..B, (x : ℂ) ^ (-s - 1) * ((Real.sin (κ * x) : ℝ) : ℂ) := by
  have hκ' : ((κ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  have hBA : ((B : ℂ) - (A : ℂ)) ≠ 0 :=
    sub_ne_zero.mpr fun h => absurd (Complex.ofReal_inj.mp h) (by linarith)
  have hmean : (κ : ℂ) * ((jumpMean A B κ : ℝ) : ℂ)
      = ((Real.sin (κ * B) - Real.sin (κ * A) : ℝ) : ℂ) * ((B : ℂ) - (A : ℂ))⁻¹ := by
    rw [jumpMean]
    push_cast
    field_simp
  rw [jumpMellin_eq hA hAB κ s, mul_sub, integral_cpow_mul_cos hA hAB hκ s]
  rw [show (κ : ℂ) * (((jumpMean A B κ : ℝ) : ℂ) * ∫ x in A..B, (x : ℂ) ^ (-s))
      = ((κ : ℂ) * ((jumpMean A B κ : ℝ) : ℂ)) * ∫ x in A..B, (x : ℂ) ^ (-s) by ring]
  rw [hmean, shellAverage]
  ring

/-- **The residual of the first trace vanishes at high frequency.** -/
theorem tendsto_jumpMellin_residual (hA : 0 < A) (hAB : A < B) (s : ℂ) :
    Tendsto (fun κ : ℝ => s * ∫ x in A..B, (x : ℂ) ^ (-s - 1) * ((Real.sin (κ * x) : ℝ) : ℂ))
      atTop (𝓝 0) := by
  simpa using (tendsto_integral_cpow_mul_sin hA hAB (-s - 1)).const_mul s

end GaloisForLFunctions.RHTower
