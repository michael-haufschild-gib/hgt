import GaloisForLFunctions.ArithmeticElectrostatics.QuantizationTurnsWindowsIntoPoints
import GaloisForLFunctions.RHTower.LorentzianZeroMass

/-!
# The energy of a zero is logarithmic

The transverse energy is quantized from below (`one_le_angularEnergy`: an off-line zero carries a
full quantum). This file bounds it from above, unconditionally, by the local density of zeros.

* **Pair bound** (`angularEnergyTerm_le_lorentz`): the angular term of two zeros is at most
  `2/(1 + (γ − γ′)²)`: the squared cosine is at most `1`, and at most `(Re ρ − Re ρ′)²/(γ − γ′)²` with
  the real parts in a strip of width one.
* **The energy of a zero** (`angularEnergy_le_log`): `E(ρ) ≤ 16(C + log(|γ| + 4))`, by the Lorentzian
  zero mass `Σ_ρ′ 1/(1 + (γ − γ′)²) ≤ 8(C + log(|γ| + 4))` (`RHTower.lorentzMass_le_log`).
* **The energy of a window** (`windowEnergy_le`): at most `16(C + log(|T| + H + 4))` times the number
  of zeros in the window.

So every zero has transverse energy between `0` (critical, under RH) and `O(log γ)`, every off-line
zero at least `1`. The energy is controlled unconditionally because each pair term is bounded;
the field is not, since a nearly coincident pair contributes `1/|ρ − ρ′|`. RH is the improvement of
the unconditional `O(log γ)` to `< 1` at every zero (`riemannHypothesis_iff_forall_angularEnergy_lt_one`),
or of the window bound to `< 2` (`riemannHypothesis_iff_windowEnergy_lt_two`).
-/

open RHTower Finset

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- **Pair bound**: `cos²θ(ρ, ρ′) ≤ 2/(1 + (γ − γ′)²)`. -/
theorem angularEnergyTerm_le_lorentz (j k : XiDivisorSupport) :
    angularEnergyTerm j k ≤ 2 * (1 / (1 + ((j : ℂ).im - (k : ℂ).im) ^ 2)) := by
  unfold angularEnergyTerm
  split_ifs with h
  · positivity
  · have hr : ((j : ℂ).re - (k : ℂ).re) ^ 2 ≤ 1 := by
      obtain ⟨hj0, hj1⟩ := xiDivisorSupport_re_mem j
      obtain ⟨hk0, hk1⟩ := xiDivisorSupport_re_mem k
      nlinarith
    have hN : Complex.normSq ((j : ℂ) - (k : ℂ)) =
        ((j : ℂ).re - (k : ℂ).re) ^ 2 + ((j : ℂ).im - (k : ℂ).im) ^ 2 := by
      rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
    have hpos : 0 < Complex.normSq ((j : ℂ) - (k : ℂ)) := by
      rw [Complex.normSq_pos, sub_ne_zero]
      exact fun hc => h (Subtype.ext hc.symm)
    rw [div_le_iff₀ hpos, hN]
    set r := ((j : ℂ).re - (k : ℂ).re) ^ 2
    set d := ((j : ℂ).im - (k : ℂ).im) ^ 2
    have hr0 : 0 ≤ r := sq_nonneg _
    have hd0 : 0 ≤ d := sq_nonneg _
    rw [show 2 * (1 / (1 + d)) * (r + d) = 2 * (r + d) / (1 + d) by ring,
      le_div_iff₀ (by positivity)]
    nlinarith

/-- **The energy of a zero is logarithmic**: `E(ρ) ≤ 16(C + log(|γ| + 4))`. -/
theorem angularEnergy_le_log (j : XiDivisorSupport) :
    angularEnergy j ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (|(j : ℂ).im| + 4)) := by
  set t := (j : ℂ).im
  have hcopy : ∀ k : XiDivisorSupport, angularEnergyTerm j k ≤
      2 * lorentzMassTerm t (supportToCopy k) := fun k => by
    rw [lorentzMassTerm, supportToCopy_fst]
    exact angularEnergyTerm_le_lorentz j k
  have hsum : Summable fun q : XiZeroCopy => 2 * lorentzMassTerm t q :=
    (summable_lorentzMassTerm t).mul_left 2
  calc angularEnergy j ≤ ∑' k : XiDivisorSupport, 2 * lorentzMassTerm t (supportToCopy k) :=
        (summable_angularEnergyTerm j).tsum_le_tsum hcopy
          (hsum.comp_injective supportToCopy_injective)
    _ ≤ ∑' q : XiZeroCopy, 2 * lorentzMassTerm t q :=
        tsum_comp_le_tsum_of_inj hsum
          (fun q => mul_nonneg zero_le_two (lorentzMassTerm_nonneg t q)) supportToCopy_injective
    _ = 2 * lorentzMass t := by rw [tsum_mul_left, lorentzMass]
    _ ≤ 2 * (8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4))) := by
        gcongr; exact lorentzMass_le_log t
    _ = 16 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) := by ring

/-- **The energy of a window**: at most `16(C + log(|T| + H + 4))` per zero of the window. -/
theorem windowEnergy_le (T : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    windowEnergy T hH ≤ ((zeroWindow_finite T hH).toFinset.card : ℝ) *
      (16 * (xiLineTwoLogDerivConstant + Real.log (|T| + H + 4))) := by
  rw [windowEnergy, ← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun ρ hρ => (angularEnergy_le_log ρ).trans ?_
  have hmem : |(ρ : ℂ).im - T| ≤ H := (zeroWindow_finite T hH).mem_toFinset.mp hρ
  have him : |(ρ : ℂ).im| ≤ |T| + H := by
    calc |(ρ : ℂ).im| = |((ρ : ℂ).im - T) + T| := by ring_nf
      _ ≤ |(ρ : ℂ).im - T| + |T| := abs_add_le _ _
      _ ≤ |T| + H := by linarith
  have hlog : Real.log (|(ρ : ℂ).im| + 4) ≤ Real.log (|T| + H + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

/-- **Two-sided law for a zero**: an off-line zero has `1 ≤ E(ρ) ≤ 16(C + log(|γ| + 4))`. -/
theorem one_le_angularEnergy_le_log {j : XiDivisorSupport} (hj : (j : ℂ).re ≠ 1 / 2) :
    1 ≤ angularEnergy j ∧
      angularEnergy j ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (|(j : ℂ).im| + 4)) :=
  ⟨one_le_angularEnergy hj, angularEnergy_le_log j⟩

end

end GaloisForLFunctions.ArithmeticElectrostatics
