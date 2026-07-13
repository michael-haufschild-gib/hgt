import GaloisForLFunctions.RHTower.PolarPrimeRegularity
import GaloisForLFunctions.RHTower.SharpWindowCommensurability

/-!
# Two-width complete divisor recovery for the moving-tent observable

The moving-tent RH criterion `RH_iff_PcalObservable_regular` reads the *off-critical* divisor on
`Re s > 1`.  The **complete** nontrivial divisor — critical-line zeros included — is recovered by two
tent observables of irrationally related widths, on the maximal strip `Re s > ½`.

The error correction `H_L` is holomorphic on `{Re s > ½} ∖ {1}` (`HL_differentiableOn_gt_half`), and the
elementary polar terms are continuous there, so at each shifted zero `s = ρ + ½` the tent observable's
only possible singularity is the prime channel's simple pole, of residue proportional to `A_L(ρ-½)`.
A single width can miss a critical-line zero at a height `γ` with `A_L(iγ) = 0`, but two incommensurable
widths never share such a zero (`sharpAmplitude_not_both_zero`); hence every nontrivial zero survives as a
genuine pole in at least one of the two observables — the joint pole divisor is the entire nontrivial
zeta divisor.  (`bounded-variation-prime-window-divisor-tomography`'s complete-recovery clause, realized
for the squared tent window.)
-/

open Filter Topology Complex

namespace RHTower

/-- `PcalCorrection` is continuous on the maximal strip `{Re > ½} ∖ {1}` (using the widened
`HL_differentiableOn_gt_half`), so the tent observable's correction stays regular down to the
critical-line pole heights `s = 1 + iγ`. -/
theorem PcalCorrection_continuousAt_gt_half (L : ℝ) (hL : 0 ≤ L) {a : ℂ}
    (hare : 1 / 2 < a.re) (hane : a ≠ 1) : ContinuousAt (PcalCorrection L) a := by
  have e2 : ((1 / 2 : ℂ)).re = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
  have ha12 : a + 1 / 2 ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    rw [Complex.add_re, Complex.one_re, e2] at hr; linarith
  have hζs : ContinuousAt (fun s => riemannZeta s) a := (differentiableAt_riemannZeta hane).continuousAt
  have hζs2 : ContinuousAt (fun s => riemannZeta (s + 1 / 2)) a :=
    ((differentiableAt_riemannZeta ha12).comp a (differentiableAt_id.add_const _)).continuousAt
  have hopen : IsOpen ({s : ℂ | 1 / 2 < s.re} \ {1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hmem : a ∈ ({s : ℂ | 1 / 2 < s.re} \ {1}) := ⟨hare, by simpa using hane⟩
  have hHL : ContinuousAt (HL L) a :=
    ((HL_differentiableOn_gt_half L hL).differentiableAt (hopen.mem_nhds hmem)).continuousAt
  unfold PcalCorrection
  exact ((continuousAt_const.mul hζs).add (continuousAt_const.mul hζs2)).sub
    (continuousAt_const.mul hHL)

/-- **Tent genuine pole from a nonvanishing amplitude.**  For a nontrivial zeta zero `ρ` (`ρ ≠ 1`,
`Re ρ > 0`, `ρ ≠ ½`) with `A_L(ρ-½) ≠ 0`, the tent observable `PcalObservable L` has no finite limit at
`s = ρ + ½` — a genuine pole.  The polar and correction terms are continuous there (the correction via
the widened `HL` holomorphy), so the pole is inherited entirely from the prime channel
(`windowObservable_no_limit`). -/
theorem PcalObservable_no_limit_of_amplitude_ne (L : ℝ) (hL : 0 ≤ L) {ρ : ℂ}
    (hζρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) (hρ0 : 0 < ρ.re) (hρhalf : ρ ≠ 1 / 2)
    (hA : rectangularWindowAmplitude L (ρ - 1 / 2) ≠ 0) :
    ¬ ∃ M : ℂ, Tendsto (PcalObservable L) (𝓝[≠] (ρ + 1 / 2)) (𝓝 M) := by
  set W : ℂ → ℂ := fun s => -2 * (rectangularWindowAmplitude L (s - 1)) ^ 2 with hWdef
  have e2 : ((1 / 2 : ℂ)).re = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
  have hare : 1 / 2 < (ρ + 1 / 2).re := by rw [Complex.add_re, e2]; linarith
  have hane : ρ + 1 / 2 ≠ 1 := fun h => hρhalf (by linear_combination h)
  have hζshift : ContinuousAt (fun s => riemannZeta (s - 1 / 2)) (ρ + 1 / 2) := by
    have hsd : DifferentiableAt ℂ (fun s : ℂ => s - 1 / 2) (ρ + 1 / 2) := differentiableAt_id.sub_const _
    have hζρd : DifferentiableAt ℂ riemannZeta (ρ + 1 / 2 - 1 / 2) := by
      rw [show ρ + 1 / 2 - 1 / 2 = ρ by ring]; exact differentiableAt_riemannZeta hρ1
    exact (hζρd.comp (ρ + 1 / 2) hsd).continuousAt
  have hCcont : ContinuousAt (fun s => 8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ 2 * riemannZeta (s - 1 / 2)
      + PcalCorrection L s) (ρ + 1 / 2) :=
    (continuousAt_const.mul hζshift).add (PcalCorrection_continuousAt_gt_half L hL hare hane)
  have hWcont : Continuous W :=
    ((((rectangularWindowAmplitude_differentiable L).comp (differentiable_id.sub_const 1)).pow 2).const_mul
      (-2)).continuous
  have hWne : W (ρ + 1 / 2) ≠ 0 := by
    simp only [hWdef]
    rw [show ρ + 1 / 2 - 1 = ρ - 1 / 2 by ring]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hA)
  have hwin_no := windowObservable_no_limit W hρ1 hζρ hWcont.continuousAt hWne
  intro hlim
  rw [show (PcalObservable L) = (fun s => windowObservable W s
      + (8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ 2 * riemannZeta (s - 1 / 2) + PcalCorrection L s))
      from funext (fun s => by simp only [PcalObservable, primeObservable, windowObservable, hWdef]; ring)]
    at hlim
  exact hwin_no ((exists_tendsto_add_continuousAt_iff hCcont).mp hlim)

/-- **Tent two-width complete divisor recovery.**  For irrationally related widths `L₁, L₂`, every
nontrivial zeta zero `ρ` (`ρ ≠ 1`, `Re ρ > 0`, `ρ ≠ ½`) — critical-line ones included — is a genuine pole
of at least one of the two tent observables `PcalObservable L₁`, `PcalObservable L₂` at `s = ρ + ½`.  A
single width can miss a critical-line zero where its amplitude `A_L(iγ)` vanishes, but incommensurable
widths never share such a zero (`sharpAmplitude_not_both_zero`), so the joint pole divisor of the two
observables is the entire nontrivial zeta divisor. -/
theorem tent_twoWidth_divisor_recovery {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hirr : Irrational (L₁ / L₂)) {ρ : ℂ} (hζρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1)
    (hρ0 : 0 < ρ.re) (hρhalf : ρ ≠ 1 / 2) :
    (¬ ∃ M : ℂ, Tendsto (PcalObservable L₁) (𝓝[≠] (ρ + 1 / 2)) (𝓝 M))
      ∨ (¬ ∃ M : ℂ, Tendsto (PcalObservable L₂) (𝓝[≠] (ρ + 1 / 2)) (𝓝 M)) := by
  have hw : ρ - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρhalf
  rcases sharpAmplitude_not_both_zero hL₁ hL₂ hirr hw with hA | hA
  · exact Or.inl (PcalObservable_no_limit_of_amplitude_ne L₁ hL₁.le hζρ hρ1 hρ0 hρhalf hA)
  · exact Or.inr (PcalObservable_no_limit_of_amplitude_ne L₂ hL₂.le hζρ hρ1 hρ0 hρhalf hA)

end RHTower
