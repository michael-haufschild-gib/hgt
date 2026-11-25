import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.WidthFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NormalizedRadius.Survival

/-! # Slow first near-Hilbert crossings measured by the actual spectral turns -/

open Set MeasureTheory ProbabilityTheory Filter Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
open PrescribedTimes WeakBonds WeakBonds.NormalizedRadius
noncomputable section

/-- Number of spectral-width turns elapsed at the actual first 9/80
crossing from the identity on the unscaled register. -/
def firstCrossingTurns (n P : ℕ) (x : PrefixIndex n→ℝ) :=
  crossingOrigin n P (9/80) x*circuitHamiltonianSpectralWidth (prefixGenerator n x)/(2*π)

/-- Turns from the first near-Hilbert crossing to the next gate visit. -/
def firstWaitTurns (n P s : ℕ) (x : PrefixIndex n→ℝ) :=
  crossingWait n P s x*circuitHamiltonianSpectralWidth (prefixGenerator n x)/(2*π)

/-- Weak cuts delay the canonical first crossing even in units of the
register's own spectral period. This removes an arbitrarily slow overall
clock from the explanation of the T^(-18) lower tail. -/
theorem gaussian_first_crossing_turns_survival :
    ∃ c>(0:ℝ), ∀ᶠ k : ℕ in atTop, let n := k+1
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let r := sqrt (Fintype.card (PrefixIndex n):ℝ)
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      ∀ T≥(1:ℝ), c≤T^18*μ.real {x | r*T/π<firstCrossingTurns n P x ∧
        ∀ s ≤ P/2, r*T/π<firstWaitTurns n P s x} := by
  obtain ⟨c,hc,hs⟩ := gaussian_normalized_joint_survival
  refine ⟨c,hc,?_⟩
  filter_upwards [hs] with k hk
  intro n P r μ T hT
  letI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  let σ := crossingOrigin n P (9/80)
  let S := {x | T<σ (atRadius r x) ∧ ∀ s≤P/2, T<crossingWait n P s (atRadius r x)}
  have hlow : c≤T^18*μ.real S := hk T hT
  apply hlow.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hT) 18)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  have hσ : T<σ (atRadius r x) := hx.1
  have hdim : 0<Fintype.card (PrefixIndex n) := by
    rw [Fintype.card_congr (pathCoeffEquiv n)]
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have hr : 0<r := sqrt_pos.mpr (Nat.cast_pos.mpr hdim)
  have hnorm : 0<coefficientNorm x := by
    by_contra! hn
    have hzero : coefficientNorm x=0 := le_antisymm hn (norm_nonneg _)
    have he : atRadius r x=0 := by simp only [atRadius,hzero,div_zero,zero_smul]
    have hm := smul_crossingOrigin n P (9/80) (by norm_num : (0:ℝ)<2) (0 : PrefixIndex n→ℝ)
    rw [smul_zero] at hm
    rw [he] at hσ
    change 2*σ 0=σ 0 at hm
    linarith only [hm,hσ,hT]
  let a := r/coefficientNorm x
  have ha : 0<a := div_pos hr hnorm
  have transfer (v w : ℝ) (hv : T<v) (hs : a*v=w) :
      r*T/π<w*circuitHamiltonianSpectralWidth (prefixGenerator n x)/(2*π) := by
    have hpos : 0<w := hs ▸ mul_pos ha ((zero_lt_one.trans_le hT).trans hv)
    have hm : r*T < coefficientNorm x*w := calc
      r*T < r*v := mul_lt_mul_of_pos_left hv hr
      _ = coefficientNorm x*(a*v) := by dsimp only [a]; field_simp [hnorm.ne']
      _ = _ := by rw [hs]
    have hw := mul_le_mul_of_nonneg_left (twice_coefficientNorm_le_width n x) hpos.le
    apply (div_lt_div_iff₀ pi_pos two_pi_pos).mpr
    have hbig : 2*(r*T)<w*circuitHamiltonianSpectralWidth (prefixGenerator n x) := by
      nlinarith only [hm,hw]
    linarith only [mul_lt_mul_of_pos_right hbig pi_pos]
  exact ⟨transfer _ _ hσ (smul_crossingOrigin n P (9/80) ha x),
    fun s hs => transfer _ _ (hx.2 s hs) (smul_crossingWait n P s ha x)⟩

#print axioms gaussian_first_crossing_turns_survival
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
