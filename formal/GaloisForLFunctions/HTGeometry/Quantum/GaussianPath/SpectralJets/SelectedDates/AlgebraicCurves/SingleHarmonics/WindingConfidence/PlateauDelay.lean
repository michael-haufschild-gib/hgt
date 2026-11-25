import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.FirstCrossing

/-! # Minimum winding for exponential confidence at a prescribed plateau date -/

open Set MeasureTheory ProbabilityTheory Filter Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
open PrescribedTimes WeakBonds
noncomputable section

/-- The nth antipode of the two extreme levels in physical units. -/
def extremalAntipode (n m : ℕ) (x : PrefixIndex n→ℝ) : ℝ :=
  ((m:ℝ)+1/2)*(2*π)/circuitHamiltonianSpectralWidth (prefixGenerator n x)

/-- A nonnegligible set of registers has stayed below the robust crossing
level at every time from the identity through the prescribed antipode.
A failure probability exponentially small in D therefore requires a
winding exponentially large in D, even though only one date is prescribed. -/
theorem gaussian_preplateau_antipode_mass :
    ∃ c>(0:ℝ), ∀ᶠ k : ℕ in atTop, let n := k+1
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let r := sqrt (Fintype.card (PrefixIndex n):ℝ)
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      ∀ m : ℕ, c≤(1+π*((m:ℝ)+1/2)/r)^18*
        μ.real {x | ∀ t∈Icc (0:ℝ) (extremalAntipode n m x), pathGateDistance n P x t<9/80} := by
  obtain ⟨c,hc,h⟩ := gaussian_first_crossing_turns_survival
  refine ⟨c,hc,?_⟩
  filter_upwards [h] with k hk
  intro n P r μ m
  letI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  have hdim : 0<Fintype.card (PrefixIndex n) := by
    rw [Fintype.card_congr (pathCoeffEquiv n)]
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have hr : 0<r := sqrt_pos.mpr (Nat.cast_pos.mpr hdim)
  let M := (m:ℝ)+1/2
  have hm : 0<M := by dsimp only [M]; positivity
  let T := 1+π*M/r
  have hT : 1≤T := le_add_of_nonneg_right (div_nonneg (mul_nonneg pi_pos.le hm.le) hr.le)
  have hthreshold : M<r*T/π := by
    apply (lt_div_iff₀ pi_pos).mpr
    have he : r*T=r+π*M := by dsimp only [T]; field_simp [hr.ne']
    rw [he,mul_comm M π]
    linarith only [hr]
  apply (hk T hT).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hT) _)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx t ht
  let g := circuitHamiltonianSpectralWidth (prefixGenerator n x)
  let σ := crossingOrigin n P (9/80) x
  have hturn : M<σ*g/(2*π) := hthreshold.trans hx.1
  have hg : 0<g := by
    by_contra! hn
    have hz : g=0 := le_antisymm hn (circuitHamiltonianSpectralWidth_nonneg _)
    rw [hz,mul_zero,zero_div] at hturn
    exact (not_lt_of_ge hm.le) hturn
  have ha : extremalAntipode n m x<σ := (div_lt_iff₀ hg).mpr ((lt_div_iff₀ two_pi_pos).mp hturn)
  by_contra! hdist
  let C := {v : ℝ | 0≤v ∧ 9/80≤pathGateDistance n P x v}
  have hσ : σ≤t := csInf_le (s:=C) ⟨0,fun _ h => h.1⟩ ⟨ht.1,hdist⟩
  exact (ht.2.trans_lt ha).not_ge hσ

#print axioms gaussian_preplateau_antipode_mass
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
