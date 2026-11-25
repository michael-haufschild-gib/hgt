import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpanningRecords.CrossingDelay

/-! # Exact equality between robust first returns and separated records -/

open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpanningRecords
open RepeatedGates.PhysicalBlocks PrecisionReturns
noncomputable section

/-- A return after the robust crossing inside a forbidden-lag window
is exactly the first return after the right endpoint of that window. -/
private theorem first_after_gap {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ)
    {v α h : ℝ} (hα : 0≤α) (hαh : α≤h) {ε : ℝ} (hε : 0<ε)
    (hex : ∀ w, v+α≤w → w<v+h → ¬HasProjectiveCircuitApproximation N ε s (unitaryEvolution H.val w)) :
    firstVisit H (v+α) s ε=firstVisit H (v+h) s ε := by
  have A := firstVisit_isLeast H (v+α) s hε
  have B := firstVisit_isLeast H (v+h) s hε
  exact le_antisymm (A.2 ⟨(add_le_add_left hαh v).trans B.1.1,B.1.2⟩)
    (B.2 ⟨le_of_not_gt (fun hh => hex _ A.1.1 hh A.1.2),A.1.2⟩)

/-- After every genuine positive-budget dip, the first return past the
next spanning-budget crossing equals the first visit at unit delay.
The same return is selected at every delay up to the logarithmic lag
horizon, even when the budget and crossing height depend on the dip. -/
theorem gaussian_exact_robust_step :
    ∃ c>0, ∃ b : ℕ, 2≤b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ (v : ℝ) (s q : ℕ) (η : ℝ), η∈Icc (9/80:ℝ) (1/8) →
        ((2*s+q:ℕ):ℝ)≤c*(n+1:ℕ) →
        HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution (prefix ω n).val v) →
        let u := firstExcessAfter ω n (s+q) v η
        0<u ∧ u≤1 ∧ orbitCircuitDistance (prefix ω n) (n+1+(s+q)) (v+u)=η ∧
          (∀ h∈Ico 0 u, orbitCircuitDistance (prefix ω n) (n+1+(s+q)) (v+h)<η) ∧
          ∀ h∈Icc (1:ℝ) (Nat.log b n:ℝ), firstVisit (prefix ω n) (v+u) s (1/10)=
            firstVisit (prefix ω n) (v+h) s (1/10) := by
  let c := min (prescribedExcess 1) (1/4:ℝ)
  have hc : 0<c := lt_min (prescribed_excess_pos (by norm_num)) (by norm_num)
  obtain ⟨A,hA,b,hb,hgap⟩ := SpanningDensity.FixedHorizon.gaussian_logarithmic_occupation
    (κ:=1/4) (by norm_num)
  refine ⟨c,hc,b,hb,?_⟩
  filter_upwards [hgap,gaussian_crossing_delay A hA] with ω hg hu
  filter_upwards [hg,hu] with n hn hd
  intro v s q η hη hq hv u
  have hN : (0:ℝ)≤(n+1:ℕ) := by positivity
  have hexc := hq.trans (mul_le_mul_of_nonneg_right (min_le_left ..) hN)
  have hs : (s:ℝ)≤1/4*(n+1:ℕ) := (show (s:ℝ) ≤ (2*s+q:ℕ) by exact_mod_cast (by omega : s≤2*s+q)).trans
    (hq.trans (mul_le_mul_of_nonneg_right (min_le_right ..) hN))
  obtain ⟨hlo,hup,he,hpre⟩ := hd v s q η hη hv hexc
  have hp : 0<u := (div_pos hA (by positivity)).trans hlo
  refine ⟨hp,hup,he,hpre,?_⟩
  intro h hh
  apply first_after_gap _ _ hp.le (hup.trans hh.1) (by norm_num)
  intro w hw hl hfit
  have gap := (hn s hs).1 v hv w hfit
  rw [abs_of_nonneg (by linarith only [hp,hw] : 0≤w-v)] at gap
  rcases gap with g|g
  · linarith only [g,hlo,hw]
  · linarith only [g,hl,hh.2]

#print axioms gaussian_exact_robust_step
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpanningRecords

