import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.PhysicalWait
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.HilbertWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Passage

/-! # The actual robust excursion containing a prescribed spectral antipode -/

open Set Filter MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
open AntipodalHorizons SharpOccupation ReturnExcursions
noncomputable section

private theorem eighth_small : (1/8:ℝ)∈Ioo (0:ℝ) (sqrt 2) := by
  constructor
  · norm_num
  · nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]

private theorem tenth_small : (1/10:ℝ)∈Ioo (0:ℝ) (sqrt 2) :=
  ⟨by norm_num,(by norm_num : (1/10:ℝ)<1/8).trans eighth_small.2⟩

/-- Every budget up to P has a genuine excursion containing a sufficiently
late prescribed extremal antipode. Its first robust crossing after the last
cheap visit and its subsequent first cheap visit bound a doubly exponential
physical wait, with no intervening affordable date. -/
theorem gaussian_antipodal_robust_excursions :
    ∃ c : ℕ, ∃ A : ℕ→ℕ, ∀ n : ℕ→ℕ, (∀ᶠ k : ℕ in atTop, A k ≤ n k) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let D : ℕ := 2^(k+3)
        let P := nearHilbertContinuousCircuitBudget (k+3)
        ∀ j≤P, InReturnExcursion (register k ω) P j (origin k (n k) ω)
          ((1/(15/16:ℝ))^D) (2*(2:ℝ)^(D^c)) := by
  obtain ⟨c,hu⟩ := gaussian_elapsed_upper
  obtain ⟨A,hA⟩ := frozen_physical_wait_of_gate_windows eighth_small.1 (by norm_num : (0:ℝ)<7/8)
    (by norm_num : (7/8:ℝ)<15/16) (gaussian_near_hilbert_antipodal_window eighth_small)
  refine ⟨c,A,?_⟩
  intro n hn
  filter_upwards [hA n hn,hu] with ω hω huω
  filter_upwards [hω,huω _ tenth_small] with k hp hdeadline
  intro D P j hj
  let H := register k ω
  let u := origin k (n k) ω
  let W := (1/(15/16:ℝ))^D
  apply excursion_of_hard_window H hj (show 0≤W by positivity)
  · intro a
    let v := PrecisionReturns.firstVisit H a 0 (1/10)
    have hv := (PrecisionReturns.firstVisit_isLeast H a 0 tenth_small.1).1
    refine ⟨v,⟨hv.1,?_⟩,hv.2⟩
    have h := hdeadline a
    dsimp only [v]
    linarith only [h]
  · intro t ht
    by_contra! hle
    have hf := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val t) P (1/8)).mpr hle
    have hmin := (PrecisionReturns.firstVisit_isLeast H u P eighth_small.1).2 ⟨ht.1,hf⟩
    change W < PrecisionReturns.firstVisit H u P (1/8)-u at hp
    linarith only [hp,ht.2,hmin]

private theorem subcritical_le_plateau {s : ℕ→ℕ} (hs : subcriticalBudget s) :
    ∀ᶠ N : ℕ in atTop, s N ≤ nearHilbertContinuousCircuitBudget N := by
  filter_upwards [hs.eventually_lt_const (by norm_num : (0:ℝ)<1/64)] with N h
  apply (Nat.le_div_iff_mul_le (by positivity : 0<64*(N+1))).mpr
  have hh := (div_lt_iff₀ (by positivity : (0:ℝ)<2^N)).mp h
  have hreal : (s N:ℝ)*(64*((N:ℝ)+1))≤(2:ℝ)^N := by
    nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) N]
  exact_mod_cast hreal

/-- At every subcritical budget the excursion containing the prescribed
antipode has the sharp short-arc base for its first post-crossing wait.
The last affordable time, first crossing at 9/80 and first subsequent
1/10 return all refer to this same physical trajectory. -/
theorem gaussian_sharp_antipodal_excursion :
    ∃ c : ℕ, ∀ s : ℕ→ℕ, subcriticalBudget s → ∀ b∈Ioo (physicalArc (1/10)) 1,
      ∃ A : ℕ→ℕ, ∀ n : ℕ→ℕ, (∀ᶠ k : ℕ in atTop, A k ≤ n k) →
        ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
          let N := k+3
          let D : ℕ := 2^N
          let P := nearHilbertContinuousCircuitBudget N
          ∀ j ≤ s N, InReturnExcursion (register k ω) P j (origin k (n k) ω)
            ((1/b)^D) (2*(2:ℝ)^(D^c)) := by
  obtain ⟨c,A₀,h₀⟩ := gaussian_antipodal_robust_excursions
  obtain ⟨_,hwait⟩ := gaussian_two_sided_circuit_wait
  refine ⟨c,?_⟩
  intro s hs b hb
  obtain ⟨A₁,h₁⟩ := hwait s hs _ tenth_small b hb
  refine ⟨fun k => max (A₀ k) (A₁ k),?_⟩
  intro n hn
  have hN := (tendsto_add_atTop_nat 3).eventually (subcritical_le_plateau hs)
  filter_upwards [h₀ n (hn.mono fun k hk => (le_max_left ..).trans hk),
    h₁ n (hn.mono fun k hk => (le_max_right ..).trans hk)] with ω hP hω
  filter_upwards [hP,hω,hN] with k hcross hfull hcost
  intro N D P j hj
  let H := register k ω
  let a := origin k (n k) ω
  obtain ⟨l,σ,v,hl,hlast,hσ,hσa,he,hfirst,hav,hvG,hv,hgap⟩ := hcross j (hj.trans hcost)
  refine ⟨l,σ,v,hl,hlast,hσ,hσa,he,hfirst,?_,hvG,hv,hgap⟩
  have hpos : 0≤(1/(15/16:ℝ))^D := by positivity
  have ha : a≤v := (le_add_of_nonneg_right hpos).trans hav.le
  obtain ⟨z,hz,C,hC,heC⟩ := hv.1.2
  have hmin := (PrecisionReturns.firstVisit_isLeast H a (s N) tenth_small.1).2
    ⟨ha,z,hz,C,hC.trans hj,heC⟩
  have hw : (1/b)^D < PrecisionReturns.firstVisit H a (s N) (1/10)-a := hfull.1
  change a+(1/b)^D < v
  linarith only [hw,hmin]

#print axioms gaussian_antipodal_robust_excursions
#print axioms gaussian_sharp_antipodal_excursion
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
