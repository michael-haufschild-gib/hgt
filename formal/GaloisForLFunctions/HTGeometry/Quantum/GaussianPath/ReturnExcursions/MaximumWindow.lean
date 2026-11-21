import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.TypicalCrossing
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.TravelTime
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactSynthesis.MaximumOccupation

/-! # Minimum cost throughout a return gap relative to the same-error orbit maximum -/
open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Every attainable budget on the window dominates the square root of the
actual maximum up to an explicit polynomial factor in register size. -/
def MaximumCostWindow {n : ℕ} (H : selfAdjoint (Reg n)) (m : ℕ) (u W : ℝ) : Prop :=
  ∀ t ∈ Icc u (u+W), ∀ s : ℕ,
    HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution H.val t) →
    m < (4*n+1)*(2*n+2)*(64*(n+1)*s)^2

private theorem maximum_cost_of_window {n m : ℕ} (H : selfAdjoint (Reg n)) {u W G : ℝ}
    (hm : m ≤ (4*n+1)*(2*n+2)*(2^n)^2)
    (hw : IsExcursionWindow H (nearHilbertContinuousCircuitBudget n) u W G) :
    MaximumCostWindow H m u W := by
  intro t ht s hy
  have hP : nearHilbertContinuousCircuitBudget n < s := by
    by_contra! hs
    obtain ⟨z,hz,C,hC,he⟩ := hy
    have hd : orbitCircuitDistance H (nearHilbertContinuousCircuitBudget n) t ≤ 1/10 :=
      (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp ⟨z,hz,C,hC.trans hs,he⟩
    linarith only [hw.1 t ht,hd]
  have hD : 2^n < 64*(n+1)*s :=
    (Nat.lt_mul_div_succ (2^n) (by positivity : 0 < 64*(n+1))).trans_le
      (Nat.mul_le_mul_left (64*(n+1)) hP)
  have hsquare : (2^n)^2 < (64*(n+1)*s)^2 := by
    rw [pow_two,pow_two]
    exact (Nat.mul_lt_mul_of_pos_left hD (by positivity : 0 < (2:ℕ)^n)).trans_le
      (Nat.mul_le_mul_right _ hD.le)
  exact hm.trans_lt (Nat.mul_lt_mul_of_pos_left hsquare (by positivity))

/-- In every observation interval, the same-error floor holds for the
whole forward window with the same exceptional measure as the bound on
actual first-crossing excursions. -/
theorem gaussian_excursion_window_relative_to_maximum :
    ∃ q : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let x := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
      let P := nearHilbertContinuousCircuitBudget N
      let G := (2:ℝ)^(D^q)
      ∃ m : ℕ, P < m ∧ m ≤ (4*N+1)*(2*N+2)*D^2 ∧ IsRecurrentOrbitCircuitMaximumAt H (1/10) m ∧
        (∀ σ t : ℝ, 9/80 ≤ orbitCircuitDistance H P σ → ∀ s ≤ P/2,
          HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val t) →
          (2:ℝ)^(N-10*N.sqrt) < |σ-t|) ∧
        ∀ b e : ℕ, 16*(b+e) ≤ 7*D → ∀ a T : ℝ, 0 ≤ T →
          (2:ℝ)^e * volume.real ({u | ¬ (IsExcursionWindow H P u ((2:ℝ)^b) G ∧
            MaximumCostWindow H m u ((2:ℝ)^b))} ∩ Icc a (a+T)) ≤ T+G := by
  obtain ⟨q,hq⟩ := gaussian_first_crossing_excursion_occupation
  obtain ⟨_,hmax⟩ := DiagonalSynthesis.gaussian_path_quadratic_maximum_occupation
  refine ⟨q,?_⟩
  filter_upwards [hq,hmax,gaussian_robust_travel_time] with ω hω hmω htω
  filter_upwards [hω,hmω,htω] with k hw hh htravel
  intro N D x H P G
  obtain ⟨m,hlo,hcap,hm,_⟩ := hh
  refine ⟨m,hlo,hcap,hm,htravel,?_⟩
  intro b e hbe a T hT
  have hsets : {u | ¬ (IsExcursionWindow H P u ((2:ℝ)^b) G ∧ MaximumCostWindow H m u ((2:ℝ)^b))} =
      {u | ¬ IsExcursionWindow H P u ((2:ℝ)^b) G} := by
    ext u
    exact not_congr ⟨And.left,fun h => ⟨h,maximum_cost_of_window H hcap h⟩⟩
  rw [hsets]
  exact hw.1 b e hbe a T hT

#print axioms gaussian_excursion_window_relative_to_maximum
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions
