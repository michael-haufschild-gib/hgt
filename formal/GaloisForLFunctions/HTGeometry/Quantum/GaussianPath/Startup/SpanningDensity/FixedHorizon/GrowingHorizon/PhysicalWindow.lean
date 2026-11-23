import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.Diagonal
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.PhysicalWindow

/-! # A physical gate floor through a diverging deterministic horizon -/
open MeasureTheory Set Filter Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- The permitted error can approach √2 as the window expands. Every
fitting circuit then needs almost one gate per physical bond. -/
theorem gaussian_expanding_gate_floor :
    ∃ L : ℕ → ℕ, Monotone L ∧ Tendsto L atTop atTop ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (1/(L n:ℝ)) (L n:ℝ),
      ∀ (ε : ℝ) (s : ℕ), 1/(L n:ℝ) ≤ 1-ε^2/2 →
      HasProjectiveCircuitApproximation (n+2) ε s
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
      (1-2/(L n:ℝ))*(n+1:ℕ) < (s:ℝ) := by
  obtain ⟨L,hm,hL,h⟩ := gaussian_expanding_cut_window
  refine ⟨L,hm,hL,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  intro t ht ε s hε hfit
  obtain ⟨z,hz,C,hC,her⟩ := hfit
  obtain ⟨c,hc⟩ := many_crossed C
  have hp := overlap_of_fit _ _ (unitaryEvolution_mem_unitary
    (isSelfAdjoint_pathHamiltonian _) t) C.eval.property z hz her
  have hsmall : ((crossed c).card:ℝ) < (1/(L n:ℝ))*(n+1:ℕ) := by
    by_contra! hlarge
    exact hn t ht ⟨C,c,hlarge,hε.trans hp⟩
  have hc' : ((n+1:ℕ):ℝ) ≤ (C.gateCount:ℝ)+2*((crossed c).card:ℝ) := by exact_mod_cast hc
  simp only [div_eq_mul_inv] at hsmall ⊢
  linarith only [hc',hsmall,show (C.gateCount:ℝ) ≤ (s:ℝ) from Nat.cast_le.mpr hC]

/-- At physical error 1/4 the floor starts at inverse system size.
The deterministic upper horizon is shared by all choices of the density. -/
theorem gaussian_expanding_from_startup :
    ∃ L : ℕ → ℕ, Monotone L ∧ Tendsto L atTop atTop ∧ ∀ η : ℝ, 0 < η →
      ∃ A > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
        A ≤ |t| *(n+1:ℕ) → |t| ≤ (L n:ℝ) → ∀ s : ℕ,
        HasProjectiveCircuitApproximation (n+2) (1/4) s
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
        (1-η)*(n+1:ℕ)<(s:ℝ) := by
  obtain ⟨L,hm,hL,h⟩ := gaussian_expanding_gate_floor
  refine ⟨L,hm,hL,?_⟩
  intro η hη
  obtain ⟨A,hA,hstart⟩ := gaussian_all_bounded_horizons hη
  refine ⟨A,hA,?_⟩
  obtain ⟨k,hk⟩ := exists_nat_gt (max 2 (2/η))
  filter_upwards [h,hstart] with ω hw hω
  filter_upwards [hw,hω 1,hL.eventually (eventually_ge_atTop k)] with n hn ha hk'
  intro t hlate hend s hs
  by_cases ht : |t|≤1
  · exact ha t hlate ht s hs
  have hlong := hk.trans_le (Nat.cast_le.mpr hk')
  have h₂ : (2:ℝ) < L n := (le_max_left ..).trans_lt hlong
  have hpos : 0 < (L n:ℝ) := (by norm_num : (0:ℝ)<2).trans h₂
  have hd : 2/(L n:ℝ) ≤ η := (div_le_iff₀ hpos).mpr (by
    have hq := (div_lt_iff₀ hη).mp ((le_max_right ..).trans_lt hlong)
    linarith only [hq])
  have hsmall : 1/(L n:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) h₂.le
  have hfit : HasProjectiveCircuitApproximation (n+2) (1/4) s
      (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) |t|) := by
    rcases le_total 0 t with ht' | ht'
    · rwa [abs_of_nonneg ht']
    · rw [abs_of_nonpos ht']
      let H : selfAdjoint (Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ) :=
        ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
      exact hs.neg_time H
  apply (mul_le_mul_of_nonneg_right (sub_le_sub_left hd 1) (Nat.cast_nonneg (n+1))).trans_lt
  exact hn |t| ⟨hsmall.trans ((by norm_num : (1/2:ℝ)≤1).trans (le_of_not_ge ht)),hend⟩
    (1/4) s (hsmall.trans (by norm_num)) hfit

#print axioms gaussian_expanding_from_startup
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
