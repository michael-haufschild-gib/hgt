import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.UniformOverlap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.PhysicalFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.PhysicalWindow

/-! # Fixed-error physical gate density from startup through every bounded time -/
open MeasureTheory Set Filter Matrix GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- A circuit fitting in operator norm has a large Choi overlap. Its
component partition supplies the cut which charges its gate count. -/
theorem gate_floor_of_cut {n s : ℕ} {ω : PathPauliDisorder} {t η ε : ℝ}
    (hn : ω∉cutOverlapEvent n t (η/2) (1-ε^2/2))
    (hs : HasProjectiveCircuitApproximation (n+2) ε s
      (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t)) :
    (1-η)*(n+1:ℕ)<(s:ℝ) := by
  obtain ⟨z,hz,C,hC,hfit⟩ := hs
  obtain ⟨c,hcut⟩ := many_crossed C
  have hc : ((n+1:ℕ):ℝ)≤(C.gateCount:ℝ)+2*((crossed c).card:ℝ) := by exact_mod_cast hcut
  by_contra! h
  apply hn ⟨C,c,?_,overlap_of_fit _ _ (unitaryEvolution_mem_unitary
    (isSelfAdjoint_pathHamiltonian _) t) C.eval.property z hz hfit⟩
  linarith only [hc,h,show (C.gateCount:ℝ)≤(s:ℝ) from Nat.cast_le.mpr hC]

/-- On a compact positive interval the gate floor holds simultaneously
at all real observation dates on almost every fixed Gaussian chain. -/
theorem gaussian_uniform_gate_floor {a T η ε : ℝ} (ha : 0<a) (hη : 0<η)
    (hε : 0≤ε) (hε' : ε<Real.sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T, ∀ s : ℕ,
      HasProjectiveCircuitApproximation (n+2) ε s (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
      (1-η)*(n+1:ℕ)<(s:ℝ) := by
  let κ := 1-ε^2/2
  have hκ : 0<κ := overlap_threshold_pos hε hε'
  filter_upwards [gaussian_uniform_cut_overlap (T:=T) ha (half_pos hη) hκ] with ω hω
  filter_upwards [hω] with n hn
  intro t ht s hs
  exact gate_floor_of_cut (hn t ht) hs

/-- A single event and onset constant give the physical lower gate density
through every bounded signed horizon, beginning at inverse system size. -/
theorem gaussian_all_bounded_horizons {η : ℝ} (hη : 0<η) :
    ∃ A>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ T : ℝ, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      A ≤ |t| *(n+1:ℕ) → |t|≤T → ∀ s : ℕ,
      HasProjectiveCircuitApproximation (n+2) (1/4) s (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
      (1-η)*(n+1:ℕ)<(s:ℝ) := by
  obtain ⟨A,b,hA,hb,hsmall⟩ := LocalEcho.gaussian_physical_window η hη
  have hε : (1/4:ℝ)<Real.sqrt 2 := (lt_of_lt_of_le (by norm_num : (1/4:ℝ)<1)
    (Real.one_le_sqrt.mpr (by norm_num)))
  have hall (K : ℕ) := gaussian_uniform_gate_floor (T:=(K:ℝ)) hb hη (by norm_num : (0:ℝ)≤1/4) hε
  refine ⟨A,hA,?_⟩
  filter_upwards [hsmall,ae_all_iff.mpr hall] with ω hω hf
  intro T
  obtain ⟨K,hK⟩ := exists_nat_gt T
  filter_upwards [hω,hf K] with n hn hn'
  intro t ht ht' s hs
  by_cases hb' : |t|≤b
  · exact hn t ht hb' s hs
  · apply hn' |t| ⟨le_of_not_ge hb',(ht'.trans hK.le)⟩ s
    rcases le_total 0 t with h|h
    · rwa [abs_of_nonneg h]
    · rw [abs_of_nonpos h]
      let H : selfAdjoint (Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ) :=
        ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
      exact hs.neg_time H

/-- The same exclusion holds around every low-cost visit. At any bounded
separation above the inverse-size onset the two budgets together exceed
the floor, independently of how both dates were selected. -/
theorem gaussian_bounded_lag_floor {η : ℝ} (hη : 0<η) :
    ∃ A>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ T : ℝ, ∀ᶠ n : ℕ in atTop,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ v w : ℝ, A ≤ |w-v| *(n+1:ℕ) → |w-v|≤T → ∀ j s : ℕ, ∀ ε δ : ℝ, ε+δ≤1/4 →
      HasProjectiveCircuitApproximation (n+2) ε j (unitaryEvolution H v) →
      HasProjectiveCircuitApproximation (n+2) δ s (unitaryEvolution H w) →
      (1-η)*(n+1:ℕ)<((j+s:ℕ):ℝ) := by
  obtain ⟨A,hA,h⟩ := gaussian_all_bounded_horizons hη
  refine ⟨A,hA,?_⟩
  filter_upwards [h] with ω hω
  intro T
  filter_upwards [hω T] with n hn
  intro _ v w hlate hT j s ε δ hε hv hw
  let H : selfAdjoint (Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ) :=
    ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  apply hn (w-v) hlate hT (j+s)
  have he := affordable_add_time H (x := -v) (y := w) (i := j) (j := s) (hv.neg_time H) hw
  rw [show -v+w=w-v by ring] at he
  obtain ⟨z,hz,C,hC,hfit⟩ := he
  exact ⟨z,hz,C,hC,hfit.trans hε⟩

#print axioms gaussian_uniform_gate_floor
#print axioms gaussian_all_bounded_horizons
#print axioms gaussian_bounded_lag_floor
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
