import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.PrefixTest
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.WindowOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.WaitingWidth

/-! # Doubly exponential first waiting times from prescribed late dates -/
open Matrix Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
open SpectralJets
noncomputable section

/-- At every sequence of sufficiently late dates prescribed independently of
the disorder, almost every chain eventually has a doubly exponential first
waiting time for every budget through half the robust threshold. The cheap
circuit may depend on the disorder and on the time. -/
theorem gaussian_path_prescribed_late_first_wait :
    ∃ c : ℕ, ∀ t : ℕ → ℝ, (∀ᶠ k : ℕ in atTop, 2*(2:ℝ)^((2^(k+3):ℕ)^c) ≤ t k) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let u := pathPauliDisorderShell ω (k+1)
        let H : selfAdjoint (Matrix (Fin N → Bool) (Fin N → Bool) ℂ) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
        ∀ s ≤ excursionGateBudget N,
          t k+(2:ℝ)^(D/4096) < firstCircuitVisit H s (t k) ∧
          firstCircuitVisit H s (t k) ≤ t k+(2:ℝ)^(D^c) := by
  obtain ⟨c,hbound⟩ := derivativePhaseHorizon_double_upper
  refine ⟨c,fun t hlate => ?_⟩
  let b (k : ℕ) := (2:ℝ)^(2^(k+3)/4096)
  let r (k : ℕ) := excursionGateBudget (k+3)
  let q (k : ℕ) := ⌈t k⌉₊+1
  have htest := gaussian_path_eventually_outside_dilation_test t b r q (fun k => Nat.succ_pos _)
  filter_upwards [htest,gaussian_path_derivative_phase_filling,gaussian_path_eventual_double_exponential_width] with ω hω hf hw
  have hN : Tendsto (fun k : ℕ => k+3) atTop atTop := tendsto_add_atTop_nat 3
  filter_upwards [hω,hf,hw,hlate,eventually_ge_atTop 64,
    hN.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier]
    with k htest hfill hwidth ht hk hent
  intro N D u H
  let M := (2:ℝ)^(D/1024)
  let G := (2:ℝ)^(D^c)
  let W := translatedExcursionWidth N ‖H.val‖
  let x : PrefixIndex (k+1) → ℝ := fun i => u (pathCoeffEquiv (k+1) i)
  let E := prescribedWindowEvent (k+1) (r k) (t k) (b k)
  let C := {v | HasProjectiveCircuitApproximation N (1/10:ℝ) (r k) (unitaryEvolution H.val v)}
  obtain ⟨e,he⟩ := hfill
  have hphase (a : ℝ) (z : Fin (D-1) → ℝ) : ∃ v ∈ Icc a (a+G), ∀ j,
      turnDist (v*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-z j) < 1/80 := by
    obtain ⟨v,hv,hh⟩ := he a z
    exact ⟨v,⟨hv.1,hv.2.trans (add_le_add le_rfl (hbound k))⟩,hh⟩
  have hG : 0 < G := by dsimp [G]; positivity
  have hM : M ≤ ((r k:ℝ)+1)^(r k) := by
    change (2:ℝ)^(D/1024) ≤ ((r k:ℝ)+1)^(r k)
    exact_mod_cast (circuit_return_spacing_factor_bounds (by dsimp [N]; omega : 64 ≤ N)).1
  have hocc (A T : ℝ) (hT : 0 ≤ T) :
      M*volume.real ({u | ∃ y ∈ Icc u (u+W), y ∈ C} ∩ Icc A (A+T)) ≤ T+G :=
    (mul_le_mul_of_nonneg_right hM ENNReal.toReal_nonneg).trans
      (excursion_occupation_at_phase_horizon (n := N) (by change 1 ≤ k+3; omega) e H hG.le hent
        (fun z => by simpa only [zero_add] using hphase 0 z) A T hT)
  have hgen : numberedGenerator (k+1) x = H.val := numberedGenerator_shell u
  have hmiss : x ∉ E := by
    intro hx
    apply htest
    refine ⟨hx,mem_iInter.mpr fun i => ?_⟩
    apply rayGrid_count_of_window_occupation i E x C (t := t k) (b := b k) (G := G) (W := W) (M := M)
      ((mul_pos (by norm_num) hG).trans_le ht) (by dsimp [b]; positivity) _ ht
      ((prescribed_width_fits k hk).trans hwidth) (by dsimp [M]; positivity) _ hocc
    · exact (Nat.le_ceil _).trans (by dsimp [q]; push_cast; linarith)
    · intro a ha hh
      obtain ⟨y,hy,hY⟩ := dilation_window_hit ha x hh
      refine ⟨y,hy,?_⟩
      change HasProjectiveCircuitApproximation (k+1+2) (1/10:ℝ) (r k) (unitaryEvolution H.val y)
      simpa only [hgen] using hY
  intro s hs
  constructor
  · by_contra! h
    have hh : t k ∈ {a | firstCircuitVisit H s a ≤ a+b k} := h
    rw [← circuitWindowHits_eq_firstVisit] at hh
    obtain ⟨v,hv,z,hz,Y,hY,herr⟩ := hh
    exact hmiss ⟨v,hv,z,hz,Y,hY.trans hs,by simpa only [hgen] using herr⟩
  · change t k ∈ {a | firstCircuitVisit H s a ≤ a+G}
    rw [← circuitWindowHits_eq_firstVisit]
    obtain ⟨v,hv,z,hz,Y,hY,herr⟩ := phase_interval_contains_zero_gate e H (t k) (t k+G) (hphase (t k))
    exact ⟨v,hv,z,hz,Y,hY.trans (Nat.zero_le s),herr⟩

#print axioms gaussian_path_prescribed_late_first_wait
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
