import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseFluctuations.PhysicalOccupation

/-! # Separation of two long-time gate-count quantiles at one error -/
open MeasureTheory Set Filter Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseFluctuations
open DiagonalSynthesis SharpOccupation
noncomputable section

private theorem separated_tails {p q a b m K : ℝ} (hp : p ∈ Icc 0 1) (hq : q ∈ Icc 0 1)
    (hab : a ≤ b) (hK : 0 < K)
    (hlo : ∀ u, 0 ≤ u → a+u ≤ m → p ≤ exp (-u^2/K))
    (hhi : ∀ u, 0 ≤ u → m+u ≤ b → q ≤ exp (-u^2/K)) :
    p*q ≤ exp (-(b-a)^2/(2*K)) := by
  let x := max 0 (m-a)
  let y := max 0 (b-m)
  have hx : p ≤ exp (-x^2/K) := by
    by_cases h : a ≤ m
    · rw [show x=m-a from max_eq_right (sub_nonneg.mpr h)]
      exact hlo _ (sub_nonneg.mpr h) (by linarith only)
    · simpa only [x,max_eq_left (sub_nonpos.mpr (le_of_not_ge h)),zero_pow (by decide : 2≠0),
        neg_zero,zero_div,exp_zero] using hp.2
  have hy : q ≤ exp (-y^2/K) := by
    by_cases h : m ≤ b
    · rw [show y=b-m from max_eq_right (sub_nonneg.mpr h)]
      exact hhi _ (sub_nonneg.mpr h) (by linarith only)
    · simpa only [y,max_eq_left (sub_nonpos.mpr (le_of_not_ge h)),zero_pow (by decide : 2≠0),
        neg_zero,zero_div,exp_zero] using hq.2
  have hg : b-a ≤ x+y := by
    have h := add_le_add (le_max_right 0 (m-a)) (le_max_right 0 (b-m))
    linarith only [h]
  have hsq := pow_le_pow_left₀ (sub_nonneg.mpr hab) hg 2
  refine (mul_le_mul hx hy hq.1 (exp_pos _).le).trans ?_
  rw [←exp_add,exp_le_exp,←add_div,show -(b-a)^2/(2*K)=(-(b-a)^2/2)/K by ring]
  apply div_le_div_of_nonneg_right _ hK.le
  nlinarith only [hsq,sq_nonneg (x-y)]

/-- At the same fixed error, the product of the fraction of visits costing
at most a and the fraction costing more than b decays quadratically
in the gap b+1−a. Both fractions are measured on the same frozen orbit. -/
theorem gaussian_quantile_separation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (Register N) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ ε : ℝ, 0 ≤ ε → ∃ F : ℕ → ℝ,
        (∀ (s : ℕ) (v : ℝ → ℝ), Tendsto (fun T => visitFraction H s ε (v T) (v T+T)) atTop (𝓝 (F s))) ∧
        ∀ a b : ℕ, a ≤ b+1 → F a*(1-F b) ≤
          exp (-((b:ℝ)+1-a)^2/(((2^N-1:ℕ):ℝ)*(eigenphaseCost N:ℝ)^2)) := by
  filter_upwards [PhaseBoundary.gaussian_uniform_affordable_fraction,gaussian_gate_count_fluctuations]
    with ω hw hf k
  intro N H ε hε
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let F (s : ℕ) := volume.real (projectiveContinuousCircuitCaptureTarget e V s ε)
  have hprob (s : ℕ) : F s ∈ Icc (0:ℝ) 1 := by
    letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
    exact ⟨ENNReal.toReal_nonneg,(measureReal_mono (μ:=volume) (subset_univ _) (measure_ne_top _ _)).trans_eq probReal_univ⟩
  have hlim (s : ℕ) (v : ℝ → ℝ) :
      Tendsto (fun T => visitFraction H s ε (v T) (v T+T)) atTop (𝓝 (F s)) := hw k s ε v
  refine ⟨F,hlim,?_⟩
  intro a b hab
  obtain ⟨p,hp,ha⟩ := hf k ε hε a
  obtain ⟨q,hq,hb⟩ := hf k ε hε b
  have ep : p=F a := tendsto_nhds_unique (hp (fun _ => 0)) (hlim a (fun _ => 0))
  have eq : q=F b := tendsto_nhds_unique (hq (fun _ => 0)) (hlim b (fun _ => 0))
  rw [ep] at ha
  rw [eq] at hb
  let d := ((2^N-1:ℕ):ℝ)
  let L := (eigenphaseCost N:ℝ)
  have hd : 0 < d := by
    change (0:ℝ) < ((2^(k+3)-1:ℕ):ℝ)
    exact_mod_cast (Nat.sub_pos_of_lt (one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by omega : k+3≠0)))
  have hL : 0 < L := by dsimp only [L,eigenphaseCost]; positivity
  have h := separated_tails (hprob a)
    (show 1-F b ∈ Icc (0:ℝ) 1 from ⟨sub_nonneg.mpr (hprob b).2,sub_le_self _ (hprob b).1⟩)
    (by exact_mod_cast hab : (a:ℝ) ≤ (b:ℝ)+1)
    (by positivity : 0 < 2*(d*(L/2)^2))
    (fun u hu h => (ha u hu).1 h) (fun u hu h => (hb u hu).2 h)
  change F a*(1-F b) ≤ exp (-((b:ℝ)+1-a)^2/(d*L^2))
  rwa [show 2*(2*(d*(L/2)^2))=d*L^2 by ring] at h

#print axioms gaussian_quantile_separation
end
end GaloisForLFunctions.HTGeometry.PhaseFluctuations
