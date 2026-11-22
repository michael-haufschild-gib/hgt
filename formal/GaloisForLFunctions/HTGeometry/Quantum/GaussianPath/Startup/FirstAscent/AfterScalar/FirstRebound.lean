import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.AfterScalar.ExitWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingWidth

/-! # Replay of the first ascent at the first deep return after the robust crossing -/
open Filter MeasureTheory Real Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.AfterScalar
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- An inverse-square scalar entry replays the sharp first-exit delay
simultaneously for every budget up to a fixed fraction of the prefix. -/
theorem gaussian_deep_return_exit :
    ∃ c C : ℝ, ∃ M : ℕ, 0 < c ∧ 0 < C ∧ 0 < M ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let N := n+2
        let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
        let W := circuitHamiltonianSpectralWidth H
        ∀ v : ℝ, HasProjectiveCircuitApproximation N (1/(N:ℝ)^2) 0 (unitaryEvolution H.val v) →
          ∀ s : ℕ, 0 < s → M*s ≤ N →
            let F := (s:ℝ)*sqrt (log ((N:ℝ)/s))/(N:ℝ)^2
            exitLag H s v-4*arcsin (1/20)/W ∈ Icc (c*F) (C*F) := by
  obtain ⟨c,C,a,m,hc,hC,ha,hm,hw⟩ := gaussian_exit_lag_with_margin
  let θ := arcsin (1/20)
  have hθ : 0 < θ := arcsin_pos.mpr (by norm_num)
  let d := sqrt (log 2)
  have hd : 0 < d := sqrt_pos.mpr (log_pos (by norm_num))
  obtain ⟨L,hL⟩ := exists_nat_ge (max (2/θ) (8/(a*c*d)))
  refine ⟨c/2,C+c/2,max m 2,half_pos hc,add_pos hC (half_pos hc),hm.trans_le (le_max_left ..),?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω,eventually_ge_atTop L] with n hn hnL
  intro N H W v hv s hs hsize F
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  have hone : (1:ℝ) ≤ N := by dsimp [N]; exact_mod_cast (by omega : 1 ≤ n+2)
  have hLN : (L:ℝ) ≤ N := by dsimp [N]; exact_mod_cast (by omega : L ≤ n+2)
  have haN := (mul_pos ha hN).trans_le hn.1
  have hsize' := (Nat.mul_le_mul_right s (le_max_left m 2)).trans hsize
  have hsize₂ := (Nat.mul_le_mul_right s (le_max_right m 2)).trans hsize
  have hs' : 0 < (s:ℝ) := by exact_mod_cast hs
  have hr : (2:ℝ) ≤ (N:ℝ)/s := (le_div_iff₀ hs').mpr (by exact_mod_cast hsize₂)
  have hfd : d ≤ (s:ℝ)*sqrt (log ((N:ℝ)/s)) := by
    have h := sqrt_le_sqrt (log_le_log (by norm_num) hr)
    exact h.trans (le_mul_of_one_le_left (sqrt_nonneg _) (by exact_mod_cast (show 1 ≤ s by omega)))
  have hθ' := (div_le_iff₀ hθ).mp ((le_max_left ..).trans (hL.trans hLN))
  have hδ : 1/(N:ℝ)^2 ∈ Icc 0 (θ/2) := by
    refine ⟨by positivity,(div_le_iff₀ (sq_pos_of_pos hN)).mpr ?_⟩
    have hpow : (N:ℝ) ≤ (N:ℝ)^2 := by simpa only [mul_one,pow_two] using mul_le_mul_of_nonneg_left hone hN.le
    have hsq := mul_le_mul_of_nonneg_left hpow hθ.le
    linarith only [hθ',hsq]
  have hK := (div_le_iff₀ (mul_pos (mul_pos ha hc) hd)).mp ((le_max_right ..).trans (hL.trans hLN))
  have hp : 8 ≤ W*(c*((s:ℝ)*sqrt (log ((N:ℝ)/s)))) := by
    have h := mul_le_mul hn.1 (mul_le_mul_of_nonneg_left hfd hc.le) (mul_nonneg hc.le hd.le) haN.le
    linarith only [hK,h]
  have herror : 4*(1/(N:ℝ)^2)/W ≤ c/2*F := by
    have hcoef : 4/W ≤ c/2*((s:ℝ)*sqrt (log ((N:ℝ)/s))) := (div_le_iff₀ haN).mpr (by linarith only [hp])
    calc 4*(1/(N:ℝ)^2)/W = (4/W)/(N:ℝ)^2 := by ring
         _ ≤ (c/2*((s:ℝ)*sqrt (log ((N:ℝ)/s))))/(N:ℝ)^2 := div_le_div_of_nonneg_right hcoef (sq_nonneg _)
         _ = _ := by dsimp only [F]; ring
  have h := hn.2 s hs hsize' _ hδ v hv
  change exitLag H s v-4*arcsin (1/20)/W ∈ Icc (c*F-4*(1/(N:ℝ)^2)/W) (C*F+4*(1/(N:ℝ)^2)/W) at h
  exact ⟨by linarith only [h.1,herror],by linarith only [h.2,herror]⟩

/-- The deep entry may specifically be the first one from the actual
first 9/80 crossing of the near-Hilbert budget. -/
theorem gaussian_first_post_crossing_rebound :
    ∃ c C : ℝ, ∃ M : ℕ, 0 < c ∧ 0 < C ∧ 0 < M ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        let P := nearHilbertContinuousCircuitBudget N
        let W := circuitHamiltonianSpectralWidth H
        ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
          (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
          let v := PrecisionReturns.firstVisit H σ 0 (1/(N:ℝ)^2)
          ∀ s : ℕ, 0 < s → M*s ≤ N →
            let F := (s:ℝ)*sqrt (log ((N:ℝ)/s))/(N:ℝ)^2
            exitLag H s v-4*arcsin (1/20)/W ∈ Icc (c*F) (C*F) := by
  obtain ⟨c,C,M,hc,hC,hM,h⟩ := gaussian_deep_return_exit
  refine ⟨c,C,M,hc,hC,hM,?_⟩
  filter_upwards [h,LocalPatches.gaussian_first_crossing_local_width] with ω he hw
  filter_upwards [(tendsto_add_atTop_nat 1).eventually he,hw] with k hk hc'
  intro N H P W
  obtain ⟨σ,hσ,heq,hpre,_⟩ := hc'
  have hpos := (show 0 ≤ LocalPatches.localCrossingWidth N by
    unfold LocalPatches.localCrossingWidth; positivity).trans_lt hσ
  refine ⟨σ,hpos,heq,hpre,?_⟩
  intro v
  exact hk v (PrecisionReturns.firstVisit_isLeast H σ 0 (show 0 < 1/(N:ℝ)^2 by dsimp [N]; positivity)).1.2

#print axioms gaussian_first_post_crossing_rebound
end
end GaloisForLFunctions.HTGeometry.FirstAscent.AfterScalar
