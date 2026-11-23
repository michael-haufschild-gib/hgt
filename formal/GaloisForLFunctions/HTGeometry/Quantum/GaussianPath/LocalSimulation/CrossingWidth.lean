import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.VolumeBound
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.InitialDeadline

/-! # Physical travel time from a low-cost circuit to the first robust crossing -/
open Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Travel width paid by the local physical simulation at Hilbert-space dimension 2^N. -/
def localCrossingWidth (N : ℕ) : ℝ :=
  (2:ℝ)^N / (2^(5*N.sqrt+26)*((N:ℝ)+1)^2)

private theorem width_one_le (N : ℕ) (hh : 64 ≤ N.sqrt) : 1 ≤ localCrossingWidth N := by
  let h := N.sqrt
  have hpoly := ReturnExcursions.dimension_dominates_speed hh
  change 64*(h+1)^2 ≤ 2^h at hpoly
  have hN : N+1 ≤ (h+1)^2 := by rw [pow_two]; exact Nat.lt_succ_sqrt N
  have hN' : N+1 ≤ 2^h := hN.trans (le_trans (by omega) hpoly)
  have hexp : 5*h+26+2*h ≤ N := by
    have hz : 8*h ≤ h*h := Nat.mul_le_mul_right h (by omega)
    have hsq := Nat.sqrt_le N
    change h*h ≤ N at hsq
    omega
  have hf : (2:ℕ)^(5*h+26)*(N+1)^2 ≤ 2^N := calc
    _ ≤ 2^(5*h+26)*(2^h)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN' 2)
    _ = 2^(5*h+26+2*h) := by rw [pow_add (2:ℕ) (5*h+26) (2*h),←pow_mul,Nat.mul_comm h 2]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp
  unfold localCrossingWidth
  apply (le_div_iff₀ (by positivity)).mpr
  rw [one_mul]
  exact_mod_cast hf

/-- A bounded duration fits both the binary spacetime schedule and its
half-budget payment inequality. -/
theorem local_width_budget {N : ℕ} (hs : 64 ≤ N.sqrt) (hN : 1 ≤ (N:ℝ))
    {t : ℝ} (ht : 0 ≤ t) (hnear : t ≤ localCrossingWidth N) :
    (N:ℝ)*(1+t) ≤ (2:ℝ)^N ∧
      ∀ g : ℕ, (g:ℝ) ≤ (N:ℝ)*(1+t)*2^(5*N.sqrt+17) → 2*g ≤ nearHilbertContinuousCircuitBudget N := by
  let B := localCrossingWidth N
  let F := (2:ℝ)^(5*N.sqrt+17)
  have hF : 1 ≤ F := one_le_pow₀ (by norm_num)
  have hB := width_one_le N hs
  change 1 ≤ B at hB
  have hcancel : 512*F*((N:ℝ)+1)^2*B = (2:ℝ)^N := by
    dsimp [B,localCrossingWidth,F]
    rw [show 5*N.sqrt+26 = (5*N.sqrt+17)+9 by omega,pow_add (2:ℝ) _ 9]
    field_simp
    ring
  have hT : 1+t ≤ 2*B := by linarith only [hnear,hB]
  have hb : 128*((N:ℝ)+1)*((N:ℝ)*(1+t)*F) ≤ (2:ℝ)^N := calc
    _ ≤ 128*((N:ℝ)+1)*((N:ℝ)*(2*B)*F) := by gcongr
    _ ≤ 512*F*((N:ℝ)+1)^2*B := by
      have hmul := mul_nonneg (mul_nonneg (show 0 ≤ F by positivity) (show 0 ≤ B by positivity))
        (show 0 ≤ 256*((N:ℝ)+1)*((N:ℝ)+2) by positivity)
      nlinarith only [hmul]
    _ = _ := hcancel
  have hvol : (N:ℝ)*(1+t) ≤ (2:ℝ)^N := by
    apply le_trans _ hb
    calc
      _ ≤ (N:ℝ)*(1+t)*F := le_mul_of_one_le_right (by positivity) hF
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (by linarith only [hN])
  refine ⟨hvol,?_⟩
  intro j hcost
  change 2*j ≤ 2^N/(64*(N+1))
  apply (Nat.le_div_iff_mul_le (by positivity)).mpr
  have h := (mul_le_mul_of_nonneg_left hcost (show 0 ≤ 128*((N:ℝ)+1) by positivity)).trans hb
  have h' : 2*(j:ℝ)*(64*((N:ℝ)+1)) ≤ (2:ℝ)^N := by linarith only [h]
  exact_mod_cast h'

/-- Uniform lower separation in physical time for every robust point and
every affordable half-budget point of the same fixed trajectory. -/
theorem gaussian_local_travel_at_error :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let x := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∀ ε : ℝ, ε+1/100 < 9/80 → ∀ σ t : ℝ, 9/80 ≤ orbitCircuitDistance H P σ → ∀ s ≤ P/2,
        HasProjectiveCircuitApproximation N ε s (unitaryEvolution H.val t) →
          localCrossingWidth N < |σ-t| := by
  filter_upwards [gaussian_path_spacetime_upper] with ω hw
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hw,eventually_ge_atTop (64*64)] with k hc hk
  intro N x H P ε hε σ t hhard s hs ht
  have hN : 1 ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by dsimp [N]; omega)
  by_contra! hnear
  obtain ⟨hvol,hb⟩ := local_width_budget (N:=N) (Nat.le_sqrt.mpr (by dsimp [N]; omega))
    hN (abs_nonneg _) hnear
  obtain ⟨j,hj,hcost⟩ := hc (σ-t) N hvol
  have hpaid := hb j hcost
  have hsep : ProjectiveCircuitSeparated N (ε+1/100) P (unitaryEvolution H.val σ) := by
    intro z hz C hC
    by_contra! he
    have hd : orbitCircuitDistance H P σ ≤ ε+1/100 :=
      (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp ⟨z,hz,C,hC,he⟩
    exact hε.not_ge (hhard.trans hd)
  have h := projectiveCircuitSeparated_unitaryEvolution_backward_cone H (show j ≤ P by omega)
    hsep hj (show ε+1/100 ≤ ε+1/100 from le_rfl)
  rw [show σ-(σ-t)=t by ring] at h
  obtain ⟨z,hz,C,hC,he⟩ := ht
  exact (h z hz C (hC.trans (by omega))).not_ge he

/-- The physical error leaves room for the local increment simulator. -/
theorem gaussian_local_robust_travel_time :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let x := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∀ σ t : ℝ, 9/80 ≤ orbitCircuitDistance H P σ → ∀ s ≤ P/2,
        HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val t) →
          localCrossingWidth N < |σ-t| := by
  filter_upwards [gaussian_local_travel_at_error] with ω hw
  filter_upwards [hw] with k hk
  exact hk (1/10) (by norm_num)

#print axioms gaussian_local_travel_at_error

/-- The true first robust crossing from the identity and its first subsequent
low-budget visit each require a full local-simulation travel width. -/
theorem gaussian_first_crossing_local_width :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let x := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ : ℝ, localCrossingWidth N < σ ∧ orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∀ s ≤ P/2, ∃ v : ℝ, σ+localCrossingWidth N < v ∧
          IsLeast {t | σ ≤ t ∧ HasProjectiveCircuitApproximation N (1/10:ℝ) s
            (unitaryEvolution H.val t)} v := by
  obtain ⟨_,hfirst⟩ := ReturnExcursions.gaussian_initial_crossing_short_return_tradeoff
  filter_upwards [hfirst,gaussian_local_robust_travel_time] with ω hf hw
  filter_upwards [hf,hw] with k hc htravel
  intro N x H P
  obtain ⟨σ,hσ,he,hprior,_,hnext⟩ := hc
  have hσ0 : 0 ≤ σ := (by positivity : (0:ℝ) ≤ 2^(N-10*N.sqrt)).trans hσ.le
  have hid : HasProjectiveCircuitApproximation N (1/10:ℝ) 0 (unitaryEvolution H.val 0) := by
    refine ⟨1,norm_one,TwoQubitCircuit.one N,by rfl,?_⟩
    simp [TwoQubitCircuit.one_eval,unitaryEvolution]
  have hw0 := htravel σ 0 he.ge 0 (Nat.zero_le _) hid
  rw [sub_zero,abs_of_nonneg hσ0] at hw0
  refine ⟨σ,hw0,he,hprior,?_⟩
  intro s hs
  obtain ⟨v,_,hv,_,_⟩ := hnext s hs
  have hwv := htravel σ v he.ge s hs hv.1.2
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hv.1.1)] at hwv
  exact ⟨v,by linarith only [hwv],hv⟩

#print axioms gaussian_local_robust_travel_time
#print axioms gaussian_first_crossing_local_width
end
end GaloisForLFunctions.HTGeometry.LocalPatches
