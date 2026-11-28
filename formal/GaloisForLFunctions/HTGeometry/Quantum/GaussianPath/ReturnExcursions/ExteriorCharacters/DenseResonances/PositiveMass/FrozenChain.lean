import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass.Laboratory
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass.Cancellation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor

/-! # Positive real near-resonances at every origin of the frozen chain -/

open Filter MeasureTheory Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
open ElapsedWindow AngularWindings.PhysicalTubes PhaseBoundary.FiniteCertificates.BudgetComparisons
noncomputable section

/-- For every circuit that ever fits, the near-resonant positive real
terms already exceed every fixed multiple of the signed test threshold.
This holds for all origins simultaneously at the first-wait horizon. -/
theorem gaussian_positive_resonant_mass :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ M : ℝ, 0≤M → ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D := 2^K
      let H := generator (pathPauliDisorderShell ω (k+1))
      let w := (11/10:ℝ)^D+clearanceTime H
      let F := (univ : Finset (Fin K → Bool)).powersetCard (D/2)
      let E := H.2.isHermitian.eigenvalues
      let B : ℝ := D.choose (D/2)
      ∀ (σ : ℝ) (C : TwoQubitCircuit K) (v : ℝ), v∈laboratoryDates H C.eval (1/10) →
        M*B^2*(9/10)^D < positiveWindow F (midpointMinor H C.eval (σ+w/2))
          (fun S => ∑ i ∈ S, E i) (D/4) w := by
  obtain ⟨C,hC,hω⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  filter_upwards [hω] with ω hw
  intro M hM
  obtain ⟨N,hN⟩ := eventually_atTop.mp (positive_band C M hM)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hw
  filter_upwards [eventually_ge_atTop J,eventually_ge_atTop N] with k hk hN'
  intro K D H w F E B σ W v hv
  let n := 2^(k+1)
  have hkn : k+1≤n := Nat.lt_two_pow_self.le
  have hd : D=4*n := by dsimp only [D,K,n]; rw [show k+3=(k+1)+2 by omega,pow_add]; ring
  have hq : D/2=2*n := by omega
  have hr : D/4=n := by omega
  have hdim : Fintype.card (Fin K → Bool)=4*n := by
    simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using hd
  have hH := hJ (k+1) (by omega)
  change ‖H.val‖≤C*(K:ℝ) at hH
  have hK : (K:ℝ)≤4*(n:ℝ) := by exact_mod_cast (show K≤4*n by dsimp only [K]; omega)
  have hδ : clearanceTime H≤1 := by
    unfold clearanceTime
    apply (div_le_one (by positivity)).mpr
    linarith only [norm_nonneg H.val]
  have hL : 1≤(11/10:ℝ)^D := one_le_pow₀ (by norm_num)
  have hw₀ : 0≤w := by dsimp [w,clearanceTime]; positivity
  have hw₁ : w≤2*(11/10:ℝ)^(4*n) := by dsimp only [w]; rw [←hd]; linarith only [hδ,hL]
  let a := midpointMinor H W.eval (σ+w/2)
  let V := H.2.isHermitian.eigenvectorUnitary
  have ha (S : Finset (Fin K → Bool)) : ‖a S‖≤1 := by
    dsimp only [a]
    rw [midpoint_norm]
    exact principal_weight_le (V⁻¹*W.eval*V)⁻¹ S
  have hmass := laboratory_weight (I:=Fin K → Bool) H W.eval hv (σ+w/2) (2*n) (by omega)
  rw [hdim,show min (2*n) (4*n-2*n)=2*n by omega] at hmass
  have hh := hN n (by omega) (I:=Fin K → Bool) hdim E ‖H.val‖ w (norm_nonneg _)
    (hH.trans (mul_le_mul_of_nonneg_left hK hC.le)) (abs_eigenvalue_le_l2_opNorm H.2.isHermitian)
    hw₀ hw₁ a (fun S _ => ha S) hmass
  dsimp only [B,F]
  rw [hq,hr,hd]
  exact hh

#print axioms gaussian_positive_resonant_mass

/-- At the original crossing, a signed upper bound at the first-wait
threshold forces a negative real mass exceeding every fixed multiple
of that threshold for every circuit that ever fits. -/
theorem gaussian_original_window_cancellation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ M : ℝ, 0≤M → ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D := 2^K
      let H := generator (pathPauliDisorderShell ω (k+1))
      let σ := Iterated.crossing H (nearHilbertContinuousCircuitBudget K) 0
      let w := (11/10:ℝ)^D+clearanceTime H
      let F := (univ : Finset (Fin K → Bool)).powersetCard (D/2)
      let E := H.2.isHermitian.eigenvalues
      let b := (D.choose (D/2):ℝ)^2*(9/10)^D
      ∀ (C : TwoQubitCircuit K) (v : ℝ), v∈laboratoryDates H C.eval (1/10) →
        windowSum F (circuitMinor H C.eval) E (D/4) σ w ≤ b →
        M*b < negativeWindow F (midpointMinor H C.eval (σ+w/2)) (fun S => ∑ i ∈ S, E i) (D/4) w := by
  filter_upwards [gaussian_positive_resonant_mass] with ω hω
  intro M hM
  filter_upwards [hω (M+1) (by linarith only [hM])] with k hk
  intro K D H σ w F E b C v hv hs
  have h := hk σ C v hv
  have hc := cancellation_bound F (circuitMinor H C.eval) E (D/4) σ w
  let Z := positiveWindow F (midpointMinor H C.eval (σ+w/2)) (fun S => ∑ i ∈ S, E i) (D/4) w
  change (M+1)*(D.choose (D/2):ℝ)^2*(9/10)^D<Z at h
  change Z≤windowSum F (circuitMinor H C.eval) E (D/4) σ w +
    negativeWindow F (midpointMinor H C.eval (σ+w/2)) (fun S => ∑ i ∈ S, E i) (D/4) w at hc
  have h' : (M+1)*b<Z := by simpa only [b,mul_assoc] using h
  linarith only [h',hc,hs]

#print axioms gaussian_original_window_cancellation
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
