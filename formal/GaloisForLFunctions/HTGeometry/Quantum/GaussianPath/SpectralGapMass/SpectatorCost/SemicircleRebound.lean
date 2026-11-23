import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.ExponentialFloor
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.CommonBasisLag
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Extensive basis-independent rebound around a scalar return -/
open Matrix Real MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

private theorem semicircle_displacement {N : ℕ} (H : selfAdjoint (Reg N)) {t : ℝ}
    (hl : π/3 ≤ t*circuitHamiltonianSpectralWidth H) (hu : t*circuitHamiltonianSpectralWidth H ≤ π) :
    1/2 ≤ ‖1-unitaryEvolution H.val t‖ := by
  let W := circuitHamiltonianSpectralWidth H
  have hsin := sin_le_sin_of_le_of_le_pi_div_two (by linarith only [pi_pos] : -(π/2) ≤ π/6)
    (by dsimp only [W]; linarith only [hu] : t*(W/2) ≤ π/2)
    (by dsimp only [W]; linarith only [hl] : π/6 ≤ t*(W/2))
  rw [sin_pi_div_six] at hsin
  have he : HasProjectiveCircuitApproximation N ‖1-unitaryEvolution H.val t‖ 0 (unitaryEvolution H.val t) := by
    refine ⟨1,norm_one,TwoQubitCircuit.one _,le_rfl,?_⟩
    rw [TwoQubitCircuit.one_eval,one_smul]
    exact (norm_sub_rev (unitaryEvolution H.val t) 1).le
  have hdist := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp he
  exact ((hsin.trans (le_abs_self _)).trans (abs_sin_spectralWidth_le_zeroGateDistance H t)).trans hdist

/-- Over a fixed part of the first spectral semicircle the sum of the
two costs is extensive in every common basis, even at arbitrary origins. -/
theorem gaussian_semicircle_common_basis :
    ∃ K > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      let width := circuitHamiltonianSpectralWidth H
      ∀ v w : ℝ, π/3 ≤ (w-v)*width → (w-v)*width ≤ π →
      ∀ (W : unitaryGroup (Fin (n+2) → Bool) ℂ) (j s : ℕ) (ε δ : ℝ), ε+δ ≤ 11/50 →
      HasProjectiveCircuitApproximation (n+2) ε j (W.val*unitaryEvolution H.val v*star W.val) →
      HasProjectiveCircuitApproximation (n+2) δ s (W.val*unitaryEvolution H.val w*star W.val) →
      ((n+2:ℕ):ℝ) ≤ K*(1+((j+s:ℕ):ℝ)) := by
  obtain ⟨a,_,ha,_,hwidth⟩ := FirstAscent.gaussian_initial_clock
  obtain ⟨_,b,_,hb,hmass⟩ := gaussian_path_eventual_coefficient_mass
  let K := 352800*b*π^2*(log 42+log 4)/a^2
  have h₁ := log_pos (by norm_num : (1:ℝ)<42)
  have h₂ := log_pos (by norm_num : (1:ℝ)<4)
  refine ⟨K,by dsimp only [K]; positivity,?_⟩
  filter_upwards [hwidth,hmass] with ω hw hm
  filter_upwards [hw,hm] with n hwidth hm
  intro H width v w hl hu W j s ε δ htol hv hw
  let N : ℝ := (n+2:ℕ)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hwd : a*N ≤ width := hwidth.1
  have hwpos := (mul_pos ha hN).trans_le hwd
  let t := w-v
  have ht : 0 < t := pos_of_mul_pos_left ((by positivity : 0 < π/3).trans_le hl) hwpos.le
  have hfit := SpectralApproximation.common_basis_lag H W hv hw
  have hfar := semicircle_displacement H hl hu
  have hs := spectral_gate_floor_margin (pathPauliDisorderShell ω n) ht.ne' (by norm_num : (0:ℝ)<1/20)
    (mul_pos hb hN) hm.2 W ((by linarith only [htol] : 2*(ε+δ)+1/20 < 1/2).trans_le hfar) hfit
  let x := log 42+((j+s:ℕ):ℝ)*log 4
  have hx : 0 ≤ x := add_nonneg h₁.le (mul_nonneg (Nat.cast_nonneg _) h₂.le)
  change (1/20:ℝ)^2/(882*(b*N)*t^2) ≤ x at hs
  have hcost := (div_le_iff₀ (show 0 < 882*(b*N)*t^2 by positivity)).mp hs
  have hθ : t*(a*N) ≤ π := (mul_le_mul_of_nonneg_left hwd ht.le).trans hu
  have hθ₂ := pow_le_pow_left₀ (mul_nonneg ht.le (mul_nonneg ha.le hN.le)) hθ 2
  have haux : (a*N)^2 ≤ 352800*b*N*π^2*x := by
    nlinarith only [mul_le_mul_of_nonneg_right hcost (sq_nonneg (a*N)),
      mul_le_mul_of_nonneg_right hθ₂ (show 0 ≤ 882*b*N*x by positivity)]
  have hnew : a^2*N ≤ 352800*b*π^2*x := by
    apply (mul_le_mul_iff_left₀ hN).mp
    nlinarith only [haux]
  have hsum : x ≤ (log 42+log 4)*(1+((j+s:ℕ):ℝ)) := by
    dsimp only [x]
    nlinarith only [h₂.le,mul_nonneg h₁.le (Nat.cast_nonneg (α:=ℝ) (j+s))]
  dsimp only [K]
  rw [div_mul_eq_mul_div,le_div_iff₀ (sq_pos_of_pos ha)]
  nlinarith only [hnew,mul_le_mul_of_nonneg_left hsum (show 0 ≤ 352800*b*π^2 by positivity)]

#print axioms gaussian_semicircle_common_basis

/-- On both sides of the first physical scalar visit after any origin,
every fitting circuit needs extensively many gates, even if the basis
is chosen after the observation time. -/
theorem gaussian_first_scalar_spectral_rebound :
    ∃ K > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      let width := circuitHamiltonianSpectralWidth H
      ∀ origin : ℝ, let v := PrecisionReturns.firstVisit H origin 0 (1/10)
      ∀ t : ℝ, π/3 ≤ |t| *width → |t| *width ≤ π →
      ∀ (W : unitaryGroup (Fin (n+2) → Bool) ℂ) (s : ℕ),
      HasProjectiveCircuitApproximation (n+2) (1/10) s (W.val*unitaryEvolution H.val (v+t)*star W.val) →
      ((n+2:ℕ):ℝ) ≤ K*(1+(s:ℝ)) := by
  obtain ⟨K,hK,h⟩ := gaussian_semicircle_common_basis
  refine ⟨K,hK,?_⟩
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  intro H width origin v t hl hu W s hs
  have hv := SpectralApproximation.conjugate_empty W
    (PrecisionReturns.firstVisit_isLeast H origin 0 (by norm_num : 0<(1/10:ℝ))).1.2
  rcases le_total 0 t with ht|ht
  · have he : v+t-v=|t| := by rw [abs_of_nonneg ht]; ring
    simpa only [Nat.zero_add] using hn v (v+t) (by rwa [he]) (by rwa [he]) W 0 s _ _ (by norm_num) hv hs
  · have he : v-(v+t)=|t| := by rw [abs_of_nonpos ht]; ring
    simpa only [Nat.add_zero] using hn (v+t) v (by rwa [he]) (by rwa [he]) W s 0 _ _ (by norm_num) hs hv

#print axioms gaussian_first_scalar_spectral_rebound
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
