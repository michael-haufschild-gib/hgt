import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.ExponentialFloor
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.CommonBasisLag
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.PairChord
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass

/-! # Inverse-square cost of tracking an orbit in one common basis -/
open Matrix Real MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

private theorem window_margin :
    ∃ k > 0, ∀ {n : ℕ} (u : PathShell n) {t B ε : ℝ}, 0 < t → 0 < B → ‖u‖^2 ≤ B →
      π ≤ 2*t*∑ i : Fin (n+2), |u (.inl (i,2))| → ε ≤ 11/50 →
      ∀ (W : unitaryGroup (Fin (n+2) → Bool) ℂ) (s : ℕ),
      HasProjectiveCircuitApproximation (n+2) ε s
        (W.val*unitaryEvolution (pathHamiltonian u) t*star W.val) →
      k ≤ (1+(s:ℝ))*B*t^2 := by
  let C := sqrt 21+2
  let D := log 42+log 4
  have hC : 0 < C := by dsimp only [C]; positivity
  have h₁ := log_pos (by norm_num : (1:ℝ)<42)
  have h₂ := log_pos (by norm_num : (1:ℝ)<4)
  have hD : 0 < D := add_pos h₁ h₂
  let k := min (1/(4*C^2)) (1/(352800*D))
  refine ⟨k,lt_min (by positivity) (by positivity),?_⟩
  intro n u t B ε ht hB hm hangle hε W s hfit
  by_contra! hsmall
  have hs : B*t^2 ≤ (1+(s:ℝ))*B*t^2 := by
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) s) (mul_nonneg hB.le (sq_nonneg t))]
  have hlim := (lt_div_iff₀ (show 0 < 4*C^2 by positivity)).mp
    (hs.trans_lt (hsmall.trans_le (min_le_left ..)))
  have hrem : C*t*‖u‖ < 1/2 := by
    apply (sq_lt_sq₀ (by positivity) (by norm_num)).mp
    nlinarith only [hlim,mul_le_mul_of_nonneg_left hm (show 0 ≤ C^2*t^2 by positivity)]
  let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  have hchord := ReturnSpacing.PhysicalComponents.paired_angle_floor u ht pi_pos.le le_rfl hangle
  rw [sin_pi_div_two] at hchord
  change 1 ≤ orbitCircuitDistance H 0 t + C*t*‖u‖ at hchord
  have hzero : HasProjectiveCircuitApproximation (n+2) ‖1-unitaryEvolution H.val t‖ 0
      (unitaryEvolution H.val t) := by
    refine ⟨1,norm_one,TwoQubitCircuit.one _,le_rfl,?_⟩
    rw [TwoQubitCircuit.one_eval,one_smul]
    exact (norm_sub_rev (unitaryEvolution H.val t) 1).le
  have hdist : orbitCircuitDistance H 0 t ≤ ‖1-unitaryEvolution H.val t‖ :=
    (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hzero
  have hfar : 2*ε+1/20 < ‖1-unitaryEvolution H.val t‖ := by
    linarith only [hchord,hrem,hdist,hε]
  have hh := spectral_gate_floor_margin u ht.ne' (by norm_num : (0:ℝ)<1/20) hB hm W hfar hfit
  have hcost := (div_le_iff₀ (show 0 < 882*B*t^2 by positivity)).mp hh
  have hlog : log 42+(s:ℝ)*log 4 ≤ (1+(s:ℝ))*D := by
    dsimp only [D]
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) s) h₁.le,h₂.le]
  have hmax := (lt_div_iff₀ (show 0 < 352800*D by positivity)).mp
    (hsmall.trans_le (min_le_right ..))
  nlinarith only [hcost,mul_le_mul_of_nonneg_right hlog (show 0≤882*B*t^2 by positivity),hmax]

/-- Any two fits in one basis obey a common budget-times-squared-lag
lower bound after inverse-size onset, with no restriction on the origin. -/
theorem gaussian_common_basis_window :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ v w : ℝ, A ≤ (w-v)*(n+2:ℕ) →
      ∀ (W : unitaryGroup (Fin (n+2) → Bool) ℂ) (j s : ℕ) (ε δ : ℝ), ε+δ ≤ 11/50 →
      HasProjectiveCircuitApproximation (n+2) ε j (W.val*unitaryEvolution H v*star W.val) →
      HasProjectiveCircuitApproximation (n+2) δ s (W.val*unitaryEvolution H w*star W.val) →
      c ≤ (1+((j+s:ℕ):ℝ))*(n+2:ℕ)*(w-v)^2 := by
  obtain ⟨k,hk,h⟩ := window_margin
  obtain ⟨a,b,ha,hb,hm⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨π/(2*a),k/b,by positivity,div_pos hk hb,?_⟩
  filter_upwards [hm] with ω hω
  filter_upwards [hω] with n hn
  intro H v w hlate W j s ε δ hε hv hw
  let u := pathPauliDisorderShell ω n
  let G : selfAdjoint (Reg (n+2)) := ⟨H,isSelfAdjoint_pathHamiltonian u⟩
  have hN : 0 < ((n+2:ℕ):ℝ) := by positivity
  have ht := pos_of_mul_pos_left ((by positivity : 0 < π/(2*a)).trans_le hlate) hN.le
  have hangle : π ≤ 2*(w-v)*∑ i : Fin (n+2), |u (.inl (i,2))| := by
    have hh := (div_le_iff₀ (show 0 < 2*a by positivity)).mp hlate
    nlinarith only [hh,mul_le_mul_of_nonneg_left hn.1 ht.le]
  have hh := h u ht (mul_pos hb hN) hn.2 hangle hε W (j+s)
    (SpectralApproximation.common_basis_lag G W hv hw)
  exact (div_le_iff₀ hb).mpr (hh.trans_eq (by ring))

#print axioms gaussian_common_basis_window
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
