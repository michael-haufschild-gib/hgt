import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.SparseProbes.FrozenLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.PhysicalLimit

/-! # Sharp change from zero to extensive gate cost at fixed trace overlap -/
open MeasureTheory Matrix Real Filter
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.SparseProbes
noncomputable section

theorem regTrace_evolution {n : ℕ} (u : PathShell n) (t : ℝ) :
    regTrace (unitaryEvolution (pathHamiltonian u) t) = shellTrace u t := by
  simp only [regTrace,shellTrace,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,
    Nat.cast_ofNat,div_eq_inv_mul]

private theorem overlap_le {n : ℕ} (u : PathShell n) (t : ℝ) (C : TwoQubitCircuit (n+2)) :
    ‖regTrace (C.eval.valᴴ*unitaryEvolution (pathHamiltonian u) t)‖ ≤
      ‖probeCovariance u t C‖+‖shellTrace u t‖ := by
  let U := unitaryEvolution (pathHamiltonian u) t
  let W := C.eval.valᴴ
  have h := norm_add_le (probeCovariance u t C) (regTrace W*regTrace U)
  change ‖(regTrace (W*U)-regTrace W*regTrace U)+regTrace W*regTrace U‖ ≤ _ at h
  rw [sub_add_cancel,norm_mul] at h
  exact h.trans (add_le_add_left ((mul_le_of_le_one_left (norm_nonneg _)
    (norm_regTrace_le_one (Unitary.star_mem C.eval.property))).trans_eq
      (congrArg norm (regTrace_evolution u t))) _)

/-- At a limiting scaled time Nt²=x, the empty circuit passes every overlap
threshold below exp(−6x). Every circuit passing a higher threshold needs a
positive fraction of all sites in gate count. The dates may depend on the draw. -/
theorem gaussian_critical_gate_transition :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (t : ℕ→ℝ) (x : ℝ),
      Tendsto (fun n => (n+2:ℕ)*(t n)^2) atTop (𝓝 x) →
      (∀ κ < exp (-6*x), ∀ᶠ n : ℕ in atTop,
        κ < ‖regTrace (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) (t n))‖) ∧
      (∀ κ > exp (-6*x), ∃ c > (0:ℝ), ∀ᶠ n : ℕ in atTop, ∀ C : TwoQubitCircuit (n+2),
        κ ≤ ‖regTrace (C.eval.valᴴ*unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) (t n))‖ →
        c*(n+2:ℕ) ≤ C.gateCount) := by
  obtain ⟨K,hK,hcov⟩ := gaussian_circuit_covariance
  filter_upwards [gaussian_spectral_profile,hcov] with ω hw hc
  intro t x ht
  let u (n : ℕ) := pathPauliDisorderShell ω n
  let a := exp (-6*x)
  have ha : 0 < a := exp_pos _
  have hlim : Tendsto (fun n => ‖shellTrace (u n) (t n)‖) atTop (𝓝 a) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha] using (hw t x ht).norm
  constructor
  · intro κ hκ
    simpa only [regTrace_evolution] using hlim.eventually_const_lt hκ
  · intro κ hκ
    let b := (κ-a)/2
    have hb : 0 < b := half_pos (sub_pos.mpr hκ)
    let R := |x|+1
    have hR : 0 < R := by dsimp only [R]; positivity
    have hKR : 0 < K*R^2 := by positivity
    refine ⟨b^4/(K*R^2),div_pos (pow_pos hb 4) hKR,?_⟩
    filter_upwards [hc,hlim.eventually_lt_const (show a < a+b by linarith only [hb]),
      ht.eventually_lt_const ((le_abs_self x).trans_lt (lt_add_one _))] with n hn hsn htn
    intro C hC
    have h₁ := overlap_le (u n) (t n) C
    have hb₁ : b ≤ ‖probeCovariance (u n) (t n) C‖ := by
      dsimp only [b] at hsn ⊢
      linarith only [h₁,hC,hsn]
    have h₂ := (pow_le_pow_left₀ hb.le hb₁ 4).trans (hn (t n) C)
    have h₃ := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) htn.le 2) hK.le)
    have hh := h₂.trans (mul_le_mul_of_nonneg_right h₃ (by positivity))
    have hN : (0:ℝ) < (n+2:ℕ) := by positivity
    apply (le_div_iff₀ hN).mp
    apply (div_le_iff₀ hKR).mpr
    simpa only [mul_comm (K*R^2)] using hh

#print axioms gaussian_critical_gate_transition
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.SparseProbes
