import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TimePacking.PhysicalSpan
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics

/-! # Gate budgets accessible by time-sample counting on a frozen Gaussian chain -/
open Set Filter MeasureTheory Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TimePacking
open DiagonalSynthesis
noncomputable section

private theorem span_at_budget {N h M : ℕ} (hN : h≤N) (H : selfAdjoint (Register N))
    (t : Fin M → ℝ) {a T e r : ℝ} (hT : 0≤T) (he : 0<e) (ht : ∀ i, t i∈Icc a (a+T))
    (hs : ∀ i j, i≠j → e≤‖unitaryEvolution H.val (t i)-unitaryEvolution H.val (t j)‖)
    (net : Finset (Register N)) (hr : 2*r<sqrt 2)
    (hc : ∀ U : Register N, Realizes h U → ∃ W∈net, ∃ z : ℂ, ‖z‖=1 ∧ ‖U-z • W‖≤r)
    (hM : net.card<M) : ((N-h:ℕ):ℝ)^h*e ≤ ‖H.val‖*T := by
  obtain ⟨m,rfl⟩ : ∃ m, N=m+h := ⟨N-h,(Nat.sub_add_cancel hN).symm⟩
  simpa only [Nat.add_sub_cancel] using
    dictionary_requires_time H t hT he ht hs net hr hc (by simpa only [Fintype.card_fin] using hM)

/-- At any exponential physical horizon, counting separated dates
against a covering of the full circuit family can certify at most
order N/log N gates, even if the observation window is chosen after
the Gaussian draw. The estimate retains the separation and horizon. -/
theorem gaussian_time_counting_ceiling :
    ∃ C > (0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ h M : ℕ, 2*h≤N → ∀ a T q e r : ℝ, 0≤T → T≤exp (q*(N:ℝ)) → 0<e → 2*r<sqrt 2 →
        ∀ t : Fin M → ℝ, (∀ i, t i∈Icc a (a+T)) →
        (∀ i j, i≠j → e≤‖unitaryEvolution H.val (t i)-unitaryEvolution H.val (t j)‖) →
        ∀ net : Finset (Register N), (∀ U : Register N, Realizes h U →
          ∃ W∈net, ∃ z : ℂ, ‖z‖=1 ∧ ‖U-z • W‖≤r) → net.card<M →
          (h:ℝ)*log ((N:ℝ)/2) ≤ q*N + log (C*(N:ℝ)/e) := by
  obtain ⟨C,hC,hw⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro N H h M hhalf a T q e r hT hmax he hr t ht hs net hc hM
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hb : h≤N := by omega
  have hm : (N:ℝ)/2≤((N-h:ℕ):ℝ) := by
    rw [Nat.cast_sub hb]
    have h' : 2*(h:ℝ)≤N := by exact_mod_cast hhalf
    linarith only [h']
  have hp := span_at_budget hb H t hT he ht hs net hr hc hM
  have hsmall : ((N:ℝ)/2)^h*e ≤ C*N*exp (q*N) :=
    ((mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hm _) he.le).trans hp).trans
      (mul_le_mul hn hmax hT (mul_nonneg hC.le hN.le))
  have hh := log_le_log (mul_pos (pow_pos (half_pos hN) _) he) hsmall
  rw [log_mul (pow_pos (half_pos hN) _).ne' he.ne',log_pow,
    log_mul (mul_pos hC hN).ne' (exp_pos _).ne',log_exp] at hh
  rw [log_div (mul_pos hC hN).ne' he.ne']
  linarith only [hh]

#print axioms gaussian_time_counting_ceiling
end
end GaloisForLFunctions.HTGeometry.TimePacking
