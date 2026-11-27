import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.MultiplexedPhases.Synthesis
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Subregister.ApproximateProduct
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.RobustReflection
import GaloisForLFunctions.HTGeometry.ChainPauliFinFamily

/-! # Projective circuit-net cardinality from phases on a subset of wires -/
open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TimePacking
open DiagonalSynthesis Subregister
open private place_sub from GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Subregister.ApproximateProduct
noncomputable section

/-- Arbitrary anchored signs on h active wires cost at most three times
their Hilbert dimension. Idle wires preserve every projective distance. -/
theorem supported_circuit_net_card {n h s : ℕ} (hh : 2 ≤ h) (hn : h ≤ n) (hs : 2^h*3 ≤ s)
    {r : ℝ} (hr : 2*r < Real.sqrt 2) (net : Finset (Register n))
    (hc : ∀ U : Register n, Realizes s U → ∃ W∈net, ∃ z : ℂ, ‖z‖=1 ∧ ‖U-z • W‖≤r) :
    2^(2^h-1) ≤ net.card := by
  classical
  have hcard : h ≤ (univ : Finset (Fin n)).card := by simpa only [card_univ,Fintype.card_fin] using hn
  obtain ⟨S,_,hS⟩ := exists_subset_card_eq hcard
  let e : Fin h ≃ S := (finCongr ((Fintype.card_coe S).trans hS).symm).trans (Fintype.equivFin S).symm
  let d := 2^h-1
  have hpos : 0 < 2^h := by positivity
  let f : (Fin h → Bool) ≃ Fin (d+1) := (qubitConfigFin h).trans (finCongr (by dsimp only [d]; omega))
  let A (x : Fin d → Bool) := anchoredSpectralBooleanReflection f 1 x
  let U (x : Fin d → Bool) := place e (A x)
  have hfit (x : Fin d → Bool) : Realizes s (U x) := by
    have hunit (i : Fin (d+1)) : ‖anchoredBooleanPacket x i‖=1 := by
      refine Fin.cases (by simp [anchoredBooleanPacket]) (fun j => ?_) i
      cases hx : x j <;> simp [anchoredBooleanPacket,hx]
    have ha : Realizes (2^h*3) (A x) := by
      simpa [A,anchoredSpectralBooleanReflection] using
        MultiplexedPhases.full_register_phases hh (anchoredBooleanPacket x ∘ f) (fun i => hunit (f i))
    obtain ⟨c,hc,C,hC,he⟩ := realizes_place e ha
    exact ⟨c,hc,C,hC.trans hs,he⟩
  have hsep {x y : Fin d → Bool} (hxy : x≠y) (z : ℂ) (hz : ‖z‖=1) :
      Real.sqrt 2 ≤ ‖U x-z • U y‖ := by
    change _ ≤ ‖place e (A x)-z • place e (A y)‖
    rw [←place_smul,←place_sub,norm_place]
    exact spectral_reflection_sqrt_two_separation f 1 hxy z hz
  by_contra! hsmall
  obtain ⟨x,hx⟩ := exists_projectively_far_from_small_net U _ r (fun hxy => hsep hxy) hr net
    (by simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using hsmall)
  obtain ⟨W,hW,z,hz,hclose⟩ := hc _ (hfit x)
  exact (hx W hW z hz).not_ge hclose

/-- Up to three times the full dimension, a fixed-radius projective
net for s gates has at least two to the power floor(s/6) centers. -/
theorem gate_budget_net_card {n s : ℕ} (hs : 12 ≤ s) (hcap : s ≤ 3*2^n)
    {r : ℝ} (hr : 2*r < Real.sqrt 2) (net : Finset (Register n))
    (hc : ∀ U : Register n, Realizes s U → ∃ W∈net, ∃ z : ℂ, ‖z‖=1 ∧ ‖U-z • W‖≤r) :
    2^(s/6) ≤ net.card := by
  let h := Nat.log 2 (s/3)
  have hnz : s/3 ≠ 0 := by omega
  have hh : 2 ≤ h := Nat.le_log_of_pow_le (by decide) (by omega : 4 ≤ s/3)
  have hlo : 2^h ≤ s/3 := Nat.pow_log_le_self 2 hnz
  have hn : h ≤ n := by
    have hp : 0 < 2^n := by positivity
    have hlt : s/3 < 2^(n+1) := by rw [pow_succ]; omega
    exact Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow hnz hlt)
  have hhi : s/3 < 2^h*2 := by simpa only [pow_succ] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) (s/3)
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : s/6 ≤ 2^h-1)).trans
    (supported_circuit_net_card hh hn (by omega) hr net hc)

#print axioms gate_budget_net_card
#print axioms supported_circuit_net_card
end
end GaloisForLFunctions.HTGeometry.TimePacking
