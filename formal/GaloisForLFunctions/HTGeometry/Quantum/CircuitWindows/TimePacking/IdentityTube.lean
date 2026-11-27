import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TimePacking.SupportedSigns
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid
import Mathlib.MeasureTheory.Measure.Real

/-! # Time required by a uniform bound on individual circuit-tube durations -/
open Set Finset MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TimePacking
open DiagonalSynthesis
noncomputable section

/-- Physical time spent within the given projective distance of one center. -/
def targetRecord {n : ℕ} (H : selfAdjoint (Register n)) (W : Register n) (ρ T : ℝ) : Set ℝ :=
  Icc 0 T ∩ {t | ∃ z : ℂ, ‖z‖=1 ∧ ‖unitaryEvolution H.val t-z • W‖ ≤ ρ}

/-- The same center covering the identity captures the entire initial
interval until the Hamiltonian speed uses up the tube's remaining radius. -/
private theorem identity_target {n s : ℕ} (H : selfAdjoint (Register n)) (net : Finset (Register n))
    {r : ℝ} (hc : ∀ U : Register n, Realizes s U → ∃ W∈net, ∃ z : ℂ, ‖z‖=1 ∧ ‖U-z • W‖≤r) :
    ∃ W∈net, ∀ ℓ T ρ : ℝ, 0 ≤ ℓ → ℓ ≤ T → ‖H.val‖*ℓ ≤ ρ-r →
      ℓ ≤ volume.real (targetRecord H W ρ T) := by
  obtain ⟨c,hc₀,C,hC,he⟩ := Realizes.one n
  obtain ⟨W,hW,z,hz,hfit⟩ := hc 1 ⟨c,hc₀,C,hC.trans (Nat.zero_le s),he⟩
  refine ⟨W,hW,?_⟩
  intro ℓ T ρ hℓ hT hr
  have hsub : Icc 0 ℓ ⊆ targetRecord H W ρ T := by
    intro t ht
    refine ⟨⟨ht.1,ht.2.trans hT⟩,z,hz,?_⟩
    have hdist := norm_unitaryEvolution_time_sub_le H.2 t 0
    rw [show unitaryEvolution H.val 0=1 by simp [unitaryEvolution],sub_zero,abs_of_nonneg ht.1] at hdist
    apply (norm_sub_le_norm_sub_add_norm_sub _ (1:Register n) _).trans
    linarith only [hdist,hfit,mul_le_mul_of_nonneg_left ht.2 (norm_nonneg H.val),hr]
  simpa only [Real.volume_real_Icc_of_le hℓ,sub_zero] using measureReal_mono (μ:=volume) hsub
    (ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_left))

/-- Even exact individual tube durations cannot certify a first exit by
multiplying the worst duration by the full dictionary size on a shorter
record. The lower bound applies to every choice of centers. -/
theorem uniform_tube_duration_requires_time {n s : ℕ} (H : selfAdjoint (Register n))
    (hs : 12 ≤ s) (hcap : s ≤ 3*2^n) {r ε T : ℝ} (hr : 2*r < Real.sqrt 2)
    (hε : 0 ≤ ε) (hT : 0 < T) (net : Finset (Register n))
    (hc : ∀ U : Register n, Realizes s U → ∃ W∈net, ∃ z : ℂ, ‖z‖=1 ∧ ‖U-z • W‖≤r)
    {P : ℝ} (hP : ∀ W∈net, volume.real (targetRecord H W (r+ε) T) ≤ P)
    (hsum : (net.card:ℝ)*P < T) : (2:ℝ)^(s/6)*ε < ‖H.val‖*T := by
  have hJ : (2:ℝ)^(s/6) ≤ net.card := by exact_mod_cast gate_budget_net_card hs hcap hr net hc
  have hpos : 0 < (net.card:ℝ) := (pow_pos (by norm_num : (0:ℝ)<2) _).trans_le hJ
  have hone : 1 ≤ (net.card:ℝ) := (one_le_pow₀ (by norm_num : (1:ℝ)≤2)).trans hJ
  obtain ⟨W,hW,hw⟩ := identity_target H net hc
  by_contra! hshort
  let ℓ := T/(net.card:ℝ)
  have hℓ : 0 ≤ ℓ := div_nonneg hT.le hpos.le
  have hℓT : ℓ ≤ T := div_le_self hT.le hone
  have hd : ‖H.val‖*ℓ ≤ r+ε-r := by
    rw [add_sub_cancel_left]
    change ‖H.val‖*(T/(net.card:ℝ)) ≤ ε
    rw [←mul_div_assoc,div_le_iff₀ hpos,mul_comm ε]
    exact hshort.trans (mul_le_mul_of_nonneg_right hJ hε)
  have hlP := (hw ℓ T (r+ε) hℓ hℓT hd).trans (hP W hW)
  have hh := (div_le_iff₀ hpos).mp hlP
  exact hsum.not_ge (hh.trans_eq (mul_comm P (net.card:ℝ)))

#print axioms uniform_tube_duration_requires_time
end
end GaloisForLFunctions.HTGeometry.TimePacking
