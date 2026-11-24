import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.EarlyHistory.MassRate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PhysicalSpeed.ExponentialDates

/-! # Distinguishing early affordable observations from a short first excursion -/
open Set MeasureTheory Filter Real Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.EarlyHistory
open ShortWindows LocalPatches.PhysicalSpeed
noncomputable section

/-- Pay a quadratic negative-log conditioning cost out of the Gaussian
first-passage tail. Both exponents refer to physical qubit count. -/
private theorem absorb_history_price {β u : ℝ} (hβ : 0<β) (hu : β<2*u) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℝ, m≤12*(N:ℝ) →
      2*m*exp (-((2:ℝ)^(u*(N:ℝ)))^2/2) ≤
        exp (-((2:ℝ)^(β*(N:ℝ))))*exp (-36*(N:ℝ)^2) := by
  have h₁ : 1<(2:ℝ)^β := one_lt_rpow (by norm_num) hβ
  have h₂ : 1<(2:ℝ)^(2*u-β) := one_lt_rpow (by norm_num) (sub_pos.mpr hu)
  have ha := (tendsto_pow_const_div_const_pow_of_one_lt 2 h₁).eventually_lt_const
    (by norm_num : (0:ℝ)<1/60)
  have hb := (tendsto_pow_const_div_const_pow_of_one_lt 0 h₂).eventually_lt_const
    (by norm_num : (0:ℝ)<1/4)
  filter_upwards [ha,hb,eventually_ge_atTop 1] with N ha hb hN
  intro m hm
  let D := (2:ℝ)^(β*(N:ℝ))
  let U := (2:ℝ)^(u*(N:ℝ))
  have hD : 0<D := rpow_pos_of_pos (by norm_num) _
  have hb' : (4:ℝ) ≤ (2:ℝ)^((2*u-β)*(N:ℝ)) := by
    rw [rpow_mul (by norm_num : (0:ℝ)≤2),rpow_natCast]
    rw [pow_zero,div_lt_iff₀ (by positivity)] at hb
    linarith only [hb]
  have hsq : 4*D ≤ U^2 := by
    apply (mul_le_mul_of_nonneg_right hb' hD.le).trans_eq
    rw [show (2:ℝ)^((2*u-β)*(N:ℝ))*D=(2:ℝ)^((2*u-β)*(N:ℝ)+β*N) from
      (rpow_add (by norm_num : (0:ℝ)<2) ..).symm]
    dsimp only [U]
    rw [pow_two,←rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have hquad : 60*(N:ℝ)^2≤D := by
    rw [div_lt_iff₀ (by positivity)] at ha
    change _≤(2:ℝ)^(β*(N:ℝ))
    rw [rpow_mul (by norm_num : (0:ℝ)≤2),rpow_natCast]
    linarith only [ha]
  have hN' : (1:ℝ)≤N := by exact_mod_cast hN
  have hh : 2*m+36*(N:ℝ)^2≤D := by
    nlinarith only [hm,hquad,mul_nonneg (sub_nonneg.mpr hN') (Nat.cast_nonneg (α:=ℝ) N)]
  have hmul : 2*m≤exp (2*m) := (le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _)
  apply (mul_le_mul_of_nonneg_right hmul (exp_pos _).le).trans
  rw [←exp_add,←exp_add]
  apply exp_le_exp.mpr
  change 2*m+ -U^2/2 ≤ -D+ -36*(N:ℝ)^2
  linarith only [hh,hsq]

/-- Condition on affordable observations at any prescribed set of dates
through exp N, even the whole interval. With conditional probability
at least 1-exp(-2^(β N)), the actual onset and every first wait through
half the crossing budget still exceed 2^(γ N), whenever β<2(1-γ). -/
theorem gaussian_conditioned_first_excursion {γ β : ℝ} (hβ : 0<β) (hγ : β<2*(1-γ)) :
    ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let t := (2:ℝ)^(γ*(N:ℝ))
      let μ := pathPauliDisorderLaw
      let F := {ω | crossingOrigin (k+1) P (9/80) (prefixPoint k ω) ≤ t ∨
        ∃ s ≤ P/2, crossingWait (k+1) P s (prefixPoint k ω) ≤ t}
      ∀ (A : Set ℝ) (s : ℝ → ℕ), (∀ v ∈ A, |v|≤exp N) →
        let E := prefixPoint k ⁻¹' affordableHistory (k+1) A s
        0<μ.real E ∧ μ.real (F ∩ E)/μ.real E ≤ exp (-((2:ℝ)^(β*(N:ℝ)))) := by
  let u := (β/2+(1-γ))/2
  have hu : β<2*u := by dsimp only [u]; linarith only [hγ]
  have hue : γ+u<1 := by dsimp only [u]; linarith only [hγ]
  have hrate := (tendsto_add_atTop_nat 3).eventually (absorb_history_price hβ hu)
  filter_upwards [gaussian_early_exponential_onset_or_return hue,gaussian_history_mass_rate,hrate]
    with k hfirst hhistory hcost
  intro N P t μ F A s hA E
  letI : IsProbabilityMeasure μ := by dsimp only [μ,pathPauliDisorderLaw]; infer_instance
  let m := Fintype.card (ChainLabel N)
  have hm : (m:ℝ) ≤ 12*(N:ℝ) := by
    exact_mod_cast (show m ≤ 12*N by simpa only [PrefixIndex,Fintype.card_fin] using prefix_card_bound (k+1))
  have he := hhistory A s hA
  have hpos : 0<μ.real E := (exp_pos _).trans_le he
  refine ⟨hpos,(div_le_iff₀ hpos).mpr ?_⟩
  apply (measureReal_mono (μ:=μ) (inter_subset_left (s:=F) (t:=E))).trans
  exact hfirst.trans ((hcost m hm).trans (mul_le_mul_of_nonneg_left he (exp_pos _).le))

#print axioms gaussian_conditioned_first_excursion
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.EarlyHistory
