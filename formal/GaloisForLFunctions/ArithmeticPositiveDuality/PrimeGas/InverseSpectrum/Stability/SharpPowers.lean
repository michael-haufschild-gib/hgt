import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.ShellBoundary
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.StrictDeficit
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # All uniform power laws for fourth-trace recovery -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

private theorem attenuation_tends_zero : Tendsto (fun n : ℕ => attenuation (number n)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((number n).val:ℝ)) atTop atTop := by
    change Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop
    simpa only [Nat.cast_add,Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop (1:ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)

private theorem boundary_forces_power {p C : ℝ}
    (hb : ∀ n : ℕ+, attenuation n^p ≤ C*attenuation n^4) : 4 ≤ p ∧ 1 ≤ C := by
  have hone : attenuation 1 = 1 := by norm_num [attenuation,gain]
  have hC : 1 ≤ C := by simpa only [hone,Real.one_rpow,one_pow,mul_one] using hb 1
  refine ⟨?_,hC⟩
  by_contra! hp
  have hgap : 0 < 4-p := sub_pos.mpr hp
  have hh (n : ℕ+) : 1 ≤ C*attenuation n^(4-p) := by
    let a := attenuation n
    have ha : 0 < a := attenuation_pos n
    have he : a^p*a^(4-p) = a^4 := by
      rw [← Real.rpow_add ha,show p+(4-p) = 4 by ring]
      exact Real.rpow_natCast a 4
    apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos ha p)).mp
    calc
      a^p*1 = a^p := mul_one _
      _ ≤ C*a^4 := hb n
      _ = a^p*(C*a^(4-p)) := by rw [← he]; ring
  have ht := ((Real.continuous_rpow_const hgap.le).continuousAt.tendsto.comp attenuation_tends_zero).const_mul C
  change Tendsto (fun n : ℕ => C*attenuation (number n)^(4-p)) atTop (𝓝 (C*(0:ℝ)^(4-p))) at ht
  rw [Real.zero_rpow hgap.ne',mul_zero] at ht
  exact (not_le_of_gt (by norm_num : (0:ℝ) < 1)) (ge_of_tendsto ht (Eventually.of_forall fun n => hh (number n)))

private theorem positive_power_iff (p : {p : ℝ // 0 < p}) (C : ℝ) :
    (∀ G : Propagator, ‖criticalOperator-G.val‖^p.val ≤ C*traceLoss G.val) ↔ 4 ≤ p.val ∧ 1 ≤ C := by
  constructor
  · intro h
    have hc : IsClosed {z : ℝ × ℝ | z.1^p.val ≤ C*z.2} :=
      isClosed_le ((Real.continuous_rpow_const p.property.le).comp continuous_fst) (continuous_const.mul continuous_snd)
    have ha : closure errorReadings ⊆ {z : ℝ × ℝ | z.1^p.val ≤ C*z.2} := by
      apply hc.closure_subset_iff.mpr
      rintro _ ⟨G,rfl⟩
      exact h G
    exact boundary_forces_power (fun n => ha (shell_boundary n))
  · rintro ⟨hp,hC⟩ G
    obtain ⟨_,hunit,hfour⟩ := trace_stability G
    have hnon := le_trans (by positivity : 0 ≤ ‖criticalOperator-G.val‖^4) hfour
    have hm : ‖criticalOperator-G.val‖^p.val ≤ ‖criticalOperator-G.val‖^4 := by
      rcases (norm_nonneg (criticalOperator-G.val)).eq_or_lt with h | h
      · rw [← h,Real.zero_rpow p.property.ne',zero_pow (by decide : 4 ≠ 0)]
      · calc
          _ ≤ ‖criticalOperator-G.val‖^(4:ℝ) := Real.rpow_le_rpow_of_exponent_ge h hunit hp
          _ = _ := Real.rpow_natCast _ 4
    exact hm.trans (hfour.trans (le_mul_of_one_le_left hnon hC))

/-- Complete classification of real exponents and constants in a uniform physical error estimate. -/
theorem uniform_power_iff (p C : ℝ) :
    (∀ G : Propagator, ‖criticalOperator-G.val‖^p ≤ C*traceLoss G.val) ↔ 4 ≤ p ∧ 1 ≤ C := by
  by_cases hp : 0 < p
  · exact positive_power_iff ⟨p,hp⟩ C
  have hp0 := le_of_not_gt hp
  constructor
  · intro h
    have h₁ (G : Propagator) : ‖criticalOperator-G.val‖^(1:ℝ) ≤ C*traceLoss G.val := by
      refine le_trans ?_ (h G)
      rcases (norm_nonneg (criticalOperator-G.val)).eq_or_lt with hz | hz
      · rw [← hz,Real.zero_rpow one_ne_zero]
        exact Real.rpow_nonneg (le_refl 0) _
      · exact Real.rpow_le_rpow_of_exponent_ge hz (trace_stability G).2.1 (hp0.trans zero_le_one)
    have him := ((positive_power_iff ⟨1,zero_lt_one⟩ C).mp h₁).1
    norm_num at him
  · rintro ⟨h,_⟩
    linarith only [h,hp0]

/-- Each sharp shell point lies in the closure and every actual propagator misses it. -/
theorem shell_boundary_unattained (n : ℕ+) :
    (attenuation n,attenuation n^4) ∈ closure errorReadings ∧
      (attenuation n,attenuation n^4) ∉ errorReadings := by
  refine ⟨shell_boundary n,?_⟩
  rintro ⟨G,hG⟩
  have hx : ‖criticalOperator-G.val‖ = attenuation n := congrArg Prod.fst hG
  have hy : traceLoss G.val = attenuation n^4 := congrArg Prod.snd hG
  have hne : G.val ≠ criticalOperator := by
    intro he
    rw [he,sub_self,norm_zero] at hx
    exact (attenuation_pos n).ne' hx.symm
  have h := (strict_trace_stability_iff G).mpr hne
  rw [hx,hy] at h
  exact lt_irrefl _ h

#print axioms uniform_power_iff
#print axioms shell_boundary_unattained

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
