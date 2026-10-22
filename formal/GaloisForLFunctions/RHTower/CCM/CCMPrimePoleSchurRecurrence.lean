import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleSchurModulation
import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleFiniteCoherence

/-!
# Recurrence of the complete actual-prime Schur energy

At every fixed aperture, one cofinal sequence of integer modulation frequencies
makes every prime-power phase recur simultaneously. The physical mass stays
fixed, all fixed-vector pairings vanish, and the full prime-edge energy tends
to zero. No infinite prime family is replaced by a finite one: the finite sum
here is exactly the aperture's actual prime operator.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct Topology BigOperators
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem finite_phase_clock (N Q : ℕ) (hQ : 0 < Q) :
    ∃ k : ℕ, Q ≤ k ∧ ∀ n : ℕ, n ≤ N →
      ‖modulationSymbol (k : ℝ) (Real.log n) - 1‖ ≤ 2 * Real.pi / (Q : ℝ) := by
  obtain ⟨k, hk, _, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_annular_quantitative hQ
      (fun i : Fin (N+1) => 2 * Real.pi * Real.log (i : ℕ))
  refine ⟨k, hk, fun n hn => ?_⟩
  let i : Fin (N+1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have h := (norm_exp_I_mul_real_sub_one_le_mod_two_pi
    ((k : ℝ) * (2 * Real.pi * Real.log n)) (r i)).trans (hr i)
  have heq : modulationSymbol (k : ℝ) (Real.log n) =
      Complex.exp (I * (((k : ℝ) * (2 * Real.pi * Real.log n) : ℝ) : ℂ)) := by
    unfold modulationSymbol
    congr 1
    push_cast
    ring
  rw [heq]
  exact h

/-- One sequence simultaneously preserves mass, escapes every fixed pairing,
and suppresses all actual prime edges at the chosen aperture. -/
theorem exists_ccmSchurPole_recurrent_modulations (a : SuzukiPositiveAperture) :
    ∃ κ : ℕ → ℝ, Tendsto κ atTop atTop ∧
      (∀ k, ‖ccmApertureModulation a (κ k) (ccmSchurPoleVector a)‖ =
        ‖ccmSchurPoleVector a‖) ∧
      (∀ g : suzukiApertureHilbert a,
        Tendsto (fun k => inner ℂ g
          (ccmApertureModulation a (κ k) (ccmSchurPoleVector a))) atTop (𝓝 0)) ∧
      Tendsto (fun k => ccmPrimePoleSchurEnergy a
        (ccmApertureModulation a (κ k) (ccmSchurPoleVector a)).1) atTop (𝓝 0) := by
  classical
  let N := ⌊Real.exp (2*a.1)⌋₊
  have hclock (j : ℕ) := finite_phase_clock N (j+1) (Nat.succ_pos j)
  choose k hk hphase using hclock
  let κ : ℕ → ℝ := fun j => (k j : ℝ)
  have hκ : Tendsto κ atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro j
    change (j : ℝ) ≤ (k j : ℝ)
    exact_mod_cast (Nat.le_succ j).trans (hk j)
  have herr (n : ℕ) (hn : n ≤ N) :
      Tendsto (fun j => ‖modulationSymbol (κ j) (Real.log n)-1‖) atTop (𝓝 0) := by
    have hinv : Tendsto (fun j : ℕ => ((j+1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hb : Tendsto (fun j : ℕ => 2*Real.pi / ((j+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero, div_eq_mul_inv] using hinv.const_mul (2*Real.pi)
    exact squeeze_zero (fun j => norm_nonneg _) (fun j => hphase j n hn) hb
  refine ⟨κ, hκ, fun j => norm_ccmApertureModulation a (κ j) _,
    fun g => (inner_ccmApertureModulation_tendsto_zero a _ g).comp hκ, ?_⟩
  have he (n : ℕ) (hn : n ∈ Finset.Icc 2 N) :
      Tendsto (fun j => (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ccmPrimePoleEdgeEnergy a (Real.log n)
          (ccmApertureModulation a (κ j) (ccmSchurPoleVector a)).1) atTop (𝓝 0) := by
    simp_rw [ccmPrimePoleEdgeEnergy_modulatedPole]
    simpa only [zero_pow two_ne_zero, zero_mul, mul_zero] using
      (((herr n (Finset.mem_Icc.mp hn).2).pow 2).mul_const
        (∫ x : ℝ, ccmPrimePoleRowDensity a (Real.log n) (ccmSchurPoleVector a).1 x)).const_mul
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
  have hsum := tendsto_finsetSum (Finset.Icc 2 N) he
  simpa only [ccmPrimePoleSchurEnergy, Finset.sum_const_zero, N] using hsum

end RHTower
