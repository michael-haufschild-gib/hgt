import GaloisForLFunctions.RHTower.HarmonicHalfErrorBounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Second-order harmonic and half-logarithmic Stirling floors

A rational cubic logarithm correction gives a neighboring-index twelfth-square
harmonic bound. The global Stirling floor retains the half-logarithmic endpoint
needed to compare smooth and centered divisor-hyperbola contributions.
-/

noncomputable section
open Filter Topology
namespace RHTower

/-- Cubic correction to the rational trapezoid upper bound for logarithm. -/
theorem log_le_half_sub_inv_cubic {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x-x⁻¹)/2 - 4/3*((x-1)/(x+1))^3 := by
  let f : ℝ → ℝ := fun x => (x-x⁻¹)/2 - 4/3*((x-1)/(x+1))^3 - Real.log x
  have hd (u : ℝ) (hu : 1 ≤ u) :
      HasDerivAt f ((1+(u^2)⁻¹)/2 - 4*((u-1)/(u+1))^2*(2/(u+1)^2) - u⁻¹) u := by
    have hu0 : u ≠ 0 := by linarith
    have hu1 : u+1 ≠ 0 := by linarith
    have hq := ((hasDerivAt_id u).sub_const 1).div ((hasDerivAt_id u).add_const 1) hu1
    convert ((((hasDerivAt_id u).sub (hasDerivAt_inv hu0)).div_const 2).sub
      ((hq.pow 3).const_mul (4/3))).sub (Real.hasDerivAt_log hu0) using 1 <;>
      first | rfl | (dsimp only [Pi.div_apply,id_eq]; ring)
  have hmono : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro u hu; exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu; exact (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu1 : 1 ≤ u := interior_subset hu
      have hu0 : u ≠ 0 := by linarith
      have hu2 : u+1 ≠ 0 := by linarith
      rw [(hd u hu1).deriv]
      have heq : (1+(u^2)⁻¹)/2 - 4*((u-1)/(u+1))^2*(2/(u+1)^2) - u⁻¹ =
          (u-1)^4*(u^2+6*u+1)/(2*u^2*(u+1)^4) := by field_simp; ring
      rw [heq]
      positivity
  have h := hmono (show (1:ℝ) ∈ Set.Ici 1 from by simp) hx hx
  simpa [f] using h

private theorem harmonic_correction_step {x : ℝ} (hx : 0 < x) :
    Real.log (x+1)-Real.log x ≤
      1/(2*x)+1/(2*(x+1))-1/(12*(x+1)^2)+1/(12*(x+2)^2) := by
  have hratio : 1 ≤ (x+1)/x := by rw [le_div_iff₀ hx]; linarith
  have hlog := log_le_half_sub_inv_cubic hratio
  rw [Real.log_div (by positivity) hx.ne'] at hlog
  have hrewrite : ((x+1)/x-((x+1)/x)⁻¹)/2 - 4/3*(((x+1)/x-1)/((x+1)/x+1))^3 =
      1/(2*x)+1/(2*(x+1))-4/(3*(2*x+1)^3) := by field_simp; ring
  rw [hrewrite] at hlog
  have hcorr : 1/(12*(x+1)^2)-1/(12*(x+2)^2) ≤ 4/(3*(2*x+1)^3) := by
    field_simp
    nlinarith [sq_nonneg x,sq_nonneg (x^2)]
  linarith

/-- A second-order harmonic correction with a neighboring-index denominator. -/
theorem harmonic_mascheroni_le_half_sub_twelfth {n : ℕ} (hn : 1 ≤ n) :
    ((harmonic n : ℚ) : ℝ)-Real.log n-Real.eulerMascheroniConstant ≤
      1/(2*(n : ℝ))-1/(12*((n : ℝ)+1)^2) := by
  let f : ℕ → ℝ := fun k => ((harmonic (k+1) : ℚ) : ℝ)-Real.log (k+1 : ℕ)-
    1/(2*(k+1 : ℕ))+1/(12*((k+1 : ℕ)+1 : ℝ)^2)
  have hmono : Monotone f := by
    apply monotone_nat_of_le_succ
    intro k
    have hlog := harmonic_correction_step (x := (k+1 : ℕ)) (by positivity)
    dsimp [f]
    rw [harmonic_succ (k+1),Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
    push_cast at hlog ⊢
    have hhalf : ((k : ℝ)+1+1)⁻¹ = 2*(1/(2*((k : ℝ)+1+1))) := by field_simp
    rw [show (k:ℝ)+1+1+1=(k:ℝ)+1+2 by ring]
    linarith only [hlog,hhalf]
  have hnat : Tendsto (fun k : ℕ => k+1) atTop atTop := tendsto_add_atTop_nat 1
  have hmain := Real.tendsto_harmonic_sub_log.comp hnat
  have hden1 : Tendsto (fun k : ℕ => 2*((k+1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hnat).const_mul_atTop (by norm_num)
  have hcorr1 : Tendsto (fun k : ℕ => (1:ℝ)/(2*(k+1 : ℕ))) atTop (nhds (0:ℝ)) :=
    tendsto_const_nhds.div_atTop hden1
  have hden2 : Tendsto (fun k : ℕ => 12*((k+1 : ℕ)+1 : ℝ)^2) atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop (by norm_num)
    exact (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp
      ((tendsto_natCast_atTop_atTop.comp hnat).atTop_add tendsto_const_nhds)
  have hcorr2 : Tendsto (fun k : ℕ => 1/(12*((k+1 : ℕ)+1 : ℝ)^2)) atTop (nhds (0:ℝ)) :=
    tendsto_const_nhds.div_atTop hden2
  have hf : Tendsto f atTop (nhds Real.eulerMascheroniConstant) := by
    simpa only [f,Function.comp_def,sub_zero,add_zero] using (hmain.sub hcorr1).add hcorr2
  have h := hmono.ge_of_tendsto hf (n-1)
  dsimp [f] at h
  rw [Nat.sub_add_cancel hn] at h
  linarith

private theorem sum_log_Icc_eq_log_factorial (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, Real.log k) = Real.log (N.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1),ih,Nat.factorial_succ,Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

/-- A rational global Stirling floor retaining the half-logarithmic endpoint. -/
theorem sum_log_Icc_ge_half_log_stirling {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ)*Real.log N-N+Real.log N/2+11/12 ≤
      ∑ k ∈ Finset.Icc 1 N, Real.log k := by
  have h := Stirling.log_stirlingSeq_bounded_by_constant (N-1)
  rw [Nat.sub_add_cancel hN,Stirling.log_stirlingSeq_formula,
    Real.log_mul (by norm_num) (by positivity),
    Real.log_div (by positivity) (by positivity),Real.log_exp] at h
  rw [sum_log_Icc_eq_log_factorial]
  linarith only [h]

end RHTower
