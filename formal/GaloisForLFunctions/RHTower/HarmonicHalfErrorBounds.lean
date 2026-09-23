import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Neighboring half-reciprocal bounds for the harmonic error

The centered harmonic remainder lies between `1/(2(n+1))` and `1/(2n)`.
A rational trapezoid upper bound for logarithm constructs the monotone lower
sequence complementary to the corrected upper sequence. Both converge to the
same Euler constant; no finite numerical approximation enters the proof.
-/

noncomputable section
open Filter Topology
namespace RHTower

/-- Trapezoid upper bound for the logarithm on the positive unit ray. -/
theorem log_le_half_sub_inv {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x - x⁻¹) / 2 := by
  let f : ℝ → ℝ := fun x => (x - x⁻¹) / 2 - Real.log x
  have hd (u : ℝ) (hu : 1 ≤ u) :
      HasDerivAt f ((1 + (u^(2 : ℕ))⁻¹) / 2 - u⁻¹) u := by
    have hu0 : u ≠ 0 := by linarith
    convert (((hasDerivAt_id u).sub (hasDerivAt_inv hu0)).div_const 2).sub
      (Real.hasDerivAt_log hu0) using 1 <;> first | rfl | ring
  have hmono : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro u hu
      exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu
      exact (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu1 : 1 ≤ u := interior_subset hu
      have hu0 : 0 < u := by linarith
      rw [(hd u hu1).deriv]
      field_simp
      nlinarith [sq_nonneg (u-1)]
  have h := hmono (show (1:ℝ) ∈ Set.Ici 1 from by simp) hx hx
  simpa [f] using h

/-- The harmonic error lies between the two neighboring half-reciprocal corrections. -/
theorem harmonic_mascheroni_half_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 / (2 * ((n : ℝ)+1)) ≤
      ((harmonic n : ℚ) : ℝ) - Real.log n - Real.eulerMascheroniConstant ∧
    ((harmonic n : ℚ) : ℝ) - Real.log n - Real.eulerMascheroniConstant ≤
      1 / (2 * (n : ℝ)) := by
  have hlo := eulerMascheroniConstant_lt_correctedUpper n
  simp only [eulerMascheroniCorrectedUpper, show n ≠ 0 by omega, if_false,
    Real.eulerMascheroniSeq'] at hlo
  constructor
  · linarith
  · let f : ℕ → ℝ := fun k => ((harmonic (k+1) : ℚ) : ℝ) -
      Real.log (k+1 : ℕ) - 1 / (2 * (k+1 : ℕ))
    have hmono : Monotone f := by
      apply monotone_nat_of_le_succ
      intro k
      have hk0 : (0:ℝ) < (k+1 : ℕ) := by positivity
      have hk1 : (0:ℝ) < (k+1 : ℕ)+1 := by positivity
      have hratio : 1 ≤ ((k+1 : ℕ)+1 : ℝ) / (k+1 : ℕ) := by
        rw [le_div_iff₀ hk0]; linarith
      have hlog := log_le_half_sub_inv hratio
      rw [Real.log_div hk1.ne' hk0.ne'] at hlog
      have hrat :
          ((((k+1 : ℕ)+1 : ℝ) / (k+1 : ℕ)) -
            ((((k+1 : ℕ)+1 : ℝ) / (k+1 : ℕ)))⁻¹) / 2 =
          1 / (2 * (k+1 : ℕ)) + 1 / (2 * ((k+1 : ℕ)+1 : ℝ)) := by
        field_simp
        ring
      rw [hrat] at hlog
      dsimp [f]
      rw [harmonic_succ (k+1), Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      push_cast at hlog ⊢
      have hhalf : ((k : ℝ)+1+1)⁻¹ = 2 * (1 / (2 * ((k : ℝ)+1+1))) := by
        field_simp
      linarith only [hlog, hhalf]
    have hnat : Tendsto (fun k : ℕ => k+1) atTop atTop :=
      Filter.tendsto_add_atTop_nat 1
    have hmain := Real.tendsto_harmonic_sub_log.comp hnat
    have hden : Tendsto (fun k : ℕ => 2 * ((k+1 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp hnat).const_mul_atTop (by norm_num)
    have hcorr : Tendsto (fun k : ℕ => 1 / (2 * ((k+1 : ℕ) : ℝ))) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hden
    have hf : Tendsto f atTop (nhds Real.eulerMascheroniConstant) := by
      simpa only [f, Function.comp_def, sub_zero] using hmain.sub hcorr
    have h := hmono.ge_of_tendsto hf (n-1)
    dsimp [f] at h
    rw [Nat.sub_add_cancel hn] at h
    linarith

end RHTower
