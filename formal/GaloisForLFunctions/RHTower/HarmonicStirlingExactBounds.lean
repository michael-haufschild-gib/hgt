import GaloisForLFunctions.RHTower.HarmonicSecondErrorBounds

/-!
# Exact harmonic and Stirling correction bounds

A cubic lower logarithm bound gives the lower twelfth-square harmonic correction.
The actual Stirling limit and its reciprocal difference bound give the exact
Stirling constant with a reciprocal error at every positive index.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private theorem log_ge_cubic {x : ℝ} (hx : 1 ≤ x) :
    2*((x-1)/(x+1))+2/3*((x-1)/(x+1))^3 ≤ Real.log x := by
  let f : ℝ → ℝ := fun x => Real.log x-2*((x-1)/(x+1))-2/3*((x-1)/(x+1))^3
  have hd (u : ℝ) (hu : 1 ≤ u) :
      HasDerivAt f (u⁻¹-4/(u+1)^2-4*((u-1)/(u+1))^2/(u+1)^2) u := by
    have hu0 : u ≠ 0 := by linarith
    have hu1 : u+1 ≠ 0 := by linarith
    have hq := ((hasDerivAt_id u).sub_const 1).div ((hasDerivAt_id u).add_const 1) hu1
    convert ((Real.hasDerivAt_log hu0).sub (hq.const_mul 2)).sub
      ((hq.pow 3).const_mul (2/3)) using 1 <;>
      first | rfl | (dsimp only [Pi.div_apply,id_eq]; ring)
  have hm : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro u hu; exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu; exact (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu1 : 1 ≤ u := interior_subset hu
      have hu0 : u ≠ 0 := by linarith
      have hu2 : u+1 ≠ 0 := by linarith
      rw [(hd u hu1).deriv]
      have he : u⁻¹-4/(u+1)^2-4*((u-1)/(u+1))^2/(u+1)^2 =
          (u-1)^4/(u*(u+1)^4) := by field_simp; ring
      rw [he]
      positivity
  have h := hm (show (1:ℝ) ∈ Set.Ici 1 by simp) hx hx
  simp only [f,sub_self,zero_div,mul_zero,Real.log_one] at h
  linarith only [h]

private theorem harmonic_lower_step {x : ℝ} (hx : 0 < x) :
    1/(2*x)+1/(2*(x+1))-1/(12*x^2)+1/(12*(x+1)^2) ≤
      Real.log (x+1)-Real.log x := by
  have h := log_ge_cubic (x := (x+1)/x) (by rw [le_div_iff₀ hx]; linarith)
  rw [Real.log_div (by positivity) hx.ne'] at h
  have he : 2*(((x+1)/x-1)/((x+1)/x+1))+2/3*(((x+1)/x-1)/((x+1)/x+1))^3 =
      2/(2*x+1)+2/(3*(2*x+1)^3) := by field_simp; ring
  rw [he] at h
  refine le_trans ?_ h
  have he' : 2/(2*x+1)+2/(3*(2*x+1)^3)-
      (1/(2*x)+1/(2*(x+1))-1/(12*x^2)+1/(12*(x+1)^2)) =
      (2*x^2+2*x+1)/(12*x^2*(x+1)^2*(2*x+1)^3) := by field_simp; ring
  have hp : 0 ≤ (2*x^2+2*x+1)/(12*x^2*(x+1)^2*(2*x+1)^3) := by positivity
  linarith only [he',hp]

/-- The lower twelfth-square correction keeps the leading harmonic constant. -/
theorem harmonic_mascheroni_ge_half_sub_twelfth {n : ℕ} (hn : 1 ≤ n) :
    1/(2*(n:ℝ))-1/(12*(n:ℝ)^2) ≤
      ((harmonic n:ℚ):ℝ)-Real.log n-Real.eulerMascheroniConstant := by
  let f : ℕ → ℝ := fun k => ((harmonic (k+1):ℚ):ℝ)-Real.log (k+1:ℕ)-
    1/(2*(k+1:ℕ))+1/(12*(k+1:ℕ)^2)
  have hm : Antitone f := by
    apply antitone_nat_of_succ_le
    intro k
    have h := harmonic_lower_step (x := (k+1:ℕ)) (by positivity)
    dsimp [f]
    rw [harmonic_succ (k+1),Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
    push_cast at h ⊢
    have he : ((k:ℝ)+1+1)⁻¹=2*(1/(2*((k:ℝ)+1+1))) := by field_simp
    linarith only [h,he]
  have hn' : Tendsto (fun k : ℕ => k+1) atTop atTop := tendsto_add_atTop_nat 1
  have hmain := Real.tendsto_harmonic_sub_log.comp hn'
  have hden : Tendsto (fun k : ℕ => 2*((k+1:ℕ):ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hn').const_mul_atTop (by norm_num)
  have hcorr : Tendsto (fun k : ℕ => (1:ℝ)/(2*(k+1:ℕ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hden2 : Tendsto (fun k : ℕ => 12*((k+1:ℕ):ℝ)^2) atTop atTop :=
    ((tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp
      (tendsto_natCast_atTop_atTop.comp hn')).const_mul_atTop (by norm_num)
  have hcorr2 : Tendsto (fun k : ℕ => (1:ℝ)/(12*(k+1:ℕ)^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden2
  have hf : Tendsto f atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa only [f,Function.comp_def,sub_zero,add_zero] using (hmain.sub hcorr).add hcorr2
  have h := hm.le_of_tendsto hf (n-1)
  dsimp [f] at h
  rw [Nat.sub_add_cancel hn] at h
  linarith

private theorem log_factorial_sum (N : ℕ) :
    (∑ k ∈ Icc 1 N,Real.log k)=Real.log (N.factorial:ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ N+1),ih,Nat.factorial_succ,Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

/-- Exact Stirling constant with a reciprocal upper error at every positive index. -/
theorem sum_log_Icc_exact_stirling_bounds {N : ℕ} (hN : 1 ≤ N) :
    let c := Real.log (2*Real.pi)/2
    (N:ℝ)*Real.log N-N+Real.log N/2+c ≤ ∑ k ∈ Icc 1 N,Real.log k ∧
    (∑ k ∈ Icc 1 N,Real.log k) ≤ (N:ℝ)*Real.log N-N+Real.log N/2+c+1/(12*N) := by
  dsimp only
  rw [log_factorial_sum]
  constructor
  · exact Stirling.le_log_factorial_stirling (by omega)
  let f : ℕ → ℝ := fun k => Real.log (Stirling.stirlingSeq (k+1))-1/(12*(k+1:ℕ))
  have hm : Monotone f := by
    apply monotone_nat_of_le_succ
    intro k
    have h := Stirling.log_stirlingSeq_sdiff_le (k+1)
    have he : (1:ℝ)/(12*(k+1:ℕ)*((k+1:ℕ)+1)) =
        1/(12*(k+1:ℕ))-1/(12*(k+1+1:ℕ)) := by push_cast; field_simp; ring
    rw [he] at h
    dsimp only [f]
    linarith only [h]
  have hn' : Tendsto (fun k : ℕ => k+1) atTop atTop := tendsto_add_atTop_nat 1
  have hlog := ((Real.continuousAt_log (show Real.sqrt Real.pi ≠ 0 by positivity)).tendsto).comp
    (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hn')
  have hden : Tendsto (fun k : ℕ => 12*((k+1:ℕ):ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hn').const_mul_atTop (by norm_num)
  have hcorr : Tendsto (fun k : ℕ => (1:ℝ)/(12*(k+1:ℕ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hf : Tendsto f atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    simpa only [f,Function.comp_def,sub_zero] using hlog.sub hcorr
  have h := hm.ge_of_tendsto hf (N-1)
  dsimp [f] at h
  rw [Nat.sub_add_cancel hN,Stirling.log_stirlingSeq_formula,
    Real.log_mul (by norm_num) (by positivity),Real.log_div (by positivity) (by positivity),
    Real.log_exp,Real.log_sqrt Real.pi_pos.le] at h
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne']
  linarith only [h]

end RHTower
