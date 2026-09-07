import GaloisForLFunctions.RHTower.HarmonicSecondErrorBounds

/-!
# Geometric harmonic centering

Two monotone sequences trap Euler’s constant around the average logarithm of
neighboring integers. A rational logarithm bound supplies the explicit error.
-/

noncomputable section
open Filter Topology
namespace RHTower

/-- Rational upper logarithm bound adapted to geometric harmonic centering. -/
theorem log_le_geometric_cubic {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 2*(x-1)/(x+1)+(x-1)^3/(6*x*(x+1)) := by
  let f : ℝ → ℝ := fun x => 2*(x-1)/(x+1)+(x-1)^3/(6*x*(x+1))-Real.log x
  have hd (u : ℝ) (hu : 1 ≤ u) :
      HasDerivAt f ((u-1)^4/(6*u^2*(u+1)^2)) u := by
    have hu0 : u ≠ 0 := by linarith
    have hu1 : u+1 ≠ 0 := by linarith
    have hq := (((hasDerivAt_id u).sub_const 1).const_mul 2).div
      ((hasDerivAt_id u).add_const 1) hu1
    have ht := (((hasDerivAt_id u).sub_const 1).pow 3).div
      (((hasDerivAt_id u).const_mul 6).mul ((hasDerivAt_id u).add_const 1))
      (show 6*u*(u+1) ≠ 0 by positivity)
    convert (hq.add ht).sub (Real.hasDerivAt_log hu0) using 1 <;>
      first | rfl | (dsimp only [Pi.div_apply,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id_eq]; field_simp; ring)
  have hmono : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro u hu; exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu; exact (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hd u (interior_subset hu)).deriv]
      positivity
  have h := hmono (show (1:ℝ) ∈ Set.Ici 1 from by simp) hx hx
  simpa [f] using h

private theorem geometric_log_step {x : ℝ} (hx : 0 < x) :
    2/(x+1) ≤ Real.log (x+2)-Real.log x ∧
    Real.log (x+2)-Real.log x ≤ 2/(x+1)+2/(3*x*(x+1)*(x+2)) := by
  have harg : 1+2/x=(x+2)/x := by field_simp
  have hlo := (Real.lt_log_one_add_of_pos (show 0 < 2/x by positivity)).le
  rw [harg,Real.log_div (by positivity) hx.ne'] at hlo
  have hcoeff : 2*(2/x)/(2/x+2)=2/(x+1) := by field_simp; ring
  rw [hcoeff] at hlo
  have hratio : 1 ≤ (x+2)/x := by rw [le_div_iff₀ hx]; linarith
  have hhi := log_le_geometric_cubic hratio
  rw [Real.log_div (by positivity) hx.ne'] at hhi
  have hrat : 2*((x+2)/x-1)/((x+2)/x+1)+((x+2)/x-1)^3/(6*((x+2)/x)*((x+2)/x+1)) =
      2/(x+1)+2/(3*x*(x+1)*(x+2)) := by field_simp; ring
  rw [hrat] at hhi
  exact ⟨hlo,hhi⟩

/-- The geometric harmonic centering has a sharp rational neighboring-product error. -/
theorem harmonic_mascheroni_geometric_bounds {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ ((harmonic n : ℚ) : ℝ)-Real.eulerMascheroniConstant-
      (Real.log n+Real.log ((n : ℝ)+1))/2 ∧
    ((harmonic n : ℚ) : ℝ)-Real.eulerMascheroniConstant-
      (Real.log n+Real.log ((n : ℝ)+1))/2 ≤ 1/(6*(n : ℝ)*((n : ℝ)+1)) := by
  let f : ℕ → ℝ := fun k => ((harmonic (k+1) : ℚ) : ℝ)-
    (Real.log (k+1 : ℕ)+Real.log ((k+1 : ℕ)+1 : ℝ))/2
  let g : ℕ → ℝ := fun k => f k-1/(6*(k+1 : ℕ)*((k+1 : ℕ)+1 : ℝ))
  have hanti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro k
    have hlog := (geometric_log_step (x := (k+1 : ℕ)) (by positivity)).1
    dsimp [f]
    rw [harmonic_succ (k+1),Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
    push_cast at hlog ⊢
    rw [show (k:ℝ)+1+1+1=(k:ℝ)+1+2 by ring]
    simp only [div_eq_mul_inv] at hlog ⊢
    linarith only [hlog]
  have hmono : Monotone g := by
    apply monotone_nat_of_le_succ
    intro k
    have hlog := (geometric_log_step (x := (k+1 : ℕ)) (by positivity)).2
    have hrat : 1/(6*((k:ℝ)+1)*((k:ℝ)+1+1))-1/(6*((k:ℝ)+1+1)*((k:ℝ)+1+2)) =
        1/(3*((k:ℝ)+1)*((k:ℝ)+1+1)*((k:ℝ)+1+2)) := by field_simp; ring
    dsimp [g,f]
    rw [harmonic_succ (k+1),Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
    push_cast at hlog ⊢
    rw [show (k:ℝ)+1+1+1=(k:ℝ)+1+2 by ring]
    simp only [div_eq_mul_inv] at hlog hrat ⊢
    linarith only [hlog,hrat]
  have hnat : Tendsto (fun k : ℕ => k+1) atTop atTop := tendsto_add_atTop_nat 1
  have hcast : Tendsto (fun k : ℕ => ((k+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnat
  have hinv : Tendsto (fun k : ℕ => (((k+1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hloglim : Tendsto (fun k : ℕ => Real.log (1+(((k+1 : ℕ) : ℝ))⁻¹)) atTop (nhds 0) := by
    have hone : Tendsto (fun k : ℕ => 1+(((k+1 : ℕ) : ℝ))⁻¹) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).add hinv
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hone
    simpa [Function.comp_def] using h
  have hlogeq (k : ℕ) : Real.log ((k+1 : ℕ)+1 : ℝ)-Real.log (k+1 : ℕ) =
      Real.log (1+(((k+1 : ℕ) : ℝ))⁻¹) := by
    rw [show (1+(((k+1 : ℕ) : ℝ))⁻¹)=((k+1 : ℕ)+1 : ℝ)/(k+1 : ℕ) by field_simp]
    rw [Real.log_div (by positivity) (by positivity)]
  have hf : Tendsto f atTop (nhds Real.eulerMascheroniConstant) := by
    have h := (Real.tendsto_harmonic_sub_log.comp hnat).sub (hloglim.div_const 2)
    simp only [zero_div,sub_zero,Function.comp_def] at h
    convert h using 1
    funext k
    dsimp [f]
    rw [← hlogeq]
    ring
  have hden : Tendsto (fun k : ℕ => 6*((k+1 : ℕ) : ℝ)*((k+1 : ℕ)+1 : ℝ)) atTop atTop :=
    (hcast.const_mul_atTop (by norm_num)).atTop_mul_atTop₀ (hcast.atTop_add tendsto_const_nhds)
  have hcorr : Tendsto (fun k : ℕ => (1:ℝ)/(6*(k+1 : ℕ)*((k+1 : ℕ)+1 : ℝ))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hg : Tendsto g atTop (nhds Real.eulerMascheroniConstant) := by
    simpa only [g,sub_zero] using hf.sub hcorr
  have hlow := hanti.le_of_tendsto hf (n-1)
  have hhigh := hmono.ge_of_tendsto hg (n-1)
  dsimp [g,f] at hlow hhigh
  rw [Nat.sub_add_cancel hn] at hlow hhigh
  constructor <;> linarith only [hlow,hhigh]

end RHTower
