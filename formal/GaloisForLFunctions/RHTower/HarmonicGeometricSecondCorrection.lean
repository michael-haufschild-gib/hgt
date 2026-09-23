import GaloisForLFunctions.RHTower.HarmonicGeometricBounds

/-!
# Second geometric harmonic correction and symmetric logarithm control

A rational lower bound for the symmetric logarithm gives the next geometric
harmonic correction. Pairing the two logarithmic branches retains a quartic
remainder needed for signed smooth divisor square-block sums.
-/

noncomputable section
open Filter Topology
namespace RHTower

private theorem symmetric_log_lower {t : ℝ} (ht0 : 0≤t) (ht1 : t<1) :
    t+t^(3 : ℕ)/(3*(1-t^(2 : ℕ)))-2*t^(5 : ℕ)/(15*(1-t^(2 : ℕ))^(2 : ℕ))≤
      (Real.log (1+t)-Real.log (1-t))/2 := by
  let f : ℝ → ℝ := fun u => (Real.log (1+u)-Real.log (1-u))/2-u-
    u^(3 : ℕ)/(3*(1-u^(2 : ℕ)))+2*u^(5 : ℕ)/(15*(1-u^(2 : ℕ))^(2 : ℕ))
  have hd (u : ℝ) (hu : u∈Set.Ico (0:ℝ) 1) :
      HasDerivAt f (8*u^(6 : ℕ)/(15*(1-u^(2 : ℕ))^(3 : ℕ))) u := by
    have hplus : 1+u≠0 := by linarith [hu.1]
    have hminus : 1-u≠0 := by linarith [hu.2]
    have hs : 0<1-u^(2 : ℕ) := by nlinarith [hu.1,hu.2]
    have h1 := ((hasDerivAt_id u).const_add 1).log hplus
    have h2 := ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).log hminus
    have hden := (hasDerivAt_const u (1:ℝ)).sub ((hasDerivAt_id u).pow 2)
    have h3 := ((hasDerivAt_id u).pow 3).div (hden.const_mul 3) (by change 3*(1-u^(2 : ℕ))≠0; positivity)
    have h4 := (((hasDerivAt_id u).pow 5).const_mul 2).div
      ((hden.pow 2).const_mul 15) (by change 15*(1-u^(2 : ℕ))^(2 : ℕ)≠0; positivity)
    convert ((((h1.sub h2).div_const 2).sub (hasDerivAt_id u)).sub h3).add h4 using 1 <;>
      first
      | rfl
      | dsimp only [Pi.div_apply,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id_eq]
        field_simp [hplus,hminus,hs.ne']
        ring
  have hm : MonotoneOn f (Set.Ico (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · intro u hu; exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu; exact (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' := interior_subset hu
      rw [(hd u hu').deriv]
      have hs : 0<1-u^(2 : ℕ) := by nlinarith [hu'.1,hu'.2]
      positivity
  have h := hm (by simp) ⟨ht0,ht1⟩ ht0
  dsimp [f] at h
  norm_num at h
  linarith only [h]

private theorem geometric_second_step {x : ℝ} (hx : 0<x) :
    1/(6*x*(x+1))-1/(30*(x*(x+1))^(2 : ℕ))-
      (1/(6*(x+1)*(x+2))-1/(30*((x+1)*(x+2))^(2 : ℕ)))≤
      (Real.log (x+2)-Real.log x)/2-1/(x+1) := by
  have ht0 : 0≤1/(x+1) := by positivity
  have ht1 : 1/(x+1)<1 := by rw [div_lt_one (by positivity)]; linarith
  have h := symmetric_log_lower ht0 ht1
  have hp : 1+1/(x+1)=(x+2)/(x+1) := by field_simp; ring
  have hm : 1-1/(x+1)=x/(x+1) := by field_simp; ring
  rw [hp,hm,Real.log_div (by positivity) (by positivity),
    Real.log_div hx.ne' (by positivity)] at h
  have he : (1/(x+1))^(3 : ℕ)/(3*(1-(1/(x+1))^(2 : ℕ)))-
      2*(1/(x+1))^(5 : ℕ)/(15*(1-(1/(x+1))^(2 : ℕ))^(2 : ℕ)) =
      1/(6*x*(x+1))-1/(30*(x*(x+1))^(2 : ℕ))-
        (1/(6*(x+1)*(x+2))-1/(30*((x+1)*(x+2))^(2 : ℕ))) := by
    have hd : 1-(1/(x+1))^(2 : ℕ)=x*(x+2)/(x+1)^(2 : ℕ) := by field_simp; ring
    rw [hd]
    field_simp [hx.ne',show x+1≠0 by positivity,show x+2≠0 by positivity]
    ring
  linarith only [h,he]

/-- The geometric harmonic remainder retains its reciprocal-product
correction with an explicit second-order lower error. -/
theorem harmonic_mascheroni_geometric_lower_second {n : ℕ} (hn : 1≤n) :
    1/(6*(n:ℝ)*(n+1))-1/(30*((n:ℝ)*(n+1))^(2 : ℕ))≤
      ((harmonic n:ℚ):ℝ)-Real.eulerMascheroniConstant-
        (Real.log n+Real.log ((n:ℝ)+1))/2 := by
  let f : ℕ → ℝ := fun k => ((harmonic (k+1):ℚ):ℝ)-
    (Real.log (k+1:ℕ)+Real.log ((k+1:ℕ)+1:ℝ))/2-
    1/(6*(k+1:ℕ)*((k+1:ℕ)+1:ℝ))+1/(30*((k+1:ℕ)*((k+1:ℕ)+1:ℝ))^(2 : ℕ))
  have hm : Antitone f := by
    apply antitone_nat_of_succ_le
    intro k
    have h := geometric_second_step (x := (k+1:ℕ)) (by positivity)
    dsimp [f]
    rw [harmonic_succ (k+1),Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
    push_cast at h ⊢
    rw [show (k:ℝ)+1+1+1=(k:ℝ)+1+2 by ring]
    simp only [div_eq_mul_inv] at h ⊢
    linarith only [h]
  have hnat : Tendsto (fun k : ℕ => k+1) atTop atTop := tendsto_add_atTop_nat 1
  have hcast : Tendsto (fun k : ℕ => ((k+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnat
  have hi : Tendsto (fun k : ℕ => (((k+1:ℕ):ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hlog : Tendsto (fun k : ℕ => Real.log (1+(((k+1:ℕ):ℝ))⁻¹)) atTop (𝓝 0) := by
    have hone : Tendsto (fun k : ℕ => 1+(((k+1:ℕ):ℝ))⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).add hi
    simpa [Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hone
  have hmain : Tendsto (fun k : ℕ => ((harmonic (k+1):ℚ):ℝ)-
      (Real.log (k+1:ℕ)+Real.log ((k+1:ℕ)+1:ℝ))/2) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    have h := (Real.tendsto_harmonic_sub_log.comp hnat).sub (hlog.div_const 2)
    simp only [zero_div,sub_zero,Function.comp_def] at h
    convert h using 1
    funext k
    have he : 1+(((k+1:ℕ):ℝ))⁻¹=((k+1:ℕ)+1:ℝ)/(k+1:ℕ) := by field_simp
    rw [he,Real.log_div (by positivity) (by positivity)]
    ring
  have hprod : Tendsto (fun k : ℕ => ((k+1:ℕ):ℝ)*((k+1:ℕ)+1:ℝ)) atTop atTop :=
    hcast.atTop_mul_atTop₀ (hcast.atTop_add tendsto_const_nhds)
  have hc1 : Tendsto (fun k : ℕ => (1:ℝ)/(6*(k+1:ℕ)*((k+1:ℕ)+1:ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1:ℝ))).div_atTop (hprod.const_mul_atTop (by norm_num : (0:ℝ)<6))
    simpa only [mul_assoc] using h
  have hc2 : Tendsto (fun k : ℕ => (1:ℝ)/(30*((k+1:ℕ)*((k+1:ℕ)+1:ℝ))^(2 : ℕ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (((tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp hprod).const_mul_atTop (by norm_num))
  have hf : Tendsto f atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa only [f,sub_zero,add_zero] using (hmain.sub hc1).add hc2
  have h := hm.le_of_tendsto hf (n-1)
  dsimp [f] at h
  rw [Nat.sub_add_cancel hn] at h
  linarith only [h]

/-- Pairing both logarithmic branches gives a quadratic term with a
controlled quartic remainder on the entire symmetric interval. -/
theorem log_symmetric_entropy_le_quartic {t : ℝ} (ht0 : 0≤t) (ht1 : t<1) :
    (1+t)*Real.log (1+t)+(1-t)*Real.log (1-t)≤t^(2 : ℕ)+t^(4 : ℕ)/(6*(1-t^(2 : ℕ))) := by
  let f : ℝ → ℝ := fun u => u^(2 : ℕ)+u^(4 : ℕ)/(6*(1-u^(2 : ℕ)))-
    ((1+u)*Real.log (1+u)+(1-u)*Real.log (1-u))
  have hd (u : ℝ) (hu : u∈Set.Ico (0:ℝ) 1) :
      HasDerivAt f (2*u+2*u^(3 : ℕ)/(3*(1-u^(2 : ℕ)))+u^(5 : ℕ)/(3*(1-u^(2 : ℕ))^(2 : ℕ))-
        (Real.log (1+u)-Real.log (1-u))) u := by
    have hp : 1+u≠0 := by linarith [hu.1]
    have hn : 1-u≠0 := by linarith [hu.2]
    have hs : 0<1-u^(2 : ℕ) := by nlinarith [hu.1,hu.2]
    have h1 := (hasDerivAt_id u).const_add 1
    have h2 := (hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)
    have h3 := ((hasDerivAt_id u).pow 4).div
      (((hasDerivAt_const u (1:ℝ)).sub ((hasDerivAt_id u).pow 2)).const_mul 6)
      (by positivity)
    convert (((hasDerivAt_id u).pow 2).add h3).sub
      ((h1.mul (h1.log hp)).add (h2.mul (h2.log hn))) using 1 <;>
      first
      | rfl
      | dsimp only [Pi.div_apply,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id_eq]
        field_simp [hp,hn,hs.ne']
        ring
  have hm : MonotoneOn f (Set.Ico (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · intro u hu; exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu; exact (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' := interior_subset hu
      have hp : 0<1+u := by linarith [hu'.1]
      have hn : 0<1-u := by linarith [hu'.2]
      have hs : 0<1-u^(2 : ℕ) := by nlinarith [hu'.1,hu'.2]
      have h := log_le_geometric_cubic (x := (1+u)/(1-u))
        (by rw [le_div_iff₀ hn]; linarith [hu'.1])
      rw [Real.log_div hp.ne' hn.ne'] at h
      have he : 2*((1+u)/(1-u)-1)/((1+u)/(1-u)+1)+
          ((1+u)/(1-u)-1)^(3 : ℕ)/(6*((1+u)/(1-u))*((1+u)/(1-u)+1)) =
          2*u+2*u^(3 : ℕ)/(3*(1-u^(2 : ℕ))) := by
        field_simp [hp.ne',hn.ne',hs.ne']
        ring
      rw [he] at h
      rw [(hd u hu').deriv]
      have hr : 0≤u^(5 : ℕ)/(3*(1-u^(2 : ℕ))^(2 : ℕ)) := by have hu0 := hu'.1; positivity
      linarith only [h,hr]
  have h := hm (by simp) ⟨ht0,ht1⟩ ht0
  dsimp [f] at h
  norm_num at h
  linarith only [h]

end RHTower
