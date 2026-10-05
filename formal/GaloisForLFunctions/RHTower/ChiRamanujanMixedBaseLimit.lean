import GaloisForLFunctions.RHTower.ChiRamanujanBoundaryEulerProduct
import GaloisForLFunctions.RHTower.ChiRamanujanMixedProfileCancellation
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# The original mixed unlabelled Euler product and both cofactors

The full finite local product, with one near-pole variable and one fixed
nonzero real frequency, has its logarithmic limit. The exact factorization
retains both frequency signs, the locally uniform regular cubic correction,
and the actual boundary and near-pole Euler products at the original cutoff.
Its nonzero limit proves simultaneous eventual local nonvanishing.

Both original growing coprime cofactors are then attached. Their zeta factor
cancels the off-pole Euler limit, giving the complete unlabelled trace divided
by `log N` squared. No source bound, convergence or nonvanishing is assumed.
Uniform physical-profile/tail control remains a separate obligation.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace RHTower.BAGTrace

private theorem cutoff_tendsto :
    Tendsto Sieve.primeSubtypeLE atTop (atTop : Filter (Finset Nat.Primes)) := by
  apply tendsto_atTop.mpr
  intro S
  filter_upwards [eventually_ge_atTop (S.sup fun p => p.val)] with N hN
  intro p hp
  exact Sieve.mem_primeSubtypeLE.mpr ((Finset.le_sup hp).trans hN)

private theorem moving_drift_zero (u : ℂ) :
    Tendsto (fun N : ℕ => u/(Real.log N : ℂ)) atTop (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp (tendsto_drift_zero 1)
  simpa only [Function.comp_def,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_zero,mul_zero,mul_one_div] using h.const_mul u

private theorem moving_regular_limit (u v : ℂ) (tau : ℝ) :
    Tendsto (fun N : ℕ => ∏ p ∈ Sieve.primeSubtypeLE N,
      cubicPrimeFactor p 1 (u/(Real.log N : ℂ)) (v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I))
      atTop (𝓝 1) := by
  have hc : TendstoLocallyUniformlyOn
      (fun N => fun w : ℂ × ℂ × ℂ => ∏ p ∈ Sieve.primeSubtypeLE N,
        cubicPrimeFactor p w.1 w.2.1 w.2.2)
      (fun w => cubicEulerCorrection w.1 w.2.1 w.2.2) atTop cubicTube := by
    intro w hw r hr
    obtain ⟨t,ht,htr⟩ := hasProdLocallyUniformlyOn_cubicPrimeFactor w hw r hr
    exact ⟨t,ht,cutoff_tendsto.eventually htr⟩
  have hx : (1,0,(tau : ℂ)*Complex.I) ∈ cubicTube := by norm_num [cubicTube]
  have hg : Tendsto (fun N : ℕ => (1,u/(Real.log N : ℂ),v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I))
      atTop (𝓝[cubicTube] (1,0,(tau : ℂ)*Complex.I)) := by
    apply tendsto_nhdsWithin_iff.mpr
    have ht := (tendsto_const_nhds (x := (1 : ℂ))).prodMk_nhds
      ((moving_drift_zero u).prodMk_nhds
        ((moving_drift_zero v).add_const ((tau : ℂ)*Complex.I)))
    simp only [zero_add] at ht
    exact ⟨ht,ht.eventually (isOpen_cubicTube.mem_nhds hx)⟩
  simpa only [cubicEulerCorrection_zero_left] using
    hc.tendsto_comp (continuousOn_cubicEulerCorrection _ hx) hx hg

private theorem base_complement_ne (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    1-cubicPrimeBase p s ≠ 0 := by
  have h : ‖cubicPrimeBase p s‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (neg_neg_of_pos hs)
  intro he
  rw [← sub_eq_zero.mp he,norm_one] at h
  exact (lt_irrefl _ h)

private theorem moving_local_factor (p : Nat.Primes) {α β : ℂ}
    (hα : |α.re| < 1/16) (hβ : |β.re| < 1/16) :
    (1-cubicPrimeBase p (1+α))*(1-cubicPrimeBase p (1+β))*
      weightedEuler (cubicPrimeBase p 1) (cubicPrimeBase p (1+α))
        (cubicPrimeBase p (1+β)) =
      cubicPrimeFactor p 1 α β *
      ((1-cubicPrimeBase p (1+(β-α)))*(1-cubicPrimeBase p (1+(α-β))))/
      ((1-cubicPrimeBase p (1-α))*(1-cubicPrimeBase p (1-β))) := by
  have ha := abs_lt.mp hα
  have hb := abs_lt.mp hβ
  have hz := base_complement_ne p (s := 1) (by norm_num)
  have hx := base_complement_ne p (s := 1+α) (by simp only [Complex.add_re,Complex.one_re]; linarith)
  have hy := base_complement_ne p (s := 1+β) (by simp only [Complex.add_re,Complex.one_re]; linarith)
  have hxi := base_complement_ne p (s := 1-α) (by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have hyi := base_complement_ne p (s := 1-β) (by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have huv := base_complement_ne p (s := 1+(α-β)) (by simp only [Complex.add_re,Complex.sub_re,Complex.one_re]; linarith)
  have hvu := base_complement_ne p (s := 1+(β-α)) (by simp only [Complex.add_re,Complex.sub_re,Complex.one_re]; linarith)
  have h := weightedEuler_eq_regularFactor (cubicPrimeBase_ne_zero p α)
    (cubicPrimeBase_ne_zero p β) hz
    (by simpa only [cubicPrimeBase_mul] using hx)
    (by simpa only [cubicPrimeBase_mul] using hy)
    (by simpa only [cubicPrimeBase_div] using hxi)
    (by simpa only [cubicPrimeBase_div] using hyi)
    (by simpa only [cubicPrimeBase_div,cubicPrimeBase_mul] using huv)
    (by simpa only [cubicPrimeBase_div,cubicPrimeBase_mul] using hvu)
  simp only [cubicPrimeBase_div,cubicPrimeBase_mul] at h
  rw [h,cubicPrimeFactor]
  field_simp


private def primeEuler (delta : ℂ) (N : ℕ) : ℂ :=
  ∏ p ∈ Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1+delta))

private theorem primeEuler_eq (delta : ℂ) (N : ℕ) :
    primeEuler delta N=∏ p ∈ Nat.primesLE N,(1-(p : ℂ)^(-(1+delta))) := by
  exact Finset.prod_subtype_of_mem (s := Nat.primesLE N)
    (fun n : ℕ => (1-(n : ℂ)^(-(1+delta)))) (fun n hn => Nat.prime_of_mem_primesLE hn)

private theorem mixed_euler_limit (tau : ℝˣ) (w : ℂ) :
    Tendsto (fun N : ℕ => primeEuler (w/(Real.log N : ℂ)+(tau : ℂ)*Complex.I) N)
      atTop (𝓝 (riemannZeta (1+(tau : ℂ)*Complex.I))⁻¹) := by
  apply (criticalMixedEulerProduct_tendsto tau (-w)).congr
  intro N
  rw [primeEuler_eq]
  apply Finset.prod_congr rfl
  intro p _
  congr 2
  ring

private theorem prime_cutoff_prod (N : ℕ) (f : ℕ → ℂ) :
    (∏ p : Sieve.primeSubtypeLE N,f p.val.val) = ∏ n ∈ Nat.primesLE N,f n := by
  calc (∏ p : Sieve.primeSubtypeLE N,f p.val.val) =
      ∏ p ∈ Sieve.primeSubtypeLE N,f p.val :=
        Finset.prod_coe_sort (Sieve.primeSubtypeLE N) (fun p : Nat.Primes => f p.val)
    _ = _ := Finset.prod_subtype_of_mem f (fun n hn => Nat.prime_of_mem_primesLE hn)

private theorem near_euler_eq (u : ℂ) (N : ℕ) :
    primeEuler (-u/(Real.log N : ℂ)) N=
      criticalMovingEulerRatio u N*(criticalPrimeNormalization (Sieve.primeSubtypeLE N) : ℂ) := by
  have hA : (criticalPrimeNormalization (Sieve.primeSubtypeLE N) : ℂ) =
      ∏ p : Sieve.primeSubtypeLE N,(1-((p : Nat.Primes) : ℂ)⁻¹) := by
    unfold criticalPrimeNormalization
    push_cast
    simp only [one_div]
  have hr : primeEuler (-u/(Real.log N : ℂ)) N /
      (criticalPrimeNormalization (Sieve.primeSubtypeLE N) : ℂ) = criticalMovingEulerRatio u N := by
    rw [hA,primeEuler_eq]
    rw [prime_cutoff_prod N (fun n => 1-(n : ℂ)⁻¹),← Finset.prod_div_distrib]
    unfold criticalMovingEulerRatio
    apply Finset.prod_congr rfl
    intro p _
    congr 3
    ring
  exact (div_eq_iff (Complex.ofReal_ne_zero.mpr (criticalPrimeNormalization_pos _).ne')).mp hr

private theorem near_euler_scaled_limit (u : ℂ) :
    Tendsto (fun N : ℕ => primeEuler (-u/(Real.log N : ℂ)) N*(Real.log N : ℂ)) atTop
      (𝓝 (Complex.exp (-criticalEulerExponent u)*(Real.exp (-Real.eulerMascheroniConstant) : ℂ))) := by
  have h := (criticalMovingEulerRatio_tendsto u).mul criticalPrimeNormalization_logScale_tendsto
  apply h.congr
  intro N
  rw [near_euler_eq]
  ring

private theorem boundary_zeta_ne (tau : ℝ) : riemannZeta (1+(tau : ℂ)*Complex.I) ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (by simp)

/-- The original unlabelled local product with both cofactor Euler factors,
one near-pole variable and one fixed off-pole frequency. -/
def criticalMixedBaseProduct (u v : ℂ) (tau : ℝ) (N : ℕ) : ℂ :=
  ∏ p ∈ Sieve.primeSubtypeLE N,
    (1-cubicPrimeBase p (1+u/(Real.log N : ℂ)))*
    (1-cubicPrimeBase p (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)))*
      weightedEuler (cubicPrimeBase p 1) (cubicPrimeBase p (1+u/(Real.log N : ℂ)))
        (cubicPrimeBase p (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)))

private theorem mixed_base_factorization (u v : ℂ) (tau : ℝ) (N : ℕ)
    (hu : |(u/(Real.log N : ℂ)).re| < 1/16)
    (hv : |(v/(Real.log N : ℂ)).re| < 1/16) :
    criticalMixedBaseProduct u v tau N =
      (∏ p ∈ Sieve.primeSubtypeLE N,cubicPrimeFactor p 1
        (u/(Real.log N : ℂ)) (v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)) *
      (primeEuler ((v-u)/(Real.log N : ℂ)+(tau : ℂ)*Complex.I) N*
        primeEuler ((u-v)/(Real.log N : ℂ)+((-tau : ℝ) : ℂ)*Complex.I) N) /
      (primeEuler (-u/(Real.log N : ℂ)) N*
        primeEuler (-v/(Real.log N : ℂ)+((-tau : ℝ) : ℂ)*Complex.I) N) := by
  have hv' : |(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I).re| < 1/16 := by simpa using hv
  have h1 : v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I-u/(Real.log N : ℂ)=
      (v-u)/(Real.log N : ℂ)+(tau : ℂ)*Complex.I := by ring
  have h2 : u/(Real.log N : ℂ)-(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)=
      (u-v)/(Real.log N : ℂ)+((-tau : ℝ) : ℂ)*Complex.I := by push_cast; ring
  have h3 : 1-u/(Real.log N : ℂ)=1+ -u/(Real.log N : ℂ) := by ring
  have h4 : 1-(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)=
      1+(-v/(Real.log N : ℂ)+((-tau : ℝ) : ℂ)*Complex.I) := by push_cast; ring
  unfold criticalMixedBaseProduct
  simp_rw [moving_local_factor _ hu hv',h1,h2,h3,h4]
  simp only [Finset.prod_mul_distrib,Finset.prod_div_distrib,primeEuler]

private theorem moving_small (u : ℂ) :
    ∀ᶠ N : ℕ in atTop, |(u/(Real.log N : ℂ)).re| < 1/16 := by
  have h := ((Complex.continuous_re.tendsto _).comp (moving_drift_zero u)).abs
  exact h.eventually (gt_mem_nhds (by norm_num : |(0 : ℂ).re| < 1/16))

private theorem normalization_ne : (Real.exp (-Real.eulerMascheroniConstant) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

/-- The complete original mixed unlabelled product has its logarithmic limit,
including both signs of the off-pole prime frequency. -/
theorem criticalMixedBaseProduct_tendsto (u v : ℂ) (tau : ℝˣ) :
    Tendsto (fun N : ℕ => criticalMixedBaseProduct u v tau N/(Real.log N : ℂ)) atTop
      (𝓝 (criticalEulerCarrier u/
        ((Real.exp (-Real.eulerMascheroniConstant) : ℂ)*riemannZeta (1+(tau : ℂ)*Complex.I)))) := by
  have h := ((moving_regular_limit u v tau).mul
    ((mixed_euler_limit tau (v-u)).mul (mixed_euler_limit (-tau) (u-v)))).div
    ((near_euler_scaled_limit u).mul (mixed_euler_limit (-tau) (-v)))
    (mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) normalization_ne)
      (inv_ne_zero (boundary_zeta_ne (-tau))))
  simp only [Units.val_neg] at h
  have he : (1 : ℂ)*((riemannZeta (1+(tau : ℂ)*Complex.I))⁻¹*
        (riemannZeta (1+((-tau : ℝ) : ℂ)*Complex.I))⁻¹)/
      ((Complex.exp (-criticalEulerExponent u)*(Real.exp (-Real.eulerMascheroniConstant) : ℂ))*
        (riemannZeta (1+((-tau : ℝ) : ℂ)*Complex.I))⁻¹) =
      criticalEulerCarrier u/
        ((Real.exp (-Real.eulerMascheroniConstant) : ℂ)*riemannZeta (1+(tau : ℂ)*Complex.I)) := by
    rw [criticalEulerCarrier,Complex.exp_neg]
    field_simp [boundary_zeta_ne tau,boundary_zeta_ne (-(tau : ℝ)),normalization_ne,Complex.exp_ne_zero]
    exact div_self (by simpa only [mul_comm] using boundary_zeta_ne (-(tau : ℝ)))
  rw [he] at h
  apply h.congr'
  filter_upwards [moving_small u,moving_small v] with N hu hv
  rw [mixed_base_factorization u v tau N hu hv]
  simp only [Pi.div_apply,div_eq_mul_inv,mul_inv_rev]
  ring

private theorem moving_re_positive (u : ℂ) :
    ∀ᶠ N : ℕ in atTop, 0 < (1+u/(Real.log N : ℂ)).re := by
  have ht := (Complex.continuous_re.tendsto _).comp
    ((tendsto_const_nhds (x := (1 : ℂ))).add (moving_drift_zero u))
  exact ht.eventually (lt_mem_nhds (by norm_num : (0 : ℝ)<(1+(0 : ℂ)).re))

private theorem moving_point_ne_one (u : ℂˣ) {N : ℕ} (hN : 2 ≤ N) :
    1+(u : ℂ)/(Real.log N : ℂ) ≠ 1 := by
  have hlog : (Real.log N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  intro hs
  have hz : (u : ℂ)/(Real.log N : ℂ) = 0 := by linear_combination hs
  exact (div_ne_zero u.ne_zero hlog) hz

private theorem positive_moving_residue (u : ℂˣ) :
    Tendsto (fun N : ℕ => ((u : ℂ)/(Real.log N : ℂ))*
      riemannZeta (1+(u : ℂ)/(Real.log N : ℂ))) atTop (𝓝 1) := by
  have ht : Tendsto (fun N : ℕ => 1+(u : ℂ)/(Real.log N : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [add_zero] using tendsto_const_nhds.add (moving_drift_zero u)
    · filter_upwards [eventually_ge_atTop 2] with N hN
      exact moving_point_ne_one u hN
  have h := riemannZeta_residue_one.comp ht
  simpa only [Function.comp_def,add_sub_cancel_left] using h

private theorem near_zeta_scaled_limit (u : ℂˣ) :
    Tendsto (fun N : ℕ => riemannZeta (1+(u : ℂ)/(Real.log N : ℂ))/(Real.log N : ℂ))
      atTop (𝓝 (u : ℂ)⁻¹) := by
  have h := (positive_moving_residue u).div_const (u : ℂ)
  simp only [one_div] at h
  apply h.congr
  intro N
  field_simp

private theorem offpole_point_ne_one (tau : ℝˣ) : 1+(tau : ℂ)*Complex.I ≠ 1 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im,Complex.one_im,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hi
  exact tau.ne_zero hi

private theorem offpole_point_limit (v : ℂ) (tau : ℝ) :
    Tendsto (fun N : ℕ => 1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)) atTop
      (𝓝 (1+(tau : ℂ)*Complex.I)) := by
  simpa only [zero_add] using
    tendsto_const_nhds.add ((moving_drift_zero v).add_const ((tau : ℂ)*Complex.I))

private theorem offpole_zeta_limit (v : ℂ) (tau : ℝˣ) :
    Tendsto (fun N : ℕ => riemannZeta (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)))
      atTop (𝓝 (riemannZeta (1+(tau : ℂ)*Complex.I))) :=
  (differentiableAt_riemannZeta (offpole_point_ne_one tau)).continuousAt.tendsto.comp
    (offpole_point_limit v tau)

/-- Every original local unlabelled mixed Euler factor is eventually nonzero
simultaneously over the full growing prime cutoff. -/
theorem criticalMixedLocalEuler_eventually_ne_zero (u v : ℂ) (tau : ℝˣ) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Sieve.primeSubtypeLE N,
      weightedEuler (cubicPrimeBase p 1) (cubicPrimeBase p (1+u/(Real.log N : ℂ)))
        (cubicPrimeBase p (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I))) ≠ 0 := by
  have hv : criticalEulerCarrier u/
      ((Real.exp (-Real.eulerMascheroniConstant) : ℂ)*riemannZeta (1+(tau : ℂ)*Complex.I)) ≠ 0 :=
    div_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero normalization_ne (boundary_zeta_ne tau))
  have h := (criticalMixedBaseProduct_tendsto u v tau).eventually_ne hv
  filter_upwards [h] with N hN p
  have hn : criticalMixedBaseProduct u v tau N ≠ 0 := by
    intro he
    exact hN (by rw [he,zero_div])
  have hp := (Finset.prod_ne_zero_iff.mp hn) p.val p.property
  exact (mul_ne_zero_iff.mp hp).2

private theorem mixed_trace_eq (u v : ℂ) (tau : ℝ) (N : ℕ)
    (hs : 1+u/(Real.log N : ℂ) ≠ 1)
    (ht : 1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I) ≠ 1)
    (hu : 0 < (1+u/(Real.log N : ℂ)).re)
    (hv : 0 < (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)).re) :
    criticalCofactor (Sieve.primeSubtypeLE N) (1+u/(Real.log N : ℂ))*
    criticalCofactor (Sieve.primeSubtypeLE N) (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I))*
      weightedTrace 1 (u/(Real.log N : ℂ)) (v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)
        (Sieve.primeSubtypeLE N) =
      riemannZeta (1+u/(Real.log N : ℂ))*
      riemannZeta (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I))*criticalMixedBaseProduct u v tau N := by
  rw [criticalCofactor_eq _ hs,criticalCofactor_eq _ ht,weightedTrace_eq hu hv]
  have hprod (s : ℂ) : (∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p s)) =
      ∏ p ∈ Sieve.primeSubtypeLE N,(1-cubicPrimeBase p s) :=
    Finset.prod_coe_sort (Sieve.primeSubtypeLE N) (fun p : Nat.Primes => 1-cubicPrimeBase p s)
  rw [hprod,hprod]
  simp only [criticalMixedBaseProduct,Finset.prod_mul_distrib]
  ring

/-- The complete unlabelled mixed trace retains both original growing coprime
cofactors. Their zeta factor cancels the actual off-pole Euler limit. -/
theorem criticalMixedCompletedTrace_tendsto (u : ℂˣ) (v : ℂ) (tau : ℝˣ) :
    Tendsto (fun N : ℕ =>
      (criticalCofactor (Sieve.primeSubtypeLE N) (1+(u : ℂ)/(Real.log N : ℂ))*
       criticalCofactor (Sieve.primeSubtypeLE N) (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I))*
       weightedTrace 1 ((u : ℂ)/(Real.log N : ℂ)) (v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)
         (Sieve.primeSubtypeLE N))/(Real.log N : ℂ)^2) atTop
      (𝓝 (criticalEulerCarrier u/((Real.exp (-Real.eulerMascheroniConstant) : ℂ)*(u : ℂ)))) := by
  have h := ((near_zeta_scaled_limit u).mul (offpole_zeta_limit v tau)).mul
    (criticalMixedBaseProduct_tendsto u v tau)
  have he : (u : ℂ)⁻¹*riemannZeta (1+(tau : ℂ)*Complex.I)*
      (criticalEulerCarrier u/
        ((Real.exp (-Real.eulerMascheroniConstant) : ℂ)*riemannZeta (1+(tau : ℂ)*Complex.I))) =
      criticalEulerCarrier u/((Real.exp (-Real.eulerMascheroniConstant) : ℂ)*(u : ℂ)) := by
    field_simp [u.ne_zero,normalization_ne,boundary_zeta_ne tau]
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2,moving_re_positive u,moving_re_positive v,
    (offpole_point_limit v tau).eventually_ne (offpole_point_ne_one tau)] with N hN hu hv ht
  have hv' : 0 < (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)).re := by simpa using hv
  rw [mixed_trace_eq u v tau N (moving_point_ne_one u hN) ht hu hv']
  simp only [div_eq_mul_inv,pow_two]
  ring

end RHTower.BAGTrace
