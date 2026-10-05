import GaloisForLFunctions.RHTower.ChiRamanujanMovingCofactorLimit
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Growing joint unlabelled Mellin source

The original cofactor-completed local Euler product has a joint growing-cutoff
limit at logarithmic complex displacements. The regular cubic correction is
controlled by its corpus local uniform product theorem; the four remaining
Euler ratios retain both frequency differences. The final theorem attaches
both original coprime cofactors and the entire unlabelled valuation trace.

Convergence is pointwise in the fixed displacement pair. Distinguished-label
assembly, compact-uniform parameter convergence and physical axes cancellation
are separate open obligations.
-/

open scoped BigOperators Topology
open Filter MeasureTheory
noncomputable section
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

private theorem moving_regular_limit (u v : ℂ) :
    Tendsto (fun N : ℕ => ∏ p ∈ Sieve.primeSubtypeLE N,
      cubicPrimeFactor p 1 (u/(Real.log N : ℂ)) (v/(Real.log N : ℂ)))
      atTop (𝓝 1) := by
  have hc : TendstoLocallyUniformlyOn
      (fun N => fun w : ℂ × ℂ × ℂ => ∏ p ∈ Sieve.primeSubtypeLE N,
        cubicPrimeFactor p w.1 w.2.1 w.2.2)
      (fun w => cubicEulerCorrection w.1 w.2.1 w.2.2) atTop cubicTube := by
    intro w hw r hr
    obtain ⟨t,ht,htr⟩ := hasProdLocallyUniformlyOn_cubicPrimeFactor w hw r hr
    exact ⟨t,ht,cutoff_tendsto.eventually htr⟩
  have hx : (1,0,0) ∈ cubicTube := by norm_num [cubicTube]
  have hg : Tendsto (fun N : ℕ => (1,u/(Real.log N : ℂ),v/(Real.log N : ℂ)))
      atTop (𝓝[cubicTube] (1,0,0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    have ht := (tendsto_const_nhds (x := (1 : ℂ))).prodMk_nhds
      ((moving_drift_zero u).prodMk_nhds (moving_drift_zero v))
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

/-- The original full unlabelled local product, including its two cofactor Euler factors. -/
def criticalJointBaseProduct (u v : ℂ) (N : ℕ) : ℂ :=
  ∏ p ∈ Sieve.primeSubtypeLE N,
    (1-cubicPrimeBase p (1+u/(Real.log N : ℂ)))*
    (1-cubicPrimeBase p (1+v/(Real.log N : ℂ)))*
      weightedEuler (cubicPrimeBase p 1) (cubicPrimeBase p (1+u/(Real.log N : ℂ)))
        (cubicPrimeBase p (1+v/(Real.log N : ℂ)))

private theorem moving_ratio_prod (u : ℂ) (N : ℕ) :
    criticalMovingEulerRatio u N =
      ∏ p ∈ Sieve.primeSubtypeLE N,
        (1-cubicPrimeBase p (1-u/(Real.log N : ℂ)))/(1-cubicPrimeBase p 1) := by
  have h := Finset.prod_subtype_of_mem (s := Nat.primesLE N)
    (fun n : ℕ => (1-(n : ℂ)^(-(1-u/(Real.log N : ℂ))))/(1-(n : ℂ)⁻¹))
    (fun n hn => Nat.prime_of_mem_primesLE hn)
  simp only [cubicPrimeBase,Complex.cpow_neg_one,criticalMovingEulerRatio,Sieve.primeSubtypeLE]
  convert h.symm using 1
  apply Finset.prod_congr rfl
  intro p hp
  rfl

private theorem joint_base_factorization (u v : ℂ) (N : ℕ)
    (hu : |(u/(Real.log N : ℂ)).re| < 1/16)
    (hv : |(v/(Real.log N : ℂ)).re| < 1/16) :
    criticalJointBaseProduct u v N =
      (∏ p ∈ Sieve.primeSubtypeLE N,
        cubicPrimeFactor p 1 (u/(Real.log N : ℂ)) (v/(Real.log N : ℂ))) *
        (criticalMovingEulerRatio (u-v) N*criticalMovingEulerRatio (v-u) N)/
          (criticalMovingEulerRatio u N*criticalMovingEulerRatio v N) := by
  let r (w : ℂ) (p : Nat.Primes) :=
    (1-cubicPrimeBase p (1-w/(Real.log N : ℂ)))/(1-cubicPrimeBase p 1)
  have he (p : Nat.Primes) :
      (1-cubicPrimeBase p (1+u/(Real.log N : ℂ)))*
      (1-cubicPrimeBase p (1+v/(Real.log N : ℂ)))*
        weightedEuler (cubicPrimeBase p 1) (cubicPrimeBase p (1+u/(Real.log N : ℂ)))
          (cubicPrimeBase p (1+v/(Real.log N : ℂ))) =
      cubicPrimeFactor p 1 (u/(Real.log N : ℂ)) (v/(Real.log N : ℂ))*
        ((r (u-v) p*r (v-u) p)/(r u p*r v p)) := by
    rw [moving_local_factor p hu hv]
    have hz := base_complement_ne p (s := 1) (by norm_num)
    have ha := abs_lt.mp hu
    have hb := abs_lt.mp hv
    have hxi := base_complement_ne p (s := 1-u/(Real.log N : ℂ))
      (by simp only [Complex.sub_re,Complex.one_re]; linarith)
    have hyi := base_complement_ne p (s := 1-v/(Real.log N : ℂ))
      (by simp only [Complex.sub_re,Complex.one_re]; linarith)
    have h1 : 1+(v/(Real.log N : ℂ)-u/(Real.log N : ℂ)) =
        1-(u-v)/(Real.log N : ℂ) := by ring
    have h2 : 1+(u/(Real.log N : ℂ)-v/(Real.log N : ℂ)) =
        1-(v-u)/(Real.log N : ℂ) := by ring
    rw [h1,h2]
    dsimp [r]
    field_simp
  unfold criticalJointBaseProduct
  simp_rw [he]
  simp only [Finset.prod_mul_distrib,Finset.prod_div_distrib]
  simp only [r,← moving_ratio_prod]
  ring

/-- The complete unlabelled joint prime product has its growing near-pole limit. -/
theorem criticalJointBaseProduct_tendsto (u v : ℂ) :
    Tendsto (criticalJointBaseProduct u v) atTop
      (𝓝 (Complex.exp ((∫ t in (0 : ℝ)..1,criticalEulerProfile u t)+
        (∫ t in (0 : ℝ)..1,criticalEulerProfile v t)-
        (∫ t in (0 : ℝ)..1,criticalEulerProfile (u-v) t)-
        (∫ t in (0 : ℝ)..1,criticalEulerProfile (v-u) t)))) := by
  have h := ((moving_regular_limit u v).mul
    ((criticalMovingEulerRatio_tendsto (u-v)).mul (criticalMovingEulerRatio_tendsto (v-u)))).div
    ((criticalMovingEulerRatio_tendsto u).mul (criticalMovingEulerRatio_tendsto v))
    (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
  have he : (1 : ℂ)*(Complex.exp (-(∫ t in (0 : ℝ)..1,criticalEulerProfile (u-v) t))*
      Complex.exp (-(∫ t in (0 : ℝ)..1,criticalEulerProfile (v-u) t)))/
      (Complex.exp (-(∫ t in (0 : ℝ)..1,criticalEulerProfile u t))*
      Complex.exp (-(∫ t in (0 : ℝ)..1,criticalEulerProfile v t))) =
      Complex.exp ((∫ t in (0 : ℝ)..1,criticalEulerProfile u t)+
        (∫ t in (0 : ℝ)..1,criticalEulerProfile v t)-
        (∫ t in (0 : ℝ)..1,criticalEulerProfile (u-v) t)-
        (∫ t in (0 : ℝ)..1,criticalEulerProfile (v-u) t)) := by
    rw [one_mul,← Complex.exp_add,← Complex.exp_add,← Complex.exp_sub]
    congr 1
    ring
  rw [he] at h
  apply h.congr'
  have hsmall (w : ℂ) : ∀ᶠ N : ℕ in atTop, |(w/(Real.log N : ℂ)).re| < 1/16 := by
    have ht := (Complex.continuous_re.tendsto _).comp (moving_drift_zero w)
    have hn := ht.abs
    exact hn.eventually (gt_mem_nhds (by norm_num : |(0 : ℂ).re| < 1/16))
  filter_upwards [hsmall u,hsmall v] with N hu hv
  exact (joint_base_factorization u v N hu hv).symm

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

private theorem completed_trace_eq (u v : ℂˣ) {N : ℕ} (hN : 2 ≤ N)
    (hu : 0 < (1+(u : ℂ)/(Real.log N : ℂ)).re)
    (hv : 0 < (1+(v : ℂ)/(Real.log N : ℂ)).re) :
    criticalCofactor (Sieve.primeSubtypeLE N) (1+(u : ℂ)/(Real.log N : ℂ))*
    criticalCofactor (Sieve.primeSubtypeLE N) (1+(v : ℂ)/(Real.log N : ℂ))*
      weightedTrace 1 ((u : ℂ)/(Real.log N : ℂ)) ((v : ℂ)/(Real.log N : ℂ))
        (Sieve.primeSubtypeLE N) =
      riemannZeta (1+(u : ℂ)/(Real.log N : ℂ))*
      riemannZeta (1+(v : ℂ)/(Real.log N : ℂ))*criticalJointBaseProduct u v N := by
  rw [criticalCofactor_eq _ (moving_point_ne_one u hN),
    criticalCofactor_eq _ (moving_point_ne_one v hN),weightedTrace_eq hu hv]
  have hprod (s : ℂ) : (∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p s)) =
      ∏ p ∈ Sieve.primeSubtypeLE N,(1-cubicPrimeBase p s) :=
    Finset.prod_coe_sort (Sieve.primeSubtypeLE N) (fun p : Nat.Primes => 1-cubicPrimeBase p s)
  rw [hprod,hprod]
  simp only [criticalJointBaseProduct,Finset.prod_mul_distrib]
  ring

/-- The actual unlabelled cone with both original growing coprime cofactors
has this joint moving double-pole residue, for every nonzero pair of displacements. -/
theorem criticalMovingCompletedTrace_tendsto (u v : ℂˣ) :
    Tendsto (fun N : ℕ => ((u : ℂ)/(Real.log N : ℂ))*((v : ℂ)/(Real.log N : ℂ))*
      criticalCofactor (Sieve.primeSubtypeLE N) (1+(u : ℂ)/(Real.log N : ℂ))*
      criticalCofactor (Sieve.primeSubtypeLE N) (1+(v : ℂ)/(Real.log N : ℂ))*
        weightedTrace 1 ((u : ℂ)/(Real.log N : ℂ)) ((v : ℂ)/(Real.log N : ℂ))
          (Sieve.primeSubtypeLE N)) atTop
      (𝓝 (Complex.exp ((∫ t in (0 : ℝ)..1,criticalEulerProfile u t)+
        (∫ t in (0 : ℝ)..1,criticalEulerProfile v t)-
        (∫ t in (0 : ℝ)..1,criticalEulerProfile ((u : ℂ)-(v : ℂ)) t)-
        (∫ t in (0 : ℝ)..1,criticalEulerProfile ((v : ℂ)-(u : ℂ)) t)))) := by
  have h := ((positive_moving_residue u).mul (positive_moving_residue v)).mul
    (criticalJointBaseProduct_tendsto u v)
  simp only [one_mul] at h
  apply h.congr'
  have he (w : ℂ) : ∀ᶠ N : ℕ in atTop, 0 < (1+w/(Real.log N : ℂ)).re := by
    have ht := (Complex.continuous_re.tendsto _).comp
      ((tendsto_const_nhds (x := (1 : ℂ))).add (moving_drift_zero w))
    exact ht.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < (1+(0 : ℂ)).re))
  filter_upwards [eventually_ge_atTop 2,he u,he v] with N hN hu hv
  calc _ = ((u : ℂ)/(Real.log N : ℂ))*((v : ℂ)/(Real.log N : ℂ))*
      (riemannZeta (1+(u : ℂ)/(Real.log N : ℂ))*
      riemannZeta (1+(v : ℂ)/(Real.log N : ℂ))*criticalJointBaseProduct u v N) := by ring
    _ = _ := by rw [← completed_trace_eq u v hN hu hv]; ring

end RHTower.BAGTrace
