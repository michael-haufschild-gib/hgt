import GaloisForLFunctions.ArithmeticElectrostatics.TheRealExteriorDissipatesHeatDepth
import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference
import GaloisForLFunctions.HTGeometry.LogDerivZeroPole
import GaloisForLFunctions.RHTower.DeBruijnTopZeroVelocity
import GaloisForLFunctions.RHTower.DeBruijnCollisionJumpLaw
import GaloisForLFunctions.RHTower.Heat.LocalizedHeatPacketFlux

/-!
# Dissipation by a simple heat-zero packet

At a simple zero the removable logarithmic derivative equals half its heat
velocity. The real-exterior work inequality survives this limit. Summing over
a conjugation-closed packet containing every nonreal zero gives dissipation
at least twice the full nonreal count.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor GaloisForLFunctions.HTGeometry
open RHTower.DeBruijn

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- A simple zero has only one divisor copy. -/
private theorem zeroCopy_eq_of_point_eq_of_simple {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (q r : ZeroCopy f)
    (hqr : zeroCopyPoint f q = zeroCopyPoint f r)
    (hd : deriv f (zeroCopyPoint f r) ≠ 0) : q = r := by
  have hbase : q.1 = r.1 := Subtype.ext hqr
  apply Sigma.eq hbase
  have ho := (hf (zeroCopyPoint f r) (mem_univ _)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (apply_zeroCopyPoint hf r) hd
  change analyticOrderAt f (r.1 : ℂ) = 1 at ho
  have hm : ((MeromorphicOn.divisor f univ) (r.1 : ℂ)).toNat = 1 := by
    rw [divisor_univ_eq_analyticOrder hf, ho]
    rfl
  haveI : Subsingleton (Fin ((MeromorphicOn.divisor f univ) (r.1 : ℂ)).toNat) := by
    rw [hm]
    infer_instance
  exact Subsingleton.elim _ _

/-- The first jet of the divided difference carries the factor two. -/
private theorem two_mul_logDeriv_dslope_self {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) :
    2 * logDeriv (dslope f a) a = deriv (deriv f) a / deriv f a := by
  have hjet := _root_.HTGeometry.iteratedDeriv_dslope_self_eq_iteratedDeriv_succ_div hf 1
  have htwo : iteratedDeriv 2 f a = deriv (deriv f) a := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hdg : deriv (dslope f a) a = deriv (deriv f) a / 2 := by
    simpa only [iteratedDeriv_one, htwo, Nat.cast_one, one_add_one_eq_two] using hjet
  rw [logDeriv_apply, dslope_same, hdg]
  ring

/-- Removing a simple pole preserves the nonpositive real-exterior work. -/
theorem im_mul_simple_regular_exterior_nonpos {f : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0)
    (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (N : Finset (ZeroCopy f)) (hreal : ∀ q, q ∉ N → (zeroCopyPoint f q).im = 0)
    (q : ZeroCopy f) (hq : q ∈ N) (hd : deriv f (zeroCopyPoint f q) ≠ 0) :
    (zeroCopyPoint f q).im *
      (deriv (deriv f) (zeroCopyPoint f q) / deriv f (zeroCopyPoint f q) -
        2 * ∑ r ∈ N.erase q, (zeroCopyPoint f q - zeroCopyPoint f r)⁻¹).im ≤ 0 := by
  classical
  let a := zeroCopyPoint f q
  have ha : f a = 0 := apply_zeroCopyPoint hf q
  have hfa := hf a (mem_univ a)
  obtain ⟨p, hp⟩ := hfa
  have hg : AnalyticAt ℂ (dslope f a) a := hp.has_fpower_series_dslope_fslope.analyticAt
  have hgn : dslope f a a ≠ 0 := by rwa [dslope_same]
  have hfac : ∀ᶠ z in 𝓝 a, f z = (z - a) ^ (0 + 1) * dslope f a z := by
    filter_upwards [] with z
    simpa only [Nat.zero_add, pow_one, smul_eq_mul, ha, sub_zero] using
      (sub_smul_dslope f a z).symm
  have hlog := logDeriv_eventuallyEq_of_factor hg hgn hfac
  have hzero : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := by
    filter_upwards [(hg.continuousAt.eventually_ne hgn).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hgz hza
    have hfac' := sub_smul_dslope f a z
    simp only [ha, sub_zero, smul_eq_mul] at hfac'
    rw [← hfac']
    exact mul_ne_zero (sub_ne_zero.mpr hza) hgz
  let R : ℂ → ℂ := fun z => logDeriv (dslope f a) z -
    ∑ r ∈ N.erase q, (z - zeroCopyPoint f r)⁻¹
  have hR : ContinuousAt R a := by
    have hs : AnalyticAt ℂ (fun z => ∑ r ∈ N.erase q, (z - zeroCopyPoint f r)⁻¹) a := by
      refine Finset.analyticAt_fun_sum _ fun r hr => ?_
      have hn : a - zeroCopyPoint f r ≠ 0 := by
        apply sub_ne_zero.mpr
        intro heq
        exact (Finset.mem_erase.mp hr).1 (zeroCopy_eq_of_point_eq_of_simple hf r q heq.symm hd)
      have hA : AnalyticAt ℂ (fun z : ℂ => 1 / (z - zeroCopyPoint f r)) a :=
        analyticAt_const.div (analyticAt_id.sub analyticAt_const) hn
      have heq : (fun z : ℂ => 1 / (z - zeroCopyPoint f r)) =
          (fun z : ℂ => (z - zeroCopyPoint f r)⁻¹) := by
        funext z
        rw [one_div]
      rwa [heq] at hA
    exact (hg.deriv.div hg hgn).continuousAt.sub hs.continuousAt
  have hlim : Tendsto (fun z : ℂ => z.im * (R z).im) (𝓝[≠] a)
      (𝓝 (a.im * (R a).im)) :=
    (Complex.continuous_im.continuousAt.mul (Complex.continuous_im.continuousAt.comp hR)).tendsto.mono_left
      nhdsWithin_le_nhds
  have hwork : a.im * (R a).im ≤ 0 := by
    apply le_of_tendsto hlim
    filter_upwards [hzero, hlog] with z hzn hlogz
    have h := im_mul_exterior_logDeriv_nonpos hC hf hf0 heven hbound N hreal hzn
    have heq : logDeriv f z - ∑ r ∈ N, (z - zeroCopyPoint f r)⁻¹ = R z := by
      rw [hlogz, ← Finset.sum_erase_add N (fun r => (z - zeroCopyPoint f r)⁻¹) hq]
      simp only [Nat.cast_zero, zero_add, one_div, R, a]
      ring
    rwa [heq] at h
  have hder := two_mul_logDeriv_dslope_self hp.analyticAt
  change a.im * (deriv (deriv f) a / deriv f a -
    2 * ∑ r ∈ N.erase q, (a - zeroCopyPoint f r)⁻¹).im ≤ 0
  rw [← hder, ← mul_sub]
  change a.im * (2 * R a).im ≤ 0
  simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
  nlinarith only [hwork]

#print axioms im_mul_simple_regular_exterior_nonpos

/-- Conjugate pairs pay the entire nonreal count; real exterior zeros add no positive work. -/
theorem heatGlobalPacket_drift_le {t : ℝ} (ht : 0 < t) {S : Finset ℂ}
    (hzero : ∀ a ∈ S, riemannHeat t a = 0)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0)
    (hcover : ∀ a, riemannHeat t a = 0 → a.im ≠ 0 → a ∈ S)
    (hconj : ∀ a ∈ S, starRingEnd ℂ a ∈ S) :
    (∑ a ∈ S, 2 * a.im *
      (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im) ≤
        -2 * (nonrealZeroCount t : ℝ) := by
  classical
  have hf := riemannHeat_analytic ht.le
  have hf0 := RHTower.riemannHeat_zero_ne ht.le
  choose q hq using fun a : S => exists_zeroCopy_of_eq_zero hf hf0 (hzero a a.property)
  have hqi : Function.Injective q := by
    intro a b hab
    apply Subtype.ext
    rw [← hq a, ← hq b, hab]
  let N := S.attach.image q
  have hNreal : ∀ r, r ∉ N → (zeroCopyPoint (riemannHeat t) r).im = 0 := by
    intro r hr
    by_contra hi
    have ha := hcover _ (apply_zeroCopyPoint hf r) hi
    let a : S := ⟨zeroCopyPoint (riemannHeat t) r, ha⟩
    have heq : q a = r := zeroCopy_eq_of_point_eq_of_simple hf (q a) r (hq a)
      (hsimple _ ha)
    exact hr (Finset.mem_image.mpr ⟨a, Finset.mem_attach S a, heq⟩)
  have hNsum (a : ℂ) : (∑ r ∈ N, (a - zeroCopyPoint (riemannHeat t) r)⁻¹) =
      ∑ b ∈ S, (a - b)⁻¹ := by
    rw [Finset.sum_image (fun r _ s _ hrs => hqi hrs)]
    simp only [hq]
    exact Finset.sum_attach S (fun b : ℂ => (a - b)⁻¹)
  obtain ⟨C, hC, hbound⟩ := (riemannKernel_superExp.mul_exp_sq ht.le).exists_envelope
  have hwork (a : S) : 2 * (a : ℂ).im *
      (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im ≤
      4 * (a : ℂ).im * (∑ b ∈ S, ((a : ℂ) - b)⁻¹).im := by
    have hqa : q a ∈ N := Finset.mem_image.mpr ⟨a, Finset.mem_attach S a, rfl⟩
    have h := im_mul_simple_regular_exterior_nonpos hC hf hf0 (riemannHeat_neg ht.le)
      hbound N hNreal (q a) hqa (by rw [hq a]; exact hsimple a a.property)
    have hs : (∑ r ∈ N.erase (q a), ((a : ℂ) - zeroCopyPoint (riemannHeat t) r)⁻¹) =
        ∑ b ∈ S, ((a : ℂ) - b)⁻¹ := by
      rw [← hNsum]
      simpa only [hq a, sub_self, inv_zero, add_zero] using
        Finset.sum_erase_add N (fun r => ((a : ℂ) - zeroCopyPoint (riemannHeat t) r)⁻¹) hqa
    rw [hq a, hs] at h
    simp only [Complex.sub_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, add_zero] at h
    nlinarith only [h]
  have hsum : (∑ a ∈ S, 2 * a.im *
      (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im) ≤
      heatPacketPairDrift S (fun _ => 1) (fun _ => 0) := by
    rw [heatPacketPairDrift_eq_field]
    apply Finset.sum_le_sum
    intro a ha
    simp only [zero_mul, zero_add]
    nlinarith only [hwork ⟨a, ha⟩]
  have hflux := heatPacketPairDrift_le (M := 0) hconj le_rfl
    (fun x => hasDerivAt_const x (1 : ℝ))
    (fun _ _ => by simp only [sub_self, abs_zero, zero_mul, le_refl])
    (fun _ => zero_le_one)
  have hcount : heatPacketNonrealWeight S (fun _ => 1) = (nonrealZeroCount t : ℝ) := by
    have hF : S.filter (fun a => a.im ≠ 0) = (riemannHeat_nonreal_zeros_finite ht).toFinset := by
      ext a
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨hzero a h.1, h.2⟩, fun h => ⟨hcover a h.1 h.2, h.2⟩⟩
    rw [heatPacketNonrealWeight, nonrealZeroCount_eq ht, ← hF, Nat.cast_sum,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    rw [zeroMult_riemannHeat_eq_one ht.le (hzero a ha) (hsimple a ha), Nat.cast_one]
    by_cases hi : a.im = 0 <;> simp only [hi, ne_eq, not_true_eq_false, not_false_eq_true,
      if_true, if_false]
  rw [hcount] at hflux
  simpa only [mul_zero, zero_mul, add_zero] using hsum.trans hflux

#print axioms heatGlobalPacket_drift_le

end

end GaloisForLFunctions.ArithmeticElectrostatics

