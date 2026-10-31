import GaloisForLFunctions.ArithmeticElectrostatics.SimpleHeatZeroBranches
import GaloisForLFunctions.RHTower.Heat.HeatExteriorForce
import GaloisForLFunctions.RHTower.Heat.HeatForwardSimpleZeros
import GaloisForLFunctions.RHTower.Heat.HeatZeroSumContinuity
import GaloisForLFunctions.RHTower.Heat.LocalizedHeatPairForce
import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference
import GaloisForLFunctions.HTGeometry.LogDerivZeroPole

/-!
# Derivatives of localized vertical heat-zero energy

The regular part of the logarithmic derivative gives each simple zero's
velocity. Isolating disks identify the actual weighted zero sum with finitely
many branches. Compact regions become simple on short forward intervals.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

private theorem second_div_first_eq_twice_regular_part
    {f R : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hz : f a = 0) (hd : deriv f a ≠ 0) (hR : ContinuousAt R a)
    (heq : ∀ᶠ z in 𝓝[≠] a, logDeriv f z = 1 / (z - a) + R z) :
    deriv (deriv f) a / deriv f a = 2 * R a := by
  obtain ⟨p, hp⟩ := hf
  have hg : AnalyticAt ℂ (dslope f a) a :=
    hp.has_fpower_series_dslope_fslope.analyticAt
  have hgn : dslope f a a ≠ 0 := by rwa [dslope_same]
  have hfac : ∀ᶠ z in 𝓝 a, f z = (z - a) ^ (0 + 1) * dslope f a z := by
    filter_upwards [] with z
    simpa only [Nat.zero_add, pow_one, smul_eq_mul, hz, sub_zero] using
      (sub_smul_dslope f a z).symm
  have hlog := logDeriv_eventuallyEq_of_factor hg hgn hfac
  have hregular : logDeriv (dslope f a) =ᶠ[𝓝[≠] a] R := by
    filter_upwards [hlog, heq] with z hz₁ hz₂
    simp only [Nat.cast_zero, zero_add] at hz₁
    exact add_left_cancel (hz₁.symm.trans hz₂)
  have hc : ContinuousAt (logDeriv (dslope f a)) a :=
    (hg.deriv.div hg hgn).continuousAt
  have hvalue : logDeriv (dslope f a) a = R a :=
    tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      ((hR.tendsto.mono_left nhdsWithin_le_nhds).congr' hregular.symm)
  have hjet := _root_.HTGeometry.iteratedDeriv_dslope_self_eq_iteratedDeriv_succ_div
    hp.analyticAt 1
  have htwo : iteratedDeriv 2 f a = deriv (deriv f) a := by
    calc
      iteratedDeriv 2 f a = deriv (iteratedDeriv 1 f) a :=
        congrFun (iteratedDeriv_succ (n := 1) (f := f)) a
      _ = deriv (deriv f) a := by rw [iteratedDeriv_one]
  have hdg : deriv (dslope f a) a = deriv (deriv f) a / 2 := by
    simpa only [iteratedDeriv_one, htwo, Nat.cast_one,
      one_add_one_eq_two] using hjet
  rw [logDeriv_apply, dslope_same, hdg] at hvalue
  calc
    deriv (deriv f) a / deriv f a = 2 * (deriv (deriv f) a / 2 / deriv f a) := by ring
    _ = 2 * R a := by rw [hvalue]

/-- A simple heat zero moves at twice the regular part of the logarithmic
derivative, expressed by the actual local packet and exterior field. -/
theorem simple_heat_zero_velocity_eq_exterior
    {t X : ℝ} (ht : 0 < t) {S : Finset ℂ} {Q : ℂ → ℂ}
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hQ : ∀ z, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
      AnalyticAt ℂ Q z ∧ (riemannHeat t z ≠ 0 →
        logDeriv (riemannHeat t) z =
          (∑ b ∈ S, (zeroMult (riemannHeat t) b : ℂ) / (z - b)) + Q z))
    {a : ℂ} (hz : riemannHeat t a = 0) (hd : deriv (riemannHeat t) a ≠ 0)
    (haX : |a.re - X| < 1) :
    deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a =
      2 * ((∑ b ∈ S.erase a, (zeroMult (riemannHeat t) b : ℂ) / (a - b)) + Q a) := by
  classical
  have haS : a ∈ S := (hpacket a).mpr ⟨hz, by linarith only [haX]⟩
  have ham := zeroMult_riemannHeat_eq_one ht.le hz hd
  have hsq := riemannHeat_zeros_im_sq_le ht hz
  have hmax : max (1 / 4 - 2 * t) 0 < (1 / 2 : ℝ) ^ 2 := by
    apply max_lt <;> linarith only [ht]
  have haim : |a.im| < 1 / 2 := by
    nlinarith only [hsq, hmax, sq_abs a.im, abs_nonneg a.im]
  have hrect : ∀ᶠ z : ℂ in 𝓝 a, |z.re - X| < 1 ∧ |z.im| < 1 / 2 := by
    have hr : Continuous (fun z : ℂ => |z.re - X|) := by fun_prop
    have hi : Continuous (fun z : ℂ => |z.im|) := by fun_prop
    exact ((isOpen_lt hr continuous_const).inter
      (isOpen_lt hi continuous_const)).mem_nhds ⟨haX, haim⟩
  have hf : AnalyticAt ℂ (riemannHeat t) a := (riemannHeat_analytic ht.le) a (mem_univ a)
  obtain ⟨p, hp⟩ := hf
  have hg : AnalyticAt ℂ (dslope (riemannHeat t) a) a :=
    hp.has_fpower_series_dslope_fslope.analyticAt
  have hgn : dslope (riemannHeat t) a a ≠ 0 := by rwa [dslope_same]
  have hzero : ∀ᶠ z in 𝓝[≠] a, riemannHeat t z ≠ 0 := by
    filter_upwards [(hg.continuousAt.eventually_ne hgn).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hgz hza
    have hfac := sub_smul_dslope (riemannHeat t) a z
    simp only [hz, sub_zero, smul_eq_mul] at hfac
    rw [← hfac]
    exact mul_ne_zero (sub_ne_zero.mpr hza) hgz
  have hR : AnalyticAt ℂ (fun z =>
      (∑ b ∈ S.erase a, (zeroMult (riemannHeat t) b : ℂ) / (z - b)) + Q z) a := by
    refine (Finset.analyticAt_fun_sum _ fun b hb => ?_).add (hQ a haX.le haim.le).1
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (Finset.mem_erase.mp hb).1.symm)
  apply second_div_first_eq_twice_regular_part hp.analyticAt hz hd hR.continuousAt
  filter_upwards [hrect.filter_mono nhdsWithin_le_nhds, hzero] with z hzr hzn
  rw [(hQ z hzr.1.le hzr.2.le).2 hzn,
    ← Finset.sum_erase_add S (fun b => (zeroMult (riemannHeat t) b : ℂ) / (z - b)) haS, ham]
  push_cast
  ring

/-- Every compact region has only simple heat zeros for a short interval
strictly after a positive time. The starting configuration may contain
collisions of arbitrary multiplicity. -/
theorem exists_compact_simple_riemannHeat_zeros_forward {t : ℝ} (ht : 0 < t)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ δ > 0, ∀ s, t < s → s < t + δ → ∀ z ∈ K,
      riemannHeat s z = 0 → deriv (riemannHeat s) z ≠ 0 ∧
        zeroMult (riemannHeat s) z = 1 := by
  classical
  choose r hr hlocal using exists_ball_simple_riemannHeat_zeros_forward ht
  choose δ hδ hsimple using fun a => hlocal a (r a) (hr a) le_rfl
  have hcover : K ⊆ ⋃ a : ℂ, ball a (r a) := by
    intro a _
    exact mem_iUnion.mpr ⟨a, mem_ball_self (hr a)⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun a => ball a (r a))
    (fun _ => isOpen_ball) hcover
  obtain ⟨η, hη, hηδ⟩ := exists_pos_le_finset_of_pos T (fun a _ => hδ a)
  refine ⟨η, hη, ?_⟩
  intro s hts hs z hz hzero
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp (hT hz)
  exact hsimple a s hts (by linarith only [hs, hηδ a ha]) z hza hzero

private theorem eventually_heat_nonzero_on_compact {t : ℝ} (ht : 0 ≤ t)
    {K : Set ℂ} (hK : IsCompact K)
    (hnz : ∀ z ∈ K, riemannHeat t z ≠ 0) :
    ∀ᶠ s in 𝓝 t, ∀ z ∈ K, riemannHeat (max s 0) z ≠ 0 := by
  have hc : ContinuousOn (fun z : ℂ => ‖riemannHeat t z‖) K :=
    (differentiable_riemannHeat ht).continuous.norm.continuousOn
  obtain ⟨δ, hδ, hmin⟩ := hK.exists_forall_le' hc
    (fun z hz => norm_pos_iff.mpr (hnz z hz))
  have hconv := tendstoLocallyUniformly_riemannHeat_clamped_nhds t
  rw [max_eq_left ht] at hconv
  have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) K hK
  rw [Metric.tendstoUniformlyOn_iff] at hu
  filter_upwards [hu δ hδ] with s hs z hz hzero
  have hlt : ‖riemannHeat t z‖ < δ := by
    simpa only [hzero, dist_zero_right] using hs z hz
  exact (not_lt_of_ge (hmin z hz)) hlt

/-- The actual localized energy is a finite sum of simple zero branches on a
short right interval. The complement of their isolating disks excludes new zeros. -/
theorem heatLocalizedVerticalEnergy_hasDerivWithinAt_of_simple
    {t X : ℝ} (ht : 0 < t) {w v : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (v x) x)
    (hsupp : ∀ x, 1 ≤ |x| → w x = 0)
    {S : Finset ℂ}
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0) :
    HasDerivWithinAt (fun h => heatLocalizedVerticalEnergy X w (t + h))
      (∑ a ∈ S, (v (a.re - X) * a.im^2 *
          (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).re +
        2 * w (a.re - X) * a.im *
          (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im))
      (Ici 0) 0 := by
  classical
  let V : ℂ → ℂ := fun a => deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a
  obtain ⟨d, hd, hsep⟩ := exists_pos_sep S
  choose r₀ hr₀ hbranch using fun a : S =>
    GaloisForLFunctions.ArithmeticElectrostatics.exists_simple_heat_zero_branch ht ((hpacket a).mp a.property).1 (hsimple a a.property)
  let r : S → ℝ := fun a => min (r₀ a) (d / 3)
  have hr (a : S) : 0 < r a := lt_min (hr₀ a) (by positivity)
  have hr₀le (a : S) : r a ≤ r₀ a := min_le_left _ _
  have hrd (a : S) : r a ≤ d / 3 := min_le_right _ _
  choose δ hδ ζ hζ0 hζd hζ using fun a : S => hbranch a (r a) (hr a) (hr₀le a)
  let K : Set ℂ := closedBall (X : ℂ) 2 \ ⋃ a : S, ball (a : ℂ) (r a)
  have hK : IsCompact K := (isCompact_closedBall (X : ℂ) 2).diff
    (isOpen_iUnion fun _ => isOpen_ball)
  have hKfree : ∀ z ∈ K, riemannHeat t z ≠ 0 := by
    intro z hz hzero
    have hnorm : ‖z - (X : ℂ)‖ ≤ 2 := by
      simpa only [mem_closedBall, dist_eq_norm] using hz.1
    have hre : |z.re - X| ≤ 2 := by
      have h := Complex.abs_re_le_norm (z - (X : ℂ))
      simp only [sub_re, ofReal_re] at h
      exact h.trans hnorm
    have hzS := (hpacket z).mpr ⟨hzero, hre⟩
    exact hz.2 (mem_iUnion.mpr ⟨⟨z, hzS⟩, mem_ball_self (hr ⟨z, hzS⟩)⟩)
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp
    (eventually_heat_nonzero_on_compact ht.le hK hKfree)
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_le_finset_of_pos S.attach (fun a _ => hδ a)
  let η := min δ₀ (ε / 2)
  have hη : 0 < η := lt_min hδ₀ (by positivity)
  have hstep (h : ℝ) (hh : h ∈ Icc (0 : ℝ) η) (a : S) :
      ζ a h ∈ ball (a : ℂ) (r a) ∧
        zeroMult (riemannHeat (t + h)) (ζ a h) = 1 ∧
        ∀ z ∈ ball (a : ℂ) (r a), riemannHeat (t + h) z = 0 ↔ z = ζ a h := by
    exact hζ a h ⟨hh.1, hh.2.trans ((min_le_left _ _).trans
      (hδ₀le a (Finset.mem_attach S a)))⟩
  have hfree (h : ℝ) (hh : h ∈ Icc (0 : ℝ) η) :
      ∀ z ∈ K, riemannHeat (t + h) z ≠ 0 := by
    have he : dist (t + h) t < ε := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hh.1]
      have hhε := hh.2.trans (min_le_right δ₀ (ε / 2))
      linarith only [hhε, hε]
    simpa only [max_eq_left (add_nonneg ht.le hh.1)] using hnear he
  have hinj (h : ℝ) (hh : h ∈ Icc (0 : ℝ) η) : Function.Injective (fun a : S => ζ a h) := by
    intro a b heq
    change ζ a h = ζ b h at heq
    by_contra hab
    have hab' : (a : ℂ) ≠ (b : ℂ) := fun he => hab (Subtype.ext he)
    have hgap := hsep a a.property b b.property hab'
    have ha := mem_ball.mp (hstep h hh a).1
    have hb := mem_ball.mp (hstep h hh b).1
    rw [← heq] at hb
    have htri := dist_triangle (a : ℂ) (ζ a h) (b : ℂ)
    rw [dist_comm (a : ℂ) (ζ a h)] at htri
    linarith only [hgap, ha, hb, htri, hrd a, hrd b, hd]
  have hrepr (h : ℝ) (hh : h ∈ Icc (0 : ℝ) η) :
      heatLocalizedVerticalEnergy X w (t + h) =
        ∑ a ∈ S.attach, w ((ζ a h).re - X) * (ζ a h).im^2 := by
    let Z := S.attach.image (fun a => ζ a h)
    have hsum : heatLocalizedVerticalEnergy X w (t + h) =
        ∑ z ∈ Z, (zeroMult (riemannHeat (t + h)) z : ℝ) *
          (w (z.re - X) * z.im^2) := by
      unfold heatLocalizedVerticalEnergy heatWeightedZeroSum
      apply tsum_eq_sum
      intro z hz
      change (zeroMult (riemannHeat (t + h)) z : ℝ) * (w (z.re - X) * z.im^2) = 0
      by_cases hzero : riemannHeat (t + h) z = 0
      · by_cases hweight : w (z.re - X) * z.im^2 = 0
        · rw [hweight, mul_zero]
        exfalso
        have hre : |z.re - X| < 1 := lt_of_not_ge fun hr =>
          hweight (by rw [hsupp _ hr, zero_mul])
        have him := abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg
          (add_nonneg ht.le hh.1) hzero
        have hzball : z ∈ closedBall (X : ℂ) 2 := by
          rw [mem_closedBall, dist_eq_norm]
          have hn := Complex.norm_le_abs_re_add_abs_im (z - (X : ℂ))
          simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at hn
          linarith only [hn, hre, him]
        have hu : z ∈ ⋃ a : S, ball (a : ℂ) (r a) := by
          by_contra hnot
          exact hfree h hh z ⟨hzball, hnot⟩ hzero
        obtain ⟨a, hza⟩ := mem_iUnion.mp hu
        have hza' := ((hstep h hh a).2.2 z hza).mp hzero
        exact hz (Finset.mem_image.mpr ⟨a, Finset.mem_attach S a, hza'.symm⟩)
      · rw [zeroMult_riemannHeat_eq_zero (add_nonneg ht.le hh.1) hzero,
          Nat.cast_zero, zero_mul]
    rw [hsum, Finset.sum_image
      (f := fun z : ℂ => (zeroMult (riemannHeat (t + h)) z : ℝ) *
        (w (z.re - X) * z.im^2)) (fun a _ b _ heq => hinj h hh heq)]
    exact Finset.sum_congr rfl fun a _ => by
      rw [(hstep h hh a).2.1, Nat.cast_one, one_mul]
  have hdbranch (a : S) :
      HasDerivWithinAt (fun h => w ((ζ a h).re - X) * (ζ a h).im^2)
        (v ((a : ℂ).re - X) * (a : ℂ).im^2 * (V a).re +
          2 * w ((a : ℂ).re - X) * (a : ℂ).im * (V a).im) (Ici 0) 0 := by
    have hre : HasDerivWithinAt (fun h => (ζ a h).re) (V a).re (Ici 0) 0 :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt 0 (hζd a)
    have him : HasDerivWithinAt (fun h => (ζ a h).im) (V a).im (Ici 0) 0 :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt 0 (hζd a)
    have hcomp := (hw ((ζ a 0).re - X)).comp_hasDerivWithinAt 0 (hre.sub_const X)
    convert hcomp.mul (him.pow 2) using 1 <;>
      first | rfl | (simp only [Pi.pow_apply, Function.comp_apply, hζ0]; ring)
  have hds := HasDerivWithinAt.sum (u := S.attach) (fun a _ => hdbranch a)
  have hsumfun : (∑ a ∈ S.attach, fun h : ℝ =>
      w ((ζ a h).re - X) * (ζ a h).im^2) =
      (fun h => ∑ a ∈ S.attach, w ((ζ a h).re - X) * (ζ a h).im^2) := by
    funext h
    rw [Finset.sum_apply]
  rw [hsumfun] at hds
  have heq : (fun h => heatLocalizedVerticalEnergy X w (t + h)) =ᶠ[𝓝[Ici 0] 0]
      (fun h => ∑ a ∈ S.attach, w ((ζ a h).re - X) * (ζ a h).im^2) := by
    have hsmall : ∀ᶠ h : ℝ in 𝓝 0, h < η := Iio_mem_nhds hη
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with h hh hh0
    change 0 ≤ h at hh0
    exact hrepr h ⟨hh0, hh.le⟩
  have hder := hds.congr_of_eventuallyEq heq (hrepr 0 ⟨le_rfl, hη.le⟩)
  rw [Finset.sum_attach S (fun a : ℂ =>
    v (a.re - X) * a.im^2 * (V a).re + 2 * w (a.re - X) * a.im * (V a).im)] at hder
  exact hder

#print axioms exists_compact_simple_riemannHeat_zeros_forward
#print axioms simple_heat_zero_velocity_eq_exterior
#print axioms heatLocalizedVerticalEnergy_hasDerivWithinAt_of_simple

end

end RHTower.DeBruijn
