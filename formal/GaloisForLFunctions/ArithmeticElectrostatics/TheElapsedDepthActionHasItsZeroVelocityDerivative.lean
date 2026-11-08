import GaloisForLFunctions.ArithmeticElectrostatics.TheElapsedDepthActionIsContinuous
import GaloisForLFunctions.ArithmeticElectrostatics.TheSimpleHeatPacketPaysElapsedDepth
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The derivative of the corrected elapsed-depth action

An enclosing simple packet tracks every nonreal zero on a short forward
interval. Differentiating its finite sum gives the actual action derivative,
including the real-axis baseline. Conjugation pairs the two half-planes and
turns the upper-packet inequality into a bound by the full nonreal count.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry RHTower.DeBruijn

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- The corrected elapsed-depth rate at one heat zero. -/
def elapsedDepthActionRate (q t : ℝ) (a : ℂ) : ℝ :=
  2 * q * ((a.im ^ 2 + 2 * t) ^ (q - 1) - (2 * t) ^ (q - 1)) +
    elapsedDepthWeight q (2 * t) a.im *
      (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im

private theorem corrected_depth_hasDerivWithinAt {y : ℝ → ℝ} {v t q : ℝ}
    (ht : 0 < t) (hy : HasDerivWithinAt y v (Ici 0) 0) :
    HasDerivWithinAt (fun h => (y h ^ 2 + 2 * (t + h)) ^ q - (2 * (t + h)) ^ q)
      (2 * q * ((y 0 ^ 2 + 2 * t) ^ (q - 1) - (2 * t) ^ (q - 1)) +
        elapsedDepthWeight q (2 * t) (y 0) * v) (Ici 0) 0 := by
  have htime := (((hasDerivAt_id (0 : ℝ)).const_add t).const_mul 2).hasDerivWithinAt
    (s := Ici 0)
  have hb : y 0 ^ 2 + 2 * (t + 0) ≠ 0 := by positivity
  have hc : 2 * (t + 0) ≠ 0 := by positivity
  have hd := (((hy.pow 2).add htime).rpow_const (Or.inl hb) (p := q)).sub
    (htime.rpow_const (Or.inl hc) (p := q))
  simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, mul_one, add_zero] at hd
  convert hd using 1
  unfold elapsedDepthWeight
  ring

private theorem eventually_heat_nonzero_on_compact_for_action {t : ℝ} (ht : 0 ≤ t)
    {K : Set ℂ} (hK : IsCompact K) (hnz : ∀ z ∈ K, riemannHeat t z ≠ 0) :
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

/-- The corrected global action differentiates by the actual velocities of
an enclosing simple packet, including branches lying on the real axis. -/
theorem heatElapsedDepthAction_hasDerivWithinAt_of_simple (q : ℝ)
    {t R : ℝ} (ht : 0 < t)
    (hconf : ∀ s, t ≤ s → ∀ z, riemannHeat s z = 0 → z.im ≠ 0 → ‖z‖ ≤ R)
    {S : Finset ℂ} (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ ‖a‖ ≤ R)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0) :
    HasDerivWithinAt (fun h => heatElapsedDepthAction q (t + h))
      (∑ a ∈ S, elapsedDepthActionRate q t a) (Ici 0) 0 := by
  classical
  let V : ℂ → ℂ := fun a => deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a
  obtain ⟨d, hd, hsep⟩ := exists_pos_sep S
  choose r₀ hr₀ hbranch using fun a : S =>
    exists_simple_heat_zero_branch ht ((hpacket a).mp a.property).1 (hsimple a a.property)
  let r : S → ℝ := fun a => min (r₀ a) (d / 3)
  have hr (a : S) : 0 < r a := lt_min (hr₀ a) (by positivity)
  have hr₀le (a : S) : r a ≤ r₀ a := min_le_left _ _
  have hrd (a : S) : r a ≤ d / 3 := min_le_right _ _
  choose δ hδ ζ hζ0 hζd hζ using fun a : S => hbranch a (r a) (hr a) (hr₀le a)
  let K : Set ℂ := closedBall (0 : ℂ) R \ ⋃ a : S, ball (a : ℂ) (r a)
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).diff
    (isOpen_iUnion fun _ => isOpen_ball)
  have hKfree : ∀ z ∈ K, riemannHeat t z ≠ 0 := by
    intro z hz hzero
    have hnorm : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz.1
    have hzS := (hpacket z).mpr ⟨hzero, hnorm⟩
    exact hz.2 (mem_iUnion.mpr ⟨⟨z, hzS⟩, mem_ball_self (hr ⟨z, hzS⟩)⟩)
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp
    (eventually_heat_nonzero_on_compact_for_action ht.le hK hKfree)
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
      heatElapsedDepthAction q (t + h) =
        ∑ a ∈ S.attach, elapsedDepthActionWeight q (2 * (t + h)) (ζ a h) := by
    let Z := S.attach.image (fun a => ζ a h)
    have hsum : heatElapsedDepthAction q (t + h) =
        ∑ z ∈ Z, (zeroMult (riemannHeat (t + h)) z : ℝ) *
          elapsedDepthActionWeight q (2 * (t + h)) z := by
      rw [heatElapsedDepthAction, heatWeightedZeroSum]
      apply tsum_eq_sum
      intro z hz
      by_cases hzero : riemannHeat (t + h) z = 0
      · by_cases him : z.im = 0
        · simp only [elapsedDepthActionWeight, him, zero_pow two_ne_zero,
            zero_add, sub_self, mul_zero]
        exfalso
        have hzball : z ∈ closedBall (0 : ℂ) R := by
          simpa only [mem_closedBall, dist_zero_right] using
            hconf (t + h) (le_add_of_nonneg_right hh.1) z hzero him
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
        elapsedDepthActionWeight q (2 * (t + h)) z)
      (fun a _ b _ heq => hinj h hh heq)]
    exact Finset.sum_congr rfl fun a _ => by
      rw [(hstep h hh a).2.1, Nat.cast_one, one_mul]
  have hdbranch (a : S) : HasDerivWithinAt
      (fun h => elapsedDepthActionWeight q (2 * (t + h)) (ζ a h))
      (elapsedDepthActionRate q t a) (Ici 0) 0 := by
    have him : HasDerivWithinAt (fun h => (ζ a h).im) (V a).im (Ici 0) 0 :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt 0 (hζd a)
    simpa only [elapsedDepthActionWeight, elapsedDepthActionRate, hζ0, V] using
      corrected_depth_hasDerivWithinAt (q := q) ht him
  have hds := HasDerivWithinAt.sum (u := S.attach) (fun a _ => hdbranch a)
  have hsumfun : (∑ a ∈ S.attach,
      fun h : ℝ => elapsedDepthActionWeight q (2 * (t + h)) (ζ a h)) =
      (fun h => ∑ a ∈ S.attach, elapsedDepthActionWeight q (2 * (t + h)) (ζ a h)) := by
    funext h
    rw [Finset.sum_apply]
  rw [hsumfun] at hds
  have heq : (fun h => heatElapsedDepthAction q (t + h)) =ᶠ[𝓝[Ici 0] 0]
      (fun h => ∑ a ∈ S.attach, elapsedDepthActionWeight q (2 * (t + h)) (ζ a h)) := by
    have hsmall : ∀ᶠ h : ℝ in 𝓝 0, h < η := Iio_mem_nhds hη
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with h hh hh0
    exact hrepr h ⟨hh0, hh.le⟩
  have hder := hds.congr_of_eventuallyEq heq (hrepr 0 ⟨le_rfl, hη.le⟩)
  rw [Finset.sum_attach S (elapsedDepthActionRate q t)] at hder
  exact hder

#print axioms heatElapsedDepthAction_hasDerivWithinAt_of_simple

private theorem deriv_conjugation_eq {f : ℂ → ℂ}
    (hf : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) (z : ℂ) :
    deriv f (starRingEnd ℂ z) = starRingEnd ℂ (deriv f z) := by
  have heq : (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) = f := by
    funext w
    simp only [Function.comp_apply, hf, Complex.conj_conj]
  have h := congrArg (fun g : ℂ → ℂ => g (starRingEnd ℂ z)) (deriv_conj_conj (f := f))
  rw [heq] at h
  simpa only [Function.comp_apply, Complex.conj_conj] using h

private theorem elapsedDepthActionRate_conj {t : ℝ} (ht : 0 ≤ t) (q : ℝ) (a : ℂ) :
    elapsedDepthActionRate q t (starRingEnd ℂ a) = elapsedDepthActionRate q t a := by
  have hd (z : ℂ) := deriv_conjugation_eq (riemannHeat_conj ht) z
  have hdd := deriv_conjugation_eq hd a
  unfold elapsedDepthActionRate elapsedDepthWeight
  rw [Complex.conj_im, hdd, hd, ← map_div₀, Complex.conj_im]
  simp only [neg_sq]
  ring

private theorem elapsedDepthActionRate_real (q t : ℝ) {a : ℂ} (ha : a.im = 0) :
    elapsedDepthActionRate q t a = 0 := by
  simp only [elapsedDepthActionRate, elapsedDepthWeight, ha, zero_pow two_ne_zero,
    zero_add, sub_self, mul_zero, zero_mul, add_zero]

private theorem sum_even_packet_eq_twice_upper (S : Finset ℂ)
    (hconj : ∀ a ∈ S, starRingEnd ℂ a ∈ S) (f : ℂ → ℝ)
    (heven : ∀ a, f (starRingEnd ℂ a) = f a)
    (hreal : ∀ a, a.im = 0 → f a = 0) :
    (∑ a ∈ S, f a) = 2 * ∑ a ∈ S.filter (fun a => 0 < a.im), f a := by
  classical
  let N := S.filter (fun a => a.im ≠ 0)
  have hN (a : ℂ) (ha : a ∈ N) : a.im ≠ 0 := (Finset.mem_filter.mp ha).2
  have hNc (a : ℂ) (ha : a ∈ N) : starRingEnd ℂ a ∈ N := by
    refine Finset.mem_filter.mpr ⟨hconj a (Finset.mem_filter.mp ha).1, ?_⟩
    simpa only [Complex.conj_im, neg_ne_zero] using hN a ha
  have hU : N.filter (fun a => 0 < a.im) = S.filter (fun a => 0 < a.im) := by
    ext a
    simp only [N, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.ne'⟩, h.2⟩⟩
  have hdrop : (∑ a ∈ S, f a) = ∑ a ∈ N, f a := by
    simp only [N, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hi : a.im = 0 <;> simp only [hi, hreal a hi, ne_eq,
      not_true_eq_false, not_false_eq_true, if_true, if_false]
  have hp := congrArg Complex.re (sum_conjugate_packet N hN hNc (fun a => (f a : ℂ)))
  simp only [Complex.re_sum, Complex.add_re, Complex.ofReal_re, heven, hU] at hp
  rw [hdrop, hp, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The corrected packet rate pays the baseline derivative once for every
nonreal zero, including both halves and their analytic multiplicities. -/
theorem heatGlobalPacket_elapsedDepthActionRate_le {t : ℝ} (ht : 0 < t) {S : Finset ℂ}
    (hzero : ∀ a ∈ S, riemannHeat t a = 0)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0)
    (hcover : ∀ a, riemannHeat t a = 0 → a.im ≠ 0 → a ∈ S)
    (hconj : ∀ a ∈ S, starRingEnd ℂ a ∈ S)
    {q : ℝ} (hq : 0 ≤ q) :
    (∑ a ∈ S, elapsedDepthActionRate q t a) ≤
      -(2 * q * (2 * t) ^ (q - 1)) * (nonrealZeroCount t : ℝ) := by
  classical
  let U := S.filter (fun a => 0 < a.im)
  have hZ : S.filter (fun a => a.im ≠ 0) = (riemannHeat_nonreal_zeros_finite ht).toFinset := by
    ext a
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨hzero a h.1, h.2⟩, fun h => ⟨hcover a h.1 h.2, h.2⟩⟩
  have hN : (nonrealZeroCount t : ℝ) = ∑ a ∈ S, if a.im = 0 then (0 : ℝ) else 1 := by
    rw [nonrealZeroCount_eq ht, ← hZ, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    rw [zeroMult_riemannHeat_eq_one ht.le (hzero a ha) (hsimple a ha), Nat.cast_one]
    by_cases hi : a.im = 0 <;> simp only [hi, ne_eq, not_true_eq_false,
      not_false_eq_true, if_true, if_false]
  have hcount : (nonrealZeroCount t : ℝ) = 2 * (U.card : ℝ) := by
    rw [hN, sum_even_packet_eq_twice_upper S hconj
      (fun a => if a.im = 0 then (0 : ℝ) else 1)
      (fun a => by simp only [Complex.conj_im, neg_eq_zero])
      (fun a ha => by simp only [ha, if_true])]
    congr 1
    change (∑ a ∈ U, if a.im = 0 then (0 : ℝ) else 1) = _
    have heq : (∑ a ∈ U, if a.im = 0 then (0 : ℝ) else 1) = ∑ _a ∈ U, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [if_neg (Finset.mem_filter.mp ha).2.ne']
    rw [heq, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hraw := heatGlobalPacket_elapsedDepth_drift_nonpos ht hzero hsimple hcover hconj
    hq (show 0 ≤ 2 * t by positivity)
  have hupper : (∑ a ∈ U, elapsedDepthActionRate q t a) =
      (∑ a ∈ U, (2 * q * (a.im ^ 2 + 2 * t) ^ (q - 1) +
        elapsedDepthWeight q (2 * t) a.im *
          (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im)) -
        (U.card : ℝ) * (2 * q * (2 * t) ^ (q - 1)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    unfold elapsedDepthActionRate
    ring
  rw [sum_even_packet_eq_twice_upper S hconj (elapsedDepthActionRate q t)
    (elapsedDepthActionRate_conj ht.le q) (fun a ha => elapsedDepthActionRate_real q t ha),
    hcount]
  change 2 * (∑ a ∈ U, elapsedDepthActionRate q t a) ≤ _
  rw [hupper]
  change (∑ a ∈ U, _) ≤ 0 at hraw
  nlinarith only [hraw]

#print axioms heatGlobalPacket_elapsedDepthActionRate_le

end

end GaloisForLFunctions.ArithmeticElectrostatics
