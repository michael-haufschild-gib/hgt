import GaloisForLFunctions.ArithmeticElectrostatics.ConfinedZeroPacketsDissipateFaster
import GaloisForLFunctions.ArithmeticElectrostatics.TheGlobalHeatDepthDissipates

/-!
# Crowding dissipation for the actual heat divisor

At every positive initial time, the nonreal divisor stays in one bounded
region. The reciprocal field of the enclosing simple packet therefore pays
an additional energy cost proportional to its population. Continuity and
forward regular intervals retain this cost through collisions.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.EntireZeroDivisor GaloisForLFunctions.HTGeometry
open RHTower.DeBruijn

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

private theorem simple_copy_unique {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (q r : ZeroCopy f) (heq : zeroCopyPoint f q = zeroCopyPoint f r)
    (hd : deriv f (zeroCopyPoint f r) ≠ 0) : q = r := by
  apply Sigma.eq (Subtype.ext heq)
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

private theorem actual_packet_work_le {t : ℝ} (ht : 0 < t) {S : Finset ℂ}
    (hz : ∀ a ∈ S, riemannHeat t a = 0)
    (hd : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0)
    (hcover : ∀ a, riemannHeat t a = 0 → a.im ≠ 0 → a ∈ S) :
    (∑ a ∈ S, 2 * a.im *
      (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im) ≤
      heatPacketPairDrift S (fun _ => 1) (fun _ => 0) := by
  classical
  have hf := riemannHeat_analytic ht.le
  have hf0 := RHTower.riemannHeat_zero_ne ht.le
  choose q hq using fun a : S => exists_zeroCopy_of_eq_zero hf hf0 (hz a a.property)
  have hqi : Function.Injective q := by
    intro a b he
    apply Subtype.ext
    rw [← hq a, ← hq b, he]
  let N := S.attach.image q
  have hreal : ∀ r, r ∉ N → (zeroCopyPoint (riemannHeat t) r).im = 0 := by
    intro r hr
    by_contra hi
    have ha := hcover _ (apply_zeroCopyPoint hf r) hi
    let a : S := ⟨zeroCopyPoint (riemannHeat t) r, ha⟩
    have he : q a = r := simple_copy_unique hf (q a) r (hq a) (hd _ ha)
    exact hr (Finset.mem_image.mpr ⟨a, Finset.mem_attach S a, he⟩)
  have hsum (a : ℂ) : (∑ r ∈ N, (a - zeroCopyPoint (riemannHeat t) r)⁻¹) =
      ∑ b ∈ S, (a - b)⁻¹ := by
    rw [Finset.sum_image (fun r _ s _ he => hqi he)]
    simp only [hq]
    exact Finset.sum_attach S (fun b : ℂ => (a - b)⁻¹)
  obtain ⟨C, hC, hbound⟩ := (riemannKernel_superExp.mul_exp_sq ht.le).exists_envelope
  rw [heatPacketPairDrift_eq_field]
  apply Finset.sum_le_sum
  intro a ha
  let aS : S := ⟨a, ha⟩
  have hqa : q aS ∈ N := Finset.mem_image.mpr ⟨aS, Finset.mem_attach S aS, rfl⟩
  have h := im_mul_simple_regular_exterior_nonpos hC hf hf0 (riemannHeat_neg ht.le)
    hbound N hreal (q aS) hqa (by rw [hq aS]; exact hd a ha)
  have he : (∑ r ∈ N.erase (q aS), (a - zeroCopyPoint (riemannHeat t) r)⁻¹) =
      ∑ b ∈ S, (a - b)⁻¹ := by
    rw [← hsum]
    simpa only [hq aS, aS, sub_self, inv_zero, add_zero] using
      Finset.sum_erase_add N (fun r => (a - zeroCopyPoint (riemannHeat t) r)⁻¹) hqa
  rw [hq aS, he] at h
  simp only [aS, Complex.sub_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, add_zero] at h
  simp only [zero_mul, zero_add, mul_one]
  nlinarith only [h]

/-- A simple enclosing packet dissipates at a rate determined by the actual
nonreal count and a containing radius; real exterior work only improves it. -/
theorem heatGlobalPacket_crowding_drift_le {t R : ℝ} (ht : 0 < t) (hR : 0 < R)
    {S : Finset ℂ} (hz : ∀ a ∈ S, riemannHeat t a = 0)
    (hd : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0)
    (hcover : ∀ a, riemannHeat t a = 0 → a.im ≠ 0 → a ∈ S)
    (hc : ∀ a ∈ S, starRingEnd ℂ a ∈ S) (hn : ∀ a ∈ S, ‖a‖ ≤ R) :
    (∑ a ∈ S, 2 * a.im *
      (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im) ≤
      -2 * (nonrealZeroCount t : ℝ) -
        ((nonrealZeroCount t : ℝ) - 2) / R^2 * heatGlobalVerticalEnergy t := by
  classical
  have hcount : heatPacketNonrealWeight S (fun _ => 1) = (nonrealZeroCount t : ℝ) := by
    have hF : S.filter (fun a => a.im ≠ 0) = (riemannHeat_nonreal_zeros_finite ht).toFinset := by
      ext a
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨hz a h.1, h.2⟩, fun h => ⟨hcover a h.1 h.2, h.2⟩⟩
    rw [heatPacketNonrealWeight, nonrealZeroCount_eq ht, ← hF, Nat.cast_sum,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    rw [zeroMult_riemannHeat_eq_one ht.le (hz a ha) (hd a ha), Nat.cast_one]
    by_cases hi : a.im = 0 <;> simp only [hi, ne_eq, not_true_eq_false, not_false_eq_true,
      if_true, if_false]
  have hcard : (nonrealZeroCount t : ℝ) ≤ S.card := by
    rw [← hcount, heatPacketNonrealWeight]
    calc
      _ ≤ ∑ _a ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun a _ => by split_ifs <;> norm_num)
      _ = _ := by simp
  have hE : heatPacketVerticalEnergy S = heatGlobalVerticalEnergy t := by
    rw [heatGlobalVerticalEnergy_eq_weightedSum ht, heatWeightedZeroSum,
      tsum_eq_sum (s := S) (fun a ha => ?_)]
    · unfold heatPacketVerticalEnergy
      apply Finset.sum_congr rfl
      intro a ha
      rw [zeroMult_riemannHeat_eq_one ht.le (hz a ha) (hd a ha), Nat.cast_one, one_mul]
    · by_cases hzero : riemannHeat t a = 0
      · have hi : a.im = 0 := by
          by_contra hi
          exact ha (hcover a hzero hi)
        rw [hi, zero_pow two_ne_zero, mul_zero]
      · rw [zeroMult_riemannHeat_eq_zero ht.le hzero, Nat.cast_zero, zero_mul]
  have h := (actual_packet_work_le ht hz hd hcover).trans
    (heatPacketPairDrift_le_crowding hR hc hn)
  rw [hcount, hE] at h
  have hcoef := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (sub_le_sub_right hcard 2) (sq_nonneg R))
    (heatGlobalVerticalEnergy_nonneg t)
  linarith only [h, hcoef]

/-- Uniform confinement supplies one crowding rate on every future regular
interval. No simplicity assumption is imposed on the initial divisor. -/
theorem heatGlobalVerticalEnergy_crowding_forward {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hconf : ∀ t, a ≤ t → ∀ z, riemannHeat t z = 0 → z.im ≠ 0 → ‖z‖ ≤ R)
    {t : ℝ} (hat : a ≤ t) :
    ∃ δ > 0, ∀ s ∈ Ioo t (t + δ),
      ∃ D : ℝ, HasDerivWithinAt heatGlobalVerticalEnergy D (Ici s) s ∧
        D ≤ -2 * (nonrealZeroCount s : ℝ) -
          ((nonrealZeroCount s : ℝ) - 2) / R^2 * heatGlobalVerticalEnergy s := by
  classical
  have ht : 0 < t := ha.trans_le hat
  obtain ⟨δ, hδ, hreg⟩ := exists_compact_simple_riemannHeat_zeros_forward ht
    (isCompact_closedBall (0 : ℂ) R)
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hs0 : 0 < s := ht.trans hs.1
  have han : AnalyticOnNhd ℂ (riemannHeat s) (closedBall 0 R) :=
    fun z _ => (riemannHeat_analytic hs0.le) z (mem_univ z)
  have hfin := finite_zeros_closedBall han (fun z _ h =>
    analyticOrderAt_riemannHeat_ne_top hs0.le z (analyticOrderAt_eq_top.mpr h))
  let S := hfin.toFinset
  have hpacket (z : ℂ) : z ∈ S ↔ riemannHeat s z = 0 ∧ ‖z‖ ≤ R := by
    simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, mem_closedBall,
      dist_zero_right, and_comm]
  have hd (z : ℂ) (hz : z ∈ S) : deriv (riemannHeat s) z ≠ 0 := by
    obtain ⟨hz0, hzn⟩ := (hpacket z).mp hz
    exact (hreg s hs.1 hs.2 z
      (by simpa only [mem_closedBall, dist_zero_right] using hzn) hz0).1
  have hfuture : ∀ u, s ≤ u → ∀ z, riemannHeat u z = 0 → z.im ≠ 0 → ‖z‖ ≤ R :=
    fun u hu => hconf u (hat.trans (hs.1.le.trans hu))
  have hder := heatGlobalVerticalEnergy_hasDerivWithinAt_of_simple hs0 hfuture hpacket hd
  let D := ∑ z ∈ S, 2 * z.im *
    (deriv (deriv (riemannHeat s)) z / deriv (riemannHeat s) z).im
  have hder' : HasDerivWithinAt (fun h => heatGlobalVerticalEnergy (s + h))
      D (Ici 0) (s - s) := by simpa only [D, sub_self] using hder
  have hg : HasDerivWithinAt (fun r : ℝ => r - s) 1 (Ici s) s :=
    ((hasDerivAt_id s).sub_const s).hasDerivWithinAt
  have hcomp := hder'.comp (h := fun r : ℝ => r - s) s hg (by
    intro r hr
    change 0 ≤ r - s
    exact sub_nonneg.mpr hr)
  have heq : (fun r => heatGlobalVerticalEnergy (s + (r - s))) = heatGlobalVerticalEnergy := by
    funext r
    congr 1
    ring
  have hactual : HasDerivWithinAt heatGlobalVerticalEnergy D (Ici s) s := by
    change HasDerivWithinAt (fun r => heatGlobalVerticalEnergy (s + (r - s)))
      (D * 1) (Ici s) s at hcomp
    rwa [heq, mul_one] at hcomp
  refine ⟨D, hactual, heatGlobalPacket_crowding_drift_le hs0 hR
    (fun z hz => ((hpacket z).mp hz).1) hd
    (fun z hz hi => (hpacket z).mpr ⟨hz, hfuture s le_rfl z hz hi⟩)
    (fun z hz => ?_) (fun z hz => ((hpacket z).mp hz).2)⟩
  obtain ⟨hz0, hzn⟩ := (hpacket z).mp hz
  apply (hpacket (starRingEnd ℂ z)).mpr
  constructor
  · rw [riemannHeat_conj hs0.le, hz0, map_zero]
  · simpa only [Complex.norm_conj] using hzn

#print axioms heatGlobalPacket_crowding_drift_le
#print axioms heatGlobalVerticalEnergy_crowding_forward

/-- Crowding gives an exponential budget for the actual surviving divisor.
The containing radius is produced unconditionally at every positive time. -/
theorem exists_heat_crowding_exponential_budget {a : ℝ} (ha : 0 < a) :
    ∃ R : ℝ, 0 < R ∧ ∀ b : ℝ, a ≤ b →
      let n : ℝ := nonrealZeroCount b
      let k := max (n - 2) 0 / R^2
      Real.exp (k * (b - a)) * (k * heatGlobalVerticalEnergy b + 2 * n) ≤
        k * heatGlobalVerticalEnergy a + 2 * n := by
  obtain ⟨R₀, hR₀⟩ := exists_heat_nonreal_norm_bound ha
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hconf : ∀ t, a ≤ t → ∀ z, riemannHeat t z = 0 → z.im ≠ 0 → ‖z‖ ≤ R :=
    fun t ht z hz hi => (hR₀ t ht z hz hi).le.trans (le_max_left _ _)
  refine ⟨R, hR, fun b hab => ?_⟩
  dsimp only
  by_cases hn : (nonrealZeroCount b : ℝ) ≤ 2
  · rw [max_eq_right (sub_nonpos.mpr hn), zero_div]
    simp only [zero_mul, Real.exp_zero, zero_add, one_mul, le_refl]
  let n : ℝ := nonrealZeroCount b
  let k := (n - 2) / R^2
  have hn2 : 2 < n := lt_of_not_ge hn
  have hk : 0 < k := div_pos (sub_pos.mpr hn2) (sq_pos_of_pos hR)
  rw [max_eq_left (sub_nonneg.mpr hn2.le)]
  change Real.exp (k * (b - a)) * (k * heatGlobalVerticalEnergy b + 2 * n) ≤
    k * heatGlobalVerticalEnergy a + 2 * n
  have hc : ContinuousOn (fun s => Real.exp (k * (s - a)) *
      (k * heatGlobalVerticalEnergy s + 2 * n)) (Icc a b) := by
    apply ContinuousOn.mul (by fun_prop)
    exact (continuousOn_const.mul
      (continuousOn_heatGlobalVerticalEnergy.mono (fun s hs => ha.trans_le hs.1))).add
      continuousOn_const
  have h := le_initial_of_forward_intervals_interior hab hc (by
    intro t ht
    obtain ⟨δ, hδ, hreg⟩ := heatGlobalVerticalEnergy_crowding_forward ha hR hconf ht.1.le
    refine ⟨δ, hδ, fun s hs hsb => ?_⟩
    obtain ⟨D, hD, hDb⟩ := hreg s hs
    have hs0 : 0 < s := (ha.trans ht.1).trans hs.1
    have hcount : n ≤ (nonrealZeroCount s : ℝ) := by
      change (nonrealZeroCount b : ℝ) ≤ (nonrealZeroCount s : ℝ)
      exact_mod_cast nonrealZeroCount_antitoneOn hs0 (ha.trans_le hab) hsb.le
    have hcoef : k * heatGlobalVerticalEnergy s ≤
        ((nonrealZeroCount s : ℝ) - 2) / R^2 * heatGlobalVerticalEnergy s :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (sub_le_sub_right hcount 2) (sq_nonneg R))
        (heatGlobalVerticalEnergy_nonneg s)
    have hsign : D + k * heatGlobalVerticalEnergy s + 2 * n ≤ 0 := by
      linarith only [hDb, hcoef, hcount]
    have hfactor := (((hasDerivAt_id s).sub_const a).const_mul k).exp
    have hprod := hfactor.hasDerivWithinAt.mul ((hD.const_mul k).add_const (2 * n))
    simp only [id_eq, mul_one] at hprod
    refine ⟨_, hprod, ?_⟩
    have he : Real.exp (k * (s - a)) * k *
        (k * heatGlobalVerticalEnergy s + 2 * n) +
        Real.exp (k * (s - a)) * (k * D) =
        Real.exp (k * (s - a)) * k * (D + k * heatGlobalVerticalEnergy s + 2 * n) := by ring
    change Real.exp (k * (s - a)) * k *
        (k * heatGlobalVerticalEnergy s + 2 * n) +
        Real.exp (k * (s - a)) * (k * D) ≤ 0
    rw [he]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.exp_pos _).le hk.le) hsign)
  simpa only [sub_self, mul_zero, Real.exp_zero, one_mul] using h

/-- The surviving population consumes exponentially more than the linear
elapsed-time budget whenever more than one conjugate pair remains. -/
theorem exists_heat_crowding_survival_budget {a : ℝ} (ha : 0 < a) :
    ∃ R : ℝ, 0 < R ∧ ∀ b : ℝ, a ≤ b →
      let n : ℝ := nonrealZeroCount b
      let k := max (n - 2) 0 / R^2
      2 * n * (Real.exp (k * (b - a)) - 1) ≤ k * heatGlobalVerticalEnergy a := by
  obtain ⟨R, hR, hbudget⟩ := exists_heat_crowding_exponential_budget ha
  refine ⟨R, hR, fun b hab => ?_⟩
  have h := hbudget b hab
  dsimp only at h ⊢
  have hk : 0 ≤ max ((nonrealZeroCount b : ℝ) - 2) 0 / R^2 :=
    div_nonneg (le_max_right _ _) (sq_nonneg R)
  have hterm := mul_nonneg
    (Real.exp_pos (max ((nonrealZeroCount b : ℝ) - 2) 0 / R^2 * (b - a))).le
    (mul_nonneg hk (heatGlobalVerticalEnergy_nonneg b))
  nlinarith only [h, hterm]

#print axioms exists_heat_crowding_exponential_budget
#print axioms exists_heat_crowding_survival_budget

end

end GaloisForLFunctions.ArithmeticElectrostatics
