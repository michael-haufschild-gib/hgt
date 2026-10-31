import GaloisForLFunctions.ArithmeticElectrostatics.SimpleHeatZeroBranches
import GaloisForLFunctions.ArithmeticElectrostatics.TheGlobalHeatDepthIsContinuous
import GaloisForLFunctions.RHTower.Heat.HeatLocalizedEnergyEvolution

/-!
# The global heat-energy derivative

A ball containing every future nonreal zero reduces the global squared-depth
energy locally to finitely many simple branches. Uniform nonvanishing on the
complement of their isolating disks excludes untracked contributions.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.EntireZeroDivisor GaloisForLFunctions.HTGeometry
open RHTower.DeBruijn

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

private theorem eventually_heat_nonzero_on_compact {t : ℝ} (ht : 0 ≤ t)
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

/-- The global energy differentiates by the actual velocities of a simple enclosing packet. -/
theorem heatGlobalVerticalEnergy_hasDerivWithinAt_of_simple
    {t R : ℝ} (ht : 0 < t)
    (hconf : ∀ s, t ≤ s → ∀ z, riemannHeat s z = 0 → z.im ≠ 0 → ‖z‖ ≤ R)
    {S : Finset ℂ} (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ ‖a‖ ≤ R)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0) :
    HasDerivWithinAt (fun h => heatGlobalVerticalEnergy (t + h))
      (∑ a ∈ S, 2 * a.im *
        (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im) (Ici 0) 0 := by
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
  -- Every nonreal zero lies on a tracked branch; real zeros have zero weight.
  have hrepr (h : ℝ) (hh : h ∈ Icc (0 : ℝ) η) :
      heatGlobalVerticalEnergy (t + h) = ∑ a ∈ S.attach, (ζ a h).im^2 := by
    let Z := S.attach.image (fun a => ζ a h)
    have hsum : heatGlobalVerticalEnergy (t + h) =
        ∑ z ∈ Z, (zeroMult (riemannHeat (t + h)) z : ℝ) * z.im^2 := by
      rw [heatGlobalVerticalEnergy_eq_weightedSum (add_pos_of_pos_of_nonneg ht hh.1),
        heatWeightedZeroSum]
      apply tsum_eq_sum
      intro z hz
      by_cases hzero : riemannHeat (t + h) z = 0
      · by_cases him : z.im = 0
        · rw [him, zero_pow two_ne_zero, mul_zero]
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
      (f := fun z : ℂ => (zeroMult (riemannHeat (t + h)) z : ℝ) * z.im^2)
      (fun a _ b _ heq => hinj h hh heq)]
    exact Finset.sum_congr rfl fun a _ => by
      rw [(hstep h hh a).2.1, Nat.cast_one, one_mul]
  have hdbranch (a : S) : HasDerivWithinAt (fun h => (ζ a h).im^2)
      (2 * (a : ℂ).im * (V a).im) (Ici 0) 0 := by
    have him : HasDerivWithinAt (fun h => (ζ a h).im) (V a).im (Ici 0) 0 :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt 0 (hζd a)
    convert him.pow 2 using 1 <;>
      first | rfl | (simp only [hζ0, Nat.cast_ofNat]; ring)
  have hds := HasDerivWithinAt.sum (u := S.attach) (fun a _ => hdbranch a)
  have hsumfun : (∑ a ∈ S.attach, fun h : ℝ => (ζ a h).im^2) =
      (fun h => ∑ a ∈ S.attach, (ζ a h).im^2) := by
    funext h
    rw [Finset.sum_apply]
  rw [hsumfun] at hds
  have heq : (fun h => heatGlobalVerticalEnergy (t + h)) =ᶠ[𝓝[Ici 0] 0]
      (fun h => ∑ a ∈ S.attach, (ζ a h).im^2) := by
    have hsmall : ∀ᶠ h : ℝ in 𝓝 0, h < η := Iio_mem_nhds hη
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with h hh hh0
    exact hrepr h ⟨hh0, hh.le⟩
  have hder := hds.congr_of_eventuallyEq heq (hrepr 0 ⟨le_rfl, hη.le⟩)
  rw [Finset.sum_attach S (fun a : ℂ => 2 * a.im * (V a).im)] at hder
  exact hder

#print axioms heatGlobalVerticalEnergy_hasDerivWithinAt_of_simple

end

end GaloisForLFunctions.ArithmeticElectrostatics
