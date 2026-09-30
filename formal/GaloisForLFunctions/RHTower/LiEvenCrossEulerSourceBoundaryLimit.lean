import GaloisForLFunctions.RHTower.LiEvenCrossEulerSourceBoundaryLayer

/-!
# The actual Euler jet's variable-coordinate source boundary limit

Fixed-coordinate Taylor limits and explicit-model orientation control every
convergent second-layer drift. The complete source error vanishes on that
scale, while actual Euler-jet orders remain natural numbers.
-/

namespace RHTower
noncomputable section

private theorem sourceBoundaryLimit_path_mem {α : Type*} {l : Filter α}
    (c lam : ℝ) (hc : 0 < c) (e d : α → ℝ)
    (he : Filter.Tendsto e l (nhdsWithin 0 (Set.Ioi 0)))
    (hd : Filter.Tendsto d l (nhds lam)) :
    ∀ᶠ z in l, c * e z + d z * (e z) ^ 2 ∈ Set.Icc 0 2 := by
  have he0 := he.mono_right nhdsWithin_le_nhds
  have hi : Filter.Tendsto (fun z => c + d z * e z) l (nhds c) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (hd.mul he0)
  have hp : Filter.Tendsto (fun z => c * e z + d z * (e z) ^ 2) l (nhds 0) := by
    simpa only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      (tendsto_const_nhds.mul he0).add (hd.mul (he0.pow 2))
  filter_upwards [he.eventually self_mem_nhdsWithin, hi.eventually (Ioi_mem_nhds hc),
    hp.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))] with z hz hi hp
  have hh := mul_pos hz hi
  exact ⟨by nlinarith, hp.le⟩

private theorem sourceBoundaryLimit_model_varying_tendsto {α : Type*} {l : Filter α}
    (m b L H lam : ℝ) (hm : 0 < m) (hb : 0 < b) (hL : 0 < L) (hH : 0 < H)
    (e d : α → ℝ) (he : Filter.Tendsto e l (nhdsWithin 0 (Set.Ioi 0)))
    (hd : Filter.Tendsto d l (nhds lam)) :
    Filter.Tendsto (fun z => liEvenCrossEulerBoundaryModel m b L H (e z)
      (liEvenCrossEulerBoundaryFirstCorrection m b L * e z + d z * (e z) ^ 2) /
        (e z) ^ 2) l
      (nhds (m * L * (liEvenCrossEulerBoundarySecondCorrection m b L H - lam))) := by
  let c : ℝ := liEvenCrossEulerBoundaryFirstCorrection m b L
  let C : ℝ := liEvenCrossEulerBoundarySecondCorrection m b L H
  let s : ℝ := m * L
  let t : ℝ := s * (C - lam)
  have hs : 0 < s := mul_pos hm hL
  have hc : 0 < c := div_pos hb hs
  have he0 := he.mono_right nhdsWithin_le_nhds
  have hS : 0 < m * L / (2 * b * H * Real.exp (2 * H)) := by positivity
  have hanti : ∀ᶠ z in l,
      StrictAntiOn (liEvenCrossEulerBoundaryModel m b L H (e z)) (Set.Icc 0 2) := by
    filter_upwards [he.eventually self_mem_nhdsWithin, he0.eventually (Iio_mem_nhds hS)]
      with z he heS
    exact liEvenCrossEulerBoundaryModel_strictAntiOn_Icc_zero_two
      m b L H (e z) hm hb hL hH he.le heS.le
  have hvarmem := sourceBoundaryLimit_path_mem c lam hc e d he hd
  apply tendsto_order.2
  constructor
  · intro r hr
    let δ : ℝ := (t - r) / (2 * s)
    have hδ : 0 < δ := div_pos (by change 0 < t - r; change r < t at hr; linarith)
      (by positivity)
    have hsδ : s * δ = (t - r) / 2 := by dsimp [δ]; field_simp
    have hboundlimit : r < m * L * (C - (lam + δ)) := by
      change r < s * (C - (lam + δ))
      rw [show s * (C - (lam + δ)) = t - s * δ by dsimp [t]; ring, hsδ]
      change r < t at hr
      linarith
    have hplus := (liEvenCrossEulerBoundaryModel_second_layer_tendsto
      m b L H (lam + δ) hm hL).comp he
    have hplusmem := sourceBoundaryLimit_path_mem c (lam + δ) hc e (fun _ => lam + δ) he tendsto_const_nhds
    filter_upwards [he.eventually self_mem_nhdsWithin, hanti, hvarmem, hplusmem,
      hd.eventually_lt_const (by linarith : lam < lam + δ),
      hplus.eventually_const_lt hboundlimit] with z he hanti hv hp hd hbound
    have hpath : c * e z + d z * (e z) ^ 2 ≤
        c * e z + (lam + δ) * (e z) ^ 2 := by
      linarith only [mul_le_mul_of_nonneg_right hd.le (sq_nonneg (e z))]
    have hmodel := hanti.antitoneOn hv hp hpath
    have hnormalized := div_le_div_of_nonneg_right hmodel (sq_nonneg (e z))
    exact hbound.trans_le hnormalized
  · intro r hr
    let δ : ℝ := (r - t) / (2 * s)
    have hδ : 0 < δ := div_pos (by change 0 < r - t; change t < r at hr; linarith)
      (by positivity)
    have hsδ : s * δ = (r - t) / 2 := by dsimp [δ]; field_simp
    have hboundlimit : m * L * (C - (lam - δ)) < r := by
      change s * (C - (lam - δ)) < r
      rw [show s * (C - (lam - δ)) = t + s * δ by dsimp [t]; ring, hsδ]
      change t < r at hr
      linarith
    have hminus := (liEvenCrossEulerBoundaryModel_second_layer_tendsto
      m b L H (lam - δ) hm hL).comp he
    have hminusmem := sourceBoundaryLimit_path_mem c (lam - δ) hc e (fun _ => lam - δ) he tendsto_const_nhds
    filter_upwards [he.eventually self_mem_nhdsWithin, hanti, hvarmem, hminusmem,
      hd.eventually_const_lt (by linarith : lam - δ < lam),
      hminus.eventually_lt_const hboundlimit] with z he hanti hv hm hd hbound
    have hpath : c * e z + (lam - δ) * (e z) ^ 2 ≤
        c * e z + d z * (e z) ^ 2 := by
      linarith only [mul_le_mul_of_nonneg_right hd.le (sq_nonneg (e z))]
    have hmodel := hanti.antitoneOn hm hv hpath
    have hnormalized := div_le_div_of_nonneg_right hmodel (sq_nonneg (e z))
    exact hnormalized.trans_lt hbound

private theorem sourceBoundaryLimit_rpow_tendsto {p : ℝ} (hp : 0 < p) :
    Filter.Tendsto (fun v : ℝ => v ^ p)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa only [Real.zero_rpow hp.ne'] using
    (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.mono_left
      nhdsWithin_le_nhds

private theorem sourceBoundaryLimit_mass_tendstoWithin :
    Filter.Tendsto (fun v : ℝ => v ^ liEvenCrossEulerCrossoverExponent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (sourceBoundaryLimit_rpow_tendsto liEvenCrossEulerCrossoverExponent_pos) ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact Real.rpow_pos_of_pos hv _

private theorem sourceBoundaryLimit_rpow_sq {v : ℝ} (hv : 0 < v) :
    v ^ (2 * liEvenCrossEulerCrossoverExponent) =
      (v ^ liEvenCrossEulerCrossoverExponent) ^ 2 := by
  rw [show 2 * liEvenCrossEulerCrossoverExponent =
    liEvenCrossEulerCrossoverExponent + liEvenCrossEulerCrossoverExponent by ring,
    Real.rpow_add hv, pow_two]

private theorem sourceBoundaryLimit_model_eq (v u : ℝ) :
    liEvenCrossEulerCrossoverTwoExponentialModel v u =
      liEvenCrossEulerBoundaryModel (normalizedPrimeArchMoment 0)
        liEvenCrossEulerCrossoverThirdAmplitude (Real.log 4) (Real.log 9)
          (v ^ liEvenCrossEulerCrossoverExponent) u := by
  unfold liEvenCrossEulerCrossoverTwoExponentialModel liEvenCrossEulerBoundaryModel
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 9)]
  ring

/-- The variable second-layer limit for literal natural-order actual LI Euler jets. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_source_boundary_layer_tendsto
    {α : Type*} {l : Filter α} (v : α → ℝ) (k : α → ℕ) {lam : ℝ}
    (hv : Filter.Tendsto v l (nhdsWithin 0 (Set.Ioi 0)))
    (hdrift : Filter.Tendsto (fun z =>
      ((k z : ℝ) - liEvenCrossEulerCrossoverCenter (v z) -
        liEvenCrossEulerSourceBoundaryFirstCorrection *
          (v z) ^ liEvenCrossEulerCrossoverExponent) /
        (v z) ^ (2 * liEvenCrossEulerCrossoverExponent)) l (nhds lam)) :
    Filter.Tendsto (fun z => (liEvenCrossFirstCurrentEvenEulerJet (v z) (k z) / (2 * v z)) /
        (v z) ^ (2 * liEvenCrossEulerCrossoverExponent)) l
      (nhds (normalizedPrimeArchMoment 0 * Real.log 4 *
        (liEvenCrossEulerSourceBoundarySecondCorrection - lam))) := by
  let e : α → ℝ := fun z => (v z) ^ liEvenCrossEulerCrossoverExponent
  let d : α → ℝ := fun z =>
    ((k z : ℝ) - liEvenCrossEulerCrossoverCenter (v z) -
      liEvenCrossEulerSourceBoundaryFirstCorrection * (v z) ^ liEvenCrossEulerCrossoverExponent) /
        (v z) ^ (2 * liEvenCrossEulerCrossoverExponent)
  let u : α → ℝ := fun z => (k z : ℝ) - liEvenCrossEulerCrossoverCenter (v z)
  have he : Filter.Tendsto e l (nhdsWithin 0 (Set.Ioi 0)) :=
    sourceBoundaryLimit_mass_tendstoWithin.comp hv
  have he0 := he.mono_right nhdsWithin_le_nhds
  have hd : Filter.Tendsto d l (nhds lam) := hdrift
  have hpositive : ∀ᶠ z in l, 0 < v z := hv.eventually self_mem_nhdsWithin
  have hpowers : ∀ᶠ z in l, (v z) ^ (2 * liEvenCrossEulerCrossoverExponent) = (e z) ^ 2 := by
    filter_upwards [hpositive] with z hz
    exact sourceBoundaryLimit_rpow_sq hz
  have hpath : ∀ᶠ z in l,
      u z = liEvenCrossEulerSourceBoundaryFirstCorrection * e z + d z * (e z) ^ 2 := by
    filter_upwards [hpositive, hpowers] with z hz hp
    have hepos : 0 < (e z) ^ 2 := sq_pos_of_pos (Real.rpow_pos_of_pos hz _)
    dsimp only [d]
    rw [hp, div_mul_cancel₀ _ hepos.ne']
    dsimp [u, e]
    ring
  have hupath : Filter.Tendsto (fun z =>
      liEvenCrossEulerSourceBoundaryFirstCorrection * e z + d z * (e z) ^ 2)
      l (nhds 0) := by
    simpa only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      (tendsto_const_nhds.mul he0).add (hd.mul (he0.pow 2))
  have hu : Filter.Tendsto u l (nhds 0) := by
    apply hupath.congr'
    filter_upwards [hpath] with z hz
    exact hz.symm
  have hm := normalizedPrimeArchMoment_pos_of_le_eleven 0 (by omega)
  have hL := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hH := Real.log_pos (by norm_num : (1 : ℝ) < 9)
  have hgeneric := sourceBoundaryLimit_model_varying_tendsto
    (normalizedPrimeArchMoment 0) liEvenCrossEulerCrossoverThirdAmplitude
      (Real.log 4) (Real.log 9) lam hm liEvenCrossEulerCrossoverThirdAmplitude_pos hL hH
        e d he hd
  have hmodel : Filter.Tendsto (fun z =>
      liEvenCrossEulerCrossoverTwoExponentialModel (v z) (u z) /
        (v z) ^ (2 * liEvenCrossEulerCrossoverExponent)) l
      (nhds (normalizedPrimeArchMoment 0 * Real.log 4 *
        (liEvenCrossEulerSourceBoundarySecondCorrection - lam))) := by
    apply hgeneric.congr'
    filter_upwards [hpowers, hpath] with z hp hu
    rw [hp, hu, sourceBoundaryLimit_model_eq]
    rfl
  obtain ⟨D, _, hremainder⟩ := liEvenCrossEulerCrossoverThreeTermProfile_uniform_remainder 2
  have hwindow : ∀ᶠ z in l, |u z| ≤ 2 := by
    filter_upwards [hu.eventually (Ioo_mem_nhds
      (by norm_num : (-2 : ℝ) < 0) (by norm_num : (0 : ℝ) < 2))] with z hz
    exact (abs_lt.2 hz).le
  let err : α → ℝ := fun z =>
    (liEvenCrossFirstCurrentEvenEulerJet (v z) (k z) / (2 * v z) -
      liEvenCrossEulerCrossoverTwoExponentialModel (v z) (u z)) /
        (v z) ^ (2 * liEvenCrossEulerCrossoverExponent)
  have hp : 0 < 1 - 2 * liEvenCrossEulerCrossoverExponent := by
    linarith [two_mul_liEvenCrossEulerCrossoverExponent_lt_one]
  have hmajor : Filter.Tendsto (fun z => D *
      (v z) ^ (1 - 2 * liEvenCrossEulerCrossoverExponent)) l (nhds 0) := by
    simpa only [mul_zero, Function.comp_def] using
      tendsto_const_nhds.mul ((sourceBoundaryLimit_rpow_tendsto hp).comp hv)
  have hbound : ∀ᶠ z in l,
      |err z| ≤ D * (v z) ^ (1 - 2 * liEvenCrossEulerCrossoverExponent) := by
    filter_upwards [hpositive, hwindow, hv.eventually hremainder] with z hz hw hrem
    have hden : 0 < (v z) ^ (2 * liEvenCrossEulerCrossoverExponent) :=
      Real.rpow_pos_of_pos hz _
    have hremk := hrem (k z) hw
    dsimp only [err]
    rw [abs_div, abs_of_pos hden]
    calc
      _ ≤ D * v z / (v z) ^ (2 * liEvenCrossEulerCrossoverExponent) :=
        div_le_div_of_nonneg_right hremk hden.le
      _ = D * (v z / (v z) ^ (2 * liEvenCrossEulerCrossoverExponent)) := by ring
      _ = D * (v z) ^ (1 - 2 * liEvenCrossEulerCrossoverExponent) := by
        rw [show v z / (v z) ^ (2 * liEvenCrossEulerCrossoverExponent) =
          (v z) ^ (1 - 2 * liEvenCrossEulerCrossoverExponent) by
          rw [Real.rpow_sub hz, Real.rpow_one]]
  have habs : Filter.Tendsto (fun z => |err z|) l (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun z => abs_nonneg (err z)) hbound hmajor
  have herror : Filter.Tendsto err l (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (by simpa only [Real.norm_eq_abs] using habs)
  have htotal : Filter.Tendsto (fun z =>
      liEvenCrossEulerCrossoverTwoExponentialModel (v z) (u z) /
        (v z) ^ (2 * liEvenCrossEulerCrossoverExponent) + err z) l
      (nhds (normalizedPrimeArchMoment 0 * Real.log 4 *
        (liEvenCrossEulerSourceBoundarySecondCorrection - lam))) := by
    simpa only [add_zero] using hmodel.add herror
  apply htotal.congr'
  exact Filter.Eventually.of_forall fun z => by dsimp only [err]; ring

/-- A drift below the second source boundary has eventually positive actual jets. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_eventually_pos_of_boundary_drift
    {α : Type*} {l : Filter α} (v : α → ℝ) (k : α → ℕ) {lam : ℝ}
    (hv : Filter.Tendsto v l (nhdsWithin 0 (Set.Ioi 0)))
    (hdrift : Filter.Tendsto (fun z =>
      ((k z : ℝ) - liEvenCrossEulerCrossoverCenter (v z) -
        liEvenCrossEulerSourceBoundaryFirstCorrection *
          (v z) ^ liEvenCrossEulerCrossoverExponent) /
        (v z) ^ (2 * liEvenCrossEulerCrossoverExponent)) l (nhds lam))
    (hlam : lam < liEvenCrossEulerSourceBoundarySecondCorrection) :
    ∀ᶠ z in l, 0 < liEvenCrossFirstCurrentEvenEulerJet (v z) (k z) := by
  have hm := normalizedPrimeArchMoment_pos_of_le_eleven 0 (by omega)
  have hL := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hμ : 0 < normalizedPrimeArchMoment 0 * Real.log 4 *
      (liEvenCrossEulerSourceBoundarySecondCorrection - lam) :=
    mul_pos (mul_pos hm hL) (by linarith)
  have hlimit := (liEvenCrossFirstCurrentEvenEulerJet_source_boundary_layer_tendsto
    v k hv hdrift).eventually_const_lt hμ
  filter_upwards [hv.eventually self_mem_nhdsWithin, hlimit] with z hz hjet
  have hp : 0 < (v z) ^ (2 * liEvenCrossEulerCrossoverExponent) :=
    Real.rpow_pos_of_pos hz _
  have hnormalized : 0 < liEvenCrossFirstCurrentEvenEulerJet (v z) (k z) / (2 * v z) := by
    simpa only [div_mul_cancel₀ _ hp.ne'] using mul_pos hjet hp
  have hden : 0 < 2 * v z := mul_pos (by norm_num) hz
  simpa only [div_mul_cancel₀ _ hden.ne'] using mul_pos hnormalized hden

/-- A drift above the second source boundary has eventually negative actual jets. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_eventually_neg_of_boundary_drift
    {α : Type*} {l : Filter α} (v : α → ℝ) (k : α → ℕ) {lam : ℝ}
    (hv : Filter.Tendsto v l (nhdsWithin 0 (Set.Ioi 0)))
    (hdrift : Filter.Tendsto (fun z =>
      ((k z : ℝ) - liEvenCrossEulerCrossoverCenter (v z) -
        liEvenCrossEulerSourceBoundaryFirstCorrection *
          (v z) ^ liEvenCrossEulerCrossoverExponent) /
        (v z) ^ (2 * liEvenCrossEulerCrossoverExponent)) l (nhds lam))
    (hlam : liEvenCrossEulerSourceBoundarySecondCorrection < lam) :
    ∀ᶠ z in l, liEvenCrossFirstCurrentEvenEulerJet (v z) (k z) < 0 := by
  have hm := normalizedPrimeArchMoment_pos_of_le_eleven 0 (by omega)
  have hL := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hμ : normalizedPrimeArchMoment 0 * Real.log 4 *
      (liEvenCrossEulerSourceBoundarySecondCorrection - lam) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hm hL) (by linarith)
  have hlimit := (liEvenCrossFirstCurrentEvenEulerJet_source_boundary_layer_tendsto
    v k hv hdrift).eventually_lt_const hμ
  filter_upwards [hv.eventually self_mem_nhdsWithin, hlimit] with z hz hjet
  have hp : 0 < (v z) ^ (2 * liEvenCrossEulerCrossoverExponent) :=
    Real.rpow_pos_of_pos hz _
  have hnormalized : liEvenCrossFirstCurrentEvenEulerJet (v z) (k z) / (2 * v z) < 0 := by
    simpa only [div_mul_cancel₀ _ hp.ne'] using mul_neg_of_neg_of_pos hjet hp
  have hden : 0 < 2 * v z := mul_pos (by norm_num) hz
  simpa only [div_mul_cancel₀ _ hden.ne'] using mul_neg_of_neg_of_pos hnormalized hden

end

end RHTower
