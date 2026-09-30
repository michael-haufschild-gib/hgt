import GaloisForLFunctions.RHTower.LiEvenCrossEulerCrossoverThreeTermProfile
import GaloisForLFunctions.RHTower.LiEvenCrossEulerBoundaryLayerExpansion
import GaloisForLFunctions.RHTower.LiEvenCrossEulerThirdTermDominance

/-!
# The source-dependent second boundary layer of the first negative Euler jet

The explicit two-exponential model supplies strict quadratic endpoint margins.
The complete source error is smaller than those margins, and separate source
positivity covers every earlier natural order. Model orientation and exact
integer rounding then locate the least negative actual jet.
-/

namespace RHTower

noncomputable section

/-- First positive source displacement of the Euler-jet crossover. -/
def liEvenCrossEulerSourceBoundaryFirstCorrection : ℝ :=
  liEvenCrossEulerBoundaryFirstCorrection (normalizedPrimeArchMoment 0)
    liEvenCrossEulerCrossoverThirdAmplitude (Real.log 4)

/-- Second source displacement, including the interaction of both exponentials. -/
def liEvenCrossEulerSourceBoundarySecondCorrection : ℝ :=
  liEvenCrossEulerBoundarySecondCorrection (normalizedPrimeArchMoment 0)
    liEvenCrossEulerCrossoverThirdAmplitude (Real.log 4) (Real.log 9)

/-- A source boundary displacement at a fixed second-layer coordinate. -/
def liEvenCrossEulerSourceBoundaryOffset (v ell : ℝ) : ℝ :=
  liEvenCrossEulerSourceBoundaryFirstCorrection * v ^ liEvenCrossEulerCrossoverExponent +
    ell * v ^ (2 * liEvenCrossEulerCrossoverExponent)

theorem liEvenCrossEulerSourceBoundaryFirstCorrection_pos :
    0 < liEvenCrossEulerSourceBoundaryFirstCorrection := by
  exact div_pos liEvenCrossEulerCrossoverThirdAmplitude_pos
    (mul_pos (normalizedPrimeArchMoment_pos_of_le_eleven 0 (by omega))
      (Real.log_pos (by norm_num : (1 : ℝ) < 4)))

theorem liEvenCrossEulerSourceBoundarySecondCorrection_eq :
    liEvenCrossEulerSourceBoundarySecondCorrection =
      liEvenCrossEulerSourceBoundaryFirstCorrection ^ 2 * Real.log (9 / 2) := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, Nat.cast_ofNat] using
      Real.log_pow (2 : ℝ) 2
  have hlogdiv : Real.log (9 / 2 : ℝ) = Real.log 9 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  unfold liEvenCrossEulerSourceBoundarySecondCorrection
    liEvenCrossEulerBoundarySecondCorrection
  change liEvenCrossEulerSourceBoundaryFirstCorrection ^ 2 *
      (Real.log 9 - Real.log 4 / 2) = _
  rw [hlog4, hlogdiv]
  ring

theorem liEvenCrossEulerSourceBoundarySecondCorrection_pos :
    0 < liEvenCrossEulerSourceBoundarySecondCorrection := by
  rw [liEvenCrossEulerSourceBoundarySecondCorrection_eq]
  exact mul_pos (sq_pos_of_pos liEvenCrossEulerSourceBoundaryFirstCorrection_pos)
    (Real.log_pos (by norm_num : (1 : ℝ) < 9 / 2))

private theorem sourceBoundary_rpow_sq {v : ℝ} (hv : 0 < v) :
    v ^ (2 * liEvenCrossEulerCrossoverExponent) =
      (v ^ liEvenCrossEulerCrossoverExponent) ^ 2 := by
  rw [show 2 * liEvenCrossEulerCrossoverExponent =
    liEvenCrossEulerCrossoverExponent + liEvenCrossEulerCrossoverExponent by ring,
    Real.rpow_add hv, pow_two]

private theorem sourceBoundary_offset_eq_sq {v : ℝ} (hv : 0 < v) (ell : ℝ) :
    liEvenCrossEulerSourceBoundaryOffset v ell =
      liEvenCrossEulerSourceBoundaryFirstCorrection * v ^ liEvenCrossEulerCrossoverExponent +
        ell * (v ^ liEvenCrossEulerCrossoverExponent) ^ 2 := by
  rw [liEvenCrossEulerSourceBoundaryOffset, sourceBoundary_rpow_sq hv]

private theorem sourceBoundary_model_eq (v u : ℝ) :
    liEvenCrossEulerCrossoverTwoExponentialModel v u =
      liEvenCrossEulerBoundaryModel (normalizedPrimeArchMoment 0)
        liEvenCrossEulerCrossoverThirdAmplitude (Real.log 4) (Real.log 9)
          (v ^ liEvenCrossEulerCrossoverExponent) u := by
  unfold liEvenCrossEulerCrossoverTwoExponentialModel liEvenCrossEulerBoundaryModel
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 9)]
  ring

private theorem sourceBoundary_mass_tendsto :
    Filter.Tendsto (fun v : ℝ => v ^ liEvenCrossEulerCrossoverExponent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa only [Real.zero_rpow liEvenCrossEulerCrossoverExponent_pos.ne'] using
    (Real.continuousAt_rpow_const 0 liEvenCrossEulerCrossoverExponent
      (Or.inr liEvenCrossEulerCrossoverExponent_pos.le)).tendsto.mono_left
        nhdsWithin_le_nhds

private theorem sourceBoundary_mass_tendstoWithin :
    Filter.Tendsto (fun v : ℝ => v ^ liEvenCrossEulerCrossoverExponent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    sourceBoundary_mass_tendsto ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact Real.rpow_pos_of_pos hv _

private theorem sourceBoundary_offset_eventually_mem (ell : ℝ) :
    ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < liEvenCrossEulerSourceBoundaryOffset v ell ∧
        liEvenCrossEulerSourceBoundaryOffset v ell < 1 := by
  let c : ℝ := liEvenCrossEulerSourceBoundaryFirstCorrection
  have hc : 0 < c := liEvenCrossEulerSourceBoundaryFirstCorrection_pos
  have hinner : Filter.Tendsto (fun v : ℝ => c + ell * v ^ liEvenCrossEulerCrossoverExponent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul sourceBoundary_mass_tendsto)
  have ht : Filter.Tendsto (fun v : ℝ =>
      c * v ^ liEvenCrossEulerCrossoverExponent +
        ell * (v ^ liEvenCrossEulerCrossoverExponent) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      (tendsto_const_nhds.mul sourceBoundary_mass_tendsto).add
        (tendsto_const_nhds.mul (sourceBoundary_mass_tendsto.pow 2))
  filter_upwards [self_mem_nhdsWithin, hinner.eventually (Ioi_mem_nhds hc),
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with v hv hinner ht
  rw [sourceBoundary_offset_eq_sq hv]
  constructor
  · have hh := mul_pos (Real.rpow_pos_of_pos hv liEvenCrossEulerCrossoverExponent) hinner
    change 0 < liEvenCrossEulerSourceBoundaryFirstCorrection *
      v ^ liEvenCrossEulerCrossoverExponent +
        ell * (v ^ liEvenCrossEulerCrossoverExponent) ^ 2
    dsimp [c] at hh
    nlinarith
  · exact ht

private theorem sourceBoundary_error_eventually_lt (D c : ℝ) (hc : 0 < c) :
    ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0),
      D * v < c * (v ^ liEvenCrossEulerCrossoverExponent) ^ 2 := by
  have hp : 0 < 1 - 2 * liEvenCrossEulerCrossoverExponent := by
    linarith [two_mul_liEvenCrossEulerCrossoverExponent_lt_one]
  have ht : Filter.Tendsto (fun v : ℝ => v ^ (1 - 2 * liEvenCrossEulerCrossoverExponent))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Real.zero_rpow hp.ne'] using
      (Real.continuousAt_rpow_const 0 (1 - 2 * liEvenCrossEulerCrossoverExponent)
        (Or.inr hp.le)).tendsto.mono_left nhdsWithin_le_nhds
  have hD : Filter.Tendsto (fun v : ℝ => D * v ^ (1 - 2 * liEvenCrossEulerCrossoverExponent))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ht
  filter_upwards [self_mem_nhdsWithin, hD.eventually (Iio_mem_nhds hc)] with v hv hsmall
  change 0 < v at hv
  have he : 0 < (v ^ liEvenCrossEulerCrossoverExponent) ^ 2 :=
    sq_pos_of_pos (Real.rpow_pos_of_pos hv _)
  have hbalance : v ^ (1 - 2 * liEvenCrossEulerCrossoverExponent) *
      (v ^ liEvenCrossEulerCrossoverExponent) ^ 2 = v := by
    rw [pow_two, ← mul_assoc, ← Real.rpow_add hv, ← Real.rpow_add hv]
    rw [show (1 - 2 * liEvenCrossEulerCrossoverExponent + liEvenCrossEulerCrossoverExponent) +
      liEvenCrossEulerCrossoverExponent = 1 by ring, Real.rpow_one]
  have hh := mul_lt_mul_of_pos_right hsmall he
  simpa only [mul_assoc, hbalance] using hh

/-- Every index through the lower floor is positive, and the upper successor is negative. -/
theorem liEvenCrossEulerSourceBoundary_eventually_floor_signs
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∀ k : ℕ, k ≤ Nat.floor (liEvenCrossEulerCrossoverCenter v +
          liEvenCrossEulerSourceBoundaryOffset v
            (liEvenCrossEulerSourceBoundarySecondCorrection - δ)) →
        0 < liEvenCrossFirstCurrentEvenEulerJet v k) ∧
      liEvenCrossFirstCurrentEvenEulerJet v
        (Nat.floor (liEvenCrossEulerCrossoverCenter v +
          liEvenCrossEulerSourceBoundaryOffset v
            (liEvenCrossEulerSourceBoundarySecondCorrection + δ)) + 1) < 0 := by
  obtain ⟨D, _, hremainder⟩ := liEvenCrossEulerCrossoverThreeTermProfile_uniform_remainder 2
  let m : ℝ := normalizedPrimeArchMoment 0
  let b : ℝ := liEvenCrossEulerCrossoverThirdAmplitude
  let L : ℝ := Real.log 4
  let H : ℝ := Real.log 9
  let c : ℝ := m * L * δ / 2
  have hm : 0 < m := normalizedPrimeArchMoment_pos_of_le_eleven 0 (by omega)
  have hb : 0 < b := liEvenCrossEulerCrossoverThirdAmplitude_pos
  have hL : 0 < L := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hH : 0 < H := Real.log_pos (by norm_num : (1 : ℝ) < 9)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall : 0 < m * L / (2 * b * H * Real.exp (2 * H)) := by positivity
  have hsides := sourceBoundary_mass_tendstoWithin.eventually
    (liEvenCrossEulerBoundaryModel_eventually_second_layer_sides m b L H hm hL hδ)
  filter_upwards [self_mem_nhdsWithin,
    liEvenCrossEulerCrossoverCenter_tendsto_atTop.eventually_ge_atTop 0,
    liEvenCrossFirstCurrentEvenEulerJet_eventually_pos_le_crossover, hremainder,
    sourceBoundary_mass_tendsto.eventually (Iio_mem_nhds hsmall),
    sourceBoundary_error_eventually_lt D c hc,
    sourceBoundary_offset_eventually_mem (liEvenCrossEulerSourceBoundarySecondCorrection - δ),
    sourceBoundary_offset_eventually_mem (liEvenCrossEulerSourceBoundarySecondCorrection + δ),
    hsides] with v hv hx hearlier herr hesmall herrsmall hloffset hhoffset hsides
  change 0 < v at hv
  let e : ℝ := v ^ liEvenCrossEulerCrossoverExponent
  have he : 0 < e := Real.rpow_pos_of_pos hv _
  have hden : 0 < 2 * v := by positivity
  have hanti := liEvenCrossEulerBoundaryModel_strictAntiOn_Icc_zero_two
    m b L H e hm hb hL hH he.le hesmall.le
  have hmodel : liEvenCrossEulerCrossoverTwoExponentialModel v =
      liEvenCrossEulerBoundaryModel m b L H e := by
    funext u
    exact sourceBoundary_model_eq v u
  rw [← hmodel] at hanti
  have hlomargin : c * e ^ 2 < liEvenCrossEulerCrossoverTwoExponentialModel v
      (liEvenCrossEulerSourceBoundaryOffset v
        (liEvenCrossEulerSourceBoundarySecondCorrection - δ)) := by
    rw [sourceBoundary_model_eq, sourceBoundary_offset_eq_sq hv]
    exact hsides.1
  have hhimargin : liEvenCrossEulerCrossoverTwoExponentialModel v
      (liEvenCrossEulerSourceBoundaryOffset v
        (liEvenCrossEulerSourceBoundarySecondCorrection + δ)) < -c * e ^ 2 := by
    rw [sourceBoundary_model_eq, sourceBoundary_offset_eq_sq hv]
    exact hsides.2
  have hlomem : liEvenCrossEulerSourceBoundaryOffset v
      (liEvenCrossEulerSourceBoundarySecondCorrection - δ) ∈ Set.Icc 0 2 :=
    ⟨hloffset.1.le, by linarith [hloffset.2]⟩
  have hhimem : liEvenCrossEulerSourceBoundaryOffset v
      (liEvenCrossEulerSourceBoundarySecondCorrection + δ) ∈ Set.Icc 0 2 :=
    ⟨hhoffset.1.le, by linarith [hhoffset.2]⟩
  constructor
  · intro k hk
    have hy : 0 ≤ liEvenCrossEulerCrossoverCenter v +
        liEvenCrossEulerSourceBoundaryOffset v
          (liEvenCrossEulerSourceBoundarySecondCorrection - δ) := by
      linarith [hloffset.1]
    have hkreal : (k : ℝ) ≤ liEvenCrossEulerCrossoverCenter v +
        liEvenCrossEulerSourceBoundaryOffset v
          (liEvenCrossEulerSourceBoundarySecondCorrection - δ) := by
      have hkcast : (k : ℝ) ≤ (Nat.floor (liEvenCrossEulerCrossoverCenter v +
          liEvenCrossEulerSourceBoundaryOffset v
            (liEvenCrossEulerSourceBoundarySecondCorrection - δ)) : ℝ) := by
        exact_mod_cast hk
      exact hkcast.trans (Nat.floor_le hy)
    by_cases hkearly : (k : ℝ) ≤ liEvenCrossEulerCrossoverCenter v
    · exact hearlier k hkearly
    · have hu0 : 0 < (k : ℝ) - liEvenCrossEulerCrossoverCenter v := by
        linarith [lt_of_not_ge hkearly]
      have hule : (k : ℝ) - liEvenCrossEulerCrossoverCenter v ≤
          liEvenCrossEulerSourceBoundaryOffset v
            (liEvenCrossEulerSourceBoundarySecondCorrection - δ) := by linarith
      have hu2 : (k : ℝ) - liEvenCrossEulerCrossoverCenter v ≤ 2 := by
        linarith [hloffset.2]
      have humem : (k : ℝ) - liEvenCrossEulerCrossoverCenter v ∈ Set.Icc 0 2 :=
        ⟨hu0.le, hu2⟩
      have hmodelge := hanti.antitoneOn humem hlomem hule
      have hmargin := hlomargin.trans_le hmodelge
      have hwindow : |(k : ℝ) - liEvenCrossEulerCrossoverCenter v| ≤ 2 := by
        rw [abs_of_pos hu0]
        exact hu2
      have hbound := (abs_le.mp (herr k hwindow)).1
      have hnormalized : 0 < liEvenCrossFirstCurrentEvenEulerJet v k / (2 * v) := by
        change D * v < c * e ^ 2 at herrsmall
        linarith
      simpa only [div_mul_cancel₀ _ hden.ne'] using mul_pos hnormalized hden
  · let n : ℕ := Nat.floor (liEvenCrossEulerCrossoverCenter v +
      liEvenCrossEulerSourceBoundaryOffset v
        (liEvenCrossEulerSourceBoundarySecondCorrection + δ)) + 1
    have hy : 0 ≤ liEvenCrossEulerCrossoverCenter v +
        liEvenCrossEulerSourceBoundaryOffset v
          (liEvenCrossEulerSourceBoundarySecondCorrection + δ) := by
      linarith [hhoffset.1]
    have hfloorle := Nat.floor_le hy
    have hfloorlt := Nat.lt_floor_add_one (liEvenCrossEulerCrossoverCenter v +
      liEvenCrossEulerSourceBoundaryOffset v
        (liEvenCrossEulerSourceBoundarySecondCorrection + δ))
    have hunlo : liEvenCrossEulerSourceBoundaryOffset v
        (liEvenCrossEulerSourceBoundarySecondCorrection + δ) <
          (n : ℝ) - liEvenCrossEulerCrossoverCenter v := by
      dsimp [n]
      push_cast
      linarith
    have hun0 : 0 < (n : ℝ) - liEvenCrossEulerCrossoverCenter v :=
      hhoffset.1.trans hunlo
    have hun2 : (n : ℝ) - liEvenCrossEulerCrossoverCenter v < 2 := by
      dsimp [n]
      push_cast
      linarith [hhoffset.2]
    have hunmem : (n : ℝ) - liEvenCrossEulerCrossoverCenter v ∈ Set.Icc 0 2 :=
      ⟨hun0.le, hun2.le⟩
    have hmodelle := hanti.antitoneOn hhimem hunmem hunlo.le
    have hmargin := hmodelle.trans_lt hhimargin
    have hwindow : |(n : ℝ) - liEvenCrossEulerCrossoverCenter v| ≤ 2 := by
      rw [abs_of_pos hun0]
      exact hun2.le
    have hbound := (abs_le.mp (herr n hwindow)).2
    have hnormalized : liEvenCrossFirstCurrentEvenEulerJet v n / (2 * v) < 0 := by
      change D * v < c * e ^ 2 at herrsmall
      linarith
    simpa only [div_mul_cancel₀ _ hden.ne'] using mul_neg_of_neg_of_pos hnormalized hden

/-- Exact two-layer floor sandwich for the least negative actual Euler-jet index. -/
theorem liEvenCrossFirstNegativeEulerOrder_eventually_source_boundary_floor_sandwich
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0),
      Nat.floor (liEvenCrossEulerCrossoverCenter v +
        liEvenCrossEulerSourceBoundaryFirstCorrection * v ^ liEvenCrossEulerCrossoverExponent +
        (liEvenCrossEulerSourceBoundarySecondCorrection - δ) *
          v ^ (2 * liEvenCrossEulerCrossoverExponent)) + 1 ≤
          liEvenCrossFirstNegativeEulerOrder v ∧
      liEvenCrossFirstNegativeEulerOrder v ≤
        Nat.floor (liEvenCrossEulerCrossoverCenter v +
          liEvenCrossEulerSourceBoundaryFirstCorrection * v ^ liEvenCrossEulerCrossoverExponent +
          (liEvenCrossEulerSourceBoundarySecondCorrection + δ) *
            v ^ (2 * liEvenCrossEulerCrossoverExponent)) + 1 := by
  filter_upwards [self_mem_nhdsWithin,
    liEvenCrossEulerSourceBoundary_eventually_floor_signs hδ] with v hv hsigns
  have hlower : Nat.floor (liEvenCrossEulerCrossoverCenter v +
      liEvenCrossEulerSourceBoundaryOffset v
        (liEvenCrossEulerSourceBoundarySecondCorrection - δ)) + 1 ≤
        liEvenCrossFirstNegativeEulerOrder v := by
    by_contra h
    have hk : liEvenCrossFirstNegativeEulerOrder v ≤ Nat.floor
        (liEvenCrossEulerCrossoverCenter v + liEvenCrossEulerSourceBoundaryOffset v
          (liEvenCrossEulerSourceBoundarySecondCorrection - δ)) := by omega
    have hpositive := hsigns.1 (liEvenCrossFirstNegativeEulerOrder v) hk
    exact (not_lt_of_gt hpositive) (liEvenCrossFirstNegativeEulerOrder_jet_neg hv)
  have hupper := liEvenCrossFirstNegativeEulerOrder_le_of_jet_neg hv hsigns.2
  simpa only [liEvenCrossEulerSourceBoundaryOffset, add_assoc] using And.intro hlower hupper

end

end RHTower
