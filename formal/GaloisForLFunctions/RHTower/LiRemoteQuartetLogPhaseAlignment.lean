import GaloisForLFunctions.RHTower.LiRemoteQuartetPhaseAlignment

/-!
# Logarithmic phase alignment for remote Li quartets

The nearest-phase construction is extended from fixed radial targets to arbitrary targets tending
to infinity.  Specializing to `c = 4 log H`, `H = 1 / ell`, proves the exact selector bounds,
phase alignment modulo `2π`, and `n / (H log H) → 4` from card equations (32)--(33).
-/

open Filter Topology

namespace RHTower

noncomputable section

theorem eventually_liVariablePhaseAlignedIntegerDegree_nonneg
    {ι : Type*} {l : Filter ι} {ell theta c : ι → ℝ}
    (hc : Tendsto c l atTop)
    (hell : Tendsto ell l (nhds 0))
    (hratio : Tendsto (fun i => ell i / theta i) l (nhds 0))
    (hpos : ∀ᶠ i in l, 0 < ell i ∧ 0 < theta i) :
    ∀ᶠ i in l, 0 ≤ liPhaseAlignedIntegerDegree (c i / ell i) (theta i) := by
  have herr := tendsto_liPhaseAlignmentRadialError hell hratio
  have herrlt : ∀ᶠ i in l, liPhaseAlignmentRadialError (ell i) (theta i) < 1 :=
    (tendsto_order.1 herr).2 1 zero_lt_one
  have hcgt : ∀ᶠ i in l, 1 < c i := hc.eventually_gt_atTop 1
  filter_upwards [hpos, herrlt, hcgt] with i hi herror hci
  have hb := abs_liPhaseAlignedIntegerDegree_sub_le
    (x := c i / ell i) hi.2
  have hlower := (abs_le.1 hb).1
  have hpoint : c i / ell i - (Real.pi / theta i + 1 / 2) ≤
      (liPhaseAlignedIntegerDegree (c i / ell i) (theta i) : ℝ) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hpoint hi.1.le
  have hid :
      ell i * (c i / ell i - (Real.pi / theta i + 1 / 2)) =
        c i - liPhaseAlignmentRadialError (ell i) (theta i) := by
    unfold liPhaseAlignmentRadialError
    field_simp [ne_of_gt hi.1, ne_of_gt hi.2]
  rw [hid] at hmul
  have hpositive : 0 < c i - liPhaseAlignmentRadialError (ell i) (theta i) := by
    linarith
  have hzprod : 0 < ell i *
      (liPhaseAlignedIntegerDegree (c i / ell i) (theta i) : ℝ) :=
    lt_of_lt_of_le hpositive hmul
  have hzreal : 0 <
      (liPhaseAlignedIntegerDegree (c i / ell i) (theta i) : ℝ) := by
    by_contra hnpos
    have hzle : (liPhaseAlignedIntegerDegree (c i / ell i) (theta i) : ℝ) ≤ 0 :=
      le_of_not_gt hnpos
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hi.1.le hzle)) hzprod
  exact_mod_cast hzreal.le

theorem eventually_cast_liVariablePhaseAlignedDegree
    {ι : Type*} {l : Filter ι} {ell theta c : ι → ℝ}
    (hc : Tendsto c l atTop)
    (hell : Tendsto ell l (nhds 0))
    (hratio : Tendsto (fun i => ell i / theta i) l (nhds 0))
    (hpos : ∀ᶠ i in l, 0 < ell i ∧ 0 < theta i) :
    ∀ᶠ i in l,
      (liPhaseAlignedDegree (c i / ell i) (theta i) : ℝ) =
        (liPhaseAlignedIntegerDegree (c i / ell i) (theta i) : ℝ) := by
  filter_upwards [eventually_liVariablePhaseAlignedIntegerDegree_nonneg
      hc hell hratio hpos] with i hi
  unfold liPhaseAlignedDegree
  exact_mod_cast Int.toNat_of_nonneg hi

theorem tendsto_liVariablePhaseAlignedDegree_radial_sub_target
    {ι : Type*} {l : Filter ι} {ell theta c : ι → ℝ}
    (hc : Tendsto c l atTop)
    (hell : Tendsto ell l (nhds 0))
    (hratio : Tendsto (fun i => ell i / theta i) l (nhds 0))
    (hpos : ∀ᶠ i in l, 0 < ell i ∧ 0 < theta i) :
    Tendsto (fun i =>
        (liPhaseAlignedDegree (c i / ell i) (theta i) : ℝ) * ell i - c i)
      l (nhds 0) := by
  have herr := tendsto_liPhaseAlignmentRadialError hell hratio
  have hcast := eventually_cast_liVariablePhaseAlignedDegree hc hell hratio hpos
  refine squeeze_zero_norm' ?_ herr
  filter_upwards [hpos, hcast] with i hi hcasti
  rw [Real.norm_eq_abs, hcasti]
  have hb := abs_liPhaseAlignedIntegerDegree_sub_le
    (x := c i / ell i) hi.2
  have heq :
      (liPhaseAlignedIntegerDegree (c i / ell i) (theta i) : ℝ) * ell i - c i =
        ell i * ((liPhaseAlignedIntegerDegree (c i / ell i) (theta i) : ℝ) -
          c i / ell i) := by
    field_simp [ne_of_gt hi.1]
  rw [heq, abs_mul, abs_of_pos hi.1]
  calc
    ell i * |(liPhaseAlignedIntegerDegree (c i / ell i) (theta i) : ℝ) -
        c i / ell i| ≤ ell i * (Real.pi / theta i + 1 / 2) :=
      mul_le_mul_of_nonneg_left hb hi.1.le
    _ = liPhaseAlignmentRadialError (ell i) (theta i) := by
      unfold liPhaseAlignmentRadialError
      field_simp [ne_of_gt hi.2]

theorem tendstoModuloTwoPi_liVariablePhaseAlignedDegree
    {ι : Type*} {l : Filter ι} {ell theta c : ι → ℝ}
    (hc : Tendsto c l atTop)
    (hell : Tendsto ell l (nhds 0))
    (htheta : Tendsto theta l (nhds 0))
    (hratio : Tendsto (fun i => ell i / theta i) l (nhds 0))
    (hpos : ∀ᶠ i in l, 0 < ell i ∧ 0 < theta i) :
    TendstoModuloTwoPi
      (fun i => (liPhaseAlignedDegree (c i / ell i) (theta i) : ℝ) * theta i)
      l 0 := by
  refine ⟨fun i => liNearestPeriodIndex (c i / ell i) (theta i), ?_⟩
  have hcast := eventually_cast_liVariablePhaseAlignedDegree hc hell hratio hpos
  have hhalf : Tendsto (fun i => theta i / 2) l (nhds 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using htheta.mul_const (2 : ℝ)⁻¹
  refine squeeze_zero_norm' ?_ hhalf
  filter_upwards [hpos, hcast] with i hi hcasti
  rw [Real.norm_eq_abs, hcasti]
  exact abs_liPhaseAlignedIntegerDegree_phase_sub_le hi.2

/-- Inverse radial visibility scale `H = 1 / ell`. -/
def liRemoteVisibilityScale (a T : ℝ) : ℝ :=
  (liRemoteRadialCoordinate a T)⁻¹

/-- Growing transverse target `c = 4 log H` from card equation (32). -/
def liRemoteLogarithmicTarget (a T : ℝ) : ℝ :=
  4 * Real.log (liRemoteVisibilityScale a T)

/-- Phase-aligned degree at the logarithmically growing transverse target. -/
def liRemoteLogPhaseAlignedDegree (a T : ℝ) : ℕ :=
  liPhaseAlignedDegree
    (liRemoteLogarithmicTarget a T / liRemoteRadialCoordinate a T)
    (liRemoteAngularCoordinate a T)

/-- Period index witnessing alignment of `liRemoteLogPhaseAlignedDegree`. -/
def liRemoteLogPhasePeriodIndex (a T : ℝ) : ℤ :=
  liNearestPeriodIndex
    (liRemoteLogarithmicTarget a T / liRemoteRadialCoordinate a T)
    (liRemoteAngularCoordinate a T)

theorem tendsto_liRemoteVisibilityScale_atTop
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i => liRemoteVisibilityScale (a i) (T i)) l atTop := by
  have hell := tendsto_liRemoteRadialCoordinate_zero hT ha
  have hpos : ∀ᶠ i in l, 0 < liRemoteRadialCoordinate (a i) (T i) :=
    (eventually_liRemoteCoordinates_pos hT ha).mono fun _ hi => hi.1
  have hwithin : Tendsto (fun i => liRemoteRadialCoordinate (a i) (T i))
      l (nhdsWithin 0 (Set.Ioi 0)) := tendsto_nhdsWithin_iff.2 ⟨hell, hpos⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hwithin
  refine hinv.congr' ?_
  filter_upwards with i
  rfl

theorem tendsto_liRemoteLogarithmicTarget_atTop
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i => liRemoteLogarithmicTarget (a i) (T i)) l atTop := by
  have hH := tendsto_liRemoteVisibilityScale_atTop hT ha
  have hlog0 := Real.tendsto_log_atTop.comp hH
  have hlog : Tendsto (fun i => Real.log (liRemoteVisibilityScale (a i) (T i)))
      l atTop := hlog0.congr' (by filter_upwards with i; rfl)
  exact Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4) hlog

theorem eventually_liRemoteLogPhaseAlignedDegree_bounds
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    ∀ᶠ i in l,
      |(liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) -
          liRemoteLogarithmicTarget (a i) (T i) /
            liRemoteRadialCoordinate (a i) (T i)| ≤
          Real.pi / liRemoteAngularCoordinate (a i) (T i) + 1 / 2 ∧
        |(liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) *
              liRemoteAngularCoordinate (a i) (T i) -
            (liRemoteLogPhasePeriodIndex (a i) (T i) : ℝ) * (2 * Real.pi)| ≤
          liRemoteAngularCoordinate (a i) (T i) / 2 := by
  let ell : ι → ℝ := fun i => liRemoteRadialCoordinate (a i) (T i)
  let theta : ι → ℝ := fun i => liRemoteAngularCoordinate (a i) (T i)
  let c : ι → ℝ := fun i => liRemoteLogarithmicTarget (a i) (T i)
  have hc := tendsto_liRemoteLogarithmicTarget_atTop hT ha
  have hell := tendsto_liRemoteRadialCoordinate_zero hT ha
  have hratio := tendsto_liRemoteRadial_div_angular hT ha
  have hpos := eventually_liRemoteCoordinates_pos hT ha
  have hcast := eventually_cast_liVariablePhaseAlignedDegree hc hell hratio hpos
  filter_upwards [hpos, hcast] with i hi hcasti
  constructor
  · unfold liRemoteLogPhaseAlignedDegree
    rw [hcasti]
    exact abs_liPhaseAlignedIntegerDegree_sub_le hi.2
  · unfold liRemoteLogPhaseAlignedDegree liRemoteLogPhasePeriodIndex
    rw [hcasti]
    exact abs_liPhaseAlignedIntegerDegree_phase_sub_le hi.2

theorem tendsto_liRemoteLogPhaseAlignedDegree_radial_sub_target
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i =>
        (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) *
            liRemoteRadialCoordinate (a i) (T i) -
          liRemoteLogarithmicTarget (a i) (T i)) l (nhds 0) := by
  exact tendsto_liVariablePhaseAlignedDegree_radial_sub_target
    (tendsto_liRemoteLogarithmicTarget_atTop hT ha)
    (tendsto_liRemoteRadialCoordinate_zero hT ha)
    (tendsto_liRemoteRadial_div_angular hT ha)
    (eventually_liRemoteCoordinates_pos hT ha)

theorem tendstoModuloTwoPi_liRemoteLogPhaseAlignedDegree
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    TendstoModuloTwoPi
      (fun i => (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) *
        liRemoteAngularCoordinate (a i) (T i)) l 0 := by
  exact tendstoModuloTwoPi_liVariablePhaseAlignedDegree
    (tendsto_liRemoteLogarithmicTarget_atTop hT ha)
    (tendsto_liRemoteRadialCoordinate_zero hT ha)
    (tendsto_liRemoteAngularCoordinate_zero hT ha)
    (tendsto_liRemoteRadial_div_angular hT ha)
    (eventually_liRemoteCoordinates_pos hT ha)

/-- Card equation (33): `n ell / log H → 4`. -/
theorem tendsto_liRemoteLogPhaseAlignedDegree_radial_div_log
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i =>
        (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) *
            liRemoteRadialCoordinate (a i) (T i) /
          Real.log (liRemoteVisibilityScale (a i) (T i))) l (nhds 4) := by
  have hdiff := tendsto_liRemoteLogPhaseAlignedDegree_radial_sub_target hT ha
  have hH := tendsto_liRemoteVisibilityScale_atTop hT ha
  have hlog := Real.tendsto_log_atTop.comp hH
  have hquot : Tendsto (fun i =>
      ((liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) *
            liRemoteRadialCoordinate (a i) (T i) -
          liRemoteLogarithmicTarget (a i) (T i)) /
        Real.log (liRemoteVisibilityScale (a i) (T i))) l (nhds 0) :=
    Filter.Tendsto.div_atTop hdiff hlog
  have hsum := hquot.add_const 4
  have hlogPos : ∀ᶠ i in l, 0 < Real.log (liRemoteVisibilityScale (a i) (T i)) :=
    hlog.eventually_gt_atTop 0
  have hsum' : Tendsto (fun i =>
      (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) *
          liRemoteRadialCoordinate (a i) (T i) /
        Real.log (liRemoteVisibilityScale (a i) (T i)))
      l (nhds (0 + 4)) := hsum.congr' (by
        filter_upwards [hlogPos] with i hi
        unfold liRemoteLogarithmicTarget
        field_simp [ne_of_gt hi]
        ring)
  simpa only [zero_add] using hsum'

/-- Card equation (33), literal form: `n / (H log H) → 4`. -/
theorem tendsto_liRemoteLogPhaseAlignedDegree_div_visibilityLog
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i =>
        (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) /
          (liRemoteVisibilityScale (a i) (T i) *
            Real.log (liRemoteVisibilityScale (a i) (T i)))) l (nhds 4) := by
  have hscale := tendsto_liRemoteLogPhaseAlignedDegree_radial_div_log hT ha
  have hpos := eventually_liRemoteCoordinates_pos hT ha
  have hlog := Real.tendsto_log_atTop.comp (tendsto_liRemoteVisibilityScale_atTop hT ha)
  have hlogPos := hlog.eventually_gt_atTop 0
  refine hscale.congr' ?_
  filter_upwards [hpos, hlogPos] with i hi hlogi
  unfold liRemoteVisibilityScale
  field_simp [ne_of_gt hi.1, ne_of_gt hlogi]

private theorem tendsto_real_fourth_atTop
    {ι : Type*} {l : Filter ι} {H : ι → ℝ}
    (hH : Tendsto H l atTop) :
    Tendsto (fun i => H i ^ 4) l atTop := by
  refine tendsto_atTop_mono' l ?_ hH
  filter_upwards [hH.eventually_gt_atTop 1] with i hi
  have h2 : H i ≤ H i ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ H i) (by linarith : 0 ≤ H i - 1)]
  have h4 : H i ^ 2 ≤ H i ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg (H i))
      (by nlinarith [sq_nonneg (H i - 1)] : 0 ≤ H i ^ 2 - 1)]
  exact h2.trans h4

private theorem tendsto_real_eighth_atTop
    {ι : Type*} {l : Filter ι} {H : ι → ℝ}
    (hH : Tendsto H l atTop) :
    Tendsto (fun i => H i ^ 8) l atTop := by
  have h4 := tendsto_real_fourth_atTop hH
  refine tendsto_atTop_mono' l ?_ h4
  filter_upwards [hH.eventually_gt_atTop 1] with i hi
  have h4one : 1 ≤ H i ^ 4 := by
    nlinarith [sq_nonneg (H i), sq_nonneg (H i ^ 2 - 1)]
  nlinarith [mul_nonneg (by positivity : 0 ≤ H i ^ 4)
    (by linarith : 0 ≤ H i ^ 4 - 1)]

/-- If `x - 4 log H → 0` and `H → ∞`, then `cosh x / H⁴ → 1/2`. -/
theorem tendsto_cosh_div_fourth_of_sub_four_log
    {ι : Type*} {l : Filter ι} {x H : ι → ℝ}
    (hH : Tendsto H l atTop)
    (hdiff : Tendsto (fun i => x i - 4 * Real.log (H i)) l (nhds 0)) :
    Tendsto (fun i => Real.cosh (x i) / H i ^ 4) l (nhds (1 / 2)) := by
  let d : ι → ℝ := fun i => x i - 4 * Real.log (H i)
  have hd : Tendsto d l (nhds 0) := hdiff
  have hexp : Tendsto (fun i => Real.exp (d i)) l (nhds 1) := by
    have h0 := (Real.continuous_exp.tendsto 0).comp hd
    simpa only [Real.exp_zero] using h0.congr' (by filter_upwards with i; rfl)
  have hneg : Tendsto (fun i => -d i) l (nhds 0) := by
    simpa only [neg_zero] using hd.neg
  have hexpNeg : Tendsto (fun i => Real.exp (-d i)) l (nhds 1) := by
    have h0 := (Real.continuous_exp.tendsto 0).comp hneg
    simpa only [Real.exp_zero] using h0.congr' (by filter_upwards with i; rfl)
  have hH8 : Tendsto (fun i => H i ^ 8) l atTop :=
    tendsto_real_eighth_atTop hH
  have hsmall : Tendsto (fun i => Real.exp (-d i) / H i ^ 8) l (nhds 0) :=
    Filter.Tendsto.div_atTop hexpNeg hH8
  have hsum := (hexp.add hsmall).mul_const (1 / 2 : ℝ)
  have hHpos : ∀ᶠ i in l, 0 < H i := hH.eventually_gt_atTop 0
  have hsum' : Tendsto (fun i => Real.cosh (x i) / H i ^ 4)
      l (nhds ((1 + 0) * (1 / 2))) := hsum.congr' (by
        filter_upwards [hHpos] with i hHi
        have hH0 := ne_of_gt hHi
        have hexpLog : Real.exp (4 * Real.log (H i)) = H i ^ 4 := by
          have h := Real.exp_nat_mul (Real.log (H i)) 4
          rw [Real.exp_log hHi] at h
          norm_num at h ⊢
          exact h
        have hx : x i = d i + 4 * Real.log (H i) := by
          dsimp [d]
          ring
        rw [Real.cosh_eq, hx, Real.exp_add, hexpLog]
        rw [show -(d i + 4 * Real.log (H i)) =
            -d i + -(4 * Real.log (H i)) by ring, Real.exp_add]
        have hexpNegLog : Real.exp (-(4 * Real.log (H i))) = (H i ^ 4)⁻¹ := by
          rw [Real.exp_neg, hexpLog]
        rw [hexpNegLog, Real.exp_neg]
        field_simp [hH0, Real.exp_ne_zero])
  norm_num at hsum' ⊢
  exact hsum'

/-- Card equation (34): the logarithmically aligned quartet is `-2 H⁴ (1+o(1))`. -/
theorem tendsto_liRemoteLogPhaseAlignedQuartetProfile_normalized
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i =>
        liRemoteQuartetProfile (liRemoteLogPhaseAlignedDegree (a i) (T i))
            (liRemoteRadialCoordinate (a i) (T i))
            (liRemoteAngularCoordinate (a i) (T i)) /
          (-2 * liRemoteVisibilityScale (a i) (T i) ^ 4))
      l (nhds 1) := by
  let n : ι → ℕ := fun i => liRemoteLogPhaseAlignedDegree (a i) (T i)
  let ell : ι → ℝ := fun i => liRemoteRadialCoordinate (a i) (T i)
  let theta : ι → ℝ := fun i => liRemoteAngularCoordinate (a i) (T i)
  let H : ι → ℝ := fun i => liRemoteVisibilityScale (a i) (T i)
  have hH : Tendsto H l atTop := tendsto_liRemoteVisibilityScale_atTop hT ha
  have hdiff : Tendsto (fun i => (n i : ℝ) * ell i - 4 * Real.log (H i))
      l (nhds 0) := by
    simpa only [n, ell, H, liRemoteLogarithmicTarget] using
      tendsto_liRemoteLogPhaseAlignedDegree_radial_sub_target hT ha
  have hcosh : Tendsto (fun i => Real.cosh ((n i : ℝ) * ell i) / H i ^ 4)
      l (nhds (1 / 2)) := tendsto_cosh_div_fourth_of_sub_four_log hH hdiff
  have hphase := tendstoModuloTwoPi_liRemoteLogPhaseAlignedDegree hT ha
  have hcos : Tendsto (fun i => Real.cos ((n i : ℝ) * theta i)) l (nhds 1) := by
    simpa only [n, theta, Real.cos_zero] using hphase.cos
  have hH4 : Tendsto (fun i => H i ^ 4) l atTop :=
    tendsto_real_fourth_atTop hH
  have hinv : Tendsto (fun i => (1 : ℝ) / H i ^ 4) l (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hH4
  have hnorm := ((hcosh.mul hcos).sub hinv).const_mul (2 : ℝ)
  have hHpos : ∀ᶠ i in l, 0 < H i := hH.eventually_gt_atTop 0
  have hnorm' : Tendsto (fun i =>
      liRemoteQuartetProfile (n i) (ell i) (theta i) / (-2 * H i ^ 4))
      l (nhds (2 * ((1 / 2) * 1 - 0))) := hnorm.congr' (by
        filter_upwards [hHpos] with i hHi
        unfold liRemoteQuartetProfile
        field_simp [ne_of_gt hHi]
        ring)
  norm_num at hnorm' ⊢
  exact hnorm'

end
end RHTower
