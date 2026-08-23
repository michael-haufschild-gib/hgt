import GaloisForLFunctions.RHTower.LiRemoteQuartetAsymptotics

/-!
# Constructive phase alignment for remote Li quartets

This module implements the card's deterministic two-stage nearest-integer selector.  It proves the
exact finite error bounds, transports them through the remote-quartet coordinate asymptotics, and
obtains a strict negative quartet limit at every positive transverse radius.  All choices are
explicit floor operations; no recurrence or subsequence extraction is used.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Nearest-integer selector, with ties resolved downward. -/
def nearestInteger (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

theorem abs_nearestInteger_sub_le_half (x : ℝ) :
    |((nearestInteger x : ℤ) : ℝ) - x| ≤ 1 / 2 := by
  rw [abs_le]
  constructor
  · have h := Int.lt_floor_add_one (x + 1 / 2)
    dsimp [nearestInteger]
    linarith
  · have h := Int.floor_le (x + 1 / 2)
    dsimp [nearestInteger]
    linarith

theorem nearestInteger_nonneg {x : ℝ} (hx : 1 / 2 ≤ x) :
    0 ≤ nearestInteger x := by
  rw [nearestInteger, Int.le_floor]
  norm_num
  linarith

theorem cast_toNat_nearestInteger {x : ℝ} (hx : 1 / 2 ≤ x) :
    ((nearestInteger x).toNat : ℝ) = (nearestInteger x : ℤ) := by
  exact_mod_cast Int.toNat_of_nonneg (nearestInteger_nonneg hx)

/-- Index of the multiple of `2π / theta` nearest to `x`. -/
def liNearestPeriodIndex (x theta : ℝ) : ℤ :=
  nearestInteger (x * theta / (2 * Real.pi))

/-- Real multiple of `2π / theta` selected near `x`. -/
def liNearestPhaseTarget (x theta : ℝ) : ℝ :=
  (liNearestPeriodIndex x theta : ℝ) * (2 * Real.pi) / theta

/-- Integer nearest to the selected real phase target. -/
def liPhaseAlignedIntegerDegree (x theta : ℝ) : ℤ :=
  nearestInteger (liNearestPhaseTarget x theta)

/-- Natural degree obtained from the phase-aligned integer. -/
def liPhaseAlignedDegree (x theta : ℝ) : ℕ :=
  (liPhaseAlignedIntegerDegree x theta).toNat

theorem abs_liNearestPhaseTarget_sub_le {x theta : ℝ} (htheta : 0 < theta) :
    |liNearestPhaseTarget x theta - x| ≤ Real.pi / theta := by
  have hm := abs_nearestInteger_sub_le_half (x * theta / (2 * Real.pi))
  have hfac : 0 ≤ (2 * Real.pi) / theta :=
    (div_pos (mul_pos (by norm_num) Real.pi_pos) htheta).le
  have heq :
      liNearestPhaseTarget x theta - x =
        ((2 * Real.pi) / theta) *
          ((liNearestPeriodIndex x theta : ℝ) -
            x * theta / (2 * Real.pi)) := by
    unfold liNearestPhaseTarget liNearestPeriodIndex
    field_simp [ne_of_gt htheta, ne_of_gt Real.pi_pos]
  rw [heq, abs_mul, abs_of_nonneg hfac]
  calc
    (2 * Real.pi / theta) *
        |(liNearestPeriodIndex x theta : ℝ) - x * theta / (2 * Real.pi)| ≤
        (2 * Real.pi / theta) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hm hfac
    _ = Real.pi / theta := by ring

theorem abs_liPhaseAlignedIntegerDegree_sub_target_le_half (x theta : ℝ) :
    |(liPhaseAlignedIntegerDegree x theta : ℝ) - liNearestPhaseTarget x theta| ≤
      1 / 2 := by
  exact abs_nearestInteger_sub_le_half _

theorem abs_liPhaseAlignedIntegerDegree_sub_le {x theta : ℝ}
    (htheta : 0 < theta) :
    |(liPhaseAlignedIntegerDegree x theta : ℝ) - x| ≤
      Real.pi / theta + 1 / 2 := by
  calc
    |(liPhaseAlignedIntegerDegree x theta : ℝ) - x| =
        |((liPhaseAlignedIntegerDegree x theta : ℝ) -
            liNearestPhaseTarget x theta) +
          (liNearestPhaseTarget x theta - x)| := by ring_nf
    _ ≤ |(liPhaseAlignedIntegerDegree x theta : ℝ) -
          liNearestPhaseTarget x theta| +
        |liNearestPhaseTarget x theta - x| := abs_add_le _ _
    _ ≤ 1 / 2 + Real.pi / theta :=
      add_le_add (abs_liPhaseAlignedIntegerDegree_sub_target_le_half _ _)
        (abs_liNearestPhaseTarget_sub_le htheta)
    _ = Real.pi / theta + 1 / 2 := by ring

theorem abs_liPhaseAlignedIntegerDegree_phase_sub_le {x theta : ℝ}
    (htheta : 0 < theta) :
    |(liPhaseAlignedIntegerDegree x theta : ℝ) * theta -
        (liNearestPeriodIndex x theta : ℝ) * (2 * Real.pi)| ≤ theta / 2 := by
  have hn := abs_liPhaseAlignedIntegerDegree_sub_target_le_half x theta
  have heq :
      (liPhaseAlignedIntegerDegree x theta : ℝ) * theta -
          (liNearestPeriodIndex x theta : ℝ) * (2 * Real.pi) =
        theta * ((liPhaseAlignedIntegerDegree x theta : ℝ) -
          liNearestPhaseTarget x theta) := by
    unfold liNearestPhaseTarget
    field_simp [ne_of_gt htheta]
  rw [heq, abs_mul, abs_of_pos htheta]
  calc
    theta * |(liPhaseAlignedIntegerDegree x theta : ℝ) -
        liNearestPhaseTarget x theta| ≤ theta * (1 / 2) :=
      mul_le_mul_of_nonneg_left hn htheta.le
    _ = theta / 2 := by ring

theorem cast_liPhaseAlignedDegree {x theta : ℝ}
    (htarget : 1 / 2 ≤ liNearestPhaseTarget x theta) :
    (liPhaseAlignedDegree x theta : ℝ) =
      (liPhaseAlignedIntegerDegree x theta : ℝ) := by
  exact cast_toNat_nearestInteger htarget

theorem abs_liPhaseAlignedDegree_sub_le {x theta : ℝ}
    (htheta : 0 < theta) (htarget : 1 / 2 ≤ liNearestPhaseTarget x theta) :
    |(liPhaseAlignedDegree x theta : ℝ) - x| ≤ Real.pi / theta + 1 / 2 := by
  rw [cast_liPhaseAlignedDegree htarget]
  exact abs_liPhaseAlignedIntegerDegree_sub_le htheta

theorem abs_liPhaseAlignedDegree_phase_sub_le {x theta : ℝ}
    (htheta : 0 < theta) (htarget : 1 / 2 ≤ liNearestPhaseTarget x theta) :
    |(liPhaseAlignedDegree x theta : ℝ) * theta -
        (liNearestPeriodIndex x theta : ℝ) * (2 * Real.pi)| ≤ theta / 2 := by
  rw [cast_liPhaseAlignedDegree htarget]
  exact abs_liPhaseAlignedIntegerDegree_phase_sub_le htheta

/-- Error envelope after multiplying the degree approximation by the radial scale. -/
def liPhaseAlignmentRadialError (ell theta : ℝ) : ℝ :=
  Real.pi * (ell / theta) + ell / 2

theorem tendsto_liPhaseAlignmentRadialError
    {ι : Type*} {l : Filter ι} {ell theta : ι → ℝ}
    (hell : Tendsto ell l (nhds 0))
    (hratio : Tendsto (fun i => ell i / theta i) l (nhds 0)) :
    Tendsto (fun i => liPhaseAlignmentRadialError (ell i) (theta i))
      l (nhds 0) := by
  have h := (hratio.const_mul Real.pi).add (hell.mul_const (1 / 2 : ℝ))
  simpa only [liPhaseAlignmentRadialError, div_eq_mul_inv, mul_zero, zero_add,
    zero_mul, one_mul] using h

theorem eventually_liPhaseAlignedIntegerDegree_nonneg
    {ι : Type*} {l : Filter ι} {ell theta : ι → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hell : Tendsto ell l (nhds 0))
    (hratio : Tendsto (fun i => ell i / theta i) l (nhds 0))
    (hpos : ∀ᶠ i in l, 0 < ell i ∧ 0 < theta i) :
    ∀ᶠ i in l, 0 ≤ liPhaseAlignedIntegerDegree (c / ell i) (theta i) := by
  have herr := tendsto_liPhaseAlignmentRadialError hell hratio
  have hlt : ∀ᶠ i in l, liPhaseAlignmentRadialError (ell i) (theta i) < c :=
    (tendsto_order.1 herr).2 c hc
  filter_upwards [hpos, hlt] with i hi herror
  have hb := abs_liPhaseAlignedIntegerDegree_sub_le
    (x := c / ell i) hi.2
  have hlower := (abs_le.1 hb).1
  have hpoint : c / ell i - (Real.pi / theta i + 1 / 2) ≤
      (liPhaseAlignedIntegerDegree (c / ell i) (theta i) : ℝ) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hpoint hi.1.le
  have hid :
      ell i * (c / ell i - (Real.pi / theta i + 1 / 2)) =
        c - liPhaseAlignmentRadialError (ell i) (theta i) := by
    unfold liPhaseAlignmentRadialError
    field_simp [ne_of_gt hi.1, ne_of_gt hi.2]
  rw [hid] at hmul
  have hzprod : 0 < ell i *
      (liPhaseAlignedIntegerDegree (c / ell i) (theta i) : ℝ) :=
    lt_of_lt_of_le (sub_pos.2 herror) hmul
  have hzreal : 0 <
      (liPhaseAlignedIntegerDegree (c / ell i) (theta i) : ℝ) := by
    by_contra hnpos
    have hzle : (liPhaseAlignedIntegerDegree (c / ell i) (theta i) : ℝ) ≤ 0 :=
      le_of_not_gt hnpos
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hi.1.le hzle)) hzprod
  exact_mod_cast hzreal.le

theorem eventually_cast_liPhaseAlignedDegree
    {ι : Type*} {l : Filter ι} {ell theta : ι → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hell : Tendsto ell l (nhds 0))
    (hratio : Tendsto (fun i => ell i / theta i) l (nhds 0))
    (hpos : ∀ᶠ i in l, 0 < ell i ∧ 0 < theta i) :
    ∀ᶠ i in l,
      (liPhaseAlignedDegree (c / ell i) (theta i) : ℝ) =
        (liPhaseAlignedIntegerDegree (c / ell i) (theta i) : ℝ) := by
  filter_upwards [eventually_liPhaseAlignedIntegerDegree_nonneg hc hell hratio hpos]
      with i hi
  unfold liPhaseAlignedDegree
  exact_mod_cast Int.toNat_of_nonneg hi

/-- Card equation (30), radial component: nearest-phase degrees satisfy `n ell → c`. -/
theorem tendsto_liPhaseAlignedDegree_mul_radial
    {ι : Type*} {l : Filter ι} {ell theta : ι → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hell : Tendsto ell l (nhds 0))
    (hratio : Tendsto (fun i => ell i / theta i) l (nhds 0))
    (hpos : ∀ᶠ i in l, 0 < ell i ∧ 0 < theta i) :
    Tendsto (fun i =>
        (liPhaseAlignedDegree (c / ell i) (theta i) : ℝ) * ell i)
      l (nhds c) := by
  have herr := tendsto_liPhaseAlignmentRadialError hell hratio
  have hcast := eventually_cast_liPhaseAlignedDegree hc hell hratio hpos
  have hdiff : Tendsto (fun i =>
      (liPhaseAlignedDegree (c / ell i) (theta i) : ℝ) * ell i - c)
      l (nhds 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [hpos, hcast] with i hi hcasti
    rw [Real.norm_eq_abs, hcasti]
    have hb := abs_liPhaseAlignedIntegerDegree_sub_le
      (x := c / ell i) hi.2
    have heq :
        (liPhaseAlignedIntegerDegree (c / ell i) (theta i) : ℝ) * ell i - c =
          ell i * ((liPhaseAlignedIntegerDegree (c / ell i) (theta i) : ℝ) -
            c / ell i) := by
      field_simp [ne_of_gt hi.1]
    rw [heq, abs_mul, abs_of_pos hi.1]
    calc
      ell i * |(liPhaseAlignedIntegerDegree (c / ell i) (theta i) : ℝ) -
          c / ell i| ≤ ell i * (Real.pi / theta i + 1 / 2) :=
        mul_le_mul_of_nonneg_left hb hi.1.le
      _ = liPhaseAlignmentRadialError (ell i) (theta i) := by
        unfold liPhaseAlignmentRadialError
        field_simp [ne_of_gt hi.2]
  have hsum := hdiff.add_const c
  simpa only [sub_add_cancel, zero_add] using hsum

/-- Card equation (30), angular component: selected degrees align modulo `2π`. -/
theorem tendstoModuloTwoPi_liPhaseAlignedDegree
    {ι : Type*} {l : Filter ι} {ell theta : ι → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hell : Tendsto ell l (nhds 0))
    (htheta : Tendsto theta l (nhds 0))
    (hratio : Tendsto (fun i => ell i / theta i) l (nhds 0))
    (hpos : ∀ᶠ i in l, 0 < ell i ∧ 0 < theta i) :
    TendstoModuloTwoPi
      (fun i => (liPhaseAlignedDegree (c / ell i) (theta i) : ℝ) * theta i)
      l 0 := by
  refine ⟨fun i => liNearestPeriodIndex (c / ell i) (theta i), ?_⟩
  have hcast := eventually_cast_liPhaseAlignedDegree hc hell hratio hpos
  have hhalf : Tendsto (fun i => theta i / 2) l (nhds 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using htheta.mul_const (2 : ℝ)⁻¹
  refine squeeze_zero_norm' ?_ hhalf
  filter_upwards [hpos, hcast] with i hi hcasti
  rw [Real.norm_eq_abs, hcasti]
  exact abs_liPhaseAlignedIntegerDegree_phase_sub_le hi.2

/-- Exact profile limit along constructive phase-aligned degrees. -/
theorem tendsto_liPhaseAlignedQuartetProfile
    {ι : Type*} {l : Filter ι} {ell theta : ι → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hell : Tendsto ell l (nhds 0))
    (htheta : Tendsto theta l (nhds 0))
    (hratio : Tendsto (fun i => ell i / theta i) l (nhds 0))
    (hpos : ∀ᶠ i in l, 0 < ell i ∧ 0 < theta i) :
    Tendsto (fun i => liRemoteQuartetProfile
        (liPhaseAlignedDegree (c / ell i) (theta i)) (ell i) (theta i))
      l (nhds (4 * (1 - Real.cosh c))) := by
  have hnell := tendsto_liPhaseAlignedDegree_mul_radial hc hell hratio hpos
  have hphase :=
    tendstoModuloTwoPi_liPhaseAlignedDegree hc hell htheta hratio hpos
  have hcosh := (Real.continuous_cosh.tendsto c).comp hnell
  have hcos := hphase.cos
  have hmul := hcosh.mul hcos
  have hone : Tendsto (fun _ : ι => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
  have hprofile := (hone.sub hmul).const_mul (4 : ℝ)
  simpa only [liRemoteQuartetProfile, Function.comp_apply, Real.cos_zero, mul_one]
    using hprofile

/-- The remote angular coordinate vanishes uniformly as height diverges. -/
theorem tendsto_liRemoteAngularCoordinate_zero
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i => liRemoteAngularCoordinate (a i) (T i)) l (nhds 0) := by
  have hscale := tendsto_liRemoteAngularScale hT ha
  have hinvT : Tendsto (fun i => (1 : ℝ) / T i) l (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hT
  have hprod := hscale.mul hinvT
  have hTpos : ∀ᶠ i in l, 0 < T i := hT.eventually_gt_atTop 0
  have hprod' : Tendsto (fun i => liRemoteAngularCoordinate (a i) (T i))
      l (nhds (1 * 0)) := hprod.congr' (by
        filter_upwards [hTpos] with i hi
        field_simp [ne_of_gt hi])
  simpa only [mul_zero] using hprod'

/-- The remote radial coordinate vanishes uniformly as height diverges. -/
theorem tendsto_liRemoteRadialCoordinate_zero
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i => liRemoteRadialCoordinate (a i) (T i)) l (nhds 0) := by
  have hratio := tendsto_liRemoteRadial_div_angular hT ha
  have htheta := tendsto_liRemoteAngularCoordinate_zero hT ha
  have hprod := hratio.mul htheta
  have hTlarge : ∀ᶠ i in l, 1 / 2 < T i := hT.eventually_gt_atTop (1 / 2)
  have hprod' : Tendsto (fun i => liRemoteRadialCoordinate (a i) (T i))
      l (nhds (0 * 0)) := hprod.congr' (by
        filter_upwards [hTlarge] with i hi
        have hthetaPos := liRemoteAngularCoordinate_pos (a := a i) hi
        field_simp [ne_of_gt hthetaPos])
  simpa only [zero_mul] using hprod'

/-- Both remote coordinates are eventually strictly positive. -/
theorem eventually_liRemoteCoordinates_pos
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    ∀ᶠ i in l,
      0 < liRemoteRadialCoordinate (a i) (T i) ∧
        0 < liRemoteAngularCoordinate (a i) (T i) := by
  filter_upwards [ha, hT.eventually_gt_atTop (1 / 2)] with i hai hTi
  exact ⟨liRemoteRadialCoordinate_pos hai.1 (ne_of_gt (by linarith)),
    liRemoteAngularCoordinate_pos hTi⟩

/-- Constructive phase-aligned degree for a remote quartet and radial target `c`. -/
def liRemotePhaseAlignedDegree (c a T : ℝ) : ℕ :=
  liPhaseAlignedDegree
    (c / liRemoteRadialCoordinate a T)
    (liRemoteAngularCoordinate a T)

/-- Integer period witnessing phase alignment of `liRemotePhaseAlignedDegree`. -/
def liRemotePhasePeriodIndex (c a T : ℝ) : ℤ :=
  liNearestPeriodIndex
    (c / liRemoteRadialCoordinate a T)
    (liRemoteAngularCoordinate a T)

/-- Card equation (29): the explicit selector satisfies both nearest-target bounds eventually. -/
theorem eventually_liRemotePhaseAlignedDegree_bounds
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    ∀ᶠ i in l,
      |(liRemotePhaseAlignedDegree c (a i) (T i) : ℝ) -
          c / liRemoteRadialCoordinate (a i) (T i)| ≤
          Real.pi / liRemoteAngularCoordinate (a i) (T i) + 1 / 2 ∧
        |(liRemotePhaseAlignedDegree c (a i) (T i) : ℝ) *
              liRemoteAngularCoordinate (a i) (T i) -
            (liRemotePhasePeriodIndex c (a i) (T i) : ℝ) * (2 * Real.pi)| ≤
          liRemoteAngularCoordinate (a i) (T i) / 2 := by
  let ell : ι → ℝ := fun i => liRemoteRadialCoordinate (a i) (T i)
  let theta : ι → ℝ := fun i => liRemoteAngularCoordinate (a i) (T i)
  have hell := tendsto_liRemoteRadialCoordinate_zero hT ha
  have hratio := tendsto_liRemoteRadial_div_angular hT ha
  have hpos := eventually_liRemoteCoordinates_pos hT ha
  have hcast := eventually_cast_liPhaseAlignedDegree hc hell hratio hpos
  filter_upwards [hpos, hcast] with i hi hcasti
  constructor
  · unfold liRemotePhaseAlignedDegree
    rw [hcasti]
    exact abs_liPhaseAlignedIntegerDegree_sub_le hi.2
  · unfold liRemotePhaseAlignedDegree liRemotePhasePeriodIndex
    rw [hcasti]
    exact abs_liPhaseAlignedIntegerDegree_phase_sub_le hi.2

/-- Card equation (30): constructive phase-aligned degrees hit radial target `c`. -/
theorem tendsto_liRemotePhaseAlignedDegree_mul_radial
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i => (liRemotePhaseAlignedDegree c (a i) (T i) : ℝ) *
        liRemoteRadialCoordinate (a i) (T i)) l (nhds c) := by
  exact tendsto_liPhaseAlignedDegree_mul_radial hc
    (tendsto_liRemoteRadialCoordinate_zero hT ha)
    (tendsto_liRemoteRadial_div_angular hT ha)
    (eventually_liRemoteCoordinates_pos hT ha)

/-- Card equation (30): constructive degrees align their angular phase modulo `2π`. -/
theorem tendstoModuloTwoPi_liRemotePhaseAlignedDegree
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    TendstoModuloTwoPi
      (fun i => (liRemotePhaseAlignedDegree c (a i) (T i) : ℝ) *
        liRemoteAngularCoordinate (a i) (T i)) l 0 := by
  exact tendstoModuloTwoPi_liPhaseAlignedDegree hc
    (tendsto_liRemoteRadialCoordinate_zero hT ha)
    (tendsto_liRemoteAngularCoordinate_zero hT ha)
    (tendsto_liRemoteRadial_div_angular hT ha)
    (eventually_liRemoteCoordinates_pos hT ha)

/-- The selected degrees have sharp transverse scale `n a / T² → c`. -/
theorem tendsto_liRemotePhaseAlignedDegreeScale
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i => (liRemotePhaseAlignedDegree c (a i) (T i) : ℝ) *
      a i / T i ^ 2) l (nhds c) := by
  have hnell := tendsto_liRemotePhaseAlignedDegree_mul_radial hc hT ha
  have hrad := tendsto_liRemoteRadialScale hT ha
  have hdiv := hnell.div hrad (by norm_num : (1 : ℝ) ≠ 0)
  have hTpos : ∀ᶠ i in l, 0 < T i := hT.eventually_gt_atTop 0
  have hpos := eventually_liRemoteCoordinates_pos hT ha
  have hdiv' : Tendsto (fun i =>
      (liRemotePhaseAlignedDegree c (a i) (T i) : ℝ) * a i / T i ^ 2)
      l (nhds (c / 1)) := hdiv.congr' (by
        filter_upwards [ha, hTpos, hpos] with i hai hTi hcoord
        have ha0 := ne_of_gt hai.1
        have hT0 := ne_of_gt hTi
        have hell0 := ne_of_gt hcoord.1
        simp only [Pi.div_apply]
        field_simp [ha0, hT0, hell0])
  simpa only [div_one] using hdiv'

/-- Card equation (31): constructive phase alignment gives the strict negative quartet limit. -/
theorem tendsto_liRemotePhaseAlignedQuartetProfile
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i => liRemoteQuartetProfile
        (liRemotePhaseAlignedDegree c (a i) (T i))
        (liRemoteRadialCoordinate (a i) (T i))
        (liRemoteAngularCoordinate (a i) (T i)))
      l (nhds (4 * (1 - Real.cosh c))) := by
  exact tendsto_liPhaseAlignedQuartetProfile hc
    (tendsto_liRemoteRadialCoordinate_zero hT ha)
    (tendsto_liRemoteAngularCoordinate_zero hT ha)
    (tendsto_liRemoteRadial_div_angular hT ha)
    (eventually_liRemoteCoordinates_pos hT ha)

/-- The limiting phase-aligned quartet signal is strictly negative for every `c > 0`. -/
theorem liPhaseAlignedQuartetLimit_neg {c : ℝ} (hc : 0 < c) :
    4 * (1 - Real.cosh c) < 0 := by
  have hcosh : 1 < Real.cosh c := Real.one_lt_cosh.2 (ne_of_gt hc)
  nlinarith

end
end RHTower
