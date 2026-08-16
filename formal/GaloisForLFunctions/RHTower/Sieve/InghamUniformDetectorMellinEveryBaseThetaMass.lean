import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinHoheiselEveryBase
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinQuantitativeThetaMass

open Complex Filter Topology Set Finset
open MeasureTheory ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-- Two-sided increment control for the power-law Route-T detector centers. -/
theorem routeT_physicalCenter_increment_bounds
    {x m : ℝ} (hx : 1 ≤ x) (hm0 : 0 ≤ m) (hmx : m ≤ x) :
    m * x ^ (inghamRouteTPhysicalScaleExponent - 1) ≤
        (x + m) ^ inghamRouteTPhysicalScaleExponent -
          x ^ inghamRouteTPhysicalScaleExponent ∧
      (x + m) ^ inghamRouteTPhysicalScaleExponent -
          x ^ inghamRouteTPhysicalScaleExponent ≤
        15 * m * x ^ (inghamRouteTPhysicalScaleExponent - 1) := by
  let q : ℝ := inghamRouteTPhysicalScaleExponent
  let t : ℝ := m / x
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ t := by
    dsimp only [t]
    positivity
  have ht1 : t ≤ 1 := by
    dsimp only [t]
    exact (div_le_one hx0).2 hmx
  have hbase1 : 1 ≤ 1 + t := by linarith
  have hq1 : 1 ≤ q := by
    dsimp only [q, inghamRouteTPhysicalScaleExponent]
    norm_num
  have hq4 : q ≤ 4 := by
    dsimp only [q, inghamRouteTPhysicalScaleExponent]
    norm_num
  have hpowLower : 1 + t ≤ (1 + t) ^ q := by
    calc
      1 + t = (1 + t) ^ (1 : ℝ) := (Real.rpow_one (1 + t)).symm
      _ ≤ (1 + t) ^ q := Real.rpow_le_rpow_of_exponent_le hbase1 hq1
  have hpowUpper : (1 + t) ^ q ≤ (1 + t) ^ (4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase1 hq4
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hpowUpper
  have ht2 : t ^ 2 ≤ t := by
    have h := pow_le_one₀ ht0 ht1 (n := 1)
    calc
      t ^ 2 = t * t ^ 1 := by ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left h ht0
      _ = t := by ring
  have ht3 : t ^ 3 ≤ t := by
    have h := pow_le_one₀ ht0 ht1 (n := 2)
    calc
      t ^ 3 = t * t ^ 2 := by ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left h ht0
      _ = t := by ring
  have ht4 : t ^ 4 ≤ t := by
    have h := pow_le_one₀ ht0 ht1 (n := 3)
    calc
      t ^ 4 = t * t ^ 3 := by ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left h ht0
      _ = t := by ring
  have hpoly : (1 + t) ^ 4 - 1 ≤ 15 * t := by
    nlinarith
  have hbracketLower : t ≤ (1 + t) ^ q - 1 := by linarith
  have hbracketUpper : (1 + t) ^ q - 1 ≤ 15 * t := by linarith
  have hfactor : x + m = x * (1 + t) := by
    dsimp only [t]
    field_simp
  have hpowFactor : (x + m) ^ q = x ^ q * (1 + t) ^ q := by
    rw [hfactor, Real.mul_rpow hx0.le (by linarith : 0 ≤ 1 + t)]
  have hscale : x ^ q * t = m * x ^ (q - 1) := by
    dsimp only [t]
    rw [Real.rpow_sub hx0, Real.rpow_one]
    field_simp
  change m * x ^ (q - 1) ≤ (x + m) ^ q - x ^ q ∧
    (x + m) ^ q - x ^ q ≤ 15 * m * x ^ (q - 1)
  rw [hpowFactor]
  constructor
  · calc
      m * x ^ (q - 1) = x ^ q * t := hscale.symm
      _ ≤ x ^ q * ((1 + t) ^ q - 1) :=
        mul_le_mul_of_nonneg_left hbracketLower (Real.rpow_nonneg hx0.le _)
      _ = x ^ q * (1 + t) ^ q - x ^ q := by ring
  · calc
      x ^ q * (1 + t) ^ q - x ^ q =
          x ^ q * ((1 + t) ^ q - 1) := by ring
      _ ≤ x ^ q * (15 * t) :=
        mul_le_mul_of_nonneg_left hbracketUpper (Real.rpow_nonneg hx0.le _)
      _ = 15 * (x ^ q * t) := by ring
      _ = 15 * m * x ^ (q - 1) := by rw [hscale]; ring

def routeTDetectorPackingStep (X : ℕ) : ℕ :=
  ⌈16 * (X : ℝ) ^ (1 / 1000 : ℝ)⌉₊

theorem inghamRouteTMellinBufferedPhysicalWidth_eq_index_rpow
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTMellinBufferedPhysicalWidth X =
      (X : ℝ) ^ (701299 / 299000 : ℝ) := by
  rw [inghamRouteTMellinBufferedPhysicalWidth_eq_center_rpow hX]
  unfold inghamRouteTMellinPhysicalCenter
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ X)]
  congr 1
  unfold inghamRouteTPhysicalScaleExponent
  norm_num

theorem routeTDetectorPackingStep_bounds {X : ℕ} (hX : 1 ≤ X) :
    16 * (X : ℝ) ^ (1 / 1000 : ℝ) ≤
        (routeTDetectorPackingStep X : ℝ) ∧
      (routeTDetectorPackingStep X : ℝ) ≤
        17 * (X : ℝ) ^ (1 / 1000 : ℝ) := by
  let u : ℝ := (X : ℝ) ^ (1 / 1000 : ℝ)
  have hXR1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hu1 : 1 ≤ u := by
    dsimp only [u]
    exact Real.one_le_rpow hXR1 (by norm_num)
  have hu0 : 0 ≤ u := zero_le_one.trans hu1
  constructor
  · exact Nat.le_ceil (16 * u)
  · have hceil : (routeTDetectorPackingStep X : ℝ) < 16 * u + 1 := by
      exact Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 16 * u)
    dsimp only [routeTDetectorPackingStep] at hceil ⊢
    linarith

theorem routeT_detectorPacking_center_gap_bounds
    {X Y : ℕ} (hX : 1 ≤ X)
    (hstep : routeTDetectorPackingStep X ≤ X)
    (hXY : X ≤ Y) (hY2 : Y ≤ 2 * X) :
    16 * inghamRouteTMellinBufferedPhysicalWidth X ≤
        inghamRouteTMellinPhysicalCenter (Y + routeTDetectorPackingStep X) -
          inghamRouteTMellinPhysicalCenter Y ∧
      inghamRouteTMellinPhysicalCenter (Y + routeTDetectorPackingStep X) -
          inghamRouteTMellinPhysicalCenter Y ≤
        2040 * inghamRouteTMellinBufferedPhysicalWidth X := by
  let x : ℝ := X
  let y : ℝ := Y
  let m : ℝ := routeTDetectorPackingStep X
  let q : ℝ := inghamRouteTPhysicalScaleExponent
  let d : ℝ := 1 / 1000
  let e : ℝ := q - 1
  let b : ℝ := 701299 / 299000
  have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast hX
  have hx0 : 0 < x := by linarith
  have hy1 : 1 ≤ y := by
    dsimp only [y]
    exact_mod_cast hX.trans hXY
  have hy0 : 0 < y := by linarith
  have hm0 : 0 ≤ m := by positivity
  have hmY : m ≤ y := by
    dsimp only [m, y]
    exact_mod_cast hstep.trans hXY
  have hinc := routeT_physicalCenter_increment_bounds hy1 hm0 hmY
  have hinc' :
      m * y ^ e ≤
          inghamRouteTMellinPhysicalCenter (Y + routeTDetectorPackingStep X) -
            inghamRouteTMellinPhysicalCenter Y ∧
        inghamRouteTMellinPhysicalCenter (Y + routeTDetectorPackingStep X) -
            inghamRouteTMellinPhysicalCenter Y ≤ 15 * m * y ^ e := by
    simpa only [inghamRouteTMellinPhysicalCenter, Nat.cast_add, q, e, y, m] using hinc
  have hstepBounds := routeTDetectorPackingStep_bounds hX
  have hmLower : 16 * x ^ d ≤ m := by
    simpa only [x, m, d] using hstepBounds.1
  have hmUpper : m ≤ 17 * x ^ d := by
    simpa only [x, m, d] using hstepBounds.2
  have he0 : 0 ≤ e := by
    dsimp only [e, q, inghamRouteTPhysicalScaleExponent]
    norm_num
  have he3 : e ≤ 3 := by
    dsimp only [e, q, inghamRouteTPhysicalScaleExponent]
    norm_num
  have hxy : x ≤ y := by dsimp only [x, y]; exact_mod_cast hXY
  have hy2x : y ≤ 2 * x := by
    dsimp only [x, y]
    exact_mod_cast hY2
  have hpowLower : x ^ e ≤ y ^ e :=
    Real.rpow_le_rpow hx0.le hxy he0
  have hpowUpper : y ^ e ≤ (2 * x) ^ e :=
    Real.rpow_le_rpow hy0.le hy2x he0
  have htwoPow : (2 : ℝ) ^ e ≤ 8 := by
    calc
      (2 : ℝ) ^ e ≤ (2 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) he3
      _ = 8 := by norm_num
  have hpowerExact : x ^ d * x ^ e = x ^ b := by
    rw [← Real.rpow_add hx0]
    congr 1
    dsimp only [d, e, q, b, inghamRouteTPhysicalScaleExponent]
    norm_num
  have hwidthExact : inghamRouteTMellinBufferedPhysicalWidth X = x ^ b := by
    simpa only [x, b] using
      (inghamRouteTMellinBufferedPhysicalWidth_eq_index_rpow hX)
  constructor
  · rw [hwidthExact]
    calc
      16 * x ^ b = (16 * x ^ d) * x ^ e := by rw [← hpowerExact]; ring
      _ ≤ m * y ^ e := by
        exact mul_le_mul hmLower hpowLower (Real.rpow_nonneg hx0.le _) hm0
      _ ≤ inghamRouteTMellinPhysicalCenter (Y + routeTDetectorPackingStep X) -
          inghamRouteTMellinPhysicalCenter Y := hinc'.1
  · rw [hwidthExact]
    calc
      inghamRouteTMellinPhysicalCenter (Y + routeTDetectorPackingStep X) -
          inghamRouteTMellinPhysicalCenter Y ≤ 15 * m * y ^ e := hinc'.2
      _ ≤ 15 * (17 * x ^ d) * (2 * x) ^ e := by gcongr
      _ = 255 * x ^ d * ((2 : ℝ) ^ e * x ^ e) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0.le]
        ring
      _ ≤ 255 * x ^ d * (8 * x ^ e) := by gcongr
      _ = 2040 * x ^ b := by rw [← hpowerExact]; ring

theorem routeT_detectorPacking_bufferedWidth_bounds
    {X Y : ℕ} (hX : 1 ≤ X) (hXY : X ≤ Y) (hY2 : Y ≤ 2 * X) :
    inghamRouteTMellinBufferedPhysicalWidth X ≤
        inghamRouteTMellinBufferedPhysicalWidth Y ∧
      inghamRouteTMellinBufferedPhysicalWidth Y ≤
        8 * inghamRouteTMellinBufferedPhysicalWidth X := by
  let x : ℝ := X
  let y : ℝ := Y
  let b : ℝ := 701299 / 299000
  have hx0 : 0 < x := by
    dsimp only [x]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hy1 : 1 ≤ Y := hX.trans hXY
  have hy0 : 0 < y := by
    dsimp only [y]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hy1)
  have hxy : x ≤ y := by dsimp only [x, y]; exact_mod_cast hXY
  have hy2x : y ≤ 2 * x := by dsimp only [x, y]; exact_mod_cast hY2
  have hb0 : 0 ≤ b := by dsimp only [b]; norm_num
  have hb3 : b ≤ 3 := by dsimp only [b]; norm_num
  have hmono : x ^ b ≤ y ^ b := Real.rpow_le_rpow hx0.le hxy hb0
  have hupper : y ^ b ≤ (2 * x) ^ b := Real.rpow_le_rpow hy0.le hy2x hb0
  have htwoPow : (2 : ℝ) ^ b ≤ 8 := by
    calc
      (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hb3
      _ = 8 := by norm_num
  have hXwidth : inghamRouteTMellinBufferedPhysicalWidth X = x ^ b := by
    simpa only [x, b] using
      (inghamRouteTMellinBufferedPhysicalWidth_eq_index_rpow hX)
  have hYwidth : inghamRouteTMellinBufferedPhysicalWidth Y = y ^ b := by
    simpa only [y, b] using
      (inghamRouteTMellinBufferedPhysicalWidth_eq_index_rpow hy1)
  rw [hXwidth, hYwidth]
  refine ⟨hmono, hupper.trans ?_⟩
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0.le]
  exact mul_le_mul_of_nonneg_right htwoPow (Real.rpow_nonneg hx0.le _)

theorem routeT_detectorPacking_windows_disjoint
    {X Y : ℕ} (hX : 1 ≤ X)
    (hstep : routeTDetectorPackingStep X ≤ X)
    (hXY : X ≤ Y) (hY2 : Y ≤ 2 * X) :
    inghamRouteTMellinPhysicalCenter Y +
        2 * inghamRouteTMellinBufferedPhysicalWidth Y ≤
      inghamRouteTMellinPhysicalCenter (Y + routeTDetectorPackingStep X) := by
  have hgap :=
    (routeT_detectorPacking_center_gap_bounds hX hstep hXY hY2).1
  have hwidth :=
    (routeT_detectorPacking_bufferedWidth_bounds hX hXY hY2).2
  linarith

theorem routeT_detectorPacking_step_reach_le
    {X Y : ℕ} (hX : 1 ≤ X)
    (hstep : routeTDetectorPackingStep X ≤ X)
    (hXY : X ≤ Y) (hYstep2 : Y + routeTDetectorPackingStep X ≤ 2 * X) :
    inghamRouteTMellinPhysicalCenter (Y + routeTDetectorPackingStep X) +
          2 * inghamRouteTMellinBufferedPhysicalWidth
            (Y + routeTDetectorPackingStep X) -
        inghamRouteTMellinPhysicalCenter Y ≤
      2056 * inghamRouteTMellinBufferedPhysicalWidth X := by
  have hY2 : Y ≤ 2 * X := le_trans (Nat.le_add_right _ _) hYstep2
  have hgap :=
    (routeT_detectorPacking_center_gap_bounds hX hstep hXY hY2).2
  have hXYstep : X ≤ Y + routeTDetectorPackingStep X :=
    hXY.trans (Nat.le_add_right _ _)
  have hwidth :=
    (routeT_detectorPacking_bufferedWidth_bounds hX hXYstep hYstep2).2
  linarith

theorem eventually_routeTDetectorPackingStep_le_self :
    ∀ᶠ X : ℕ in atTop, routeTDetectorPackingStep X ≤ X := by
  have hgrow : Tendsto (fun X : ℕ => (X : ℝ) ^ (999 / 1000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 999 / 1000)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hgrow.eventually_ge_atTop 17,
      eventually_ge_atTop (1 : ℕ)] with X hlarge hX
  have hx0 : (0 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hstepUpper := (routeTDetectorPackingStep_bounds hX).2
  have hpower :
      17 * (X : ℝ) ^ (1 / 1000 : ℝ) ≤ (X : ℝ) := by
    calc
      17 * (X : ℝ) ^ (1 / 1000 : ℝ) ≤
          (X : ℝ) ^ (999 / 1000 : ℝ) *
            (X : ℝ) ^ (1 / 1000 : ℝ) := by gcongr
      _ = (X : ℝ) := by
        rw [← Real.rpow_add hx0, show (999 / 1000 : ℝ) + 1 / 1000 = 1 by norm_num,
          Real.rpow_one]
  exact_mod_cast hstepUpper.trans hpower

/-- Ordered disjoint windows inject their total increment into the enclosing monotone increment. -/
theorem sum_range_window_diff_le_of_monotone
    {f : ℝ → ℝ} (hf : Monotone f) {a b : ℕ → ℝ} (K : ℕ)
    (hsep : ∀ i < K, b i ≤ a (i + 1)) :
    ∑ i ∈ Finset.range (K + 1), (f (b i) - f (a i)) ≤
      f (b K) - f (a 0) := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hsepPrev : ∀ i < K, b i ≤ a (i + 1) := by
        intro i hi
        exact hsep i (hi.trans (Nat.lt_succ_self K))
      have hih := ih hsepPrev
      have hbridge : f (b K) ≤ f (a (K + 1)) :=
        hf (hsep K (Nat.lt_succ_self K))
      rw [show K + 1 + 1 = (K + 1) + 1 by omega, Finset.sum_range_succ]
      linarith

/-- Sparse quantitative detector windows have a positive aggregate theta density on every
index block that remains in one dyadic index shell. -/
theorem eventually_routeT_detectorPacking_block_theta_mass :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ,
      X + K * routeTDetectorPackingStep X ≤ 2 * X →
      (((K + 1 : ℕ) : ℝ) / 4) *
          inghamRouteTMellinBufferedPhysicalWidth X <
        Chebyshev.theta
            (inghamRouteTMellinPhysicalCenter
                (X + K * routeTDetectorPackingStep X) +
              2 * inghamRouteTMellinBufferedPhysicalWidth
                (X + K * routeTDetectorPackingStep X)) -
          Chebyshev.theta (inghamRouteTMellinPhysicalCenter X) := by
  rcases (eventually_atTop.1
    eventually_inghamRouteTBuffered_theta_window_gt_quarter_width) with ⟨Q, hQ⟩
  filter_upwards [eventually_routeTDetectorPackingStep_le_self,
      eventually_ge_atTop (max 1 Q)] with X hstep hX
  intro K hblock
  classical
  let S : ℕ := routeTDetectorPackingStep X
  let Y : ℕ → ℕ := fun i => X + i * S
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hQX : Q ≤ X := le_trans (le_max_right _ _) hX
  have hYbounds : ∀ i ∈ Finset.range (K + 1), X ≤ Y i ∧ Y i ≤ 2 * X := by
    intro i hi
    have hiK : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have himul : i * S ≤ K * S := Nat.mul_le_mul_right S hiK
    constructor
    · dsimp only [Y]
      exact Nat.le_add_right _ _
    · dsimp only [Y]
      exact (Nat.add_le_add_left himul X).trans (by simpa only [S] using hblock)
  have hlocal : ∀ i ∈ Finset.range (K + 1),
      inghamRouteTMellinBufferedPhysicalWidth (Y i) / 4 <
        Chebyshev.theta
            (inghamRouteTMellinPhysicalCenter (Y i) +
              2 * inghamRouteTMellinBufferedPhysicalWidth (Y i)) -
          Chebyshev.theta (inghamRouteTMellinPhysicalCenter (Y i)) := by
    intro i hi
    apply hQ (Y i)
    exact hQX.trans (hYbounds i hi).1
  have hwidthLower : ∀ i ∈ Finset.range (K + 1),
      inghamRouteTMellinBufferedPhysicalWidth X ≤
        inghamRouteTMellinBufferedPhysicalWidth (Y i) := by
    intro i hi
    exact (routeT_detectorPacking_bufferedWidth_bounds hX1
      (hYbounds i hi).1 (hYbounds i hi).2).1
  have hterm : ∀ i ∈ Finset.range (K + 1),
      inghamRouteTMellinBufferedPhysicalWidth X / 4 <
        Chebyshev.theta
            (inghamRouteTMellinPhysicalCenter (Y i) +
              2 * inghamRouteTMellinBufferedPhysicalWidth (Y i)) -
          Chebyshev.theta (inghamRouteTMellinPhysicalCenter (Y i)) := by
    intro i hi
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (hwidthLower i hi) (by norm_num))
      (hlocal i hi)
  have hsumLower :
      (((K + 1 : ℕ) : ℝ) / 4) *
          inghamRouteTMellinBufferedPhysicalWidth X <
        ∑ i ∈ Finset.range (K + 1),
          (Chebyshev.theta
              (inghamRouteTMellinPhysicalCenter (Y i) +
                2 * inghamRouteTMellinBufferedPhysicalWidth (Y i)) -
            Chebyshev.theta (inghamRouteTMellinPhysicalCenter (Y i))) := by
    have hsum := Finset.sum_lt_sum_of_nonempty
      (Finset.nonempty_range_iff.mpr (by omega : K + 1 ≠ 0)) hterm
    have hleft :
        (((K + 1 : ℕ) : ℝ) / 4) *
            inghamRouteTMellinBufferedPhysicalWidth X =
          ∑ _i ∈ Finset.range (K + 1),
            inghamRouteTMellinBufferedPhysicalWidth X / 4 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [hleft]
    exact hsum
  have hsep : ∀ i < K,
      inghamRouteTMellinPhysicalCenter (Y i) +
          2 * inghamRouteTMellinBufferedPhysicalWidth (Y i) ≤
        inghamRouteTMellinPhysicalCenter (Y (i + 1)) := by
    intro i hi
    have hiRange : i ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
    have hgeom := routeT_detectorPacking_windows_disjoint hX1
      (by simpa only [S] using hstep) (hYbounds i hiRange).1 (hYbounds i hiRange).2
    simpa only [Y, S, Nat.succ_mul, Nat.add_assoc] using hgeom
  have hsumUpper := sum_range_window_diff_le_of_monotone Chebyshev.theta_mono
    (a := fun i => inghamRouteTMellinPhysicalCenter (Y i))
    (b := fun i => inghamRouteTMellinPhysicalCenter (Y i) +
      2 * inghamRouteTMellinBufferedPhysicalWidth (Y i)) K hsep
  exact hsumLower.trans_le (by
    simpa only [Y, S, Nat.zero_mul, Nat.add_zero] using hsumUpper)

/-- A `K`-window sparse detector block occupies at most a fixed multiple of `K` base widths. -/
theorem routeT_detectorPacking_block_reach_le
    {X K : ℕ} (hX : 1 ≤ X)
    (hblock : X + K * routeTDetectorPackingStep X ≤ 2 * X) :
    inghamRouteTMellinPhysicalCenter
          (X + K * routeTDetectorPackingStep X) +
        2 * inghamRouteTMellinBufferedPhysicalWidth
          (X + K * routeTDetectorPackingStep X) -
        inghamRouteTMellinPhysicalCenter X ≤
      (255 * (K : ℝ) + 16) *
        inghamRouteTMellinBufferedPhysicalWidth X := by
  let x : ℝ := X
  let m : ℝ := K * routeTDetectorPackingStep X
  let q : ℝ := inghamRouteTPhysicalScaleExponent
  let d : ℝ := 1 / 1000
  let e : ℝ := q - 1
  let b : ℝ := 701299 / 299000
  have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast hX
  have hx0 : 0 < x := by linarith
  have hm0 : 0 ≤ m := by positivity
  have hmX : m ≤ x := by
    dsimp only [m, x]
    have hblock' : X + K * routeTDetectorPackingStep X ≤ X + X := by
      simpa only [two_mul] using hblock
    exact_mod_cast (Nat.le_of_add_le_add_left hblock')
  have hinc := (routeT_physicalCenter_increment_bounds hx1 hm0 hmX).2
  have hinc' :
      inghamRouteTMellinPhysicalCenter
            (X + K * routeTDetectorPackingStep X) -
          inghamRouteTMellinPhysicalCenter X ≤
        15 * m * x ^ e := by
    simpa only [inghamRouteTMellinPhysicalCenter, Nat.cast_add, Nat.cast_mul,
      q, e, m, x] using hinc
  have hstepUpper :
      (routeTDetectorPackingStep X : ℝ) ≤ 17 * x ^ d := by
    simpa only [x, d] using (routeTDetectorPackingStep_bounds hX).2
  have hmUpper : m ≤ (K : ℝ) * (17 * x ^ d) := by
    dsimp only [m]
    exact mul_le_mul_of_nonneg_left hstepUpper (Nat.cast_nonneg K)
  have hpowerExact : x ^ d * x ^ e = x ^ b := by
    rw [← Real.rpow_add hx0]
    congr 1
    dsimp only [d, e, q, b, inghamRouteTPhysicalScaleExponent]
    norm_num
  have hcenter :
      inghamRouteTMellinPhysicalCenter
            (X + K * routeTDetectorPackingStep X) -
          inghamRouteTMellinPhysicalCenter X ≤
        255 * (K : ℝ) * x ^ b := by
    calc
      inghamRouteTMellinPhysicalCenter
            (X + K * routeTDetectorPackingStep X) -
          inghamRouteTMellinPhysicalCenter X ≤ 15 * m * x ^ e := hinc'
      _ ≤ 15 * ((K : ℝ) * (17 * x ^ d)) * x ^ e := by gcongr
      _ = 255 * (K : ℝ) * x ^ b := by rw [← hpowerExact]; ring
  have hindexLower : X ≤ X + K * routeTDetectorPackingStep X :=
    Nat.le_add_right _ _
  have hwidth := (routeT_detectorPacking_bufferedWidth_bounds hX hindexLower hblock).2
  have hwidthExact : inghamRouteTMellinBufferedPhysicalWidth X = x ^ b := by
    simpa only [x, b] using
      (inghamRouteTMellinBufferedPhysicalWidth_eq_index_rpow hX)
  rw [hwidthExact] at hwidth ⊢
  linarith

/-- Any exponent strictly above the buffered detector exponent carries a fixed proportional
theta mass at every sufficiently large real base.  The proof packs disjoint detector windows;
it does not invoke a short-interval PNT. -/
theorem eventually_routeT_detectorPacking_theta_mass_every_base
    {alpha : ℝ}
    (halpha : (701299 / 1000000 : ℝ) < alpha)
    (halpha1 : alpha < 1) :
    ∀ᶠ z : ℝ in atTop,
      z ^ alpha / 16384 <
        Chebyshev.theta (z + z ^ alpha / 2) - Chebyshev.theta z := by
  rcases (eventually_atTop.1
    eventually_routeT_detectorPacking_block_theta_mass) with ⟨M0, hM0⟩
  let M : ℕ := max 1 M0
  let q : ℝ := inghamRouteTPhysicalScaleExponent
  let r : ℝ := 299 / 1000
  let beta : ℝ := 701299 / 1000000
  let b : ℝ := 701299 / 299000
  let d : ℝ := 1 / 1000
  let e : ℝ := q - 1
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0M : M0 ≤ M := le_max_right _ _
  have hq0 : 0 < q := inghamRouteTPhysicalScaleExponent_pos
  have hr0 : 0 < r := by dsimp only [r]; norm_num
  have hbeta0 : 0 < beta := by dsimp only [beta]; norm_num
  have halpha0 : 0 < alpha := hbeta0.trans halpha
  have hdiff : 0 < alpha - beta := by dsimp only [beta] at halpha ⊢; linarith
  have hgrow : Tendsto (fun z : ℝ => z ^ (alpha - beta)) atTop atTop :=
    tendsto_rpow_atTop hdiff
  have hMpower1 : (1 : ℝ) ≤ (M : ℝ) ^ q :=
    Real.one_le_rpow (by exact_mod_cast hM1) hq0.le
  filter_upwards [hgrow.eventually_ge_atTop 2048,
      eventually_ge_atTop ((M : ℝ) ^ q)] with z hlarge hzM
  have hz1 : 1 ≤ z := hMpower1.trans hzM
  have hz0 : 0 < z := by linarith
  let u : ℝ := z ^ r
  let X : ℕ := ⌊u⌋₊
  let B : ℕ := X + 1
  have hMroot : ((M : ℝ) ^ q) ^ r = (M : ℝ) := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (M : ℝ))]
    have hqr : q * r = 1 := by
      dsimp only [q, r, inghamRouteTPhysicalScaleExponent]
      norm_num
    rw [hqr, Real.rpow_one]
  have hMu : (M : ℝ) ≤ u := by
    have hpow := Real.rpow_le_rpow
      (Real.rpow_nonneg (by positivity) q) hzM hr0.le
    rw [hMroot] at hpow
    exact hpow
  have hMX : M ≤ X := by
    dsimp only [X]
    exact Nat.le_floor hMu
  have hX1 : 1 ≤ X := hM1.trans hMX
  have hB1 : 1 ≤ B := by dsimp only [B]; omega
  have hM0B : M0 ≤ B := hM0M.trans (hMX.trans (by dsimp only [B]; omega))
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hu1 : 1 ≤ u := by
    dsimp only [u]
    exact Real.one_le_rpow hz1 hr0.le
  have hXu : (X : ℝ) ≤ u := by
    dsimp only [X]
    exact Nat.floor_le hu0
  have huB : u < (B : ℝ) := by
    dsimp only [B, X]
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one u
  have hB2u : (B : ℝ) ≤ 2 * u := by
    have hBupper : (B : ℝ) ≤ u + 1 := by
      dsimp only [B]
      push_cast
      linarith
    linarith
  have huq : u ^ q = z := by
    dsimp only [u]
    rw [← Real.rpow_mul hz0.le]
    have hrq : r * q = 1 := by
      dsimp only [q, r, inghamRouteTPhysicalScaleExponent]
      norm_num
    rw [hrq, Real.rpow_one]
  have hcenterX : inghamRouteTMellinPhysicalCenter X ≤ z := by
    unfold inghamRouteTMellinPhysicalCenter
    have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (X : ℝ)) hXu hq0.le
    rwa [huq] at hpow
  have hzCenterB : z < inghamRouteTMellinPhysicalCenter B := by
    unfold inghamRouteTMellinPhysicalCenter
    have hpow := Real.rpow_lt_rpow hu0 huB hq0
    rwa [huq] at hpow
  have hb0 : 0 ≤ b := by dsimp only [b]; norm_num
  have hb3 : b ≤ 3 := by dsimp only [b]; norm_num
  have hwidthExact : inghamRouteTMellinBufferedPhysicalWidth B = (B : ℝ) ^ b := by
    simpa only [b] using
      (inghamRouteTMellinBufferedPhysicalWidth_eq_index_rpow hB1)
  have hwidthPos : 0 < inghamRouteTMellinBufferedPhysicalWidth B :=
    inghamRouteTMellinBufferedPhysicalWidth_pos hB1
  have htwoPow : (2 : ℝ) ^ b ≤ 8 := by
    calc
      (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hb3
      _ = 8 := by norm_num
  have huPow : u ^ b = z ^ beta := by
    dsimp only [u]
    rw [← Real.rpow_mul hz0.le]
    congr 1
    dsimp only [r, b, beta]
    norm_num
  have hwidthCoarse :
      inghamRouteTMellinBufferedPhysicalWidth B ≤ 8 * z ^ beta := by
    rw [hwidthExact]
    calc
      (B : ℝ) ^ b ≤ (2 * u) ^ b :=
        Real.rpow_le_rpow (by positivity) hB2u hb0
      _ = (2 : ℝ) ^ b * u ^ b := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hu0]
      _ ≤ 8 * u ^ b :=
        mul_le_mul_of_nonneg_right htwoPow (Real.rpow_nonneg hu0 _)
      _ = 8 * z ^ beta := by rw [huPow]
  have hsplit : z ^ beta * z ^ (alpha - beta) = z ^ alpha := by
    rw [← Real.rpow_add hz0]
    congr 1
    ring
  have hwidthSmall :
      inghamRouteTMellinBufferedPhysicalWidth B ≤ z ^ alpha / 256 := by
    calc
      inghamRouteTMellinBufferedPhysicalWidth B ≤ 8 * z ^ beta := hwidthCoarse
      _ ≤ z ^ alpha / 256 := by
        rw [← hsplit]
        have hzbeta0 : 0 ≤ z ^ beta := Real.rpow_nonneg hz0.le _
        nlinarith [mul_le_mul_of_nonneg_left hlarge hzbeta0]
  have he0 : 0 ≤ e := by
    dsimp only [e, q, inghamRouteTPhysicalScaleExponent]
    norm_num
  have heb : e ≤ b := by
    dsimp only [e, q, b, inghamRouteTPhysicalScaleExponent]
    norm_num
  have hgapXB := inghamRouteTMellinPhysicalCenter_succ_sub_le hX1
  have hXBpow : (X : ℝ) ^ e ≤ (B : ℝ) ^ e := by
    apply Real.rpow_le_rpow (by positivity) _ he0
    dsimp only [B]
    push_cast
    linarith
  have hBpow : (B : ℝ) ^ e ≤ (B : ℝ) ^ b := by
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB1) heb
  have hinitial :
      inghamRouteTMellinPhysicalCenter B - z ≤
        15 * inghamRouteTMellinBufferedPhysicalWidth B := by
    calc
      inghamRouteTMellinPhysicalCenter B - z ≤
          inghamRouteTMellinPhysicalCenter B -
            inghamRouteTMellinPhysicalCenter X := by linarith
      _ ≤ 15 * (X : ℝ) ^ e := by
        simpa only [B, e] using hgapXB
      _ ≤ 15 * (B : ℝ) ^ e := by gcongr
      _ ≤ 15 * (B : ℝ) ^ b := by gcongr
      _ = 15 * inghamRouteTMellinBufferedPhysicalWidth B := by rw [hwidthExact]
  let v : ℝ := z ^ alpha /
    (4096 * inghamRouteTMellinBufferedPhysicalWidth B)
  let K : ℕ := ⌊v⌋₊
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have hKv : (K : ℝ) ≤ v := by
    dsimp only [K]
    exact Nat.floor_le hv0
  have hvK : v < (K : ℝ) + 1 := by
    dsimp only [K]
    exact Nat.lt_floor_add_one v
  have hstepUpper := (routeTDetectorPackingStep_bounds hB1).2
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB1)
  have hd0 : 0 ≤ d := by dsimp only [d]; norm_num
  have hfactorWidth : (B : ℝ) ^ b = (B : ℝ) ^ d * (B : ℝ) ^ e := by
    rw [← Real.rpow_add hB0]
    congr 1
    dsimp only [b, d, e, q, inghamRouteTPhysicalScaleExponent]
    norm_num
  have hfactorCenter : inghamRouteTMellinPhysicalCenter B =
      (B : ℝ) ^ e * (B : ℝ) := by
    unfold inghamRouteTMellinPhysicalCenter
    calc
      (B : ℝ) ^ inghamRouteTPhysicalScaleExponent =
          (B : ℝ) ^ (e + 1) := by
            congr 1
            dsimp only [e, q]
            ring
      _ = (B : ℝ) ^ e * (B : ℝ) ^ (1 : ℝ) := Real.rpow_add hB0 e 1
      _ = (B : ℝ) ^ e * (B : ℝ) := by rw [Real.rpow_one]
  have hzalphaLe : z ^ alpha ≤ z := by
    have := Real.rpow_le_rpow_of_exponent_le hz1 halpha1.le
    simpa only [Real.rpow_one] using this
  have hzalphaCenter : z ^ alpha ≤
      (B : ℝ) ^ e * (B : ℝ) :=
    hzalphaLe.trans (hzCenterB.le.trans_eq hfactorCenter)
  have hratioLe : z ^ alpha / (B : ℝ) ^ e ≤ (B : ℝ) := by
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hB0 e)).2
      (by simpa only [mul_comm] using hzalphaCenter)
  have hKSreal :
      ((K * routeTDetectorPackingStep B : ℕ) : ℝ) ≤ (B : ℝ) := by
    have hmul : (K : ℝ) * (routeTDetectorPackingStep B : ℝ) ≤
        v * (17 * (B : ℝ) ^ d) :=
      mul_le_mul hKv (by simpa only [d] using hstepUpper)
        (Nat.cast_nonneg _) hv0
    calc
      ((K * routeTDetectorPackingStep B : ℕ) : ℝ) =
          (K : ℝ) * (routeTDetectorPackingStep B : ℝ) := by push_cast; ring
      _ ≤ v * (17 * (B : ℝ) ^ d) := hmul
      _ = (17 / 4096) * (z ^ alpha / (B : ℝ) ^ e) := by
        dsimp only [v]
        rw [hwidthExact, hfactorWidth]
        field_simp
      _ ≤ (17 / 4096) * (B : ℝ) := by gcongr
      _ ≤ (B : ℝ) := by nlinarith
  have hKS : K * routeTDetectorPackingStep B ≤ B := by exact_mod_cast hKSreal
  have hblock : B + K * routeTDetectorPackingStep B ≤ 2 * B := by
    rw [two_mul]
    exact Nat.add_le_add_left hKS B
  have hblockMass := hM0 B hM0B K hblock
  have hreach := routeT_detectorPacking_block_reach_le hB1 hblock
  let E : ℝ :=
    inghamRouteTMellinPhysicalCenter
        (B + K * routeTDetectorPackingStep B) +
      2 * inghamRouteTMellinBufferedPhysicalWidth
        (B + K * routeTDetectorPackingStep B)
  have hKW : (K : ℝ) * inghamRouteTMellinBufferedPhysicalWidth B ≤
      z ^ alpha / 4096 := by
    calc
      (K : ℝ) * inghamRouteTMellinBufferedPhysicalWidth B ≤
          v * inghamRouteTMellinBufferedPhysicalWidth B := by gcongr
      _ = z ^ alpha / 4096 := by
        dsimp only [v]
        field_simp
  have hreachSmall : E - inghamRouteTMellinPhysicalCenter B ≤
      (511 / 4096 : ℝ) * z ^ alpha := by
    dsimp only [E]
    calc
      inghamRouteTMellinPhysicalCenter
            (B + K * routeTDetectorPackingStep B) +
          2 * inghamRouteTMellinBufferedPhysicalWidth
            (B + K * routeTDetectorPackingStep B) -
          inghamRouteTMellinPhysicalCenter B ≤
        (255 * (K : ℝ) + 16) *
          inghamRouteTMellinBufferedPhysicalWidth B := hreach
      _ = 255 * ((K : ℝ) * inghamRouteTMellinBufferedPhysicalWidth B) +
          16 * inghamRouteTMellinBufferedPhysicalWidth B := by ring
      _ ≤ 255 * (z ^ alpha / 4096) + 16 * (z ^ alpha / 256) := by gcongr
      _ = (511 / 4096 : ℝ) * z ^ alpha := by ring
  have hEupper : E ≤ z + z ^ alpha / 2 := by
    have hpow0 : 0 ≤ z ^ alpha := Real.rpow_nonneg hz0.le _
    have hinitSmall :
        inghamRouteTMellinPhysicalCenter B - z ≤
          (15 / 256 : ℝ) * z ^ alpha := by
      calc
        inghamRouteTMellinPhysicalCenter B - z ≤
            15 * inghamRouteTMellinBufferedPhysicalWidth B := hinitial
        _ ≤ 15 * (z ^ alpha / 256) := by gcongr
        _ = (15 / 256 : ℝ) * z ^ alpha := by ring
    linarith
  have hlowerScale : z ^ alpha / 16384 <
      (((K + 1 : ℕ) : ℝ) / 4) *
        inghamRouteTMellinBufferedPhysicalWidth B := by
    have hmul := mul_lt_mul_of_pos_right hvK
      (div_pos hwidthPos (by norm_num : (0 : ℝ) < 4))
    dsimp only [v] at hmul
    calc
      z ^ alpha / 16384 =
          (z ^ alpha / (4096 * inghamRouteTMellinBufferedPhysicalWidth B)) *
            (inghamRouteTMellinBufferedPhysicalWidth B / 4) := by
              field_simp [ne_of_gt hwidthPos]
              norm_num
      _ < ((K : ℝ) + 1) *
          (inghamRouteTMellinBufferedPhysicalWidth B / 4) := hmul
      _ = (((K + 1 : ℕ) : ℝ) / 4) *
          inghamRouteTMellinBufferedPhysicalWidth B := by push_cast; ring
  have hthetaBlock : z ^ alpha / 16384 <
      Chebyshev.theta E - Chebyshev.theta
        (inghamRouteTMellinPhysicalCenter B) := by
    exact hlowerScale.trans (by simpa only [E] using hblockMass)
  have hleftMono := Chebyshev.theta_mono hzCenterB.le
  have hrightMono := Chebyshev.theta_mono hEupper
  linarith

theorem routeTBufferedDetectorPhysicalExponent_lt_handoff :
    (701299 / 1000000 : ℝ) < routeTPhysicalSliceHandoffTheta := by
  have hbetaHoheisel :
      (701299 / 1000000 : ℝ) < routeTHoheiselEveryBaseExponent := by
    unfold routeTHoheiselEveryBaseExponent
    norm_num
  exact hbetaHoheisel.trans routeTHoheiselEveryBaseExponent_lt_handoff

/-- Every handoff-scale central half-window carries proportional prime logarithmic mass. -/
theorem eventually_routeT_handoff_central_theta_mass :
    ∀ᶠ N : ℝ in atTop,
      N ^ routeTPhysicalSliceHandoffTheta / 16384 <
        Chebyshev.theta
            (N + 3 * N ^ routeTPhysicalSliceHandoffTheta / 2) -
          Chebyshev.theta
            (N + N ^ routeTPhysicalSliceHandoffTheta / 2) := by
  have htheta := eventually_routeT_detectorPacking_theta_mass_every_base
    routeTBufferedDetectorPhysicalExponent_lt_handoff
    (routeTPhysicalSliceHandoffTheta_lt_three_fourths.trans (by norm_num))
  rcases eventually_atTop.1 htheta with ⟨Q, hQ⟩
  filter_upwards [eventually_ge_atTop (max 1 Q)] with N hN
  let theta : ℝ := routeTPhysicalSliceHandoffTheta
  let R : ℝ := N ^ theta
  let z : ℝ := N + R / 2
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hQN : Q ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := by linarith
  have htheta0 : 0 ≤ theta := by
    dsimp only [theta]
    exact routeTPhysicalSliceHandoffTheta_pos.le
  have htheta1 : theta ≤ 1 := by
    dsimp only [theta]
    exact (routeTPhysicalSliceHandoffTheta_lt_three_fourths.trans (by norm_num)).le
  have hR0 : 0 < R := by dsimp only [R]; positivity
  have hRN : R ≤ N := by
    dsimp only [R]
    have hpow := Real.rpow_le_rpow_of_exponent_le hN1 htheta1
    simpa only [Real.rpow_one] using hpow
  have hNz : N ≤ z := by dsimp only [z]; linarith
  have hz0 : 0 < z := hN0.trans_le hNz
  have hz2N : z ≤ 2 * N := by dsimp only [z]; linarith
  have htwoPow : (2 : ℝ) ^ theta ≤ 2 := by
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) htheta1
    simpa only [Real.rpow_one] using hpow
  have hzPow : z ^ theta ≤ 2 * R := by
    calc
      z ^ theta ≤ (2 * N) ^ theta :=
        Real.rpow_le_rpow hz0.le hz2N htheta0
      _ = (2 : ℝ) ^ theta * N ^ theta := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hN0.le]
      _ ≤ 2 * N ^ theta :=
        mul_le_mul_of_nonneg_right htwoPow (Real.rpow_nonneg hN0.le _)
      _ = 2 * R := by rfl
  have hzQ : Q ≤ z := hQN.trans hNz
  have hlocal := hQ z hzQ
  have hendpoint : z + z ^ theta / 2 ≤ N + 3 * R / 2 := by
    dsimp only [z]
    linarith
  have hright := Chebyshev.theta_mono hendpoint
  have hscale : R / 16384 ≤ z ^ theta / 16384 := by
    gcongr
    exact Real.rpow_le_rpow hN0.le hNz htheta0
  dsimp only [theta, R, z] at hlocal hright hscale ⊢
  linarith

/-- Every handoff reference has a fixed, corpus-generated smooth von Mangoldt mass floor. -/
theorem eventually_routeT_handoff_reference_smooth_vonMangoldt_mass_lower :
    ∀ᶠ N : ℝ in atTop,
      routeTSmoothWindowCentralMargin *
          (N ^ routeTPhysicalSliceHandoffTheta / 16384) <
        ∑' n : ℕ, (vonMangoldt n : ℝ) *
          routeTSmoothWindowWeight N
            (N ^ routeTPhysicalSliceHandoffTheta) n := by
  filter_upwards [eventually_routeT_handoff_central_theta_mass,
      eventually_ge_atTop (1 : ℝ)] with N htheta hN
  have hN0 : 0 ≤ N := by linarith
  have hR0 : 0 < N ^ routeTPhysicalSliceHandoffTheta := by positivity
  have hinject := routeT_theta_window_mul_margin_le_smooth_vonMangoldt_mass hN0 hR0
  exact (mul_lt_mul_of_pos_left htheta routeTSmoothWindowCentralMargin_pos).trans_le hinject

end

end RHTower.Sieve
