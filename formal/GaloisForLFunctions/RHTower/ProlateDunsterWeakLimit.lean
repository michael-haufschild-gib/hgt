import GaloisForLFunctions.RHTower.ProlateDunsterDensityTransfer

/-!
# Weak radial limit for exact endpoint-normalized prolate solutions

The exact Dunster/Bessel density is averaged on compact intervals and controlled by a uniform
integrable tail.  The `L¹` transfer from `ProlateDunsterDensityTransfer` then carries the same tail
law to every exact endpoint-normalized radial prolate solution.
-/

noncomputable section

open Filter MeasureTheory Set

namespace GaloisForLFunctions.RHTower

theorem tendsto_profileWeight_fixed_radius
    {ι : Type*} {l : Filter ι} {s : ι → ℝ} (hs : Tendsto s l (nhds 0))
    {a : ℝ} (ha : 1 < a) :
    Tendsto (fun i => profileWeight (s i) a) l (nhds (profileWeight 0 a)) := by
  have hleft : 0 < a ^ (2 : ℕ) - 1 := by nlinarith
  have hden : Real.pi * Real.sqrt ((a ^ (2 : ℕ) - 1) * (a ^ (2 : ℕ) - 0)) ≠ 0 := by
    have ha0 : 0 < a := by linarith
    have : 0 < (a ^ (2 : ℕ) - 1) * (a ^ (2 : ℕ) - 0) :=
      by simpa using mul_pos hleft (sq_pos_of_pos ha0)
    positivity
  have hcont : ContinuousAt (fun u : ℝ => profileWeight u a) 0 := by
    rw [show (fun u : ℝ => profileWeight u a) =
        fun u => 1 / (Real.pi * Real.sqrt ((a ^ (2 : ℕ) - 1) * (a ^ (2 : ℕ) - u))) by
      funext u
      rw [profileWeight]]
    exact continuousAt_const.div
      (continuousAt_const.mul
        (Real.continuous_sqrt.continuousAt.comp
          (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)))) hden
  exact hcont.tendsto.comp hs

theorem tendsto_ampFourth_fixed_radius
    {ι : Type*} {l : Filter ι} {s : ι → ℝ} (hs : Tendsto s l (nhds 0))
    {a : ℝ} (ha : 1 < a) :
    Tendsto (fun i => ampFourth (s i) a) l (nhds (ampFourth 0 a)) := by
  have hden : Real.sqrt (Real.sqrt ((a ^ (2 : ℕ) - 1) * (a ^ (2 : ℕ) - 0))) ≠ 0 := by
    have hleft : 0 < a ^ (2 : ℕ) - 1 := by nlinarith
    have ha0 : 0 < a := by linarith
    have : 0 < (a ^ (2 : ℕ) - 1) * (a ^ (2 : ℕ) - 0) :=
      by simpa using mul_pos hleft (sq_pos_of_pos ha0)
    positivity
  have hcont : ContinuousAt (fun u : ℝ => ampFourth u a) 0 := by
    rw [show (fun u : ℝ => ampFourth u a) =
        fun u => 1 / Real.sqrt (Real.sqrt ((a ^ (2 : ℕ) - 1) * (a ^ (2 : ℕ) - u))) by
      funext u
      rw [ampFourth]]
    exact continuousAt_const.div
      (Real.continuous_sqrt.continuousAt.comp
        (Real.continuous_sqrt.continuousAt.comp
          (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)))) hden
  exact hcont.tendsto.comp hs

/-- At every fixed strict exterior radius, the Dunster oscillatory argument diverges with the
bandwidth. -/
theorem tendsto_c_mul_xiEndpointPhase_fixed_radius_atTop
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i) {a : ℝ} (ha : 1 < a) :
    Tendsto (fun i => c i * xiEndpointPhase (s i) a) l atTop := by
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hcPos : ∀ᶠ i in l, 0 < c i := hc.eventually (eventually_gt_atTop 0)
  have hq : 0 < (2 / 3 : ℝ) * Real.sqrt (a ^ (2 : ℕ) - 1) := by
    have : 0 < a ^ (2 : ℕ) - 1 := by nlinarith
    positivity
  have hlinear : Tendsto
      (fun i => ((2 / 3 : ℝ) * Real.sqrt (a ^ (2 : ℕ) - 1)) * c i) l atTop :=
    hc.const_mul_atTop hq
  refine tendsto_atTop_mono' l ?_ hlinear
  filter_upwards [hs0, hsHalf, hcPos] with i hsi0 hsi1 hci
  have hphase := sqrt_div_sqrt_two_le_xiEndpointPhase hsi0 hsi1 ha.le
  have h23 : (2 / 3 : ℝ) * Real.sqrt (a ^ (2 : ℕ) - 1) ≤
      Real.sqrt (a ^ (2 : ℕ) - 1) / Real.sqrt 2 := by
    have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hroot : 0 ≤ Real.sqrt (a ^ (2 : ℕ) - 1) := Real.sqrt_nonneg _
    have hcoeff : (2 / 3 : ℝ) ≤ 1 / Real.sqrt 2 := by
      rw [le_div_iff₀ hsqrt2pos]
      nlinarith
    calc
      (2 / 3 : ℝ) * Real.sqrt (a ^ (2 : ℕ) - 1)
          ≤ (1 / Real.sqrt 2) * Real.sqrt (a ^ (2 : ℕ) - 1) :=
        mul_le_mul_of_nonneg_right hcoeff hroot
      _ = Real.sqrt (a ^ (2 : ℕ) - 1) / Real.sqrt 2 := by
        rw [div_eq_mul_inv]
        ring
  nlinarith

/-- On every fixed compact exterior interval, the explicit squared-profile error tends to zero. -/
theorem tendsto_profileSqError_zero
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    {a b : ℝ} (ha : 1 < a) :
    Tendsto (fun i => profileSqError (s i) (c i) a b) l (nhds 0) := by
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hcPos : ∀ᶠ i in l, 0 < c i := hc.eventually (eventually_gt_atTop 0)
  have harg := tendsto_c_mul_xiEndpointPhase_fixed_radius_atTop hc hs hs0 ha
  have hrootTop : Tendsto
      (fun i => Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) l atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp harg)
  have hinvRoot : Tendsto
      (fun i => (Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a)))⁻¹) l (nhds 0) :=
    tendsto_inv_atTop_zero.comp hrootTop
  have hinvC : Tendsto (fun i => (c i)⁻¹) l (nhds 0) :=
    tendsto_inv_atTop_zero.comp hc
  have hW := tendsto_profileWeight_fixed_radius hs ha
  have hA := tendsto_ampFourth_fixed_radius hs ha
  have hterm1 : Tendsto (fun i => 2 * profileWeight (s i) a / c i) l (nhds 0) := by
    simpa [div_eq_mul_inv] using (hW.const_mul 2).mul hinvC
  have hE : Tendsto (fun i =>
      5 * ampFourth (s i) a /
        Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) l (nhds 0) := by
    simpa [div_eq_mul_inv] using (hA.const_mul 5).mul hinvRoot
  have hB : Tendsto (fun i =>
      2 * Real.sqrt (2 / Real.pi) * ampFourth (s i) a +
        5 * ampFourth (s i) a /
          Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) l
      (nhds (2 * Real.sqrt (2 / Real.pi) * ampFourth 0 a)) := by
    convert (hA.const_mul (2 * Real.sqrt (2 / Real.pi))).add hE using 1 <;> ring
  have hterm2 : Tendsto (fun i =>
      (2 * Real.sqrt (2 / Real.pi) * ampFourth (s i) a +
          5 * ampFourth (s i) a /
            Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) *
        (5 * ampFourth (s i) a /
          Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) * (b - a))
      l (nhds 0) := by
    convert (hB.mul hE).mul_const (b - a) using 1 <;> ring
  have hden : Tendsto (fun i => a ^ (2 : ℕ) - s i) l (nhds (a ^ (2 : ℕ))) := by
    simpa using tendsto_const_nhds.sub hs
  have ha2 : a ^ (2 : ℕ) ≠ 0 := by positivity
  have hterm3 : Tendsto (fun i =>
      3 * s i * profileDensity a / (a ^ (2 : ℕ) - s i) * (b - a)) l (nhds 0) := by
    have hnum : Tendsto (fun i => 3 * s i * profileDensity a) l (nhds 0) := by
      have hnum' := hs.const_mul (3 * profileDensity a)
      convert hnum' using 1
      · funext i
        ring
      · ring
    have hquot : Tendsto (fun i =>
        3 * s i * profileDensity a / (a ^ (2 : ℕ) - s i)) l (nhds 0) := by
      convert hnum.div hden ha2 using 1
      · funext i
        change 3 * s i * profileDensity a / (a ^ (2 : ℕ) - s i) =
          3 * s i * profileDensity a / (a ^ (2 : ℕ) - s i)
        rfl
      · ring
    simpa using hquot.mul_const (b - a)
  rw [show (fun i => profileSqError (s i) (c i) a b) = fun i =>
      2 * profileWeight (s i) a / c i +
        (2 * Real.sqrt (2 / Real.pi) * ampFourth (s i) a +
            5 * ampFourth (s i) a /
              Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) *
          (5 * ampFourth (s i) a /
            Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) * (b - a) +
        3 * s i * profileDensity a / (a ^ (2 : ℕ) - s i) * (b - a) by
    funext i
    rw [profileSqError]]
  convert (hterm1.add hterm2).add hterm3 using 1 <;> ring

/-- Compact-interval oscillatory averaging for the literal regular Bessel density. -/
theorem tendsto_intervalIntegral_radialProlateBesselDensity
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Tendsto (fun i => ∫ x in a..b, radialProlateBesselDensity (s i) (c i) x) l
      (nhds (∫ x in a..b, profileDensity x)) := by
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hcPos : ∀ᶠ i in l, 0 < c i := hc.eventually (eventually_gt_atTop 0)
  have harg := tendsto_c_mul_xiEndpointPhase_fixed_radius_atTop hc hs hs0 ha
  have hcxi : ∀ᶠ i in l, 1 ≤ c i * xiEndpointPhase (s i) a :=
    harg.eventually (eventually_ge_atTop 1)
  have herr := tendsto_profileSqError_zero hc hs hs0 (b := b) ha
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using squeeze_zero'
    (Filter.Eventually.of_forall fun i => abs_nonneg
      ((∫ x in a..b, radialProlateBesselDensity (s i) (c i) x) -
        ∫ x in a..b, profileDensity x))
    (by
      filter_upwards [hs0, hsHalf, hcPos, hcxi] with i hsi0 hsi1 hci hcxii
      simpa only [radialProlateBesselDensity, profileSqError] using
        abs_integral_profileSq_sub_density_le hsi0 hsi1 ha hab hci hcxii)
    herr

theorem tendsto_integral_Ioi_profileDensity_atTop_zero :
    Tendsto (fun a : ℝ => ∫ x in Ioi a, profileDensity x) atTop (nhds 0) := by
  have hlim : Tendsto (fun a : ℝ => 1 / 2 - radialAngle a / Real.pi)
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) atTop (nhds (1 / 2)) :=
      tendsto_const_nhds
    have h := hconst.sub tendsto_radialAngle_div_pi
    convert h using 1
    norm_num
  have hformula : (fun a : ℝ => ∫ x in Ioi a, profileDensity x) =ᶠ[atTop]
      fun a => 1 / 2 - radialAngle a / Real.pi := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    exact integral_Ioi_profileDensity_eq ha
  exact hlim.congr' hformula.symm

/-- Global tail-mass convergence of the literal regular Bessel density. -/
theorem tendsto_integral_Ioi_radialProlateBesselDensity
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i) {a : ℝ} (ha : 1 < a) :
    Tendsto (fun i => ∫ x in Ioi a, radialProlateBesselDensity (s i) (c i) x) l
      (nhds (∫ x in Ioi a, profileDensity x)) := by
  let K : ℝ := 4 * Real.pi * lgBesselCommonEnvelopeConstant ^ (2 : ℕ)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hcPos : ∀ᶠ i in l, 0 < c i := hc.eventually (eventually_gt_atTop 0)
  have hargA := tendsto_c_mul_xiEndpointPhase_fixed_radius_atTop hc hs hs0 ha
  have hcxiA : ∀ᶠ i in l, 1 ≤ c i * xiEndpointPhase (s i) a :=
    hargA.eventually (eventually_ge_atTop 1)
  rw [Metric.tendsto_nhds]
  intro eps heps
  have htailScaled : Tendsto
      (fun B : ℝ => (K + 1) * ∫ x in Ioi B, profileDensity x) atTop (nhds 0) := by
    simpa using tendsto_integral_Ioi_profileDensity_atTop_zero.const_mul (K + 1)
  have htailSmall : ∀ᶠ B : ℝ in atTop,
      (K + 1) * ∫ x in Ioi B, profileDensity x < eps / 2 :=
    htailScaled.eventually (eventually_lt_nhds (half_pos heps))
  obtain ⟨B, hBsmall, hBa⟩ :=
    (htailSmall.and (eventually_gt_atTop a)).exists
  have hlocal := tendsto_intervalIntegral_radialProlateBesselDensity
    hc hs hs0 ha hBa.le
  have hlocalEv : ∀ᶠ i in l,
      dist (∫ x in a..B, radialProlateBesselDensity (s i) (c i) x)
        (∫ x in a..B, profileDensity x) < eps / 2 :=
    (Metric.tendsto_nhds.mp hlocal) (eps / 2) (half_pos heps)
  filter_upwards [hs0, hsHalf, hcPos, hcxiA, hlocalEv] with
      i hsi0 hsi1 hci hcxia hloc
  have hB1 : 1 < B := ha.trans hBa
  have hphaseAB : xiEndpointPhase (s i) a ≤ xiEndpointPhase (s i) B :=
    xiEndpointPhase_le_of_le hsi0 hsi1 ha.le hBa.le
  have hcxiB : 1 ≤ c i * xiEndpointPhase (s i) B :=
    hcxia.trans (mul_le_mul_of_nonneg_left hphaseAB hci.le)
  have hBintA : IntegrableOn (radialProlateBesselDensity (s i) (c i)) (Ioi a) :=
    integrableOn_radialProlateBesselDensity hsi0 hsi1 hci ha hcxia
  have hDintA : IntegrableOn profileDensity (Ioi a) :=
    integrableOn_profileDensity.mono_set (Ioi_subset_Ioi ha.le)
  have hdisj : Disjoint (Ioc a B) (Ioi B) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  have hunion : Ioc a B ∪ Ioi B = Ioi a := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact hBa.trans hx
    · intro hx
      exact le_or_gt x B |>.elim (fun hxB => Or.inl ⟨hx, hxB⟩) Or.inr
  have hIocSub : Ioc a B ⊆ Ioi a := fun _ hx => hx.1
  have hIoiBSub : Ioi B ⊆ Ioi a := fun _ hx => hBa.trans hx
  have hsplitBessel :
      (∫ x in Ioi a, radialProlateBesselDensity (s i) (c i) x) =
        (∫ x in a..B, radialProlateBesselDensity (s i) (c i) x) +
          ∫ x in Ioi B, radialProlateBesselDensity (s i) (c i) x := by
    rw [intervalIntegral.integral_of_le hBa.le]
    rw [← hunion]
    exact integral_union_ae hdisj.aedisjoint measurableSet_Ioi.nullMeasurableSet
      (hBintA.mono_set hIocSub) (hBintA.mono_set hIoiBSub)
  have hsplitDensity :
      (∫ x in Ioi a, profileDensity x) =
        (∫ x in a..B, profileDensity x) + ∫ x in Ioi B, profileDensity x := by
    rw [intervalIntegral.integral_of_le hBa.le]
    rw [← hunion]
    exact integral_union_ae hdisj.aedisjoint measurableSet_Ioi.nullMeasurableSet
      (hDintA.mono_set hIocSub) (hDintA.mono_set hIoiBSub)
  have htailB := integral_Ioi_radialProlateBesselDensity_le
    hsi0 hsi1 hci hB1 hcxiB
  have htailB0 : 0 ≤ ∫ x in Ioi B,
      radialProlateBesselDensity (s i) (c i) x :=
    integral_nonneg fun x => radialProlateBesselDensity_nonneg (s i) (c i) x
  have htailD0 : 0 ≤ ∫ x in Ioi B, profileDensity x :=
    integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact profileDensity_nonneg (hB1.trans hx).le)
  rw [Real.dist_eq, hsplitBessel, hsplitDensity]
  calc
    |((∫ x in a..B, radialProlateBesselDensity (s i) (c i) x) +
          ∫ x in Ioi B, radialProlateBesselDensity (s i) (c i) x) -
        ((∫ x in a..B, profileDensity x) + ∫ x in Ioi B, profileDensity x)|
        ≤ |(∫ x in a..B, radialProlateBesselDensity (s i) (c i) x) -
              ∫ x in a..B, profileDensity x| +
            (∫ x in Ioi B, radialProlateBesselDensity (s i) (c i) x) +
              ∫ x in Ioi B, profileDensity x := by
          calc
            |_ - _| = |((∫ x in a..B,
                  radialProlateBesselDensity (s i) (c i) x) -
                ∫ x in a..B, profileDensity x) +
              ((∫ x in Ioi B, radialProlateBesselDensity (s i) (c i) x) -
                ∫ x in Ioi B, profileDensity x)| := by ring_nf
            _ ≤ |(∫ x in a..B, radialProlateBesselDensity (s i) (c i) x) -
                  ∫ x in a..B, profileDensity x| +
                |(∫ x in Ioi B, radialProlateBesselDensity (s i) (c i) x) -
                  ∫ x in Ioi B, profileDensity x| := abs_add_le _ _
            _ ≤ _ := by
              have htailTriangle := abs_sub
                (∫ x in Ioi B, radialProlateBesselDensity (s i) (c i) x)
                (∫ x in Ioi B, profileDensity x)
              rw [abs_of_nonneg htailB0, abs_of_nonneg htailD0] at htailTriangle
              linarith
    _ < eps / 2 + K * (∫ x in Ioi B, profileDensity x) +
          ∫ x in Ioi B, profileDensity x := by
        rw [Real.dist_eq] at hloc
        change (∫ x in Ioi B, radialProlateBesselDensity (s i) (c i) x) ≤
          K * ∫ x in Ioi B, profileDensity x at htailB
        linarith
    _ = eps / 2 + (K + 1) * ∫ x in Ioi B, profileDensity x := by ring
    _ < eps / 2 + eps / 2 := by linarith
    _ = eps := by ring

theorem tendsto_dunsterEndpointCrossing_comp_atTop_one
    {ι : Type*} {l : Filter ι} {c : ι → ℝ} (hc : Tendsto c l atTop) :
    Tendsto (fun i => dunsterEndpointCrossing (c i)) l (nhds 1) := by
  have hc0 : ∀ᶠ i in l, c i ≠ 0 :=
    (hc.eventually (eventually_gt_atTop 0)).mono fun _ hi => hi.ne'
  have hinv : Tendsto (fun i => (c i)⁻¹) l (nhds 0) :=
    tendsto_inv_atTop_zero.comp hc
  have hterm : Tendsto (fun i => 9 / (8 * c i ^ (2 : ℕ))) l (nhds 0) := by
    have hraw := (hinv.pow 2).const_mul (9 / 8)
    have hraw0 : Tendsto (fun i => (9 / 8 : ℝ) * (c i)⁻¹ ^ (2 : ℕ)) l (nhds 0) := by
      simpa using hraw
    apply hraw0.congr'
    filter_upwards [hc0] with i hci
    field_simp
  simpa [dunsterEndpointCrossing] using tendsto_const_nhds.add hterm

/-- Global tail-mass convergence for every exact endpoint-normalized radial prolate solution. -/
theorem tendsto_integral_Ioi_radialProlateDensity
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    {R DR DDR : ι → ℝ → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    (hR1 : ∀ᶠ i in l, R i 1 = 1)
    (hR : ∀ᶠ i in l, ∀ t, HasDerivAt (R i) (DR i t) t)
    (hDR : ∀ᶠ i in l, ∀ t, HasDerivAt (DR i) (DDR i t) t)
    (hode : ∀ᶠ i in l, ∀ t, (t ^ (2 : ℕ) - 1) * DDR i t + 2 * t * DR i t
      - (s i * c i ^ (2 : ℕ) - c i ^ (2 : ℕ) * t ^ (2 : ℕ)) * R i t = 0)
    {a : ℝ} (ha : 1 < a) :
    Tendsto (fun i => ∫ x in Ioi a, radialProlateDensity (c i) (R i) x) l
      (nhds (∫ x in Ioi a, profileDensity x)) := by
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hc5 : ∀ᶠ i in l, 5 ≤ c i := hc.eventually (eventually_ge_atTop 5)
  have hcross := tendsto_dunsterEndpointCrossing_comp_atTop_one hc
  have hcrossA : ∀ᶠ i in l, dunsterEndpointCrossing (c i) ≤ a :=
    (hcross.eventually (eventually_lt_nhds ha)).mono fun _ hi => hi.le
  have hbessel := tendsto_integral_Ioi_radialProlateBesselDensity hc hs hs0 ha
  have hinvC : Tendsto (fun i => (c i)⁻¹) l (nhds 0) :=
    tendsto_inv_atTop_zero.comp hc
  have hbound : Tendsto
      (fun i => 2 * radialProlateDensityTransferConstant / c i) l (nhds 0) := by
    simpa [div_eq_mul_inv] using
      hinvC.const_mul (2 * radialProlateDensityTransferConstant)
  have hdiff : Tendsto (fun i =>
      (∫ x in Ioi a, radialProlateDensity (c i) (R i) x) -
        ∫ x in Ioi a, radialProlateBesselDensity (s i) (c i) x) l (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, Real.norm_eq_abs] using squeeze_zero'
      (Filter.Eventually.of_forall fun i => abs_nonneg
        ((∫ x in Ioi a, radialProlateDensity (c i) (R i) x) -
          ∫ x in Ioi a, radialProlateBesselDensity (s i) (c i) x))
      (by
        filter_upwards [hs0, hsHalf, hc5, hcrossA, hR1, hR, hDR, hode]
          with i hsi0 hsi1 hci hcai hR1i hRi hDRi hodei
        have hci0 : 0 < c i := lt_of_lt_of_le (by norm_num) hci
        have hcross1 : 1 < dunsterEndpointCrossing (c i) :=
          dunsterEndpointCrossing_gt_one hci0
        have hBint : IntegrableOn (radialProlateBesselDensity (s i) (c i)) (Ioi a) := by
          have hargCross := one_le_c_mul_xiEndpointPhase_crossing hsi0 hsi1 hci
          have hphase := xiEndpointPhase_le_of_le hsi0 hsi1 hcross1.le hcai
          exact integrableOn_radialProlateBesselDensity hsi0 hsi1 hci0 ha
            (hargCross.trans (mul_le_mul_of_nonneg_left hphase hci0.le))
        let E : ℝ → ℝ := fun x =>
          (radialProlateDensityTransferConstant / c i) * profileWeight (s i) x
        have hEint : IntegrableOn E (Ioi a) :=
          (integrableOn_profileWeight hsi0 hsi1 ha).const_mul
            (radialProlateDensityTransferConstant / c i)
        have hExactCont : Continuous (radialProlateDensity (c i) (R i)) := by
          have hRc : Continuous (R i) := continuous_iff_continuousAt.mpr fun x =>
            (hRi x).continuousAt
          unfold radialProlateDensity
          fun_prop
        have hDiffMeas : AEStronglyMeasurable
            (fun x => radialProlateDensity (c i) (R i) x -
              radialProlateBesselDensity (s i) (c i) x)
            (volume.restrict (Ioi a)) :=
          (hExactCont.continuousOn.sub
            (continuousOn_radialProlateBesselDensity hsi0 hsi1 ha)).aestronglyMeasurable
              measurableSet_Ioi
        have hDiffInt : IntegrableOn
            (fun x => radialProlateDensity (c i) (R i) x -
              radialProlateBesselDensity (s i) (c i) x) (Ioi a) := by
          refine Integrable.mono' hEint hDiffMeas ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          rw [Real.norm_eq_abs]
          exact abs_radialProlateDensity_sub_besselDensity_le
            hsi0 hsi1 hci hR1i hRi hDRi hodei (hcai.trans hx.le)
        have hExactInt : IntegrableOn (radialProlateDensity (c i) (R i)) (Ioi a) := by
          have hadd := hDiffInt.add hBint
          rw [show radialProlateDensity (c i) (R i) =
              (fun x => radialProlateDensity (c i) (R i) x -
                radialProlateBesselDensity (s i) (c i) x) +
                radialProlateBesselDensity (s i) (c i) by
            funext x
            simp]
          exact hadd
        rw [← integral_sub hExactInt hBint, ← Real.norm_eq_abs]
        calc
          ‖∫ x in Ioi a,
              (radialProlateDensity (c i) (R i) x -
                radialProlateBesselDensity (s i) (c i) x)‖
              ≤ ∫ x in Ioi a,
                  ‖radialProlateDensity (c i) (R i) x -
                    radialProlateBesselDensity (s i) (c i) x‖ :=
                norm_integral_le_integral_norm _
          _ = ∫ x in Ioi a,
                |radialProlateDensity (c i) (R i) x -
                  radialProlateBesselDensity (s i) (c i) x| := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x _
              exact Real.norm_eq_abs _
          _ ≤ 2 * radialProlateDensityTransferConstant / c i :=
            integral_Ioi_abs_radialProlateDensity_sub_besselDensity_le
              hsi0 hsi1 hci hcai hR1i hRi hDRi hodei)
      hbound
  have hadd := hdiff.add hbessel
  simpa only [sub_add_cancel, zero_add] using hadd

end GaloisForLFunctions.RHTower

end
