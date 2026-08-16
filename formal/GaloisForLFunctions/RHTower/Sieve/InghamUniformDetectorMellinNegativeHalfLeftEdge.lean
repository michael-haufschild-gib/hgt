import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinEntireXiSource
import GaloisForLFunctions.RHTower.TitchmarshZetaInputs
import GaloisForLFunctions.RHTower.Sieve.ZetaDerivBound
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegBound

open Complex Filter Metric Set Finset Topology MeasureTheory Asymptotics

namespace RHTower.Sieve

noncomputable section

open GaloisForLFunctions.HTGeometry

theorem routeTSmoothWindowWeight_isMellinFlatKernel
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) :
    RHTower.IsMellinFlatKernel
      (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) := by
  let W : ℝ → ℂ := fun x => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)
  have hcont : Continuous W := by
    have hreal : Continuous (routeTSmoothWindowWeight N H) := by
      unfold routeTSmoothWindowWeight
      exact (smoothWeight_contDiff (N + H) H (n := 0)).continuous.sub
        (smoothWeight_contDiff N H (n := 0)).continuous
    exact Complex.continuous_ofReal.comp hreal
  have hloc : LocallyIntegrableOn W (Ioi 0) :=
    hcont.locallyIntegrable.locallyIntegrableOn _
  have htop : ∃ a : ℝ, 0 < a ∧ W =O[atTop]
      (fun x : ℝ => Real.exp (-a * x)) := by
    refine ⟨1, by norm_num, ?_⟩
    have heq : W =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [eventually_ge_atTop (N + 2 * H)] with x hx
      have hplus : GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x = 0 :=
        GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH (by linarith)
      have hbase : GaloisForLFunctions.HTGeometry.smoothWeight N H x = 0 :=
        GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH (by linarith)
      simp only [W, routeTSmoothWindowWeight, hplus, hbase, sub_self,
        Complex.ofReal_zero]
    exact heq.trans_isBigO (isBigO_zero _ _)
  have hzero : RHTower.SuperpolynomialDecayAtZero W := by
    intro b
    have heq : W =ᶠ[𝓝[>] 0] (fun _ => 0) := by
      have hlt : ∀ᶠ x : ℝ in 𝓝[>] 0, x < N :=
        (eventually_lt_nhds hN).filter_mono nhdsWithin_le_nhds
      filter_upwards [hlt] with x hx
      have hplus : GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x = 1 :=
        GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH (by linarith)
      have hbase : GaloisForLFunctions.HTGeometry.smoothWeight N H x = 1 :=
        GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH hx.le
      simp only [W, routeTSmoothWindowWeight, hplus, hbase, sub_self,
        Complex.ofReal_zero]
    exact heq.trans_isBigO (isBigO_zero _ _)
  exact ⟨hloc, htop, hzero⟩

/-- Compact-support interval representation at every complex Mellin parameter. -/
theorem mellin_routeTSmoothWindowWeight_eq_interval
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (s : ℂ) :
    mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s =
      ∫ x in N..(N + 2 * H),
        ((routeTSmoothWindowWeight N H x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) := by
  let f : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (s - 1) * ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)
  have hall : IntegrableOn f (Ioi (0 : ℝ)) := by
    simpa only [f, MellinConvergent, smul_eq_mul] using
      (routeTSmoothWindowWeight_isMellinFlatKernel hN hH).mellinConvergent s
  have hleft : IntegrableOn f (Ioc 0 N) := hall.mono_set (by
    intro x hx
    exact hx.1)
  have hright : IntegrableOn f (Ioi (N + 2 * H)) := hall.mono_set (by
    intro x hx
    exact lt_trans (by linarith : (0 : ℝ) < N + 2 * H) hx)
  have hmid : IntegrableOn f (Ioc N (N + 2 * H)) := hall.mono_set (by
    intro x hx
    exact lt_trans hN hx.1)
  have hsplit0 : Ioc (0 : ℝ) N ∪ Set.Ioi N = Set.Ioi 0 :=
    Ioc_union_Ioi_eq_Ioi hN.le
  have hsplitN : Ioc N (N + 2 * H) ∪ Ioi (N + 2 * H) = Ioi N :=
    Ioc_union_Ioi_eq_Ioi (by linarith)
  rw [mellin]
  simp only [smul_eq_mul]
  change (∫ x in Ioi (0 : ℝ), f x) = _
  rw [← hsplit0, setIntegral_union (by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_le.mpr hx')) measurableSet_Ioi hleft (hall.mono_set (by
        intro x hx
        exact lt_trans hN hx))]
  have hzleft : ∫ x in Ioc (0 : ℝ) N, f x = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hplus : GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x = 1 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH
        (hx.2.trans (le_add_of_nonneg_right hH.le))
    have hbase : GaloisForLFunctions.HTGeometry.smoothWeight N H x = 1 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH hx.2
    simp [f, routeTSmoothWindowWeight, hplus, hbase]
  rw [hzleft, zero_add, ← hsplitN, setIntegral_union (by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_le.mpr hx')) measurableSet_Ioi hmid hright]
  have hzright : ∫ x in Ioi (N + 2 * H), f x = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hx' : N + 2 * H < x := hx
    have hplus : GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x = 0 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH (by linarith)
    have hbase : GaloisForLFunctions.HTGeometry.smoothWeight N H x = 0 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH (by linarith)
    simp [f, routeTSmoothWindowWeight, hplus, hbase]
  rw [hzright, add_zero, intervalIntegral.integral_of_le (by linarith)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _hx
  exact mul_comm _ _

/-- Iterated Mellin integration by parts at any parameter avoiding the finitely many factors. -/
theorem intervalIntegral_byParts_iterate_of_ne
    {v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvan : ∀ i : ℕ, iteratedDeriv i v a = 0 ∧ iteratedDeriv i v b = 0)
    {s : ℂ} (j : ℕ) (hs : ∀ i ∈ Finset.range j, s + (i : ℂ) ≠ 0) :
    (∫ x in a..b, ((v x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1))
      = (-1) ^ j / (∏ i ∈ Finset.range j, (s + (i : ℂ))) *
        ∫ x in a..b, ((iteratedDeriv j v x : ℝ) : ℂ) *
          (x : ℂ) ^ (s + (j : ℂ) - 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hsj : s + (j : ℂ) ≠ 0 := hs j (Finset.mem_range.mpr (Nat.lt_succ_self j))
      have hprev : ∀ i ∈ Finset.range j, s + (i : ℂ) ≠ 0 := by
        intro i hi
        exact hs i (Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans (Nat.lt_succ_self j)))
      have hstep := intervalIntegral_byParts_of_vanishing (v := iteratedDeriv j v) hab ha
        ((contDiff_top_iteratedDeriv hv j).of_le (WithTop.coe_le_coe.mpr le_top))
        (hvan j).1 (hvan j).2 (s := s + (j : ℂ)) hsj
      rw [ih hprev, hstep]
      have hsucc : (iteratedDeriv (j + 1) v) = deriv (iteratedDeriv j v) :=
        iteratedDeriv_succ
      have hprod : (∏ i ∈ Finset.range (j + 1), (s + (i : ℂ))) =
          (∏ i ∈ Finset.range j, (s + (i : ℂ))) * (s + (j : ℂ)) :=
        Finset.prod_range_succ _ _
      rw [hprod, hsucc]
      have hpow : ∀ x : ℝ, (x : ℂ) ^ (s + (j : ℂ)) =
          (x : ℂ) ^ (s + ((j + 1 : ℕ) : ℂ) - 1) := by
        intro x
        congr 1
        push_cast
        ring
      rw [intervalIntegral.integral_congr (g := fun x : ℝ =>
        (((deriv (iteratedDeriv j v) x : ℝ) : ℂ) *
          ((x : ℂ) ^ (s + ((j + 1 : ℕ) : ℂ) - 1))) / (s + (j : ℂ)))
        (fun x _ => by rw [hpow x]; ring)]
      rw [intervalIntegral.integral_div]
      field_simp
      ring

/-- Sharp support-length bound for the final derivative integral on any fixed vertical line. -/
theorem exists_bound_routeTWindow_iteratedDerivMellin_line (j : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ sigma N H t : ℝ, 0 < N → 0 < H → H ≤ N →
      0 ≤ sigma + (j : ℝ) - 1 →
      ‖∫ x in N..(N + 2 * H),
          ((iteratedDeriv j (routeTSmoothWindowWeight N H) x : ℝ) : ℂ) *
            (x : ℂ) ^ (((sigma : ℂ) + (t : ℂ) * I) + (j : ℂ) - 1)‖
        ≤ Cj * H / H ^ j * (3 * N) ^ (sigma + (j : ℝ) - 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_iteratedDeriv_smoothWeight_uniform j
  refine ⟨4 * C, by positivity, fun sigma N H t hN hH hHN hexp => ?_⟩
  let f : ℝ → ℂ := fun x =>
    ((iteratedDeriv j (routeTSmoothWindowWeight N H) x : ℝ) : ℂ) *
      (x : ℂ) ^ (((sigma : ℂ) + (t : ℂ) * I) + (j : ℂ) - 1)
  have hboundf : ∀ x ∈ Set.uIoc N (N + 2 * H),
      ‖f x‖ ≤ 2 * C / H ^ j * (3 * N) ^ (sigma + (j : ℝ) - 1) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hx0 : 0 < x := lt_trans hN hx.1
    have hxupper : x ≤ N + 2 * H := hx.2
    have hx3 : x ≤ 3 * N := by linarith
    have hplus := hbound (N + H) H hH x
    have hbase := hbound N H hH x
    have hderiv : |iteratedDeriv j (routeTSmoothWindowWeight N H) x| ≤
        2 * C / H ^ j := by
      change |iteratedDeriv j
        (GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H -
          GaloisForLFunctions.HTGeometry.smoothWeight N H) x| ≤ _
      rw [iteratedDeriv_sub
        (smoothWeight_contDiff (N + H) H).contDiffAt
        (smoothWeight_contDiff N H).contDiffAt]
      calc
        |iteratedDeriv j (GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H) x -
            iteratedDeriv j (GaloisForLFunctions.HTGeometry.smoothWeight N H) x|
            ≤ |iteratedDeriv j (GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H) x| +
                |iteratedDeriv j (GaloisForLFunctions.HTGeometry.smoothWeight N H) x| := abs_sub _ _
        _ ≤ C / H ^ j + C / H ^ j := add_le_add hplus hbase
        _ = 2 * C / H ^ j := by ring
    change ‖((iteratedDeriv j (routeTSmoothWindowWeight N H) x : ℝ) : ℂ) *
      (x : ℂ) ^ (((sigma : ℂ) + (t : ℂ) * I) + (j : ℂ) - 1)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (((sigma : ℂ) + (t : ℂ) * I) + (j : ℂ) - 1).re =
        sigma + (j : ℝ) - 1 := by simp
    rw [hre]
    have hpow : x ^ (sigma + (j : ℝ) - 1) ≤
        (3 * N) ^ (sigma + (j : ℝ) - 1) :=
      Real.rpow_le_rpow hx0.le hx3 hexp
    exact mul_le_mul hderiv hpow (by positivity) (by positivity)
  have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := f) (C := 2 * C / H ^ j * (3 * N) ^ (sigma + (j : ℝ) - 1)) hboundf
  change ‖∫ x in N..(N + 2 * H), f x‖ ≤ _
  calc
    ‖∫ x in N..(N + 2 * H), f x‖
        ≤ 2 * C / H ^ j * (3 * N) ^ (sigma + (j : ℝ) - 1) *
          |N + 2 * H - N| := hInt
    _ = (4 * C) * H / H ^ j * (3 * N) ^ (sigma + (j : ℝ) - 1) := by
      rw [abs_of_pos (by linarith : 0 < N + 2 * H - N)]
      ring

/-- Arbitrary-order decay for the normalized adjacent Route-T Mellin kernel on any vertical line. -/
theorem exists_bound_routeTNormalizedSmoothWindowMellin_line (j : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ sigma N H t : ℝ, 0 < N → 0 < H → H ≤ N →
      1 ≤ j → 0 ≤ sigma + (j : ℝ) - 1 →
      0 < |t| →
      |t| ^ j * ‖routeTNormalizedSmoothWindowMellin N H ((sigma : ℂ) + (t : ℂ) * I)‖
        ≤ Cj * (3 * N) ^ (sigma + (j : ℝ) - 1) / H ^ j := by
  obtain ⟨Cj, hCj, hIntBound⟩ :=
    exists_bound_routeTWindow_iteratedDerivMellin_line j
  refine ⟨Cj, hCj, fun sigma N H t hN hH hHN hj hexp ht => ?_⟩
  let W : ℝ → ℝ := routeTSmoothWindowWeight N H
  let s : ℂ := (sigma : ℂ) + (t : ℂ) * I
  let a : ℝ := N / 2
  let B : ℝ := N + 2 * H
  let b : ℝ := B + 1
  let f0 : ℝ → ℂ := fun x => ((W x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)
  have hv : ContDiff ℝ (⊤ : ℕ∞) W := by
    dsimp only [W, routeTSmoothWindowWeight]
    exact (smoothWeight_contDiff (N + H) H).sub (smoothWeight_contDiff N H)
  have ha0 : 0 < a := by dsimp only [a]; linarith
  have haN : a < N := by dsimp only [a]; linarith
  have hNB : N ≤ B := by dsimp only [B]; linarith
  have hBb : B < b := by dsimp only [b]; linarith
  have hf0cont : ContinuousOn f0 (Ioi (0 : ℝ)) := by
    intro x hx
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
    · exact Complex.continuous_ofReal.continuousAt.comp_of_eq hv.continuous.continuousAt rfl
    · exact ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
        (Or.inl (by simpa using hx))
  have hIleft0 : IntervalIntegrable f0 volume a N := by
    refine (hf0cont.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le haN.le] at hx
    exact lt_of_lt_of_le ha0 hx.1
  have hImid0 : IntervalIntegrable f0 volume N B := by
    refine (hf0cont.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hNB] at hx
    exact lt_of_lt_of_le hN hx.1
  have hIright0 : IntervalIntegrable f0 volume B b := by
    refine (hf0cont.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hBb.le] at hx
    exact lt_of_lt_of_le hN (hNB.trans hx.1)
  have hleft0 : (∫ x in a..N, f0 x) = 0 := by
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le haN.le] at hx
    have hplus : GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x = 1 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH
        (hx.2.trans (le_add_of_nonneg_right hH.le))
    have hbase : GaloisForLFunctions.HTGeometry.smoothWeight N H x = 1 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH hx.2
    simp [f0, W, routeTSmoothWindowWeight, hplus, hbase]
  have hright0 : (∫ x in B..b, f0 x) = 0 := by
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hBb.le] at hx
    have hxB : B ≤ x := hx.1
    have hplus : GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x = 0 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH (by
        dsimp only [B] at hxB
        linarith)
    have hbase : GaloisForLFunctions.HTGeometry.smoothWeight N H x = 0 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH (by
        dsimp only [B] at hxB
        linarith)
    simp [f0, W, routeTSmoothWindowWeight, hplus, hbase]
  have hwide0 : (∫ x in a..b, f0 x) = ∫ x in N..B, f0 x := by
    have h₁ := intervalIntegral.integral_add_adjacent_intervals hIleft0 hImid0
    have h₂ := intervalIntegral.integral_add_adjacent_intervals
      (hIleft0.trans hImid0) hIright0
    rw [hleft0, zero_add] at h₁
    rw [← h₁, hright0, add_zero] at h₂
    exact h₂.symm
  have hmellinWide :
      mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s =
        ∫ x in a..b, f0 x := by
    rw [mellin_routeTSmoothWindowWeight_eq_interval hN hH s]
    change (∫ x in N..B, f0 x) = _
    exact hwide0.symm
  have hWa : W =ᶠ[nhds a] (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds haN] with x hx
    have hx' : x < N := hx
    have hplus : GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x = 1 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH (by linarith)
    have hbase : GaloisForLFunctions.HTGeometry.smoothWeight N H x = 1 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH hx.le
    simp [W, routeTSmoothWindowWeight, hplus, hbase]
  have hWb : W =ᶠ[nhds b] (fun _ => 0) := by
    have hBb' : B < b := hBb
    filter_upwards [Ioi_mem_nhds hBb'] with x hx
    have hx' : B < x := hx
    have hplus : GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x = 0 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH (by
        dsimp only [B] at hx'
        linarith)
    have hbase : GaloisForLFunctions.HTGeometry.smoothWeight N H x = 0 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH (by
        dsimp only [B] at hx'
        linarith)
    simp [W, routeTSmoothWindowWeight, hplus, hbase]
  have hvan : ∀ i : ℕ, iteratedDeriv i W a = 0 ∧ iteratedDeriv i W b = 0 := by
    intro i
    constructor
    · rw [hWa.iteratedDeriv_eq i, iteratedDeriv_const]
      simp
    · rw [hWb.iteratedDeriv_eq i, iteratedDeriv_const]
      simp
  have hsne : ∀ i ∈ Finset.range j, s + (i : ℂ) ≠ 0 := by
    intro i hi hzero
    have ht0 : t = 0 := calc
      t = (s + (i : ℂ)).im := by simp [s]
      _ = 0 := by rw [hzero]; rfl
    rw [ht0, abs_zero] at ht
    exact (lt_irrefl 0 ht)
  have hab : a ≤ b := haN.le.trans (hNB.trans hBb.le)
  have hparts := intervalIntegral_byParts_iterate_of_ne
    (v := W) (a := a) (b := b) hab ha0 hv hvan j hsne
  have hMellinParts :
      mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s =
        (-1) ^ j / (∏ i ∈ Finset.range j, (s + (i : ℂ))) *
          ∫ x in a..b, ((iteratedDeriv j W x : ℝ) : ℂ) *
            (x : ℂ) ^ (s + (j : ℂ) - 1) := by
    rw [hmellinWide]
    exact hparts
  let fj : ℝ → ℂ := fun x => ((iteratedDeriv j W x : ℝ) : ℂ) *
    (x : ℂ) ^ (s + (j : ℂ) - 1)
  have hfjcont : ContinuousOn fj (Ioi (0 : ℝ)) := by
    intro x hx
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
    · exact Complex.continuous_ofReal.continuousAt.comp_of_eq
        ((contDiff_top_iteratedDeriv hv j).continuous.continuousAt) rfl
    · exact ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
        (Or.inl (by simpa using hx))
  have hIleftj : IntervalIntegrable fj volume a N := by
    refine (hfjcont.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le haN.le] at hx
    exact lt_of_lt_of_le ha0 hx.1
  have hImidj : IntervalIntegrable fj volume N B := by
    refine (hfjcont.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hNB] at hx
    exact lt_of_lt_of_le hN hx.1
  have hIrightj : IntervalIntegrable fj volume B b := by
    refine (hfjcont.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hBb.le] at hx
    exact lt_of_lt_of_le hN (hNB.trans hx.1)
  have hleftj : (∫ x in a..N, fj x) = 0 := by
    rw [← intervalIntegral.integral_zero]
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ N := by
      rw [ae_iff]
      rw [show {x : ℝ | ¬x ≠ N} = {N} by ext x; simp]
      exact measure_singleton N
    filter_upwards [hne] with x hxne hx
    rw [Set.uIoc_of_le haN.le] at hx
    have hxlt : x < N := lt_of_le_of_ne hx.2 hxne
    have hplus := iteratedDeriv_smoothWeight_eq_zero_of_lt hH (by omega : j ≠ 0)
      (show x < N + H by linarith)
    have hbase := iteratedDeriv_smoothWeight_eq_zero_of_lt hH (by omega : j ≠ 0) hxlt
    change ((iteratedDeriv j
      (GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H -
        GaloisForLFunctions.HTGeometry.smoothWeight N H) x : ℝ) : ℂ) * _ = 0
    rw [iteratedDeriv_sub (smoothWeight_contDiff (N + H) H).contDiffAt
      (smoothWeight_contDiff N H).contDiffAt, hplus, hbase, sub_self]
    simp
  have hrightj : (∫ x in B..b, fj x) = 0 := by
    rw [← intervalIntegral.integral_zero]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [] with x hx
    rw [Set.uIoc_of_le hBb.le] at hx
    have hxgt : B < x := hx.1
    have hplus := iteratedDeriv_smoothWeight_eq_zero_of_gt hH (by omega : j ≠ 0)
      (show N + H + H < x by dsimp only [B] at hxgt; linarith)
    have hbase := iteratedDeriv_smoothWeight_eq_zero_of_gt hH (by omega : j ≠ 0)
      (show N + H < x by dsimp only [B] at hxgt; linarith)
    change ((iteratedDeriv j
      (GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H -
        GaloisForLFunctions.HTGeometry.smoothWeight N H) x : ℝ) : ℂ) * _ = 0
    rw [iteratedDeriv_sub (smoothWeight_contDiff (N + H) H).contDiffAt
      (smoothWeight_contDiff N H).contDiffAt, hplus, hbase, sub_self]
    simp
  have hwidej : (∫ x in a..b, fj x) = ∫ x in N..B, fj x := by
    have h₁ := intervalIntegral.integral_add_adjacent_intervals hIleftj hImidj
    have h₂ := intervalIntegral.integral_add_adjacent_intervals
      (hIleftj.trans hImidj) hIrightj
    rw [hleftj, zero_add] at h₁
    rw [← h₁, hrightj, add_zero] at h₂
    exact h₂.symm
  have hMellinMid :
      mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s =
        (-1) ^ j / (∏ i ∈ Finset.range j, (s + (i : ℂ))) *
          ∫ x in N..B, ((iteratedDeriv j W x : ℝ) : ℂ) *
            (x : ℂ) ^ (s + (j : ℂ) - 1) := by
    rw [hMellinParts]
    change _ = _ * ∫ x in N..B, fj x
    rw [hwidej]
  let P : ℂ := ∏ i ∈ Finset.range j, (s + (i : ℂ))
  have hPne : P ≠ 0 := by
    dsimp only [P]
    exact Finset.prod_ne_zero_iff.mpr fun i hi => hsne i hi
  have hprod : |t| ^ j ≤ ‖P‖ := by
    dsimp only [P]
    rw [Complex.norm_prod]
    calc
      |t| ^ j = ∏ _i ∈ Finset.range j, |t| := by simp
      _ ≤ ∏ i ∈ Finset.range j, ‖s + (i : ℂ)‖ := by
        apply Finset.prod_le_prod
        · intro i hi
          exact abs_nonneg t
        · intro i hi
          have him : t = (s + (i : ℂ)).im := by simp [s]
          rw [him]
          exact Complex.abs_im_le_norm _
  have hPpos : 0 < ‖P‖ := norm_pos_iff.mpr hPne
  have hquot : |t| ^ j / ‖P‖ ≤ 1 := (div_le_one hPpos).mpr hprod
  let J : ℂ := ∫ x in N..B, ((iteratedDeriv j W x : ℝ) : ℂ) *
    (x : ℂ) ^ (s + (j : ℂ) - 1)
  have hMellinBound :
      |t| ^ j *
          ‖mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s‖
        ≤ ‖J‖ := by
    have hEq : mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s =
        (-1) ^ j / P * J := by simpa only [P, J] using hMellinMid
    rw [hEq, norm_mul, norm_div, norm_pow]
    norm_num
    calc
      |t| ^ j * (‖P‖⁻¹ * ‖J‖) = (|t| ^ j / ‖P‖) * ‖J‖ := by ring
      _ ≤ 1 * ‖J‖ := mul_le_mul_of_nonneg_right hquot (norm_nonneg J)
      _ = ‖J‖ := one_mul _
  have hJBound : ‖J‖ ≤ Cj * H / H ^ j *
      (3 * N) ^ (sigma + (j : ℝ) - 1) := by
    simpa only [J, W, s, B] using hIntBound sigma N H t hN hH hHN hexp
  rw [routeTNormalizedSmoothWindowMellin]
  have hnormInv : ‖(H : ℂ)⁻¹‖ = H⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  rw [norm_mul, hnormInv]
  calc
    |t| ^ j * (H⁻¹ *
        ‖mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s‖) =
        H⁻¹ * (|t| ^ j *
          ‖mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s‖) := by ring
    _ ≤ H⁻¹ * ‖J‖ := mul_le_mul_of_nonneg_left hMellinBound (by positivity)
    _ ≤ H⁻¹ * (Cj * H / H ^ j * (3 * N) ^ (sigma + (j : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hJBound (by positivity)
    _ = Cj * (3 * N) ^ (sigma + (j : ℝ) - 1) / H ^ j := by
      field_simp [hH.ne']

/-- Explicit quadratic derivative growth on the zero-free line `Re s = -1/2`. -/
theorem norm_deriv_riemannZeta_negative_half_le
    {t : ℝ} (ht : 3 ≤ |t|) :
    ‖deriv riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
      160 * Real.exp 4 * (1 + |t|) ^ 2 := by
  let s : ℂ := (-1 / 2 : ℂ) + (t : ℂ) * I
  let R : ℝ := 1 / 2
  have hR : 0 < R := by norm_num [R]
  have hsre : s.re = -1 / 2 := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hne : ∀ w ∈ closedBall s R, w ≠ 1 := by
    intro w hw hweq
    rw [mem_closedBall, Complex.dist_eq, hweq] at hw
    have hre := Complex.abs_re_le_norm ((1 : ℂ) - s)
    have hreval : |((1 : ℂ) - s).re| = 3 / 2 := by
      rw [Complex.sub_re, hsre]
      norm_num
    rw [hreval] at hre
    dsimp only [R] at hw
    linarith
  have hsphere : ∀ w ∈ sphere s R,
      ‖riemannZeta w‖ ≤ 80 * Real.exp 4 * (1 + |t|) ^ 2 := by
    intro w hw
    rw [mem_sphere, Complex.dist_eq] at hw
    have hreNorm := Complex.abs_re_le_norm (w - s)
    have himNorm := Complex.abs_im_le_norm (w - s)
    rw [hw] at hreNorm himNorm
    have hwreLow : -1 ≤ w.re := by
      have hdiff : |w.re - s.re| ≤ R := by simpa using hreNorm
      rw [hsre] at hdiff
      dsimp only [R] at hdiff
      have hb := abs_le.mp hdiff
      linarith [hb.1]
    have hwreHigh : w.re ≤ 5 / 2 := by
      have hdiff : |w.re - s.re| ≤ R := by simpa using hreNorm
      rw [hsre] at hdiff
      dsimp only [R] at hdiff
      have hb := abs_le.mp hdiff
      linarith [hb.2]
    have hwimLower : 2 ≤ |w.im| := by
      have hdiff : |w.im - s.im| ≤ R := by simpa using himNorm
      rw [hsim] at hdiff
      have htri : |t| ≤ |w.im| + |w.im - t| := by
        calc
          |t| = |w.im - (w.im - t)| := by ring_nf
          _ ≤ |w.im| + |w.im - t| := abs_sub _ _
      dsimp only [R] at hdiff
      linarith
    have hwimUpper : 1 + |w.im| ≤ 2 * (1 + |t|) := by
      have hdiff : |w.im - s.im| ≤ R := by simpa using himNorm
      rw [hsim] at hdiff
      have htri : |w.im| ≤ |w.im - t| + |t| := by
        calc
          |w.im| = |(w.im - t) + t| := by ring_nf
          _ ≤ |w.im - t| + |t| := abs_add_le _ _
      dsimp only [R] at hdiff
      linarith [abs_nonneg t]
    have hbase := RHTower.norm_riemannZeta_le_titchmarsh_strip hwreLow hwreHigh hwimLower
    have hweta : (w.re : ℂ) + (w.im : ℂ) * I = w := by
      apply Complex.ext <;> simp
    rw [hweta] at hbase
    calc
      ‖riemannZeta w‖ ≤ 20 * Real.exp 4 * (1 + |w.im|) ^ 2 := hbase
      _ ≤ 20 * Real.exp 4 * (2 * (1 + |t|)) ^ 2 := by gcongr
      _ = 80 * Real.exp 4 * (1 + |t|) ^ 2 := by ring
  have hcauchy := norm_deriv_riemannZeta_le hR hne hsphere
  dsimp only [R] at hcauchy
  change ‖deriv riemannZeta s‖ ≤ _
  calc
    ‖deriv riemannZeta s‖ ≤ (80 * Real.exp 4 * (1 + |t|) ^ 2) / (1 / 2) := hcauchy
    _ = 160 * Real.exp 4 * (1 + |t|) ^ 2 := by ring

/-- Coarse uniform inverse-zeta bound on `Re s = -1/2` above Titchmarsh height. -/
theorem norm_inv_riemannZeta_negative_half_le
    {t : ℝ} (ht : 9 ≤ |t|) :
    ‖(riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ 8 ^ 4 * 6048 := by
  let T : ℝ := |t|
  let z : ℂ := RHTower.smoothAFEZetaLeftLinePt t
  let D : ℝ := 8 ^ 4 * 6048
  have hT : 9 ≤ T := ht
  have hTpos : 0 < T := by linarith
  have hlogpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogle : Real.log T ≤ T := Real.log_le_self hTpos.le
  have hzNorm : T ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    simpa only [z, RHTower.smoothAFEZetaLeftLinePt_im, T] using h
  have hpi : 2 * Real.pi ≤ 8 := by
    linarith [Real.pi_lt_four]
  have hratio : T / 8 ≤ ‖z‖ / (2 * Real.pi) := by
    have hden : 0 < 2 * Real.pi := by positivity
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) hden]
    calc
      T * (2 * Real.pi) ≤ ‖z‖ * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hzNorm hden.le
      _ ≤ ‖z‖ * 8 := mul_le_mul_of_nonneg_left hpi (norm_nonneg z)
  have hfactor : (1 : ℝ) / (6048 * T) ≤
      (1 / 2 : ℝ) ^ 3 / (756 * Real.log T) := by
    norm_num [div_eq_mul_inv]
    have hinv := inv_anti₀ hlogpos hlogle
    nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ T / 8) hratio 4
  have hmul : (T / 8) ^ 4 * (1 / (6048 * T)) ≤
      (‖z‖ / (2 * Real.pi)) ^ 4 *
        ((1 / 2 : ℝ) ^ 3 / (756 * Real.log T)) :=
    mul_le_mul hpow hfactor (by positivity) (by positivity)
  have hterm := RHTower.titchmarsh_terminal_zeta_lower ht
  have hsimple : (1 : ℝ) / D ≤ ‖riemannZeta z‖ ^ 4 := by
    have hleft : (1 : ℝ) / D ≤ (T / 8) ^ 4 * (1 / (6048 * T)) := by
      dsimp only [D]
      field_simp [hTpos.ne']
      have hT1 : (1 : ℝ) ≤ T := by linarith
      exact one_le_pow₀ hT1
    exact hleft.trans (hmul.trans (by simpa only [z, T] using hterm))
  have hD : (1 : ℝ) ≤ D := by dsimp only [D]; norm_num
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hqpos : 0 < (1 : ℝ) / D := div_pos zero_lt_one hDpos
  have hnormLower : (1 : ℝ) / D ≤ ‖riemannZeta z‖ := by
    let x : ℝ := ‖riemannZeta z‖
    have hx0 : 0 ≤ x := norm_nonneg _
    have hq1 : (1 : ℝ) / D ≤ 1 := (div_le_one hDpos).2 hD
    by_cases hx1 : x ≤ 1
    · have hxx : x ^ 2 ≤ x := by
        nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
      have hx20 : 0 ≤ x ^ 2 := sq_nonneg x
      have hx21 : x ^ 2 ≤ 1 := hxx.trans hx1
      have hxxxx : (x ^ 2) ^ 2 ≤ x ^ 2 := by
        nlinarith [mul_nonneg hx20 (sub_nonneg.mpr hx21)]
      have hx4 : x ^ 4 ≤ x := by
        calc
          x ^ 4 = (x ^ 2) ^ 2 := by ring
          _ ≤ x ^ 2 := hxxxx
          _ ≤ x := hxx
      exact hsimple.trans hx4
    · exact hq1.trans (le_of_not_ge hx1)
  have hnormPos : 0 < ‖riemannZeta z‖ := lt_of_lt_of_le hqpos hnormLower
  have hfinal : ‖(riemannZeta z)⁻¹‖ ≤ D := by
    rw [norm_inv]
    apply (inv_le_iff_one_le_mul₀ hnormPos).2
    calc
      1 = D * (1 / D) := by field_simp
      _ ≤ D * ‖riemannZeta z‖ := mul_le_mul_of_nonneg_left hnormLower hDpos.le
  have hhalf : (((-1 / 2 : ℝ) : ℂ)) = (-1 / 2 : ℂ) := by norm_num
  rw [← hhalf]
  simpa only [z, D, RHTower.smoothAFEZetaLeftLinePt] using hfinal

/-- Explicit quadratic growth for the regular logarithmic derivative on `Re s = -1/2`. -/
theorem norm_zetaLogDerivReg_negative_half_le
    {t : ℝ} (ht : 9 ≤ |t|) :
    ‖zetaLogDerivReg ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
      (160 * Real.exp 4 * (8 ^ 4 * 6048) + 1) * (1 + |t|) ^ 2 := by
  let s : ℂ := (-1 / 2 : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [s] at hre
    norm_num at hre
  have hz0 : riemannZeta s ≠ 0 := by
    have ht0 : t ≠ 0 := by
      intro h
      rw [h, abs_zero] at ht
      linarith
    apply RHTower.riemannZeta_ne_zero_of_re_lt_zero (by dsimp only [s]; norm_num)
    intro n htriv
    apply ht0
    have him := congrArg Complex.im htriv
    have hsIm : s.im = t := by simp [s]
    have hrIm : (-(2 * ((n : ℂ) + 1))).im = 0 := by simp
    rw [hsIm, hrIm] at him
    exact him
  have hderiv := norm_deriv_riemannZeta_negative_half_le (by linarith)
  have hinv := norm_inv_riemannZeta_negative_half_le ht
  have hpole : ‖(s - 1)⁻¹‖ ≤ 1 := by
    have ht0 : t ≠ 0 := by
      intro h
      rw [h, abs_zero] at ht
      linarith
    have hheight := norm_inv_sub_one_le_height (β := -1 / 2) ht0
    have hone : 1 ≤ |t| := by linarith
    have hinvOne : |t|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hone
    dsimp only [s]
    simpa only [show (-1 / 2 : ℂ) = (((-1 / 2 : ℝ) : ℂ)) by norm_num] using
      hheight.trans hinvOne
  have hreg := norm_zetaLogDerivReg_le hs1 hz0
  have hprod :
      ‖deriv riemannZeta s‖ * ‖(riemannZeta s)⁻¹‖ ≤
        (160 * Real.exp 4 * (8 ^ 4 * 6048)) * (1 + |t|) ^ 2 := by
    calc
      ‖deriv riemannZeta s‖ * ‖(riemannZeta s)⁻¹‖ ≤
          (160 * Real.exp 4 * (1 + |t|) ^ 2) * (8 ^ 4 * 6048) :=
        mul_le_mul hderiv hinv (norm_nonneg _) (by positivity)
      _ = (160 * Real.exp 4 * (8 ^ 4 * 6048)) * (1 + |t|) ^ 2 := by ring
  have hpow : 1 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
  calc
    ‖zetaLogDerivReg ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ = ‖zetaLogDerivReg s‖ := by rfl
    _ ≤ ‖deriv riemannZeta s‖ * ‖(riemannZeta s)⁻¹‖ + ‖(s - 1)⁻¹‖ := hreg
    _ ≤ (160 * Real.exp 4 * (8 ^ 4 * 6048)) * (1 + |t|) ^ 2 + 1 :=
      add_le_add hprod hpole
    _ ≤ (160 * Real.exp 4 * (8 ^ 4 * 6048) + 1) * (1 + |t|) ^ 2 := by
      nlinarith [show 0 ≤ 160 * Real.exp 4 * (8 ^ 4 * 6048) by positivity]

/-- High-height product bound: fourth-order Mellin decay beats quadratic zeta growth. -/
theorem exists_bound_zetaLogDerivReg_mul_routeTKernel_negative_half_high :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N H t : ℝ, 0 < N → 0 < H → H ≤ N → 9 ≤ |t| →
      ‖zetaLogDerivReg ((-1 / 2 : ℂ) + (t : ℂ) * I) *
          routeTNormalizedSmoothWindowMellin N H ((-1 / 2 : ℂ) + (t : ℂ) * I)‖
        ≤ C * (3 * N) ^ (5 / 2 : ℝ) / (H ^ 4 * |t| ^ 2) := by
  obtain ⟨Ck, hCk, hk⟩ :=
    exists_bound_routeTNormalizedSmoothWindowMellin_line 4
  let Cz : ℝ := 160 * Real.exp 4 * (8 ^ 4 * 6048) + 1
  refine ⟨4 * Cz * Ck, by dsimp only [Cz]; positivity,
    fun N H t hN hH hHN ht => ?_⟩
  have htpos : 0 < |t| := by linarith
  have hz := norm_zetaLogDerivReg_negative_half_le ht
  have hz' : ‖zetaLogDerivReg ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
      4 * Cz * |t| ^ 2 := by
    have hone : 1 ≤ |t| := by linarith
    have hlin : 1 + |t| ≤ 2 * |t| := by linarith
    calc
      ‖zetaLogDerivReg ((-1 / 2 : ℂ) + (t : ℂ) * I)‖
          ≤ Cz * (1 + |t|) ^ 2 := by simpa only [Cz] using hz
      _ ≤ Cz * (2 * |t|) ^ 2 := by gcongr
      _ = 4 * Cz * |t| ^ 2 := by ring
  have hk0 := hk (-1 / 2) N H t hN hH hHN (by norm_num) (by norm_num) htpos
  have hk' :
      ‖routeTNormalizedSmoothWindowMellin N H ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
        Ck * (3 * N) ^ (5 / 2 : ℝ) / (H ^ 4 * |t| ^ 4) := by
    have hpowpos : 0 < |t| ^ 4 := pow_pos htpos _
    have hdeneq : Ck * (3 * N) ^ (5 / 2 : ℝ) / (H ^ 4 * |t| ^ 4) =
        (Ck * (3 * N) ^ (5 / 2 : ℝ) / H ^ 4) / |t| ^ 4 := by
      field_simp [hH.ne', htpos.ne']
    rw [hdeneq]
    apply (le_div_iff₀ hpowpos).2
    have hhalf : (((-1 / 2 : ℝ) : ℂ)) = (-1 / 2 : ℂ) := by norm_num
    rw [← hhalf]
    calc
      ‖routeTNormalizedSmoothWindowMellin N H
          (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ * |t| ^ 4 =
          |t| ^ 4 * ‖routeTNormalizedSmoothWindowMellin N H
            (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := mul_comm _ _
      _ ≤ Ck * (3 * N) ^ ((-1 / 2 : ℝ) + (4 : ℝ) - 1) / H ^ 4 := hk0
      _ = Ck * (3 * N) ^ (5 / 2 : ℝ) / H ^ 4 := by norm_num
  rw [norm_mul]
  calc
    ‖zetaLogDerivReg ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ *
        ‖routeTNormalizedSmoothWindowMellin N H ((-1 / 2 : ℂ) + (t : ℂ) * I)‖
        ≤ (4 * Cz * |t| ^ 2) *
          (Ck * (3 * N) ^ (5 / 2 : ℝ) / (H ^ 4 * |t| ^ 4)) :=
      mul_le_mul hz' hk' (norm_nonneg _) (by positivity)
    _ = (4 * Cz * Ck) * (3 * N) ^ (5 / 2 : ℝ) / (H ^ 4 * |t| ^ 2) := by
      field_simp [htpos.ne']

/-- Compact-height bound for the same regular logarithmic derivative. -/
theorem exists_bound_zetaLogDerivReg_negative_half_compact :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 9 →
      ‖zetaLogDerivReg ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  let g : ℝ → ℝ := fun t =>
    ‖zetaLogDerivReg ((-1 / 2 : ℂ) + (t : ℂ) * I)‖
  have hgcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro t
    let s : ℂ := (-1 / 2 : ℂ) + (t : ℂ) * I
    have hs1 : s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      dsimp only [s] at hre
      norm_num at hre
    have hz0 : riemannZeta s ≠ 0 := by
      apply RHTower.riemannZeta_ne_zero_of_re_lt_zero (by dsimp only [s]; norm_num)
      intro n htriv
      have hre := congrArg Complex.re htriv
      have hsRe : s.re = -1 / 2 := by simp [s]
      have hrRe : (-(2 * ((n : ℂ) + 1))).re = -2 * ((n : ℝ) + 1) := by simp
      rw [hsRe, hrRe] at hre
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hG : zetaResidueUnit s ≠ 0 := (zetaResidueUnit_ne_zero_iff hs1).2 hz0
    have hinner : ContinuousAt (fun u : ℝ => (-1 / 2 : ℂ) + (u : ℂ) * I) t := by
      fun_prop
    have hcomp := (differentiableAt_zetaLogDerivReg hG).continuousAt.comp_of_eq hinner rfl
    simpa only [g, s, Function.comp_apply] using hcomp.norm
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (-9 : ℝ) ≤ 9)) hgcont.continuousOn
  refine ⟨max (g t₀) 0, le_max_right _ _, fun t ht => ?_⟩
  have htmem : t ∈ Set.Icc (-9 : ℝ) 9 := by rw [Set.mem_Icc]; exact abs_le.mp ht
  exact (hmax htmem).trans (le_max_left _ _)

/-- Whole truncated left edge, with separated compact and high-height scale laws. -/
theorem exists_bound_routeT_zetaLogDerivReg_negative_half_edge :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ N H T : ℝ,
      0 < N → 0 < H → H ≤ N → 9 ≤ T →
      ‖∫ t in (-T)..T,
          zetaLogDerivReg ((-1 / 2 : ℂ) + (t : ℂ) * I) *
            routeTNormalizedSmoothWindowMellin N H
              ((-1 / 2 : ℂ) + (t : ℂ) * I)‖
        ≤ 2 * T *
          (A * N ^ (-(3 / 2 : ℝ)) +
            B * (3 * N) ^ (5 / 2 : ℝ) / H ^ 4) := by
  obtain ⟨A, hA, hlow⟩ := exists_bound_zetaLogDerivReg_negative_half_compact
  obtain ⟨B, hB, hhigh⟩ :=
    exists_bound_zetaLogDerivReg_mul_routeTKernel_negative_half_high
  refine ⟨A, B, hA, hB, fun N H T hN hH hHN hT => ?_⟩
  let f : ℝ → ℂ := fun t =>
    zetaLogDerivReg ((-1 / 2 : ℂ) + (t : ℂ) * I) *
      routeTNormalizedSmoothWindowMellin N H ((-1 / 2 : ℂ) + (t : ℂ) * I)
  let C : ℝ := A * N ^ (-(3 / 2 : ℝ)) +
    B * (3 * N) ^ (5 / 2 : ℝ) / H ^ 4
  have hpoint : ∀ t : ℝ, ‖f t‖ ≤ C := by
    intro t
    by_cases htlow : |t| ≤ 9
    · have hz := hlow t htlow
      have hk := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
        hN hH (s := ((-1 / 2 : ℂ) + (t : ℂ) * I)) (by norm_num)
      have hk' : ‖routeTNormalizedSmoothWindowMellin N H
          ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ N ^ (-(3 / 2 : ℝ)) := by
        convert hk using 1; norm_num
      have hmul : ‖f t‖ ≤ A * N ^ (-(3 / 2 : ℝ)) := by
        rw [norm_mul]
        exact mul_le_mul hz hk' (norm_nonneg _) hA
      exact hmul.trans (le_add_of_nonneg_right (by positivity))
    · have ht : 9 ≤ |t| := le_of_not_ge htlow
      have hraw := hhigh N H t hN hH hHN ht
      have ht2 : 1 ≤ |t| ^ 2 := by
        have : (1 : ℝ) ≤ |t| := by linarith
        exact one_le_pow₀ this
      have hcollapse :
          B * (3 * N) ^ (5 / 2 : ℝ) / (H ^ 4 * |t| ^ 2) ≤
            B * (3 * N) ^ (5 / 2 : ℝ) / H ^ 4 := by
        have hnum : 0 ≤ B * (3 * N) ^ (5 / 2 : ℝ) := by positivity
        have hH4 : 0 < H ^ 4 := pow_pos hH _
        calc
          B * (3 * N) ^ (5 / 2 : ℝ) / (H ^ 4 * |t| ^ 2) =
              (B * (3 * N) ^ (5 / 2 : ℝ) / H ^ 4) / |t| ^ 2 := by
                field_simp [hH.ne', (show t ≠ 0 by
                  intro h; rw [h, abs_zero] at ht; linarith)]
          _ ≤ B * (3 * N) ^ (5 / 2 : ℝ) / H ^ 4 :=
            div_le_self (div_nonneg hnum hH4.le) ht2
      exact hraw.trans (hcollapse.trans (le_add_of_nonneg_left (by positivity)))
  have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := f) (C := C) (a := -T) (b := T) (fun t _ht => hpoint t)
  change ‖∫ t in (-T)..T, f t‖ ≤ _
  calc
    ‖∫ t in (-T)..T, f t‖ ≤ C * |T - -T| := hInt
    _ = 2 * T * C := by
      rw [abs_of_pos (by linarith : 0 < T - -T)]
      ring

/-- Exact compact-height spatial exponent under the buffered Route-T schedule. -/
theorem routeT_negative_half_compact_scale_eq
    {X : ℕ} (hX : 1 ≤ X) :
    (X : ℝ) * inghamRouteTMellinPhysicalCenter X ^ (-(3 / 2 : ℝ)) =
      (X : ℝ) ^ (-(1201 / 299 : ℝ)) := by
  have hx : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  unfold inghamRouteTMellinPhysicalCenter
  calc
    (X : ℝ) * ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^ (-(3 / 2 : ℝ)) =
        (X : ℝ) ^ (1 : ℝ) *
          (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (-(3 / 2 : ℝ))) := by
            rw [Real.rpow_one, Real.rpow_mul hx.le]
    _ = (X : ℝ) ^
        (1 + inghamRouteTPhysicalScaleExponent * (-(3 / 2 : ℝ))) := by
          rw [← Real.rpow_add hx]
    _ = (X : ℝ) ^ (-(1201 / 299 : ℝ)) := by
      congr 1
      unfold inghamRouteTPhysicalScaleExponent
      norm_num

/-- Exact high-height spatial exponent under the buffered Route-T schedule. -/
theorem routeT_negative_half_high_scale_eq
    {X : ℕ} (hX : 1 ≤ X) :
    (X : ℝ) *
        (3 * inghamRouteTMellinPhysicalCenter X) ^ (5 / 2 : ℝ) /
          inghamRouteTMellinBufferedPhysicalWidth X ^ 4 =
      3 ^ (5 / 2 : ℝ) * (X : ℝ) ^ (-(1549 / 74750 : ℝ)) := by
  have hx : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  let a : ℝ := inghamRouteTPhysicalScaleExponent
  let b : ℝ := inghamRouteTMellinBufferedFrequencyExponent
  have hN : inghamRouteTMellinPhysicalCenter X = (X : ℝ) ^ a := by
    rfl
  have hF : inghamRouteTMellinBufferedFrequency X = (X : ℝ) ^ b := by
    rfl
  have hH : inghamRouteTMellinBufferedPhysicalWidth X = (X : ℝ) ^ (a - b) := by
    rw [inghamRouteTMellinBufferedPhysicalWidth, hN, hF, Real.rpow_sub hx]
  rw [hN, hH]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3)
    (Real.rpow_nonneg hx.le a)]
  rw [← Real.rpow_mul hx.le a (5 / 2 : ℝ)]
  rw [← Real.rpow_mul_natCast hx.le (a - b) 4]
  have hmul :
      (X : ℝ) * (X : ℝ) ^ (a * (5 / 2 : ℝ)) =
        (X : ℝ) ^ (1 + a * (5 / 2 : ℝ)) := by
    calc
      (X : ℝ) * (X : ℝ) ^ (a * (5 / 2 : ℝ)) =
          (X : ℝ) ^ (1 : ℝ) * (X : ℝ) ^ (a * (5 / 2 : ℝ)) := by
            rw [Real.rpow_one]
      _ = (X : ℝ) ^ (1 + a * (5 / 2 : ℝ)) :=
        (Real.rpow_add hx (1 : ℝ) (a * (5 / 2 : ℝ))).symm
  calc
    (X : ℝ) * (3 ^ (5 / 2 : ℝ) * (X : ℝ) ^ (a * (5 / 2 : ℝ))) /
        (X : ℝ) ^ ((a - b) * (4 : ℝ)) =
      3 ^ (5 / 2 : ℝ) *
        ((X : ℝ) ^ (1 + a * (5 / 2 : ℝ)) /
          (X : ℝ) ^ ((a - b) * (4 : ℝ))) := by
        rw [← hmul]
        ring
    _ = 3 ^ (5 / 2 : ℝ) *
        (X : ℝ) ^ (1 + a * (5 / 2 : ℝ) - (a - b) * 4) := by
      rw [Real.rpow_sub hx]
    _ = 3 ^ (5 / 2 : ℝ) * (X : ℝ) ^ (-(1549 / 74750 : ℝ)) := by
      congr 2
      dsimp only [a, b]
      unfold inghamRouteTPhysicalScaleExponent inghamRouteTMellinBufferedFrequencyExponent
      norm_num

/-- Regular logarithmic-derivative contribution on the scheduled `Re s = -1/2` left edge. -/
def inghamRouteTBufferedNegativeHalfLeftEdge (X : ℕ) : ℂ :=
  ∫ t in (-(X : ℝ))..(X : ℝ),
    zetaLogDerivReg ((-1 / 2 : ℂ) + (t : ℂ) * I) *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        ((-1 / 2 : ℂ) + (t : ℂ) * I)

/-- The complete scheduled left edge vanishes unconditionally. -/
theorem tendsto_inghamRouteTBufferedNegativeHalfLeftEdge_zero :
    Tendsto inghamRouteTBufferedNegativeHalfLeftEdge atTop (𝓝 0) := by
  obtain ⟨A, B, hA, hB, hedge⟩ :=
    exists_bound_routeT_zetaLogDerivReg_negative_half_edge
  have hcoreLow : Tendsto (fun X : ℕ => (X : ℝ) ^ (-(1201 / 299 : ℝ)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1201 / 299)).comp
      tendsto_natCast_atTop_atTop
  have hcoreHigh : Tendsto (fun X : ℕ => (X : ℝ) ^ (-(1549 / 74750 : ℝ)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1549 / 74750)).comp
      tendsto_natCast_atTop_atTop
  have hscaled : Tendsto (fun X : ℕ =>
      (2 * A) * (X : ℝ) ^ (-(1201 / 299 : ℝ)) +
        (2 * B * 3 ^ (5 / 2 : ℝ)) *
          (X : ℝ) ^ (-(1549 / 74750 : ℝ))) atTop (𝓝 0) := by
    convert (hcoreLow.const_mul (2 * A)).add
      (hcoreHigh.const_mul (2 * B * 3 ^ (5 / 2 : ℝ))) using 1; simp
  have hupper : Tendsto (fun X : ℕ =>
      2 * (X : ℝ) *
        (A * inghamRouteTMellinPhysicalCenter X ^ (-(3 / 2 : ℝ)) +
          B * (3 * inghamRouteTMellinPhysicalCenter X) ^ (5 / 2 : ℝ) /
            inghamRouteTMellinBufferedPhysicalWidth X ^ 4)) atTop (𝓝 0) := by
    refine hscaled.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hlo := routeT_negative_half_compact_scale_eq hX
    have hhi := routeT_negative_half_high_scale_eq hX
    symm
    calc
      2 * (X : ℝ) *
          (A * inghamRouteTMellinPhysicalCenter X ^ (-(3 / 2 : ℝ)) +
            B * (3 * inghamRouteTMellinPhysicalCenter X) ^ (5 / 2 : ℝ) /
              inghamRouteTMellinBufferedPhysicalWidth X ^ 4) =
          2 * A * ((X : ℝ) *
            inghamRouteTMellinPhysicalCenter X ^ (-(3 / 2 : ℝ))) +
          2 * B * ((X : ℝ) *
            (3 * inghamRouteTMellinPhysicalCenter X) ^ (5 / 2 : ℝ) /
              inghamRouteTMellinBufferedPhysicalWidth X ^ 4) := by ring
      _ = 2 * A * (X : ℝ) ^ (-(1201 / 299 : ℝ)) +
          2 * B * (3 ^ (5 / 2 : ℝ) *
            (X : ℝ) ^ (-(1549 / 74750 : ℝ))) := by rw [hlo, hhi]
      _ = (2 * A) * (X : ℝ) ^ (-(1201 / 299 : ℝ)) +
          (2 * B * 3 ^ (5 / 2 : ℝ)) *
            (X : ℝ) ^ (-(1549 / 74750 : ℝ)) := by ring
  have hnorm : Tendsto (fun X : ℕ =>
      ‖inghamRouteTBufferedNegativeHalfLeftEdge X‖) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards with X
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop (9 : ℕ)] with X hX
      have hX1 : 1 ≤ X := by omega
      have hXR : (9 : ℝ) ≤ X := by exact_mod_cast hX
      simpa only [inghamRouteTBufferedNegativeHalfLeftEdge] using
        hedge (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) (X : ℝ)
          (inghamRouteTMellinPhysicalCenter_pos hX1)
          (inghamRouteTMellinBufferedPhysicalWidth_pos hX1)
          (inghamRouteTMellinBufferedPhysicalWidth_le_center hX1) hXR
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

end


end RHTower.Sieve
