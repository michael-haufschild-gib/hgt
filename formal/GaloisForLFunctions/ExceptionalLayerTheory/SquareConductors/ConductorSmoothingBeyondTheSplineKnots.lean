import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFifteenSixteenthsProductWindow

/-!
# Two-variable conductor-mesh smoothing beyond the B-spline knot barrier

For any pair of monotone product cutoffs `u(n) ≤ w(n)` in the detached subquadratic
regime, the conductors `n ∈ (N, M]` admitting a given pair `(p, v)` form one
contiguous integer interval `[a, d)`. Trapezoidal Euler-Maclaurin summation across
`[a, d)` replaces the discrete conductor sum by its antiderivative in `n`, raising
regularity from `C^{6,1}` (`dyadicSpline`) to `C^{7,1}` (`conductorSplineIntegral`)
with ninth-order off-knot smoothness, while charging only the two interval endpoints
at eighth order and the interior curvature at fifth order.
-/

noncomputable section
open Finset ArithmeticFunction MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.CountingHolography.Sections
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Admissible conductors of any monotone shell form a single contiguous interval `Ico a d`. -/
theorem monotone_shell_conductors {u w : ℕ → ℕ} (hu : Monotone u) (hw : Monotone w)
    {N M : ℕ} (hNM : N ≤ M) (q v : ℕ) :
    ∃ a d : ℕ, N < a ∧ a ≤ d ∧ d ≤ M + 1 ∧
      (Ioc N M).filter (fun n => v ≤ n ∧ u n < q ∧ q ≤ w n) = Ico a d := by
  let S := (Ioc N M).filter (fun n => v ≤ n ∧ u n < q ∧ q ≤ w n)
  by_cases hne : S.Nonempty
  · let a := S.min' hne
    let d := S.max' hne + 1
    have ha_mem : a ∈ S := min'_mem S hne
    have hc_mem : S.max' hne ∈ S := max'_mem S hne
    obtain ⟨⟨haN, _⟩, hav, _, haq⟩ := mem_filter.mp ha_mem |>.imp mem_Ioc.mp id
    obtain ⟨⟨_, hcM⟩, _, hcq, _⟩ := mem_filter.mp hc_mem |>.imp mem_Ioc.mp id
    refine ⟨a, d, haN, Nat.le_succ_of_le (min'_le S _ hc_mem), Nat.succ_le_succ hcM, ?_⟩
    ext n
    change n ∈ S ↔ n ∈ Ico a d
    simp only [mem_Ico]
    constructor
    · intro hn
      exact ⟨min'_le S n hn, Nat.lt_succ_of_le (le_max' S n hn)⟩
    · rintro ⟨han, hnd⟩
      have hnc : n ≤ S.max' hne := Nat.le_of_lt_succ hnd
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨haN.trans_le han, hnc.trans hcM⟩,
        hav.trans han, (hu hnc).trans_lt hcq, haq.trans (hw han)⟩
  · rw [not_nonempty_iff_eq_empty] at hne
    refine ⟨N + 1, N + 1, Nat.lt_succ_self N, le_rfl, Nat.succ_le_succ hNM, ?_⟩
    change S = _
    rw [hne, Ico_self]

private theorem trapezoidal_step {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) :
    (g n + g (n + 1 : ℕ)) / 2 - (∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), g t) =
      -∫ s in (0 : ℝ)..1, (s * (s - 1) / 2) * iteratedDeriv 2 g ((n : ℝ) + s) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let f_pos := fun u : ℝ => g (max (1 / 2 : ℝ) ((n : ℝ) + u))
  have hf_cont : Continuous f_pos := by
    refine hg.continuousOn.comp_continuous (continuous_const.max (continuous_const.add continuous_id))
      fun u => (by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_left _ _)
  have hf_eq : ∀ u : ℝ, -1 / 2 < u → f_pos u = g ((n : ℝ) + u) := fun u hu => by
    dsimp only [f_pos]
    rw [max_eq_right (by linarith)]
  let K := fun s : ℝ =>
    (s - 1 / 2) * g ((n : ℝ) + s) - (s * (s - 1) / 2) * deriv g ((n : ℝ) + s) -
      ∫ u in (0 : ℝ)..s, f_pos u
  have hd_g1 : ContDiffOn ℝ 1 (deriv g) (Set.Ioi 0) :=
    hg.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdK : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt K (-((s * (s - 1) / 2) * iteratedDeriv 2 g ((n : ℝ) + s))) s := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have ht0 : (0 : ℝ) < (n : ℝ) + s := by linarith [hs.1]
    have hshift : HasDerivAt (fun r : ℝ => (n : ℝ) + r) 1 s :=
      (hasDerivAt_id s).const_add (n : ℝ)
    have hdg : HasDerivAt g (deriv g ((n : ℝ) + s)) ((n : ℝ) + s) :=
      ((hg.differentiableOn (by simp) _ ht0).differentiableAt (isOpen_Ioi.mem_nhds ht0)).hasDerivAt
    have hddg : HasDerivAt (deriv g) (iteratedDeriv 2 g ((n : ℝ) + s)) ((n : ℝ) + s) := by
      have hd := ((hd_g1.differentiableOn (by simp) _ ht0).differentiableAt
        (isOpen_Ioi.mem_nhds ht0)).hasDerivAt
      rwa [show deriv (deriv g) ((n : ℝ) + s) = iteratedDeriv 2 g ((n : ℝ) + s) by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]] at hd
    have h1 : HasDerivAt (fun r => (r - 1 / 2) * g ((n : ℝ) + r))
        (1 * g ((n : ℝ) + s) + (s - 1 / 2) * (deriv g ((n : ℝ) + s) * 1)) s :=
      ((hasDerivAt_id s).sub_const (1 / 2)).mul (hdg.comp s hshift)
    have hpoly : HasDerivAt (fun r : ℝ => r * (r - 1) / 2) (s - 1 / 2) s := by
      have h := ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).div_const 2
      exact h.congr_deriv (by dsimp only [id]; ring)
    have h2 : HasDerivAt (fun r => (r * (r - 1) / 2) * deriv g ((n : ℝ) + r))
        ((s - 1 / 2) * deriv g ((n : ℝ) + s) +
          (s * (s - 1) / 2) * (iteratedDeriv 2 g ((n : ℝ) + s) * 1)) s :=
      hpoly.mul (hddg.comp s hshift)
    have h3 : HasDerivAt (fun r => ∫ u in (0 : ℝ)..r, f_pos u) (g ((n : ℝ) + s)) s := by
      rw [← hf_eq s (by linarith [hs.1])]
      exact (hf_cont.integral_hasStrictDerivAt 0 s).hasDerivAt
    exact ((h1.sub h2).sub h3).congr_deriv (by ring)
  have hint_rhs : IntervalIntegrable
      (fun s : ℝ => -((s * (s - 1) / 2) * iteratedDeriv 2 g ((n : ℝ) + s))) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    have hcd2 : ContinuousOn (iteratedDeriv 2 g) (Set.Ioi 0) := by
      have hc := hd_g1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
      rwa [show deriv (deriv g) = iteratedDeriv 2 g by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]] at hc
    refine ContinuousOn.neg (((continuousOn_id.mul (continuousOn_id.sub continuousOn_const)).div_const 2).mul ?_)
    exact hcd2.comp (continuousOn_const.add continuousOn_id) fun s hs => by linarith [hs.1, hn']
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hdK hint_rhs
  rw [intervalIntegral.integral_neg] at hftc
  have hint_eq : (∫ u in (0 : ℝ)..1, f_pos u) = ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), g t := by
    have hcongr : ∫ u in (0 : ℝ)..1, f_pos u = ∫ u in (0 : ℝ)..1, g ((n : ℝ) + u) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le zero_le_one] at hu
      exact hf_eq u (by linarith [hu.1])
    rw [hcongr, intervalIntegral.integral_comp_add_left g (n : ℝ), add_zero]
    push_cast
  have hK1 : K 1 = (1 / 2 : ℝ) * g (n + 1 : ℕ) - ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), g t := by
    dsimp only [K]
    rw [hint_eq]
    push_cast
    ring
  have hK0 : K 0 = -(1 / 2 : ℝ) * g n := by
    dsimp only [K]; simp; ring
  rw [hK1, hK0] at hftc
  linarith

/-- Trapezoidal Euler-Maclaurin formula on `Ico a d` (`0 < a ≤ d`). -/
theorem trapezoidal_euler_maclaurin_Ico {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) :
    (∑ n ∈ Ico a d, g n) =
      (∫ t in (a : ℝ)..d, g t) - (g d - g a) / 2 -
        ∑ n ∈ Ico a d, ∫ s in (0 : ℝ)..1,
          (s * (s - 1) / 2) * iteratedDeriv 2 g ((n : ℝ) + s) := by
  induction d, had using Nat.le_induction with
  | base => simp
  | succ d had ih =>
    rw [Finset.sum_Ico_succ_top had, Finset.sum_Ico_succ_top had, ih]
    have hd_pos : 0 < d := ha.trans_le had
    have hstep := trapezoidal_step hg hd_pos
    have hint1 : IntervalIntegrable g volume (a : ℝ) (d : ℝ) := by
      refine (hg.continuousOn.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le (by exact_mod_cast had : (a : ℝ) ≤ d)]
      intro t ht; exact (Nat.cast_pos.mpr ha).trans_le ht.1
    have hint2 : IntervalIntegrable g volume (d : ℝ) ((d + 1 : ℕ) : ℝ) := by
      refine (hg.continuousOn.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le (by push_cast; linarith : (d : ℝ) ≤ (d + 1 : ℕ))]
      intro t ht; exact (Nat.cast_pos.mpr hd_pos).trans_le ht.1
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    linarith

private theorem bdiff_iter_sub (r : ℕ) (f g : ℕ → ℝ) :
    bdiff^[r] (fun j => f j - g j) = fun j => bdiff^[r] f j - bdiff^[r] g j := by
  induction r with
  | zero => rfl
  | succ r ih =>
    funext j
    simp only [Function.iterate_succ_apply', ih, bdiff]
    ring

private theorem bdiff_iter_const_mul (r : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    bdiff^[r] (fun j => c * f j) = fun j => c * bdiff^[r] f j := by
  induction r with
  | zero => rfl
  | succ r ih =>
    funext j
    simp only [Function.iterate_succ_apply', ih, bdiff]
    ring

private theorem bdiff_iter_intervalIntegral (r : ℕ) (H : ℕ → ℝ → ℝ)
    (hcont : ∀ j, ContinuousOn (H j) (Set.Icc 0 1)) (j : ℕ) :
    bdiff^[r] (fun i => ∫ s in (0 : ℝ)..1, H i s) j =
      ∫ s in (0 : ℝ)..1, bdiff^[r] (fun i => H i s) j := by
  induction r generalizing j with
  | zero => rfl
  | succ r ih =>
    simp only [Function.iterate_succ_apply', bdiff]
    rw [ih j, ih (j + 1)]
    have hi1 : ContinuousOn (fun s => bdiff^[r] (fun i => H i s) j) (Set.Icc 0 1) := by
      clear ih
      induction r generalizing j with
      | zero => exact hcont j
      | succ r ihr =>
        have heq : (fun s => bdiff^[r + 1] (fun i => H i s) j) =
            fun s => bdiff^[r] (fun i => H i s) j - bdiff^[r] (fun i => H i s) (j + 1) := by
          funext s; rw [Function.iterate_succ_apply']; rfl
        rw [heq]; exact (ihr j).sub (ihr (j + 1))
    have hi2 : ContinuousOn (fun s => bdiff^[r] (fun i => H i s) (j + 1)) (Set.Icc 0 1) := by
      clear ih hi1
      induction r generalizing j with
      | zero => exact hcont (j + 1)
      | succ r ihr =>
        have heq : (fun s => bdiff^[r + 1] (fun i => H i s) (j + 1)) =
            fun s => bdiff^[r] (fun i => H i s) (j + 1) - bdiff^[r] (fun i => H i s) (j + 2) := by
          funext s; rw [Function.iterate_succ_apply']; rfl
        rw [heq]; exact (ihr (j + 1)).sub (ihr (j + 2))
    rw [← intervalIntegral.integral_sub
      (hi1.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
      (hi2.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable]

/-- Summing `n² · unitHorizonPair n q` across a conductor interval `Ico a d ⊆ (N, 2N]`
gains an extra derivative in the leading integral term, bounding the aggregate by
`O(q⁸ / N¹⁴ + q⁷ / N¹³ + q⁴ / N⁸)`. -/
theorem conductor_interval_horizonPair_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N a d q : ℕ}, 0 < N → N < a → a ≤ d → d ≤ 2 * N + 1 →
      0 < q → 8 * (q : ℝ) < Real.exp (-8) * (N : ℝ) ^ 2 →
      |∑ n ∈ Ico a d, (n : ℝ) ^ 2 * unitHorizonPair n q| ≤
        K * ((q : ℝ) ^ 8 / (N : ℝ) ^ 14 + (q : ℝ) ^ 7 / (N : ℝ) ^ 13 +
          (q : ℝ) ^ 4 / (N : ℝ) ^ 8) := by
  obtain ⟨C7, hC7, hper7⟩ := centeredPrimeWeight_periodic_iter 7
  obtain ⟨C6, hC6, hper6⟩ := centeredPrimeWeight_periodic_iter 6
  obtain ⟨C3, hC3, hper3⟩ := centeredPrimeWeight_periodic_iter 3
  obtain ⟨K9, hK9, hsum9⟩ := sum_fwdDiff_nine_conductorSplineIntegral_le
  obtain ⟨K8, hK8, hsum8⟩ := sum_fwdDiff_eight_dyadicSpline_le
  obtain ⟨K5, hK5, hsum5⟩ := sum_fwdDiff_five_conductorCurvatureProfile_le
  let K := max (2 * C7 * K9) (max (C6 * K8) (C3 * K5))
  have hK : 0 ≤ K := le_trans (by positivity) (le_max_left _ _)
  refine ⟨K, hK, fun {N a d q} hN hNa had hd2N hq hbirth => ?_⟩
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  rcases eq_or_lt_of_le had with rfl | hlt
  · simp only [Ico_self, sum_empty, abs_zero]
    positivity
  have ha_pos : 0 < a := hN.trans hNa
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha_pos
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr (ha_pos.trans hlt)
  have hNa_le : (N : ℝ) ≤ a := by exact_mod_cast hNa.le
  have had_le : (a : ℝ) ≤ d := by exact_mod_cast had
  let Lmax := (Icc 1 (2 * N)).sup splineHorizon
  let topScale := 4 * Real.exp 8 * ((2 * N + 2 : ℕ) : ℝ) ^ 2 / (q : ℝ)
  let b := max (Lmax / q + 2) (⌊topScale⌋₊ + 2)
  have hb_gt : ∀ n ∈ Ico a d, splineHorizon n < q * b := by
    intro n hn
    have hn_mem : n ∈ Icc 1 (2 * N) := by
      obtain ⟨h1, h2⟩ := mem_Ico.mp hn
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    have hsup : splineHorizon n ≤ Lmax := le_sup hn_mem
    have hdiv := Nat.div_add_mod Lmax q
    have hmod := Nat.mod_lt Lmax hq
    have hlt1 : Lmax < q * (Lmax / q + 2) := by nlinarith
    exact hsup.trans_lt (hlt1.trans_le (Nat.mul_le_mul_left q (le_max_left _ _)))
  have hterm_eq : ∀ n ∈ Ico a d, (n : ℝ) ^ 2 * unitHorizonPair n q =
      ∑ j ∈ range b,
        ((n : ℝ) * dyadicSpline (((j : ℝ) * q) / (n : ℝ) ^ 2) -
          (n : ℝ) * dyadicSpline ((((j + 1 : ℕ) : ℝ) * q) / (n : ℝ) ^ 2)) *
        centeredPrimeWeight 1 j := by
    intro n hn
    have hn0 : 0 < n := ha_pos.trans_le (mem_Ico.mp hn).1
    have hn_r : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
    rw [unitHorizonPair_eq_quotient_blocks hn0 hq (hb_gt n hn), mul_sum]
    refine sum_congr rfl fun j _ => ?_
    unfold sampledSpline
    have e1 : ((q * j : ℕ) : ℝ) = (j : ℝ) * q := by push_cast; ring
    have e2 : ((q * (j + 1) : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) * q := by push_cast; ring
    rw [e1, e2]
    field_simp [hn_r.ne']
  rw [sum_congr rfl hterm_eq, sum_comm]
  let G := fun j : ℕ => ∑ n ∈ Ico a d, (n : ℝ) * dyadicSpline (((j : ℝ) * q) / (n : ℝ) ^ 2)
  have hswap_inner : (∑ x ∈ range b, ∑ y ∈ Ico a d,
      ((y : ℝ) * dyadicSpline (((x : ℝ) * q) / (y : ℝ) ^ 2) -
        (y : ℝ) * dyadicSpline ((((x + 1 : ℕ) : ℝ) * q) / (y : ℝ) ^ 2)) *
        centeredPrimeWeight 1 x) =
      ∑ j ∈ range b, (G j - G (j + 1)) * centeredPrimeWeight 1 j := by
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_mul, sum_sub_distrib]
  rw [hswap_inner]
  let I_seq := fun j : ℕ => ∫ t in (a : ℝ)..d, t * dyadicSpline (((j : ℝ) * q) / t ^ 2)
  let B_seq := fun j : ℕ => ((d : ℝ) * dyadicSpline (((j : ℝ) * q) / (d : ℝ) ^ 2) -
    (a : ℝ) * dyadicSpline (((j : ℝ) * q) / (a : ℝ) ^ 2)) / 2
  let H_curv := fun j n : ℕ => fun s : ℝ =>
    (s * (s - 1) / 2) * (conductorCurvatureProfile (((j : ℝ) * q) / ((n : ℝ) + s) ^ 2) / ((n : ℝ) + s))
  let R_seq := fun j : ℕ => ∑ n ∈ Ico a d, ∫ s in (0 : ℝ)..1, H_curv j n s
  have hG_em : ∀ j : ℕ, G j = I_seq j - B_seq j - R_seq j := by
    intro j
    let z := (j : ℝ) * q
    have hcd : ContDiffOn ℝ 2 (fun t : ℝ => t * dyadicSpline (z / t ^ 2)) (Set.Ioi 0) :=
      (hasDerivAt_conductor_profile z zero_lt_one).1
    have hem := trapezoidal_euler_maclaurin_Ico hcd ha_pos had
    dsimp only [G, I_seq, B_seq, R_seq, H_curv, z] at hem ⊢
    rw [hem]
    congr 1
    refine sum_congr rfl fun n hn => intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    have ht0 : (0 : ℝ) < (n : ℝ) + s := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast ha_pos.trans_le (mem_Ico.mp hn).1
      linarith [hs.1]
    rw [(hasDerivAt_conductor_profile z ht0).2]
  have hdecomp : (∑ j ∈ range b, (G j - G (j + 1)) * centeredPrimeWeight 1 j) =
      (∑ j ∈ range b, (I_seq j - I_seq (j + 1)) * centeredPrimeWeight 1 j) -
      (∑ j ∈ range b, (B_seq j - B_seq (j + 1)) * centeredPrimeWeight 1 j) -
      (∑ j ∈ range b, (R_seq j - R_seq (j + 1)) * centeredPrimeWeight 1 j) := by
    simp only [hG_em]
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [hdecomp]
  have hlo_ratio : ∀ {j : ℕ} {t : ℝ}, j ≤ 8 → (N : ℝ) ≤ t →
      ((j : ℝ) * q) / t ^ 2 < Real.exp (-8) := by
    intro j t hj ht
    have ht_pos : 0 < t := hN'.trans_le ht
    rw [div_lt_iff₀ (sq_pos_of_pos ht_pos)]
    have hj8 : (j : ℝ) * q ≤ 8 * q := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hq'.le
    have htsq : (N : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hN'.le ht 2
    exact hj8.trans_lt (hbirth.trans_le (mul_le_mul_of_nonneg_left htsq (Real.exp_pos (-8)).le))
  have hhi_ratio : ∀ {j : ℕ} {t : ℝ}, b ≤ j → 0 < t → t ≤ ((2 * N + 1 : ℕ) : ℝ) →
      4 * Real.exp 8 < ((j : ℝ) * q) / t ^ 2 := by
    intro j t hj ht0 ht_hi
    rw [lt_div_iff₀ (sq_pos_of_pos ht0)]
    have htsq : t ^ 2 < ((2 * N + 2 : ℕ) : ℝ) ^ 2 := by
      refine pow_lt_pow_left₀ ?_ ht0.le (by decide : 2 ≠ 0)
      push_cast at ht_hi ⊢; linarith
    have hb_fl : topScale < b := by
      have h1 : topScale < (⌊topScale⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one topScale
      have h2 : (⌊topScale⌋₊ + 2 : ℕ) ≤ b := le_max_right _ _
      have h3 : ((⌊topScale⌋₊ + 2 : ℕ) : ℝ) ≤ b := by exact_mod_cast h2
      push_cast at h3; linarith
    have hjq : 4 * Real.exp 8 * ((2 * N + 2 : ℕ) : ℝ) ^ 2 < (j : ℝ) * q := by
      have : topScale * q < (b : ℝ) * q := mul_lt_mul_of_pos_right hb_fl hq'
      have hjb : (b : ℝ) * q ≤ (j : ℝ) * q :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hq'.le
      dsimp only [topScale] at this
      rw [div_mul_cancel₀ _ hq'.ne'] at this
      exact this.trans_le hjb
    exact (mul_lt_mul_of_pos_left htsq (by positivity)).trans hjq
  -- Bound 1: Integral piece I_seq (9th order, s = 7)
  have hI_zero_lo : ∀ j ≤ 8, I_seq j = 0 := by
    intro j hj
    dsimp only [I_seq]
    rw [intervalIntegral.integral_of_le had_le]
    apply setIntegral_eq_zero_of_forall_eq_zero; intro t ht
    rw [dyadicSpline_eq_zero_outside fun hs =>
      (hlo_ratio hj (hNa_le.trans ht.1.le)).not_ge hs.1, mul_zero]
  have hI_zero_hi : ∀ j, b ≤ j → I_seq j = 0 := by
    intro j hj
    dsimp only [I_seq]
    rw [intervalIntegral.integral_of_le had_le]
    apply setIntegral_eq_zero_of_forall_eq_zero; intro t ht
    have ht0 : 0 < t := ha'.trans ht.1
    have ht2N : t ≤ ((2 * N + 1 : ℕ) : ℝ) := ht.2.trans (by exact_mod_cast hd2N)
    rw [dyadicSpline_eq_zero_outside fun hs =>
      (hhi_ratio hj ht0 ht2N).not_ge hs.2, mul_zero]
  have hI_bound : |∑ j ∈ range b, (I_seq j - I_seq (j + 1)) * centeredPrimeWeight 1 j| ≤
      2 * C7 * K9 * (q : ℝ) ^ 8 / (N : ℝ) ^ 14 := by
    have hp := hper7 (fun j => I_seq j - I_seq (j + 1)) b
      (fun j hj => by rw [hI_zero_lo j (by omega), hI_zero_lo (j + 1) (by omega), sub_self])
      (fun j hj => by rw [hI_zero_hi j hj, hI_zero_hi (j + 1) (by omega), sub_self])
    refine hp.trans ?_
    have hI_antideriv : I_seq = fun j : ℕ =>
        (a : ℝ) ^ 2 * conductorSplineIntegral ((j : ℝ) * ((q : ℝ) / (a : ℝ) ^ 2)) -
          (d : ℝ) ^ 2 * conductorSplineIntegral ((j : ℝ) * ((q : ℝ) / (d : ℝ) ^ 2)) := by
      funext j
      dsimp only [I_seq]
      rw [integral_mul_dyadicSpline_inv_sq ha' had_le (by positivity)]
      congr 2 <;> ring_nf
    have hbdiff9 : ∀ j, |bdiff^[8] (fun i => I_seq i - I_seq (i + 1)) j| ≤
        (a : ℝ) ^ 2 * |(fwdDiff ((q : ℝ) / (a : ℝ) ^ 2))^[9] conductorSplineIntegral
            ((j : ℝ) * ((q : ℝ) / (a : ℝ) ^ 2))| +
          (d : ℝ) ^ 2 * |(fwdDiff ((q : ℝ) / (d : ℝ) ^ 2))^[9] conductorSplineIntegral
            ((j : ℝ) * ((q : ℝ) / (d : ℝ) ^ 2))| := by
      intro j
      have hstep : (fun i => I_seq i - I_seq (i + 1)) = bdiff I_seq := rfl
      rw [hstep, ← Function.iterate_succ_apply, hI_antideriv,
        bdiff_iter_sub, bdiff_iter_const_mul, bdiff_iter_const_mul,
        bdiff_iter_sample_eq, bdiff_iter_sample_eq]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;>
      · rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (sq_nonneg _)]
    have ha_h : 0 < (q : ℝ) / (a : ℝ) ^ 2 ∧ (q : ℝ) / (a : ℝ) ^ 2 ≤ 1 := by
      refine ⟨div_pos hq' (sq_pos_of_pos ha'), ?_⟩
      have hlt8 := hlo_ratio (j := 1) (by decide) hNa_le
      have hexp1 : Real.exp (-8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      simp only [Nat.cast_one, one_mul] at hlt8
      linarith
    have hd_h : 0 < (q : ℝ) / (d : ℝ) ^ 2 ∧ (q : ℝ) / (d : ℝ) ^ 2 ≤ 1 := by
      refine ⟨div_pos hq' (sq_pos_of_pos hd'), ?_⟩
      have hlt8 := hlo_ratio (j := 1) (by decide) (hNa_le.trans had_le)
      have hexp1 : Real.exp (-8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      simp only [Nat.cast_one, one_mul] at hlt8
      linarith
    have hsum_a : (a : ℝ) ^ 2 * (K9 * ((q : ℝ) / (a : ℝ) ^ 2) ^ 8) ≤
        K9 * (q : ℝ) ^ 8 / (N : ℝ) ^ 14 := by
      have heq : (a : ℝ) ^ 2 * (K9 * ((q : ℝ) / (a : ℝ) ^ 2) ^ 8) =
          K9 * (q : ℝ) ^ 8 / (a : ℝ) ^ 14 := by field_simp [ha'.ne']
      rw [heq]
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hN' 14)
        (pow_le_pow_left₀ hN'.le hNa_le 14)
    have hsum_d : (d : ℝ) ^ 2 * (K9 * ((q : ℝ) / (d : ℝ) ^ 2) ^ 8) ≤
        K9 * (q : ℝ) ^ 8 / (N : ℝ) ^ 14 := by
      have heq : (d : ℝ) ^ 2 * (K9 * ((q : ℝ) / (d : ℝ) ^ 2) ^ 8) =
          K9 * (q : ℝ) ^ 8 / (d : ℝ) ^ 14 := by field_simp [hd'.ne']
      rw [heq]
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hN' 14)
        (pow_le_pow_left₀ hN'.le (hNa_le.trans had_le) 14)
    calc C7 * ∑ j ∈ range b, |bdiff^[8] (fun i => I_seq i - I_seq (i + 1)) j|
        ≤ C7 * ((a : ℝ) ^ 2 * (∑ j ∈ range b,
              |(fwdDiff ((q : ℝ) / (a : ℝ) ^ 2))^[9] conductorSplineIntegral
                ((j : ℝ) * ((q : ℝ) / (a : ℝ) ^ 2))|) +
            (d : ℝ) ^ 2 * (∑ j ∈ range b,
              |(fwdDiff ((q : ℝ) / (d : ℝ) ^ 2))^[9] conductorSplineIntegral
                ((j : ℝ) * ((q : ℝ) / (d : ℝ) ^ 2))|)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC7
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_le_sum fun j _ => hbdiff9 j
      _ ≤ C7 * ((a : ℝ) ^ 2 * (K9 * ((q : ℝ) / (a : ℝ) ^ 2) ^ 8) +
            (d : ℝ) ^ 2 * (K9 * ((q : ℝ) / (d : ℝ) ^ 2) ^ 8)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_left (hsum9 ha_h.1 ha_h.2 b) (sq_nonneg _))
            (mul_le_mul_of_nonneg_left (hsum9 hd_h.1 hd_h.2 b) (sq_nonneg _))) hC7
      _ ≤ C7 * (K9 * (q : ℝ) ^ 8 / (N : ℝ) ^ 14 + K9 * (q : ℝ) ^ 8 / (N : ℝ) ^ 14) :=
          mul_le_mul_of_nonneg_left (add_le_add hsum_a hsum_d) hC7
      _ = 2 * C7 * K9 * (q : ℝ) ^ 8 / (N : ℝ) ^ 14 := by ring
  -- Bound 2: Boundary piece B_seq (8th order, s = 6)
  have hB_zero_lo : ∀ j ≤ 7, B_seq j = 0 := by
    intro j hj
    dsimp only [B_seq]
    rw [dyadicSpline_eq_zero_outside fun hs =>
        (hlo_ratio (hj.trans (by decide)) (hNa_le.trans had_le)).not_ge hs.1,
      dyadicSpline_eq_zero_outside fun hs =>
        (hlo_ratio (hj.trans (by decide)) hNa_le).not_ge hs.1]
    ring
  have hB_zero_hi : ∀ j, b ≤ j → B_seq j = 0 := by
    intro j hj
    dsimp only [B_seq]
    have hd2N' : (d : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast hd2N
    rw [dyadicSpline_eq_zero_outside fun hs => (hhi_ratio hj hd' hd2N').not_ge hs.2,
      dyadicSpline_eq_zero_outside fun hs => (hhi_ratio hj ha' (had_le.trans hd2N')).not_ge hs.2]
    ring
  have hB_bound : |∑ j ∈ range b, (B_seq j - B_seq (j + 1)) * centeredPrimeWeight 1 j| ≤
      C6 * K8 * (q : ℝ) ^ 7 / (N : ℝ) ^ 13 := by
    have hp := hper6 (fun j => B_seq j - B_seq (j + 1)) b
      (fun j hj => by rw [hB_zero_lo j (by omega), hB_zero_lo (j + 1) (by omega), sub_self])
      (fun j hj => by rw [hB_zero_hi j hj, hB_zero_hi (j + 1) (by omega), sub_self])
    refine hp.trans ?_
    have hB_form : B_seq = fun j : ℕ =>
        ((d : ℝ) / 2) * dyadicSpline ((j : ℝ) * ((q : ℝ) / (d : ℝ) ^ 2)) -
          ((a : ℝ) / 2) * dyadicSpline ((j : ℝ) * ((q : ℝ) / (a : ℝ) ^ 2)) := by
      funext j; dsimp only [B_seq]; ring_nf
    have hbdiff8 : ∀ j, |bdiff^[7] (fun i => B_seq i - B_seq (i + 1)) j| ≤
        ((d : ℝ) / 2) * |(fwdDiff ((q : ℝ) / (d : ℝ) ^ 2))^[8] dyadicSpline
            ((j : ℝ) * ((q : ℝ) / (d : ℝ) ^ 2))| +
          ((a : ℝ) / 2) * |(fwdDiff ((q : ℝ) / (a : ℝ) ^ 2))^[8] dyadicSpline
            ((j : ℝ) * ((q : ℝ) / (a : ℝ) ^ 2))| := by
      intro j
      have hstep : (fun i => B_seq i - B_seq (i + 1)) = bdiff B_seq := rfl
      rw [hstep, ← Function.iterate_succ_apply, hB_form,
        bdiff_iter_sub, bdiff_iter_const_mul, bdiff_iter_const_mul,
        bdiff_iter_sample_eq, bdiff_iter_sample_eq]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;>
      · rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (by positivity)]
    have ha_h : 0 < (q : ℝ) / (a : ℝ) ^ 2 ∧ (q : ℝ) / (a : ℝ) ^ 2 ≤ 1 := by
      refine ⟨div_pos hq' (sq_pos_of_pos ha'), ?_⟩
      have hlt8 := hlo_ratio (j := 1) (by decide) hNa_le
      have hexp1 : Real.exp (-8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      simp only [Nat.cast_one, one_mul] at hlt8; linarith
    have hd_h : 0 < (q : ℝ) / (d : ℝ) ^ 2 ∧ (q : ℝ) / (d : ℝ) ^ 2 ≤ 1 := by
      refine ⟨div_pos hq' (sq_pos_of_pos hd'), ?_⟩
      have hlt8 := hlo_ratio (j := 1) (by decide) (hNa_le.trans had_le)
      have hexp1 : Real.exp (-8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      simp only [Nat.cast_one, one_mul] at hlt8; linarith
    have hsum_d : ((d : ℝ) / 2) * (K8 * ((q : ℝ) / (d : ℝ) ^ 2) ^ 7) ≤
        (K8 / 2) * (q : ℝ) ^ 7 / (N : ℝ) ^ 13 := by
      have heq : ((d : ℝ) / 2) * (K8 * ((q : ℝ) / (d : ℝ) ^ 2) ^ 7) =
          (K8 / 2) * (q : ℝ) ^ 7 / (d : ℝ) ^ 13 := by field_simp [hd'.ne']
      rw [heq]
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hN' 13)
        (pow_le_pow_left₀ hN'.le (hNa_le.trans had_le) 13)
    have hsum_a : ((a : ℝ) / 2) * (K8 * ((q : ℝ) / (a : ℝ) ^ 2) ^ 7) ≤
        (K8 / 2) * (q : ℝ) ^ 7 / (N : ℝ) ^ 13 := by
      have heq : ((a : ℝ) / 2) * (K8 * ((q : ℝ) / (a : ℝ) ^ 2) ^ 7) =
          (K8 / 2) * (q : ℝ) ^ 7 / (a : ℝ) ^ 13 := by field_simp [ha'.ne']
      rw [heq]
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hN' 13)
        (pow_le_pow_left₀ hN'.le hNa_le 13)
    calc C6 * ∑ j ∈ range b, |bdiff^[7] (fun i => B_seq i - B_seq (i + 1)) j|
        ≤ C6 * (((d : ℝ) / 2) * (∑ j ∈ range b,
              |(fwdDiff ((q : ℝ) / (d : ℝ) ^ 2))^[8] dyadicSpline
                ((j : ℝ) * ((q : ℝ) / (d : ℝ) ^ 2))|) +
            ((a : ℝ) / 2) * (∑ j ∈ range b,
              |(fwdDiff ((q : ℝ) / (a : ℝ) ^ 2))^[8] dyadicSpline
                ((j : ℝ) * ((q : ℝ) / (a : ℝ) ^ 2))|)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC6
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_le_sum fun j _ => hbdiff8 j
      _ ≤ C6 * (((d : ℝ) / 2) * (K8 * ((q : ℝ) / (d : ℝ) ^ 2) ^ 7) +
            ((a : ℝ) / 2) * (K8 * ((q : ℝ) / (a : ℝ) ^ 2) ^ 7)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_left (hsum8 hd_h.1 hd_h.2 b) (by positivity))
            (mul_le_mul_of_nonneg_left (hsum8 ha_h.1 ha_h.2 b) (by positivity))) hC6
      _ ≤ C6 * ((K8 / 2) * (q : ℝ) ^ 7 / (N : ℝ) ^ 13 + (K8 / 2) * (q : ℝ) ^ 7 / (N : ℝ) ^ 13) :=
          mul_le_mul_of_nonneg_left (add_le_add hsum_d hsum_a) hC6
      _ = C6 * K8 * (q : ℝ) ^ 7 / (N : ℝ) ^ 13 := by ring
  -- Bound 3: Curvature remainder piece R_seq (5th order, s = 3)
  have hR_zero_lo : ∀ j ≤ 4, R_seq j = 0 := by
    intro j hj
    dsimp only [R_seq, H_curv]
    apply sum_eq_zero; intro n hn
    rw [intervalIntegral.integral_of_le zero_le_one]
    apply setIntegral_eq_zero_of_forall_eq_zero; intro s hs
    have hnN : (N : ℝ) ≤ (n : ℝ) + s := by
      have : (N : ℝ) ≤ n := hNa_le.trans (by exact_mod_cast (mem_Ico.mp hn).1)
      linarith [hs.1]
    rw [conductorCurvatureProfile_eq_zero_outside fun hmem =>
      (hlo_ratio (hj.trans (by decide)) hnN).not_ge hmem.1, zero_div, mul_zero]
  have hR_zero_hi : ∀ j, b ≤ j → R_seq j = 0 := by
    intro j hj
    dsimp only [R_seq, H_curv]
    apply sum_eq_zero; intro n hn
    rw [intervalIntegral.integral_of_le zero_le_one]
    apply setIntegral_eq_zero_of_forall_eq_zero; intro s hs
    have hnd : n + 1 ≤ d := (mem_Ico.mp hn).2
    have hns_pos : 0 < (n : ℝ) + s := by
      have : (0 : ℝ) < n := Nat.cast_pos.mpr (ha_pos.trans_le (mem_Ico.mp hn).1)
      linarith [hs.1]
    have hns_hi : (n : ℝ) + s ≤ ((2 * N + 1 : ℕ) : ℝ) := by
      have : ((n + 1 : ℕ) : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast hnd.trans hd2N
      push_cast at this ⊢; linarith [hs.2]
    rw [conductorCurvatureProfile_eq_zero_outside fun hmem =>
      (hhi_ratio hj hns_pos hns_hi).not_ge hmem.2, zero_div, mul_zero]
  have hR_bound : |∑ j ∈ range b, (R_seq j - R_seq (j + 1)) * centeredPrimeWeight 1 j| ≤
      C3 * K5 * (q : ℝ) ^ 4 / (N : ℝ) ^ 8 := by
    have hp := hper3 (fun j => R_seq j - R_seq (j + 1)) b
      (fun j hj => by rw [hR_zero_lo j (by omega), hR_zero_lo (j + 1) (by omega), sub_self])
      (fun j hj => by rw [hR_zero_hi j hj, hR_zero_hi (j + 1) (by omega), sub_self])
    refine hp.trans ?_
    have hHcont : ∀ n ∈ Ico a d, ∀ i : ℕ, ContinuousOn (H_curv i n) (Set.Icc 0 1) := by
      intro n hn i
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (ha_pos.trans_le (mem_Ico.mp hn).1)
      dsimp only [H_curv]
      refine ((continuousOn_id.mul (continuousOn_id.sub continuousOn_const)).div_const 2).mul ?_
      refine ContinuousOn.div ?_ (continuousOn_const.add continuousOn_id) fun s hs => by linarith [hs.1]
      exact contDiff_four_conductorCurvatureProfile.continuous.comp_continuousOn
        (continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
          fun s hs => (sq_pos_of_pos (by linarith [hs.1])).ne')
    have hbdiff5 : ∀ j, |bdiff^[4] (fun i => R_seq i - R_seq (i + 1)) j| ≤
        ∑ n ∈ Ico a d, ∫ s in (0 : ℝ)..1,
          (1 / (8 * (N : ℝ))) * |(fwdDiff ((q : ℝ) / ((n : ℝ) + s) ^ 2))^[5]
            conductorCurvatureProfile ((j : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))| := by
      intro j
      have hstep : (fun i => R_seq i - R_seq (i + 1)) = bdiff R_seq := rfl
      rw [hstep, ← Function.iterate_succ_apply]
      dsimp only [R_seq]
      rw [bdiff_iter_sum 5 (Ico a d)]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
      rw [bdiff_iter_intervalIntegral 5 (H_curv · n) (hHcont n hn) j]
      have hcont_rhs : ContinuousOn (fun s : ℝ => (1 / (8 * (N : ℝ))) *
          |(fwdDiff ((q : ℝ) / ((n : ℝ) + s) ^ 2))^[5] conductorCurvatureProfile
            ((j : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))|) (Set.Icc 0 1) := by
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (ha_pos.trans_le (mem_Ico.mp hn).1)
        have hstep_c : ∀ r : ℕ, ContinuousOn (fun s : ℝ =>
            (fwdDiff ((q : ℝ) / ((n : ℝ) + s) ^ 2))^[r] conductorCurvatureProfile
              ((j : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))) (Set.Icc 0 1) := by
          intro r
          have heq_r : (fun s : ℝ => (fwdDiff ((q : ℝ) / ((n : ℝ) + s) ^ 2))^[r]
              conductorCurvatureProfile ((j : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))) =
              fun s : ℝ => (-1 : ℝ) ^ r * bdiff^[r] (fun i : ℕ =>
                conductorCurvatureProfile ((i : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))) j := by
            funext s
            rw [bdiff_iter_sample_eq, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
          rw [heq_r]
          refine continuousOn_const.mul ?_
          clear heq_r
          induction r generalizing j with
          | zero =>
            exact contDiff_four_conductorCurvatureProfile.continuous.comp_continuousOn
              (continuousOn_const.mul (continuousOn_const.div
                ((continuousOn_const.add continuousOn_id).pow 2)
                fun s hs => (sq_pos_of_pos (by linarith [hs.1])).ne'))
          | succ r ihr =>
            have heq' : (fun s : ℝ => bdiff^[r + 1] (fun i : ℕ =>
                conductorCurvatureProfile ((i : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))) j) =
                fun s => bdiff^[r] (fun i =>
                  conductorCurvatureProfile ((i : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))) j -
                bdiff^[r] (fun i =>
                  conductorCurvatureProfile ((i : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))) (j + 1) := by
              funext s; rw [Function.iterate_succ_apply']; rfl
            rw [heq']; exact (ihr j).sub (ihr (j + 1))
        exact continuousOn_const.mul (hstep_c 5).abs
      have hcont_lhs : ContinuousOn (fun s => bdiff^[5] (fun i => H_curv i n s) j) (Set.Icc 0 1) := by
        suffices ∀ r k, ContinuousOn (fun s => bdiff^[r] (fun i => H_curv i n s) k) (Set.Icc 0 1) from
          this 5 j
        intro r
        induction r with
        | zero => intro k; exact hHcont n hn k
        | succ r ihr =>
          intro k
          have heq' : (fun s => bdiff^[r + 1] (fun i => H_curv i n s) k) =
              fun s => bdiff^[r] (fun i => H_curv i n s) k -
                bdiff^[r] (fun i => H_curv i n s) (k + 1) := by
            funext s; rw [Function.iterate_succ_apply']; rfl
          rw [heq']; exact (ihr k).sub (ihr (k + 1))
      rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
      refine abs_integral_le_integral_abs.trans ?_
      refine setIntegral_mono_on
        (hcont_lhs.abs.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (hcont_rhs.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        measurableSet_Ioc fun s hs => ?_
      have heq_s : (fun i : ℕ => H_curv i n s) = fun i : ℕ =>
          ((s * (s - 1) / 2) / ((n : ℝ) + s)) *
            conductorCurvatureProfile ((i : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2)) := by
        funext i; dsimp only [H_curv]; ring
      rw [heq_s, bdiff_iter_const_mul, bdiff_iter_sample_eq, abs_mul, abs_mul,
        abs_pow, abs_neg, abs_one, one_pow, one_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have hnN : (N : ℝ) ≤ (n : ℝ) + s := by
        have : (N : ℝ) ≤ n := hNa_le.trans (by exact_mod_cast (mem_Ico.mp hn).1)
        linarith [hs.1.le]
      have hquad : |s * (s - 1) / 2| ≤ 1 / 8 := by
        have hnonpos : s * (s - 1) / 2 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hs.1.le (by linarith [hs.2]))
            (by norm_num)
        rw [abs_of_nonpos hnonpos]
        nlinarith [sq_nonneg (s - 1 / 2)]
      rw [abs_div, abs_of_pos (hN'.trans_le hnN)]
      calc |s * (s - 1) / 2| / ((n : ℝ) + s)
          ≤ (1 / 8) / (N : ℝ) := div_le_div₀ (by norm_num) hquad hN' hnN
        _ = 1 / (8 * (N : ℝ)) := by ring
    have hsum_R : (∑ j ∈ range b, |bdiff^[4] (fun i => R_seq i - R_seq (i + 1)) j|) ≤
        K5 * (q : ℝ) ^ 4 / (N : ℝ) ^ 8 := by
      calc (∑ j ∈ range b, |bdiff^[4] (fun i => R_seq i - R_seq (i + 1)) j|)
          ≤ ∑ j ∈ range b, ∑ n ∈ Ico a d, ∫ s in (0 : ℝ)..1,
              (1 / (8 * (N : ℝ))) * |(fwdDiff ((q : ℝ) / ((n : ℝ) + s) ^ 2))^[5]
                conductorCurvatureProfile ((j : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))| :=
            sum_le_sum fun j _ => hbdiff5 j
        _ = ∑ n ∈ Ico a d, ∫ s in (0 : ℝ)..1, ∑ j ∈ range b,
              (1 / (8 * (N : ℝ))) * |(fwdDiff ((q : ℝ) / ((n : ℝ) + s) ^ 2))^[5]
                conductorCurvatureProfile ((j : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))| := by
            rw [sum_comm]
            refine sum_congr rfl fun n hn => ?_
            have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (ha_pos.trans_le (mem_Ico.mp hn).1)
            have hint_j : ∀ j ∈ range b, IntervalIntegrable (fun s : ℝ =>
                (1 / (8 * (N : ℝ))) * |(fwdDiff ((q : ℝ) / ((n : ℝ) + s) ^ 2))^[5]
                  conductorCurvatureProfile ((j : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))|) volume 0 1 := by
              intro j _
              refine ContinuousOn.intervalIntegrable ?_
              rw [Set.uIcc_of_le zero_le_one]
              have heq_5 : (fun s : ℝ => (fwdDiff ((q : ℝ) / ((n : ℝ) + s) ^ 2))^[5]
                  conductorCurvatureProfile ((j : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))) =
                  fun s : ℝ => (-1 : ℝ) ^ 5 * bdiff^[5] (fun i : ℕ =>
                    conductorCurvatureProfile ((i : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))) j := by
                funext s
                rw [bdiff_iter_sample_eq, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
              refine continuousOn_const.mul (ContinuousOn.abs ?_)
              rw [heq_5]
              refine continuousOn_const.mul ?_
              suffices ∀ r k, ContinuousOn (fun s : ℝ => bdiff^[r] (fun i : ℕ =>
                  conductorCurvatureProfile ((i : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))) k) (Set.Icc 0 1) from
                this 5 j
              intro r
              induction r with
              | zero =>
                intro k
                exact contDiff_four_conductorCurvatureProfile.continuous.comp_continuousOn
                  (continuousOn_const.mul (continuousOn_const.div
                    ((continuousOn_const.add continuousOn_id).pow 2)
                    fun s hs => (sq_pos_of_pos (by linarith [hs.1])).ne'))
              | succ r ihr =>
                intro k
                have heq' : (fun s : ℝ => bdiff^[r + 1] (fun i : ℕ =>
                    conductorCurvatureProfile ((i : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))) k) =
                    fun s => bdiff^[r] (fun i =>
                      conductorCurvatureProfile ((i : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))) k -
                    bdiff^[r] (fun i =>
                      conductorCurvatureProfile ((i : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))) (k + 1) := by
                  funext s; rw [Function.iterate_succ_apply']; rfl
                rw [heq']; exact (ihr k).sub (ihr (k + 1))
            exact (intervalIntegral.integral_finsetSum hint_j).symm
        _ ≤ ∑ _n ∈ Ico a d, (1 / (8 * (N : ℝ))) * (K5 * ((q : ℝ) / (N : ℝ) ^ 2) ^ 4) := by
            refine sum_le_sum fun n hn => ?_
            have hpoint : ∀ s ∈ Set.uIoc (0 : ℝ) 1,
                ‖∑ j ∈ range b, (1 / (8 * (N : ℝ))) *
                  |(fwdDiff ((q : ℝ) / ((n : ℝ) + s) ^ 2))^[5]
                    conductorCurvatureProfile ((j : ℝ) * ((q : ℝ) / ((n : ℝ) + s) ^ 2))|‖ ≤
                  (1 / (8 * (N : ℝ))) * (K5 * ((q : ℝ) / (N : ℝ) ^ 2) ^ 4) := by
              intro s hs
              rw [Set.uIoc_of_le zero_le_one] at hs
              rw [Real.norm_of_nonneg (sum_nonneg fun _ _ => by positivity), ← mul_sum]
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hnN : (N : ℝ) ≤ (n : ℝ) + s := by
                have : (N : ℝ) ≤ n := hNa_le.trans (by exact_mod_cast (mem_Ico.mp hn).1)
                linarith [hs.1.le]
              have hns_pos : 0 < (n : ℝ) + s := hN'.trans_le hnN
              have hh_ns : 0 < (q : ℝ) / ((n : ℝ) + s) ^ 2 ∧ (q : ℝ) / ((n : ℝ) + s) ^ 2 ≤ 1 := by
                refine ⟨div_pos hq' (sq_pos_of_pos hns_pos), ?_⟩
                have hlt8 := hlo_ratio (j := 1) (by decide) hnN
                have hexp1 : Real.exp (-8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
                simp only [Nat.cast_one, one_mul] at hlt8; linarith
              refine (hsum5 hh_ns.1 hh_ns.2 b).trans (mul_le_mul_of_nonneg_left ?_ hK5)
              refine pow_le_pow_left₀ (by positivity) ?_ 4
              exact div_le_div_of_nonneg_left hq'.le (sq_pos_of_pos hN')
                (pow_le_pow_left₀ hN'.le hnN 2)
            have hb_ivl := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
            rw [Real.norm_of_nonneg (intervalIntegral.integral_nonneg zero_le_one
              fun s _ => sum_nonneg fun _ _ => by positivity)] at hb_ivl
            exact hb_ivl.trans_eq (by simp)
        _ ≤ (N : ℝ) * ((1 / (8 * (N : ℝ))) * (K5 * ((q : ℝ) / (N : ℝ) ^ 2) ^ 4)) := by
            rw [sum_const, nsmul_eq_mul]
            have hlen : ((d - a : ℕ) : ℝ) ≤ N := by exact_mod_cast (show d - a ≤ N by omega)
            rw [Nat.card_Ico]
            exact mul_le_mul_of_nonneg_right hlen (by positivity)
        _ ≤ K5 * (q : ℝ) ^ 4 / (N : ℝ) ^ 8 := by
            have heq : (N : ℝ) * ((1 / (8 * (N : ℝ))) * (K5 * ((q : ℝ) / (N : ℝ) ^ 2) ^ 4)) =
                (1 / 8) * (K5 * (q : ℝ) ^ 4 / (N : ℝ) ^ 8) := by field_simp [hN'.ne']
            rw [heq]
            have hpos : 0 ≤ K5 * (q : ℝ) ^ 4 / (N : ℝ) ^ 8 := by positivity
            linarith
    calc C3 * (∑ j ∈ range b, |bdiff^[4] (fun i => R_seq i - R_seq (i + 1)) j|)
        ≤ C3 * (K5 * (q : ℝ) ^ 4 / (N : ℝ) ^ 8) := mul_le_mul_of_nonneg_left hsum_R hC3
      _ = C3 * K5 * (q : ℝ) ^ 4 / (N : ℝ) ^ 8 := by ring
  have htri : |(∑ j ∈ range b, (I_seq j - I_seq (j + 1)) * centeredPrimeWeight 1 j) -
      (∑ j ∈ range b, (B_seq j - B_seq (j + 1)) * centeredPrimeWeight 1 j) -
      (∑ j ∈ range b, (R_seq j - R_seq (j + 1)) * centeredPrimeWeight 1 j)| ≤
      |∑ j ∈ range b, (I_seq j - I_seq (j + 1)) * centeredPrimeWeight 1 j| +
      |∑ j ∈ range b, (B_seq j - B_seq (j + 1)) * centeredPrimeWeight 1 j| +
      |∑ j ∈ range b, (R_seq j - R_seq (j + 1)) * centeredPrimeWeight 1 j| :=
    (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
  refine htri.trans ?_
  have hK1 : 2 * C7 * K9 ≤ K := le_max_left _ _
  have hK2 : C6 * K8 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK3 : C3 * K5 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have ht1 : 2 * C7 * K9 * (q : ℝ) ^ 8 / (N : ℝ) ^ 14 ≤ K * ((q : ℝ) ^ 8 / (N : ℝ) ^ 14) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hK1 (by positivity)
  have ht2 : C6 * K8 * (q : ℝ) ^ 7 / (N : ℝ) ^ 13 ≤ K * ((q : ℝ) ^ 7 / (N : ℝ) ^ 13) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hK2 (by positivity)
  have ht3 : C3 * K5 * (q : ℝ) ^ 4 / (N : ℝ) ^ 8 ≤ K * ((q : ℝ) ^ 4 / (N : ℝ) ^ 8) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hK3 (by positivity)
  linarith [hI_bound, hB_bound, hR_bound, ht1, ht2, ht3]

/-- General two-variable conductor-smoothed shell bound across `N < n ≤ M ≤ 2N` for any
monotone product cutoffs `u(n) ≤ w(n)` in the detached subquadratic range. -/
theorem conductor_smoothed_shell_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u w : ℕ → ℕ}, Monotone u → Monotone w →
      ∀ {N M : ℕ}, 0 < N → N ≤ M → M ≤ 2 * N → 1 ≤ w M →
      8 * (w M : ℝ) < Real.exp (-8) * (N : ℝ) ^ 2 →
      (∀ n ∈ Ioc N M, productLower 1 (splineHorizon n) ≤ u n ∧ u n ≤ w n) →
      |∑ n ∈ Ioc N M, (n : ℝ) ^ 2 *
          (cappedUpperProductReading (u n) n n - cappedUpperProductReading (w n) n n)| ≤
        C * (1 + Real.log (w M)) *
          ((w M : ℝ) ^ 9 / (N : ℝ) ^ 14 + (w M : ℝ) ^ 8 / (N : ℝ) ^ 13 +
            (w M : ℝ) ^ 5 / (N : ℝ) ^ 8) := by
  obtain ⟨K, hK, hcond⟩ := conductor_interval_horizonPair_bound
  let G := 2 * (1 + mass (1 + 1))
  have hG : 0 ≤ G := (abs_nonneg _).trans (innerJump_pointwise_bound 1 0)
  let E := Real.log 4 + 4
  have hE : 0 ≤ E := by dsimp only [E]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity
  refine ⟨G * K * E, by positivity, fun {u w} hu hw {N M} hN hNM hM2N hwM hbirth hgeom => ?_⟩
  let W := w M
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hwM
  have hrow_ex : ∀ n ∈ Ioc N M,
      (n : ℝ) ^ 2 * (cappedUpperProductReading (u n) n n - cappedUpperProductReading (w n) n n) =
        ordinaryFactorTail 4 W fun p =>
          ∑ v ∈ (Icc 1 (min (W / p) M)).filter (p.Coprime ·),
            if v ≤ n ∧ u n < p * v ∧ p * v ≤ w n then
              innerJump 1 v * ((n : ℝ) ^ 2 * unitHorizonPair n (p * v))
            else 0 := by
    intro n hn
    obtain ⟨hnN, hnM⟩ := mem_Ioc.mp hn
    have hn0 : 0 < n := hN.trans hnN
    obtain ⟨hYn, huwn⟩ := hgeom n hn
    have hwnW : w n ≤ W := hw hnM
    have hbirth_n : (w n : ℝ) + 1 < Real.exp (-8) * (n : ℝ) ^ 2 := by
      have hwn' : (w n : ℝ) ≤ W := by exact_mod_cast hwnW
      have hNn : (N : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg N) (by exact_mod_cast hnN.le) 2
      have hNexp := mul_le_mul_of_nonneg_left hNn (Real.exp_pos (-8)).le
      linarith
    rw [capped_shell_exchange hn0 huwn hbirth_n hYn n]
    have hpad := unit_prime_padding hwnW
      (fun p => ∑ v ∈ shellFactors n (u n) (w n) p, innerJump 1 v * unitHorizonPair n (p * v))
      fun p hp => by
        have hh : min (w n / p) n = 0 := by rw [Nat.div_eq_of_lt hp, zero_min]
        simp only [shellFactors, hh, Ioc_eq_empty_of_le (Nat.zero_le _), filter_empty, sum_empty]
    rw [hpad]
    unfold ordinaryFactorTail
    rw [mul_sum]
    refine sum_congr rfl fun p hp => ?_
    have hp0 := (mem_filter.mp hp).2.pos
    rw [mul_left_comm ((n : ℝ) ^ 2) (vonMangoldt p), mul_sum]
    congr 1
    let S_big := (Icc 1 (min (W / p) M)).filter (p.Coprime ·)
    let P_cond := fun v : ℕ => v ≤ n ∧ u n < p * v ∧ p * v ≤ w n
    have hfilt : S_big.filter P_cond = shellFactors n (u n) (w n) p := by
      ext v
      simp only [S_big, P_cond, shellFactors, mem_filter, mem_Icc, mem_Ioc, le_min_iff]
      constructor
      · rintro ⟨⟨⟨hv1, _, _⟩, hcop⟩, hvn, hlo, hhi⟩
        exact ⟨⟨(Nat.div_lt_iff_lt_mul hp0).mpr (by simpa [Nat.mul_comm] using hlo),
          (Nat.le_div_iff_mul_le hp0).mpr (by simpa [Nat.mul_comm] using hhi), hvn⟩, hcop⟩
      · rintro ⟨⟨hlo, hhi, hvn⟩, hcop⟩
        have hlo' : u n < p * v := by
          simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hp0).mp hlo
        have hhi' : p * v ≤ w n := by
          simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp0).mp hhi
        exact ⟨⟨⟨(Nat.zero_le _).trans_lt hlo,
          hhi.trans (Nat.div_le_div_right hwnW), hvn.trans hnM⟩, hcop⟩, hvn, hlo', hhi'⟩
    dsimp only
    rw [← sum_filter, hfilt]
    exact sum_congr rfl fun v _ => by ring
  rw [sum_congr rfl hrow_ex]
  have hcomm_outer :
      (∑ n ∈ Ioc N M, ordinaryFactorTail 4 W fun p =>
          ∑ v ∈ (Icc 1 (min (W / p) M)).filter (p.Coprime ·),
            if v ≤ n ∧ u n < p * v ∧ p * v ≤ w n then
              innerJump 1 v * ((n : ℝ) ^ 2 * unitHorizonPair n (p * v))
            else 0) =
        ordinaryFactorTail 4 W fun p =>
          ∑ v ∈ (Icc 1 (min (W / p) M)).filter (p.Coprime ·),
            innerJump 1 v * ∑ n ∈ (Ioc N M).filter (fun n => v ≤ n ∧ u n < p * v ∧ p * v ≤ w n),
              (n : ℝ) ^ 2 * unitHorizonPair n (p * v) := by
    unfold ordinaryFactorTail
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [← mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [← sum_filter, mul_sum]
  rw [hcomm_outer]
  let S_scale := (W : ℝ) ^ 8 / (N : ℝ) ^ 14 + (W : ℝ) ^ 7 / (N : ℝ) ^ 13 +
    (W : ℝ) ^ 4 / (N : ℝ) ^ 8
  have hS_nonneg : 0 ≤ S_scale := by dsimp only [S_scale]; positivity
  suffices hrow : ∀ p ∈ (Ioc 4 W).filter Nat.Prime,
      |∑ v ∈ (Icc 1 (min (W / p) M)).filter (p.Coprime ·),
          innerJump 1 v * ∑ n ∈ (Ioc N M).filter (fun n => v ≤ n ∧ u n < p * v ∧ p * v ≤ w n),
            (n : ℝ) ^ 2 * unitHorizonPair n (p * v)| ≤
        (G * K * (W : ℝ) * S_scale) / p by
    refine (ordinaryFactorTail_reciprocal hwM (by positivity : 0 ≤ G * K * (W : ℝ) * S_scale) hrow).trans_eq ?_
    dsimp only [S_scale, E]
    ring
  intro p hp
  have hp0 := (mem_filter.mp hp).2.pos
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp0
  let Vf := (Icc 1 (min (W / p) M)).filter (p.Coprime ·)
  have heach : ∀ v ∈ Vf,
      |innerJump 1 v * ∑ n ∈ (Ioc N M).filter (fun n => v ≤ n ∧ u n < p * v ∧ p * v ≤ w n),
          (n : ℝ) ^ 2 * unitHorizonPair n (p * v)| ≤ G * (K * S_scale) := by
    intro v hv
    obtain ⟨hv1, hvhi⟩ := mem_Icc.mp (mem_filter.mp hv).1
    have hprod : p * v ≤ W := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp0).mp (hvhi.trans (min_le_left _ _))
    have hprod' : ((p * v : ℕ) : ℝ) ≤ W := by exact_mod_cast hprod
    have hq_pos : 0 < p * v := Nat.mul_pos hp0 hv1
    have hq_birth : 8 * ((p * v : ℕ) : ℝ) < Real.exp (-8) * (N : ℝ) ^ 2 := by linarith
    obtain ⟨a, d, hNa, had, hdM, hset⟩ := monotone_shell_conductors hu hw hNM (p * v) v
    rw [hset, abs_mul]
    have hd2N : d ≤ 2 * N + 1 := hdM.trans (Nat.succ_le_succ hM2N)
    refine mul_le_mul (innerJump_pointwise_bound 1 v)
      ((hcond hN hNa had hd2N hq_pos hq_birth).trans ?_) (abs_nonneg _) hG
    refine mul_le_mul_of_nonneg_left ?_ hK
    dsimp only [S_scale]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod' 8) (by positivity)
    · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod' 7) (by positivity)
    · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod' 4) (by positivity)
  have hcard : Vf.card ≤ W / p := by
    refine (card_le_card (filter_subset _ _)).trans ?_
    rw [Nat.card_Icc, Nat.add_sub_cancel]; exact min_le_left _ _
  have hc : (Vf.card : ℝ) * p ≤ W := by
    exact_mod_cast (Nat.mul_le_mul_right p hcard).trans (Nat.div_mul_le_self W p)
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum heach).trans ?_)
  rw [sum_const, nsmul_eq_mul, le_div_iff₀ hp']
  have he := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ G * (K * S_scale))
  calc (Vf.card : ℝ) * (G * (K * S_scale)) * p
      = ((Vf.card : ℝ) * p) * (G * (K * S_scale)) := by ring
    _ ≤ (W : ℝ) * (G * (K * S_scale)) := he
    _ = G * K * (W : ℝ) * S_scale := by ring

#print axioms monotone_shell_conductors
#print axioms trapezoidal_euler_maclaurin_Ico
#print axioms conductor_interval_horizonPair_bound
#print axioms conductor_smoothed_shell_bound
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
