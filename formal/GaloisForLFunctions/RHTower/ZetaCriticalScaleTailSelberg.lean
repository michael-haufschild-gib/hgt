import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailFromGate
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergWeights
import GaloisForLFunctions.RHTower.XiCriticalScaleDiscSeamExplicitDensity
import GaloisForLFunctions.RHTower.SpeiserShadowExponentialDensity

/-!
# Explicit exponential tails beyond the critical scale

With Selberg's twisted mollifier the gate constant is `c_R = e^{2R}/(1 − e^{−2R/15})`, so
`log c_R − 2R = −log(1 − e^{−2R/15}) =: g(R)`, which decays like `e^{−2R/15}`.  The tail law of
`ZetaCriticalScaleTailFromGate` then gives, for every `R > 0` and `η > 0` and all large `V`:

* `4π Σ_{0 < Im ρ ≤ V} m_ρ (Re ρ − ½ − R/log V)⁺ ≤ (g(R) + η) V`
  (`eventually_offLineTail_le_selberg`);
* the zeros with `Re ρ ≥ ½ + 2R/log V`, `0 < Im ρ ≤ V`, number at most
  `(g(R) + η) V log V / (4πR)`, a proportion `≈ g(R)/(2R)` of all zeros
  (`eventually_offLineCountBeyond_le_selberg`);
* among the right discs `D_1, …, D_K` of radius `r = 2R/log V` with `V ≤ 3rK + 4r`, `3rK + r ≤ V`,
  at most `(3K + 4)(g(R) + η)/(2π)` contain a zero, and every other one has a contracting adjoint
  Hankel seam (`eventually_card_badCriticalScaleDiscs_le_selberg`,
  `eventually_goodCriticalScaleDiscs_selberg`).

* the heights `t ∈ [20, V]` shadowed by a zero with `|Re ρ − ½| ≥ κ/log V` have measure at most
  `(g(κ/2) + η)(V + 1)/π`; off them every local RH sign at horizontal distance `≥ κ/log V` holds
  (`eventually_volume_kappaShadow_le_selberg`).

All constants are explicit; the rate `2R/15` is twice the mollifier exponent `1/15`.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

/-- `g(R) = −log(1 − e^{−2R/15})`. -/
def selbergTailRate (R : ℝ) : ℝ := -Real.log (1 - Real.exp (-(2 * R / 15)))

theorem one_le_selbergBlockConst {R : ℝ} (hR : 0 < R) :
    1 ≤ ZetaGateProductAFE.selbergBlockConst R := by
  unfold ZetaGateProductAFE.selbergBlockConst
  have h1 : 0 < Real.exp (-(2 * R / 15)) := Real.exp_pos _
  have h2 := ZetaGateProductAFE.exp_neg_lt_one (show 0 < 2 * R / 15 by positivity)
  rw [le_div_iff₀ (by linarith)]
  have h3 : 1 ≤ Real.exp (2 * R) := Real.one_le_exp (by positivity)
  linarith

theorem log_selbergBlockConst_sub {R : ℝ} (hR : 0 < R) :
    Real.log (max (ZetaGateProductAFE.selbergBlockConst R) 1) - 2 * R = selbergTailRate R := by
  rw [max_eq_left (one_le_selbergBlockConst hR)]
  unfold ZetaGateProductAFE.selbergBlockConst selbergTailRate
  have h2 := ZetaGateProductAFE.exp_neg_lt_one (show 0 < 2 * R / 15 by positivity)
  rw [Real.log_div (Real.exp_pos _).ne' (by linarith), Real.log_exp]
  ring

/-- **The tail law with Selberg's twisted mollifier.** -/
theorem eventually_offLineTail_le_selberg {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ V in atTop,
      4 * Real.pi * offLineTail (R / Real.log V) V ≤ (selbergTailRate R + η) * V := by
  have h := eventually_offLineTail_le_of_zetaGate hR (le_max_right _ 1) hη
    (ZetaGateProductAFE.zetaMollifiedMeanSquareGate_selberg hR)
  rwa [log_selbergBlockConst_sub hR] at h

theorem selbergTailRate_add_nonneg {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    0 ≤ selbergTailRate R + η := by
  unfold selbergTailRate
  have h := ZetaGateProductAFE.exp_neg_lt_one (show 0 < 2 * R / 15 by positivity)
  have hpos : 0 < 1 - Real.exp (-(2 * R / 15)) := by linarith
  have : Real.log (1 - Real.exp (-(2 * R / 15))) ≤ 0 :=
    Real.log_nonpos hpos.le (by linarith [Real.exp_pos (-(2 * R / 15))])
  linarith

/-! ## Counting the zeros beyond the critical scale -/

/-- The zeros with `Re ρ ≥ ½ + a`, `0 < Im ρ ≤ T`, with multiplicity. -/
def offLineCountBeyond (a T : ℝ) : ℝ :=
  ∑ z ∈ (stripFinsetPos T).filter (fun z => 1 / 2 + a ≤ z.re), ((analyticOrderAt xi z).toNat : ℝ)

/-- `d · #{Re ρ ≥ ½ + 2d} ≤ Σ m_ρ (Re ρ − ½ − d)⁺`. -/
theorem mul_offLineCountBeyond_le_offLineTail (d T : ℝ) :
    d * offLineCountBeyond (2 * d) T ≤ offLineTail d T := by
  classical
  unfold offLineCountBeyond offLineTail
  rw [Finset.mul_sum]
  calc ∑ z ∈ (stripFinsetPos T).filter (fun z => 1 / 2 + 2 * d ≤ z.re),
        d * ((analyticOrderAt xi z).toNat : ℝ)
      ≤ ∑ z ∈ (stripFinsetPos T).filter (fun z => 1 / 2 + 2 * d ≤ z.re),
          ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2 - d) 0 := by
        refine Finset.sum_le_sum fun z hz => ?_
        have hre := (Finset.mem_filter.mp hz).2
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (le_max_of_le_left (by linarith)) (Nat.cast_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
        mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)

/-- **Few zeros beyond the critical scale, from a tail law.**  If eventually
`4π Σ m_ρ (Re ρ − ½ − R/log V)⁺ ≤ G V`, then the zeros with `Re ρ ≥ ½ + 2R/log V`, `0 < Im ρ ≤ V`
number at most `G V log V/(4πR)`. -/
theorem eventually_offLineCountBeyond_le_of_tail {R G : ℝ} (hR : 0 < R)
    (htail : ∀ᶠ V in atTop, 4 * Real.pi * offLineTail (R / Real.log V) V ≤ G * V) :
    ∀ᶠ V in atTop,
      offLineCountBeyond (2 * (R / Real.log V)) V
        ≤ G / (4 * Real.pi * R) * (V * Real.log V) := by
  filter_upwards [htail, eventually_gt_atTop (1 : ℝ)]
    with V hV hV1
  have hlog : 0 < Real.log V := Real.log_pos hV1
  have hd : 0 < R / Real.log V := div_pos hR hlog
  have h := mul_offLineCountBeyond_le_offLineTail (R / Real.log V) V
  have h4 : 4 * Real.pi * (R / Real.log V * offLineCountBeyond (2 * (R / Real.log V)) V)
      ≤ G * V :=
    (mul_le_mul_of_nonneg_left h (by positivity)).trans hV
  have hπR : 0 < 4 * Real.pi * R := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hπR]
  have e : 4 * Real.pi * (R / Real.log V * offLineCountBeyond (2 * (R / Real.log V)) V)
      * Real.log V = offLineCountBeyond (2 * (R / Real.log V)) V * (4 * Real.pi * R) := by
    field_simp
  have h5 := mul_le_mul_of_nonneg_right h4 hlog.le
  rw [e] at h5
  calc offLineCountBeyond (2 * (R / Real.log V)) V * (4 * Real.pi * R)
      ≤ G * V * Real.log V := h5
    _ = G * (V * Real.log V) := by ring


/-- **Few zeros beyond the critical scale, explicitly.**  For all large `V`, the zeros with
`Re ρ ≥ ½ + 2R/log V` and `0 < Im ρ ≤ V` number at most `(g(R) + η) V log V/(4πR)`. -/
theorem eventually_offLineCountBeyond_le_selberg {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ V in atTop,
      offLineCountBeyond (2 * (R / Real.log V)) V
        ≤ (selbergTailRate R + η) / (4 * Real.pi * R) * (V * Real.log V) :=
  eventually_offLineCountBeyond_le_of_tail hR (eventually_offLineTail_le_selberg hR hη)

/-! ## Exceptional critical-scale discs -/

/-- **Exceptional discs against the tail.**  `(r/2) · #{exceptional D_k, k ≤ K} ≤
Σ_{0 < Im ρ ≤ 3rK + r} m_ρ (Re ρ − ½ − r/2)⁺`. -/
theorem mul_card_badCriticalScaleDiscs_le_offLineTail {r : ℝ} (hr : 0 < r) (K : ℕ) :
    r / 2 * ((badCriticalScaleDiscs r K).card : ℝ) ≤ offLineTail (r / 2) (3 * r * K + r) := by
  classical
  set T := 3 * r * K + r
  have hchoose : ∀ k ∈ badCriticalScaleDiscs r K,
      ∃ z ∈ closedBall (criticalScaleCenter r k) r, xi z = 0 := by
    intro k hk
    unfold badCriticalScaleDiscs at hk
    exact (Finset.mem_filter.mp hk).2
  choose! w hwball hwzero using hchoose
  have hIcc : ∀ k ∈ badCriticalScaleDiscs r K, 1 ≤ k ∧ k ≤ K := by
    intro k hk
    unfold badCriticalScaleDiscs at hk
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
  have hstrip : ∀ k ∈ badCriticalScaleDiscs r K, w k ∈ stripFinsetPos T := by
    intro k hk
    obtain ⟨h1, -, h3, h4⟩ := re_im_of_mem_criticalScaleDisc (hwball k hk)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (hIcc k hk).1
    have hkK : (k : ℝ) ≤ K := by exact_mod_cast (hIcc k hk).2
    rw [mem_stripFinsetPos]
    exact ⟨by linarith, xi_zero_re_lt_one (hwzero k hk), by nlinarith, by nlinarith, hwzero k hk⟩
  have hinj : Set.InjOn w (badCriticalScaleDiscs r K : Set ℕ) := by
    intro k hk l hl hkl
    obtain ⟨-, -, hk1, hk2⟩ := re_im_of_mem_criticalScaleDisc (hwball k hk)
    obtain ⟨-, -, hl1, hl2⟩ := re_im_of_mem_criticalScaleDisc (hwball l hl)
    rw [hkl] at hk1 hk2
    have f1 : (k : ℝ) - l < 1 := by
      by_contra hc; push Not at hc; nlinarith
    have f2 : (l : ℝ) - k < 1 := by
      by_contra hc; push Not at hc; nlinarith
    have g1 : (k : ℤ) - l < 1 := by exact_mod_cast f1
    have g2 : (l : ℤ) - k < 1 := by exact_mod_cast f2
    omega
  have hsub : (badCriticalScaleDiscs r K).image w ⊆ stripFinsetPos T := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact hstrip k hk
  calc r / 2 * ((badCriticalScaleDiscs r K).card : ℝ)
      = ∑ k ∈ badCriticalScaleDiscs r K, r / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ k ∈ badCriticalScaleDiscs r K, max ((w k).re - 1 / 2 - r / 2) 0 := by
        refine Finset.sum_le_sum fun k hk => ?_
        have := (re_im_of_mem_criticalScaleDisc (hwball k hk)).1
        exact le_max_of_le_left (by linarith)
    _ = ∑ z ∈ (badCriticalScaleDiscs r K).image w, max (z.re - 1 / 2 - r / 2) 0 :=
        (Finset.sum_image (f := fun z : ℂ => max (z.re - 1 / 2 - r / 2) 0) (g := w)
          (fun x hx y hy h => hinj hx hy h)).symm
    _ ≤ ∑ z ∈ (badCriticalScaleDiscs r K).image w,
          ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2 - r / 2) 0 := by
        refine Finset.sum_le_sum fun z hz => ?_
        have hzb := mem_stripFinsetPos.mp (hsub hz)
        have h1 := DeBruijn.one_le_toNat_analyticOrderAt_xi hzb.2.2.2.2
        have h1' : (1 : ℝ) ≤ ((analyticOrderAt xi z).toNat : ℝ) := by exact_mod_cast h1
        have hpos : 0 ≤ max (z.re - 1 / 2 - r / 2) 0 := le_max_right _ _
        nlinarith
    _ ≤ offLineTail (r / 2) T :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
          mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)

/-- **Exceptional critical-scale discs from a tail law.**  For all large `V`, with `r = 2R/log V`,
every `K` with `3rK + r ≤ V ≤ 3rK + 4r` has at most `(3K + 4)G/(2π)` exceptional discs
among `D_1, …, D_K`. -/
theorem eventually_card_badCriticalScaleDiscs_le_of_tail {R G : ℝ} (hR : 0 < R) (hG : 0 ≤ G)
    (htail : ∀ᶠ V in atTop, 4 * Real.pi * offLineTail (R / Real.log V) V ≤ G * V) :
    ∀ᶠ V in atTop, ∀ K : ℕ,
      3 * (2 * R / Real.log V) * K + 2 * R / Real.log V ≤ V →
      V ≤ 3 * (2 * R / Real.log V) * K + 4 * (2 * R / Real.log V) →
      ((badCriticalScaleDiscs (2 * R / Real.log V) K).card : ℝ)
        ≤ (3 * K + 4) * G / (2 * Real.pi) := by
  filter_upwards [htail, eventually_gt_atTop (1 : ℝ)]
    with V hV hV1 K hKV hVK
  have hlog : 0 < Real.log V := Real.log_pos hV1
  set r := 2 * R / Real.log V with hr
  have hr0 : 0 < r := by positivity
  have hrhalf : r / 2 = R / Real.log V := by rw [hr]; ring
  have h1 := mul_card_badCriticalScaleDiscs_le_offLineTail hr0 K
  rw [hrhalf] at h1
  have h2 := h1.trans (offLineTail_mono hKV)
  have h3 := (mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Real.pi)).trans hV
  have hg0 : 0 ≤ G := hG
  -- `V ≤ (3K + 4) r`, i.e. `V log V ≤ 2R(3K + 4)`
  have hVr : V * Real.log V ≤ 2 * R * (3 * K + 4) := by
    have : V ≤ r * (3 * K + 4) := by linarith
    have h := mul_le_mul_of_nonneg_right this hlog.le
    have e : r * (3 * K + 4) * Real.log V = 2 * R * (3 * K + 4) := by
      rw [hr]; field_simp
    linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [le_div_iff₀ (by positivity)]
  -- `4π (R/log V) #bad ≤ (g + η) V`, multiply by `log V / (2R)`
  have h4 : 4 * Real.pi * (R / Real.log V) * ((badCriticalScaleDiscs r K).card : ℝ) * Real.log V
      ≤ G * V * Real.log V := by
    have := mul_le_mul_of_nonneg_right h3 hlog.le
    linarith
  have e : 4 * Real.pi * (R / Real.log V) * ((badCriticalScaleDiscs r K).card : ℝ) * Real.log V
      = 2 * R * (((badCriticalScaleDiscs r K).card : ℝ) * (2 * Real.pi)) := by
    field_simp
    ring
  rw [e] at h4
  have h5 : G * V * Real.log V
      ≤ G * (2 * R * (3 * K + 4)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hVr hg0
  have h6 : 2 * R * (((badCriticalScaleDiscs r K).card : ℝ) * (2 * Real.pi))
      ≤ 2 * R * ((3 * K + 4) * G) := by
    linarith
  exact le_of_mul_le_mul_left h6 (by positivity)


/-- **Exceptional critical-scale discs, explicitly.**  For all large `V`, with `r = 2R/log V`,
every `K` with `3rK + r ≤ V ≤ 3rK + 4r` has at most `(3K + 4)(g(R) + η)/(2π)` exceptional discs
among `D_1, …, D_K`. -/
theorem eventually_card_badCriticalScaleDiscs_le_selberg {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ V in atTop, ∀ K : ℕ,
      3 * (2 * R / Real.log V) * K + 2 * R / Real.log V ≤ V →
      V ≤ 3 * (2 * R / Real.log V) * K + 4 * (2 * R / Real.log V) →
      ((badCriticalScaleDiscs (2 * R / Real.log V) K).card : ℝ)
        ≤ (3 * K + 4) * (selbergTailRate R + η) / (2 * Real.pi) :=
  eventually_card_badCriticalScaleDiscs_le_of_tail hR (selbergTailRate_add_nonneg hR hη)
    (eventually_offLineTail_le_selberg hR hη)

/-- **Contracting seams on all but a fraction `≈ 3G/(2π)` of the critical-scale discs, from a tail
law.**
For all large `V`, with `r = 2R/log V` and `3rK + r ≤ V ≤ 3rK + 4r`, at least
`K − (3K + 4)G/(2π)` of `D_1, …, D_K` are zero-free with adjoint Hankel seam `< 1`. -/
theorem eventually_goodCriticalScaleDiscs_of_tail {R G : ℝ} (hR : 0 < R) (hG : 0 ≤ G)
    (htail : ∀ᶠ V in atTop, 4 * Real.pi * offLineTail (R / Real.log V) V ≤ G * V) :
    ∀ᶠ V in atTop, ∀ K : ℕ,
      3 * (2 * R / Real.log V) * K + 2 * R / Real.log V ≤ V →
      V ≤ 3 * (2 * R / Real.log V) * K + 4 * (2 * R / Real.log V) →
      (K : ℝ) - (3 * K + 4) * G / (2 * Real.pi)
          ≤ ((Finset.Icc 1 K \ badCriticalScaleDiscs (2 * R / Real.log V) K).card : ℝ) ∧
      ∀ hr : 0 < 2 * R / Real.log V,
        ∀ k ∈ Finset.Icc 1 K \ badCriticalScaleDiscs (2 * R / Real.log V) K,
          ∃ hne : ∀ ζ ∈ sphere (criticalScaleCenter (2 * R / Real.log V) k)
              (2 * R / Real.log V), xi ζ ≠ 0,
            ‖(xiDiscDatum (criticalScaleCenter (2 * R / Real.log V) k) (2 * R / Real.log V) hr
              hne).circlePhase.datum.adjointHankelSeam‖ < 1 := by
  classical
  filter_upwards [eventually_card_badCriticalScaleDiscs_le_of_tail hR hG htail] with V hV K hKV hVK
  set r := 2 * R / Real.log V with hr
  refine ⟨?_, fun hr0 k hk => ?_⟩
  · have hbad := hV K hKV hVK
    have hsub : badCriticalScaleDiscs r K ⊆ Finset.Icc 1 K := by
      intro k hk
      unfold badCriticalScaleDiscs at hk
      exact (Finset.mem_filter.mp hk).1
    have hcard := Finset.card_sdiff_of_subset hsub
    have hK : ((Finset.Icc 1 K).card : ℝ) = K := by simp
    have e : ((Finset.Icc 1 K \ badCriticalScaleDiscs r K).card : ℝ)
        = ((Finset.Icc 1 K).card : ℝ) - (badCriticalScaleDiscs r K).card := by
      rw [hcard, Nat.cast_sub (Finset.card_le_card hsub)]
    rw [e, hK]
    linarith
  · obtain ⟨hkI, hkb⟩ := Finset.mem_sdiff.mp hk
    apply criticalScaleDisc_adjointSeam_lt_one hr0
    intro z hz hz0
    apply hkb
    unfold badCriticalScaleDiscs
    exact Finset.mem_filter.mpr ⟨hkI, z, hz, hz0⟩


/-- **Contracting seams on all but an explicit exponential fraction of critical-scale discs.**
For all large `V`, with `r = 2R/log V` and `3rK + r ≤ V ≤ 3rK + 4r`, at least
`K − (3K + 4)(g(R) + η)/(2π)` of `D_1, …, D_K` are zero-free with adjoint Hankel seam `< 1`. -/
theorem eventually_goodCriticalScaleDiscs_selberg {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ V in atTop, ∀ K : ℕ,
      3 * (2 * R / Real.log V) * K + 2 * R / Real.log V ≤ V →
      V ≤ 3 * (2 * R / Real.log V) * K + 4 * (2 * R / Real.log V) →
      (K : ℝ) - (3 * K + 4) * (selbergTailRate R + η) / (2 * Real.pi)
          ≤ ((Finset.Icc 1 K \ badCriticalScaleDiscs (2 * R / Real.log V) K).card : ℝ) ∧
      ∀ hr : 0 < 2 * R / Real.log V,
        ∀ k ∈ Finset.Icc 1 K \ badCriticalScaleDiscs (2 * R / Real.log V) K,
          ∃ hne : ∀ ζ ∈ sphere (criticalScaleCenter (2 * R / Real.log V) k)
              (2 * R / Real.log V), xi ζ ≠ 0,
            ‖(xiDiscDatum (criticalScaleCenter (2 * R / Real.log V) k) (2 * R / Real.log V) hr
              hne).circlePhase.datum.adjointHankelSeam‖ < 1 :=
  eventually_goodCriticalScaleDiscs_of_tail hR (selbergTailRate_add_nonneg hR hη)
    (eventually_offLineTail_le_selberg hR hη)

/-! ## The shadow of the zeros beyond the critical scale -/

/-- **The `κ`-shadow against the tail.**  The heights `t ∈ [20, V]` shadowed by a zero with
`|Re ρ − ½| ≥ a` have measure at most `4 Σ_{0 < Im ρ ≤ V + 1} m_ρ (Re ρ − ½ − a/2)⁺`. -/
theorem volume_kappaShadow_le_offLineTail {a V : ℝ} (ha : 0 < a) :
    volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
        a ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} ≤
      ENNReal.ofReal (4 * offLineTail (a / 2) (V + 1)) := by
  classical
  set F := (stripFinsetPos (V + 1)).filter (fun w => 1 / 2 + a ≤ w.re) with hF
  have hsub : {t : ℝ | t ∈ Icc 20 V ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
      a ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} ⊆
      ⋃ w ∈ F, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    rintro t ⟨ht, ρ, hρ, hr, hdist⟩
    have hlt1 : ρ.re < 1 := by
      by_contra h; push Not at h; exact xi_ne_zero_of_one_le_re h hρ
    have hgt0 : 0 < ρ.re := by
      by_contra h
      push Not at h
      apply xi_ne_zero_of_one_le_re (ρ := 1 - ρ) (by simp; linarith)
      rw [xi_one_sub]; exact hρ
    obtain ⟨w, hw, hwre, hwim⟩ : ∃ w : ℂ, xi w = 0 ∧ w.re = 1 / 2 + |ρ.re - 1 / 2| ∧
        w.im = ρ.im := by
      rcases le_or_gt (1 / 2) ρ.re with h | h
      · exact ⟨ρ, hρ, by rw [abs_of_nonneg (by linarith)]; ring, rfl⟩
      · refine ⟨1 - (starRingEnd ℂ) ρ, by rw [xi_one_sub, xi_conj, hρ, map_zero], ?_, by simp⟩
        rw [abs_of_neg (by linarith)]; simp; ring
    have hrhalf : |ρ.re - 1 / 2| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    have htw : |t - w.im| ≤ w.re - 1 / 2 := by rw [hwim, hwre]; linarith
    have htw' := abs_le.mp htw
    have hwmem : w ∈ F := by
      refine Finset.mem_filter.mpr ⟨mem_stripFinsetPos.mpr ⟨?_, xi_zero_re_lt_one hw, ?_, ?_, hw⟩,
        by rw [hwre]; linarith⟩
      · rw [hwre]; positivity
      · linarith [ht.1]
      · linarith [ht.2]
    refine Set.mem_iUnion₂.mpr ⟨w, hwmem, ?_⟩
    exact ⟨by linarith, by linarith⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ w ∈ F, volume (Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2))) ≤
      ENNReal.ofReal (4 * (((analyticOrderAt xi w).toNat : ℝ) * max (w.re - 1 / 2 - a / 2) 0)) := by
    intro w hw
    obtain ⟨hwS, hwre⟩ := Finset.mem_filter.mp hw
    have hm := DeBruijn.one_le_toNat_analyticOrderAt_xi (mem_stripFinsetPos.mp hwS).2.2.2.2
    have hm' : (1 : ℝ) ≤ ((analyticOrderAt xi w).toNat : ℝ) := by exact_mod_cast hm
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    rw [max_eq_left (by linarith)]
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)

/-- **The `κ`-shadow beyond the critical scale, from a tail law at `R = κ/2`.**  For `κ > 0`, `η > 0` and all large
`V`, the heights `t ∈ [20, V]` shadowed by a zero with `|Re ρ − ½| ≥ κ/log V` have measure at most
`G(V + 1)/π`. -/
theorem eventually_volume_kappaShadow_le_of_tail {κ G : ℝ} (hκ : 0 < κ)
    (htail : ∀ᶠ V in atTop, 4 * Real.pi * offLineTail (κ / 2 / Real.log V) V ≤ G * V) :
    ∀ᶠ V in atTop,
      volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
          κ / Real.log V ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} ≤
        ENNReal.ofReal (G * (V + 1) / Real.pi) := by
  have hshift : Tendsto (fun V : ℝ => V + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  filter_upwards [hshift.eventually htail,
    eventually_gt_atTop (1 : ℝ)] with V hV hV1
  have hlog : 0 < Real.log V := Real.log_pos hV1
  refine (volume_kappaShadow_le_offLineTail (div_pos hκ hlog)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hanti : offLineTail (κ / Real.log V / 2) (V + 1)
      ≤ offLineTail (κ / 2 / Real.log (V + 1)) (V + 1) := by
    apply offLineTail_anti
    have hle : Real.log V ≤ Real.log (V + 1) := Real.log_le_log (by linarith) (by linarith)
    rw [div_div, div_div]
    exact div_le_div_of_nonneg_left hκ.le (by positivity) (by nlinarith)
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [le_div_iff₀ hπ]
  have := mul_le_mul_of_nonneg_left hanti (by norm_num : (0 : ℝ) ≤ 4)
  nlinarith


/-- **The `κ`-shadow beyond the critical scale, explicitly.**  For `κ > 0`, `η > 0` and all large
`V`, the heights `t ∈ [20, V]` shadowed by a zero with `|Re ρ − ½| ≥ κ/log V` have measure at most
`(g(κ/2) + η)(V + 1)/π`. -/
theorem eventually_volume_kappaShadow_le_selberg {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    ∀ᶠ V in atTop,
      volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
          κ / Real.log V ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} ≤
        ENNReal.ofReal ((selbergTailRate (κ / 2) + η) * (V + 1) / Real.pi) :=
  eventually_volume_kappaShadow_le_of_tail hκ
    (eventually_offLineTail_le_selberg (by positivity : 0 < κ / 2) hη)

end

end RHTower
