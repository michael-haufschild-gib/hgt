import GaloisForLFunctions.SquareRootThreshold.ZetaLagPositivityForcesCloseCompanions

/-!
# Hiding requires loud twins

`zeta_companion_law` assumes that no other exponent lies within `r` of the evaluation point
`s = (Re z* − κ/V) + i Im z*` below the Legendre record `z*`. Here the near zone `|z − s| < r` is
charged instead of excluded. On `[0, V]` the Fejér kernel is bounded by `V max(1, e^{Re w·V})`
(`norm_fejerWin_le_max`), so an exponent of the near zone costs at most
`V (|D(z)| + |D(z)| e^{(Re z − σ)V})`.

**Twin law** (`zeta_twin_law`). Under the hypotheses of the companion law without the exclusion,
positivity of the window functionals `P_v` on `[0, V]` forces
`(4/3) Π |D(z*)| (e^κ − 2) ≤ |M|(1/σ³ + 1/24) + (8/3) Σ|D| (1/64 + 1/r³)
  + (V³/2π²)(W_near + L_near)`,
`W_near = Σ_{near} |D(z)|`, `L_near = Σ_{near} |D(z)| e^{(Re z − σ)V}`. Since `|D(z*)| e^κ` is the
record's own loudness at `σ` (`|D(z*)| e^{(Re z* − σ)V}`), and `V³ ≥ (8/3)κ(κ² + 4π²)Π`, a record that
is not quiet can hide only if the near zone carries loudness `L_near + W_near ≳ |D(z*)| e^κ/κ³`:
other zeros within `r ≍ κ(log |Im z*|)^{1/3}/V` of the point just below the record, together nearly
as loud as the record itself. Off-line zeros of `ζ` can hide from the lag family only as loud
twins (clusters) of their Legendre records, at every lag.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- `|E_V(w)| ≤ V max(1, e^{Re w·V})`. -/
theorem norm_lapWin_le_max {V : ℝ} (hV : 0 ≤ V) (w : ℂ) :
    ‖lapWin V w‖ ≤ V * max 1 (Real.exp (w.re * V)) := by
  refine (norm_lapWin_le hV w).trans ?_
  have h : ∫ u in (0 : ℝ)..V, Real.exp (w.re * u) ≤ ∫ _u in (0 : ℝ)..V, max 1 (Real.exp (w.re * V)) :=
    intervalIntegral.integral_mono_on hV
      ((by fun_prop : Continuous fun u : ℝ => Real.exp (w.re * u)).intervalIntegrable _ _)
      intervalIntegrable_const fun u hu => by
        rcases le_or_gt 0 w.re with h | h
        · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 h)).trans (le_max_right _ _)
        · exact (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg h.le hu.1)).trans
            (le_max_left _ _)
  simpa using h

/-- `|F_V(w)| ≤ V max(1, e^{Re w·V})`. -/
theorem norm_fejerWin_le_max {V : ℝ} (hV : 0 ≤ V) (w : ℂ) :
    ‖fejerWin V w‖ ≤ V * max 1 (Real.exp (w.re * V)) := by
  have h : ∀ c : ℂ, c.re = 0 → ‖lapWin V (w + c)‖ ≤ V * max 1 (Real.exp (w.re * V)) := fun c hc => by
    have := norm_lapWin_le_max hV (w + c); rwa [Complex.add_re, hc, add_zero] at this
  have ha : (2 * π * I / V : ℂ).re = 0 := by simp
  have h1 := h 0 (by simp)
  have h2 := h _ ha
  have h3 := h (-(2 * π * I / V)) (by rw [Complex.neg_re, ha, neg_zero])
  rw [add_zero] at h1
  rw [← sub_eq_add_neg] at h3
  rw [fejerWin]
  calc ‖lapWin V w / 2 - lapWin V (w + 2 * π * I / V) / 4 - lapWin V (w - 2 * π * I / V) / 4‖
      ≤ ‖lapWin V w‖ / 2 + ‖lapWin V (w + 2 * π * I / V)‖ / 4 +
          ‖lapWin V (w - 2 * π * I / V)‖ / 4 := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans_eq ?_) ?_)
        · simp
        · simp
    _ ≤ V * max 1 (Real.exp (w.re * V)) := by linarith

/-- `|D| |F_V(z − s)| ≤ V(|D| + |D| e^{(Re z − Re s)V})` for every exponent. -/
theorem norm_mul_fejerWin_le_near {V : ℝ} (hV : 0 ≤ V) (d : ℝ) (hd : 0 ≤ d) (z s : ℂ) :
    d * ‖fejerWin V (z - s)‖ ≤ V * (d + d * Real.exp ((z.re - s.re) * V)) := by
  have := norm_fejerWin_le_max hV (z - s)
  rw [Complex.sub_re] at this
  calc d * ‖fejerWin V (z - s)‖ ≤ d * (V * max 1 (Real.exp ((z.re - s.re) * V))) :=
        mul_le_mul_of_nonneg_left this hd
    _ ≤ d * (V * (1 + Real.exp ((z.re - s.re) * V))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hV) hd
        exact max_le (by linarith [Real.exp_pos ((z.re - s.re) * V)])
          (by linarith)
    _ = _ := by ring

/-- **Twin law for `ζ`.** Under the hypotheses of `zeta_companion_law` without the exclusion of a
near zone, positivity of the window functionals on `[0, V]` forces
`(4/3) Π |D(z*)| (e^κ − 2) ≤ |M|(1/σ³ + 1/24) + (8/3) Σ_z |D(z)| (1/64 + 1/r³)
  + (V³/2π²) Σ_{0 < |z − s| < r} |D(z)| (1 + e^{(Re z − σ)V})`. -/
theorem zeta_twin_law {w V : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (hV : π ≤ V)
    (hP : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (lagPrimeWindowRHS v w (EF.weilTest
      (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig (modScaledBump w 0) z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hσ : 0 < z₁.re - κ / V) (hr : 0 < r) (hVr : 4 * π ≤ V * r)
    (hV3 : 8 / 3 * (κ * (κ ^ 2 + 4 * π ^ 2)) * (480 * Real.log 1080 * (1 / 64 + 3) +
      480 * Real.log (180 * (|z₁.im| + 6)) * (1 / r ^ 3 + 3)) ≤ V ^ 3) :
    4 / 3 * (480 * Real.log 1080 * (1 / 64 + 3) +
        480 * Real.log (180 * (|z₁.im| + 6)) * (1 / r ^ 3 + 3)) *
        ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * (Real.exp κ - 2) ≤
      |2 * (lagStructure zetaZeroConfig (modScaledBump w 0) 0).re| *
          (1 / (z₁.re - κ / V) ^ 3 + 1 / 24) +
        8 / 3 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖) *
          (1 / 64 + 1 / r ^ 3) +
        V ^ 3 / (2 * π ^ 2) * ∑' z : ℂ, (if evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 ∧
          z ≠ z₁ ∧ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ < r then
            ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ *
              (1 + Real.exp ((z.re - (z₁.re - κ / V)) * V)) else 0) := by
  classical
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs : ∀ u, b u ≠ 0 → |u| ≤ w := modScaledBump_support hw 0
  set D := evenCoeff zetaZeroConfig b with hDdef
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set σ : ℝ := z₁.re - κ / V with hσdef
  set θ : ℝ := κ / V with hθdef
  have hV0 : 0 < V := lt_of_lt_of_le Real.pi_pos hV
  have hθ0 : 0 < θ := div_pos hκ hV0
  have hθV : θ * V = κ := by rw [hθdef]; field_simp
  set s : ℂ := (σ : ℂ) + z₁.im * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = z₁.im := by simp [hs]
  -- the lag family is nonnegative on `[0, V]`
  have hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re :=
    fun v hv => by
      rw [hbdef, zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
        (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
        (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
          (modScaledBump_support hw 0)) v (-1)),
        literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv.1]
      exact hP v hv
  have hcore := norm_evenCoeff_mul_fejerWin_le zetaZeroConfig temperedConfig_zetaZeroConfig hb hbs
    hV0.le hm z₁ σ z₁.im
  rw [← hs] at hcore
  -- the record term
  have hz₁s : z₁ - s = (θ : ℂ) := by apply Complex.ext <;> simp [hs, hσdef, hθdef]
  have hLHS : ‖D z₁ * fejerWin V (z₁ - s)‖ =
      ‖D z₁‖ * (2 * π ^ 2 * (Real.exp κ - 1) / (θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2))) := by
    rw [norm_mul, hz₁s, norm_fejerWin_ofReal_pos hV0 hθ0, hθV]
  -- the loudness of every exponent, relative to the record
  have hloud : ∀ z, D z ≠ 0 → ‖D z‖ * Real.exp ((z.re - σ) * V) ≤ ‖D z₁‖ * Real.exp κ + ‖D z‖ :=
    fun z hz => by
      by_cases hre : 0 < z.re
      · have h := hrec z hz hre
        have e1 : ‖D z‖ * Real.exp ((z.re - σ) * V) =
            ‖D z‖ * Real.exp (z.re * V) * Real.exp (-σ * V) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        have e2 : ‖D z₁‖ * Real.exp κ = ‖D z₁‖ * Real.exp (z₁.re * V) * Real.exp (-σ * V) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; rw [hσdef]; linarith [hθV]
        rw [e1, e2]
        have := mul_le_mul_of_nonneg_right h (Real.exp_pos (-σ * V)).le
        linarith [norm_nonneg (D z)]
      · push Not at hre
        have : Real.exp ((z.re - σ) * V) ≤ 1 := Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) hV0.le)
        have := mul_le_mul_of_nonneg_left this (norm_nonneg (D z))
        have := mul_nonneg (norm_nonneg (D z₁)) (Real.exp_pos κ).le
        linarith
  set c : ℝ := 8 * π ^ 2 / 3 with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  -- potential kernels
  have hkern : ∀ {z u : ℂ} {d : ℝ}, 0 < d → 4 * π ≤ V * d → u.re = σ → D z ≠ 0 →
      d ≤ ‖z - u‖ → ‖D z‖ * ‖fejerWin V (z - u)‖ ≤
        c / V ^ 2 * (‖D z₁‖ * Real.exp κ * (1 / ‖z - u‖ ^ 3) + 2 * ‖D z‖ / d ^ 3) := by
    intro z u d hd hVd hu hz hgap
    have hzu : 0 < ‖z - u‖ := lt_of_lt_of_le hd hgap
    have h4 : 4 * π ≤ V * ‖z - u‖ := hVd.trans (mul_le_mul_of_nonneg_left hgap hV0.le)
    have hcube := norm_fejerWin_le_cube hV0 h4
    rw [Complex.sub_re, hu, ← hc] at hcube
    have hcube' : 1 / ‖z - u‖ ^ 3 ≤ 1 / d ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hd.le hgap 3)
    have hl := hloud z hz
    calc ‖D z‖ * ‖fejerWin V (z - u)‖
        ≤ ‖D z‖ * (c * (Real.exp ((z.re - σ) * V) + 1) / (V ^ 2 * ‖z - u‖ ^ 3)) :=
          mul_le_mul_of_nonneg_left hcube (norm_nonneg _)
      _ = c / V ^ 2 * ((‖D z‖ * Real.exp ((z.re - σ) * V) + ‖D z‖) * (1 / ‖z - u‖ ^ 3)) := by
          field_simp
      _ ≤ c / V ^ 2 * ((‖D z₁‖ * Real.exp κ + 2 * ‖D z‖) * (1 / ‖z - u‖ ^ 3)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by positivity)
          linarith
      _ ≤ c / V ^ 2 * (‖D z₁‖ * Real.exp κ * (1 / ‖z - u‖ ^ 3) + 2 * ‖D z‖ / d ^ 3) := by
          gcongr
          rw [add_mul]
          have : 2 * ‖D z‖ * (1 / ‖z - u‖ ^ 3) ≤ 2 * ‖D z‖ * (1 / d ^ 3) :=
            mul_le_mul_of_nonneg_left hcube' (by positivity)
          rw [show 2 * ‖D z‖ / d ^ 3 = 2 * ‖D z‖ * (1 / d ^ 3) by ring]
          linarith
  -- the potential sums
  have hsD := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig hb hbs
  obtain ⟨hs0, hP0b⟩ := tsum_inv_cube_le (b := b) (s := (σ : ℂ)) (r := 4) (by norm_num)
    (fun z => D z ≠ 0) fun z hz => ⟨hz, (four_le_abs_im_of_evenCoeff_zeta hz).trans (by
      have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this)⟩
  obtain ⟨hs1, hP1b⟩ := tsum_inv_cube_le (b := b) (s := s) hr
    (fun z => D z ≠ 0 ∧ z ≠ z₁ ∧ r ≤ ‖z - s‖) fun z hz => ⟨hz.1, hz.2.2⟩
  rw [show (|((σ : ℂ)).im| : ℝ) = 0 by simp, zero_add] at hP0b
  rw [hsim] at hP1b
  set P0 : ℝ := ∑' z : ℂ, (if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) with hP0
  set P1 : ℝ := ∑' z : ℂ, (if D z ≠ 0 ∧ z ≠ z₁ ∧ r ≤ ‖z - s‖ then 1 / ‖z - s‖ ^ 3 else 0)
    with hP1
  set Nn : ℝ := ∑' z : ℂ, (if D z ≠ 0 ∧ z ≠ z₁ ∧ ‖z - s‖ < r then
    ‖D z‖ * (1 + Real.exp ((z.re - σ) * V)) else 0) with hNn
  have hsN : Summable fun z : ℂ => (if D z ≠ 0 ∧ z ≠ z₁ ∧ ‖z - s‖ < r then
      ‖D z‖ * (1 + Real.exp ((z.re - σ) * V)) else 0) :=
    (hsD.mul_right (1 + Real.exp ((1 / 2 + |σ|) * V))).of_nonneg_of_le
      (fun z => by split_ifs <;> positivity) fun z => by
        split_ifs with h
        · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h1 : (z.re - σ) * V ≤ (1 / 2 + |σ|) * V := mul_le_mul_of_nonneg_right
            (by linarith [(abs_le.mp (abs_re_le_of_evenCoeff_ne_zero h.1)).2, neg_abs_le σ]) hV0.le
          linarith [Real.exp_le_exp.mpr h1]
        · positivity
  have hP0 : ∑' z : ℂ, ‖D z‖ * ‖fejerWin V (z - σ)‖ ≤
      c / V ^ 2 * (‖D z₁‖ * Real.exp κ * P0 + 2 * W / 4 ^ 3) := by
    have hle : ∀ z : ℂ, ‖D z‖ * ‖fejerWin V (z - σ)‖ ≤ c / V ^ 2 *
        (‖D z₁‖ * Real.exp κ * (if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) +
          2 * ‖D z‖ / 4 ^ 3) := fun z => by
      by_cases hz : D z = 0
      · simp only [hz, norm_zero, zero_mul, ne_eq, not_true_eq_false, if_false, mul_zero,
          zero_add, zero_div]
        positivity
      · rw [if_pos hz]
        exact hkern (by norm_num) (by linarith [Real.pi_pos]) (by simp) hz
          ((four_le_abs_im_of_evenCoeff_zeta hz).trans (by
            have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this))
    have hR : Summable fun z : ℂ => c / V ^ 2 *
        (‖D z₁‖ * Real.exp κ * (if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) +
          2 * ‖D z‖ / 4 ^ 3) :=
      ((hs0.mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _
    refine (Summable.tsum_le_tsum hle (hR.of_nonneg_of_le (fun _ => by positivity) hle) hR).trans
      (le_of_eq ?_)
    rw [tsum_mul_left, Summable.tsum_add (hs0.mul_left _) ((hsD.mul_left 2).div_const _),
      tsum_mul_left, tsum_div_const, tsum_mul_left]
  have hP1 : ∑' z : ℂ, (if z = z₁ then 0 else ‖D z‖ * ‖fejerWin V (z - s)‖) ≤
      c / V ^ 2 * (‖D z₁‖ * Real.exp κ * P1 + 2 * W / r ^ 3) + V * Nn := by
    have hle : ∀ z : ℂ, (if z = z₁ then 0 else ‖D z‖ * ‖fejerWin V (z - s)‖) ≤ c / V ^ 2 *
        (‖D z₁‖ * Real.exp κ * (if D z ≠ 0 ∧ z ≠ z₁ ∧ r ≤ ‖z - s‖ then 1 / ‖z - s‖ ^ 3 else 0) +
          2 * ‖D z‖ / r ^ 3) + V * (if D z ≠ 0 ∧ z ≠ z₁ ∧ ‖z - s‖ < r then
            ‖D z‖ * (1 + Real.exp ((z.re - σ) * V)) else 0) := fun z => by
      have hc0' : 0 ≤ c / V ^ 2 := by positivity
      by_cases hzz : z = z₁
      · rw [if_pos hzz]; split_ifs <;> positivity
      · rw [if_neg hzz]
        by_cases hz : D z = 0
        · simp only [hz, norm_zero, zero_mul, ne_eq, not_true_eq_false, false_and, if_false,
            mul_zero, zero_div, add_zero]
          positivity
        · by_cases hfar : r ≤ ‖z - s‖
          · rw [if_pos ⟨hz, hzz, hfar⟩, if_neg (fun h => absurd h.2.2 (not_lt.mpr hfar)), mul_zero,
              add_zero]
            exact hkern hr hVr hsre hz hfar
          · push Not at hfar
            rw [if_neg (fun h => absurd h.2.2 (not_le.mpr hfar)), if_pos ⟨hz, hzz, hfar⟩, mul_zero,
              zero_add]
            have hn := norm_mul_fejerWin_le_near hV0.le ‖D z‖ (norm_nonneg _) z s
            rw [hsre] at hn
            have h0 : 0 ≤ c / V ^ 2 * (2 * ‖D z‖ / r ^ 3) := by positivity
            calc ‖D z‖ * ‖fejerWin V (z - s)‖
                ≤ V * (‖D z‖ + ‖D z‖ * Real.exp ((z.re - σ) * V)) := hn
              _ = V * (‖D z‖ * (1 + Real.exp ((z.re - σ) * V))) := by ring
              _ ≤ _ := le_add_of_nonneg_left h0
    have hR : Summable fun z : ℂ => c / V ^ 2 *
        (‖D z₁‖ * Real.exp κ * (if D z ≠ 0 ∧ z ≠ z₁ ∧ r ≤ ‖z - s‖ then 1 / ‖z - s‖ ^ 3 else 0) +
          2 * ‖D z‖ / r ^ 3) + V * (if D z ≠ 0 ∧ z ≠ z₁ ∧ ‖z - s‖ < r then
            ‖D z‖ * (1 + Real.exp ((z.re - σ) * V)) else 0) :=
      (((hs1.mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _).add (hsN.mul_left V)
    refine (Summable.tsum_le_tsum hle (hR.of_nonneg_of_le
      (fun z => by split_ifs <;> positivity) hle) hR).trans (le_of_eq ?_)
    rw [Summable.tsum_add (((hs1.mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _)
      (hsN.mul_left V), tsum_mul_left, Summable.tsum_add (hs1.mul_left _)
      ((hsD.mul_left 2).div_const _), tsum_mul_left, tsum_div_const, tsum_mul_left, tsum_mul_left]
  -- the archimedean-pole kernels
  have hE1 : ‖fejerWin V (-(σ : ℂ))‖ ≤ 2 * π ^ 2 / (V ^ 2 * σ ^ 3) := norm_fejerWin_neg_le hV0 hσ
  have hE2 : ‖fejerWin V (-s)‖ ≤ c * 2 / (V ^ 2 * 4 ^ 3) := by
    have h4 : (4 : ℝ) ≤ ‖(0 : ℂ) - s‖ := by
      rw [zero_sub, norm_neg]
      exact (four_le_abs_im_of_evenCoeff_zeta hz₁).trans (by
        rw [← hsim]; exact Complex.abs_im_le_norm s)
    have := norm_fejerWin_sub_le hV0 (by norm_num) (by linarith [Real.pi_pos]) h4
    rw [zero_sub, Complex.zero_re, hsre, ← hc] at this
    refine this.trans ?_
    have : Real.exp ((0 - σ) * V) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hV0.le)
    gcongr
    linarith
  -- assemble, in units of `u = 2π²/V²`
  set u : ℝ := 2 * π ^ 2 / V ^ 2 with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  set Pb : ℝ := 480 * Real.log 1080 * (1 / 64 + 3) +
    480 * Real.log (180 * (|z₁.im| + 6)) * (1 / r ^ 3 + 3) with hPb
  have hPle : P0 + P1 ≤ Pb := by
    have h0 : P0 ≤ 480 * Real.log 1080 * (1 / 64 + 3) := by
      refine hP0b.trans (le_of_eq ?_); norm_num
    rw [hPb]; linarith [hP1b]
  have hcu : c / V ^ 2 = u * (4 / 3) := by rw [hc, hu]; field_simp; ring
  have hE1' : 2 * π ^ 2 / (V ^ 2 * σ ^ 3) = u * (1 / σ ^ 3) := by rw [hu]; field_simp
  have hE2' : c * 2 / (V ^ 2 * 4 ^ 3) = u * (1 / 24) := by rw [hc, hu]; field_simp; norm_num
  have hDe : 0 ≤ ‖D z₁‖ * Real.exp κ := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hbig : ‖D z₁‖ * (2 * π ^ 2 * (Real.exp κ - 1) / (θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2))) ≤
      u * (|M| * (1 / σ ^ 3 + 1 / 24) + 4 / 3 * (‖D z₁‖ * Real.exp κ) * Pb +
        8 / 3 * W * (1 / 64 + 1 / r ^ 3)) + V * Nn := by
    rw [← hLHS]
    refine hcore.trans ?_
    have h1 : |M| * (‖fejerWin V (-(σ : ℂ))‖ + ‖fejerWin V (-s)‖) ≤ u * (|M| * (1 / σ ^ 3 + 1 / 24)) := by
      calc |M| * (‖fejerWin V (-(σ : ℂ))‖ + ‖fejerWin V (-s)‖) ≤
            |M| * (u * (1 / σ ^ 3) + u * (1 / 24)) :=
            mul_le_mul_of_nonneg_left (add_le_add (hE1.trans_eq hE1') (hE2.trans_eq hE2'))
              (abs_nonneg M)
        _ = _ := by ring
    have h2 : c / V ^ 2 * (‖D z₁‖ * Real.exp κ * P0 + 2 * W / 4 ^ 3) +
        c / V ^ 2 * (‖D z₁‖ * Real.exp κ * P1 + 2 * W / r ^ 3) ≤
        u * (4 / 3 * (‖D z₁‖ * Real.exp κ) * Pb + 8 / 3 * W * (1 / 64 + 1 / r ^ 3)) := by
      rw [hcu]
      have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
      have : ‖D z₁‖ * Real.exp κ * (P0 + P1) ≤ ‖D z₁‖ * Real.exp κ * Pb :=
        mul_le_mul_of_nonneg_left hPle hDe
      have e : u * (4 / 3) * (‖D z₁‖ * Real.exp κ * P0 + 2 * W / 4 ^ 3) +
          u * (4 / 3) * (‖D z₁‖ * Real.exp κ * P1 + 2 * W / r ^ 3) =
          u * (4 / 3 * (‖D z₁‖ * Real.exp κ * (P0 + P1)) + 8 / 3 * W * (1 / 64 + 1 / r ^ 3)) := by
        ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ hu0.le
      linarith
    linarith
  -- `V³/(κ(κ² + 4π²)) ≥ (8/3)Π`
  have hQ : θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2) = κ * (κ ^ 2 + 4 * π ^ 2) / V := by
    rw [hθdef]; field_simp
  have hQ0 : 0 < κ * (κ ^ 2 + 4 * π ^ 2) := by positivity
  have hexp : 0 ≤ Real.exp κ - 1 := by linarith [Real.one_le_exp hκ.le]
  have hlow : u * (8 / 3 * Pb * (‖D z₁‖ * (Real.exp κ - 1))) ≤
      ‖D z₁‖ * (2 * π ^ 2 * (Real.exp κ - 1) / (θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2))) := by
    rw [hQ]
    have hX : 0 ≤ ‖D z₁‖ * (Real.exp κ - 1) := mul_nonneg (norm_nonneg _) hexp
    have hk : u * (8 / 3 * Pb) ≤ 2 * π ^ 2 / (κ * (κ ^ 2 + 4 * π ^ 2) / V) := by
      rw [hu, div_div_eq_mul_div, le_div_iff₀ hQ0]
      have : 8 / 3 * Pb * (κ * (κ ^ 2 + 4 * π ^ 2)) ≤ V ^ 3 :=
        calc 8 / 3 * Pb * (κ * (κ ^ 2 + 4 * π ^ 2)) = 8 / 3 * (κ * (κ ^ 2 + 4 * π ^ 2)) * Pb := by
              ring
          _ ≤ V ^ 3 := hV3
      calc 2 * π ^ 2 / V ^ 2 * (8 / 3 * Pb) * (κ * (κ ^ 2 + 4 * π ^ 2))
          = 2 * π ^ 2 / V ^ 2 * (8 / 3 * Pb * (κ * (κ ^ 2 + 4 * π ^ 2))) := by ring
        _ ≤ 2 * π ^ 2 / V ^ 2 * V ^ 3 := mul_le_mul_of_nonneg_left this (by positivity)
        _ = 2 * π ^ 2 * V := by field_simp
    calc u * (8 / 3 * Pb * (‖D z₁‖ * (Real.exp κ - 1)))
        = u * (8 / 3 * Pb) * (‖D z₁‖ * (Real.exp κ - 1)) := by ring
      _ ≤ 2 * π ^ 2 / (κ * (κ ^ 2 + 4 * π ^ 2) / V) * (‖D z₁‖ * (Real.exp κ - 1)) :=
          mul_le_mul_of_nonneg_right hk hX
      _ = ‖D z₁‖ * (2 * π ^ 2 * (Real.exp κ - 1) / (κ * (κ ^ 2 + 4 * π ^ 2) / V)) := by ring
  have hVN : V * Nn = u * (V ^ 3 / (2 * π ^ 2) * Nn) := by rw [hu]; field_simp
  have hcomb := hlow.trans hbig
  rw [hVN, ← mul_add] at hcomb
  have hfin := le_of_mul_le_mul_left hcomb hu0
  linarith

end GaloisForLFunctions.SquareRootThreshold
