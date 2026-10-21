import GaloisForLFunctions.SquareRootThreshold.FejerPowerLagWindowKernel
import GaloisForLFunctions.SquareRootThreshold.ModulatedLagFamilySeesNearTopZerosOfZeta

/-!
# The twin radius of `ζ` at the uncertainty scale

With the weight `sin²(πu/V)` the twin law (`zeta_twin_law_of_bump`) places the loud twin of a record
within `r ≍ κ (log γ*)^{1/3}/V`: the potential of the competitors is cubic, and the local zero
count `L = log(180(|γ*| + 6))` enters through `L^{1/3}`. The weight `sin^{2k}(πu/V)` of
`FejerPowerLagWindowKernel` has kernel decay `|z|^{−(2k+1)}`, so the count enters through
`L^{1/(2k+1)}`, and the price is the factor `(κ² + 4π²k²)^k` of the record term at depth `κ/V`.

**Twin law of order `k`** (`zeta_powTwin_law`). For `k ≥ 1`, `V ≥ πk`, `0 < r ≤ 4`, `Vr ≥ 4πk`,
`2(4/3)^k κ(κ² + 4π²k²)^k Π ≤ V^{2k+1} r^{2k−2}`, nonnegativity of the window functionals on `[0, V]`
forces `(4/3)^k (Π/r^{2k−2}) |D(z*)| (e^κ − 2)` below the archimedean and total-mass terms plus
`V^{2k+1}/((2k)! π^{2k})` times the loudness of the near zone `|z − s| < r`.

**Loud records** (`exists_loud_record_of_near_top`, `zeta_powTwin_of_record`). For a zero
`1/V`-near the top, modulated to its height, the record keeps `|D(z*)| ≥ a_w²/(2e)`; a record of
known loudness that is not quiet has a twin.

**Twin radius** (`zeta_near_top_twin_radius`, `zeta_near_top_twin_radius_log_log`). With
`κ = log(3 + e(|M| + W)/(60 L a_w²))` (`twinDepth`), every `k ≥ 1` with `log L ≤ 2k + 1` gives the
radius `73(κ + 2πk)/V`; with `k = ⌈(log L)/2⌉ + 1`:

  if the modulated difference tests are Weil nonnegative on `[0, V]` and
  `V ≥ 73(κ + π log L + 4π) max(1, 2/Re z*)`, another zero of `ζ` lies within
  `73(κ + π log log(180(|γ*| + 6)) + 4π)/V` of `(Re z* − κ/V) + i Im z*`.

The lag window `[0, V]` cannot resolve below `1/V`; the twin radius is at this uncertainty scale up to
`κ + log log γ*`. Against the mean spacing `2π/log γ*` of the zeros, positivity on `[0, V]` with
`V ≫ (κ + log log γ*) log γ*` forces a near-top zero into a pair closer than the mean spacing, at
the depth of the record; the square-root threshold `V ≍ log γ` is missed by the factor
`κ + log log γ`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- `1/x^{2k+1} ≤ (1/x³)/d^{2k−2}` for `x ≥ d > 0`, `k ≥ 1`. -/
theorem one_div_pow_le_cube {x d : ℝ} (hd : 0 < d) (hx : d ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    1 / x ^ (2 * k + 1) ≤ 1 / x ^ 3 / d ^ (2 * k - 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le hd hx
  rw [show 2 * k + 1 = 3 + (2 * k - 2) by omega, pow_add, div_div, one_div_le_one_div
    (by positivity) (by positivity)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hx _) (by positivity)

/-- **Twin law for `ζ` with the weight `sin^{2k}(πu/V)`.** Let `k ≥ 1`, `V ≥ πk`, let the difference
tests of a `C²` bump be Weil nonnegative on `[0, V]`, let `z*` be the Legendre record at lag `V`,
`σ = Re z* − κ/V > 0`, `s = σ + i Im z*`, `0 < r ≤ 4`, `Vr ≥ 4πk`, and
`2(4/3)^k κ(κ² + 4π²k²)^k Π ≤ V^{2k+1} r^{2k−2}`, `Π = twinPotential r (Im z*)`. Then
`(4/3)^k (Π/r^{2k−2}) |D(z*)| (e^κ − 2) ≤ |M|(2/σ^{2k+1} + 2(4/3)^k/4^{2k+1})
  + 2(4/3)^k W (1/4^{2k+1} + 1/r^{2k+1}) + V^{2k+1}/((2k)! π^{2k}) Σ_{0 < |z − s| < r} |D(z)|(1 + e^{(Re z − σ)V})`. -/
theorem zeta_powTwin_law {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {k : ℕ} (hk : 1 ≤ k) {V : ℝ} (hV : π * k ≤ V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig b z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hσ : 0 < z₁.re - κ / V) (hr : 0 < r) (hr4 : r ≤ 4)
    (hVr : 4 * π * k ≤ V * r)
    (hVk : 2 * (4 / 3) ^ k * (κ * (κ ^ 2 + 4 * π ^ 2 * k ^ 2) ^ k) * twinPotential r z₁.im ≤
      V ^ (2 * k + 1) * r ^ (2 * k - 2)) :
    (4 / 3) ^ k * (twinPotential r z₁.im / r ^ (2 * k - 2)) * ‖evenCoeff zetaZeroConfig b z₁‖ *
        (Real.exp κ - 2) ≤
      |2 * (lagStructure zetaZeroConfig b 0).re| *
          (2 / (z₁.re - κ / V) ^ (2 * k + 1) + 2 * (4 / 3) ^ k / 4 ^ (2 * k + 1)) +
        2 * (4 / 3) ^ k * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) *
          (1 / 4 ^ (2 * k + 1) + 1 / r ^ (2 * k + 1)) +
        V ^ (2 * k + 1) / ((2 * k).factorial * π ^ (2 * k)) *
          ∑' z : ℂ, (if evenCoeff zetaZeroConfig b z ≠ 0 ∧ z ≠ z₁ ∧
            ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ < r then
              ‖evenCoeff zetaZeroConfig b z‖ * (1 + Real.exp ((z.re - (z₁.re - κ / V)) * V))
            else 0) := by
  classical
  set D := evenCoeff zetaZeroConfig b with hDdef
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set σ : ℝ := z₁.re - κ / V with hσdef
  set θ : ℝ := κ / V with hθdef
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  have hθ0 : 0 < θ := div_pos hκ hV0
  have hθV : θ * V = κ := by rw [hθdef]; field_simp
  set s : ℂ := (σ : ℂ) + z₁.im * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = z₁.im := by simp [hs]
  set ck : ℝ := (4 / 3) ^ k with hck
  set uk : ℝ := (2 * k).factorial * (π / V) ^ (2 * k) with huk
  have hck0 : 0 < ck := by positivity
  have huk0 : 0 < uk := by positivity
  set Q : ℝ := (κ ^ 2 + 4 * π ^ 2 * k ^ 2) ^ k with hQ
  have hQ0 : 0 < Q := by positivity
  have hcore := norm_evenCoeff_mul_fejerPowWin_le zetaZeroConfig temperedConfig_zetaZeroConfig hb
    hbs hV0.le k hm z₁ σ z₁.im
  rw [← hs] at hcore
  -- the record term
  have hz₁s : z₁ - s = (θ : ℂ) := by apply Complex.ext <;> simp [hs, hσdef, hθdef]
  have hLHS : uk * (Real.exp κ - 1) * V ^ (2 * k + 1) / (κ * Q) ≤ ‖fejerPowWin k V (z₁ - s)‖ := by
    rw [hz₁s]
    refine le_trans (le_of_eq ?_) (norm_fejerPowWin_ofReal_ge hV0 k hθ0)
    have e : θ ^ 2 + (2 * π * k / V) ^ 2 = (κ ^ 2 + 4 * π ^ 2 * k ^ 2) / V ^ 2 := by
      rw [hθdef]; field_simp; ring
    have hVne : V ≠ 0 := hV0.ne'
    have hκne : κ ≠ 0 := hκ.ne'
    rw [e, hθV, hθdef, huk, hQ, div_pow, div_pow, ← pow_mul V 2 k, pow_succ]
    field_simp
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
  -- potential kernels
  have hkern : ∀ {z u : ℂ} {d : ℝ}, 0 < d → 4 * π * k ≤ V * d → u.re = σ → D z ≠ 0 →
      d ≤ ‖z - u‖ → ‖D z‖ * ‖fejerPowWin k V (z - u)‖ ≤
        ck * uk * (‖D z₁‖ * Real.exp κ * (1 / ‖z - u‖ ^ 3 / d ^ (2 * k - 2)) +
          2 * ‖D z‖ / d ^ (2 * k + 1)) := by
    intro z u d hd hVd hu hz hgap
    have hzu : 0 < ‖z - u‖ := lt_of_lt_of_le hd hgap
    have h4 : 4 * π * k ≤ V * ‖z - u‖ := hVd.trans (mul_le_mul_of_nonneg_left hgap hV0.le)
    have hdec := norm_fejerPowWin_le_decay hV0 k (norm_pos_iff.mp hzu) h4
    rw [Complex.sub_re, hu] at hdec
    have hp1 := one_div_pow_le_cube hd hgap hk
    have hp2 : 1 / ‖z - u‖ ^ (2 * k + 1) ≤ 1 / d ^ (2 * k + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hd.le hgap _)
    have hl := hloud z hz
    calc ‖D z‖ * ‖fejerPowWin k V (z - u)‖
        ≤ ‖D z‖ * ((4 / 3) ^ k * (2 * k).factorial * (π / V) ^ (2 * k) *
            (Real.exp ((z.re - σ) * V) + 1) / ‖z - u‖ ^ (2 * k + 1)) :=
          mul_le_mul_of_nonneg_left hdec (norm_nonneg _)
      _ = ck * uk * ((‖D z‖ * Real.exp ((z.re - σ) * V) + ‖D z‖) *
            (1 / ‖z - u‖ ^ (2 * k + 1))) := by rw [hck, huk]; field_simp
      _ ≤ ck * uk * ((‖D z₁‖ * Real.exp κ + 2 * ‖D z‖) * (1 / ‖z - u‖ ^ (2 * k + 1))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by positivity)
          linarith
      _ ≤ ck * uk * (‖D z₁‖ * Real.exp κ * (1 / ‖z - u‖ ^ 3 / d ^ (2 * k - 2)) +
            2 * ‖D z‖ / d ^ (2 * k + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [add_mul, show 2 * ‖D z‖ / d ^ (2 * k + 1) = 2 * ‖D z‖ * (1 / d ^ (2 * k + 1)) by
            ring]
          exact add_le_add (mul_le_mul_of_nonneg_left hp1 (by positivity))
            (mul_le_mul_of_nonneg_left hp2 (by positivity))
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
  have hV4 : 4 * π * k ≤ V * 4 := by linarith
  have hP0 : ∑' z : ℂ, ‖D z‖ * ‖fejerPowWin k V (z - σ)‖ ≤
      ck * uk * (‖D z₁‖ * Real.exp κ * (P0 / 4 ^ (2 * k - 2)) + 2 * W / 4 ^ (2 * k + 1)) := by
    have hle : ∀ z : ℂ, ‖D z‖ * ‖fejerPowWin k V (z - σ)‖ ≤ ck * uk *
        (‖D z₁‖ * Real.exp κ * ((if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) / 4 ^ (2 * k - 2)) +
          2 * ‖D z‖ / 4 ^ (2 * k + 1)) := fun z => by
      by_cases hz : D z = 0
      · simp only [hz, norm_zero, zero_mul, ne_eq, not_true_eq_false, if_false, zero_div,
          mul_zero, zero_add]
        positivity
      · rw [if_pos hz]
        exact hkern (by norm_num) hV4 (by simp) hz
          ((four_le_abs_im_of_evenCoeff_zeta hz).trans (by
            have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this))
    have hR : Summable fun z : ℂ => ck * uk *
        (‖D z₁‖ * Real.exp κ * ((if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) / 4 ^ (2 * k - 2)) +
          2 * ‖D z‖ / 4 ^ (2 * k + 1)) :=
      (((hs0.div_const _).mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _
    refine (Summable.tsum_le_tsum hle (hR.of_nonneg_of_le (fun _ => by positivity) hle) hR).trans
      (le_of_eq ?_)
    rw [tsum_mul_left, Summable.tsum_add ((hs0.div_const _).mul_left _)
      ((hsD.mul_left 2).div_const _), tsum_mul_left, tsum_div_const, tsum_div_const, tsum_mul_left]
  have hP1 : ∑' z : ℂ, (if z = z₁ then 0 else ‖D z‖ * ‖fejerPowWin k V (z - s)‖) ≤
      ck * uk * (‖D z₁‖ * Real.exp κ * (P1 / r ^ (2 * k - 2)) + 2 * W / r ^ (2 * k + 1)) +
        V * Nn := by
    have hle : ∀ z : ℂ, (if z = z₁ then 0 else ‖D z‖ * ‖fejerPowWin k V (z - s)‖) ≤ ck * uk *
        (‖D z₁‖ * Real.exp κ * ((if D z ≠ 0 ∧ z ≠ z₁ ∧ r ≤ ‖z - s‖ then 1 / ‖z - s‖ ^ 3 else 0) /
          r ^ (2 * k - 2)) + 2 * ‖D z‖ / r ^ (2 * k + 1)) +
          V * (if D z ≠ 0 ∧ z ≠ z₁ ∧ ‖z - s‖ < r then
            ‖D z‖ * (1 + Real.exp ((z.re - σ) * V)) else 0) := fun z => by
      have hc0' : 0 ≤ ck * uk := by positivity
      by_cases hzz : z = z₁
      · rw [if_pos hzz]; split_ifs <;> positivity
      · rw [if_neg hzz]
        by_cases hz : D z = 0
        · simp only [hz, norm_zero, zero_mul, ne_eq, not_true_eq_false, false_and, if_false,
            zero_div, mul_zero, add_zero]
          positivity
        · by_cases hfar : r ≤ ‖z - s‖
          · rw [if_pos ⟨hz, hzz, hfar⟩, if_neg (fun h => absurd h.2.2 (not_lt.mpr hfar)), mul_zero,
              add_zero]
            exact hkern hr hVr hsre hz hfar
          · push Not at hfar
            rw [if_neg (fun h => absurd h.2.2 (not_le.mpr hfar)), if_pos ⟨hz, hzz, hfar⟩, zero_div,
              mul_zero, zero_add]
            have hn := norm_fejerPowWin_le_max hV0.le k (z - s)
            rw [Complex.sub_re, hsre] at hn
            have h0 : 0 ≤ ck * uk * (2 * ‖D z‖ / r ^ (2 * k + 1)) := by positivity
            have hmax : max 1 (Real.exp ((z.re - σ) * V)) ≤ 1 + Real.exp ((z.re - σ) * V) :=
              max_le (by linarith [Real.exp_pos ((z.re - σ) * V)]) (by linarith)
            calc ‖D z‖ * ‖fejerPowWin k V (z - s)‖
                ≤ ‖D z‖ * (V * (1 + Real.exp ((z.re - σ) * V))) :=
                  mul_le_mul_of_nonneg_left (hn.trans (mul_le_mul_of_nonneg_left hmax hV0.le))
                    (norm_nonneg _)
              _ = V * (‖D z‖ * (1 + Real.exp ((z.re - σ) * V))) := by ring
              _ ≤ _ := le_add_of_nonneg_left h0
    have hR : Summable fun z : ℂ => ck * uk *
        (‖D z₁‖ * Real.exp κ * ((if D z ≠ 0 ∧ z ≠ z₁ ∧ r ≤ ‖z - s‖ then 1 / ‖z - s‖ ^ 3 else 0) /
          r ^ (2 * k - 2)) + 2 * ‖D z‖ / r ^ (2 * k + 1)) +
          V * (if D z ≠ 0 ∧ z ≠ z₁ ∧ ‖z - s‖ < r then
            ‖D z‖ * (1 + Real.exp ((z.re - σ) * V)) else 0) :=
      ((((hs1.div_const _).mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _).add
        (hsN.mul_left V)
    refine (Summable.tsum_le_tsum hle (hR.of_nonneg_of_le
      (fun z => by split_ifs <;> positivity) hle) hR).trans (le_of_eq ?_)
    rw [Summable.tsum_add ((((hs1.div_const _).mul_left _).add
      ((hsD.mul_left 2).div_const _)).mul_left _) (hsN.mul_left V), tsum_mul_left,
      Summable.tsum_add ((hs1.div_const _).mul_left _) ((hsD.mul_left 2).div_const _),
      tsum_mul_left, tsum_div_const, tsum_div_const, tsum_mul_left, tsum_mul_left]
  -- the archimedean-pole kernels
  have hE1 : ‖fejerPowWin k V (-(σ : ℂ))‖ ≤ uk * (2 / σ ^ (2 * k + 1)) := by
    have := norm_fejerPowWin_neg_le hV0 k hσ
    rw [huk]; refine this.trans (le_of_eq ?_); ring
  have hE2 : ‖fejerPowWin k V (-s)‖ ≤ uk * (2 * ck / 4 ^ (2 * k + 1)) := by
    have h4 : (4 : ℝ) ≤ ‖s‖ := (four_le_abs_im_of_evenCoeff_zeta hz₁).trans (by
      rw [← hsim]; exact Complex.abs_im_le_norm s)
    have hs0' : -s ≠ 0 := fun h => by
      rw [neg_eq_zero] at h; rw [h, norm_zero] at h4; norm_num at h4
    have hdec := norm_fejerPowWin_le_decay hV0 k hs0' (by
      rw [norm_neg]; exact hV4.trans (mul_le_mul_of_nonneg_left h4 hV0.le))
    rw [norm_neg, Complex.neg_re, hsre] at hdec
    refine hdec.trans ?_
    have he : Real.exp (-σ * V) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ.le) hV0.le)
    have hpow : (4 : ℝ) ^ (2 * k + 1) ≤ ‖s‖ ^ (2 * k + 1) := pow_le_pow_left₀ (by norm_num) h4 _
    calc (4 / 3) ^ k * ((2 * k).factorial : ℝ) * (π / V) ^ (2 * k) * (Real.exp (-σ * V) + 1) /
          ‖s‖ ^ (2 * k + 1)
        ≤ (4 / 3) ^ k * ((2 * k).factorial : ℝ) * (π / V) ^ (2 * k) * 2 / 4 ^ (2 * k + 1) := by
          gcongr; linarith
      _ = uk * (2 * ck / 4 ^ (2 * k + 1)) := by rw [huk, hck]; ring
  -- assemble, in units of `u_k = (2k)! (π/V)^{2k}`
  set Pb : ℝ := twinPotential r z₁.im with hPb
  have hPle : P0 + P1 ≤ Pb := by
    have h0 : P0 ≤ 480 * Real.log 1080 * (1 / 64 + 3) := by
      refine hP0b.trans (le_of_eq ?_); norm_num
    rw [hPb, twinPotential]; linarith [hP1b]
  have hP0' : 0 ≤ P0 := tsum_nonneg fun z => by split_ifs <;> positivity
  have hP1' : 0 ≤ P1 := tsum_nonneg fun z => by split_ifs <;> positivity
  have hr4' : 1 / (4 : ℝ) ^ (2 * k - 2) ≤ 1 / r ^ (2 * k - 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hr.le hr4 _)
  have hPr : P0 / 4 ^ (2 * k - 2) + P1 / r ^ (2 * k - 2) ≤ Pb / r ^ (2 * k - 2) := by
    have h1 : P0 / 4 ^ (2 * k - 2) ≤ P0 / r ^ (2 * k - 2) := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div P0]
      exact mul_le_mul_of_nonneg_left hr4' hP0'
    calc P0 / 4 ^ (2 * k - 2) + P1 / r ^ (2 * k - 2) ≤ P0 / r ^ (2 * k - 2) + P1 / r ^ (2 * k - 2) := by
          linarith
      _ = (P0 + P1) / r ^ (2 * k - 2) := by rw [add_div]
      _ ≤ Pb / r ^ (2 * k - 2) := div_le_div_of_nonneg_right hPle (by positivity)
  have hDe : 0 ≤ ‖D z₁‖ * Real.exp κ := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
  have hbig : ‖D z₁‖ * ‖fejerPowWin k V (z₁ - s)‖ ≤
      uk * (|M| * (2 / σ ^ (2 * k + 1) + 2 * ck / 4 ^ (2 * k + 1)) +
        ck * (‖D z₁‖ * Real.exp κ) * (Pb / r ^ (2 * k - 2)) +
        2 * ck * W * (1 / 4 ^ (2 * k + 1) + 1 / r ^ (2 * k + 1))) + V * Nn := by
    rw [← norm_mul]
    refine hcore.trans ?_
    have h1 : |M| * (‖fejerPowWin k V (-(σ : ℂ))‖ + ‖fejerPowWin k V (-s)‖) ≤
        uk * (|M| * (2 / σ ^ (2 * k + 1) + 2 * ck / 4 ^ (2 * k + 1))) := by
      calc |M| * (‖fejerPowWin k V (-(σ : ℂ))‖ + ‖fejerPowWin k V (-s)‖) ≤
            |M| * (uk * (2 / σ ^ (2 * k + 1)) + uk * (2 * ck / 4 ^ (2 * k + 1))) :=
            mul_le_mul_of_nonneg_left (add_le_add hE1 hE2) (abs_nonneg M)
        _ = _ := by ring
    have h2 : ck * uk * (‖D z₁‖ * Real.exp κ * (P0 / 4 ^ (2 * k - 2)) + 2 * W / 4 ^ (2 * k + 1)) +
        ck * uk * (‖D z₁‖ * Real.exp κ * (P1 / r ^ (2 * k - 2)) + 2 * W / r ^ (2 * k + 1)) ≤
        uk * (ck * (‖D z₁‖ * Real.exp κ) * (Pb / r ^ (2 * k - 2)) +
          2 * ck * W * (1 / 4 ^ (2 * k + 1) + 1 / r ^ (2 * k + 1))) := by
      have := mul_le_mul_of_nonneg_left hPr hDe
      have e : ck * uk * (‖D z₁‖ * Real.exp κ * (P0 / 4 ^ (2 * k - 2)) + 2 * W / 4 ^ (2 * k + 1)) +
          ck * uk * (‖D z₁‖ * Real.exp κ * (P1 / r ^ (2 * k - 2)) + 2 * W / r ^ (2 * k + 1)) =
          uk * (ck * (‖D z₁‖ * Real.exp κ * (P0 / 4 ^ (2 * k - 2) + P1 / r ^ (2 * k - 2))) +
            2 * ck * W * (1 / 4 ^ (2 * k + 1) + 1 / r ^ (2 * k + 1))) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ huk0.le
      have := mul_le_mul_of_nonneg_left this hck0.le
      linarith
    linarith
  -- `V^{2k+1} r^{2k−2} ≥ 2(4/3)^k κ Q Π`
  have hlow : uk * (2 * ck * (Pb / r ^ (2 * k - 2)) * (‖D z₁‖ * (Real.exp κ - 1))) ≤
      ‖D z₁‖ * ‖fejerPowWin k V (z₁ - s)‖ := by
    have hexp : 0 ≤ Real.exp κ - 1 := by linarith [Real.one_le_exp hκ.le]
    have hX : 0 ≤ ‖D z₁‖ * (Real.exp κ - 1) := mul_nonneg (norm_nonneg _) hexp
    have hk' : 2 * ck * (Pb / r ^ (2 * k - 2)) ≤ V ^ (2 * k + 1) / (κ * Q) := by
      rw [le_div_iff₀ (by positivity), show 2 * ck * (Pb / r ^ (2 * k - 2)) * (κ * Q) =
        2 * ck * Pb * (κ * Q) / r ^ (2 * k - 2) by ring, div_le_iff₀ (by positivity)]
      calc 2 * ck * Pb * (κ * Q) = 2 * (4 / 3) ^ k * (κ * (κ ^ 2 + 4 * π ^ 2 * k ^ 2) ^ k) *
            twinPotential r z₁.im := by rw [hck, hQ, hPb]; ring
        _ ≤ _ := hVk
    calc uk * (2 * ck * (Pb / r ^ (2 * k - 2)) * (‖D z₁‖ * (Real.exp κ - 1)))
        ≤ uk * (V ^ (2 * k + 1) / (κ * Q) * (‖D z₁‖ * (Real.exp κ - 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk' hX) huk0.le
      _ = ‖D z₁‖ * (uk * (Real.exp κ - 1) * V ^ (2 * k + 1) / (κ * Q)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLHS (norm_nonneg _)
  have hVN : V * Nn = uk * (V ^ (2 * k + 1) / ((2 * k).factorial * π ^ (2 * k)) * Nn) := by
    rw [huk, div_pow, pow_succ]; field_simp
  have hcomb := hlow.trans hbig
  rw [hVN, ← mul_add] at hcomb
  have hfin := le_of_mul_le_mul_left hcomb huk0
  rw [hck] at hfin ⊢
  linarith

/-! ### Near-top zeros and their records -/

/-- **A near-top zero makes a loud record.** Let `½ + z₀` be a zero right of the line at height
`γ₀ = Im z₀ > 0` with `40 log(180γ₀)(e^{w/2}B_w)²(1 + 2γ₀)^{−4} ≤ a_w²/2`, which is `1/V`-near the
top of the family modulated to `γ₀`. Then the Legendre record `z*` at lag `V` exists and keeps the
coefficient `|D(z*)| ≥ a_w²/(2e)`. -/
theorem exists_loud_record_of_near_top {w V : ℝ} (hw : 0 < w) (hV : 0 < V) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re) (him₀ : 0 < z₀.im)
    (hΓ : 40 * Real.log (180 * z₀.im) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
      (1 + 2 * z₀.im) ^ 4 ≤ centerAmplitude w ^ 2 / 2)
    (htop : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → z.re ≤ z₀.re + 1 / V) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧ 0 < z₁.re ∧
      centerAmplitude w ^ 2 / (2 * Real.exp 1) ≤
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ ∧
      ∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ * Real.exp (z₁.re * V) := by
  set b := modScaledBump w z₀.im with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set a := centerAmplitude w with ha
  have ha0 : 0 < a := centerAmplitude_pos hw
  have hD₀ : a ^ 2 / 2 ≤ ‖D z₀‖ := by
    have := norm_evenCoeff_modScaledBump_center_ge hw hz₀ hre₀ him₀
    rw [show 4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u)) = a from rfl] at this
    linarith
  have hD₀ne : D z₀ ≠ 0 := fun h => by
    rw [h, norm_zero] at hD₀; nlinarith
  obtain ⟨z₁, hz₁, hre₁, hrec⟩ := exists_right_record zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w _) (modScaledBump_support hw _) hV.le hD₀ne hre₀
  refine ⟨z₁, hz₁, hre₁, ?_, hrec⟩
  have h1 := hrec z₀ hD₀ne hre₀
  have h2 := htop z₁ hz₁
  have h3 : Real.exp (z₁.re * V) ≤ Real.exp (z₀.re * V) * Real.exp 1 := by
    rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
    have : (z₁.re - z₀.re) * V ≤ 1 := by
      have := mul_le_mul_of_nonneg_right (show z₁.re - z₀.re ≤ 1 / V by linarith) hV.le
      rwa [div_mul_cancel₀ _ hV.ne'] at this
    linarith
  have hE := Real.exp_pos (z₀.re * V)
  have h5 : ‖D z₀‖ ≤ ‖D z₁‖ * Real.exp 1 := by
    have : ‖D z₀‖ * Real.exp (z₀.re * V) ≤ (‖D z₁‖ * Real.exp 1) * Real.exp (z₀.re * V) := by
      have := h1.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg (D z₁)))
      linarith
    exact le_of_mul_le_mul_right this hE
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Loud records have twins of order `k`.** Let the difference tests of a `C²` bump be Weil
nonnegative on `[0, V]`, `k ≥ 1`, `V ≥ πk`, and let `z*` be the Legendre record at lag `V` with
`|D(z*)| ≥ ε`. For every `κ > 0` and `0 < r ≤ 4` with `Vr ≥ 4πk`, `V ≥ 2κ/Re z*`,
`2(4/3)^k κ(κ² + 4π²k²)^k Π ≤ V^{2k+1} r^{2k−2}` and the non-quietness
`|M|(2(2/Re z*)^{2k+1} + 2(4/3)^k/4^{2k+1}) + 2(4/3)^k W(1/4^{2k+1} + 1/r^{2k+1})
  < (4/3)^k (Π/r^{2k−2}) ε (e^κ − 2)`,
another exponent lies within `r` of `(Re z* − κ/V) + i Im z*`. -/
theorem zeta_powTwin_of_record {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {k : ℕ} (hk : 1 ≤ k) {V : ℝ} (hV : π * k ≤ V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig b z₁ ≠ 0) (hre₁ : 0 < z₁.re)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ ‖evenCoeff zetaZeroConfig b z₁‖)
    {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hr4 : r ≤ 4) (hVr : 4 * π * k ≤ V * r)
    (hκV : 2 * κ / z₁.re ≤ V)
    (hVk : 2 * (4 / 3) ^ k * (κ * (κ ^ 2 + 4 * π ^ 2 * k ^ 2) ^ k) * twinPotential r z₁.im ≤
      V ^ (2 * k + 1) * r ^ (2 * k - 2))
    (hNQ : |2 * (lagStructure zetaZeroConfig b 0).re| *
          (2 * (2 / z₁.re) ^ (2 * k + 1) + 2 * (4 / 3) ^ k / 4 ^ (2 * k + 1)) +
        2 * (4 / 3) ^ k * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) *
          (1 / 4 ^ (2 * k + 1) + 1 / r ^ (2 * k + 1)) <
        (4 / 3) ^ k * (twinPotential r z₁.im / r ^ (2 * k - 2)) * ε * (Real.exp κ - 2)) :
    ∃ z, z ≠ z₁ ∧ evenCoeff zetaZeroConfig b z ≠ 0 ∧
      ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ < r := by
  classical
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  set D := evenCoeff zetaZeroConfig b with hDdef
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set Pb := twinPotential r z₁.im with hPb
  have hσ : z₁.re / 2 ≤ z₁.re - κ / V := by
    have : κ / V ≤ z₁.re / 2 := by
      rw [div_le_iff₀ hV0]; rw [div_le_iff₀ hre₁] at hκV; linarith
    linarith
  have hσ0 : 0 < z₁.re - κ / V := by linarith
  by_contra hno
  push Not at hno
  have hlaw := zeta_powTwin_law hb hbs hk hV hm hz₁ hrec hκ hσ0 hr hr4 hVr hVk
  have hnear : ∑' z : ℂ, (if D z ≠ 0 ∧ z ≠ z₁ ∧ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ < r then
        ‖D z‖ * (1 + Real.exp ((z.re - (z₁.re - κ / V)) * V)) else 0) = 0 := by
    refine (tsum_congr fun z => ?_).trans tsum_zero
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact absurd (hno z h2 h1) (not_le.mpr h3)
  rw [hnear, mul_zero, add_zero] at hlaw
  have hσp : 2 / (z₁.re - κ / V) ^ (2 * k + 1) ≤ 2 * (2 / z₁.re) ^ (2 * k + 1) := by
    rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have := pow_le_pow_left₀ (by positivity) hσ (2 * k + 1)
    rw [div_pow, div_le_iff₀ (by positivity)] at this
    nlinarith
  have hMle : |M| * (2 / (z₁.re - κ / V) ^ (2 * k + 1) + 2 * (4 / 3) ^ k / 4 ^ (2 * k + 1)) ≤
      |M| * (2 * (2 / z₁.re) ^ (2 * k + 1) + 2 * (4 / 3) ^ k / 4 ^ (2 * k + 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg M)
  have hPb0 : 0 ≤ Pb / r ^ (2 * k - 2) := div_nonneg (twinPotential_pos hr _).le (by positivity)
  have hNQpos : 0 < Real.exp κ - 2 ∨ Real.exp κ - 2 ≤ 0 := lt_or_ge 0 _
  have h0 : 0 ≤ |M| * (2 * (2 / z₁.re) ^ (2 * k + 1) + 2 * (4 / 3) ^ k / 4 ^ (2 * k + 1)) +
      2 * (4 / 3) ^ k * W * (1 / 4 ^ (2 * k + 1) + 1 / r ^ (2 * k + 1)) := by
    have : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
    positivity
  rcases hNQpos with hpos | hneg
  · have hD : (4 / 3) ^ k * (Pb / r ^ (2 * k - 2)) * ε * (Real.exp κ - 2) ≤
        (4 / 3) ^ k * (Pb / r ^ (2 * k - 2)) * ‖D z₁‖ * (Real.exp κ - 2) := by
      gcongr
    linarith
  · have : (4 / 3) ^ k * (Pb / r ^ (2 * k - 2)) * ε * (Real.exp κ - 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith

/-! ### The twin radius -/

/-- The depth offset `κ = log(3 + e(|M| + W)/(60 L a²))`, `L = log(180(|Im z*| + 6))`. -/
def twinDepth (M W L a : ℝ) : ℝ := Real.log (3 + Real.exp 1 * (|M| + W) / (60 * L * a ^ 2))

theorem log_three_le_twinDepth {M W L a : ℝ} (hW : 0 ≤ W) (hL : 0 < L) (ha : 0 < a) :
    Real.log 3 ≤ twinDepth M W L a := by
  unfold twinDepth
  exact Real.log_le_log (by norm_num) (by
    have : 0 ≤ Real.exp 1 * (|M| + W) / (60 * L * a ^ 2) := by positivity
    linarith)

/-- `480 L/r³ ≤ twinPotential r γ ≤ 3840 L/r³` for `0 < r ≤ 1`, `L = log(180(|γ| + 6))`. -/
theorem twinPotential_bounds {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (γ : ℝ) :
    480 * Real.log (180 * (|γ| + 6)) / r ^ 3 ≤ twinPotential r γ ∧
      twinPotential r γ ≤ 3840 * Real.log (180 * (|γ| + 6)) / r ^ 3 := by
  unfold twinPotential
  have hL : Real.log 1080 ≤ Real.log (180 * (|γ| + 6)) :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg γ])
  have hL0 : 0 < Real.log 1080 := Real.log_pos (by norm_num)
  have hr3 : r ^ 3 ≤ 1 := pow_le_one₀ hr.le hr1
  have hi : 1 ≤ 1 / r ^ 3 := by rw [le_div_iff₀ (by positivity)]; linarith
  set L := Real.log (180 * (|γ| + 6))
  have hL0' : 0 < L := lt_of_lt_of_le hL0 hL
  constructor
  · have h1 : 0 ≤ 480 * Real.log 1080 * (1 / 64 + 3) := by positivity
    have h2 : 480 * L / r ^ 3 ≤ 480 * L * (1 / r ^ 3 + 3) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · have h1 : 480 * Real.log 1080 * (1 / 64 + 3) ≤ 480 * L * (4 * (1 / r ^ 3)) := by
      have h4 : 1 / 64 + 3 ≤ 4 * (1 / r ^ 3) := by linarith
      calc 480 * Real.log 1080 * (1 / 64 + 3) ≤ 480 * L * (1 / 64 + 3) := by gcongr
        _ ≤ 480 * L * (4 * (1 / r ^ 3)) := mul_le_mul_of_nonneg_left h4 (by positivity)
    have h2 : 480 * L * (1 / r ^ 3 + 3) ≤ 480 * L * (4 * (1 / r ^ 3)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc 480 * Real.log 1080 * (1 / 64 + 3) + 480 * L * (1 / r ^ 3 + 3)
        ≤ 480 * L * (4 * (1 / r ^ 3)) + 480 * L * (4 * (1 / r ^ 3)) := add_le_add h1 h2
      _ = 3840 * L / r ^ 3 := by ring

/-- `7680 (4/3)^k L ≤ 73^{2k+1}` once `log L ≤ 2k + 1`, `k ≥ 1`. -/
theorem twin_radius_numeric {k : ℕ} (hk : 1 ≤ k) {L : ℝ} (hL : 0 < L)
    (hlog : Real.log L ≤ 2 * k + 1) : 7680 * (4 / 3) ^ k * L ≤ 73 ^ (2 * k + 1) := by
  have h1 : L ≤ Real.exp 1 ^ (2 * k + 1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_log hL]
    refine Real.exp_le_exp.mpr ?_
    push_cast; linarith
  have h2 : (4 / 3 : ℝ) ^ k ≤ (4 / 3) ^ (2 * k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (7680 : ℝ) ≤ 20 ^ (2 * k + 1) :=
    le_trans (by norm_num) (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 20) (by omega : 3 ≤ 2 * k + 1))
  have he : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h4 : (20 * (4 / 3) * Real.exp 1) ^ (2 * k + 1) ≤ 73 ^ (2 * k + 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  calc 7680 * (4 / 3) ^ k * L ≤ 20 ^ (2 * k + 1) * (4 / 3) ^ (2 * k + 1) *
        Real.exp 1 ^ (2 * k + 1) := by
        gcongr
    _ = (20 * (4 / 3) * Real.exp 1) ^ (2 * k + 1) := by rw [mul_pow, mul_pow]
    _ ≤ _ := h4

/-- **The twin radius of a near-top zero.** Let `½ + z₀` be a zero right of the line at height
`γ₀ = Im z₀ > 0` with `40 log(180γ₀)(e^{w/2}B_w)²(1 + 2γ₀)^{−4} ≤ a_w²/2`, `1/V`-near the top of the
family modulated to `γ₀`, and let the modulated difference tests be Weil nonnegative on `[0, V]`.
Then the Legendre record `z*` at lag `V` has `|D(z*)| ≥ a_w²/(2e)`, and for every `k ≥ 1` with
`log log(180(|Im z*| + 6)) ≤ 2k + 1`, every `κ ≥ twinDepth M W L a_w` and
`V ≥ 73(κ + 2πk) max(1, 2/Re z*)`, another exponent lies within `73(κ + 2πk)/V` of
`(Re z* − κ/V) + i Im z*`. -/
theorem zeta_near_top_twin_radius {w V : ℝ} (hw : 0 < w) (hV : 0 < V) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re) (him₀ : 0 < z₀.im)
    (hΓ : 40 * Real.log (180 * z₀.im) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
      (1 + 2 * z₀.im) ^ 4 ≤ centerAmplitude w ^ 2 / 2)
    (htop : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → z.re ≤ z₀.re + 1 / V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧ 0 < z₁.re ∧
      centerAmplitude w ^ 2 / (2 * Real.exp 1) ≤
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ ∧
      (∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ * Real.exp (z₁.re * V)) ∧
      ∀ k : ℕ, 1 ≤ k → Real.log (Real.log (180 * (|z₁.im| + 6))) ≤ 2 * k + 1 →
        ∀ κ : ℝ, twinDepth (2 * (lagStructure zetaZeroConfig (modScaledBump w z₀.im) 0).re)
            (∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖)
            (Real.log (180 * (|z₁.im| + 6))) (centerAmplitude w) ≤ κ →
        73 * (κ + 2 * π * k) * max 1 (2 / z₁.re) ≤ V →
        ∃ z, z ≠ z₁ ∧ evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 ∧
          ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ < 73 * (κ + 2 * π * k) / V := by
  obtain ⟨z₁, hz₁, hre₁, hD₁, hrec⟩ := exists_loud_record_of_near_top hw hV hz₀ hre₀ him₀ hΓ htop
  refine ⟨z₁, hz₁, hre₁, hD₁, hrec, fun k hk hlog κ hκd hVk => ?_⟩
  set b := modScaledBump w z₀.im with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set L : ℝ := Real.log (180 * (|z₁.im| + 6)) with hL
  set a := centerAmplitude w with ha
  set R : ℝ := 73 * (κ + 2 * π * k) with hR
  set r : ℝ := R / V with hr
  set ck : ℝ := (4 / 3) ^ k with hck
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha0 : 0 < a := centerAmplitude_pos hw
  have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
  have hL0 : 0 < L := Real.log_pos (by nlinarith [abs_nonneg z₁.im])
  have hκ0 : 0 < κ := lt_of_lt_of_le (Real.log_pos (by norm_num))
    ((log_three_le_twinDepth hW0 hL0 ha0).trans hκd)
  have hR0 : 0 < R := by rw [hR]; positivity
  have hr0 : 0 < r := div_pos hR0 hV
  have hck1 : 1 ≤ ck := one_le_pow₀ (by norm_num)
  have hmax1 : 1 ≤ max 1 (2 / z₁.re) := le_max_left _ _
  have hmax2 : 2 / z₁.re ≤ max 1 (2 / z₁.re) := le_max_right _ _
  have hRV : R ≤ V := le_trans (le_mul_of_one_le_right hR0.le hmax1) hVk
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hV]; exact hRV
  have hrx : r ≤ z₁.re / 2 := by
    rw [hr, div_le_iff₀ hV]
    have := le_trans (mul_le_mul_of_nonneg_left hmax2 hR0.le) hVk
    rw [mul_div_assoc', div_le_iff₀ hre₁] at this
    linarith
  have hVr : V * r = R := by rw [hr]; field_simp
  have hπk : π * k ≤ V := by
    have h0 : 0 ≤ π * k := mul_nonneg Real.pi_pos.le (Nat.cast_nonneg k)
    have : π * k ≤ R := by rw [hR]; linarith
    linarith
  -- the order-`k` side condition
  have hVk' : 2 * ck * (κ * (κ ^ 2 + 4 * π ^ 2 * k ^ 2) ^ k) * twinPotential r z₁.im ≤
      V ^ (2 * k + 1) * r ^ (2 * k - 2) := by
    obtain ⟨-, hPu⟩ := twinPotential_bounds hr0 hr1 z₁.im
    rw [← hL] at hPu
    have hQ : (κ ^ 2 + 4 * π ^ 2 * k ^ 2) ^ k ≤ (κ + 2 * π * k) ^ (2 * k) := by
      rw [pow_mul]
      have h := mul_nonneg (mul_nonneg hκ0.le Real.pi_pos.le) (Nat.cast_nonneg (α := ℝ) k)
      exact pow_le_pow_left₀ (by positivity) (by linarith [show (κ + 2 * π * k) ^ 2 =
        κ ^ 2 + 4 * π ^ 2 * k ^ 2 + 4 * (κ * π * k) by ring]) k
    have hnum := twin_radius_numeric hk hL0 hlog
    have hVr' : V ^ (2 * k + 1) * r ^ (2 * k - 2) = R ^ (2 * k + 1) / r ^ 3 := by
      rw [← hVr, mul_pow, eq_div_iff (by positivity), mul_assoc, ← pow_add,
        show 2 * k - 2 + 3 = 2 * k + 1 by omega]
    rw [hVr']
    have hκR : κ ≤ κ + 2 * π * k := by
      have := mul_nonneg Real.pi_pos.le (Nat.cast_nonneg (α := ℝ) k); linarith
    have hP0 := (twinPotential_pos hr0 z₁.im).le
    calc 2 * ck * (κ * (κ ^ 2 + 4 * π ^ 2 * k ^ 2) ^ k) * twinPotential r z₁.im
        ≤ 2 * ck * ((κ + 2 * π * k) * (κ + 2 * π * k) ^ (2 * k)) * (3840 * L / r ^ 3) := by
          gcongr
      _ = 7680 * ck * L * (κ + 2 * π * k) ^ (2 * k + 1) / r ^ 3 := by ring
      _ ≤ 73 ^ (2 * k + 1) * (κ + 2 * π * k) ^ (2 * k + 1) / r ^ 3 := by gcongr
      _ = R ^ (2 * k + 1) / r ^ 3 := by rw [hR, mul_pow]
  -- non-quietness
  have hNQ : |M| * (2 * (2 / z₁.re) ^ (2 * k + 1) + 2 * ck / 4 ^ (2 * k + 1)) +
      2 * ck * W * (1 / 4 ^ (2 * k + 1) + 1 / r ^ (2 * k + 1)) <
      ck * (twinPotential r z₁.im / r ^ (2 * k - 2)) * (a ^ 2 / (2 * Real.exp 1)) *
        (Real.exp κ - 2) := by
    obtain ⟨hPl, -⟩ := twinPotential_bounds hr0 hr1 z₁.im
    rw [← hL] at hPl
    set t : ℝ := 1 / r ^ (2 * k + 1) with ht
    have ht0 : 0 < t := by rw [ht]; positivity
    have h2x : (2 / z₁.re) ^ (2 * k + 1) ≤ t := by
      rw [ht, one_div, ← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [div_le_iff₀ hre₁, inv_mul_eq_div, le_div_iff₀ hr0]; linarith
    have h4 : 1 / (4 : ℝ) ^ (2 * k + 1) ≤ t :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hr0.le (by linarith) _)
    have hlhs : |M| * (2 * (2 / z₁.re) ^ (2 * k + 1) + 2 * ck / 4 ^ (2 * k + 1)) +
        2 * ck * W * (1 / 4 ^ (2 * k + 1) + 1 / r ^ (2 * k + 1)) ≤ 4 * ck * (|M| + W) * t := by
      have e1 : 2 * ck / (4 : ℝ) ^ (2 * k + 1) = 2 * ck * (1 / 4 ^ (2 * k + 1)) := by ring
      rw [e1]
      have hM1 : |M| * (2 * (2 / z₁.re) ^ (2 * k + 1) + 2 * ck * (1 / 4 ^ (2 * k + 1))) ≤
          |M| * (4 * ck * t) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg M)
        have h1 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 2 * ck by positivity)
        have h2 : 1 * t ≤ ck * t := mul_le_mul_of_nonneg_right hck1 ht0.le
        linarith
      have hW1 : 2 * ck * W * (1 / 4 ^ (2 * k + 1) + 1 / r ^ (2 * k + 1)) ≤ 2 * ck * W * (2 * t) := by
        refine mul_le_mul_of_nonneg_left (by rw [← ht]; linarith) (by positivity)
      linarith
    have hexp : 1 + Real.exp 1 * (|M| + W) / (60 * L * a ^ 2) ≤ Real.exp κ - 2 := by
      have h := Real.exp_le_exp.mpr hκd
      rw [twinDepth, Real.exp_log (by positivity)] at h
      linarith
    have hPr : 480 * L * t ≤ twinPotential r z₁.im / r ^ (2 * k - 2) := by
      rw [le_div_iff₀ (by positivity), ht]
      calc 480 * L * (1 / r ^ (2 * k + 1)) * r ^ (2 * k - 2) = 480 * L / r ^ 3 := by
            rw [show 2 * k + 1 = 3 + (2 * k - 2) by omega, pow_add]
            field_simp
        _ ≤ _ := hPl
    have hE := Real.exp_pos 1
    have hrhs : 4 * ck * (|M| + W) * t + ck * (240 * L * a ^ 2 / Real.exp 1) * t ≤
        ck * (twinPotential r z₁.im / r ^ (2 * k - 2)) * (a ^ 2 / (2 * Real.exp 1)) *
          (Real.exp κ - 2) := by
      have hX : 0 ≤ a ^ 2 / (2 * Real.exp 1) * (1 + Real.exp 1 * (|M| + W) / (60 * L * a ^ 2)) := by
        positivity
      calc 4 * ck * (|M| + W) * t + ck * (240 * L * a ^ 2 / Real.exp 1) * t
          = ck * (480 * L * t) * (a ^ 2 / (2 * Real.exp 1) *
              (1 + Real.exp 1 * (|M| + W) / (60 * L * a ^ 2))) := by
            field_simp; ring
        _ ≤ ck * (twinPotential r z₁.im / r ^ (2 * k - 2)) * (a ^ 2 / (2 * Real.exp 1) *
              (1 + Real.exp 1 * (|M| + W) / (60 * L * a ^ 2))) := by gcongr
        _ ≤ ck * (twinPotential r z₁.im / r ^ (2 * k - 2)) * (a ^ 2 / (2 * Real.exp 1) *
              (Real.exp κ - 2)) := by
            have hP0 := (twinPotential_pos hr0 z₁.im).le
            gcongr
        _ = _ := by ring
    have hpos : 0 < ck * (240 * L * a ^ 2 / Real.exp 1) * t := by positivity
    linarith
  have hπk0 : 0 ≤ π * k := mul_nonneg Real.pi_pos.le (Nat.cast_nonneg k)
  have h4πk : 4 * π * k ≤ V * r := by rw [hVr, hR]; linarith
  have hκV : 2 * κ / z₁.re ≤ V := by
    have h1 := le_trans (mul_le_mul_of_nonneg_left hmax2 hR0.le) hVk
    rw [mul_div_assoc', div_le_iff₀ hre₁] at h1
    rw [div_le_iff₀ hre₁]
    have : 2 * κ ≤ R * 2 := by rw [hR]; linarith
    linarith
  exact zeta_powTwin_of_record (contDiff_modScaledBump_two w _) (modScaledBump_support hw _) hk
    hπk hm hz₁ hre₁ hrec (by positivity) hD₁ hκ0 hr0 (by linarith) h4πk hκV hVk' hNQ

/-- **The twin radius is `O((κ + log log γ*)/V)`.** Under the hypotheses of
`zeta_near_top_twin_radius`, with `ℓ = log log(180(|Im z*| + 6))`, `κ ≥ twinDepth M W L a_w` and
`V ≥ 73(κ + πℓ + 4π) max(1, 2/Re z*)`, another exponent lies within `73(κ + πℓ + 4π)/V` of
`(Re z* − κ/V) + i Im z*`: take `k = ⌈ℓ/2⌉ + 1`. -/
theorem zeta_near_top_twin_radius_log_log {w V : ℝ} (hw : 0 < w) (hV : 0 < V) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re) (him₀ : 0 < z₀.im)
    (hΓ : 40 * Real.log (180 * z₀.im) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
      (1 + 2 * z₀.im) ^ 4 ≤ centerAmplitude w ^ 2 / 2)
    (htop : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → z.re ≤ z₀.re + 1 / V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧ 0 < z₁.re ∧
      centerAmplitude w ^ 2 / (2 * Real.exp 1) ≤
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ ∧
      (∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ * Real.exp (z₁.re * V)) ∧
      ∀ κ : ℝ, twinDepth (2 * (lagStructure zetaZeroConfig (modScaledBump w z₀.im) 0).re)
          (∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖)
          (Real.log (180 * (|z₁.im| + 6))) (centerAmplitude w) ≤ κ →
        73 * (κ + π * Real.log (Real.log (180 * (|z₁.im| + 6))) + 4 * π) * max 1 (2 / z₁.re) ≤ V →
        ∃ z, z ≠ z₁ ∧ evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 ∧
          ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ <
            73 * (κ + π * Real.log (Real.log (180 * (|z₁.im| + 6))) + 4 * π) / V := by
  obtain ⟨z₁, hz₁, hre₁, hD₁, hrec, hk⟩ :=
    zeta_near_top_twin_radius hw hV hz₀ hre₀ him₀ hΓ htop hm
  refine ⟨z₁, hz₁, hre₁, hD₁, hrec, fun κ hκd hVk => ?_⟩
  set ℓ := Real.log (Real.log (180 * (|z₁.im| + 6))) with hℓ
  have hL1 : 1 ≤ Real.log (180 * (|z₁.im| + 6)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    nlinarith [abs_nonneg z₁.im]
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg hL1
  set k : ℕ := ⌈ℓ / 2⌉₊ + 1 with hkdef
  have hceil1 : ℓ / 2 ≤ ⌈ℓ / 2⌉₊ := Nat.le_ceil _
  have hceil2 : (⌈ℓ / 2⌉₊ : ℝ) < ℓ / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hkr : (k : ℝ) = ⌈ℓ / 2⌉₊ + 1 := by rw [hkdef]; push_cast; ring
  have h2πk : 2 * π * k ≤ π * ℓ + 4 * π := by
    rw [hkr]; nlinarith [Real.pi_pos]
  have hmax0 : 0 < max 1 (2 / z₁.re) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hV' : 73 * (κ + 2 * π * k) * max 1 (2 / z₁.re) ≤ V :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) hmax0.le) hVk
  obtain ⟨z, hz, hDz, hdist⟩ := hk k (by omega) (by rw [hkr]; linarith) κ hκd hV'
  refine ⟨z, hz, hDz, lt_of_lt_of_le hdist ?_⟩
  exact div_le_div_of_nonneg_right (by linarith) hV.le

end GaloisForLFunctions.SquareRootThreshold
