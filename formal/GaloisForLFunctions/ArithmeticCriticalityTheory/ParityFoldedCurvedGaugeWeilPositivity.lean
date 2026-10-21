import GaloisForLFunctions.ArithmeticCriticalityTheory.EvenGaugeFoldedConductance
import GaloisForLFunctions.ArithmeticCriticalityTheory.QuadraticGaugeWindowWeilPositivity
import GaloisForLFunctions.RHTower.WeilMarkovPrimitiveHyperplane

/-!
# Weil positivity on `[−6/25, 6/25]` from the parity fold

The full zero form splits orthogonally into reflection parities:
`Ẑ(F) = Ẑ(F_e) + Ẑ(F_o)` and `∫ F² = ∫ F_e² + ∫ F_o²` (`fullZeroForm_eq_even_add_odd`,
`integral_sq_eq_even_add_odd`).

**Even tests.** In a curved even gauge `M` the jump part of `Ẑ(M u)` has the density
`κ(t) = ω(t) − 2cosh(t/2)` (`weilJumpDensity`), negative past the plastic threshold `log ρ ≈ 0.2812`.
On even profiles it folds to the conductance `κ(s) + κ(s + 2x)` on the pairs `x + s < R`
(`integral_kappa_mul_gaugeJumpProfile_nonneg_of_fold`), and for `R ≤ 27/100` the folded conductance is
nonnegative (`weilJumpDensity_fold_nonneg`): below the plastic threshold both terms are, and above it
the short lag carries `ω(s) ≥ 1/(2s)`, which beats the linear deficit `2cosh − ω ≤ 6.5 (t − 0.275)`. The negative density therefore costs nothing on even tests. The gauge
`q P` with `q(y) = 1 − 13 y²`, radius `241/1000` and collar `1/1000` has potential

    −𝒲M(x) + 2 ∫ M(y) cosh((x − y)/2) dy ≥ q(x) (D − ½ log(1 − x²/R²)) + 1.126868 − 21.20808 x² − 0.40625 x⁴,

`D = −log(2R) − R/2 − (γ + log π)`, and a one-dimensional inequality with the anchors
`1 − x²/R² = (3/4)^k`, `k ≤ 8` (`evenCurvedGauge_window_inequality`) bounds it below by `1/250` on
`[−6/25, 6/25]`.

**Odd tests.** The folded odd plateau gives `Ẑ(F_o) ≥ (1/40) ∫ F_o²` on `[−7/25, 7/25]`
(`fullZeroForm_ge_of_odd_support_le`).

**Theorem** (`fullZeroForm_ge_of_support_le_parityFolded`). Every real `F ∈ C²_c` vanishing outside
`[−6/25, 6/25]` satisfies `Ẑ(F) ≥ (1/250) ∫ F²`; hence `μ(A) ≥ 1/250` for every aperture `A ≤ 6/25`
(`one_div_250_le_ccmRestrictedWeilGroundEnergy`). The reach is `2.29` times the Markov window
`21/200`, past the reach `39/200` of the curved gauge that pays for the negative density.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar GaloisForLFunctions.ArithmeticIncidencePositivity
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The parity split -/

/-- **The parity split of the full zero form**: `Ẑ(F) = Ẑ(F_e) + Ẑ(F_o)`. -/
theorem fullZeroForm_eq_even_add_odd {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) :
    fullZeroForm F = fullZeroForm (evenPartReal F) + fullZeroForm (oddPartReal F) := by
  have hm := markovEnergy_ofReal_eq_even_add_odd hF hFc
  have hFe := (contDiff_evenPartReal hF).continuous
  have hFo := (contDiff_oddPartReal hF).continuous
  have hFec := hasCompactSupport_evenPartReal hFc
  have hFoc := hasCompactSupport_oddPartReal hFc
  have hsum : F = fun x => evenPartReal F x + oddPartReal F x :=
    funext fun x => (evenPartReal_add_oddPartReal F x).symm
  have hS : oddPoleMoment F = oddPoleMoment (oddPartReal F) := by
    conv_lhs => rw [hsum]
    rw [oddPoleMoment_add hFe hFec hFo hFoc, oddPoleMoment_eq_zero_of_even (evenPartReal_neg F),
      zero_add]
  have hC : evenPoleMoment F = evenPoleMoment (evenPartReal F) := by
    conv_lhs => rw [hsum]
    rw [evenPoleMoment_add hFe hFec hFo hFoc, evenPoleMoment_eq_zero_of_odd (oddPartReal_neg F),
      add_zero]
  unfold fullZeroForm
  rw [hm, hS, hC, oddPoleMoment_eq_zero_of_even (evenPartReal_neg F),
    evenPoleMoment_eq_zero_of_odd (oddPartReal_neg F)]
  ring

/-- The parts are orthogonal: `∫ F² = ∫ F_e² + ∫ F_o²`. -/
theorem integral_sq_eq_even_add_odd {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    (∫ x, F x ^ 2) = (∫ x, evenPartReal F x ^ 2) + ∫ x, oddPartReal F x ^ 2 := by
  have hFe : Continuous (evenPartReal F) := by unfold evenPartReal; fun_prop
  have hFo : Continuous (oddPartReal F) := by unfold oddPartReal; fun_prop
  have hFec := hasCompactSupport_evenPartReal hFc
  have hFoc := hasCompactSupport_oddPartReal hFc
  have ie : Integrable fun x => evenPartReal F x ^ 2 :=
    (hFe.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFec)
  have io : Integrable fun x => oddPartReal F x ^ 2 :=
    (hFo.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFoc)
  have ieo : Integrable fun x => evenPartReal F x * oddPartReal F x :=
    (hFe.mul hFo).integrable_of_hasCompactSupport hFec.mul_right
  have hcross : (∫ x, evenPartReal F x * oddPartReal F x) = 0 := by
    have h := integral_neg_eq_self (fun x => evenPartReal F x * oddPartReal F x) volume
    simp only [evenPartReal_neg, oddPartReal_neg, mul_neg, integral_neg] at h
    linarith
  have hpt : ∀ x, F x ^ 2 = (evenPartReal F x ^ 2 + oddPartReal F x ^ 2) +
      2 * (evenPartReal F x * oddPartReal F x) := fun x => by
    rw [← evenPartReal_add_oddPartReal F x]; ring
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (f := fun x => evenPartReal F x ^ 2 + oddPartReal F x ^ 2)
      (g := fun x => 2 * (evenPartReal F x * oddPartReal F x)) (ie.add io) (ieo.const_mul 2),
    integral_add ie io, integral_const_mul, hcross]
  ring

/-! ### The folded Weil jump density -/

/-- The Weil jump density `ω(t) − 2cosh(t/2)`: the archimedean jump density minus the pole. -/
def weilJumpDensity (t : ℝ) : ℝ := archLevyDensity t - 2 * Real.cosh (t / 2)

theorem measurable_weilJumpDensity : Measurable weilJumpDensity :=
  measurable_archLevyDensity.sub
    (continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).measurable

theorem two_mul_cosh_half_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    2 * Real.cosh (t / 2) ≤ 2.26 := by
  have hc : Real.cosh (t / 2) ≤ Real.cosh (1 / 2) :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg (by linarith), abs_of_pos (by norm_num)]; linarith)
  have hp := exp_le_taylor_five (x := 1 / 2) (by norm_num [abs_of_pos])
  have hm := exp_le_taylor_five (x := -(1 / 2)) (by norm_num [abs_of_pos])
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hp
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hm
  norm_num at hp hm
  have : 2 * Real.cosh (1 / 2) ≤ 2.26 := by
    rw [Real.cosh_eq]
    norm_num
    linarith
  linarith

/-- `|ω(t) − 2cosh(t/2)| ≤ 4/t` on `(0, 1]`. -/
theorem abs_weilJumpDensity_le {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    |weilJumpDensity t| ≤ 4 / t := by
  have hω := archLevyDensity_le_of_le_one h0 h1
  have hω0 := (archLevyDensity_pos h0).le
  have hc := two_mul_cosh_half_le h0.le h1
  have hc0 : 0 ≤ 2 * Real.cosh (t / 2) := by positivity
  have ht : 2.26 ≤ 4 / t := by rw [le_div_iff₀ h0]; linarith
  have h32 : 3 / 2 / t ≤ 4 / t := by gcongr; norm_num
  unfold weilJumpDensity
  rw [abs_le]
  constructor <;> linarith

/-- **The folded Weil conductance is nonnegative** on every pair `x + s < 27/100`. Below the
plastic threshold both terms are; above it the short lag `s < 0.26` carries `s ω(s) ≥ ½ + s/4 − s²/16`,
which beats the linear deficit `2cosh − ω ≤ 6.5(t − 0.275)` of the long lag `t = s + 2x < 0.54 − s`. -/
theorem weilJumpDensity_fold_nonneg {s x : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hxs : x + s < 27 / 100) : 0 ≤ weilJumpDensity s + weilJumpDensity (s + 2 * x) := by
  by_cases h : s + 2 * x ≤ 0.28
  · have h1 := two_mul_cosh_le_archLevyDensity_of_le_plastic hs (by linarith)
    have h2 := two_mul_cosh_le_archLevyDensity_of_le_plastic (by linarith : 0 < s + 2 * x) h
    unfold weilJumpDensity
    linarith
  · replace h : 0.28 < s + 2 * x := not_le.mp h
    have hlin := two_mul_cosh_sub_archLevyDensity_le_linear (t := s + 2 * x) (by linarith)
      (by linarith)
    have hω := mul_archLevyDensity_ge hs (by linarith)
    have hc : Real.cosh (s / 2) ≤ 1.0085 := by
      have hc' : Real.cosh (s / 2) ≤ Real.cosh 0.13 :=
        Real.cosh_le_cosh.mpr (by
          rw [abs_of_pos (by linarith), abs_of_pos (by norm_num)]; linarith)
      have hp := exp_le_taylor_five (x := 0.13) (by norm_num [abs_of_pos])
      have hm := exp_le_taylor_five (x := -0.13) (by norm_num [abs_of_pos])
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.13)] at hp
      rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 0.13)] at hm
      norm_num at hp hm
      have : 2 * Real.cosh 0.13 ≤ 2.017 := by
        rw [Real.cosh_eq]
        norm_num
        linarith
      linarith
    have e1 := mul_le_mul_of_nonneg_left hc hs.le
    have e2 := mul_le_mul_of_nonneg_left hlin hs.le
    have e3 : s * (s + 2 * x - 0.275) ≤ s * (0.265 - s) :=
      mul_le_mul_of_nonneg_left (by linarith) hs.le
    have key : 0 ≤ s * (weilJumpDensity s + weilJumpDensity (s + 2 * x)) := by
      unfold weilJumpDensity
      nlinarith [e1, e2, e3, hω, sq_nonneg (s - 0.271)]
    exact (mul_nonneg_iff_of_pos_left hs).mp key

/-! ### The even window inequality -/

/-- **The even window inequality.** For `0 ≤ y ≤ 6/25` and `D ≥ −1.1134689`:
`1/250 ≤ (1 − 13y²)(D − ½ log(1 − (1000/241)² y²)) + 1.126868 − 21.20808 y² − 0.40625 y⁴`. On each
piece the logarithm is replaced by its tangent at an anchor `(3/4)^k` and the remainder is a concave
quadratic in `y²`. -/
theorem evenCurvedGauge_window_inequality {y D : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 6 / 25)
    (hD : -1.1134689 ≤ D) :
    1 / 250 ≤ (1 - 13 * y ^ 2) * (D + -(1 / 2) * Real.log (1 - 1000000 / 58081 * y ^ 2)) +
      1.126868 - 21.20808 * y ^ 2 - 0.40625 * y ^ 4 := by
  have hy2 : y ^ 2 ≤ (6 / 25) ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have hq : 0 ≤ 1 - 13 * y ^ 2 := by nlinarith
  have hs : 1000000 / 58081 * y ^ 2 < 1 := by nlinarith
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have anc := fun k : ℕ => mul_le_mul_of_nonneg_left
    (neg_half_log_one_sub_ge_anchor_pow (s := 1000000 / 58081 * y ^ 2) hs k) hq
  set ℓ := -(1 / 2) * Real.log (1 - 1000000 / 58081 * y ^ 2) with hℓ
  have piece : ∀ (lo hi : ℝ), lo ≤ y → y ≤ hi → 0 ≤ lo →
      (lo ^ 2 ≤ y ^ 2 ∧ y ^ 2 ≤ hi ^ 2 ∧ 0 ≤ (y ^ 2 - lo ^ 2) * (hi ^ 2 - y ^ 2)) := by
    intro lo hi hl hh h0
    have h1 : lo ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ h0 hl 2
    have h2 : y ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ (h0.trans hl) hh 2
    exact ⟨h1, h2, mul_nonneg (by linarith) (by linarith)⟩
  rcases le_or_gt y 0.135 with h1 | h1
  · obtain ⟨p1, p2, p3⟩ := piece 0 0.135 hy0 h1 le_rfl
    have h := anc 0; norm_num at h; linarith
  rcases le_or_gt y 0.172 with h2 | h2
  · obtain ⟨p1, p2, p3⟩ := piece 0.135 0.172 h1.le h2 (by norm_num)
    have h := anc 1; norm_num at h; linarith
  rcases le_or_gt y 0.191 with h3 | h3
  · obtain ⟨p1, p2, p3⟩ := piece 0.172 0.191 h2.le h3 (by norm_num)
    have h := anc 2; norm_num at h; linarith
  rcases le_or_gt y 0.203 with h4 | h4
  · obtain ⟨p1, p2, p3⟩ := piece 0.191 0.203 h3.le h4 (by norm_num)
    have h := anc 3; norm_num at h; linarith
  rcases le_or_gt y 0.212 with h5 | h5
  · obtain ⟨p1, p2, p3⟩ := piece 0.203 0.212 h4.le h5 (by norm_num)
    have h := anc 4; norm_num at h; linarith
  rcases le_or_gt y 0.22 with h6 | h6
  · obtain ⟨p1, p2, p3⟩ := piece 0.212 0.22 h5.le h6 (by norm_num)
    have h := anc 5; norm_num at h; linarith
  rcases le_or_gt y 0.228 with h7 | h7
  · obtain ⟨p1, p2, p3⟩ := piece 0.22 0.228 h6.le h7 (by norm_num)
    have h := anc 6; norm_num at h; linarith
  rcases le_or_gt y 0.236 with h8 | h8
  · obtain ⟨p1, p2, p3⟩ := piece 0.228 0.236 h7.le h8 (by norm_num)
    have h := anc 7; norm_num at h; linarith
  · obtain ⟨p1, p2, p3⟩ := piece 0.236 (6 / 25) h8.le hy (by norm_num)
    have h := anc 8; norm_num at h; linarith

/-- The archimedean constant of the radius `241/1000`: `−log(241/500) − 241/2000 − (γ + log π)`. -/
theorem evenGauge_constant_ge :
    -1.1134689 ≤ -Real.log (2 * (241 / 1000)) - 241 / 1000 / 2 - 2 * archConstantReal := by
  have hsplit : Real.log (2 * (241 / 1000)) = Real.log (241 / 250) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 241 / 250 by norm_num)
  have h2 := Real.log_two_gt_d9
  have hC := two_mul_archConstantReal_lt_sharp
  norm_num at hl
  linarith

/-! ### Even-sector positivity on `[−6/25, 6/25]` -/

/-- **Weil positivity of every even test supported in `[−6/25, 6/25]`.** Every even `F ∈ C²_c`
vanishing outside `[−6/25, 6/25]` satisfies `Ẑ(F) ≥ (1/250) ∫ F²`. -/
theorem fullZeroForm_ge_of_even_support_le_folded {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (heven : ∀ x, F (-x) = F x)
    (hsupp : ∀ x, 6 / 25 < |x| → F x = 0) :
    1 / 250 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set M := curvedWindowGauge 13 (241 / 1000) (1 / 1000) with hMdef
  set u : ℝ → ℝ := fun x => F x * (curvedProfile 13 x)⁻¹ with hudef
  have hc : (0 : ℝ) ≤ 13 := by norm_num
  have hcR : (13 : ℝ) * (241 / 1000) ^ 2 ≤ 1 := by norm_num
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hMd : ContDiff ℝ 2 M := contDiff_curvedWindowGauge _ _ _
  have hMcs : HasCompactSupport M := hasCompactSupport_curvedWindowGauge _ _ hδ
  have hnn : ∀ y, 0 ≤ M y := curvedWindowGauge_nonneg hc hcR hδ
  have hle : ∀ y, M y ≤ 1 := curvedWindowGauge_le_one hc hcR hδ
  have hzero : ∀ y, 241 / 1000 ≤ |y| → M y = 0 := fun y hy => curvedWindowGauge_eq_zero 13 hδ hy
  have hMB : ∀ x, M x ≠ 0 → |x| ≤ 241 / 1000 := fun x hx => by
    by_contra h
    exact hx (hzero x (not_le.mp h).le)
  have hMe : ∀ y, M (-y) = M y := curvedWindowGauge_neg 13 _ _
  have hlog2 : 2 * (241 / 1000 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num; linarith
  have hqpos : ∀ y, |y| ≤ 241 / 1000 → 0 < curvedProfile 13 y := fun y hy => by
    have := curvedProfile_ge_of_le hc hy
    norm_num at this
    linarith
  -- the profile
  have hu : ContDiff ℝ 2 u := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : |y| < 241 / 1000
    · exact hF.contDiffAt.mul ((contDiff_curvedProfile 13).contDiffAt.inv
        (hqpos y hy.le).ne' |>.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl))
    · have hopen : IsOpen {z : ℝ | 6 / 25 < |z|} := isOpen_lt continuous_const continuous_abs
      have hev : u =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds (show 6 / 25 < |y| by linarith [not_lt.mp hy])] with z hz
        simp [hudef, hsupp z hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have huc : HasCompactSupport u := hFc.mul_right
  have hue : ∀ x, u (-x) = u x := fun x => by
    simp only [hudef]
    rw [heven, curvedProfile_neg]
  have hFu : (fun x => M x * u x) = F := funext fun x => by
    by_cases hx : |x| ≤ 6 / 25
    · have hq := (hqpos x (by linarith)).ne'
      simp only [hudef, hMdef]
      rw [curvedWindowGauge_eq 13 hδ (by linarith : |x| ≤ 241 / 1000 - 1 / 1000)]
      field_simp
    · simp only [hudef, hsupp x (not_le.mp hx), zero_mul, mul_zero]
  -- the representation
  have hrep := fullZeroForm_mul_eq_gauge_window hu huc hMd hMcs hle hnn hzero hlog2
  rw [hFu] at hrep
  -- the jump part is a folded nonnegative energy
  obtain ⟨Ku, -, hKu⟩ := exists_lipschitz_bound_of_compactSupport (hu.of_le (by norm_num)) huc
  have huL : ∀ a b, |u a - u b| ≤ Ku * |a - b| := fun a b => hKu b a
  have hωI := integrableOn_archLevy_mul_gaugeJumpProfile hle hnn hzero (by norm_num) (by norm_num)
    hu.continuous hMd.continuous hMcs huL
  have hcI : Integrable fun t => Real.cosh (t / 2) * gaugeJumpProfile M u t :=
    (integrable_gaugeJump_kernel hu.continuous hMd.continuous hMB).integral_prod_left.congr
      (Eventually.of_forall fun t => by
        simp only [gaugeJumpProfile]
        rw [integral_const_mul])
  have hfoldI : 0 ≤ ∫ t in Ioi (0 : ℝ), weilJumpDensity t * gaugeJumpProfile M u t :=
    integral_kappa_mul_gaugeJumpProfile_nonneg_of_fold hMd.continuous hu.continuous hMe hue hnn
      hle hzero huL (by norm_num) measurable_weilJumpDensity (C := 4) (by norm_num)
      (fun t ht0 ht1 => abs_weilJumpDensity_le ht0 (by linarith))
      (fun s x hs hx hxs => weilJumpDensity_fold_nonneg hs hx (by linarith))
  have hjump : 0 ≤ (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M u t) -
      2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M u t := by
    have e : (∫ t in Ioi (0 : ℝ), weilJumpDensity t * gaugeJumpProfile M u t) =
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M u t) -
          2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M u t := by
      rw [← integral_const_mul, ← integral_sub hωI (hcI.integrableOn.const_mul 2)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      unfold weilJumpDensity
      ring
    rw [← e]
    exact hfoldI
  -- the potential integrands
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hMd.of_le (by norm_num)) hMcs
  have hML : ∀ a b, |M a - M b| ≤ KM * |a - b| := fun a b => hKM b a
  have hdec8 : ∀ y, |M y| ≤ Real.exp (8 * (241 / 1000)) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < 241 / 1000
    · rw [abs_of_nonneg (hnn y), ← Real.exp_add]
      exact (hle y).trans (Real.one_le_exp (by nlinarith))
    · rw [hzero y (not_lt.mp hy), abs_zero]
      positivity
  have hW : Continuous fun x => -poleFreeWeilOperator M x :=
    (continuous_poleFreeWeilOperator hMd.continuous hML hdec8).neg
  have hG : Continuous fun x => ∫ y, M y * Real.cosh ((x - y) / 2) := by
    have e := funext (integral_gauge_cosh_eq hMd.continuous hMcs)
    rw [e]
    fun_prop
  have hu2M : Continuous fun x => u x ^ 2 * M x := (hu.continuous.pow 2).mul hMd.continuous
  have hu2Mc : HasCompactSupport fun x => u x ^ 2 * M x := (hasCompactSupport_sq huc).mul_right
  have i1 : Integrable fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x :=
    (hu2M.mul hW).integrable_of_hasCompactSupport hu2Mc.mul_right
  have i2 : Integrable fun x => u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2) :=
    (hu2M.mul hG).integrable_of_hasCompactSupport hu2Mc.mul_right
  -- the pointwise potential
  have hD := evenGauge_constant_ge
  have hpt : ∀ x, 1 / 250 * F x ^ 2 ≤ u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * ∫ y, M y * Real.cosh ((x - y) / 2)) := by
    intro x
    by_cases hx : |x| ≤ 6 / 25
    · have hxR : |x| ≤ 241 / 1000 - 1 / 1000 := by linarith
      have hMx : M x = curvedProfile 13 x := curvedWindowGauge_eq 13 hδ hxR
      have hFx : F x = M x * u x := (congrFun hFu x).symm
      have hq0 : 0 ≤ curvedProfile 13 x := (hqpos x (by linarith)).le
      have hWx : curvedProfile 13 x *
            ((-(1 / 2) * Real.log (1 - Real.exp (-2 * (241 / 1000 - x))) -
                3 / 4 * (241 / 1000 - x) + (241 / 1000 - x) ^ 2 / 12) +
              (-(1 / 2) * Real.log (1 - Real.exp (-2 * (241 / 1000 + x))) -
                3 / 4 * (241 / 1000 + x) + (241 / 1000 + x) ^ 2 / 12) - 2 * archConstantReal) +
          13 * (sqMomentFloor (241 / 1000 - x) + sqMomentFloor (241 / 1000 + x) -
            2 * (1 + 241 / 1000 / 2) * x ^ 2) ≤ -poleFreeWeilOperator M x :=
        neg_poleFreeWeilOperator_curvedWindowGauge_ge hc hcR hδ (by norm_num) hxR
      have hbr := curvedGauge_bracket_ge (R := 241 / 1000) (x := x) (by norm_num) (by norm_num)
        (by linarith)
      have hk : x ^ 2 / (241 / 1000) ^ 2 = 1000000 / 58081 * x ^ 2 := by ring
      rw [hk] at hbr
      have hGx : 2 * (241 / 1000 - 1 / 1000) - 2 / 3 * 13 * (241 / 1000 - 1 / 1000) ^ 3 ≤
          ∫ y, M y * Real.cosh ((x - y) / 2) :=
        integral_curvedWindowGauge_cosh_ge hc hcR hδ (by norm_num) x
      have hreg : 1.126868 - 21.20808 * x ^ 2 - 0.40625 * x ^ 4 ≤
          13 * (sqMomentFloor (241 / 1000 - x) + sqMomentFloor (241 / 1000 + x) -
            2 * (1 + 241 / 1000 / 2) * x ^ 2) +
          2 * (2 * (241 / 1000 - 1 / 1000) - 2 / 3 * 13 * (241 / 1000 - 1 / 1000) ^ 3) := by
        unfold sqMomentFloor
        nlinarith [sq_nonneg x]
      have h1D := evenCurvedGauge_window_inequality (abs_nonneg x) hx hD
      have h4 : |x| ^ 4 = x ^ 4 := by
        rw [show |x| ^ 4 = (|x| ^ 2) ^ 2 by ring, sq_abs]; ring
      rw [h4, sq_abs] at h1D
      have hpot : 1 / 250 ≤ -poleFreeWeilOperator M x + 2 * ∫ y, M y * Real.cosh ((x - y) / 2) := by
        have hqbr := mul_le_mul_of_nonneg_left hbr hq0
        unfold curvedProfile at hqbr hWx
        linarith [hqbr, hWx, hGx, hreg, h1D]
      rw [hFx]
      have hu2 : 0 ≤ u x ^ 2 * M x := mul_nonneg (sq_nonneg _) (hnn x)
      have hM1 := hle x
      nlinarith [mul_le_mul_of_nonneg_left hpot hu2, mul_nonneg hu2 (by linarith : 0 ≤ 1 - M x)]
    · have hF0 : F x = 0 := hsupp x (not_le.mp hx)
      have hu0 : u x = 0 := by simp [hudef, hF0]
      rw [hF0, hu0]
      simp
  -- assemble
  have hF2 : Integrable fun x => 1 / 250 * F x ^ 2 :=
    ((hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)).const_mul _
  have e : ∀ x, u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * ∫ y, M y * Real.cosh ((x - y) / 2)) =
      u x ^ 2 * M x * -poleFreeWeilOperator M x +
        2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2)) := fun x => by ring
  have hsum : Integrable fun x => u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * ∫ y, M y * Real.cosh ((x - y) / 2)) :=
    (i1.add (i2.const_mul 2)).congr (Eventually.of_forall fun x => (e x).symm)
  have hint := integral_mono hF2 hsum hpt
  have hsplit : (∫ x, u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * ∫ y, M y * Real.cosh ((x - y) / 2))) =
      (∫ x, u x ^ 2 * M x * -poleFreeWeilOperator M x) +
        2 * ∫ x, u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2) := by
    rw [integral_congr_ae (Eventually.of_forall e),
      integral_add (f := fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x)
        (g := fun x => 2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2))) i1
        (i2.const_mul 2), integral_const_mul]
  rw [integral_const_mul] at hint
  rw [hrep]
  linarith [hjump, hint, hsplit]

/-! ### All profiles on `[−6/25, 6/25]` -/

/-- **Weil positivity on `[−6/25, 6/25]` from the parity fold.** Every real `F ∈ C²_c` vanishing
outside `[−6/25, 6/25]` satisfies `Ẑ(F) ≥ (1/250) ∫ F²`. -/
theorem fullZeroForm_ge_of_support_le_parityFolded {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hsupp : ∀ x, 6 / 25 < |x| → F x = 0) :
    1 / 250 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  have hse : ∀ x, 6 / 25 < |x| → evenPartReal F x = 0 := fun x hx => by
    unfold evenPartReal
    rw [hsupp x hx, hsupp (-x) (by rwa [abs_neg])]
    norm_num
  have hso : ∀ x, 7 / 25 < |x| → oddPartReal F x = 0 := fun x hx => by
    unfold oddPartReal
    rw [hsupp x (by linarith), hsupp (-x) (by rw [abs_neg]; linarith)]
    norm_num
  have he := fullZeroForm_ge_of_even_support_le_folded (contDiff_evenPartReal hF)
    (hasCompactSupport_evenPartReal hFc) (evenPartReal_neg F) hse
  have ho := fullZeroForm_ge_of_odd_support_le (contDiff_oddPartReal hF)
    (hasCompactSupport_oddPartReal hFc) (oddPartReal_neg F) hso
  have hnn : 0 ≤ ∫ x, oddPartReal F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [fullZeroForm_eq_even_add_odd hF hFc, integral_sq_eq_even_add_odd hF.continuous hFc]
  linarith

/-! ### Complex tests and the restricted Weil ground energy -/

/-- **Coercive zeta positivity for complex tests on `[−6/25, 6/25]`.** -/
theorem zetaZeroConfig_re_W_ge_of_support_le_parityFolded {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Icc (-(6 / 25)) (6 / 25)) :
    1 / 250 * ∫ x, ‖g x‖ ^ 2 ≤ (zetaZeroConfig.W g g).re := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hzero : ∀ x, 6 / 25 < |x| → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hgs h
      rw [mem_Icc] at this
      exact absurd (abs_le.mpr this) (not_le.mpr hx)
  have hre : ContDiff ℝ 2 fun u => (g u).re := Complex.reCLM.contDiff.comp hg
  have him : ContDiff ℝ 2 fun u => (g u).im := Complex.imCLM.contDiff.comp hg
  have hrec : HasCompactSupport fun u => (g u).re := hgc.comp_left Complex.zero_re
  have himc : HasCompactSupport fun u => (g u).im := hgc.comp_left Complex.zero_im
  have h1 := fullZeroForm_ge_of_support_le_parityFolded hre hrec fun x hx => by simp [hzero x hx]
  have h2 := fullZeroForm_ge_of_support_le_parityFolded him himc fun x hx => by simp [hzero x hx]
  have hsplit := GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im
    hg hgc
  have i1 : Integrable fun x => (g x).re ^ 2 :=
    (hre.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hrec)
  have i2 : Integrable fun x => (g x).im ^ 2 :=
    (him.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq himc)
  have hnorm : (∫ x, ‖g x‖ ^ 2) = (∫ x, (g x).re ^ 2) + ∫ x, (g x).im ^ 2 := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hsplit, hnorm]
  linarith

/-- **The parity-fold floor**: `μ(A) ≥ 1/250` for every aperture `A ≤ 6/25`. -/
theorem one_div_250_le_ccmRestrictedWeilGroundEnergy {A : SuzukiPositiveAperture}
    (hA : A.1 ≤ 6 / 25) : 1 / 250 ≤ ccmRestrictedWeilGroundEnergy A := by
  rw [← suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  refine (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).2 ?_
  rintro r ⟨u, hu, rfl⟩
  have hnorm : ‖suzukiWeilIntervalFormEmbedding A u.toCCMFormVector‖ =
      ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ := by
    change ‖suzukiPhysicalToApertureCLM A (ccmArchimedeanFormToAperture A u.toCCMFormVector)‖ = _
    exact (suzukiApertureL2Equiv A).symm.norm_map _
  have hmass : suzukiWeilIntervalFormMass A u.toCCMFormVector = ∫ x, ‖u x‖ ^ 2 := by
    unfold suzukiWeilIntervalFormMass
    rw [hnorm, norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector]
  have hpos : 0 < suzukiWeilIntervalFormMass A u.toCCMFormVector :=
    pow_pos (norm_pos_iff.mpr hu) 2
  unfold suzukiWeilIntervalFormRayleigh
  rw [le_div_iff₀ hpos, ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil, hmass]
  have hsupp : tsupport (u : ℝ → ℂ) ⊆ Icc (-(6 / 25)) (6 / 25) :=
    u.tsupport_subset.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact zetaZeroConfig_re_W_ge_of_support_le_parityFolded
    (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hsupp

/-- **Contact apertures exceed `6/25`.** -/
theorem lt_of_ccmRestrictedWeilGroundEnergy_nonpos_parityFolded {A : SuzukiPositiveAperture}
    (h : ccmRestrictedWeilGroundEnergy A ≤ 0) : 6 / 25 < A.1 := by
  by_contra hA
  have := one_div_250_le_ccmRestrictedWeilGroundEnergy (not_lt.mp hA)
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory
