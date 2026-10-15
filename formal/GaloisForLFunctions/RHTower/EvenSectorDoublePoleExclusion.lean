import GaloisForLFunctions.RHTower.EvenSectorNegPartAbelRigidity
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# The double-pole branch of the even Weil cone is empty

For every pole weight and every arithmetic source positive on even tests, either the
source is the von Mangoldt source, or its negative part has a divergent Dirichlet
series at an exponent strictly greater than one (`canonical_or_negative_superpole`).
There is no convergence or Abel-limit assumption in this classification.

The mechanism is the exact cosine covariance of an even compact bump. If `g` is
`farBump`, `e_t = g(.-t)+g(.+t)`, and `Q` is the actual pole-weighted Weil form, then

`Q(g+c e_t) = C(0)+4c C(t)+2c²(C(0)+C(2t))`.

Positivity gives `2 C(t)² ≤ C(0)(C(0)+C(2t))`. A value above a fixed multiple of
its exponential type would propagate by repeated squaring and contradict that
type. This removes the polynomial factor of a negative double pole. The exact
compact-window Abel transform then supplies the missing hypothesis of Abel
pinning, and pinning identifies the source. The positive-part convergence already
forced by the cone makes the final alternative concern the negative part alone.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section
namespace RHTower.EvenSector
open OddSector WeilOneSided WeilPoleWeight

/-- The archimedean part of the cosine covariance of the fixed even bump. -/
def farCosineArch (t : ℝ) : ℝ :=
  1 / (2 * Real.pi) * ∫ r : ℝ,
    ‖paperFT (fun u => (farBump u : ℂ)) r‖ ^ 2 * Real.cos (t * r) * EF.gammaBracket r

/-- The exact arithmetic cosine covariance; no positivity assumption enters its definition. -/
def farCosineKernel (β : ℝ) (lam : ℕ → ℝ) (t : ℝ) : ℝ :=
  β * farJ ^ 2 * (Real.exp (-t / 2) + Real.exp (t / 2)) +
    farCosineArch t - farSum lam (t / 2)

theorem paperFT_evenFarBump (a r : ℝ) :
    paperFT (fun u => (evenFarBump a u : ℂ)) r =
      (2 * Real.cos (a * r) : ℝ) * paperFT (fun u => (farBump u : ℂ)) r := by
  rw [evenFarBumpC_eq,
    paperFT_sum_translate Finset.univ ![1, 1] ![a, -a]
      (g := fun u => (farBump u : ℂ))
      (Complex.continuous_ofReal.comp continuous_farBump)
      (hasCompactSupport_farBump.comp_left Complex.ofReal_zero)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos, Complex.cos]
  push_cast
  rw [show I * (r : ℂ) * (a : ℂ) = ((a : ℂ) * (r : ℂ)) * I by ring,
    show I * (r : ℂ) * -(a : ℂ) = -(((a : ℂ) * (r : ℂ)) * I) by ring]
  ring_nf

theorem atomPairing_farBump (lam : ℕ → ℝ) :
    atomPairing lam (crossCorr farBump farBump) = 0 := by
  unfold atomPairing
  refine (tsum_congr (g := fun _ : ℕ => (0 : ℝ)) ?_).trans
    (tsum_zero : (∑' _ : ℕ, (0 : ℝ)) = 0)
  intro n
  split_ifs with hn
  · have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by positivity) (by exact_mod_cast hn)
    have hlog : 0 < Real.log n := (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).trans_le hl
    have hk : farKernel (Real.log n) = 0 :=
      farKernel_eq_zero (by rw [abs_of_pos hlog]; exact two_mul_rOut_lt_log_two.le.trans hl)
    change lam n / Real.sqrt n * (farKernel (Real.log n) + farKernel (-Real.log n)) = 0
    rw [farKernel_neg, hk]
    ring
  · ring

theorem atomPairing_farBump_evenFarBump (lam : ℕ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    atomPairing lam (crossCorr farBump (evenFarBump a)) = 2 * farSum lam (a / 2) := by
  unfold atomPairing farSum
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  split_ifs with hn
  · have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by positivity) (by exact_mod_cast hn)
    have hlog : 0 < Real.log n := (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).trans_le hl
    rw [crossCorr_evenFarBump_right continuous_farBump hasCompactSupport_farBump,
      crossCorr_evenFarBump_right continuous_farBump hasCompactSupport_farBump]
    change lam n / Real.sqrt n *
      ((farKernel (Real.log n + a) + farKernel (Real.log n - a)) +
        (farKernel (-Real.log n + a) + farKernel (-Real.log n - a))) = _
    have hz : farKernel (Real.log n + a) = 0 :=
      farKernel_eq_zero (by rw [abs_of_pos (by linarith)]; linarith [two_mul_rOut_lt_log_two])
    rw [show -Real.log n - a = -(Real.log n + a) by ring,
      show -Real.log n + a = -(Real.log n - a) by ring,
      farKernel_neg, farKernel_neg, hz]
    rw [show 2 * (a / 2) = a by ring]
    ring
  · ring

theorem integrable_farCosineArch (t : ℝ) :
    Integrable fun r : ℝ =>
      ‖paperFT (fun u => (farBump u : ℂ)) r‖ ^ 2 * Real.cos (t * r) * EF.gammaBracket r := by
  have hg := integrable_normSq_paperFT_ofReal_mul_gammaBracket (contDiff_farBump 2)
    (fun x hx => farBump_eq_zero hx.le)
  have hc : Continuous fun r : ℝ => Real.cos (t * r) := by fun_prop
  exact (hg.bdd_mul hc.aestronglyMeasurable
    (Eventually.of_forall fun r => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * r))).congr
      (Eventually.of_forall fun r => by ring)

theorem abs_farCosineArch_le (t : ℝ) :
    |farCosineArch t| ≤ 1 / (2 * Real.pi) *
      ∫ r : ℝ, ‖paperFT (fun u => (farBump u : ℂ)) r‖ ^ 2 * |EF.gammaBracket r| := by
  have hg := integrable_normSq_paperFT_mul_abs_gammaBracket (contDiff_farBump 2)
    (fun x hx => farBump_eq_zero hx.le)
  unfold farCosineArch
  rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun r => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (norm_nonneg _)]
  calc _ ≤ ‖paperFT (fun u => (farBump u : ℂ)) r‖ ^ 2 * 1 * |EF.gammaBracket r| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (t * r)) (sq_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

theorem farArch_farBump_add_smul_evenFarBump (a c : ℝ) :
    farArch (fun x => farBump x + c * evenFarBump a x) =
      farCosineArch 0 + 4 * c * farCosineArch a +
        c ^ 2 * (2 * farCosineArch 0 + 2 * farCosineArch (2 * a)) := by
  have hft : ∀ r : ℝ,
      paperFT (fun u => ((farBump u + c * evenFarBump a u : ℝ) : ℂ)) r =
        ((1 + 2 * c * Real.cos (a * r) : ℝ) : ℂ) *
          paperFT (fun u => (farBump u : ℂ)) r := by
    intro r
    have hf := paperFT_ofReal_add_smul continuous_farBump hasCompactSupport_farBump
      (continuous_evenFarBump a) (hasCompactSupport_evenFarBump a) 1 c r
    simp only [one_mul, Complex.ofReal_one] at hf
    rw [hf, paperFT_evenFarBump]
    push_cast
    ring
  have hpt : ∀ r : ℝ,
      ‖paperFT (fun u => ((farBump u + c * evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 * EF.gammaBracket r =
        (‖paperFT (fun u => (farBump u : ℂ)) r‖ ^ 2 * Real.cos (0 * r) * EF.gammaBracket r) +
        (4 * c) * (‖paperFT (fun u => (farBump u : ℂ)) r‖ ^ 2 * Real.cos (a * r) * EF.gammaBracket r) +
        c ^ 2 * (2 * (‖paperFT (fun u => (farBump u : ℂ)) r‖ ^ 2 * Real.cos (0 * r) * EF.gammaBracket r) +
          2 * (‖paperFT (fun u => (farBump u : ℂ)) r‖ ^ 2 * Real.cos ((2 * a) * r) * EF.gammaBracket r)) := by
    intro r
    rw [hft, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      show (2 * a) * r = 2 * (a * r) by ring, Real.cos_two_mul]
    simp only [zero_mul, Real.cos_zero, mul_one]
    ring
  unfold farArch farCosineArch
  simp_rw [hpt]
  have hsum := integral_add
    ((integrable_farCosineArch 0).add ((integrable_farCosineArch a).const_mul (4 * c)))
    ((((integrable_farCosineArch 0).const_mul 2).add
      ((integrable_farCosineArch (2 * a)).const_mul 2)).const_mul (c ^ 2))
  have hleft := integral_add (integrable_farCosineArch 0)
    ((integrable_farCosineArch a).const_mul (4 * c))
  have hright := integral_add ((integrable_farCosineArch 0).const_mul 2)
    ((integrable_farCosineArch (2 * a)).const_mul 2)
  simp only [Pi.add_apply] at hsum hleft hright
  rw [hsum, hleft, integral_const_mul, integral_const_mul, hright]
  simp only [integral_const_mul]
  ring

theorem integral_farBump_add_smul_evenFarBump (a c : ℝ) :
    (∫ x, (farBump x + c * evenFarBump a x) * Real.exp (-x / 2)) =
      farJ * (1 + c * (Real.exp (-a / 2) + Real.exp (a / 2))) := by
  have hg : Integrable fun x => farBump x * Real.exp (-x / 2) :=
    (continuous_farBump.mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_farBump.mul_right
  have he : Integrable fun x => evenFarBump a x * Real.exp (-x / 2) :=
    ((continuous_evenFarBump a).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_evenFarBump a).mul_right
  rw [show (fun x => (farBump x + c * evenFarBump a x) * Real.exp (-x / 2)) =
      fun x => farBump x * Real.exp (-x / 2) + c * (evenFarBump a x * Real.exp (-x / 2)) by
      funext x; ring,
    integral_add hg (he.const_mul c), integral_const_mul, integral_evenFarBump_mul_exp]
  change farJ + c * ((Real.exp (-a / 2) + Real.exp (a / 2)) * farJ) = _
  ring

theorem farCosineKernel_zero (β : ℝ) (lam : ℕ → ℝ) :
    farCosineKernel β lam 0 = 2 * β * farJ ^ 2 + farCosineArch 0 := by
  simp [farCosineKernel, farSum_eq_zero_of_nonpos lam (le_refl 0)]
  ring

/-- Exact quadratic source identity for two even translates. -/
theorem re_weilPoleWeightFunctional_farBump_add_smul_evenFarBump
    (β : ℝ) (lam : ℕ → ℝ) {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    (weilPoleWeightFunctional β lam
      (EF.weilTest (fun x => ((farBump x + c * evenFarBump a x : ℝ) : ℂ))
        (fun x => ((farBump x + c * evenFarBump a x : ℝ) : ℂ)))).re =
      farCosineKernel β lam 0 + 4 * c * farCosineKernel β lam a +
        2 * c ^ 2 * (farCosineKernel β lam 0 + farCosineKernel β lam (2 * a)) := by
  have hg : Continuous fun x => farBump x + c * evenFarBump a x :=
    continuous_farBump.add ((continuous_evenFarBump a).const_mul c)
  have hgc : HasCompactSupport fun x => farBump x + c * evenFarBump a x :=
    hasCompactSupport_farBump.add (hasCompactSupport_evenFarBump a).mul_left
  have hge : ∀ x, farBump (-x) + c * evenFarBump a (-x) = farBump x + c * evenFarBump a x :=
    fun x => by rw [farBump_neg, evenFarBump_neg]
  rw [re_weilPoleWeightFunctional_eq_add, re_weilFullFunctional_ofReal_eq lam hg hgc,
    re_weilPoleTerm_ofReal_even hg hgc hge,
    integral_farBump_add_smul_evenFarBump,
    farArch_farBump_add_smul_evenFarBump,
    RHTower.atomPairing_add_smul_expand lam continuous_farBump hasCompactSupport_farBump
      (continuous_evenFarBump a) (hasCompactSupport_evenFarBump a),
    atomPairing_farBump, atomPairing_farBump_evenFarBump lam ha, atomPairing_evenFarBump lam ha,
    farCosineKernel_zero]
  unfold farCosineKernel
  rw [show 2 * a / 2 = a by ring,
    show -(2 * a) / 2 = -a by ring]
  have hneg : Real.exp (-a / 2) ^ 2 = Real.exp (-a) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hpos : Real.exp (a / 2) ^ 2 = Real.exp a := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hcross : Real.exp (-a / 2) * Real.exp (a / 2) = 1 := by
    rw [← Real.exp_add, show -a / 2 + a / 2 = 0 by ring, Real.exp_zero]
  linear_combination 2 * β * farJ ^ 2 * c ^ 2 * hneg +
    2 * β * farJ ^ 2 * c ^ 2 * hpos + 4 * β * farJ ^ 2 * c ^ 2 * hcross

theorem farCosineKernel_zero_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) : 0 ≤ farCosineKernel β lam 0 := by
  have hp := h (fun x => (farBump x : ℂ)) (contDiff_ofReal_comp (contDiff_farBump 2))
    (hasCompactSupport_farBump.comp_left Complex.ofReal_zero) (fun x => by rw [farBump_neg])
  have he := re_weilPoleWeightFunctional_farBump_add_smul_evenFarBump β lam (le_refl 0) 0
  simp only [zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at he
  rwa [he] at hp

/-- Positivity imposes the cosine doubling law on the actual arithmetic kernel. -/
theorem farCosineKernel_doubling {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {a : ℝ} (ha : 0 ≤ a) :
    2 * farCosineKernel β lam a ^ 2 ≤
      farCosineKernel β lam 0 * (farCosineKernel β lam 0 + farCosineKernel β lam (2 * a)) := by
  have hquad : ∀ c : ℝ, 0 ≤ farCosineKernel β lam 0 + 4 * c * farCosineKernel β lam a +
      2 * c ^ 2 * (farCosineKernel β lam 0 + farCosineKernel β lam (2 * a)) := by
    intro c
    rw [← re_weilPoleWeightFunctional_farBump_add_smul_evenFarBump β lam ha c]
    exact h _ (contDiff_ofReal_comp ((contDiff_farBump 2).add ((contDiff_evenFarBump a).const_smul c)))
      ((hasCompactSupport_farBump.add (hasCompactSupport_evenFarBump a).mul_left).comp_left
        Complex.ofReal_zero) (fun x => by rw [farBump_neg, evenFarBump_neg])
  have hd := discrim_le_zero (a := 2 * (farCosineKernel β lam 0 + farCosineKernel β lam (2 * a)))
    (b := 4 * farCosineKernel β lam a) (c := farCosineKernel β lam 0)
    (fun c => by nlinarith only [hquad c])
  unfold discrim at hd
  nlinarith only [hd]

/-- Compact arithmetic windows inherit the absolute Dirichlet exponential type. -/
theorem exists_abs_farSum_half_le_exp {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {s : ℝ} (hs : 0 < s) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ,
      |farSum lam (t / 2)| ≤ D * Real.exp ((1 / 2 + s) * t) := by
  let c : ℕ → ℝ := fun n => if 2 ≤ n then lam n / Real.sqrt n else 0
  let b : ℝ := 1 / 2 + s
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hm : 0 ≤ farMass := integral_nonneg farBump_nonneg
  have hsum : Summable fun n : ℕ => |c n| * Real.exp (-b * Real.log n) :=
    summable_abs_coeff_mul_exp hsl hs
  refine ⟨farMass * Real.exp b * (∑' n : ℕ, |c n| * Real.exp (-b * Real.log n)), by positivity, ?_⟩
  intro t
  have hterm : ∀ n : ℕ, ‖c n * farKernel (Real.log n - t)‖ ≤
      (farMass * Real.exp (b * (t + 1))) * (|c n| * Real.exp (-b * Real.log n)) := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (farKernel_nonneg _)]
    have hk : farKernel (Real.log n - t) ≤
        farMass * Real.exp (b * (t + 1)) * Real.exp (-b * Real.log n) := by
      by_cases hz : 2 * (nodeBump 2).rOut ≤ |Real.log n - t|
      · rw [farKernel_eq_zero hz]; positivity
      · have hr := nodeBump_rOut_le 2
        have hlog : Real.log n ≤ t + 1 := by
          have := le_abs_self (Real.log n - t)
          push Not at hz
          linarith
        have he : 1 ≤ Real.exp (b * (t + 1)) * Real.exp (-b * Real.log n) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by nlinarith)
        calc farKernel (Real.log n - t) ≤ farMass := farKernel_le _
          _ ≤ farMass * (Real.exp (b * (t + 1)) * Real.exp (-b * Real.log n)) := by
            nlinarith only [he, hm]
          _ = _ := by ring
    calc _ ≤ |c n| * (farMass * Real.exp (b * (t + 1)) * Real.exp (-b * Real.log n)) :=
        mul_le_mul_of_nonneg_left hk (abs_nonneg _)
      _ = _ := by ring
  have hmajor := hsum.mul_left (farMass * Real.exp (b * (t + 1)))
  have hnorm : Summable fun n : ℕ => ‖c n * farKernel (Real.log n - t)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmajor
  have hnormsum := (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hterm hmajor)
  rw [tsum_mul_left, Real.norm_eq_abs] at hnormsum
  have he : Real.exp (b * (t + 1)) = Real.exp b * Real.exp (b * t) := by
    rw [← Real.exp_add]; congr 1; ring
  change |∑' n : ℕ, c n * farKernel (Real.log n - 2 * (t / 2))| ≤ _
  rw [show 2 * (t / 2) = t by ring]
  calc _ ≤ (farMass * Real.exp (b * (t + 1))) *
        (∑' n : ℕ, |c n| * Real.exp (-b * Real.log n)) := hnormsum
    _ = _ := by rw [he]; ring

/-- Every right-of-one absolute Dirichlet exponent controls this exact cosine kernel. -/
theorem exists_farCosineKernel_le_exp {β : ℝ} {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {s : ℝ} (hs : 0 < s) :
    ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t →
      farCosineKernel β lam t ≤ M * Real.exp ((1 / 2 + s) * t) := by
  obtain ⟨D, hD, hwindow⟩ := exists_abs_farSum_half_le_exp hsl hs
  let A : ℝ := 1 / (2 * Real.pi) *
    ∫ r : ℝ, ‖paperFT (fun u => (farBump u : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|
  have hA : 0 ≤ A := mul_nonneg (by positivity) (integral_nonneg (fun _ => by positivity))
  refine ⟨2 * |β| * farJ ^ 2 + A + D, ?_⟩
  intro t ht
  have harch := (le_abs_self (farCosineArch t)).trans (abs_farCosineArch_le t)
  have hprime := (neg_le_abs (farSum lam (t / 2))).trans (hwindow t)
  have he : 1 ≤ Real.exp ((1 / 2 + s) * t) := Real.one_le_exp (by positivity)
  have hneg : Real.exp (-t / 2) ≤ Real.exp ((1 / 2 + s) * t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hpos : Real.exp (t / 2) ≤ Real.exp ((1 / 2 + s) * t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hpole : β * farJ ^ 2 * (Real.exp (-t / 2) + Real.exp (t / 2)) ≤
      2 * |β| * farJ ^ 2 * Real.exp ((1 / 2 + s) * t) := by
    calc _ ≤ |β| * farJ ^ 2 * (Real.exp (-t / 2) + Real.exp (t / 2)) := by
          gcongr; exact le_abs_self β
      _ ≤ |β| * farJ ^ 2 * (2 * Real.exp ((1 / 2 + s) * t)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  unfold farCosineKernel
  change farCosineArch t ≤ A at harch
  nlinarith only [hpole, hprime, harch, mul_le_mul_of_nonneg_left he hA]

theorem cosine_doubling_exponential_type {C : ℝ → ℝ} {q b M : ℝ}
    (hq : 0 ≤ q) (hb : 0 ≤ b)
    (hquad : ∀ t, 0 ≤ t → 2 * C t ^ 2 ≤ q * (q + C (2 * t)))
    (hgrowth : ∀ t, 0 ≤ t → C t ≤ M * Real.exp (b * t))
    {t : ℝ} (ht : 0 ≤ t) : C t ≤ 2 * q * Real.exp (b * t) := by
  rcases eq_or_lt_of_le hq with hq | hq
  · have h := hquad t ht
    rw [← hq] at h ⊢
    nlinarith [sq_nonneg (C t)]
  by_contra hfail
  have hlarge : 2 * q * Real.exp (b * t) < C t := lt_of_not_ge hfail
  let r := C t / (2 * q)
  have he : 1 ≤ Real.exp (b * t) := Real.one_le_exp (mul_nonneg hb ht)
  have hr : Real.exp (b * t) < r := (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hr1 : 1 < r := he.trans_lt hr
  have hr0 : 0 < r := by linarith
  have hiter : ∀ n : ℕ, 2 * q * r ^ (2 ^ n) ≤ C ((2 : ℝ) ^ n * t) := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, pow_one, one_mul]
      dsimp [r]
      rw [mul_div_cancel₀ _ (by positivity : 2 * q ≠ 0)]
    | succ n ih =>
      have hp : 1 ≤ r ^ (2 ^ n) := one_le_pow₀ hr1.le
      have hc : 2 * q ≤ C ((2 : ℝ) ^ n * t) := by nlinarith
      have hx := hquad ((2 : ℝ) ^ n * t) (by positivity)
      have hs : (2 * q * r ^ (2 ^ n)) ^ 2 ≤ C ((2 : ℝ) ^ n * t) ^ 2 :=
        pow_le_pow_left₀ (by positivity) ih 2
      rw [show (2 : ℝ) ^ (n + 1) * t = 2 * ((2 : ℝ) ^ n * t) by rw [pow_succ]; ring]
      rw [show (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 by rw [pow_succ], pow_mul]
      nlinarith [sq_nonneg (C ((2 : ℝ) ^ n * t)), sq_nonneg q]
  have hratio : 1 < r / Real.exp (b * t) :=
    (one_lt_div (Real.exp_pos _)).mpr hr
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt hratio).comp
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℕ) < 2 by decide))
  obtain ⟨n, hn⟩ := (hpow.eventually (eventually_gt_atTop (M / (2 * q)))).exists
  have hlow := hiter n
  have hupp := hgrowth ((2 : ℝ) ^ n * t) (by positivity)
  have hexp : Real.exp (b * ((2 : ℝ) ^ n * t)) =
      Real.exp (b * t) ^ (2 ^ n) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp] at hupp
  change M / (2 * q) < (r / Real.exp (b * t)) ^ (2 ^ n) at hn
  rw [div_pow] at hn
  have hden : 0 < Real.exp (b * t) ^ (2 ^ n) := by positivity
  have hbad := (div_lt_div_iff₀ (by positivity : 0 < 2 * q) hden).mp hn
  nlinarith

/-- Reflection positivity removes every polynomial prefactor at the Dirichlet boundary. -/
theorem exists_farSum_uniform_exponential_floor {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 0 < s → ∀ a : ℝ, 0 ≤ a →
      -K * Real.exp ((1 + s) * a) ≤ farSum lam a := by
  let q := farCosineKernel β lam 0
  have hq : 0 ≤ q := farCosineKernel_zero_nonneg h
  let A : ℝ := 1 / (2 * Real.pi) *
    ∫ r : ℝ, ‖paperFT (fun u => (farBump u : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|
  have hA : 0 ≤ A := mul_nonneg (by positivity) (integral_nonneg (fun _ => by positivity))
  refine ⟨2 * |β| * farJ ^ 2 + A + 2 * q, by positivity, ?_⟩
  intro s hs a ha
  obtain ⟨M, hM⟩ := exists_farCosineKernel_le_exp (β := β) hsl (half_pos hs)
  have hC := cosine_doubling_exponential_type (C := farCosineKernel β lam) (q := q) hq (by positivity : 0 ≤ 1 / 2 + s / 2)
    (fun t ht => farCosineKernel_doubling h (a := t) ht) hM (show 0 ≤ 2 * a by positivity)
  rw [show (1 / 2 + s / 2) * (2 * a) = (1 + s) * a by ring] at hC
  have he : 1 ≤ Real.exp ((1 + s) * a) := Real.one_le_exp (by positivity)
  have hneg : Real.exp (-a) ≤ Real.exp ((1 + s) * a) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hpos : Real.exp a ≤ Real.exp ((1 + s) * a) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hP : -2 * |β| * farJ ^ 2 * Real.exp ((1 + s) * a) ≤
      β * farJ ^ 2 * (Real.exp (-a) + Real.exp a) := by
    have hp := mul_le_mul_of_nonneg_left (show Real.exp (-a) + Real.exp a ≤
      2 * Real.exp ((1 + s) * a) by linarith)
        (show 0 ≤ |β| * farJ ^ 2 by positivity)
    have hb := mul_le_mul_of_nonneg_right (neg_abs_le β)
      (show 0 ≤ farJ ^ 2 * (Real.exp (-a) + Real.exp a) by positivity)
    nlinarith only [hp, hb]
  have hArch : -A ≤ farCosineArch (2 * a) :=
    (neg_le_neg (abs_farCosineArch_le (2 * a))).trans (neg_abs_le _)
  have hAE := mul_le_mul_of_nonneg_left he hA
  unfold farCosineKernel at hC
  rw [show 2 * a / 2 = a by ring, show -(2 * a) / 2 = -a by ring] at hC
  nlinarith only [hC, hP, hArch, hAE]

/-- The exact Abel transform of an even-positive source has no negative higher-order pole. -/
theorem exists_oddDirichlet_simple_pole_floor {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 0 < s → s ≤ 1 → -B ≤ s * oddDirichlet lam s := by
  obtain ⟨K, hK, hwindow⟩ := exists_farSum_uniform_exponential_floor h hsl
  have hI : ∀ s : ℝ, 0 < s → -K / s ≤ farLaplace s / 2 * oddDirichlet lam s := by
    intro s hs
    obtain ⟨hint, heq⟩ := integral_farSum_mul_exp hsl hs
    have hzero : ∫ a in Ioi 0, farSum lam a * Real.exp (-(1 + 2 * s) * a) =
        ∫ a, farSum lam a * Real.exp (-(1 + 2 * s) * a) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => by
        simp only [mem_Ioi, not_lt] at ha
        rw [farSum_eq_zero_of_nonpos lam ha, zero_mul]
    have hexp : IntegrableOn (fun a : ℝ => Real.exp (-s * a)) (Ioi 0) :=
      integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0
    have hval : ∫ a in Ioi 0, -K * Real.exp (-s * a) = -K / s := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hs)]
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
      ring
    rw [← heq, ← hzero, ← hval]
    refine setIntegral_mono_on (hexp.const_mul _) hint.integrableOn measurableSet_Ioi fun a ha => ?_
    have hw := mul_le_mul_of_nonneg_right (hwindow s hs a (le_of_lt (mem_Ioi.mp ha)))
      (Real.exp_pos (-(1 + 2 * s) * a)).le
    have he : Real.exp ((1 + s) * a) * Real.exp (-(1 + 2 * s) * a) = Real.exp (-s * a) := by
      rw [← Real.exp_add]; congr 1; ring
    simpa only [mul_assoc, he] using hw
  let c : ℝ := Real.exp (-(1 / 6 : ℝ)) * farJ ^ 2 / 2
  have hc : 0 < c := by have hJ := farJ_pos; dsimp [c]; positivity
  refine ⟨K / c, by positivity, ?_⟩
  intro s hs hs1
  have hL : c ≤ farLaplace s / 2 := by
    have h0 := farLaplace_ge hs.le
    rw [farLaplace_zero] at h0
    have he := Real.exp_le_exp.mpr (show -(1 / 6 : ℝ) ≤ -(s / 6) by linarith)
    have he' := mul_le_mul_of_nonneg_right he (sq_nonneg farJ)
    dsimp [c]
    linarith
  have hi := mul_le_mul_of_nonneg_left (hI s hs) hs.le
  have hcancel : s * (-K / s) = -K := mul_div_cancel₀ (-K) hs.ne'
  rw [hcancel] at hi
  by_cases hF : 0 ≤ s * oddDirichlet lam s
  · exact (neg_nonpos.mpr (by positivity : 0 ≤ K / c)).trans hF
  · have hprod := mul_le_mul_of_nonpos_right hL (le_of_not_ge hF)
    rw [← neg_div]
    apply (div_le_iff₀ hc).mpr
    nlinarith only [hi, hprod]

theorem no_negative_double_pole_of_weilPositiveEvenAt {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) :
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * (s * oddDirichlet lam s) := by
  obtain ⟨B, hB, hfloor⟩ := exists_oddDirichlet_simple_pole_floor h hsl
  intro ε hε
  have hδ : 0 < ε / (B + 1) := by positivity
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with s hs hs1 hsδ
  have hs' : 0 < s := hs
  have hf := mul_le_mul_of_nonneg_left (hfloor s hs' hs1.le) hs'.le
  have hsmall : s * (B + 1) < ε := (lt_div_iff₀ (by positivity)).mp hsδ
  nlinarith only [hf, hsmall, hs']

/-- Absolute convergence to the right of one leaves only the canonical source. -/
private theorem canonical_of_weilPositiveEvenAt_of_absolute_convergence {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  (riemannHypothesis_of_weilPositiveEvenAt_of_abel h hsl
    (no_negative_double_pole_of_weilPositiveEvenAt h hsl)).2

/-- **EWU branch elimination.** Every even-positive arithmetic source is canonical,
or its negative part diverges at some Dirichlet exponent strictly greater than one.
The alternatives cover the entire cone; no summability or Abel premise is assumed. -/
theorem canonical_or_negative_superpole (β : ℝ) (lam : ℕ → ℝ) :
    WeilPositiveEvenAt β lam →
      (∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∨
        ∃ σ : ℝ, 1 < σ ∧ ¬Summable (fun n : ℕ => max (-lam n) 0 / (n : ℝ) ^ σ) := by
  intro h
  by_cases hs : ∀ σ : ℝ, 1 < σ → Summable (fun n : ℕ => max (-lam n) 0 / (n : ℝ) ^ σ)
  · exact Or.inl (canonical_of_weilPositiveEvenAt_of_absolute_convergence h
      (fun σ hσ => summable_abs_div_rpow_of_weilPositiveEvenAt_of_negPart h hσ (hs σ hσ)))
  · exact Or.inr (by push Not at hs; exact hs)

end RHTower.EvenSector
