import GaloisForLFunctions.RHTower.CHMDStage8EvenWindowPosPartAndTwoBumpMidpointConvexity

/-!
# CHMD Stage 9: Odd Two-Bump Midpoint Concavity and the Three Joint Parity Elimination Laws

This module establishes the **Stage 9** odd-sector counterpart to Stage 8 and the three exact
joint parity elimination laws on `WeilPositiveEvenPolar lam ∧ WeilPositiveOddPolar lam` (and in
particular on the full polar cone `WeilPositive lam`):

1. **The Odd Pole-Free Cone `WeilPositiveOddPolar` and Subsumption Laws
   (`WeilPositiveOddPolar`, `weilPositiveOddPolar_of_weilPositiveOddAt`,
   `weilPositiveOddPolar_of_weilPositive`, `re_weilPoleTerm_ofReal_odd`)**:
   We define `WeilPositiveOddPolar lam` as Weil positivity on all odd compactly supported `C²`
   tests with `paperFT f (I / 2) = 0`, and prove that it is implied both by `WeilPositiveOddAt β lam`
   at any real pole weight `β ∈ ℝ` and by `WeilPositive lam`.

2. **Exact Cross-Kernel, Cross-Sum, and Hyperbolic Sine Pole-Free Coefficient for Odd Far Bumps
   (`oddFarBump_eq_zero`, `continuous_oddFarBump`, `farCrossKernel_neg_of_odd`,
   `crossCorr_oddFarBump_right`, `atomPairing_crossCorr_oddFarBump`,
   `farCrossKernel_oddFarBump`, `farCrossSum_oddFarBump`,
   `oddFarCoeff`, `oddFarCoeff_oddFarBump_eq_sinh_div_sinh`, `integral_sub_oddFarCoeff_mul_exp`)**:
   For `oddFarBump b x = farBump (x - b) - farBump (x + b)`:
   - `farCrossKernel (oddFarBump b) y = farKernel (y - b) - farKernel (y + b)`;
   - `farCrossSum lam (oddFarBump b) a = farSum lam ((a + b) / 2) - farSum lam ((a - b) / 2)`;
   - `oddFarCoeff (oddFarBump b) a = Real.sinh (b / 2) / Real.sinh (a / 2) ∈ [0, 1]` for `0 ≤ b ≤ a` (`0 < a`).

3. **Uniform Odd Two-Bump Archimedean Bound and Midpoint Concavity Law on `WeilPositiveOddPolar`
   (`abs_farArch_oddFarBump_le`, `abs_farArch_oddFarBump_add_oddFarBump_le`,
   `farArch_oddFarBump_sub_smul_le`, `two_bump_farSum_midpoint_le_of_weilPositiveOddPolar`,
   `two_bump_sinh_normalized_midpoint_le_of_weilPositiveOddPolar`)**:
   On `H_{b, a}(x) = oddFarBump b x - (sinh(b/2) / sinh(a/2)) * oddFarBump a x` (`0 ≤ b`, `b + 2 ≤ a`),
   the archimedean energy is bounded uniformly by `(4 / π) * farBumpArchMass`, and the odd
   self-terms `-2 * farSum lam b`, `-2 * s^2 * farSum lam a` and opposite-side cross-term
   `+4 * s * farSum lam ((a + b) / 2)` flip sign relative to the even case while the same-side
   cross-term `-4 * s * farSum lam ((a - b) / 2)` retains the same negative sign:
   `-2 * farSum lam b - 2 * s^2 * farSum lam a + 4 * s * (farSum lam ((a + b) / 2) - farSum lam ((a - b) / 2)) ≤ (4 / π) * farBumpArchMass`.

4. **The Three Joint Parity Elimination Laws (`joint_two_bump_eliminate_lower_endpoint`,
   `joint_two_bump_eliminate_midpoint`, `joint_two_bump_eliminate_upper_endpoint`)**:
   Combining the even (`c = cosh(b/2) / cosh(a/2)`) and odd (`s = sinh(b/2) / sinh(a/2)`)
   two-bump pole-free inequalities with positive weights `(1, 1)`, `(s, c)`, and `(s^2, c^2)`
   respectively eliminates each of the three high-scale window sums `farSum lam b`,
   `farSum lam ((a + b) / 2)`, and `farSum lam a` in turn:
   - **Lower-Endpoint Elimination `(1, 1)`**:
     `2 * (c^2 - s^2) * farSum lam a - 4 * (c - s) * farSum lam ((a + b) / 2) - 4 * (c + s) * farSum lam ((a - b) / 2) ≤ (8 / π) * farBumpArchMass`;
   - **Midpoint Elimination `(s, c)`**:
     `2 * c * s * (c - s) * farSum lam a - 2 * (c - s) * farSum lam b - 8 * c * s * farSum lam ((a - b) / 2) ≤ (c + s) * ((4 / π) * farBumpArchMass)`;
   - **Upper-Endpoint Elimination `(s^2, c^2)`**:
     `4 * c * s * (c - s) * farSum lam ((a + b) / 2) - 2 * (c^2 - s^2) * farSum lam b - 4 * c * s * (c + s) * farSum lam ((a - b) / 2) ≤ (c^2 + s^2) * ((4 / π) * farBumpArchMass)`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.CHMDStage9

open EvenSector OddSector WeilOneSided WeilPoleWeight WeilSpectral WeilMeanSquare ResonatorProfile
open CHMDStage6 CHMDStage7 CHMDStage8

/-! ## Section 1: The Odd Pole-Free Cone `WeilPositiveOddPolar` and Subsumption Laws -/

/-- Weil positivity on odd tests whose Fourier transform vanishes at `i/2`; the pole term vanishes. -/
def WeilPositiveOddPolar (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → (∀ x, f (-x) = -f x) →
    paperFT f (I / 2) = 0 → 0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re

/-- Odd Weil positivity at any pole weight `β ∈ ℝ` implies odd pole-free positivity. -/
theorem weilPositiveOddPolar_of_weilPositiveOddAt {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveOddAt β lam) : WeilPositiveOddPolar lam := by
  intro f hf hfc hfo h0
  have hpos := h f hf hfc hfo
  rw [re_weilPoleWeightFunctional_eq_add, re_weilPoleTerm_weilTest_of_odd hf.continuous hfc hfo,
    h0, norm_zero, sq, mul_zero, mul_zero, mul_zero, add_zero] at hpos
  exact hpos

/-- Polar Weil positivity (`WeilPositive lam`) implies odd pole-free positivity. -/
theorem weilPositiveOddPolar_of_weilPositive {lam : ℕ → ℝ} (hW : WeilPositive lam) :
    WeilPositiveOddPolar lam := by
  intro f hf hfc hfo h0
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hfs : tsupport f ⊆ Icc (-|R|) |R| := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    rw [mem_Icc]
    constructor <;> [have := neg_abs_le x; have := le_abs_self x] <;>
      linarith [le_abs_self R]
  have hm : paperFT f (-(I / 2)) = 0 := by rw [paperFT_neg_of_odd hfo, h0, neg_zero]
  have h := hW |R| (abs_nonneg R) f hf hfs h0 hm
  rw [integral_weilAtomSymbol_eq_two_pi_mul_re (abs_nonneg R) hf hfs h0 hm] at h
  have hπ : 0 < 2 * π := by positivity
  exact nonneg_of_mul_nonneg_right (by linarith) hπ

/-- For a real odd test `F`, the pole term is `-2 * (∫ u, F u * Real.exp (-u / 2)) ^ 2`. -/
theorem re_weilPoleTerm_ofReal_odd {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hFo : ∀ x, F (-x) = -F x) :
    (weilPoleTerm (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re =
      -2 * (∫ u, F u * Real.exp (-u / 2)) ^ 2 := by
  have hc : Continuous fun u => (F u : ℂ) := Complex.continuous_ofReal.comp hF
  have hcs : HasCompactSupport fun u => (F u : ℂ) := hFc.comp_left Complex.ofReal_zero
  have hodd : ∀ x, (fun u => (F u : ℂ)) (-x) = -(fun u => (F u : ℂ)) x := fun x => by
    dsimp only; rw [hFo x, Complex.ofReal_neg]
  rw [re_weilPoleTerm_weilTest_of_odd hc hcs hodd, paperFT_ofRealFun_I_div_two,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## Section 2: Odd Far-Bump Support, Cross-Kernel, Cross-Sum, and Hyperbolic Sine Pole-Free Coefficient -/

theorem continuous_oddFarBump (a : ℝ) : Continuous (oddFarBump a) :=
  (contDiff_oddFarBump a).continuous

theorem oddFarBump_eq_zero {a x : ℝ} (ha : 0 ≤ a) (hx : a + 1 < |x|) : oddFarBump a x = 0 := by
  have hr := nodeBump_rOut_le 2
  have h1 := abs_sub_abs_le_abs_sub x a
  have h2 := abs_sub_abs_le_abs_sub x (-a)
  rw [abs_of_nonneg ha] at h1
  rw [abs_neg, abs_of_nonneg ha, sub_neg_eq_add] at h2
  unfold oddFarBump
  rw [farBump_eq_zero (by linarith), farBump_eq_zero (by linarith), sub_zero]

theorem farCrossKernel_neg_of_odd {g : ℝ → ℝ} (hgo : ∀ x, g (-x) = -g x) (y : ℝ) :
    farCrossKernel g (-y) = -farCrossKernel g y := by
  unfold farCrossKernel crossCorr
  rw [← integral_neg_eq_self (fun t => g t * farBump (t - -y)), ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [hgo t, show -t - -y = -(t - y) by ring, farBump_neg]
  ring

theorem crossCorr_oddFarBump_right {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (a y : ℝ) :
    crossCorr g (oddFarBump a) y = farCrossKernel g (y + a) - farCrossKernel g (y - a) := by
  unfold crossCorr oddFarBump farCrossKernel crossCorr
  have i1 : Integrable fun t => g t * farBump (t - y - a) := by
    refine (integrable_translate_prod hg hgc continuous_farBump (y + a)).congr
      (Eventually.of_forall fun t => ?_)
    show g t * farBump (t - (y + a)) = g t * farBump (t - y - a)
    rw [show t - (y + a) = t - y - a by ring]
  have i2 : Integrable fun t => g t * farBump (t - y + a) := by
    refine (integrable_translate_prod hg hgc continuous_farBump (y - a)).congr
      (Eventually.of_forall fun t => ?_)
    show g t * farBump (t - (y - a)) = g t * farBump (t - y + a)
    rw [show t - (y - a) = t - y + a by ring]
  have e : (fun t => g t * (farBump (t - y - a) - farBump (t - y + a))) =
      fun t => g t * farBump (t - y - a) - g t * farBump (t - y + a) := by
    funext t; ring
  rw [e, integral_sub i1 i2]
  congr 1
  · congr 1; funext t; congr 2; ring
  · congr 1; funext t; congr 2; ring

/-- The atoms of `g ⋆ õ_a` for an odd test `g` are `-2 * farCrossSum lam g a` once `a ≥ R + 1`. -/
theorem atomPairing_crossCorr_oddFarBump (lam : ℕ → ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgo : ∀ x, g (-x) = -g x) {R : ℝ} (hR : 0 ≤ R)
    (hgs : ∀ x, R < |x| → g x = 0) {a : ℝ} (ha : R + 1 ≤ a) :
    atomPairing lam (crossCorr g (oddFarBump a)) = -2 * farCrossSum lam g a := by
  unfold atomPairing farCrossSum
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  split_ifs with hn
  · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    rw [crossCorr_oddFarBump_right hg hgc, crossCorr_oddFarBump_right hg hgc]
    have z1 : farCrossKernel g (Real.log n + a) = 0 :=
      farCrossKernel_eq_zero hgs (by rw [abs_of_pos (by linarith)]; linarith)
    have z2 : farCrossKernel g (-Real.log n - a) = 0 := by
      rw [show -Real.log n - a = -(Real.log n + a) by ring, farCrossKernel_neg_of_odd hgo, z1,
        neg_zero]
    have e3 : farCrossKernel g (-Real.log n + a) = -farCrossKernel g (Real.log n - a) := by
      rw [show -Real.log n + a = -(Real.log n - a) by ring, farCrossKernel_neg_of_odd hgo]
    rw [z1, z2, e3]
    ring
  · ring

/-- **Cross-Kernel of an Odd Far Bump**:
`farCrossKernel (oddFarBump b) y = farKernel (y - b) - farKernel (y + b)`. -/
theorem farCrossKernel_oddFarBump (b y : ℝ) :
    farCrossKernel (oddFarBump b) y = farKernel (y - b) - farKernel (y + b) := by
  unfold farCrossKernel oddFarBump farKernel crossCorr
  have i1 : Integrable fun t => farBump (t - b) * farBump (t - y) := by
    have := (integrable_farBump_mul (y - b)).comp_sub_right b
    refine this.congr (Eventually.of_forall fun t => ?_)
    show farBump (t - b) * farBump (t - b - (y - b)) = _
    rw [show t - b - (y - b) = t - y by ring]
  have i2 : Integrable fun t => farBump (t + b) * farBump (t - y) := by
    have := (integrable_farBump_mul (y + b)).comp_add_right b
    refine this.congr (Eventually.of_forall fun t => ?_)
    show farBump (t + b) * farBump (t + b - (y + b)) = _
    rw [show t + b - (y + b) = t - y by ring]
  have e : (fun t => (farBump (t - b) - farBump (t + b)) * farBump (t - y)) =
      fun t => farBump (t - b) * farBump (t - y) - farBump (t + b) * farBump (t - y) := by
    funext t; ring
  rw [e, integral_sub i1 i2]
  have j1 : ∫ t, farBump (t - b) * farBump (t - y) =
      ∫ s, farBump s * farBump (s - (y - b)) := by
    rw [← integral_sub_right_eq_self (fun s => farBump s * farBump (s - (y - b))) b]
    congr 1; funext t; congr 2; ring
  have j2 : ∫ t, farBump (t + b) * farBump (t - y) =
      ∫ s, farBump s * farBump (s - (y + b)) := by
    rw [← integral_add_right_eq_self (fun s => farBump s * farBump (s - (y + b))) b]
    congr 1; funext t; congr 2; ring
  rw [j1, j2]

/-- **Cross-Sum of an Odd Far Bump**:
for any `lam : ℕ → ℝ` and any `b, a : ℝ`,
`farCrossSum lam (oddFarBump b) a = farSum lam ((a + b) / 2) - farSum lam ((a - b) / 2)`. -/
theorem farCrossSum_oddFarBump (lam : ℕ → ℝ) (b a : ℝ) :
    farCrossSum lam (oddFarBump b) a =
      farSum lam ((a + b) / 2) - farSum lam ((a - b) / 2) := by
  unfold farCrossSum farSum
  have hs1 := summable_farSum_term lam ((a + b) / 2)
  have hs2 := summable_farSum_term lam ((a - b) / 2)
  rw [← hs1.tsum_sub hs2]
  refine tsum_congr fun n => ?_
  rw [farCrossKernel_oddFarBump b (Real.log n - a),
    show Real.log n - a - b = Real.log n - 2 * ((a + b) / 2) by ring,
    show Real.log n - a + b = Real.log n - 2 * ((a - b) / 2) by ring]
  ring

/-- The pole-free coefficient `s_a = P / ((e^{-a/2} - e^{a/2}) J)` for an odd far bump. -/
def oddFarCoeff (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  (∫ x, g x * Real.exp (-x / 2)) / ((Real.exp (-a / 2) - Real.exp (a / 2)) * farJ)

theorem exp_neg_half_sub_exp_half_ne_zero {a : ℝ} (ha : a ≠ 0) :
    Real.exp (-a / 2) - Real.exp (a / 2) ≠ 0 := by
  intro h
  have h1 : Real.exp (-a / 2) = Real.exp (a / 2) := sub_eq_zero.mp h
  have h2 : -a / 2 = a / 2 := Real.exp_injective h1
  exact ha (by linarith)

theorem integral_sub_oddFarCoeff_mul_exp {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {a : ℝ} (ha : a ≠ 0) :
    ∫ x, (g x - oddFarCoeff g a * oddFarBump a x) * Real.exp (-x / 2) = 0 := by
  have hJ := farJ_pos.ne'
  have hE := exp_neg_half_sub_exp_half_ne_zero ha
  have hig : Integrable fun x => g x * Real.exp (-x / 2) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have hio : Integrable fun x => oddFarBump a x * Real.exp (-x / 2) :=
    ((continuous_oddFarBump a).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_oddFarBump a).mul_right
  have e : (fun x => (g x - oddFarCoeff g a * oddFarBump a x) * Real.exp (-x / 2)) =
      fun x => g x * Real.exp (-x / 2) - oddFarCoeff g a * (oddFarBump a x * Real.exp (-x / 2)) := by
    funext x; ring
  rw [e, integral_sub hig (hio.const_mul _), integral_const_mul, integral_oddFarBump_mul_exp]
  unfold oddFarCoeff
  rw [div_mul_cancel₀ _ (mul_ne_zero hE hJ), sub_self]

/-- **Pole-Free Coefficient of an Odd Far Bump**:
`oddFarCoeff (oddFarBump b) a = (Real.exp (-b / 2) - Real.exp (b / 2)) / (Real.exp (-a / 2) - Real.exp (a / 2))`. -/
theorem oddFarCoeff_oddFarBump (b a : ℝ) :
    oddFarCoeff (oddFarBump b) a =
      (Real.exp (-b / 2) - Real.exp (b / 2)) / (Real.exp (-a / 2) - Real.exp (a / 2)) := by
  unfold oddFarCoeff
  rw [integral_oddFarBump_mul_exp]
  have hJ : farJ ≠ 0 := farJ_pos.ne'
  exact mul_div_mul_right _ _ hJ

/-- **Hyperbolic Sine Form of `oddFarCoeff (oddFarBump b) a`**:
`oddFarCoeff (oddFarBump b) a = Real.sinh (b / 2) / Real.sinh (a / 2)`. -/
theorem oddFarCoeff_oddFarBump_eq_sinh_div_sinh (b a : ℝ) :
    oddFarCoeff (oddFarBump b) a = Real.sinh (b / 2) / Real.sinh (a / 2) := by
  have hb : Real.exp (-b / 2) - Real.exp (b / 2) = -2 * Real.sinh (b / 2) := by
    rw [Real.sinh_eq, show -(b / 2) = -b / 2 by ring]; ring
  have ha : Real.exp (-a / 2) - Real.exp (a / 2) = -2 * Real.sinh (a / 2) := by
    rw [Real.sinh_eq, show -(a / 2) = -a / 2 by ring]; ring
  rw [oddFarCoeff_oddFarBump, hb, ha]
  exact mul_div_mul_left _ _ (by norm_num)

theorem oddFarCoeff_oddFarBump_nonneg {b a : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ a) :
    0 ≤ oddFarCoeff (oddFarBump b) a := by
  rw [oddFarCoeff_oddFarBump_eq_sinh_div_sinh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr (by linarith))
    (Real.sinh_nonneg_iff.mpr (by linarith))

theorem oddFarCoeff_oddFarBump_le_one {b a : ℝ} (hba : b ≤ a) (ha : 0 < a) :
    oddFarCoeff (oddFarBump b) a ≤ 1 := by
  have hsinh : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by linarith)
  rw [oddFarCoeff_oddFarBump_eq_sinh_div_sinh, div_le_one hsinh]
  exact Real.sinh_le_sinh.mpr (by linarith)

/-! ## Section 3: Uniform Odd Two-Bump Archimedean Bound and Midpoint Concavity Law on `WeilPositiveOddPolar` -/

theorem integral_oddFarBump_arch_le (a : ℝ) :
    ∫ r : ℝ, ‖paperFT (fun u => ((oddFarBump a u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r| ≤
      farBumpArchMass :=
  integral_normSq_mul_abs_gammaBracket_le 2 (norm_paperFT_oddFarBump_le a)

theorem abs_farArch_oddFarBump_le (a : ℝ) :
    |farArch (oddFarBump a)| ≤ 1 / (2 * Real.pi) * farBumpArchMass :=
  (abs_farArch_le (oddFarBump a)).trans
    (mul_le_mul_of_nonneg_left (integral_oddFarBump_arch_le a) (by positivity))

/-- **Uniform Archimedean Bound for the Sum of Two Odd Far Bumps**:
`|farArch (oddFarBump b + oddFarBump a)| ≤ (2 / π) * farBumpArchMass` for all `0 ≤ b ≤ a`. -/
theorem abs_farArch_oddFarBump_add_oddFarBump_le {b a : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    |farArch (fun x => oddFarBump b x + oddFarBump a x)| ≤
      2 / Real.pi * farBumpArchMass := by
  have hbs : ∀ x, b + 1 < |x| → oddFarBump b x = 0 := fun x hx => oddFarBump_eq_zero hb hx
  have ha0 : 0 ≤ a := hb.trans hba
  have has : ∀ x, a + 1 < |x| → oddFarBump a x = 0 := fun x hx => oddFarBump_eq_zero ha0 hx
  have hbs' : ∀ x, a + 1 < |x| → oddFarBump b x = 0 := fun x hx => hbs x (by linarith)
  have hs : ∀ x, a + 1 < |x| → oddFarBump b x + oddFarBump a x = 0 := fun x hx => by
    rw [hbs' x hx, has x hx, add_zero]
  have hbc := hasCompactSupport_oddFarBump b
  have hac := hasCompactSupport_oddFarBump a
  have hIb := integrable_normSq_paperFT_mul_abs_gammaBracket (contDiff_oddFarBump b) hbs'
  have hIa := integrable_normSq_paperFT_mul_abs_gammaBracket (contDiff_oddFarBump a) has
  have hIs := integrable_normSq_paperFT_mul_abs_gammaBracket
    ((contDiff_oddFarBump b).add (contDiff_oddFarBump a)) hs
  have hpt : ∀ r : ℝ, ‖paperFT (fun u => ((oddFarBump b u + oddFarBump a u : ℝ) : ℂ)) r‖ ^ 2 *
      |EF.gammaBracket r| ≤
      2 * (‖paperFT (fun u => ((oddFarBump b u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) +
        2 * (‖paperFT (fun u => ((oddFarBump a u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) := by
    intro r
    have e : paperFT (fun u => ((oddFarBump b u + oddFarBump a u : ℝ) : ℂ)) r =
        paperFT (fun u => ((oddFarBump b u : ℝ) : ℂ)) r +
          paperFT (fun u => ((oddFarBump a u : ℝ) : ℂ)) r := by
      have := paperFT_ofReal_add_smul (continuous_oddFarBump b) hbc (continuous_oddFarBump a)
        hac 1 1 r
      rw [show (fun u => ((oddFarBump b u + oddFarBump a u : ℝ) : ℂ)) =
        fun u => ((1 * oddFarBump b u + 1 * oddFarBump a u : ℝ) : ℂ) by
          funext u; push_cast; ring, this]
      push_cast; ring
    rw [e]
    have hsq : ‖paperFT (fun u => ((oddFarBump b u : ℝ) : ℂ)) r +
        paperFT (fun u => ((oddFarBump a u : ℝ) : ℂ)) r‖ ^ 2 ≤
        2 * ‖paperFT (fun u => ((oddFarBump b u : ℝ) : ℂ)) r‖ ^ 2 +
          2 * ‖paperFT (fun u => ((oddFarBump a u : ℝ) : ℂ)) r‖ ^ 2 := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _)
        (norm_add_le (paperFT (fun u => ((oddFarBump b u : ℝ) : ℂ)) r)
          (paperFT (fun u => ((oddFarBump a u : ℝ) : ℂ)) r)) 2
      nlinarith [sq_nonneg (‖paperFT (fun u => ((oddFarBump b u : ℝ) : ℂ)) r‖ -
        ‖paperFT (fun u => ((oddFarBump a u : ℝ) : ℂ)) r‖)]
    have hG := abs_nonneg (EF.gammaBracket r)
    nlinarith
  have hint : ∫ r : ℝ, ‖paperFT (fun u => ((oddFarBump b u + oddFarBump a u : ℝ) : ℂ)) r‖ ^ 2 *
      |EF.gammaBracket r| ≤ 4 * farBumpArchMass := by
    calc ∫ r : ℝ, ‖paperFT (fun u => ((oddFarBump b u + oddFarBump a u : ℝ) : ℂ)) r‖ ^ 2 *
          |EF.gammaBracket r|
        ≤ ∫ r : ℝ, (2 * (‖paperFT (fun u => ((oddFarBump b u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) +
          2 * (‖paperFT (fun u => ((oddFarBump a u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|)) :=
          integral_mono hIs ((hIb.const_mul 2).add (hIa.const_mul 2)) hpt
      _ = 2 * (∫ r : ℝ, ‖paperFT (fun u => ((oddFarBump b u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) +
          2 * ∫ r : ℝ, ‖paperFT (fun u => ((oddFarBump a u : ℝ) : ℂ)) r‖ ^ 2 *
            |EF.gammaBracket r| := by
          rw [integral_add (hIb.const_mul 2) (hIa.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 4 * farBumpArchMass := by
          linarith [integral_oddFarBump_arch_le b, integral_oddFarBump_arch_le a]
  calc |farArch (fun x => oddFarBump b x + oddFarBump a x)|
      ≤ 1 / (2 * Real.pi) * (4 * farBumpArchMass) :=
        (abs_farArch_le _).trans (mul_le_mul_of_nonneg_left hint (by positivity))
    _ = 2 / Real.pi * farBumpArchMass := by ring

/-- **Uniform Archimedean Bound for Two-Bump Odd Linear Combinations**:
for all `0 ≤ b ≤ a` and `0 ≤ s ≤ 1`,
`farArch (fun x => oddFarBump b x - s * oddFarBump a x) ≤ (4 / π) * farBumpArchMass`. -/
theorem farArch_oddFarBump_sub_smul_le {b a s : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    farArch (fun x => oddFarBump b x - s * oddFarBump a x) ≤
      4 / Real.pi * farBumpArchMass := by
  have ha0 : 0 ≤ a := hb.trans hba
  have hbs : ∀ x, a + 1 < |x| → oddFarBump b x = 0 := fun x hx =>
    oddFarBump_eq_zero hb (by linarith)
  have has : ∀ x, a + 1 < |x| → oddFarBump a x = 0 := fun x hx =>
    oddFarBump_eq_zero ha0 hx
  rw [farArch_sub_smul (contDiff_oddFarBump b) (contDiff_oddFarBump a) hbs has s]
  have hAb := (le_abs_self _).trans (abs_farArch_oddFarBump_le b)
  have hAa := (le_abs_self _).trans (abs_farArch_oddFarBump_le a)
  have hAs := (neg_le_abs _).trans (abs_farArch_oddFarBump_add_oddFarBump_le hb hba)
  have hM0 : 0 ≤ 1 / (2 * Real.pi) * farBumpArchMass :=
    (abs_nonneg _).trans (abs_farArch_oddFarBump_le 0)
  have h1 : (1 + s) * farArch (oddFarBump b) ≤ 2 * (1 / (2 * Real.pi) * farBumpArchMass) := by
    calc (1 + s) * farArch (oddFarBump b)
        ≤ (1 + s) * (1 / (2 * Real.pi) * farBumpArchMass) :=
          mul_le_mul_of_nonneg_left hAb (by linarith)
      _ ≤ 2 * (1 / (2 * Real.pi) * farBumpArchMass) :=
          mul_le_mul_of_nonneg_right (by linarith) hM0
  have h2 : -s * farArch (fun x => oddFarBump b x + oddFarBump a x) ≤
      2 / Real.pi * farBumpArchMass := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hMpos : 0 ≤ farBumpArchMass := nonneg_of_mul_nonneg_right hM0 (by positivity)
    calc -s * farArch (fun x => oddFarBump b x + oddFarBump a x)
        = s * (-farArch (fun x => oddFarBump b x + oddFarBump a x)) := by ring
      _ ≤ s * (2 / Real.pi * farBumpArchMass) :=
          mul_le_mul_of_nonneg_left hAs hs0
      _ ≤ 1 * (2 / Real.pi * farBumpArchMass) :=
          mul_le_mul_of_nonneg_right hs1 (by positivity)
      _ = 2 / Real.pi * farBumpArchMass := one_mul _
  have h3 : (s + s ^ 2) * farArch (oddFarBump a) ≤
      2 * (1 / (2 * Real.pi) * farBumpArchMass) := by
    have hs2 : s + s ^ 2 ≤ 2 := by nlinarith
    calc (s + s ^ 2) * farArch (oddFarBump a)
        ≤ (s + s ^ 2) * (1 / (2 * Real.pi) * farBumpArchMass) :=
          mul_le_mul_of_nonneg_left hAa (by positivity)
      _ ≤ 2 * (1 / (2 * Real.pi) * farBumpArchMass) :=
          mul_le_mul_of_nonneg_right hs2 hM0
  have he : 2 * (1 / (2 * Real.pi) * farBumpArchMass) + 2 / Real.pi * farBumpArchMass +
      2 * (1 / (2 * Real.pi) * farBumpArchMass) = 4 / Real.pi * farBumpArchMass := by ring
  linarith

/-- **Uniform Odd Two-Bump Midpoint Concavity Inequality on `WeilPositiveOddPolar`**:
for every `lam` satisfying `WeilPositiveOddPolar lam` and all `0 ≤ b` and `b + 2 ≤ a`,
with `s = oddFarCoeff (oddFarBump b) a = sinh(b/2) / sinh(a/2)`,
`-2 * farSum lam b - 2 * s^2 * farSum lam a + 4 * s * (farSum lam ((a + b) / 2) - farSum lam ((a - b) / 2)) ≤ (4 / π) * farBumpArchMass`. -/
theorem two_bump_farSum_midpoint_le_of_weilPositiveOddPolar {lam : ℕ → ℝ}
    (hpfo : WeilPositiveOddPolar lam) {b a : ℝ} (hb : 0 ≤ b) (hba : b + 2 ≤ a) :
    -2 * farSum lam b - 2 * oddFarCoeff (oddFarBump b) a ^ 2 * farSum lam a +
      4 * oddFarCoeff (oddFarBump b) a *
        (farSum lam ((a + b) / 2) - farSum lam ((a - b) / 2)) ≤
      4 / Real.pi * farBumpArchMass := by
  have ha0 : 0 ≤ a := by linarith
  have hapos : 0 < a := by linarith
  have hba' : b ≤ a := by linarith
  set s := oddFarCoeff (oddFarBump b) a with hs
  have hs0 : 0 ≤ s := oddFarCoeff_oddFarBump_nonneg hb ha0
  have hs1 : s ≤ 1 := oddFarCoeff_oddFarBump_le_one hba' hapos
  set H : ℝ → ℝ := fun x => oddFarBump b x - s * oddFarBump a x with hH
  have hHd : ContDiff ℝ 2 H :=
    (contDiff_oddFarBump b).sub (contDiff_const.mul (contDiff_oddFarBump a))
  have hbs : ∀ x, b + 1 < |x| → oddFarBump b x = 0 := fun x hx => oddFarBump_eq_zero hb hx
  have has : ∀ x, a + 1 < |x| → oddFarBump a x = 0 := fun x hx => oddFarBump_eq_zero ha0 hx
  have hHs : ∀ x, a + 1 < |x| → H x = 0 := fun x hx => by
    simp only [hH, hbs x (by linarith), has x hx, mul_zero, sub_zero]
  have hHc := hasCompactSupport_of_abs_gt_eq_zero hHs
  have hHo : ∀ x, H (-x) = -H x := fun x => by simp only [hH, oddFarBump_neg]; ring
  have hP0 : ∫ u, H u * Real.exp (-u / 2) = 0 :=
    integral_sub_oddFarCoeff_mul_exp (continuous_oddFarBump b) (hasCompactSupport_oddFarBump b)
      hapos.ne'
  have hpos := hpfo (fun u => (H u : ℂ)) (contDiff_ofReal_comp hHd)
    (hHc.comp_left Complex.ofReal_zero)
    (fun x => by rw [hHo x, Complex.ofReal_neg])
    (by rw [paperFT_ofRealFun_I_div_two, hP0, Complex.ofReal_zero])
  rw [re_weilFullFunctional_ofReal_eq lam hHd.continuous hHc,
    re_weilPoleTerm_ofReal_odd hHd.continuous hHc hHo, hP0] at hpos
  have hH' : H = fun u => oddFarBump b u + -s * oddFarBump a u := by
    funext u; simp only [hH]; ring
  have hatoms : atomPairing lam (crossCorr H H) =
      -2 * farSum lam b + 4 * s * (farSum lam ((a + b) / 2) - farSum lam ((a - b) / 2)) -
        2 * s ^ 2 * farSum lam a := by
    rw [hH', atomPairing_add_smul_expand lam (continuous_oddFarBump b)
      (hasCompactSupport_oddFarBump b) (continuous_oddFarBump a)
      (hasCompactSupport_oddFarBump a) (-s),
      atomPairing_oddFarBump lam hb,
      atomPairing_crossCorr_oddFarBump lam (continuous_oddFarBump b)
        (hasCompactSupport_oddFarBump b) (oddFarBump_neg b) (R := b + 1) (by linarith) hbs
        (by linarith),
      farCrossSum_oddFarBump lam b a,
      atomPairing_oddFarBump lam ha0]
    ring
  have harch := farArch_oddFarBump_sub_smul_le hb hba' hs0 hs1
  rw [← hH] at harch
  linarith

/-- **Hyperbolic Sine Normalized Odd Two-Bump Midpoint Inequality on `WeilPositiveOddPolar`**:
rewrites `two_bump_farSum_midpoint_le_of_weilPositiveOddPolar` explicitly in terms of
`Real.sinh (b / 2) / Real.sinh (a / 2)`. -/
theorem two_bump_sinh_normalized_midpoint_le_of_weilPositiveOddPolar {lam : ℕ → ℝ}
    (hpfo : WeilPositiveOddPolar lam) {b a : ℝ} (hb : 0 ≤ b) (hba : b + 2 ≤ a) :
    -2 * farSum lam b - 2 * (Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2 * farSum lam a +
      4 * (Real.sinh (b / 2) / Real.sinh (a / 2)) *
        (farSum lam ((a + b) / 2) - farSum lam ((a - b) / 2)) ≤
      4 / Real.pi * farBumpArchMass := by
  rw [← oddFarCoeff_oddFarBump_eq_sinh_div_sinh]
  exact two_bump_farSum_midpoint_le_of_weilPositiveOddPolar hpfo hb hba

/-! ## Section 4: The Three Joint Parity Elimination Laws -/

/-- **Joint Parity Elimination Law 1 (Lower-Endpoint Elimination, Weights `(1, 1)`)**:
adding the even and odd two-bump pole-free inequalities cancels `farSum lam b` identically:
`2 * (c^2 - s^2) * farSum lam a - 4 * (c - s) * farSum lam ((a + b) / 2) - 4 * (c + s) * farSum lam ((a - b) / 2) ≤ (8 / π) * farBumpArchMass`. -/
theorem joint_two_bump_eliminate_lower_endpoint {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) (hpfo : WeilPositiveOddPolar lam)
    {b a : ℝ} (hb : 0 ≤ b) (hba : b + 2 ≤ a) :
    let c := Real.cosh (b / 2) / Real.cosh (a / 2)
    let s := Real.sinh (b / 2) / Real.sinh (a / 2)
    2 * (c ^ 2 - s ^ 2) * farSum lam a -
      4 * (c - s) * farSum lam ((a + b) / 2) -
      4 * (c + s) * farSum lam ((a - b) / 2) ≤
      8 / Real.pi * farBumpArchMass := by
  dsimp only
  have he := two_bump_cosh_normalized_midpoint_le_of_weilPositiveEvenPolar hpfe hb hba
  have ho := two_bump_sinh_normalized_midpoint_le_of_weilPositiveOddPolar hpfo hb hba
  have hsum := add_le_add he ho
  calc 2 * ((Real.cosh (b / 2) / Real.cosh (a / 2)) ^ 2 -
          (Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2) * farSum lam a -
        4 * (Real.cosh (b / 2) / Real.cosh (a / 2) -
          Real.sinh (b / 2) / Real.sinh (a / 2)) * farSum lam ((a + b) / 2) -
        4 * (Real.cosh (b / 2) / Real.cosh (a / 2) +
          Real.sinh (b / 2) / Real.sinh (a / 2)) * farSum lam ((a - b) / 2)
      = (2 * farSum lam b + 2 * (Real.cosh (b / 2) / Real.cosh (a / 2)) ^ 2 * farSum lam a -
          4 * (Real.cosh (b / 2) / Real.cosh (a / 2)) *
            (farSum lam ((a + b) / 2) + farSum lam ((a - b) / 2))) +
        (-2 * farSum lam b - 2 * (Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2 * farSum lam a +
          4 * (Real.sinh (b / 2) / Real.sinh (a / 2)) *
            (farSum lam ((a + b) / 2) - farSum lam ((a - b) / 2))) := by ring
    _ ≤ 4 / Real.pi * farBumpArchMass + 4 / Real.pi * farBumpArchMass := hsum
    _ = 8 / Real.pi * farBumpArchMass := by ring

/-- **Joint Parity Elimination Law 2 (Midpoint Elimination, Weights `(s, c)`)**:
combining the even and odd two-bump pole-free inequalities with nonnegative weights `s` and `c`
cancels the midpoint term `farSum lam ((a + b) / 2)` identically:
`2 * c * s * (c - s) * farSum lam a - 2 * (c - s) * farSum lam b - 8 * c * s * farSum lam ((a - b) / 2) ≤ (c + s) * (4 / π * farBumpArchMass)`. -/
theorem joint_two_bump_eliminate_midpoint {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) (hpfo : WeilPositiveOddPolar lam)
    {b a : ℝ} (hb : 0 ≤ b) (hba : b + 2 ≤ a) :
    let c := Real.cosh (b / 2) / Real.cosh (a / 2)
    let s := Real.sinh (b / 2) / Real.sinh (a / 2)
    2 * c * s * (c - s) * farSum lam a -
      2 * (c - s) * farSum lam b -
      8 * c * s * farSum lam ((a - b) / 2) ≤
      (c + s) * (4 / Real.pi * farBumpArchMass) := by
  dsimp only
  set c := Real.cosh (b / 2) / Real.cosh (a / 2) with hc_def
  set s := Real.sinh (b / 2) / Real.sinh (a / 2) with hs_def
  have hc0 : 0 ≤ c := by
    rw [hc_def, ← farCoeff_evenFarBump_eq_cosh_div_cosh]; exact farCoeff_evenFarBump_nonneg b a
  have hs0 : 0 ≤ s := by
    rw [hs_def, ← oddFarCoeff_oddFarBump_eq_sinh_div_sinh]
    exact oddFarCoeff_oddFarBump_nonneg hb (by linarith)
  have he := mul_le_mul_of_nonneg_left
    (two_bump_cosh_normalized_midpoint_le_of_weilPositiveEvenPolar hpfe hb hba) hs0
  have ho := mul_le_mul_of_nonneg_left
    (two_bump_sinh_normalized_midpoint_le_of_weilPositiveOddPolar hpfo hb hba) hc0
  have hsum := add_le_add he ho
  calc 2 * c * s * (c - s) * farSum lam a -
        2 * (c - s) * farSum lam b -
        8 * c * s * farSum lam ((a - b) / 2)
      = s * (2 * farSum lam b + 2 * c ^ 2 * farSum lam a -
          4 * c * (farSum lam ((a + b) / 2) + farSum lam ((a - b) / 2))) +
        c * (-2 * farSum lam b - 2 * s ^ 2 * farSum lam a +
          4 * s * (farSum lam ((a + b) / 2) - farSum lam ((a - b) / 2))) := by ring
    _ ≤ s * (4 / Real.pi * farBumpArchMass) + c * (4 / Real.pi * farBumpArchMass) := hsum
    _ = (c + s) * (4 / Real.pi * farBumpArchMass) := by ring

/-- **Joint Parity Elimination Law 3 (Upper-Endpoint Elimination, Weights `(s^2, c^2)`)**:
combining the even and odd two-bump pole-free inequalities with nonnegative weights `s^2` and `c^2`
cancels the upper-endpoint term `farSum lam a` identically:
`4 * c * s * (c - s) * farSum lam ((a + b) / 2) - 2 * (c^2 - s^2) * farSum lam b - 4 * c * s * (c + s) * farSum lam ((a - b) / 2) ≤ (c^2 + s^2) * (4 / π * farBumpArchMass)`. -/
theorem joint_two_bump_eliminate_upper_endpoint {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) (hpfo : WeilPositiveOddPolar lam)
    {b a : ℝ} (hb : 0 ≤ b) (hba : b + 2 ≤ a) :
    let c := Real.cosh (b / 2) / Real.cosh (a / 2)
    let s := Real.sinh (b / 2) / Real.sinh (a / 2)
    4 * c * s * (c - s) * farSum lam ((a + b) / 2) -
      2 * (c ^ 2 - s ^ 2) * farSum lam b -
      4 * c * s * (c + s) * farSum lam ((a - b) / 2) ≤
      (c ^ 2 + s ^ 2) * (4 / Real.pi * farBumpArchMass) := by
  dsimp only
  set c := Real.cosh (b / 2) / Real.cosh (a / 2)
  set s := Real.sinh (b / 2) / Real.sinh (a / 2)
  have he := mul_le_mul_of_nonneg_left
    (two_bump_cosh_normalized_midpoint_le_of_weilPositiveEvenPolar hpfe hb hba) (sq_nonneg s)
  have ho := mul_le_mul_of_nonneg_left
    (two_bump_sinh_normalized_midpoint_le_of_weilPositiveOddPolar hpfo hb hba) (sq_nonneg c)
  have hsum := add_le_add he ho
  calc 4 * c * s * (c - s) * farSum lam ((a + b) / 2) -
        2 * (c ^ 2 - s ^ 2) * farSum lam b -
        4 * c * s * (c + s) * farSum lam ((a - b) / 2)
      = s ^ 2 * (2 * farSum lam b + 2 * c ^ 2 * farSum lam a -
          4 * c * (farSum lam ((a + b) / 2) + farSum lam ((a - b) / 2))) +
        c ^ 2 * (-2 * farSum lam b - 2 * s ^ 2 * farSum lam a +
          4 * s * (farSum lam ((a + b) / 2) - farSum lam ((a - b) / 2))) := by ring
    _ ≤ s ^ 2 * (4 / Real.pi * farBumpArchMass) + c ^ 2 * (4 / Real.pi * farBumpArchMass) := hsum
    _ = (c ^ 2 + s ^ 2) * (4 / Real.pi * farBumpArchMass) := by ring

end RHTower.CHMDStage9

end
