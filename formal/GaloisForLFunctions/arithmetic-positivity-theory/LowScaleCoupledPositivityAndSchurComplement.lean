import GaloisForLFunctions.«arithmetic-positivity-theory».MultiScaleLowModeAndGridTentSchurBridge
import GaloisForLFunctions.«arithmetic-positivity-theory».ExplicitBlockThresholdsOfTheCriticalFamily

/-!
# Low-Scale Archimedean Regularity, Bilinear Schur Complement, and Positivity of the Coupled Critical Form

This module resolves Open Problem 7.1 (*Low scales and the coupled form*) of the Arithmetic
Positivity Theory programme by eliminating the $\log M$ growth of the low-mode archimedean penalty,
establishing the exact bilinear Schur-complement decomposition of the complete form across low and
high scales, and proving unconditional positive definiteness of coupled low–high critical sources
for unrestricted low-mode coefficients across all five realizations of the form and their
grid-tent and smooth-detector transfers:

1. **Global Clock-Lipschitz Jump Bound and Scale-Free Low-Mode Archimedean Ceiling
   (`sq_criticalTruncatedSource_sub_shift_le`, `sourceAutocorrelation_criticalTruncatedSource_jump_le_sqrt`,
   `biScaleLevyEnergy_criticalTruncatedTest_le`, `highBand_plancherel_criticalTruncatedSource_le`):**
   Writing the doubly collared critical source in clock coordinates as
   $g^V(y) = e^{y/2} F_V(e^{-y})$ with $F_V(v) = \chi(v/V)\sigma(v-1)B_{S,b}(v)$, the clock profile
   $F_V$ is globally bounded and globally Lipschitz on $\mathbb{R}$ with constants independent of
   $V \ge 1$. Interpolating the clock-Lipschitz increment bound
   $|g^V(u) - g^V(u+x)| \le K e^{-u/2} x$ ($u \le 0$) with the envelope bound
   $|g^V(u) - g^V(u+x)| \le K e^{u/2}$ via $|Δ|^4 = |Δ| \cdot |Δ|^3 \le (K^2 \sqrt{x} e^{u/2})^2$
   yields the global pointwise envelope
   $$(g^V(u) - g^V(u+x))^2 \le K(S,b)^2 \sqrt{x} \, e^{u/2} \qquad (u \le 0, \; x \in [0, 1])$$
   without interval splitting. Integrating over $u \le 0$ bounds the autocorrelation jump by
   $a_{g^V}(0) - a_{g^V}(x) \le K(S,b)^2 \sqrt{x}$ for $x \in [0, 1]$ and the total archimedean
   Lévy energy on any low window `ScaleWindow S_low 1 L_low` by
   $$\mathrm{biScaleLevyEnergy}(g^V_{\mathrm{low}}) \le C_{\mathrm{low,arch}} L_{\mathrm{low}}^3 \sum_{n \in S_{\mathrm{low}}} b_n^2,$$
   uniformly in $V \ge 1$ and completely independent of any high scale $M$. By the spectral jump
   identity, the high-frequency Plancherel tail of $g^V_{\mathrm{low}}$ above $R$ decays at rate
   $O(L_{\mathrm{low}}^3 R^{-1/2}) E_{\mathrm{low}} \to 0$.

2. **Scale-Free Low-Penalty Two-Band Archimedean Law and Bilinear Lévy Decomposition
   (`ofReal_le_criticalTruncatedLevyEnergy_of_lowWindow_high_scaleFree`,
   `biScaleLevyEnergy_union_ge_of_gamma`, `biScaleLevyEnergy_union_schur_ge`):**
   Splitting the autocorrelation jump spectrally via
   $\Delta_{g_{\mathrm{low}} + g_{\mathrm{high}}}(x) \ge \frac{1}{2}\Delta_{g_{\mathrm{high}}}(x) - \Delta_{g_{\mathrm{low}}}(x)$
   replaces the growing low-mode archimedean penalty $s_T(\log M - c_T) K_{\mathrm{low}} E_{\mathrm{low}}$
   of `ofReal_le_criticalTruncatedLevyEnergy_of_low_high_split` by the scale-free low-mode ceiling
   $\mathrm{criticalLowWindowLevyConstant}\ L_{\mathrm{low}} \cdot E_{\mathrm{low}}$, which is
   independent of $M$ and $V \ge 1$. Moreover, applying the shift-adapted Young weight
   $\beta(x) = \gamma x^{1/4}$ on $(0, 1]$ and $\beta(x) = \gamma$ on $(1, \infty)$ preserves
   both diagonal Lévy energies with unit coefficient:
   $$\mathrm{biScaleLevyEnergy}(g^V_{\mathrm{low}} + g^V_{\mathrm{high}}) \ge
     \mathrm{biScaleLevyEnergy}(g^V_{\mathrm{low}}) + \mathrm{biScaleLevyEnergy}(g^V_{\mathrm{high}})
     - 2 C_{\mathrm{cross,arch}}(L_{\mathrm{low}}) \sqrt{E_{\mathrm{low}} E_{\mathrm{high}}}.$$

3. **Exact Bilinear Schur-Complement Theorem and Scale-Free Low-Penalty Complete Energy Bound
   (`compactFullWeilEnergy_criticalTruncatedTest_ge_of_lowWindow_lacunary_scaleFree`,
   `compactFullWeilEnergy_criticalTruncatedTest_schur_decomposition`,
   `compactFullWeilEnergy_pos_of_lowMode_certificate_and_schur_complement`):**
   Combining all four channels gives both:
   - the unconditional scale-free low-penalty lower bound on `S_low ∪ ⋃_{i < J} S_i` where the
     total low-mode penalty $\mathrm{criticalLowWindowTotalPenalty}(L_{\mathrm{low}}) E_{\mathrm{low}}$
     is completely independent of the high scale $M_0$, the block count $J$, and the truncation $V$;
   - the exact bilinear Schur-complement inequality
     $$\mathrm{compactFullWeilEnergy}(g^V_{\mathrm{low}} + g^V_{\mathrm{high}}) \ge
       \mathrm{compactFullWeilEnergy}(g^V_{\mathrm{low}}) + \mathrm{compactFullWeilEnergy}(g^V_{\mathrm{high}})
       - 2 C_{\mathrm{Schur}}(L_{\mathrm{low}}) \sqrt{E_{\mathrm{low}} E_{\mathrm{high}}},$$
     so any low-mode subspace with certificate $\mathrm{compactFullWeilEnergy}(g^V_{\mathrm{low}}) \ge \mu_{\mathrm{low}} E_{\mathrm{low}}$
     ($\mu_{\mathrm{low}} > 0$) has a controlled Schur complement against every high block or
     lacunary block family once $\mu_{\mathrm{high}}(M_0) \ge 4 C_{\mathrm{Schur}}(L_{\mathrm{low}})^2 / \mu_{\mathrm{low}}$,
     yielding strict positivity for all unrestricted nonzero $(b_{\mathrm{low}}, b_{\mathrm{high}})$.

4. **Unconditional Positivity of Coupled Low–High Critical Sources for Unrestricted Low-Mode Coefficients
   (`coupledLowHighLacunaryThreshold`, `all_five_forms_pos_of_lowWindow_lacunary_dominance`,
   `compactFullWeilEnergy_coupled_pos_for_unrestricted_low_modes`,
   `exists_coupled_gridTentPattern_and_smoothDetector_pos_for_unrestricted_low_modes`):**
   Because the low-mode penalty no longer grows with $\log M_0$, raising $M_0$ above the explicit
   closed-form threshold `coupledLowHighLacunaryThreshold L_low (γ⁻¹ ^ 2)` certifies strict
   positivity of every coupled critical source
   $$g^V_{\mathrm{coupled}}(b_{\mathrm{low}}) = \sum_{n \in S_{\mathrm{low}}} b_{\mathrm{low}}(n) \bigl(g^V_n + \gamma_n g^V_{\phi(n)}\bigr)$$
   (for every injection $\phi : S_{\mathrm{low}} \hookrightarrow S_{\mathrm{high}}$ and every coupling
   $|\gamma_n| \ge \gamma > 0$, including unit 1-to-1 coupling $\gamma_n = 1$) for **every
   unrestricted nonzero low-mode coefficient vector $b_{\mathrm{low}}$**, simultaneously across all
   five realizations of the complete form and their single-scale `gridTentPattern` and
   `smoothGridTentDetector` transfers.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators CompactlySupported ComplexConjugate ENNReal
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ## Section 1: Global Clock-Lipschitz Jump Bound and Scale-Free Low-Mode Archimedean Ceiling -/

/-- The clock profile `F_V(v) = χ(v/V) σ(v - 1) B_{S,b}(v)` of `criticalTruncatedSource V S b`,
so that `criticalTruncatedSource V S b y = e^{y/2} F_V(e^{-y})` for all `y ∈ ℝ`. -/
def criticalTruncatedClockProfile (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) : ℝ :=
  criticalUpperCutoff (v / V) * (Real.smoothTransition (v - 1) * realPhaseCombination S b v)

theorem criticalTruncatedSource_eq_exp_half_mul_clockProfile (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ)
    (y : ℝ) :
    criticalTruncatedSource V S b y =
      Real.exp (y / 2) * criticalTruncatedClockProfile V S b (Real.exp (-y)) := by
  rw [criticalTruncatedSource_eq]
  unfold criticalTruncatedClockProfile
  ring

theorem criticalTruncatedClockProfile_eq_zero_of_le_one (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ)
    {v : ℝ} (hv : v ≤ 1) :
    criticalTruncatedClockProfile V S b v = 0 := by
  unfold criticalTruncatedClockProfile
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul, mul_zero]

theorem abs_criticalTruncatedClockProfile_le (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    |criticalTruncatedClockProfile V S b v| ≤ 2 * ∑ n ∈ S, |b n| := by
  unfold criticalTruncatedClockProfile
  rw [abs_mul, abs_mul]
  have h1 : |criticalUpperCutoff (v / V)| ≤ 1 := by
    rw [abs_of_nonneg (criticalUpperCutoff_nonneg _)]
    exact criticalUpperCutoff_le_one _
  have h2 : |Real.smoothTransition (v - 1)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have h3 := abs_realPhaseCombination_le_two_mul S b v
  calc |criticalUpperCutoff (v / V)| *
        (|Real.smoothTransition (v - 1)| * |realPhaseCombination S b v|)
      ≤ 1 * (1 * (2 * ∑ n ∈ S, |b n|)) :=
        mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) zero_le_one) (by positivity) zero_le_one
    _ = 2 * ∑ n ∈ S, |b n| := by ring

theorem abs_criticalTruncatedSource_le_exp_half (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (y : ℝ) :
    |criticalTruncatedSource V S b y| ≤ (2 * ∑ n ∈ S, |b n|) * Real.exp (y / 2) := by
  rw [criticalTruncatedSource_eq_exp_half_mul_clockProfile, abs_mul,
    abs_of_pos (Real.exp_pos (y / 2)), mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_criticalTruncatedClockProfile_le V S b _)
    (Real.exp_pos _).le

/-- Global Lipschitz bound for `criticalTruncatedClockProfile V S b` on `ℝ`, uniform in `V ≥ 1`. -/
theorem abs_criticalTruncatedClockProfile_sub_le {V : ℝ} (hV : 1 ≤ V) (S : Finset ℕ) (b : ℕ → ℝ)
    (v v' : ℝ) :
    |criticalTruncatedClockProfile V S b v - criticalTruncatedClockProfile V S b v'| ≤
      (4 * smoothTransitionSlope * (∑ n ∈ S, |b n|) + realPhaseLipschitz S b) * |v - v'| := by
  have hV0 : 0 < V := by linarith
  have hsl := smoothTransitionSlope_nonneg
  have hMB : 0 ≤ 2 * ∑ n ∈ S, |b n| := by
    have := Finset.sum_nonneg fun n (_ : n ∈ S) => abs_nonneg (b n)
    positivity
  have hL1 : |criticalUpperCutoff (v / V) - criticalUpperCutoff (v' / V)| ≤
      smoothTransitionSlope * |v - v'| := by
    unfold criticalUpperCutoff
    rw [show 1 - Real.smoothTransition (v / V - 1) - (1 - Real.smoothTransition (v' / V - 1)) =
        Real.smoothTransition (v' / V - 1) - Real.smoothTransition (v / V - 1) by ring]
    refine (abs_smoothTransition_sub_le _ _).trans ?_
    rw [show v' / V - 1 - (v / V - 1) = -(v - v') / V by ring, abs_div, abs_neg, abs_of_pos hV0]
    have hdiv : |v - v'| / V ≤ |v - v'| := div_le_self (abs_nonneg _) hV
    exact mul_le_mul_of_nonneg_left hdiv hsl
  have hL2 : |Real.smoothTransition (v - 1) - Real.smoothTransition (v' - 1)| ≤
      smoothTransitionSlope * |v - v'| := by
    refine (abs_smoothTransition_sub_le _ _).trans ?_
    rw [show v - 1 - (v' - 1) = v - v' by ring]
  have hL3 := abs_realPhaseCombination_sub_le S b v v'
  have hB1 : |criticalUpperCutoff (v / V)| ≤ 1 := by
    rw [abs_of_nonneg (criticalUpperCutoff_nonneg _)]; exact criticalUpperCutoff_le_one _
  have hB2 (w : ℝ) : |Real.smoothTransition (w - 1)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
  have hB3 (w : ℝ) : |realPhaseCombination S b w| ≤ 2 * ∑ n ∈ S, |b n| :=
    abs_realPhaseCombination_le_two_mul S b w
  have h23 : |Real.smoothTransition (v - 1) * realPhaseCombination S b v -
      Real.smoothTransition (v' - 1) * realPhaseCombination S b v'| ≤
      (realPhaseLipschitz S b + 2 * smoothTransitionSlope * ∑ n ∈ S, |b n|) * |v - v'| := by
    have heq : Real.smoothTransition (v - 1) * realPhaseCombination S b v -
        Real.smoothTransition (v' - 1) * realPhaseCombination S b v' =
        Real.smoothTransition (v - 1) * (realPhaseCombination S b v - realPhaseCombination S b v') +
        realPhaseCombination S b v' * (Real.smoothTransition (v - 1) - Real.smoothTransition (v' - 1)) := by
      ring
    rw [heq]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hA := mul_le_mul (hB2 v) hL3 (abs_nonneg _) zero_le_one
    have hB := mul_le_mul (hB3 v') hL2 (abs_nonneg _) hMB
    linarith
  have hB23 : |Real.smoothTransition (v' - 1) * realPhaseCombination S b v'| ≤
      2 * ∑ n ∈ S, |b n| := by
    rw [abs_mul]
    calc |Real.smoothTransition (v' - 1)| * |realPhaseCombination S b v'|
        ≤ 1 * (2 * ∑ n ∈ S, |b n|) := mul_le_mul (hB2 v') (hB3 v') (abs_nonneg _) zero_le_one
      _ = 2 * ∑ n ∈ S, |b n| := one_mul _
  unfold criticalTruncatedClockProfile
  have heq : criticalUpperCutoff (v / V) * (Real.smoothTransition (v - 1) * realPhaseCombination S b v) -
      criticalUpperCutoff (v' / V) * (Real.smoothTransition (v' - 1) * realPhaseCombination S b v') =
      criticalUpperCutoff (v / V) * (Real.smoothTransition (v - 1) * realPhaseCombination S b v -
        Real.smoothTransition (v' - 1) * realPhaseCombination S b v') +
      (Real.smoothTransition (v' - 1) * realPhaseCombination S b v') *
        (criticalUpperCutoff (v / V) - criticalUpperCutoff (v' / V)) := by
    ring
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have hC := mul_le_mul hB1 h23 (abs_nonneg _) zero_le_one
  have hD := mul_le_mul hB23 hL1 (abs_nonneg _) hMB
  linarith

/-- Unified translation-envelope constant `(4 sup|σ'| + 6) ∑_{n ∈ S} |b_n| + realPhaseLipschitz S b`
controlling both the clock-Lipschitz increment and the exponential envelope of `g^V` uniformly in `V ≥ 1`. -/
def criticalTruncatedJumpEnvelopeConstant (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  (4 * smoothTransitionSlope + 6) * (∑ n ∈ S, |b n|) + realPhaseLipschitz S b

theorem criticalTruncatedJumpEnvelopeConstant_nonneg (S : Finset ℕ) (b : ℕ → ℝ) :
    0 ≤ criticalTruncatedJumpEnvelopeConstant S b := by
  unfold criticalTruncatedJumpEnvelopeConstant
  have h1 := smoothTransitionSlope_nonneg
  have h2 : 0 ≤ ∑ n ∈ S, |b n| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h3 := realPhaseLipschitz_nonneg S b
  positivity

private theorem exp_half_le_two_of_le_one {x : ℝ} (hx : x ≤ 1) : Real.exp (x / 2) ≤ 2 := by
  have h1 : Real.exp (x / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (1 / 2) ^ 2 ≤ (2 : ℝ) ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have h3 : Real.exp (1 / 2) ≤ 2 := by
    nlinarith [Real.exp_pos (1 / 2)]
  exact h1.trans h3

/-- Envelope bound on `g^V(u) - g^V(u + x)` for `u ≤ 0` and `x ∈ [0, 1]`. -/
theorem abs_criticalTruncatedSource_sub_shift_le_exp_half {V : ℝ} (S : Finset ℕ) (b : ℕ → ℝ)
    {u x : ℝ} (hx1 : x ≤ 1) :
    |criticalTruncatedSource V S b u - criticalTruncatedSource V S b (u + x)| ≤
      criticalTruncatedJumpEnvelopeConstant S b * Real.exp (u / 2) := by
  have h1 := abs_criticalTruncatedSource_le_exp_half V S b u
  have h2 := abs_criticalTruncatedSource_le_exp_half V S b (u + x)
  have hexp : Real.exp ((u + x) / 2) ≤ 2 * Real.exp (u / 2) := by
    rw [show (u + x) / 2 = u / 2 + x / 2 by ring, Real.exp_add, mul_comm]
    exact mul_le_mul_of_nonneg_right (exp_half_le_two_of_le_one hx1) (Real.exp_pos _).le
  have hMB : 0 ≤ 2 * ∑ n ∈ S, |b n| := by
    have := Finset.sum_nonneg fun n (_ : n ∈ S) => abs_nonneg (b n); positivity
  have h3 : |criticalTruncatedSource V S b u - criticalTruncatedSource V S b (u + x)| ≤
      (6 * ∑ n ∈ S, |b n|) * Real.exp (u / 2) := by
    calc |criticalTruncatedSource V S b u - criticalTruncatedSource V S b (u + x)|
        ≤ |criticalTruncatedSource V S b u| + |criticalTruncatedSource V S b (u + x)| :=
          abs_sub _ _
      _ ≤ (2 * ∑ n ∈ S, |b n|) * Real.exp (u / 2) +
            (2 * ∑ n ∈ S, |b n|) * (2 * Real.exp (u / 2)) :=
          add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left hexp hMB))
      _ = (6 * ∑ n ∈ S, |b n|) * Real.exp (u / 2) := by ring
  refine h3.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  unfold criticalTruncatedJumpEnvelopeConstant
  have := smoothTransitionSlope_nonneg
  have : 0 ≤ ∑ n ∈ S, |b n| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have := realPhaseLipschitz_nonneg S b
  nlinarith

/-- Clock-Lipschitz bound on `g^V(u) - g^V(u + x)` for `u ≤ 0` and `x ∈ [0, 1]`, uniform in `V ≥ 1`. -/
theorem abs_criticalTruncatedSource_sub_shift_le_exp_neg_half {V : ℝ} (hV : 1 ≤ V)
    (S : Finset ℕ) (b : ℕ → ℝ) {u x : ℝ} (hu : u ≤ 0) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |criticalTruncatedSource V S b u - criticalTruncatedSource V S b (u + x)| ≤
      criticalTruncatedJumpEnvelopeConstant S b * Real.exp (-(u / 2)) * x := by
  set F := criticalTruncatedClockProfile V S b
  rw [criticalTruncatedSource_eq_exp_half_mul_clockProfile,
    criticalTruncatedSource_eq_exp_half_mul_clockProfile]
  have heq : Real.exp (u / 2) * F (Real.exp (-u)) -
      Real.exp ((u + x) / 2) * F (Real.exp (-(u + x))) =
      Real.exp (u / 2) * (F (Real.exp (-u)) - F (Real.exp (-(u + x)))) +
      (Real.exp (u / 2) - Real.exp ((u + x) / 2)) * F (Real.exp (-(u + x))) := by
    ring
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos (u / 2))]
  have hexp_diff : |Real.exp (-u) - Real.exp (-(u + x))| ≤ Real.exp (-u) * x := by
    have h1 : Real.exp (-(u + x)) = Real.exp (-u) * Real.exp (-x) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : 1 - x ≤ Real.exp (-x) := by
      linarith [Real.add_one_le_exp (-x)]
    rw [h1, show Real.exp (-u) - Real.exp (-u) * Real.exp (-x) =
        Real.exp (-u) * (1 - Real.exp (-x)) by ring,
      abs_mul, abs_of_pos (Real.exp_pos (-u)), abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos (-u)).le
  have hFL := (abs_criticalTruncatedClockProfile_sub_le hV S b
    (Real.exp (-u)) (Real.exp (-(u + x)))).trans
    (mul_le_mul_of_nonneg_left hexp_diff (by
      have := smoothTransitionSlope_nonneg
      have : 0 ≤ ∑ n ∈ S, |b n| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have := realPhaseLipschitz_nonneg S b
      positivity))
  have hexp_prod : Real.exp (u / 2) * Real.exp (-u) = Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hA : Real.exp (u / 2) * |F (Real.exp (-u)) - F (Real.exp (-(u + x)))| ≤
      (4 * smoothTransitionSlope * (∑ n ∈ S, |b n|) + realPhaseLipschitz S b) *
        Real.exp (-(u / 2)) * x := by
    calc Real.exp (u / 2) * |F (Real.exp (-u)) - F (Real.exp (-(u + x)))|
        ≤ Real.exp (u / 2) * ((4 * smoothTransitionSlope * (∑ n ∈ S, |b n|) +
            realPhaseLipschitz S b) * (Real.exp (-u) * x)) :=
          mul_le_mul_of_nonneg_left hFL (Real.exp_pos _).le
      _ = (4 * smoothTransitionSlope * (∑ n ∈ S, |b n|) + realPhaseLipschitz S b) *
            (Real.exp (u / 2) * Real.exp (-u)) * x := by ring
      _ = (4 * smoothTransitionSlope * (∑ n ∈ S, |b n|) + realPhaseLipschitz S b) *
            Real.exp (-(u / 2)) * x := by rw [hexp_prod]
  have hexp_half_diff : |Real.exp (u / 2) - Real.exp ((u + x) / 2)| ≤ Real.exp (-(u / 2)) * x := by
    have h1 : Real.exp ((u + x) / 2) = Real.exp ((u + x) / 2) * 1 := (mul_one _).symm
    have h2 : Real.exp (u / 2) = Real.exp ((u + x) / 2) * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (-(x / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h4 : 1 - x / 2 ≤ Real.exp (-(x / 2)) := by
      linarith [Real.add_one_le_exp (-(x / 2))]
    have h5 : Real.exp ((u + x) / 2) ≤ 2 * Real.exp (u / 2) := by
      rw [show (u + x) / 2 = u / 2 + x / 2 by ring, Real.exp_add, mul_comm]
      exact mul_le_mul_of_nonneg_right (exp_half_le_two_of_le_one hx1) (Real.exp_pos _).le
    have h6 : Real.exp (u / 2) ≤ Real.exp (-(u / 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [show Real.exp (u / 2) - Real.exp ((u + x) / 2) =
        -(Real.exp ((u + x) / 2) * (1 - Real.exp (-(x / 2)))) by
          rw [h2]; ring,
      abs_neg, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (by linarith)]
    calc Real.exp ((u + x) / 2) * (1 - Real.exp (-(x / 2)))
        ≤ (2 * Real.exp (u / 2)) * (x / 2) :=
          mul_le_mul h5 (by linarith) (by linarith) (by positivity)
      _ = Real.exp (u / 2) * x := by ring
      _ ≤ Real.exp (-(u / 2)) * x := mul_le_mul_of_nonneg_right h6 hx0
  have hB : |Real.exp (u / 2) - Real.exp ((u + x) / 2)| * |F (Real.exp (-(u + x)))| ≤
      (2 * ∑ n ∈ S, |b n|) * Real.exp (-(u / 2)) * x := by
    calc |Real.exp (u / 2) - Real.exp ((u + x) / 2)| * |F (Real.exp (-(u + x)))|
        ≤ (Real.exp (-(u / 2)) * x) * (2 * ∑ n ∈ S, |b n|) :=
          mul_le_mul hexp_half_diff (abs_criticalTruncatedClockProfile_le V S b _)
            (abs_nonneg _) (by positivity)
      _ = (2 * ∑ n ∈ S, |b n|) * Real.exp (-(u / 2)) * x := by ring
  unfold criticalTruncatedJumpEnvelopeConstant
  have : 0 ≤ (∑ n ∈ S, |b n|) * Real.exp (-(u / 2)) * x := by
    have : 0 ≤ ∑ n ∈ S, |b n| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  linarith

/-- **Global Pointwise Square-Increment Envelope for Doubly Collared Critical Sources.**
For every `V ≥ 1`, `u ≤ 0`, and `x ∈ [0, 1]`, interpolating the clock-Lipschitz bound and the
amplitude bound via `|Δ|^4 = |Δ| · |Δ|^3` yields
`(g^V(u) - g^V(u + x))^2 ≤ K(S, b)^2 √x e^{u/2}` without interval splitting. -/
theorem sq_criticalTruncatedSource_sub_shift_le {V : ℝ} (hV : 1 ≤ V)
    (S : Finset ℕ) (b : ℕ → ℝ) {u x : ℝ} (hu : u ≤ 0) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (criticalTruncatedSource V S b u - criticalTruncatedSource V S b (u + x)) ^ 2 ≤
      criticalTruncatedJumpEnvelopeConstant S b ^ 2 * Real.sqrt x * Real.exp (u / 2) := by
  set D := |criticalTruncatedSource V S b u - criticalTruncatedSource V S b (u + x)|
  set K := criticalTruncatedJumpEnvelopeConstant S b
  set E := Real.exp (u / 2)
  set E_inv := Real.exp (-(u / 2))
  have hD : 0 ≤ D := abs_nonneg _
  have hK : 0 ≤ K := criticalTruncatedJumpEnvelopeConstant_nonneg S b
  have hE : 0 < E := Real.exp_pos _
  have hEE : E_inv * E = 1 := by
    dsimp only [E, E_inv]
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h1 : D ≤ K * E_inv * x :=
    abs_criticalTruncatedSource_sub_shift_le_exp_neg_half hV S b hu hx0 hx1
  have h2 : D ≤ K * E :=
    abs_criticalTruncatedSource_sub_shift_le_exp_half S b hx1
  have h2_cube : D ^ 3 ≤ (K * E) ^ 3 := pow_le_pow_left₀ hD h2 3
  have h4 : (D ^ 2) ^ 2 ≤ (K ^ 2 * Real.sqrt x * E) ^ 2 := by
    calc (D ^ 2) ^ 2 = D * D ^ 3 := by ring
      _ ≤ (K * E_inv * x) * (K * E) ^ 3 :=
          mul_le_mul h1 h2_cube (by positivity) (by positivity)
      _ = K ^ 4 * x * (E_inv * E) * E ^ 2 := by ring
      _ = (K ^ 2 * Real.sqrt x * E) ^ 2 := by
          rw [hEE, mul_one, mul_pow, mul_pow, Real.sq_sqrt hx0]
          ring
  have hRHS : 0 ≤ K ^ 2 * Real.sqrt x * E := by positivity
  have hD2 : D ^ 2 = (criticalTruncatedSource V S b u - criticalTruncatedSource V S b (u + x)) ^ 2 :=
    sq_abs _
  rw [← hD2]
  nlinarith [sq_nonneg (D ^ 2 - K ^ 2 * Real.sqrt x * E)]

/-- For `u > 0` and `x ≥ 0`, both `g^V(u)` and `g^V(u + x)` vanish. -/
private theorem criticalTruncatedSource_sub_shift_eq_zero_of_pos (V : ℝ) (S : Finset ℕ)
    (b : ℕ → ℝ) {u x : ℝ} (hu : 0 < u) (hx0 : 0 ≤ x) :
    criticalTruncatedSource V S b u - criticalTruncatedSource V S b (u + x) = 0 := by
  have h1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : Real.exp (-(u + x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [criticalTruncatedSource_eq_exp_half_mul_clockProfile V S b u,
    criticalTruncatedSource_eq_exp_half_mul_clockProfile V S b (u + x),
    criticalTruncatedClockProfile_eq_zero_of_le_one V S b h1,
    criticalTruncatedClockProfile_eq_zero_of_le_one V S b h2, mul_zero, mul_zero, sub_self]

/-- **Integrated Square-Increment Bound for Doubly Collared Critical Sources.**
For every `V ≥ 1` and `x ∈ [0, 1]`,
`∫ u, (g^V(u) - g^V(u + x))^2 ≤ 2 K(S, b)^2 √x`. -/
theorem integral_criticalTruncatedSource_sub_shift_sq_le {V : ℝ} (hV : 1 ≤ V)
    (S : Finset ℕ) (b : ℕ → ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ u : ℝ, (criticalTruncatedSource V S b u - criticalTruncatedSource V S b (u + x)) ^ 2 ≤
      2 * criticalTruncatedJumpEnvelopeConstant S b ^ 2 * Real.sqrt x := by
  set g := criticalTruncatedSource V S b
  set K := criticalTruncatedJumpEnvelopeConstant S b
  set env : ℝ → ℝ := (Iic (0 : ℝ)).indicator fun u => K ^ 2 * Real.sqrt x * Real.exp (u / 2)
  have hpt (u : ℝ) : (g u - g (u + x)) ^ 2 ≤ env u := by
    by_cases hu : u ≤ 0
    · simp only [env, indicator_of_mem (show u ∈ Iic (0 : ℝ) from hu)]
      exact sq_criticalTruncatedSource_sub_shift_le hV S b hu hx0 hx1
    · simp only [env, indicator_of_notMem (show u ∉ Iic (0 : ℝ) from hu)]
      rw [criticalTruncatedSource_sub_shift_eq_zero_of_pos V S b (not_le.mp hu) hx0, zero_pow two_ne_zero]
  have henv_int : Integrable env := by
    rw [integrable_indicator_iff measurableSet_Iic]
    exact IntegrableOn.congr_fun
      ((integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 2) 0).const_mul (K ^ 2 * Real.sqrt x))
      (fun u _ => by ring_nf) measurableSet_Iic
  have hg_cont : Continuous fun u => (g u - g (u + x)) ^ 2 :=
    ((continuous_criticalTruncatedSource V S b).sub
      ((continuous_criticalTruncatedSource V S b).comp (continuous_id.add continuous_const))).pow 2
  have hg_int : Integrable fun u => (g u - g (u + x)) ^ 2 :=
    henv_int.mono' hg_cont.aestronglyMeasurable (Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpt u)
  have hexp_int : (∫ u : ℝ in Iic 0, Real.exp (u / 2)) = 2 := by
    have he := integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 2) 0
    norm_num at he
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using he
  calc ∫ u : ℝ, (g u - g (u + x)) ^ 2
      ≤ ∫ u : ℝ, env u := integral_mono hg_int henv_int hpt
    _ = K ^ 2 * Real.sqrt x * ∫ u : ℝ in Iic 0, Real.exp (u / 2) := by
        unfold env
        rw [integral_indicator measurableSet_Iic, integral_const_mul]
    _ = 2 * K ^ 2 * Real.sqrt x := by rw [hexp_int]; ring

/-- **Autocorrelation Jump Bound at Small Shifts (`x ∈ [0, 1]`).**
For every `V ≥ 1` and `x ∈ [0, 1]`,
`ac(0) - ac(x) ≤ K(S, b)^2 √x` uniformly in `V`. -/
theorem sourceAutocorrelation_criticalTruncatedSource_jump_le_sqrt {V : ℝ} (hV : 1 ≤ V)
    (S : Finset ℕ) (b : ℕ → ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    sourceAutocorrelation (criticalTruncatedSource V S b) 0 -
      sourceAutocorrelation (criticalTruncatedSource V S b) x ≤
        criticalTruncatedJumpEnvelopeConstant S b ^ 2 * Real.sqrt x := by
  have hV0 : 0 < V := by linarith
  set f := criticalTruncatedTest hV0 S b
  set g := criticalTruncatedSource V S b
  have hac (y : ℝ) : sourceAutocorrelation g y = autocorr f y := by
    rw [← autocorr_neg]
    unfold sourceAutocorrelation autocorr
    simp only [sub_eq_add_neg]
    rfl
  have hshift := integral_sub_shift_sq f.hasCompactSupport f.continuous x
  have hint := integral_criticalTruncatedSource_sub_shift_sq_le hV S b hx0 hx1
  change (∫ u : ℝ, (g u - g (u + x)) ^ 2) = 2 * (autocorr f 0 - autocorr f x) at hshift
  rw [hac 0, hac x]
  linarith

/-- **Autocorrelation Jump Nonnegativity and Global Mass Ceiling (`x ∈ ℝ`).**
For every `V : ℝ`, `S : Finset ℕ`, `b : ℕ → ℝ`, and `x : ℝ`,
`0 ≤ ac(0) - ac(x) ≤ 2 U ∑_{n ∈ S} b_n^2`. -/
theorem sourceAutocorrelation_criticalTruncatedSource_jump_bounds (V : ℝ)
    (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    0 ≤ sourceAutocorrelation (criticalTruncatedSource V S b) 0 -
      sourceAutocorrelation (criticalTruncatedSource V S b) x ∧
    sourceAutocorrelation (criticalTruncatedSource V S b) 0 -
      sourceAutocorrelation (criticalTruncatedSource V S b) x ≤
        2 * criticalCollarMassUpper * ∑ n ∈ S, b n ^ 2 := by
  set g := criticalTruncatedSource V S b
  have hg := admissibleSource_criticalTruncatedSource V S b
  have hmi := integrable_levySourceSpectralDensity hg
  have hmc := continuous_levySourceSpectralDensity hg
  have hjump := sourceAutocorrelation_jump_eq_spectral hg x
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnn_int : ∀ t : ℝ, 0 ≤ levySourceSpectralDensity g t * (1 - Real.cos (t * x)) := fun t =>
    mul_nonneg (sq_nonneg _) (by linarith [Real.cos_le_one (t * x)])
  have hnn : 0 ≤ sourceAutocorrelation g 0 - sourceAutocorrelation g x := by
    rw [hjump]
    exact mul_nonneg (by positivity) (integral_nonneg hnn_int)
  refine ⟨hnn, ?_⟩
  have hic : Integrable fun t => levySourceSpectralDensity g t * (1 - Real.cos (t * x)) := by
    refine (hmi.const_mul 2).mono'
      (hmc.mul (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (hnn_int t)]
    have h0 : 0 ≤ levySourceSpectralDensity g t := sq_nonneg _
    have h2 : 1 - Real.cos (t * x) ≤ 2 := by linarith [Real.neg_one_le_cos (t * x)]
    nlinarith
  have hle : (∫ t, levySourceSpectralDensity g t * (1 - Real.cos (t * x))) ≤
      ∫ t, 2 * levySourceSpectralDensity g t := by
    refine integral_mono hic (hmi.const_mul 2) fun t => ?_
    have h0 : 0 ≤ levySourceSpectralDensity g t := sq_nonneg _
    have h2 : 1 - Real.cos (t * x) ≤ 2 := by linarith [Real.neg_one_le_cos (t * x)]
    nlinarith
  rw [integral_const_mul, integral_levySourceSpectralDensity hg] at hle
  have hsq : ∫ y, g y ^ 2 = sourceAutocorrelation g 0 := by
    unfold sourceAutocorrelation; simp only [sub_zero, sq]
  have hm := sourceAutocorrelation_criticalTruncatedSource_zero_le V S b
  rw [hjump]
  have h1 : 1 / (2 * Real.pi) * (2 * (2 * Real.pi * ∫ y, g y ^ 2)) = 2 * sourceAutocorrelation g 0 := by
    rw [hsq]; field_simp
  calc 1 / (2 * Real.pi) * ∫ t, levySourceSpectralDensity g t * (1 - Real.cos (t * x))
      ≤ 1 / (2 * Real.pi) * (2 * (2 * Real.pi * ∫ y, g y ^ 2)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 2 * sourceAutocorrelation g 0 := h1
    _ ≤ 2 * criticalCollarMassUpper * ∑ n ∈ S, b n ^ 2 := by linarith

/-- On `ScaleWindow S 1 L` (`1 ≤ L`), `criticalTruncatedJumpEnvelopeConstant S b ^ 2` is bounded by
`(4 sup|σ'| + 20)^2 L^3 ∑_{n ∈ S} b_n^2`. -/
theorem criticalTruncatedJumpEnvelopeConstant_sq_le_of_window {S : Finset ℕ} {L : ℕ}
    (hL : 1 ≤ L) (hS : ScaleWindow S 1 L) (b : ℕ → ℝ) :
    criticalTruncatedJumpEnvelopeConstant S b ^ 2 ≤
      (4 * smoothTransitionSlope + 20) ^ 2 * (L : ℝ) ^ 3 * ∑ n ∈ S, b n ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsub : S ⊆ Finset.range L := by
    intro n hn
    rw [Finset.mem_range]
    have := (hS n hn).2
    omega
  have hcard : (S.card : ℝ) ≤ L := by
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hlip : realPhaseLipschitz S b ≤ 14 * (L : ℝ) * ∑ n ∈ S, |b n| := by
    unfold realPhaseLipschitz
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hnL : ((n + 1 : ℕ) : ℝ) ≤ L := by
      have := (hS n hn).2
      exact_mod_cast (show n + 1 ≤ L by omega)
    have hfreq := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).2
    have hcoeff : 9 / 2 * (factorialShiftedFreq (n + 1) + ((n + 1 : ℕ) : ℝ)) ≤ 14 * (L : ℝ) := by
      linarith
    calc |b n| * (9 / 2 * (factorialShiftedFreq (n + 1) + ((n + 1 : ℕ) : ℝ)))
        ≤ |b n| * (14 * (L : ℝ)) := mul_le_mul_of_nonneg_left hcoeff (abs_nonneg _)
      _ = 14 * (L : ℝ) * |b n| := by ring
  have hK : criticalTruncatedJumpEnvelopeConstant S b ≤
      (4 * smoothTransitionSlope + 20) * (L : ℝ) * ∑ n ∈ S, |b n| := by
    unfold criticalTruncatedJumpEnvelopeConstant
    have hsl := smoothTransitionSlope_nonneg
    have hsum_nn : 0 ≤ ∑ n ∈ S, |b n| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h1 : (4 * smoothTransitionSlope + 6) * ∑ n ∈ S, |b n| ≤
        (4 * smoothTransitionSlope + 6) * (L : ℝ) * ∑ n ∈ S, |b n| := by
      calc (4 * smoothTransitionSlope + 6) * ∑ n ∈ S, |b n|
          = (4 * smoothTransitionSlope + 6) * 1 * ∑ n ∈ S, |b n| := by ring
        _ ≤ (4 * smoothTransitionSlope + 6) * (L : ℝ) * ∑ n ∈ S, |b n| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL1 (by positivity)) hsum_nn
    linarith
  have hcs : (∑ n ∈ S, |b n|) ^ 2 ≤ (L : ℝ) * ∑ n ∈ S, b n ^ 2 := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := S) (f := fun n => |b n|)
    simp only [sq_abs] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hK_nn := criticalTruncatedJumpEnvelopeConstant_nonneg S b
  calc criticalTruncatedJumpEnvelopeConstant S b ^ 2
      ≤ ((4 * smoothTransitionSlope + 20) * (L : ℝ) * ∑ n ∈ S, |b n|) ^ 2 :=
        pow_le_pow_left₀ hK_nn hK 2
    _ = (4 * smoothTransitionSlope + 20) ^ 2 * (L : ℝ) ^ 2 * (∑ n ∈ S, |b n|) ^ 2 := by ring
    _ ≤ (4 * smoothTransitionSlope + 20) ^ 2 * (L : ℝ) ^ 2 * ((L : ℝ) * ∑ n ∈ S, b n ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by
          have := smoothTransitionSlope_nonneg; positivity)
    _ = (4 * smoothTransitionSlope + 20) ^ 2 * (L : ℝ) ^ 3 * ∑ n ∈ S, b n ^ 2 := by ring

/-- Upper bound `archLevySinhWeight x ≤ 3 / x` on `x ∈ (0, 1]`. -/
theorem archLevySinhWeight_le_three_div {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    archLevySinhWeight x ≤ 3 / x := by
  rw [archLevySinhWeight, exp_half_div_sinh_eq hx0]
  unfold RHTower.archLevyDensity
  set r := Real.exp (-2 * x)
  have hr_lt : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hd : 0 < 1 - r := by linarith
  have hprod : r * Real.exp (2 * x) = 1 := by
    dsimp only [r]; rw [← Real.exp_add]; simp
  have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
    linarith [Real.add_one_le_exp (2 * x)]
  have hr_bound : r * (1 + 2 * x) ≤ 1 := by
    calc r * (1 + 2 * x) ≤ r * Real.exp (2 * x) :=
          mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ = 1 := hprod
  have h2x : 2 * x ≤ 3 * (1 - r) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 - 2 * x by linarith) hd.le]
  have hexp_half : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [le_div_iff₀ hx0]
  have hdiv : (2 * x) / (1 - r) ≤ 3 := by
    rw [div_le_iff₀ hd]; exact h2x
  calc 2 * (Real.exp (-x / 2) / (1 - r)) * x
      = Real.exp (-x / 2) * ((2 * x) / (1 - r)) := by ring
    _ ≤ 1 * 3 := mul_le_mul hexp_half hdiv (by positivity) zero_le_one
    _ = 3 := one_mul 3

/-- Upper bound `archLevySinhWeight x ≤ 48 * x ^ (-2 : ℝ)` on `x ≥ 1`. -/
theorem archLevySinhWeight_le_fortyEight_rpow_neg_two {x : ℝ} (hx1 : 1 ≤ x) :
    archLevySinhWeight x ≤ 48 * x ^ (-2 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  rw [archLevySinhWeight, exp_half_div_sinh_eq hx0]
  unfold RHTower.archLevyDensity
  set r := Real.exp (-2 * x)
  have hr_lt : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hd : 0 < 1 - r := by linarith
  have hprod : r * Real.exp (2 * x) = 1 := by
    dsimp only [r]; rw [← Real.exp_add]; simp
  have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
    linarith [Real.add_one_le_exp (2 * x)]
  have hr_bound : r * (1 + 2 * x) ≤ 1 := by
    calc r * (1 + 2 * x) ≤ r * Real.exp (2 * x) :=
          mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ = 1 := hprod
  have h2 : 2 ≤ 3 * (1 - r) := by
    have hr3 : 3 * r ≤ r * (1 + 2 * x) := by
      calc 3 * r = r * 3 := mul_comm 3 r
        _ ≤ r * (1 + 2 * x) := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    linarith
  have hx4 : x / 4 ≤ Real.exp (x / 4) := by
    linarith [Real.add_one_le_exp (x / 4)]
  have hx2 : (x / 4) ^ 2 ≤ Real.exp (x / 2) := by
    calc (x / 4) ^ 2 ≤ Real.exp (x / 4) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hx4 2
      _ = Real.exp (x / 2) := by rw [← Real.exp_nat_mul]; ring_nf
  have hprod_half : Real.exp (-x / 2) * Real.exp (x / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hexp_half : Real.exp (-x / 2) ≤ 16 * x ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc Real.exp (-x / 2) * x ^ 2 = 16 * (Real.exp (-x / 2) * (x / 4) ^ 2) := by ring
      _ ≤ 16 * (Real.exp (-x / 2) * Real.exp (x / 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hx2 (Real.exp_pos _).le) (by norm_num)
      _ = 16 := by rw [hprod_half, mul_one]
  have hdiv : 2 * (Real.exp (-x / 2) / (1 - r)) ≤ 3 * Real.exp (-x / 2) := by
    rw [mul_div_assoc', div_le_iff₀ hd]
    calc 2 * Real.exp (-x / 2) ≤ 3 * (1 - r) * Real.exp (-x / 2) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = 3 * Real.exp (-x / 2) * (1 - r) := by ring
  linarith

private theorem integral_Ioc_zero_one_rpow {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun x : ℝ => x ^ a) (Ioc 0 1) ∧
    (∫ x in Ioc (0 : ℝ) 1, x ^ a) = 1 / (a + 1) := by
  have hane : a + 1 ≠ 0 := by linarith
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' ha), ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl ha), Real.one_rpow, Real.zero_rpow hane]
  ring

/-- Scale-free low-window Archimedean Lévy ceiling constant
`6 (4 sup|σ'| + 20)^2 L_low^3 + 96 U`, completely independent of `V ≥ 1` and of any high scale `M`. -/
def criticalLowWindowLevyConstant (L_low : ℕ) : ℝ :=
  6 * (4 * smoothTransitionSlope + 20) ^ 2 * (L_low : ℝ) ^ 3 + 96 * criticalCollarMassUpper

theorem criticalLowWindowLevyConstant_pos (L_low : ℕ) :
    0 < criticalLowWindowLevyConstant L_low := by
  unfold criticalLowWindowLevyConstant
  have h1 := smoothTransitionSlope_nonneg
  have h2 : 0 < criticalCollarMassUpper := by
    unfold criticalCollarMassUpper
    have := factorialUnitIntervalUpper_pos
    positivity
  positivity

/-- **Uniform Scale-Free Archimedean Lévy Ceiling on Any Finite Support `S`.**
For every `V ≥ 1`, `S : Finset ℕ`, and `b : ℕ → ℝ`,
`biScaleLevyEnergy (criticalTruncatedTest hV0 S b) ≤ 6 K(S, b)^2 + 96 U ∑_{n ∈ S} b_n^2`. -/
theorem biScaleLevyEnergy_criticalTruncatedTest_le_general {V : ℝ} (hV0 : 0 < V) (hV : 1 ≤ V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    biScaleLevyEnergy (criticalTruncatedTest hV0 S b) ≤
      6 * criticalTruncatedJumpEnvelopeConstant S b ^ 2 +
        96 * criticalCollarMassUpper * ∑ n ∈ S, b n ^ 2 := by
  set f := criticalTruncatedTest hV0 S b
  set g := criticalTruncatedSource V S b
  set K := criticalTruncatedJumpEnvelopeConstant S b
  set E := ∑ n ∈ S, b n ^ 2
  set U := criticalCollarMassUpper
  set F : ℝ → ℝ := fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x
  obtain ⟨Kg, hKg⟩ := exists_lipschitz_criticalTruncatedSource hV0 S b
  have hF_int : IntegrableOn F (Ioi 0) := integrableOn_levy_of_lipschitz f hKg
  have hac (x : ℝ) : autocorr f x = sourceAutocorrelation g x := by
    rw [← autocorr_neg]; unfold sourceAutocorrelation autocorr; simp only [sub_eq_add_neg]; rfl
  have hsplit : ∫ x in Ioi (0 : ℝ), F x =
      (∫ x in Ioc (0 : ℝ) 1, F x) + ∫ x in Ioi (1 : ℝ), F x := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hF_int.mono_set Ioc_subset_Ioi_self) (hF_int.mono_set (Ioi_subset_Ioi zero_le_one))]
  obtain ⟨hi_half, hval_half⟩ := integral_Ioc_zero_one_rpow (a := -(1 / 2 : ℝ)) (by norm_num)
  have hIoc : (∫ x in Ioc (0 : ℝ) 1, F x) ≤ 6 * K ^ 2 := by
    have hpt : ∀ x ∈ Ioc (0 : ℝ) 1, F x ≤ (3 * K ^ 2) * x ^ (-(1 / 2 : ℝ)) := by
      intro x hx
      dsimp only [F]
      rw [hac 0, hac x]
      have hj := sourceAutocorrelation_criticalTruncatedSource_jump_le_sqrt hV S b hx.1.le hx.2
      have hnn := (sourceAutocorrelation_criticalTruncatedSource_jump_bounds V S b x).1
      have hw := archLevySinhWeight_le_three_div hx.1 hx.2
      have hω_nn := (archLevySinhWeight_pos hx.1).le
      have hsqrt_div : Real.sqrt x * (3 / x) = 3 * x ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, show 3 / x = 3 * x ^ (-1 : ℝ) by rw [Real.rpow_neg_one]; ring,
          show x ^ (1 / 2 : ℝ) * (3 * x ^ (-1 : ℝ)) =
            3 * (x ^ (1 / 2 : ℝ) * x ^ (-1 : ℝ)) by ring,
          ← Real.rpow_add hx.1]
        norm_num
      calc (sourceAutocorrelation g 0 - sourceAutocorrelation g x) * archLevySinhWeight x
          ≤ (K ^ 2 * Real.sqrt x) * (3 / x) := mul_le_mul hj hw hω_nn (by positivity)
        _ = K ^ 2 * (Real.sqrt x * (3 / x)) := by ring
        _ = (3 * K ^ 2) * x ^ (-(1 / 2 : ℝ)) := by rw [hsqrt_div]; ring
    calc ∫ x in Ioc (0 : ℝ) 1, F x
        ≤ ∫ x in Ioc (0 : ℝ) 1, (3 * K ^ 2) * x ^ (-(1 / 2 : ℝ)) :=
          setIntegral_mono_on (hF_int.mono_set Ioc_subset_Ioi_self)
            (hi_half.const_mul _) measurableSet_Ioc hpt
      _ = (3 * K ^ 2) * ∫ x in Ioc (0 : ℝ) 1, x ^ (-(1 / 2 : ℝ)) := integral_const_mul _ _
      _ = 6 * K ^ 2 := by rw [hval_half]; ring
  have hi_two : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hval_two : (∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ)) = 1 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]
    norm_num
  have hIoi : (∫ x in Ioi (1 : ℝ), F x) ≤ 96 * U * E := by
    have hpt : ∀ x ∈ Ioi (1 : ℝ), F x ≤ (96 * U * E) * x ^ (-2 : ℝ) := by
      intro x hx
      have hx0 : 0 < x := lt_trans one_pos hx
      dsimp only [F]
      rw [hac 0, hac x]
      obtain ⟨hnn, hj⟩ := sourceAutocorrelation_criticalTruncatedSource_jump_bounds V S b x
      have hw := archLevySinhWeight_le_fortyEight_rpow_neg_two (le_of_lt hx)
      have hω_nn := (archLevySinhWeight_pos hx0).le
      have hUE : 0 ≤ 2 * U * E := by
        have : 0 ≤ U := by unfold U criticalCollarMassUpper; have := factorialUnitIntervalUpper_pos; positivity
        have : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
        positivity
      calc (sourceAutocorrelation g 0 - sourceAutocorrelation g x) * archLevySinhWeight x
          ≤ (2 * U * E) * (48 * x ^ (-2 : ℝ)) := mul_le_mul hj hw hω_nn hUE
        _ = (96 * U * E) * x ^ (-2 : ℝ) := by ring
    calc ∫ x in Ioi (1 : ℝ), F x
        ≤ ∫ x in Ioi (1 : ℝ), (96 * U * E) * x ^ (-2 : ℝ) :=
          setIntegral_mono_on (hF_int.mono_set (Ioi_subset_Ioi zero_le_one))
            (hi_two.const_mul _) measurableSet_Ioi hpt
      _ = (96 * U * E) * ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) := integral_const_mul _ _
      _ = 96 * U * E := by rw [hval_two, mul_one]
  unfold biScaleLevyEnergy
  change (∫ x in Ioi (0 : ℝ), F x) ≤ _
  linarith

/-- **Uniform Scale-Free Archimedean Lévy Ceiling on Low Windows `ScaleWindow S_low 1 L_low`.**
For every `V ≥ 1`, `ScaleWindow S_low 1 L_low` (`1 ≤ L_low`), and `b : ℕ → ℝ`,
`biScaleLevyEnergy (criticalTruncatedTest hV0 S_low b) ≤ criticalLowWindowLevyConstant L_low * ∑_{n ∈ S_low} b_n^2`,
uniformly in `V` and completely independent of any high scale `M`. -/
theorem biScaleLevyEnergy_criticalTruncatedTest_le {V : ℝ} (hV0 : 0 < V) (hV : 1 ≤ V)
    {S_low : Finset ℕ} {L_low : ℕ} (hL_low : 1 ≤ L_low) (hlow : ScaleWindow S_low 1 L_low)
    (b : ℕ → ℝ) :
    biScaleLevyEnergy (criticalTruncatedTest hV0 S_low b) ≤
      criticalLowWindowLevyConstant L_low * ∑ n ∈ S_low, b n ^ 2 := by
  have h1 := biScaleLevyEnergy_criticalTruncatedTest_le_general hV0 hV S_low b
  have h2 := criticalTruncatedJumpEnvelopeConstant_sq_le_of_window hL_low hlow b
  unfold criticalLowWindowLevyConstant
  linarith

/-! ## Section 2: Scale-Free Low-Penalty Two-Band Archimedean Law and Bilinear Lévy Decomposition -/

/-- **Pointwise Spectral Autocorrelation Jump Split (`1/2 Δ_high ≤ Δ_union + Δ_low`).**
For any disjoint `S_low, S_high`, any `V : ℝ`, any `b : ℕ → ℝ`, and any shift `x : ℝ`,
`1/2 * (ac_{high}(0) - ac_{high}(x)) ≤ (ac_{union}(0) - ac_{union}(x)) + (ac_{low}(0) - ac_{low}(x))`. -/
theorem sourceAutocorrelation_union_jump_add_ge (V : ℝ) {S_low S_high : Finset ℕ}
    (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ) (x : ℝ) :
    1 / 2 * (sourceAutocorrelation (criticalTruncatedSource V S_high b) 0 -
        sourceAutocorrelation (criticalTruncatedSource V S_high b) x) ≤
      (sourceAutocorrelation (criticalTruncatedSource V (S_low ∪ S_high) b) 0 -
        sourceAutocorrelation (criticalTruncatedSource V (S_low ∪ S_high) b) x) +
      (sourceAutocorrelation (criticalTruncatedSource V S_low b) 0 -
        sourceAutocorrelation (criticalTruncatedSource V S_low b) x) := by
  set g := criticalTruncatedSource V (S_low ∪ S_high) b
  set g_low := criticalTruncatedSource V S_low b
  set g_high := criticalTruncatedSource V S_high b
  have hg := admissibleSource_criticalTruncatedSource V (S_low ∪ S_high) b
  have hg_low := admissibleSource_criticalTruncatedSource V S_low b
  have hg_high := admissibleSource_criticalTruncatedSource V S_high b
  have hpt (t : ℝ) : levySourceSpectralDensity g_high t ≤
      2 * levySourceSpectralDensity g t + 2 * levySourceSpectralDensity g_low t := by
    have hfun : (fun y => (g y : ℂ)) =
        (fun y => (g_low y : ℂ)) + (1 : ℂ) • fun y => (g_high y : ℂ) := by
      funext y
      have hu := criticalTruncatedSource_union V hdisj b y
      simp only [Pi.add_apply, one_smul, g, g_low, g_high]
      rw [hu]; push_cast; ring
    unfold levySourceSpectralDensity
    have hft := RHTower.WeilSpectral.paperFT_add_smul_real hg_low.1 hg_high.1 1 t
    rw [← hfun, one_mul] at hft
    set u := ‖paperFT (fun y => (g y : ℂ)) t‖
    set u_low := ‖paperFT (fun y => (g_low y : ℂ)) t‖
    set u_high := ‖paperFT (fun y => (g_high y : ℂ)) t‖
    have htri : u_high ≤ u + u_low := by
      have hsub : paperFT (fun y => (g_high y : ℂ)) t =
          paperFT (fun y => (g y : ℂ)) t - paperFT (fun y => (g_low y : ℂ)) t := by
        linear_combination -hft
      dsimp only [u, u_low, u_high]
      rw [hsub]
      exact norm_sub_le _ _
    have hsq : u_high ^ 2 ≤ (u + u_low) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (u - u_low)]
  have hic (f : ℝ → ℝ) (hf : AdmissibleSource f) :
      Integrable fun t => levySourceSpectralDensity f t * (1 - Real.cos (t * x)) := by
    refine ((integrable_levySourceSpectralDensity hf).const_mul 2).mono'
      ((continuous_levySourceSpectralDensity hf).mul
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have h0 : 0 ≤ levySourceSpectralDensity f t := sq_nonneg _
    have h1 : 0 ≤ 1 - Real.cos (t * x) := by linarith [Real.cos_le_one (t * x)]
    have h2 : 1 - Real.cos (t * x) ≤ 2 := by linarith [Real.neg_one_le_cos (t * x)]
    rw [Real.norm_of_nonneg (mul_nonneg h0 h1)]
    nlinarith
  rw [sourceAutocorrelation_jump_eq_spectral hg_high x,
    sourceAutocorrelation_jump_eq_spectral hg x,
    sourceAutocorrelation_jump_eq_spectral hg_low x]
  have hint_le : (∫ t, levySourceSpectralDensity g_high t * (1 - Real.cos (t * x))) ≤
      2 * (∫ t, levySourceSpectralDensity g t * (1 - Real.cos (t * x))) +
        2 * ∫ t, levySourceSpectralDensity g_low t * (1 - Real.cos (t * x)) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hic g hg).const_mul 2) ((hic g_low hg_low).const_mul 2)]
    refine integral_mono (hic g_high hg_high)
      (((hic g hg).const_mul 2).add ((hic g_low hg_low).const_mul 2)) fun t => ?_
    have h1 : 0 ≤ 1 - Real.cos (t * x) := by linarith [Real.cos_le_one (t * x)]
    have := mul_le_mul_of_nonneg_right (hpt t) h1
    linarith
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hint_le hpi.le
  linarith

/-- Bridge between `sourceLevyEnergy (criticalTruncatedSource V S b)` and
`biScaleLevyEnergy (criticalTruncatedTest hV S b)`. -/
theorem sourceLevyEnergy_criticalTruncatedSource_eq_ofReal {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    sourceLevyEnergy (criticalTruncatedSource V S b) =
      ENNReal.ofReal (biScaleLevyEnergy (criticalTruncatedTest hV S b)) := by
  set f := criticalTruncatedTest hV S b
  set g := criticalTruncatedSource V S b
  obtain ⟨K, hK⟩ := exists_lipschitz_criticalTruncatedSource hV S b
  have hJ := integrableOn_levy_of_lipschitz f (K := K) hK
  have hac (x : ℝ) : autocorr f x = sourceAutocorrelation g x := by
    rw [← autocorr_neg]; unfold sourceAutocorrelation autocorr; simp only [sub_eq_add_neg]; rfl
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    intro x hx
    rw [hac 0, hac x]
    exact mul_nonneg (sourceAutocorrelation_criticalTruncatedSource_jump_bounds V S b x).1
      (archLevySinhWeight_pos hx).le
  unfold sourceLevyEnergy biScaleLevyEnergy
  simp only [← hac]
  exact (ofReal_integral_eq_lintegral_ofReal hJ
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hnn))).symm

/-- **Two-Band Real Lévy Energy Split (`1/2 Lévy(g_high) - Lévy(g_low) ≤ Lévy(g_low + g_high)`).** -/
theorem biScaleLevyEnergy_criticalTruncatedTest_union_ge_half_sub {V : ℝ} (hV : 0 < V)
    {S_low S_high : Finset ℕ} (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ) :
    1 / 2 * biScaleLevyEnergy (criticalTruncatedTest hV S_high b) -
      biScaleLevyEnergy (criticalTruncatedTest hV S_low b) ≤
        biScaleLevyEnergy (criticalTruncatedTest hV (S_low ∪ S_high) b) := by
  set f := criticalTruncatedTest hV (S_low ∪ S_high) b
  set f_low := criticalTruncatedTest hV S_low b
  set f_high := criticalTruncatedTest hV S_high b
  obtain ⟨K, hK⟩ := exists_lipschitz_criticalTruncatedSource hV (S_low ∪ S_high) b
  obtain ⟨K_low, hK_low⟩ := exists_lipschitz_criticalTruncatedSource hV S_low b
  obtain ⟨K_high, hK_high⟩ := exists_lipschitz_criticalTruncatedSource hV S_high b
  have hJ := integrableOn_levy_of_lipschitz f hK
  have hJ_low := integrableOn_levy_of_lipschitz f_low hK_low
  have hJ_high := integrableOn_levy_of_lipschitz f_high hK_high
  have hac (S : Finset ℕ) (x : ℝ) :
      autocorr (criticalTruncatedTest hV S b) x =
        sourceAutocorrelation (criticalTruncatedSource V S b) x := by
    rw [← autocorr_neg]; unfold sourceAutocorrelation autocorr; simp only [sub_eq_add_neg]; rfl
  unfold biScaleLevyEnergy
  have hle : (∫ x in Ioi (0 : ℝ),
      1 / 2 * ((autocorr f_high 0 - autocorr f_high x) * archLevySinhWeight x)) ≤
      (∫ x in Ioi (0 : ℝ), (autocorr f 0 - autocorr f x) * archLevySinhWeight x) +
        ∫ x in Ioi (0 : ℝ), (autocorr f_low 0 - autocorr f_low x) * archLevySinhWeight x := by
    rw [← integral_add hJ hJ_low]
    refine setIntegral_mono_on (hJ_high.const_mul (1 / 2)) (hJ.add hJ_low) measurableSet_Ioi
      fun x hx => ?_
    dsimp only [f, f_low, f_high]
    rw [hac, hac, hac, hac, hac, hac]
    have hj := sourceAutocorrelation_union_jump_add_ge V hdisj b x
    have hω := (archLevySinhWeight_pos hx).le
    have := mul_le_mul_of_nonneg_right hj hω
    linarith
  rw [integral_const_mul] at hle
  linarith

/-- **Scale-Free Low-Penalty Two-Band Archimedean Coercivity (`biScaleLevyEnergy` form).**
Unlike `ofReal_le_criticalTruncatedLevyEnergy_of_low_high_split`, whose low-mode penalty grew like
`s_T (log M - c_T) K_low E_low`, here the low-mode penalty is `criticalLowWindowLevyConstant L_low * E_low`,
completely independent of the high scale `M` and the truncation `V ≥ criticalTruncationThreshold`. -/
theorem biScaleLevyEnergy_criticalTruncatedTest_ge_of_lowWindow_high_scaleFree
    {S_low S_high : Finset ℕ} {L_low M : ℕ} (hL_low : 1 ≤ L_low)
    (hlow : ScaleWindow S_low 1 L_low) (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ)
    (hM : 2 ≤ M) (hS_high : ∀ n ∈ S_high, M ≤ n + 1)
    {V : ℝ} (hVpos : 0 < V) (hV : criticalTruncationThreshold ≤ V) :
    criticalTruncatedArchLogSlope / 2 * (Real.log M - criticalTruncatedArchLogOffset) *
      (∑ n ∈ S_high, b n ^ 2) -
    criticalLowWindowLevyConstant L_low * (∑ n ∈ S_low, b n ^ 2) ≤
      biScaleLevyEnergy (criticalTruncatedTest hVpos (S_low ∪ S_high) b) := by
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  have hsplit := biScaleLevyEnergy_criticalTruncatedTest_union_ge_half_sub hVpos hdisj b
  have hlow_ub := biScaleLevyEnergy_criticalTruncatedTest_le hVpos hV1 hL_low hlow b
  have hhigh_er := ofReal_le_criticalTruncatedLevyEnergy S_high b hM hS_high hV
  rw [sourceLevyEnergy_criticalTruncatedSource_eq_ofReal hVpos S_high b] at hhigh_er
  have hhigh_nn : 0 ≤ biScaleLevyEnergy (criticalTruncatedTest hVpos S_high b) := by
    unfold biScaleLevyEnergy
    refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
    have hac (y : ℝ) : autocorr (criticalTruncatedTest hVpos S_high b) y =
        sourceAutocorrelation (criticalTruncatedSource V S_high b) y := by
      rw [← autocorr_neg]; unfold sourceAutocorrelation autocorr; simp only [sub_eq_add_neg]; rfl
    rw [hac 0, hac x]
    exact mul_nonneg (sourceAutocorrelation_criticalTruncatedSource_jump_bounds V S_high b x).1
      (archLevySinhWeight_pos hx).le
  have hhigh : criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) *
      (∑ n ∈ S_high, b n ^ 2) ≤
      biScaleLevyEnergy (criticalTruncatedTest hVpos S_high b) := by
    rcases le_or_gt (criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) *
        (∑ n ∈ S_high, b n ^ 2)) 0 with hnp | hpos
    · exact hnp.trans hhigh_nn
    · exact (ENNReal.ofReal_le_ofReal_iff hhigh_nn).mp hhigh_er
  linarith

/-- **Scale-Free Low-Penalty Two-Band Archimedean Coercivity (`sourceLevyEnergy` form).** -/
theorem ofReal_le_criticalTruncatedLevyEnergy_of_lowWindow_high_scaleFree
    {S_low S_high : Finset ℕ} {L_low M : ℕ} (hL_low : 1 ≤ L_low)
    (hlow : ScaleWindow S_low 1 L_low) (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ)
    (hM : 2 ≤ M) (hS_high : ∀ n ∈ S_high, M ≤ n + 1)
    {V : ℝ} (hV : criticalTruncationThreshold ≤ V) :
    ENNReal.ofReal (criticalTruncatedArchLogSlope / 2 * (Real.log M - criticalTruncatedArchLogOffset) *
      (∑ n ∈ S_high, b n ^ 2) -
      criticalLowWindowLevyConstant L_low * (∑ n ∈ S_low, b n ^ 2)) ≤
      sourceLevyEnergy (criticalTruncatedSource V (S_low ∪ S_high) b) := by
  have hVpos : 0 < V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  rw [sourceLevyEnergy_criticalTruncatedSource_eq_ofReal hVpos]
  exact ENNReal.ofReal_le_ofReal
    (biScaleLevyEnergy_criticalTruncatedTest_ge_of_lowWindow_high_scaleFree
      hL_low hlow hdisj b hM hS_high hVpos hV)

/-- **Shift-Adapted Bilinear Lévy Energy Decomposition (`biScaleLevyEnergy_union_ge_of_gamma`).**
For any disjoint `S_low, S_high` with `ScaleWindow S_low 1 L_low` (`1 ≤ L_low`), any `V ≥ 1`,
any `b : ℕ → ℝ`, and any coupling parameter `γ > 0`, choosing the shift-adapted Young weight
`β(x) = γ x^{1/4}` on `(0, 1]` and `β(x) = γ` on `(1, ∞)` retains 100% of both diagonal Lévy
energies `biScaleLevyEnergy f_low + biScaleLevyEnergy f_high` up to a scale-free bilinear error:
`biScaleLevyEnergy f_low + biScaleLevyEnergy f_high - γ⁻¹ * (2 C_levy(L_low) E_low) - γ * (120 U E_high) ≤ biScaleLevyEnergy f`. -/
theorem biScaleLevyEnergy_union_ge_of_gamma {V : ℝ} (hV0 : 0 < V) (hV : 1 ≤ V)
    {S_low S_high : Finset ℕ} {L_low : ℕ} (hL_low : 1 ≤ L_low) (hlow : ScaleWindow S_low 1 L_low)
    (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ) {γ : ℝ} (hγ : 0 < γ) :
    biScaleLevyEnergy (criticalTruncatedTest hV0 S_low b) +
      biScaleLevyEnergy (criticalTruncatedTest hV0 S_high b) -
      (γ⁻¹ * (2 * criticalLowWindowLevyConstant L_low * ∑ n ∈ S_low, b n ^ 2) +
        γ * (120 * criticalCollarMassUpper * ∑ n ∈ S_high, b n ^ 2)) ≤
      biScaleLevyEnergy (criticalTruncatedTest hV0 (S_low ∪ S_high) b) := by
  set f := criticalTruncatedTest hV0 (S_low ∪ S_high) b
  set f_low := criticalTruncatedTest hV0 S_low b
  set f_high := criticalTruncatedTest hV0 S_high b
  set g := criticalTruncatedSource V (S_low ∪ S_high) b
  set g_low := criticalTruncatedSource V S_low b
  set g_high := criticalTruncatedSource V S_high b
  set K_low := criticalTruncatedJumpEnvelopeConstant S_low b
  set E_low := ∑ n ∈ S_low, b n ^ 2
  set E_high := ∑ n ∈ S_high, b n ^ 2
  set U := criticalCollarMassUpper
  have hU : 0 ≤ U := by unfold U criticalCollarMassUpper; have := factorialUnitIntervalUpper_pos; positivity
  have hE_low : 0 ≤ E_low := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE_high : 0 ≤ E_high := Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨Kg, hKg⟩ := exists_lipschitz_criticalTruncatedSource hV0 (S_low ∪ S_high) b
  obtain ⟨Kg_low, hKg_low⟩ := exists_lipschitz_criticalTruncatedSource hV0 S_low b
  obtain ⟨Kg_high, hKg_high⟩ := exists_lipschitz_criticalTruncatedSource hV0 S_high b
  have hJ := integrableOn_levy_of_lipschitz f hKg
  have hJ_low := integrableOn_levy_of_lipschitz f_low hKg_low
  have hJ_high := integrableOn_levy_of_lipschitz f_high hKg_high
  have hac (S : Finset ℕ) (x : ℝ) :
      autocorr (criticalTruncatedTest hV0 S b) x =
        sourceAutocorrelation (criticalTruncatedSource V S b) x := by
    rw [← autocorr_neg]; unfold sourceAutocorrelation autocorr; simp only [sub_eq_add_neg]; rfl
  -- Pointwise jump inequality for any `β > 0`:
  have hjump_beta (x : ℝ) {β : ℝ} (hβ : 0 < β) :
      (autocorr f_low 0 - autocorr f_low x) + (autocorr f_high 0 - autocorr f_high x) -
        (β⁻¹ * (autocorr f_low 0 - autocorr f_low x) +
          β * (autocorr f_high 0 - autocorr f_high x)) ≤
        autocorr f 0 - autocorr f x := by
    have hs := integral_sub_shift_sq f.hasCompactSupport f.continuous x
    have hs_low := integral_sub_shift_sq f_low.hasCompactSupport f_low.continuous x
    have hs_high := integral_sub_shift_sq f_high.hasCompactSupport f_high.continuous x
    change (∫ u : ℝ, (g u - g (u + x)) ^ 2) = 2 * (autocorr f 0 - autocorr f x) at hs
    change (∫ u : ℝ, (g_low u - g_low (u + x)) ^ 2) = 2 * (autocorr f_low 0 - autocorr f_low x) at hs_low
    change (∫ u : ℝ, (g_high u - g_high (u + x)) ^ 2) = 2 * (autocorr f_high 0 - autocorr f_high x) at hs_high
    have h_int (h : C_c(ℝ, ℝ)) : Integrable fun u : ℝ => (h u - h (u + x)) ^ 2 := by
      have hc : Continuous fun u : ℝ => (h u - h (u + x)) ^ 2 :=
        (h.continuous.sub (h.continuous.comp (continuous_id.add continuous_const))).pow 2
      have hsh : Continuous fun u : ℝ => u - x := continuous_id.sub continuous_const
      have hcs : HasCompactSupport fun u : ℝ => (h u - h (u + x)) ^ 2 := by
        refine HasCompactSupport.intro
          (h.hasCompactSupport.isCompact.union (h.hasCompactSupport.isCompact.image hsh))
          fun u hu => ?_
        have hu1 : h u = 0 := by
          by_contra hne; exact hu (Or.inl (subset_tsupport h hne))
        have hu2 : h (u + x) = 0 := by
          by_contra hne
          exact hu (Or.inr ⟨u + x, subset_tsupport h hne, add_sub_cancel_right u x⟩)
        simp [hu1, hu2]
      exact hc.integrable_of_hasCompactSupport hcs
    have hi : Integrable fun u : ℝ => (g u - g (u + x)) ^ 2 := h_int f
    have hi_low : Integrable fun u : ℝ => (g_low u - g_low (u + x)) ^ 2 := h_int f_low
    have hi_high : Integrable fun u : ℝ => (g_high u - g_high (u + x)) ^ 2 := h_int f_high
    have hpt_u (u : ℝ) :
        (1 - β⁻¹) * (g_low u - g_low (u + x)) ^ 2 +
          (1 - β) * (g_high u - g_high (u + x)) ^ 2 ≤
          (g u - g (u + x)) ^ 2 := by
      have hu1 := criticalTruncatedSource_union V hdisj b u
      have hu2 := criticalTruncatedSource_union V hdisj b (u + x)
      change _ ≤ (criticalTruncatedSource V (S_low ∪ S_high) b u -
        criticalTruncatedSource V (S_low ∪ S_high) b (u + x)) ^ 2
      rw [hu1, hu2]
      set a := g_low u - g_low (u + x)
      set c := g_high u - g_high (u + x)
      have h1 : (a + c - (g_low u + g_high u - (g_low (u + x) + g_high (u + x)))) = 0 := by ring
      rw [show g_low u + g_high u - (g_low (u + x) + g_high (u + x)) = a + c by ring]
      have hsq : 0 ≤ β⁻¹ * (a + β * c) ^ 2 := mul_nonneg (inv_pos.mpr hβ).le (sq_nonneg _)
      have hid : (a + c) ^ 2 - ((1 - β⁻¹) * a ^ 2 + (1 - β) * c ^ 2) = β⁻¹ * (a + β * c) ^ 2 := by
        field_simp [hβ.ne']; ring
      linarith
    have hint_u : (1 - β⁻¹) * (∫ u : ℝ, (g_low u - g_low (u + x)) ^ 2) +
        (1 - β) * (∫ u : ℝ, (g_high u - g_high (u + x)) ^ 2) ≤
        ∫ u : ℝ, (g u - g (u + x)) ^ 2 := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add (hi_low.const_mul (1 - β⁻¹)) (hi_high.const_mul (1 - β))]
      exact integral_mono ((hi_low.const_mul (1 - β⁻¹)).add (hi_high.const_mul (1 - β))) hi hpt_u
    rw [hs, hs_low, hs_high] at hint_u
    linarith
  set F : ℝ → ℝ := fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x
  set F_low : ℝ → ℝ := fun x => (autocorr f_low 0 - autocorr f_low x) * archLevySinhWeight x
  set F_high : ℝ → ℝ := fun x => (autocorr f_high 0 - autocorr f_high x) * archLevySinhWeight x
  obtain ⟨hi_34, hval_34⟩ := integral_Ioc_zero_one_rpow (a := -(3 / 4 : ℝ)) (by norm_num)
  have hIoc : (∫ x in Ioc (0 : ℝ) 1, F_low x + F_high x - F x) ≤
      12 * (γ⁻¹ * K_low ^ 2 + γ * (2 * U * E_high)) := by
    have hpt : ∀ x ∈ Ioc (0 : ℝ) 1, F_low x + F_high x - F x ≤
        (3 * (γ⁻¹ * K_low ^ 2 + γ * (2 * U * E_high))) * x ^ (-(3 / 4 : ℝ)) := by
      intro x hx
      have hx14 : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx.1 _
      have hβ : 0 < γ * x ^ (1 / 4 : ℝ) := mul_pos hγ hx14
      have hj := hjump_beta x hβ
      have hω_nn := (archLevySinhWeight_pos hx.1).le
      have hj_ω := mul_le_mul_of_nonneg_right hj hω_nn
      dsimp only [F, F_low, F_high]
      have hdiff : (autocorr f_low 0 - autocorr f_low x) * archLevySinhWeight x +
          (autocorr f_high 0 - autocorr f_high x) * archLevySinhWeight x -
          (autocorr f 0 - autocorr f x) * archLevySinhWeight x ≤
          ((γ * x ^ (1 / 4 : ℝ))⁻¹ * (autocorr f_low 0 - autocorr f_low x) +
            (γ * x ^ (1 / 4 : ℝ)) * (autocorr f_high 0 - autocorr f_high x)) *
            archLevySinhWeight x := by linarith
      refine hdiff.trans ?_
      rw [hac S_low 0, hac S_low x, hac S_high 0, hac S_high x]
      have hj_low := sourceAutocorrelation_criticalTruncatedSource_jump_le_sqrt hV S_low b hx.1.le hx.2
      obtain ⟨hnn_high, hj_high⟩ := sourceAutocorrelation_criticalTruncatedSource_jump_bounds V S_high b x
      have hnn_low := (sourceAutocorrelation_criticalTruncatedSource_jump_bounds V S_low b x).1
      have hw := archLevySinhWeight_le_three_div hx.1 hx.2
      have h1 : (γ * x ^ (1 / 4 : ℝ))⁻¹ * (sourceAutocorrelation g_low 0 - sourceAutocorrelation g_low x) ≤
          γ⁻¹ * K_low ^ 2 * x ^ (1 / 4 : ℝ) := by
        have hsqrt_eq : Real.sqrt x = x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx.1]; norm_num
        calc (γ * x ^ (1 / 4 : ℝ))⁻¹ * (sourceAutocorrelation g_low 0 - sourceAutocorrelation g_low x)
            ≤ (γ * x ^ (1 / 4 : ℝ))⁻¹ * (K_low ^ 2 * Real.sqrt x) :=
              mul_le_mul_of_nonneg_left hj_low (inv_pos.mpr hβ).le
          _ = γ⁻¹ * K_low ^ 2 * x ^ (1 / 4 : ℝ) := by
              rw [hsqrt_eq, mul_inv]; field_simp [hx14.ne', hγ.ne']
      have h2 : (γ * x ^ (1 / 4 : ℝ)) * (sourceAutocorrelation g_high 0 - sourceAutocorrelation g_high x) ≤
          γ * (2 * U * E_high) * x ^ (1 / 4 : ℝ) := by
        calc (γ * x ^ (1 / 4 : ℝ)) * (sourceAutocorrelation g_high 0 - sourceAutocorrelation g_high x)
            ≤ (γ * x ^ (1 / 4 : ℝ)) * (2 * U * E_high) :=
              mul_le_mul_of_nonneg_left hj_high hβ.le
          _ = γ * (2 * U * E_high) * x ^ (1 / 4 : ℝ) := by ring
      have hrpow_div : x ^ (1 / 4 : ℝ) * (3 / x) = 3 * x ^ (-(3 / 4 : ℝ)) := by
        rw [show 3 / x = 3 * x ^ (-1 : ℝ) by rw [Real.rpow_neg_one]; ring,
          show x ^ (1 / 4 : ℝ) * (3 * x ^ (-1 : ℝ)) = 3 * (x ^ (1 / 4 : ℝ) * x ^ (-1 : ℝ)) by ring,
          ← Real.rpow_add hx.1]
        norm_num
      calc ((γ * x ^ (1 / 4 : ℝ))⁻¹ * (sourceAutocorrelation g_low 0 - sourceAutocorrelation g_low x) +
            (γ * x ^ (1 / 4 : ℝ)) * (sourceAutocorrelation g_high 0 - sourceAutocorrelation g_high x)) *
            archLevySinhWeight x
          ≤ (γ⁻¹ * K_low ^ 2 * x ^ (1 / 4 : ℝ) + γ * (2 * U * E_high) * x ^ (1 / 4 : ℝ)) * (3 / x) :=
            mul_le_mul (add_le_add h1 h2) hw hω_nn (by positivity)
        _ = (γ⁻¹ * K_low ^ 2 + γ * (2 * U * E_high)) * (x ^ (1 / 4 : ℝ) * (3 / x)) := by ring
        _ = (3 * (γ⁻¹ * K_low ^ 2 + γ * (2 * U * E_high))) * x ^ (-(3 / 4 : ℝ)) := by
            rw [hrpow_div]; ring
    calc ∫ x in Ioc (0 : ℝ) 1, F_low x + F_high x - F x
        ≤ ∫ x in Ioc (0 : ℝ) 1,
            (3 * (γ⁻¹ * K_low ^ 2 + γ * (2 * U * E_high))) * x ^ (-(3 / 4 : ℝ)) :=
          setIntegral_mono_on (((hJ_low.add hJ_high).sub hJ).mono_set Ioc_subset_Ioi_self)
            (hi_34.const_mul _) measurableSet_Ioc hpt
      _ = (3 * (γ⁻¹ * K_low ^ 2 + γ * (2 * U * E_high))) *
            ∫ x in Ioc (0 : ℝ) 1, x ^ (-(3 / 4 : ℝ)) := integral_const_mul _ _
      _ = 12 * (γ⁻¹ * K_low ^ 2 + γ * (2 * U * E_high)) := by rw [hval_34]; ring
  have hi_two : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hval_two : (∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ)) = 1 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]; norm_num
  have hIoi : (∫ x in Ioi (1 : ℝ), F_low x + F_high x - F x) ≤
      48 * (γ⁻¹ * (2 * U * E_low) + γ * (2 * U * E_high)) := by
    have hpt : ∀ x ∈ Ioi (1 : ℝ), F_low x + F_high x - F x ≤
        (48 * (γ⁻¹ * (2 * U * E_low) + γ * (2 * U * E_high))) * x ^ (-2 : ℝ) := by
      intro x hx
      have hx0 : 0 < x := lt_trans one_pos hx
      have hj := hjump_beta x hγ
      have hω_nn := (archLevySinhWeight_pos hx0).le
      have hj_ω := mul_le_mul_of_nonneg_right hj hω_nn
      dsimp only [F, F_low, F_high]
      have hdiff : (autocorr f_low 0 - autocorr f_low x) * archLevySinhWeight x +
          (autocorr f_high 0 - autocorr f_high x) * archLevySinhWeight x -
          (autocorr f 0 - autocorr f x) * archLevySinhWeight x ≤
          (γ⁻¹ * (autocorr f_low 0 - autocorr f_low x) +
            γ * (autocorr f_high 0 - autocorr f_high x)) * archLevySinhWeight x := by linarith
      refine hdiff.trans ?_
      rw [hac S_low 0, hac S_low x, hac S_high 0, hac S_high x]
      obtain ⟨_, hj_low⟩ := sourceAutocorrelation_criticalTruncatedSource_jump_bounds V S_low b x
      obtain ⟨_, hj_high⟩ := sourceAutocorrelation_criticalTruncatedSource_jump_bounds V S_high b x
      have hw := archLevySinhWeight_le_fortyEight_rpow_neg_two (le_of_lt hx)
      calc (γ⁻¹ * (sourceAutocorrelation g_low 0 - sourceAutocorrelation g_low x) +
            γ * (sourceAutocorrelation g_high 0 - sourceAutocorrelation g_high x)) *
            archLevySinhWeight x
          ≤ (γ⁻¹ * (2 * U * E_low) + γ * (2 * U * E_high)) * (48 * x ^ (-2 : ℝ)) :=
            mul_le_mul (add_le_add (mul_le_mul_of_nonneg_left hj_low (inv_pos.mpr hγ).le)
              (mul_le_mul_of_nonneg_left hj_high hγ.le)) hw hω_nn (by positivity)
        _ = (48 * (γ⁻¹ * (2 * U * E_low) + γ * (2 * U * E_high))) * x ^ (-2 : ℝ) := by ring
    calc ∫ x in Ioi (1 : ℝ), F_low x + F_high x - F x
        ≤ ∫ x in Ioi (1 : ℝ),
            (48 * (γ⁻¹ * (2 * U * E_low) + γ * (2 * U * E_high))) * x ^ (-2 : ℝ) :=
          setIntegral_mono_on (((hJ_low.add hJ_high).sub hJ).mono_set (Ioi_subset_Ioi zero_le_one))
            (hi_two.const_mul _) measurableSet_Ioi hpt
      _ = (48 * (γ⁻¹ * (2 * U * E_low) + γ * (2 * U * E_high))) *
            ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) := integral_const_mul _ _
      _ = 48 * (γ⁻¹ * (2 * U * E_low) + γ * (2 * U * E_high)) := by rw [hval_two, mul_one]
  have hJ_diff : IntegrableOn (fun x : ℝ => F_low x + F_high x - F x) (Ioi 0) :=
    (hJ_low.add hJ_high).sub hJ
  have htot : (∫ x in Ioi (0 : ℝ), F_low x + F_high x - F x) =
      (∫ x in Ioc (0 : ℝ) 1, F_low x + F_high x - F x) +
        ∫ x in Ioi (1 : ℝ), F_low x + F_high x - F x := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hJ_diff.mono_set Ioc_subset_Ioi_self)
        (hJ_diff.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hlin : (∫ x in Ioi (0 : ℝ), F_low x + F_high x - F x) =
      biScaleLevyEnergy f_low + biScaleLevyEnergy f_high - biScaleLevyEnergy f := by
    calc ∫ x in Ioi (0 : ℝ), F_low x + F_high x - F x
        = (∫ x in Ioi (0 : ℝ), F_low x + F_high x) - ∫ x in Ioi (0 : ℝ), F x :=
          integral_sub (hJ_low.add hJ_high) hJ
      _ = (∫ x in Ioi (0 : ℝ), F_low x) + (∫ x in Ioi (0 : ℝ), F_high x) -
            ∫ x in Ioi (0 : ℝ), F x := by rw [integral_add hJ_low hJ_high]
      _ = biScaleLevyEnergy f_low + biScaleLevyEnergy f_high - biScaleLevyEnergy f := rfl
  have hK_low_sq := criticalTruncatedJumpEnvelopeConstant_sq_le_of_window hL_low hlow b
  have hK_low_bound : 12 * K_low ^ 2 + 96 * U * E_low ≤
      2 * criticalLowWindowLevyConstant L_low * E_low := by
    unfold criticalLowWindowLevyConstant
    linarith [mul_nonneg hU hE_low]
  have hγ_inv : 0 ≤ γ⁻¹ := (inv_pos.mpr hγ).le
  have hlow_err : 12 * (γ⁻¹ * K_low ^ 2) + 48 * (γ⁻¹ * (2 * U * E_low)) ≤
      γ⁻¹ * (2 * criticalLowWindowLevyConstant L_low * E_low) := by
    calc 12 * (γ⁻¹ * K_low ^ 2) + 48 * (γ⁻¹ * (2 * U * E_low))
        = γ⁻¹ * (12 * K_low ^ 2 + 96 * U * E_low) := by ring
      _ ≤ γ⁻¹ * (2 * criticalLowWindowLevyConstant L_low * E_low) :=
          mul_le_mul_of_nonneg_left hK_low_bound hγ_inv
  linarith

/-! ## Section 3: Scale-Free Complete Energy Bounds and Exact Bilinear Schur-Complement Decomposition -/

/-- Exact `ℝ`-valued channel decomposition of `compactFullWeilEnergy (criticalTruncatedTest hV S b)`. -/
theorem compactFullWeilEnergy_criticalTruncatedTest_eq {V : ℝ} (hV : 0 < V) (S : Finset ℕ)
    (b : ℕ → ℝ) :
    compactFullWeilEnergy (criticalTruncatedTest hV S b) =
      biScaleLevyEnergy (criticalTruncatedTest hV S b) +
        EF.gammaBracket 0 * sourceAutocorrelation (criticalTruncatedSource V S b) 0 +
        2 * (criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b) -
        2 * criticalTruncatedPrimeEnergy V S b := by
  have h1 := compactFullWeilEnergy_criticalTruncatedTest hV S b
  unfold criticalTruncatedCompleteEnergy at h1
  rw [sourceLevyEnergy_criticalTruncatedSource_eq_ofReal hV S b, EReal.coe_ennreal_ofReal] at h1
  have hnn : 0 ≤ biScaleLevyEnergy (criticalTruncatedTest hV S b) := by
    unfold biScaleLevyEnergy
    refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
    have hac (y : ℝ) : autocorr (criticalTruncatedTest hV S b) y =
        sourceAutocorrelation (criticalTruncatedSource V S b) y := by
      rw [← autocorr_neg]; unfold sourceAutocorrelation autocorr; simp only [sub_eq_add_neg]; rfl
    rw [hac 0, hac x]
    exact mul_nonneg (sourceAutocorrelation_criticalTruncatedSource_jump_bounds V S b x).1
      (archLevySinhWeight_pos hx).le
  rw [max_eq_left hnn, ← EReal.coe_add] at h1
  have h2 := EReal.coe_eq_coe_iff.mp h1
  linarith

/-- Scale-free total low-window penalty constant
`C_levy(L_low) + C_{Γ,pol} + 2 (C_TW (3 + log L_low) + 650 K_CB)`,
completely independent of the high scale `M₀`, the number of blocks `J`, and the truncation `V`. -/
def criticalLowWindowTotalPenalty (L_low : ℕ) : ℝ :=
  criticalLowWindowLevyConstant L_low +
    criticalAllScaleGammaPolarConstant +
    2 * (criticalTruncatedWindowPrimeSlope * (3 + Real.log L_low) +
      650 * truncatedCrossBlockConstant)

theorem criticalLowWindowTotalPenalty_pos (L_low : ℕ) :
    0 < criticalLowWindowTotalPenalty L_low := by
  unfold criticalLowWindowTotalPenalty
  have h1 := criticalLowWindowLevyConstant_pos L_low
  have h2 := criticalAllScaleGammaPolarConstant_nonneg
  have h3 := criticalTruncatedWindowPrimeSlope_nonneg
  have h4 := truncatedCrossBlockConstant_nonneg
  have h5 : 0 ≤ 3 + Real.log (L_low : ℝ) := by
    rcases Nat.eq_zero_or_pos L_low with rfl | hpos
    · simp
    · have : (1 : ℝ) ≤ L_low := by exact_mod_cast hpos
      have := Real.log_nonneg this
      linarith
  positivity

/-- **Scale-Free Low-Penalty Complete Weil Energy Lower Bound on Low Window + Lacunary Block Family.**
Unlike `compactFullWeilEnergy_criticalTruncatedTest_ge_of_lowWindow_lacunary`, the low-window penalty
`criticalLowWindowTotalPenalty L_low` is completely independent of `M 0`, `J`, and `V ≥ criticalTruncationThreshold`. -/
theorem compactFullWeilEnergy_criticalTruncatedTest_ge_of_lowWindow_lacunary_scaleFree
    {S_low : Finset ℕ} {L_low J : ℕ} (hL_low : 1 ≤ L_low) (hlow : ScaleWindow S_low 1 L_low)
    {M : ℕ → ℕ} {S : ℕ → Finset ℕ} (hlac : IsLacunaryBlockFamily J M S)
    (hsep : L_low ^ 8 ≤ M 0) (b : ℕ → ℝ)
    {V : ℝ} (hVpos : 0 < V) (hV : criticalTruncationThreshold ≤ V) :
    (criticalTruncatedArchLogSlope / 2 * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
        criticalAllScaleGammaPolarConstant -
        2 * (lacunaryPrimeConstant + 100 * truncatedCrossBlockConstant)) *
      (∑ n ∈ (Finset.range J).biUnion S, b n ^ 2) -
    criticalLowWindowTotalPenalty L_low * (∑ n ∈ S_low, b n ^ 2) ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ (Finset.range J).biUnion S) b) := by
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  have hM2 : 2 ≤ M 0 := by have := hlac.1; omega
  have hdisj := disjoint_lowWindow_lacunary hlow hlac hsep
  set S_high := (Finset.range J).biUnion S
  set T := S_low ∪ S_high
  have hE_union : ∑ n ∈ T, b n ^ 2 = (∑ n ∈ S_low, b n ^ 2) + ∑ n ∈ S_high, b n ^ 2 :=
    Finset.sum_union hdisj
  have hlev := biScaleLevyEnergy_criticalTruncatedTest_ge_of_lowWindow_high_scaleFree
    hL_low hlow hdisj b hM2 (fun n hn => hlac.lower hn) hVpos hV
  have hgp := neg_le_criticalTruncatedGammaPolar_all_scales T b hV1
  rw [hE_union] at hgp
  have hP := (abs_le.mp (abs_criticalTruncatedPrimeEnergy_le_of_lowWindow_lacunary hVpos
    hL_low hlow hlac hsep b)).2
  rw [compactFullWeilEnergy_criticalTruncatedTest_eq hVpos T b]
  unfold criticalLowWindowTotalPenalty
  linarith

/-- **Scale-Free Low-Window Archimedean Complete Energy Lower Bound on Low Window + High Window `[M, LM]`.** -/
theorem compactFullWeilEnergy_criticalTruncatedTest_ge_of_lowWindow_window_scaleFree
    {S_low S_high : Finset ℕ} {L_low M L : ℕ} (hL_low : 1 ≤ L_low)
    (hlow : ScaleWindow S_low 1 L_low) (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ)
    (hM : 2 ≤ M) (hL : 1 ≤ L) (hS_low : ∀ n ∈ S_low, n + 1 ≤ L * M)
    (hS_high : ScaleWindow S_high M L)
    {V : ℝ} (hVpos : 0 < V) (hV : criticalTruncationThreshold ≤ V) :
    (criticalTruncatedArchLogSlope / 2 * (Real.log M - criticalTruncatedArchLogOffset) -
        criticalAllScaleGammaPolarConstant -
        2 * criticalTruncatedWindowPrimeSlope * (4 + Real.log L)) *
      (∑ n ∈ S_high, b n ^ 2) -
    (criticalLowWindowLevyConstant L_low +
        criticalAllScaleGammaPolarConstant +
        4 * criticalTruncatedWindowPrimeSlope * (3 + Real.log ((L * M : ℕ) : ℝ)) ^ 2) *
      (∑ n ∈ S_low, b n ^ 2) ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ S_high) b) := by
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  set T := S_low ∪ S_high
  have hE_union : ∑ n ∈ T, b n ^ 2 = (∑ n ∈ S_low, b n ^ 2) + ∑ n ∈ S_high, b n ^ 2 :=
    Finset.sum_union hdisj
  have hlev := biScaleLevyEnergy_criticalTruncatedTest_ge_of_lowWindow_high_scaleFree
    hL_low hlow hdisj b hM (fun n hn => (hS_high n hn).1) hVpos hV
  have hgp := neg_le_criticalTruncatedGammaPolar_all_scales T b hV1
  rw [hE_union] at hgp
  have hP := (abs_le.mp (abs_criticalTruncatedPrimeEnergy_le_of_low_and_window hVpos hdisj
    (by omega) hL hS_low hS_high b)).2
  rw [compactFullWeilEnergy_criticalTruncatedTest_eq hVpos T b]
  linarith

/-- Disjoint union additivity of `criticalTruncatedPolarReadout`. -/
theorem criticalTruncatedPolarReadout_union {V : ℝ} (hV : 0 < V) {S_low S_high : Finset ℕ}
    (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ) :
    criticalTruncatedPolarReadout V (S_low ∪ S_high) b =
      criticalTruncatedPolarReadout V S_low b + criticalTruncatedPolarReadout V S_high b := by
  unfold criticalTruncatedPolarReadout
  have hint (S : Finset ℕ) :
      Integrable fun x : ℝ => criticalTruncatedSource V S b x * Real.exp (x / 2) := by
    set f := criticalTruncatedTest hV S b
    exact (f.continuous.mul (Real.continuous_exp.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  rw [← integral_add (hint S_low) (hint S_high)]
  exact integral_congr_ae (Eventually.of_forall fun x => by
    dsimp only
    rw [criticalTruncatedSource_union V hdisj b x, add_mul])

/-- Disjoint union additivity of `criticalTruncatedPolarEndpoint`. -/
theorem criticalTruncatedPolarEndpoint_union {V : ℝ} (hV : 0 < V) {S_low S_high : Finset ℕ}
    (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ) :
    criticalTruncatedPolarEndpoint V (S_low ∪ S_high) b =
      criticalTruncatedPolarEndpoint V S_low b + criticalTruncatedPolarEndpoint V S_high b := by
  unfold criticalTruncatedPolarEndpoint
  have hint (S : Finset ℕ) :
      Integrable fun x : ℝ => criticalTruncatedSource V S b x * Real.exp (-(x / 2)) := by
    set f := criticalTruncatedTest hV S b
    exact (f.continuous.mul (Real.continuous_exp.comp (continuous_id.div_const 2).neg)).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  rw [← integral_add (hint S_low) (hint S_high)]
  exact integral_congr_ae (Eventually.of_forall fun x => by
    dsimp only
    rw [criticalTruncatedSource_union V hdisj b x, add_mul])

/-- Bilinear `γ`-weighted decomposition of the Gamma + polar channels on `S_low ∪ S_high`. -/
theorem criticalTruncatedGammaPolar_union_ge_of_gamma {V : ℝ} (hV : 1 ≤ V)
    {S_low S_high : Finset ℕ} (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ) {γ : ℝ} (hγ : 0 < γ) :
    (EF.gammaBracket 0 * sourceAutocorrelation (criticalTruncatedSource V S_low b) 0 +
      2 * (criticalTruncatedPolarReadout V S_low b * criticalTruncatedPolarEndpoint V S_low b)) +
    (EF.gammaBracket 0 * sourceAutocorrelation (criticalTruncatedSource V S_high b) 0 +
      2 * (criticalTruncatedPolarReadout V S_high b * criticalTruncatedPolarEndpoint V S_high b)) -
    (γ⁻¹ * (criticalAllScaleGammaPolarConstant * ∑ n ∈ S_low, b n ^ 2) +
      γ * (criticalAllScaleGammaPolarConstant * ∑ n ∈ S_high, b n ^ 2)) ≤
      EF.gammaBracket 0 * sourceAutocorrelation (criticalTruncatedSource V (S_low ∪ S_high) b) 0 +
        2 * (criticalTruncatedPolarReadout V (S_low ∪ S_high) b *
          criticalTruncatedPolarEndpoint V (S_low ∪ S_high) b) := by
  have hV0 : 0 < V := by linarith
  set g := criticalTruncatedSource V (S_low ∪ S_high) b
  set g_low := criticalTruncatedSource V S_low b
  set g_high := criticalTruncatedSource V S_high b
  set E_low := ∑ n ∈ S_low, b n ^ 2
  set E_high := ∑ n ∈ S_high, b n ^ 2
  set U := criticalCollarMassUpper
  have hγ_inv : 0 ≤ γ⁻¹ := (inv_pos.mpr hγ).le
  -- 1. Gamma channel `ac(0)` bilinear bound:
  have hi (S : Finset ℕ) : Integrable fun y : ℝ => criticalTruncatedSource V S b y ^ 2 := by
    set f := criticalTruncatedTest hV0 S b
    have h1 : Integrable fun y : ℝ => f y * f y :=
      (f.continuous.mul f.continuous).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right
    simpa only [sq, criticalTruncatedTest_apply, f] using h1
  have hac_eq (S : Finset ℕ) : sourceAutocorrelation (criticalTruncatedSource V S b) 0 =
      ∫ y : ℝ, criticalTruncatedSource V S b y ^ 2 := by
    unfold sourceAutocorrelation
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only [sub_zero, sq])
  have hac_low_le := sourceAutocorrelation_criticalTruncatedSource_zero_le V S_low b
  have hac_high_le := sourceAutocorrelation_criticalTruncatedSource_zero_le V S_high b
  have hac_diff : |sourceAutocorrelation g 0 - sourceAutocorrelation g_low 0 -
      sourceAutocorrelation g_high 0| ≤
      γ⁻¹ * (U * E_low) + γ * (U * E_high) := by
    have hlow_pt (y : ℝ) :
        (1 - γ⁻¹) * g_low y ^ 2 + (1 - γ) * g_high y ^ 2 ≤ g y ^ 2 := by
      have hu := criticalTruncatedSource_union V hdisj b y
      change _ ≤ (criticalTruncatedSource V (S_low ∪ S_high) b y) ^ 2
      rw [hu]
      have hsq : 0 ≤ γ⁻¹ * (g_low y + γ * g_high y) ^ 2 := mul_nonneg hγ_inv (sq_nonneg _)
      have hid : (g_low y + g_high y) ^ 2 - ((1 - γ⁻¹) * g_low y ^ 2 + (1 - γ) * g_high y ^ 2) =
          γ⁻¹ * (g_low y + γ * g_high y) ^ 2 := by field_simp [hγ.ne']; ring
      linarith
    have hhigh_pt (y : ℝ) :
        g y ^ 2 ≤ (1 + γ⁻¹) * g_low y ^ 2 + (1 + γ) * g_high y ^ 2 := by
      have hu := criticalTruncatedSource_union V hdisj b y
      change (criticalTruncatedSource V (S_low ∪ S_high) b y) ^ 2 ≤ _
      rw [hu]
      have hsq : 0 ≤ γ⁻¹ * (g_low y - γ * g_high y) ^ 2 := mul_nonneg hγ_inv (sq_nonneg _)
      have hid : ((1 + γ⁻¹) * g_low y ^ 2 + (1 + γ) * g_high y ^ 2) - (g_low y + g_high y) ^ 2 =
          γ⁻¹ * (g_low y - γ * g_high y) ^ 2 := by field_simp [hγ.ne']; ring
      linarith
    have hint1 : (1 - γ⁻¹) * sourceAutocorrelation g_low 0 +
        (1 - γ) * sourceAutocorrelation g_high 0 ≤ sourceAutocorrelation g 0 := by
      rw [hac_eq S_low, hac_eq S_high, hac_eq (S_low ∪ S_high),
        ← integral_const_mul, ← integral_const_mul,
        ← integral_add ((hi S_low).const_mul (1 - γ⁻¹)) ((hi S_high).const_mul (1 - γ))]
      exact integral_mono (((hi S_low).const_mul (1 - γ⁻¹)).add ((hi S_high).const_mul (1 - γ)))
        (hi (S_low ∪ S_high)) hlow_pt
    have hint2 : sourceAutocorrelation g 0 ≤
        (1 + γ⁻¹) * sourceAutocorrelation g_low 0 +
        (1 + γ) * sourceAutocorrelation g_high 0 := by
      rw [hac_eq S_low, hac_eq S_high, hac_eq (S_low ∪ S_high),
        ← integral_const_mul, ← integral_const_mul,
        ← integral_add ((hi S_low).const_mul (1 + γ⁻¹)) ((hi S_high).const_mul (1 + γ))]
      exact integral_mono (hi (S_low ∪ S_high))
        (((hi S_low).const_mul (1 + γ⁻¹)).add ((hi S_high).const_mul (1 + γ))) hhigh_pt
    have h1 := mul_le_mul_of_nonneg_left hac_low_le hγ_inv
    have h2 := mul_le_mul_of_nonneg_left hac_high_le hγ.le
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hΩ_bound : |EF.gammaBracket 0 * sourceAutocorrelation g 0 -
      EF.gammaBracket 0 * sourceAutocorrelation g_low 0 -
      EF.gammaBracket 0 * sourceAutocorrelation g_high 0| ≤
      |EF.gammaBracket 0| * (γ⁻¹ * (U * E_low) + γ * (U * E_high)) := by
    rw [show EF.gammaBracket 0 * sourceAutocorrelation g 0 -
        EF.gammaBracket 0 * sourceAutocorrelation g_low 0 -
        EF.gammaBracket 0 * sourceAutocorrelation g_high 0 =
        EF.gammaBracket 0 * (sourceAutocorrelation g 0 - sourceAutocorrelation g_low 0 -
          sourceAutocorrelation g_high 0) by ring, abs_mul]
    exact mul_le_mul_of_nonneg_left hac_diff (abs_nonneg _)
  -- 2. Polar channel bilinear bound:
  set a := criticalTruncatedReadoutConstant
  set c := criticalTruncatedEndpointConstant
  set T_low := ∑ n ∈ S_low, |b n| / ((n + 1 : ℕ) : ℝ)
  set T_high := ∑ n ∈ S_high, |b n| / ((n + 1 : ℕ) : ℝ)
  have ha : 0 ≤ a := by
    unfold a criticalTruncatedReadoutConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarWeight v| := integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    have : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
    positivity
  have hc : 0 ≤ c := by
    unfold c criticalTruncatedEndpointConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v| :=
      integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    positivity
  have hT_low : 0 ≤ T_low := Finset.sum_nonneg fun n _ => by positivity
  have hT_high : 0 ≤ T_high := Finset.sum_nonneg fun n _ => by positivity
  have hR_low := abs_criticalTruncatedPolarReadout_le hV0 S_low b
  have hE_low := abs_criticalTruncatedPolarEndpoint_le hV S_low b
  have hR_high := abs_criticalTruncatedPolarReadout_le hV0 S_high b
  have hE_high := abs_criticalTruncatedPolarEndpoint_le hV S_high b
  have hT2_low := sq_sum_abs_div_succ_le_pi_sq_div_six S_low b
  have hT2_high := sq_sum_abs_div_succ_le_pi_sq_div_six S_high b
  have hpol_cross1 : |criticalTruncatedPolarReadout V S_low b *
      criticalTruncatedPolarEndpoint V S_high b| ≤ 144 * a * c * (T_low * T_high) := by
    rw [abs_mul]
    calc |criticalTruncatedPolarReadout V S_low b| * |criticalTruncatedPolarEndpoint V S_high b|
        ≤ (a * (12 * T_low)) * (c * (12 * T_high)) :=
          mul_le_mul hR_low hE_high (abs_nonneg _) (by positivity)
      _ = 144 * a * c * (T_low * T_high) := by ring
  have hpol_cross2 : |criticalTruncatedPolarReadout V S_high b *
      criticalTruncatedPolarEndpoint V S_low b| ≤ 144 * a * c * (T_low * T_high) := by
    rw [abs_mul]
    calc |criticalTruncatedPolarReadout V S_high b| * |criticalTruncatedPolarEndpoint V S_low b|
        ≤ (a * (12 * T_high)) * (c * (12 * T_low)) :=
          mul_le_mul hR_high hE_low (abs_nonneg _) (by positivity)
      _ = 144 * a * c * (T_low * T_high) := by ring
  have hyoung : 2 * (T_low * T_high) ≤ γ⁻¹ * T_low ^ 2 + γ * T_high ^ 2 := by
    have hsq : 0 ≤ γ⁻¹ * (T_low - γ * T_high) ^ 2 := mul_nonneg hγ_inv (sq_nonneg _)
    have hid : (γ⁻¹ * T_low ^ 2 + γ * T_high ^ 2) - 2 * (T_low * T_high) =
        γ⁻¹ * (T_low - γ * T_high) ^ 2 := by field_simp [hγ.ne']; ring
    linarith
  have hpol_diff : |2 * (criticalTruncatedPolarReadout V (S_low ∪ S_high) b *
      criticalTruncatedPolarEndpoint V (S_low ∪ S_high) b) -
      2 * (criticalTruncatedPolarReadout V S_low b * criticalTruncatedPolarEndpoint V S_low b) -
      2 * (criticalTruncatedPolarReadout V S_high b * criticalTruncatedPolarEndpoint V S_high b)| ≤
      γ⁻¹ * (48 * Real.pi ^ 2 * a * c * E_low) +
        γ * (48 * Real.pi ^ 2 * a * c * E_high) := by
    rw [criticalTruncatedPolarReadout_union hV0 hdisj b,
      criticalTruncatedPolarEndpoint_union hV0 hdisj b,
      show 2 * ((criticalTruncatedPolarReadout V S_low b + criticalTruncatedPolarReadout V S_high b) *
        (criticalTruncatedPolarEndpoint V S_low b + criticalTruncatedPolarEndpoint V S_high b)) -
        2 * (criticalTruncatedPolarReadout V S_low b * criticalTruncatedPolarEndpoint V S_low b) -
        2 * (criticalTruncatedPolarReadout V S_high b * criticalTruncatedPolarEndpoint V S_high b) =
        2 * (criticalTruncatedPolarReadout V S_low b * criticalTruncatedPolarEndpoint V S_high b) +
          2 * (criticalTruncatedPolarReadout V S_high b * criticalTruncatedPolarEndpoint V S_low b) by ring]
    have htri := abs_add_le
      (2 * (criticalTruncatedPolarReadout V S_low b * criticalTruncatedPolarEndpoint V S_high b))
      (2 * (criticalTruncatedPolarReadout V S_high b * criticalTruncatedPolarEndpoint V S_low b))
    have hc1 : |2 * (criticalTruncatedPolarReadout V S_low b *
        criticalTruncatedPolarEndpoint V S_high b)| ≤ 288 * a * c * (T_low * T_high) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [hpol_cross1]
    have hc2 : |2 * (criticalTruncatedPolarReadout V S_high b *
        criticalTruncatedPolarEndpoint V S_low b)| ≤ 288 * a * c * (T_low * T_high) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [hpol_cross2]
    have h1 := mul_le_mul_of_nonneg_left hyoung (show 0 ≤ 288 * a * c by positivity)
    have h2 := mul_le_mul_of_nonneg_left hT2_low (show 0 ≤ 288 * a * c * γ⁻¹ by positivity)
    have h3 := mul_le_mul_of_nonneg_left hT2_high (show 0 ≤ 288 * a * c * γ by positivity)
    dsimp only [T_low, T_high, E_low, E_high] at h1 h2 h3 ⊢
    linarith [htri, hc1, hc2, h1, h2, h3]
  have hΩ_low := (abs_le.mp hΩ_bound).1
  have hpol_low := (abs_le.mp hpol_diff).1
  unfold criticalAllScaleGammaPolarConstant
  dsimp only [g, g_low, g_high, E_low, E_high, U, a, c] at hΩ_low hpol_low ⊢
  linarith

/-- Bilinear `γ`-weighted prime cross-coupling bound between a low window `ScaleWindow S_low 1 L_low`
and a high lacunary block family `IsLacunaryBlockFamily J M S` (`L_low ^ 8 ≤ M 0`). -/
theorem abs_truncatedBlockCoupling_add_symm_le_of_lowWindow_lacunary_gamma {V : ℝ} (hV : 0 < V)
    {S_low : Finset ℕ} {L_low J : ℕ} (hlow : ScaleWindow S_low 1 L_low)
    {M : ℕ → ℕ} {S : ℕ → Finset ℕ} (hlac : IsLacunaryBlockFamily J M S)
    (hsep : L_low ^ 8 ≤ M 0) (b : ℕ → ℝ) {γ : ℝ} (hγ : 0 < γ) :
    2 * |truncatedBlockCoupling V S_low ((Finset.range J).biUnion S) b +
      truncatedBlockCoupling V ((Finset.range J).biUnion S) S_low b| ≤
      γ⁻¹ * (1300 * truncatedCrossBlockConstant * ∑ n ∈ S_low, b n ^ 2) +
        γ * (200 * truncatedCrossBlockConstant * ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2) := by
  set I := Finset.range J
  set J_low := lowDyadicIndices L_low
  set S_high := I.biUnion S
  set K := truncatedCrossBlockConstant
  have hK : 0 ≤ K := truncatedCrossBlockConstant_nonneg
  set X_low : ℕ → ℝ := fun k => ∑ n ∈ dyadicSlice S_low k, b n ^ 2
  set s_low : ℕ → ℝ := fun k => Real.sqrt (X_low k)
  set w_low : ℕ → ℝ := fun k => (((2 ^ k : ℕ) : ℝ) ^ (1 / 16 : ℝ))⁻¹
  set X : ℕ → ℝ := fun i => ∑ n ∈ S i, b n ^ 2
  set s : ℕ → ℝ := fun i => Real.sqrt (X i)
  set w : ℕ → ℝ := fun i => ((M i : ℝ) ^ (1 / 16 : ℝ))⁻¹
  have hX_low (k : ℕ) : 0 ≤ X_low k := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hX (i : ℕ) : 0 ≤ X i := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd_low := pairwiseDisjoint_dyadicSlice S_low (J_low : Set ℕ)
  have hd := hlac.pairwiseDisjoint
  have hbi_low := biUnion_dyadicSlice_lowDyadicIndices hlow
  set E_low := ∑ n ∈ S_low, b n ^ 2
  set E_high := ∑ n ∈ S_high, b n ^ 2
  have hE_low_eq : E_low = ∑ k ∈ J_low, X_low k := by
    calc E_low = ∑ n ∈ J_low.biUnion (dyadicSlice S_low), b n ^ 2 := by
          dsimp only [E_low, J_low]; rw [hbi_low]
      _ = ∑ k ∈ J_low, X_low k := Finset.sum_biUnion hd_low
  have hE_high_eq : E_high = ∑ i ∈ I, X i := Finset.sum_biUnion hd
  have hpair : ∀ k ∈ J_low, ∀ i ∈ I,
      |truncatedBlockCoupling V (dyadicSlice S_low k) (S i) b| ≤
        50 * K * (w_low k * s_low k) * (w i * s i) ∧
      |truncatedBlockCoupling V (S i) (dyadicSlice S_low k) b| ≤
        50 * K * (w_low k * s_low k) * (w i * s i) := by
    intro k hk i hi
    have hi_lt := Finset.mem_range.mp hi
    have hk_le : 2 ^ k ≤ L_low := (Finset.mem_filter.mp hk).2
    have hM0_le : M 0 ≤ M i := by
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact le_rfl
      · exact hlac.le_of_lt hpos hi_lt
    have hpow : (2 ^ k) ^ 8 ≤ M i :=
      (Nat.pow_le_pow_left hk_le 8).trans (hsep.trans hM0_le)
    have h2k_1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hMi_1 : 1 ≤ M i := by have := hlac.three_le i hi_lt; omega
    have h1 := abs_truncatedBlockCoupling_le_of_pow_le hV (dyadicScaleBlock_dyadicSlice S_low k)
      (hlac.2.2 i hi_lt) h2k_1 hMi_1 (Or.inl hpow) b
    have h2 := abs_truncatedBlockCoupling_le_of_pow_le hV (hlac.2.2 i hi_lt)
      (dyadicScaleBlock_dyadicSlice S_low k) hMi_1 h2k_1 (Or.inr hpow) b
    refine ⟨h1.trans (le_of_eq ?_), h2.trans (le_of_eq ?_)⟩
    · simp only [w_low, s_low, X_low, w, s, X, K]; ring
    · simp only [w_low, s_low, X_low, w, s, X, K]; ring
  set A_low := ∑ k ∈ J_low, w_low k * s_low k
  set B_high := ∑ i ∈ I, w i * s i
  have hbi1 (k : ℕ) : truncatedBlockCoupling V (dyadicSlice S_low k) S_high b =
      ∑ i ∈ I, truncatedBlockCoupling V (dyadicSlice S_low k) (S i) b :=
    truncatedBlockCoupling_biUnion_right V (dyadicSlice S_low k) hd b
  have hbi2 (k : ℕ) : truncatedBlockCoupling V S_high (dyadicSlice S_low k) b =
      ∑ i ∈ I, truncatedBlockCoupling V (S i) (dyadicSlice S_low k) b :=
    truncatedBlockCoupling_biUnion_left V hd (dyadicSlice S_low k) b
  have hcross1 : |truncatedBlockCoupling V S_low S_high b| ≤ 50 * K * A_low * B_high := by
    rw [← hbi_low, truncatedBlockCoupling_biUnion_left V hd_low S_high b]
    simp_rw [hbi1]
    calc |∑ k ∈ J_low, ∑ i ∈ I, truncatedBlockCoupling V (dyadicSlice S_low k) (S i) b|
        ≤ ∑ k ∈ J_low, ∑ i ∈ I, |truncatedBlockCoupling V (dyadicSlice S_low k) (S i) b| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
            Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ k ∈ J_low, ∑ i ∈ I, 50 * K * (w_low k * s_low k) * (w i * s i) :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun i hi => (hpair k hk i hi).1
      _ = 50 * K * A_low * B_high := by
          dsimp only [A_low, B_high]
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hcross2 : |truncatedBlockCoupling V S_high S_low b| ≤ 50 * K * A_low * B_high := by
    rw [← hbi_low, truncatedBlockCoupling_biUnion_right V S_high hd_low b]
    simp_rw [hbi2]
    calc |∑ k ∈ J_low, ∑ i ∈ I, truncatedBlockCoupling V (S i) (dyadicSlice S_low k) b|
        ≤ ∑ k ∈ J_low, ∑ i ∈ I, |truncatedBlockCoupling V (S i) (dyadicSlice S_low k) b| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
            Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ k ∈ J_low, ∑ i ∈ I, 50 * K * (w_low k * s_low k) * (w i * s i) :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun i hi => (hpair k hk i hi).2
      _ = 50 * K * A_low * B_high := by
          dsimp only [A_low, B_high]
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hA_sq : A_low ^ 2 ≤ 13 * E_low := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq J_low w_low s_low
    have hs2 : ∑ k ∈ J_low, s_low k ^ 2 = E_low := by
      rw [hE_low_eq]
      exact Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hX_low k)
    rw [hs2] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_right (sum_lowDyadicIndices_weight_sq_le L_low)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hB_sq : B_high ^ 2 ≤ 2 * E_high := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq I w s
    have hs2 : ∑ i ∈ I, s i ^ 2 = E_high := by
      rw [hE_high_eq]
      exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hX i)
    rw [hs2] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_right hlac.sum_weight_sq_le
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hγ_inv : 0 ≤ γ⁻¹ := (inv_pos.mpr hγ).le
  have hyoung : 200 * K * A_low * B_high ≤ 100 * K * (γ⁻¹ * A_low ^ 2 + γ * B_high ^ 2) := by
    have hsq : 0 ≤ 100 * K * γ⁻¹ * (A_low - γ * B_high) ^ 2 := by positivity
    have hid : 100 * K * (γ⁻¹ * A_low ^ 2 + γ * B_high ^ 2) - 200 * K * A_low * B_high =
        100 * K * γ⁻¹ * (A_low - γ * B_high) ^ 2 := by field_simp [hγ.ne']; ring
    linarith
  have h1 := mul_le_mul_of_nonneg_left hA_sq (show 0 ≤ 100 * K * γ⁻¹ by positivity)
  have h2 := mul_le_mul_of_nonneg_left hB_sq (show 0 ≤ 100 * K * γ by positivity)
  have htri := abs_add_le (truncatedBlockCoupling V S_low S_high b)
    (truncatedBlockCoupling V S_high S_low b)
  linarith

/-- Scale-free low-window Schur coupling constant
`2 C_levy(L_low) + C_{Γ,pol} + 1300 K_CB`. -/
def criticalSchurLowConstant (L_low : ℕ) : ℝ :=
  2 * criticalLowWindowLevyConstant L_low +
    criticalAllScaleGammaPolarConstant +
    1300 * truncatedCrossBlockConstant

theorem criticalSchurLowConstant_pos (L_low : ℕ) : 0 < criticalSchurLowConstant L_low := by
  unfold criticalSchurLowConstant
  have := criticalLowWindowLevyConstant_pos L_low
  have := criticalAllScaleGammaPolarConstant_nonneg
  have := truncatedCrossBlockConstant_nonneg
  positivity

/-- Scale-free high-block Schur coupling constant
`120 U + C_{Γ,pol} + 200 K_CB`. -/
def criticalSchurHighConstant : ℝ :=
  120 * criticalCollarMassUpper +
    criticalAllScaleGammaPolarConstant +
    200 * truncatedCrossBlockConstant

theorem criticalSchurHighConstant_pos : 0 < criticalSchurHighConstant := by
  unfold criticalSchurHighConstant
  have hU : 0 < criticalCollarMassUpper := by
    unfold criticalCollarMassUpper; have := factorialUnitIntervalUpper_pos; positivity
  have := criticalAllScaleGammaPolarConstant_nonneg
  have := truncatedCrossBlockConstant_nonneg
  positivity

/-- **Exact Bilinear `γ`-Weighted Schur-Complement Decomposition of the Complete Weil Functional.**
For every truncation `V ≥ 1`, every low window `ScaleWindow S_low 1 L_low` (`1 ≤ L_low`),
every high lacunary block family `IsLacunaryBlockFamily J M S` with `L_low ^ 8 ≤ M 0`,
every coefficient vector `b : ℕ → ℝ`, and every `γ > 0`, the complete Weil energy of the two-band
source retains 100% of both diagonal Weil energies up to the scale-free bilinear cross-defect
`γ⁻¹ * C_{Schur,low}(L_low) E_low + γ * C_{Schur,high} E_high`. -/
theorem compactFullWeilEnergy_criticalTruncatedTest_schur_gamma {V : ℝ} (hVpos : 0 < V) (hV : 1 ≤ V)
    {S_low : Finset ℕ} {L_low J : ℕ} (hL_low : 1 ≤ L_low) (hlow : ScaleWindow S_low 1 L_low)
    {M : ℕ → ℕ} {S : ℕ → Finset ℕ} (hlac : IsLacunaryBlockFamily J M S)
    (hsep : L_low ^ 8 ≤ M 0) (b : ℕ → ℝ) {γ : ℝ} (hγ : 0 < γ) :
    compactFullWeilEnergy (criticalTruncatedTest hVpos S_low b) +
      compactFullWeilEnergy (criticalTruncatedTest hVpos ((Finset.range J).biUnion S) b) -
      (γ⁻¹ * (criticalSchurLowConstant L_low * ∑ n ∈ S_low, b n ^ 2) +
        γ * (criticalSchurHighConstant * ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2)) ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ (Finset.range J).biUnion S) b) := by
  have hdisj := disjoint_lowWindow_lacunary hlow hlac hsep
  set S_high := (Finset.range J).biUnion S
  have hlev := biScaleLevyEnergy_union_ge_of_gamma hVpos hV hL_low hlow hdisj b hγ
  have hgp := criticalTruncatedGammaPolar_union_ge_of_gamma hV hdisj b hγ
  have hP_union := criticalTruncatedPrimeEnergy_union hVpos hdisj b
  have hP_cross := abs_truncatedBlockCoupling_add_symm_le_of_lowWindow_lacunary_gamma
    hVpos hlow hlac hsep b hγ
  have hP_low : -(2 * |truncatedBlockCoupling V S_low S_high b +
      truncatedBlockCoupling V S_high S_low b|) ≤
      -2 * (truncatedBlockCoupling V S_low S_high b +
        truncatedBlockCoupling V S_high S_low b) := by
    have := le_abs_self (truncatedBlockCoupling V S_low S_high b +
      truncatedBlockCoupling V S_high S_low b)
    linarith
  rw [compactFullWeilEnergy_criticalTruncatedTest_eq hVpos S_low b,
    compactFullWeilEnergy_criticalTruncatedTest_eq hVpos S_high b,
    compactFullWeilEnergy_criticalTruncatedTest_eq hVpos (S_low ∪ S_high) b,
    hP_union]
  unfold criticalSchurLowConstant criticalSchurHighConstant
  linarith

/-- If `∑ n ∈ S, b n ^ 2 = 0`, then `criticalTruncatedSource V S b` vanishes identically and its
complete Weil energy is `0`. -/
theorem compactFullWeilEnergy_criticalTruncatedTest_eq_zero_of_sum_sq_eq_zero
    {V : ℝ} (hVpos : 0 < V) {S : Finset ℕ} {b : ℕ → ℝ} (h0 : ∑ n ∈ S, b n ^ 2 = 0) :
    (∀ x, criticalTruncatedSource V S b x = 0) ∧
    compactFullWeilEnergy (criticalTruncatedTest hVpos S b) = 0 := by
  have hb0 : ∀ n ∈ S, b n = 0 := by
    intro n hn
    have hsq0 : b n ^ 2 = 0 :=
      le_antisymm ((Finset.single_le_sum (fun k _ => sq_nonneg (b k)) hn).trans h0.le) (sq_nonneg _)
    exact sq_eq_zero_iff.mp hsq0
  have hsrc : ∀ x, criticalTruncatedSource V S b x = 0 := by
    intro x
    rw [criticalTruncatedSource_eq]
    have hph : realPhaseCombination S b (Real.exp (-x)) = 0 := by
      unfold realPhaseCombination
      exact Finset.sum_eq_zero fun n hn => by rw [hb0 n hn, zero_mul]
    rw [hph, mul_zero, mul_zero, mul_zero]
  refine ⟨hsrc, ?_⟩
  have hac0 (x : ℝ) : sourceAutocorrelation (criticalTruncatedSource V S b) x = 0 := by
    unfold sourceAutocorrelation
    simp [hsrc]
  have hac_f (x : ℝ) : autocorr (criticalTruncatedTest hVpos S b) x = 0 := by
    rw [← autocorr_neg]
    unfold autocorr
    simp [criticalTruncatedTest_apply, hsrc]
  have hlev0 : biScaleLevyEnergy (criticalTruncatedTest hVpos S b) = 0 := by
    unfold biScaleLevyEnergy
    simp [hac_f]
  have hR0 : criticalTruncatedPolarReadout V S b = 0 := by
    unfold criticalTruncatedPolarReadout
    simp [hsrc]
  have hP0 : criticalTruncatedPrimeEnergy V S b = 0 := by
    unfold criticalTruncatedPrimeEnergy criticalTruncatedPrimeAtom
    simp [hsrc]
  rw [compactFullWeilEnergy_criticalTruncatedTest_eq hVpos S b, hlev0, hac0 0, hR0, hP0]
  ring

/-- If `∑ n ∈ S_low, b n ^ 2 = 0` and `Disjoint S_low S_high`, then
`compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ S_high) b) = compactFullWeilEnergy (criticalTruncatedTest hVpos S_high b)`. -/
private theorem compactFullWeilEnergy_union_eq_right_of_sum_sq_eq_zero
    {V : ℝ} (hVpos : 0 < V) {S_low S_high : Finset ℕ} (hdisj : Disjoint S_low S_high)
    {b : ℕ → ℝ} (h0 : ∑ n ∈ S_low, b n ^ 2 = 0) :
    compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ S_high) b) =
      compactFullWeilEnergy (criticalTruncatedTest hVpos S_high b) := by
  have hsrc := (compactFullWeilEnergy_criticalTruncatedTest_eq_zero_of_sum_sq_eq_zero hVpos h0).1
  congr 1
  ext x
  change criticalTruncatedSource V (S_low ∪ S_high) b x = criticalTruncatedSource V S_high b x
  rw [criticalTruncatedSource_union V hdisj b x, hsrc x, zero_add]

/-- **Exact Off-Diagonal Cauchy–Schwarz Schur-Complement Inequality (`2 √(C_low C_high) √(E_low E_high)`).** -/
theorem compactFullWeilEnergy_criticalTruncatedTest_schur_sqrt {V : ℝ} (hVpos : 0 < V) (hV : 1 ≤ V)
    {S_low : Finset ℕ} {L_low J : ℕ} (hL_low : 1 ≤ L_low) (hlow : ScaleWindow S_low 1 L_low)
    {M : ℕ → ℕ} {S : ℕ → Finset ℕ} (hlac : IsLacunaryBlockFamily J M S)
    (hsep : L_low ^ 8 ≤ M 0) (b : ℕ → ℝ) :
    compactFullWeilEnergy (criticalTruncatedTest hVpos S_low b) +
      compactFullWeilEnergy (criticalTruncatedTest hVpos ((Finset.range J).biUnion S) b) -
      2 * Real.sqrt (criticalSchurLowConstant L_low * criticalSchurHighConstant) *
        Real.sqrt ((∑ n ∈ S_low, b n ^ 2) * ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2) ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ (Finset.range J).biUnion S) b) := by
  have hdisj := disjoint_lowWindow_lacunary hlow hlac hsep
  set S_high := (Finset.range J).biUnion S
  set E_low := ∑ n ∈ S_low, b n ^ 2
  set E_high := ∑ n ∈ S_high, b n ^ 2
  set A := criticalSchurLowConstant L_low * E_low
  set B := criticalSchurHighConstant * E_high
  have hC_low := criticalSchurLowConstant_pos L_low
  have hC_high := criticalSchurHighConstant_pos
  have hE_low_nn : 0 ≤ E_low := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE_high_nn : 0 ≤ E_high := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases eq_or_lt_of_le hE_low_nn with hE_low0 | hE_low_pos
  · have h1 := (compactFullWeilEnergy_criticalTruncatedTest_eq_zero_of_sum_sq_eq_zero hVpos hE_low0.symm).2
    have h2 := compactFullWeilEnergy_union_eq_right_of_sum_sq_eq_zero hVpos hdisj hE_low0.symm
    have hsqrt0 : Real.sqrt (E_low * E_high) = 0 := by rw [← hE_low0, zero_mul, Real.sqrt_zero]
    rw [h1, h2, hsqrt0]
    linarith
  · rcases eq_or_lt_of_le hE_high_nn with hE_high0 | hE_high_pos
    · have h1 := (compactFullWeilEnergy_criticalTruncatedTest_eq_zero_of_sum_sq_eq_zero hVpos hE_high0.symm).2
      have h2 := compactFullWeilEnergy_union_eq_right_of_sum_sq_eq_zero hVpos hdisj.symm hE_high0.symm
      rw [Finset.union_comm] at h2
      have hsqrt0 : Real.sqrt (E_low * E_high) = 0 := by rw [← hE_high0, mul_zero, Real.sqrt_zero]
      rw [h1, h2, hsqrt0]
      linarith
    · have hA : 0 < A := mul_pos hC_low hE_low_pos
      have hB : 0 < B := mul_pos hC_high hE_high_pos
      set γ := Real.sqrt (A / B)
      have hγ : 0 < γ := Real.sqrt_pos.mpr (div_pos hA hB)
      have hschur := compactFullWeilEnergy_criticalTruncatedTest_schur_gamma
        hVpos hV hL_low hlow hlac hsep b hγ
      have hγ_eq : γ⁻¹ * A + γ * B =
          2 * Real.sqrt (criticalSchurLowConstant L_low * criticalSchurHighConstant) *
            Real.sqrt (E_low * E_high) := by
        have h1 : γ = Real.sqrt A / Real.sqrt B := Real.sqrt_div hA.le B
        have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
        have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
        have hsqA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
        have hsqB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB.le
        have h2 : γ⁻¹ * A + γ * B = 2 * (Real.sqrt A * Real.sqrt B) := by
          rw [h1, inv_div]
          calc Real.sqrt B / Real.sqrt A * A + Real.sqrt A / Real.sqrt B * B
              = Real.sqrt B / Real.sqrt A * Real.sqrt A ^ 2 +
                  Real.sqrt A / Real.sqrt B * Real.sqrt B ^ 2 := by rw [hsqA, hsqB]
            _ = 2 * (Real.sqrt A * Real.sqrt B) := by
                field_simp [hsA.ne', hsB.ne']; ring
        rw [h2, ← Real.sqrt_mul hA.le,
          show A * B = (criticalSchurLowConstant L_low * criticalSchurHighConstant) *
            (E_low * E_high) by dsimp only [A, B]; ring,
          Real.sqrt_mul (mul_pos hC_low hC_high).le]
        ring
      dsimp only [A, B, E_low, E_high, S_high] at hγ_eq
      linarith

/-- **Unconditional Schur-Complement Positivity from Any Low-Mode Certificate (`μ_low > 0`).**
If `μ_low * E_low ≤ compactFullWeilEnergy (criticalTruncatedTest hVpos S_low b)` with `0 < μ_low`,
and the high lacunary block family satisfies the explicit Schur-complement threshold
`2 * C_{Schur,low}(L_low) * C_{Schur,high} / μ_low + μ_low / 2 ≤ s_T (log(M 0) - c_T) - C_{Γ,pol} - 2 C_lac`,
then `μ_low / 2 * (E_low + E_high) ≤ compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ S_high) b)`,
which is strictly positive whenever `∃ n ∈ S_low ∪ S_high, b n ≠ 0`. -/
theorem compactFullWeilEnergy_pos_of_lowMode_certificate_and_schur_complement
    {V : ℝ} (hVpos : 0 < V) (hV : criticalTruncationThreshold ≤ V)
    {S_low : Finset ℕ} {L_low J : ℕ} (hL_low : 1 ≤ L_low) (hlow : ScaleWindow S_low 1 L_low)
    {M : ℕ → ℕ} {S : ℕ → Finset ℕ} (hlac : IsLacunaryBlockFamily J M S)
    (hsep : L_low ^ 8 ≤ M 0) (b : ℕ → ℝ)
    {μ_low : ℝ} (hμ_low : 0 < μ_low)
    (hcert : μ_low * (∑ n ∈ S_low, b n ^ 2) ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos S_low b))
    (hM_schur : 2 * criticalSchurLowConstant L_low * criticalSchurHighConstant / μ_low + μ_low / 2 ≤
      criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
        criticalAllScaleGammaPolarConstant - 2 * lacunaryPrimeConstant) :
    μ_low / 2 * ((∑ n ∈ S_low, b n ^ 2) + ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2) ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ (Finset.range J).biUnion S) b) ∧
    ((∃ n ∈ S_low ∪ (Finset.range J).biUnion S, b n ≠ 0) →
      0 < compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ (Finset.range J).biUnion S) b)) := by
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  have hM2 : 2 ≤ M 0 := by have := hlac.1; omega
  set S_high := (Finset.range J).biUnion S
  set E_low := ∑ n ∈ S_low, b n ^ 2
  set E_high := ∑ n ∈ S_high, b n ^ 2
  have hE_low_nn : 0 ≤ E_low := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE_high_nn : 0 ≤ E_high := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- High-band diagonal lower bound:
  have hhigh_lev_er := ofReal_le_criticalTruncatedLevyEnergy S_high b hM2
    (fun n hn => hlac.lower hn) hV
  rw [sourceLevyEnergy_criticalTruncatedSource_eq_ofReal hVpos S_high b] at hhigh_lev_er
  have hhigh_lev_nn : 0 ≤ biScaleLevyEnergy (criticalTruncatedTest hVpos S_high b) := by
    unfold biScaleLevyEnergy
    refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
    have hac (y : ℝ) : autocorr (criticalTruncatedTest hVpos S_high b) y =
        sourceAutocorrelation (criticalTruncatedSource V S_high b) y := by
      rw [← autocorr_neg]; unfold sourceAutocorrelation autocorr; simp only [sub_eq_add_neg]; rfl
    rw [hac 0, hac x]
    exact mul_nonneg (sourceAutocorrelation_criticalTruncatedSource_jump_bounds V S_high b x).1
      (archLevySinhWeight_pos hx).le
  have hhigh_lev : criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) *
      E_high ≤ biScaleLevyEnergy (criticalTruncatedTest hVpos S_high b) := by
    rcases le_or_gt (criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) *
        E_high) 0 with hnp | hpos
    · exact hnp.trans hhigh_lev_nn
    · exact (ENNReal.ofReal_le_ofReal_iff hhigh_lev_nn).mp hhigh_lev_er
  have hhigh_gp := neg_le_criticalTruncatedGammaPolar_all_scales S_high b hV1
  have hhigh_P := (abs_le.mp (abs_criticalTruncatedPrimeEnergy_le_of_lacunary hVpos hlac b)).2
  have hhigh_tot : (criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
      criticalAllScaleGammaPolarConstant - 2 * lacunaryPrimeConstant) * E_high ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos S_high b) := by
    rw [compactFullWeilEnergy_criticalTruncatedTest_eq hVpos S_high b]
    dsimp only [E_high] at hhigh_lev hhigh_gp hhigh_P ⊢
    linarith
  -- Choose `γ = 2 * C_{Schur,low}(L_low) / μ_low`:
  set γ := 2 * criticalSchurLowConstant L_low / μ_low
  have hC_low := criticalSchurLowConstant_pos L_low
  have hγ : 0 < γ := div_pos (by positivity) hμ_low
  have hschur := compactFullWeilEnergy_criticalTruncatedTest_schur_gamma
    hVpos hV1 hL_low hlow hlac hsep b hγ
  have hγ_low : γ⁻¹ * (criticalSchurLowConstant L_low * E_low) = μ_low / 2 * E_low := by
    dsimp only [γ]
    field_simp [hC_low.ne', hμ_low.ne']
  have hγ_high : γ * (criticalSchurHighConstant * E_high) =
      (2 * criticalSchurLowConstant L_low * criticalSchurHighConstant / μ_low) * E_high := by
    dsimp only [γ]; ring
  have hhigh_margin := mul_le_mul_of_nonneg_right hM_schur hE_high_nn
  have hmain : μ_low / 2 * (E_low + E_high) ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ S_high) b) := by
    dsimp only [E_low, E_high, S_high] at hγ_low hγ_high hhigh_tot hhigh_margin hcert ⊢
    linarith
  refine ⟨hmain, fun ⟨n, hn, hbn⟩ => ?_⟩
  have hdisj := disjoint_lowWindow_lacunary hlow hlac hsep
  have hsum_pos : 0 < E_low + E_high := by
    rw [← Finset.sum_union hdisj]
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hbn)
      (Finset.single_le_sum (fun k _ => sq_nonneg (b k)) hn)
  exact lt_of_lt_of_le (mul_pos (by positivity) hsum_pos) hmain

/-! ## Section 4: Unconditional Positivity of Coupled Low–High Sources and Dominance Cones Across All Five Form Realizations -/

/-- Logarithmic target for the base scale `M 0` of a high lacunary block family to dominate a
low window `[1, L_low]` on the dominance cone `E_low ≤ Λ E_high` with margin `(s_T / 4) log(M 0) E_high`. -/
def coupledLowHighLacunaryLogTarget (L_low : ℕ) (Λ : ℝ) : ℝ :=
  4 / criticalTruncatedArchLogSlope *
    (criticalTruncatedArchLogSlope / 2 * criticalTruncatedArchLogOffset +
      criticalAllScaleGammaPolarConstant +
      2 * (lacunaryPrimeConstant + 100 * truncatedCrossBlockConstant) +
      criticalLowWindowTotalPenalty L_low * max Λ 0)

/-- Explicit closed-form base-scale threshold `M₀(L_low, Λ)` for coupled low–high positivity,
completely determined by `L_low` and the low-to-high energy ratio `Λ`. -/
def coupledLowHighLacunaryThreshold (L_low : ℕ) (Λ : ℝ) : ℕ :=
  max (max 3 (L_low ^ 8)) ⌈Real.exp (coupledLowHighLacunaryLogTarget L_low Λ)⌉₊

theorem coupledLowHighLacunaryThreshold_spec (L_low : ℕ) (Λ : ℝ) {M₀ : ℕ}
    (hM₀ : coupledLowHighLacunaryThreshold L_low Λ ≤ M₀) :
    3 ≤ M₀ ∧
    L_low ^ 8 ≤ M₀ ∧
    criticalLowWindowTotalPenalty L_low * max Λ 0 +
      criticalTruncatedArchLogSlope / 4 * Real.log M₀ ≤
      criticalTruncatedArchLogSlope / 2 * (Real.log M₀ - criticalTruncatedArchLogOffset) -
        criticalAllScaleGammaPolarConstant -
        2 * (lacunaryPrimeConstant + 100 * truncatedCrossBlockConstant) := by
  have h1 : 3 ≤ M₀ := ((le_max_left 3 _).trans (le_max_left _ _)).trans hM₀
  have h2 : L_low ^ 8 ≤ M₀ := ((le_max_right 3 _).trans (le_max_left _ _)).trans hM₀
  have h3 : ⌈Real.exp (coupledLowHighLacunaryLogTarget L_low Λ)⌉₊ ≤ M₀ :=
    (le_max_right _ _).trans hM₀
  have hM0_pos : (0 : ℝ) < M₀ := by positivity
  have hexp_le : Real.exp (coupledLowHighLacunaryLogTarget L_low Λ) ≤ M₀ :=
    (Nat.le_ceil _).trans (by exact_mod_cast h3)
  have hlog_le : coupledLowHighLacunaryLogTarget L_low Λ ≤ Real.log M₀ := by
    rw [← Real.log_exp (coupledLowHighLacunaryLogTarget L_low Λ)]
    exact Real.log_le_log (Real.exp_pos _) hexp_le
  have hs : 0 < criticalTruncatedArchLogSlope := criticalTruncatedArchLogSlope_pos
  have hmul := mul_le_mul_of_nonneg_left hlog_le (show 0 ≤ criticalTruncatedArchLogSlope / 4 by positivity)
  have hlhs : criticalTruncatedArchLogSlope / 4 * coupledLowHighLacunaryLogTarget L_low Λ =
      criticalTruncatedArchLogSlope / 2 * criticalTruncatedArchLogOffset +
        criticalAllScaleGammaPolarConstant +
        2 * (lacunaryPrimeConstant + 100 * truncatedCrossBlockConstant) +
        criticalLowWindowTotalPenalty L_low * max Λ 0 := by
    unfold coupledLowHighLacunaryLogTarget
    field_simp [hs.ne']
  refine ⟨h1, h2, ?_⟩
  linarith

/-- **Quantitative Weil Positivity on Every Low–High Dominance Cone `E_low ≤ Λ E_high`.**
Because the low-window penalty `criticalLowWindowTotalPenalty L_low` is completely independent of
`M 0`, `J`, and `V`, raising `M 0 ≥ coupledLowHighLacunaryThreshold L_low Λ` guarantees
`(s_T / 4) log(M 0) E_high ≤ compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ S_high) b)`
for every `b : ℕ → ℝ` with `E_low ≤ Λ E_high`. -/
theorem compactFullWeilEnergy_ge_of_lowWindow_lacunary_dominance
    {S_low : Finset ℕ} {L_low J : ℕ} (hL_low : 1 ≤ L_low) (hlow : ScaleWindow S_low 1 L_low)
    (Λ : ℝ) {M : ℕ → ℕ} {S : ℕ → Finset ℕ} (hlac : IsLacunaryBlockFamily J M S)
    (hM₀ : coupledLowHighLacunaryThreshold L_low Λ ≤ M 0)
    {V : ℝ} (hVpos : 0 < V) (hV : criticalTruncationThreshold ≤ V)
    (b : ℕ → ℝ) (hdom : ∑ n ∈ S_low, b n ^ 2 ≤ Λ * ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2) :
    criticalTruncatedArchLogSlope / 4 * Real.log (M 0) *
      (∑ n ∈ (Finset.range J).biUnion S, b n ^ 2) ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ (Finset.range J).biUnion S) b) ∧
    ((∃ n ∈ S_low ∪ (Finset.range J).biUnion S, b n ≠ 0) →
      0 < compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ (Finset.range J).biUnion S) b)) := by
  obtain ⟨hM3, hsep, hslope⟩ := coupledLowHighLacunaryThreshold_spec L_low Λ hM₀
  set S_high := (Finset.range J).biUnion S
  set E_low := ∑ n ∈ S_low, b n ^ 2
  set E_high := ∑ n ∈ S_high, b n ^ 2
  have hE_low_nn : 0 ≤ E_low := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE_high_nn : 0 ≤ E_high := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdom_max : E_low ≤ max Λ 0 * E_high :=
    hdom.trans (mul_le_mul_of_nonneg_right (le_max_left Λ 0) hE_high_nn)
  have hpen_pos := criticalLowWindowTotalPenalty_pos L_low
  have hpen_le : criticalLowWindowTotalPenalty L_low * E_low ≤
      criticalLowWindowTotalPenalty L_low * max Λ 0 * E_high := by
    calc criticalLowWindowTotalPenalty L_low * E_low
        ≤ criticalLowWindowTotalPenalty L_low * (max Λ 0 * E_high) :=
          mul_le_mul_of_nonneg_left hdom_max hpen_pos.le
      _ = criticalLowWindowTotalPenalty L_low * max Λ 0 * E_high := by ring
  have hbase := compactFullWeilEnergy_criticalTruncatedTest_ge_of_lowWindow_lacunary_scaleFree
    hL_low hlow hlac hsep b hVpos hV
  have hhigh_margin := mul_le_mul_of_nonneg_right hslope hE_high_nn
  have hmain : criticalTruncatedArchLogSlope / 4 * Real.log (M 0) * E_high ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ S_high) b) := by
    dsimp only [E_low, E_high, S_high] at hbase hpen_le hhigh_margin ⊢
    linarith
  refine ⟨hmain, fun ⟨n, hn, hbn⟩ => ?_⟩
  have hdisj := disjoint_lowWindow_lacunary hlow hlac hsep
  have hsum_pos : 0 < E_low + E_high := by
    rw [← Finset.sum_union hdisj]
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hbn)
      (Finset.single_le_sum (fun k _ => sq_nonneg (b k)) hn)
  have hE_high_pos : 0 < E_high := by
    have : 0 < (1 + max Λ 0) * E_high := by linarith
    exact pos_of_mul_pos_right this (by positivity)
  have hlog_pos : 0 < Real.log (M 0) :=
    Real.log_pos (by exact_mod_cast (show 1 < M 0 by omega))
  have hs := criticalTruncatedArchLogSlope_pos
  exact lt_of_lt_of_le (by positivity) hmain

/-- **Unconditional Positivity Across All Five Form Realizations and Grid-Tent / Smooth-Detector
Transfers on Every Low–High Dominance Cone `E_low ≤ Λ E_high`.** -/
theorem all_five_forms_pos_of_lowWindow_lacunary_dominance
    {S_low : Finset ℕ} {L_low J : ℕ} (hL_low : 1 ≤ L_low) (hlow : ScaleWindow S_low 1 L_low)
    (Λ : ℝ) {M : ℕ → ℕ} {S : ℕ → Finset ℕ} (hlac : IsLacunaryBlockFamily J M S)
    (hM₀ : coupledLowHighLacunaryThreshold L_low Λ ≤ M 0)
    {V : ℝ} (hVpos : 0 < V) (hV : criticalTruncationThreshold ≤ V)
    (b : ℕ → ℝ) (hdom : ∑ n ∈ S_low, b n ^ 2 ≤ Λ * ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2)
    (hb : ∃ n ∈ S_low ∪ (Finset.range J).biUnion S, b n ≠ 0) :
    let T : Finset ℕ := S_low ∪ (Finset.range J).biUnion S
    let R : ℝ := Real.log (2 * V)
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedTest hVpos T b x
    0 < compactFullWeilEnergy (criticalTruncatedTest hVpos T b) ∧
    0 < fullZeroForm (criticalTruncatedTest hVpos T b) ∧
    ∃ μ : ℝ, 0 < μ ∧ ∀ᶠ n : ℕ in atTop,
      let M_grid : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
      let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M_grid
      μ ≤ compactFullWeilEnergy P ∧
      μ ≤ fullZeroForm P ∧
      ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ / 2 →
        let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M_grid q
        ContDiff ℝ 2 D ∧
        HasCompactSupport D ∧
        μ / 2 ≤ (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
          (EF.weilTest D D)).re ∧
        μ / 2 ≤ (zetaZeroConfig.W D D).re ∧
        configurationReflectionDefect zetaZeroConfig D + μ / 2 ≤
          configurationSquareMass zetaZeroConfig D := by
  dsimp only
  set T := S_low ∪ (Finset.range J).biUnion S
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  have hpos := (compactFullWeilEnergy_ge_of_lowWindow_lacunary_dominance
    hL_low hlow Λ hlac hM₀ hVpos hV b hdom).2 hb
  have hzf : 0 < fullZeroForm (criticalTruncatedTest hVpos T b) := by
    rw [fullZeroForm_eq_compactFullWeilEnergy]
    exact hpos
  set μ := compactFullWeilEnergy (criticalTruncatedTest hVpos T b) / 2
  have hμ : 0 < μ := by unfold μ; linarith
  refine ⟨hpos, hzf, μ, hμ,
    gridTentPattern_and_smoothDetector_pos_of_compactFullWeilEnergy_ge
      hVpos hV1 T b hμ (by unfold μ; linarith)⟩

/-- Coefficient vector of the coupled low–high critical source
`∑_{n ∈ S_low} b_low(n) (g^V_n + γ(n) g^V_{φ(n)})`, where `φ` embeds the low window `S_low` into a
high lacunary block family `S_high` with coupling weights `γ(n)`. -/
def coupledCriticalCoefficient (S_low : Finset ℕ) (φ : ℕ → ℕ) (γ b_low : ℕ → ℝ) (m : ℕ) : ℝ :=
  (∑ n ∈ S_low, if m = n then b_low n else 0) +
    ∑ n ∈ S_low, if m = φ n then γ n * b_low n else 0

/-- On `m ∈ S_low`, `coupledCriticalCoefficient S_low φ γ b_low m = b_low m`. -/
theorem coupledCriticalCoefficient_apply_of_mem_low {S_low S_high : Finset ℕ}
    (hdisj : Disjoint S_low S_high) {φ : ℕ → ℕ} (hφ_mem : ∀ n ∈ S_low, φ n ∈ S_high)
    (γ b_low : ℕ → ℝ) {m : ℕ} (hm : m ∈ S_low) :
    coupledCriticalCoefficient S_low φ γ b_low m = b_low m := by
  unfold coupledCriticalCoefficient
  have h1 : (∑ n ∈ S_low, if m = n then b_low n else 0) = b_low m := by
    simp [hm]
  have h2 : (∑ n ∈ S_low, if m = φ n then γ n * b_low n else 0) = 0 := by
    refine Finset.sum_eq_zero fun n hn => if_neg ?_
    rintro rfl
    exact Finset.disjoint_left.mp hdisj hm (hφ_mem n hn)
  rw [h1, h2, add_zero]

/-- On `m = φ n` (`n ∈ S_low`), `coupledCriticalCoefficient S_low φ γ b_low (φ n) = γ n * b_low n`. -/
theorem coupledCriticalCoefficient_apply_phi {S_low S_high : Finset ℕ}
    (hdisj : Disjoint S_low S_high) {φ : ℕ → ℕ} (hφ_inj : Set.InjOn φ S_low)
    (hφ_mem : ∀ n ∈ S_low, φ n ∈ S_high) (γ b_low : ℕ → ℝ) {n : ℕ} (hn : n ∈ S_low) :
    coupledCriticalCoefficient S_low φ γ b_low (φ n) = γ n * b_low n := by
  unfold coupledCriticalCoefficient
  have h1 : (∑ k ∈ S_low, if φ n = k then b_low k else 0) = 0 := by
    refine Finset.sum_eq_zero fun k hk => if_neg ?_
    intro heq
    exact Finset.disjoint_left.mp hdisj hk (heq ▸ hφ_mem n hn)
  have h2 : (∑ k ∈ S_low, if φ n = φ k then γ k * b_low k else 0) = γ n * b_low n := by
    rw [Finset.sum_eq_single n]
    · simp
    · intro k hk hne
      exact if_neg fun heq => hne (hφ_inj hk hn heq.symm)
    · intro hnot
      exact absurd hn hnot
  rw [h1, zero_add, h2]

/-- Low-band `ℓ²` energy identity and high-band `ℓ²` energy lower bound for `coupledCriticalCoefficient`. -/
theorem sum_sq_coupledCriticalCoefficient {S_low S_high : Finset ℕ}
    (hdisj : Disjoint S_low S_high) {φ : ℕ → ℕ} (hφ_inj : Set.InjOn φ S_low)
    (hφ_mem : ∀ n ∈ S_low, φ n ∈ S_high) {γ : ℕ → ℝ} {γ₀ : ℝ} (hγ₀ : 0 ≤ γ₀)
    (hγ : ∀ n ∈ S_low, γ₀ ≤ |γ n|) (b_low : ℕ → ℝ) :
    (∑ m ∈ S_low, coupledCriticalCoefficient S_low φ γ b_low m ^ 2 =
      ∑ n ∈ S_low, b_low n ^ 2) ∧
    γ₀ ^ 2 * (∑ n ∈ S_low, b_low n ^ 2) ≤
      ∑ m ∈ S_high, coupledCriticalCoefficient S_low φ γ b_low m ^ 2 := by
  classical
  refine ⟨Finset.sum_congr rfl fun m hm => by
    rw [coupledCriticalCoefficient_apply_of_mem_low hdisj hφ_mem γ b_low hm], ?_⟩
  have himg_sub : S_low.image φ ⊆ S_high := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
    exact hφ_mem n hn
  have himg_eq : ∑ m ∈ S_low.image φ, coupledCriticalCoefficient S_low φ γ b_low m ^ 2 =
      ∑ n ∈ S_low, (γ n * b_low n) ^ 2 := by
    rw [Finset.sum_image fun a ha b hb hab => hφ_inj ha hb hab]
    exact Finset.sum_congr rfl fun n hn => by
      rw [coupledCriticalCoefficient_apply_phi hdisj hφ_inj hφ_mem γ b_low hn]
  have hle_img : γ₀ ^ 2 * (∑ n ∈ S_low, b_low n ^ 2) ≤
      ∑ n ∈ S_low, (γ n * b_low n) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hsq : γ₀ ^ 2 ≤ (γ n) ^ 2 := by
      rw [← sq_abs (γ n)]
      exact pow_le_pow_left₀ hγ₀ (hγ n hn) 2
    calc γ₀ ^ 2 * b_low n ^ 2 ≤ (γ n) ^ 2 * b_low n ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (γ n * b_low n) ^ 2 := by ring
  calc γ₀ ^ 2 * (∑ n ∈ S_low, b_low n ^ 2)
      ≤ ∑ n ∈ S_low, (γ n * b_low n) ^ 2 := hle_img
    _ = ∑ m ∈ S_low.image φ, coupledCriticalCoefficient S_low φ γ b_low m ^ 2 := himg_eq.symm
    _ ≤ ∑ m ∈ S_high, coupledCriticalCoefficient S_low φ γ b_low m ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => sq_nonneg _

/-- **Unconditional Positivity of Coupled Low–High Critical Sources for ALL Unrestricted Nonzero
Low-Mode Coefficient Vectors `b_low` Across All Five Form Realizations.**
For every low window `ScaleWindow S_low 1 L_low` (`1 ≤ L_low`, including `0 ∈ S_low`, i.e. scale `M = 1`),
every coupling floor `γ₀ > 0`, every lacunary block family `IsLacunaryBlockFamily J M S` with
`coupledLowHighLacunaryThreshold L_low (γ₀ ^ 2)⁻¹ ≤ M 0`, every injection `φ` of `S_low` into `S_high`,
every coupling profile `γ` with `∀ n ∈ S_low, γ₀ ≤ |γ n|` (in particular unit coupling `γ(n) = 1`),
every truncation `V ≥ criticalTruncationThreshold`, and **every unrestricted nonzero low-mode
coefficient vector `b_low : ℕ → ℝ`** (`∃ n ∈ S_low, b_low n ≠ 0`), the coupled critical source
`criticalTruncatedTest hVpos (S_low ∪ S_high) (coupledCriticalCoefficient S_low φ γ b_low)`
and its single-scale `gridTentPattern` and `smoothGridTentDetector` transfers are unconditionally
strictly positive across all five form realizations, with explicit lower bound
`(s_T / 4) log(M 0) γ₀^2 ∑_{n ∈ S_low} b_low(n)^2 ≤ compactFullWeilEnergy ...`. -/
theorem coupled_low_high_pos_for_unrestricted_low_modes
    {S_low : Finset ℕ} {L_low J : ℕ} (hL_low : 1 ≤ L_low) (hlow : ScaleWindow S_low 1 L_low)
    {γ₀ : ℝ} (hγ₀ : 0 < γ₀)
    {M : ℕ → ℕ} {S : ℕ → Finset ℕ} (hlac : IsLacunaryBlockFamily J M S)
    (hM₀ : coupledLowHighLacunaryThreshold L_low (γ₀ ^ 2)⁻¹ ≤ M 0)
    {φ : ℕ → ℕ} (hφ_inj : Set.InjOn φ S_low)
    (hφ_mem : ∀ n ∈ S_low, φ n ∈ (Finset.range J).biUnion S)
    {γ : ℕ → ℝ} (hγ : ∀ n ∈ S_low, γ₀ ≤ |γ n|)
    {V : ℝ} (hVpos : 0 < V) (hV : criticalTruncationThreshold ≤ V)
    (b_low : ℕ → ℝ) (hb_low : ∃ n ∈ S_low, b_low n ≠ 0) :
    let T : Finset ℕ := S_low ∪ (Finset.range J).biUnion S
    let b : ℕ → ℝ := coupledCriticalCoefficient S_low φ γ b_low
    let R : ℝ := Real.log (2 * V)
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedTest hVpos T b x
    criticalTruncatedArchLogSlope / 4 * Real.log (M 0) * γ₀ ^ 2 * (∑ n ∈ S_low, b_low n ^ 2) ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos T b) ∧
    0 < compactFullWeilEnergy (criticalTruncatedTest hVpos T b) ∧
    0 < fullZeroForm (criticalTruncatedTest hVpos T b) ∧
    ∃ μ : ℝ, 0 < μ ∧ ∀ᶠ n : ℕ in atTop,
      let M_grid : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
      let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M_grid
      μ ≤ compactFullWeilEnergy P ∧
      μ ≤ fullZeroForm P ∧
      ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ / 2 →
        let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M_grid q
        ContDiff ℝ 2 D ∧
        HasCompactSupport D ∧
        μ / 2 ≤ (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
          (EF.weilTest D D)).re ∧
        μ / 2 ≤ (zetaZeroConfig.W D D).re ∧
        configurationReflectionDefect zetaZeroConfig D + μ / 2 ≤
          configurationSquareMass zetaZeroConfig D := by
  dsimp only
  obtain ⟨hM3, hsep, _⟩ := coupledLowHighLacunaryThreshold_spec L_low (γ₀ ^ 2)⁻¹ hM₀
  have hdisj := disjoint_lowWindow_lacunary hlow hlac hsep
  set S_high := (Finset.range J).biUnion S
  set b := coupledCriticalCoefficient S_low φ γ b_low
  obtain ⟨hlow_eq, hhigh_ge⟩ := sum_sq_coupledCriticalCoefficient hdisj hφ_inj hφ_mem hγ₀.le hγ b_low
  have hdom : ∑ m ∈ S_low, b m ^ 2 ≤ (γ₀ ^ 2)⁻¹ * ∑ m ∈ S_high, b m ^ 2 := by
    rw [hlow_eq, inv_mul_eq_div, le_div_iff₀ (sq_pos_of_pos hγ₀), mul_comm]
    exact hhigh_ge
  rcases hb_low with ⟨n₀, hn₀, hbn₀⟩
  have hb_union : ∃ m ∈ S_low ∪ S_high, b m ≠ 0 := by
    refine ⟨n₀, Finset.mem_union_left S_high hn₀, ?_⟩
    dsimp only [b]
    rw [coupledCriticalCoefficient_apply_of_mem_low hdisj hφ_mem γ b_low hn₀]
    exact hbn₀
  have hge := (compactFullWeilEnergy_ge_of_lowWindow_lacunary_dominance
    hL_low hlow (γ₀ ^ 2)⁻¹ hlac hM₀ hVpos hV b hdom).1
  have hall := all_five_forms_pos_of_lowWindow_lacunary_dominance
    hL_low hlow (γ₀ ^ 2)⁻¹ hlac hM₀ hVpos hV b hdom hb_union
  have hlog_nn : 0 ≤ Real.log (M 0) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ M 0 by omega))
  have hs := criticalTruncatedArchLogSlope_pos
  have hquant : criticalTruncatedArchLogSlope / 4 * Real.log (M 0) * γ₀ ^ 2 *
      (∑ n ∈ S_low, b_low n ^ 2) ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ S_high) b) := by
    calc criticalTruncatedArchLogSlope / 4 * Real.log (M 0) * γ₀ ^ 2 * (∑ n ∈ S_low, b_low n ^ 2)
        = criticalTruncatedArchLogSlope / 4 * Real.log (M 0) *
            (γ₀ ^ 2 * ∑ n ∈ S_low, b_low n ^ 2) := by ring
      _ ≤ criticalTruncatedArchLogSlope / 4 * Real.log (M 0) * ∑ m ∈ S_high, b m ^ 2 :=
          mul_le_mul_of_nonneg_left hhigh_ge (by positivity)
      _ ≤ compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ S_high) b) := hge
  exact ⟨hquant, hall.1, hall.2.1, hall.2.2⟩

end GaloisForLFunctions.ArithmeticPositivityTheory
end
