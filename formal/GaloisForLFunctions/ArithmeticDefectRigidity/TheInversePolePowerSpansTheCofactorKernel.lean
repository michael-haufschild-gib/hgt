import GaloisForLFunctions.ArithmeticDefectRigidity.TheResidualAndPoleTraceDetermineTheRow
import GaloisForLFunctions.ArithmeticDefectRigidity.TheRenormalizedCofactorActsOnPowerRowsByZeta
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheZeroFreeBandBelowHalfDamping
import GaloisForLFunctions.RHTower.HardyLittlewoodExponentLaw
import GaloisForLFunctions.HTGeometry.SubexponentialSqrtSummable
import GaloisForLFunctions.ArithmeticOrientationTheory.LocalFactorsAreTheUnitsOfTheWienerMonoid

/-!
# The inverse pole power spans the kernel of the renormalized cofactor

The Möbius floor inverse of the pole power, `q_ε(n) = Σ_{d≤n} μ(d) d^{-ε} ⌊n/d⌋^{1−ε}`, is an exact
solution of the renormalized inversion law. Its total cofactor sum is the pole power itself, so
`q_ε + D̃q_ε = (1 − 𝓛(q_ε)) n^{1−ε}`. We prove:

* `q_ε` lies in the absolute pole-trace domain (`inversePolePower_mem_poleTraceDomain`): the
  de la Vallée Poussin rate `M(x) ≪ x e^{-√(log x)/12}` and `Σμ(d)/d = 0` give
  `q_ε(n) = O(n^{1−ε} e^{-c√(log n)})` after a hyperbola split at `√n`;
* its trace is `𝓛(q_ε) = 1` (`poleTrace_inversePoleVector`): for real `w > 1 − ε` the Mellin trace
  is `Δ(w)/ζ(w+ε)` with `(w − α)Δ(w) → α` and `(w − α)ζ(w + ε) → 1`;
* hence `q_ε` is an exact `(−1)`-eigenvector of `D̃`, and the kernel of the renormalized residual on
  the trace domain is exactly the line `ℝ q_ε` (`renormalizedResidual_eq_zero_iff`).
-/

open Finset Filter Topology Real
open GaloisForLFunctions.TransHorizonIncidenceMechanics (mellinCell mellinCell_nonneg mellinCell_bounds)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-! ### Summation by parts -/

/-- The partial sums `F(d) = Σ_{e≤d} f(e)`. -/
def partialSumRow (f : ℕ → ℝ) (d : ℕ) : ℝ := ∑ e ∈ range (d + 1), f e

/-- **Abel summation on `(a, n]`.** -/
theorem sum_Ioc_mul_eq_abel (f g : ℕ → ℝ) {a n : ℕ} (h : a ≤ n) :
    ∑ d ∈ Ioc a n, f d * g d = partialSumRow f n * g (n + 1) - partialSumRow f a * g (a + 1) +
      ∑ d ∈ Ioc a n, partialSumRow f d * (g d - g (d + 1)) := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n han ih =>
    rw [sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega), ih]
    simp only [partialSumRow]
    rw [Finset.sum_range_succ _ (n + 1)]
    ring

/-- `Σ_{d∈(a,n]} d (g(d) − g(d+1)) = a g(a+1) − n g(n+1) + Σ_{d∈(a,n]} g(d)`. -/
theorem sum_Ioc_mul_sub_eq (g : ℕ → ℝ) {a n : ℕ} (h : a ≤ n) :
    ∑ d ∈ Ioc a n, (d : ℝ) * (g d - g (d + 1)) =
      (a : ℝ) * g (a + 1) - (n : ℝ) * g (n + 1) + ∑ d ∈ Ioc a n, g d := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n han ih =>
    rw [sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega), ih]
    push_cast
    ring

/-! ### The prime-number-theorem rate -/

/-- The Mertens function `M(x) = Σ_{e≤x} μ(e)`. -/
def mertensRow : ℕ → ℝ := partialSumRow fun e => (ArithmeticFunction.moebius e : ℝ)

/-- The decay profile `e^{-c√(log x)}`. -/
def sqrtLogDecay (c x : ℝ) : ℝ := Real.exp (-(c * Real.sqrt (Real.log x)))

theorem sqrtLogDecay_pos (c x : ℝ) : 0 < sqrtLogDecay c x := Real.exp_pos _

theorem sqrtLogDecay_le_one {c x : ℝ} (hc : 0 ≤ c) : sqrtLogDecay c x ≤ 1 :=
  Real.exp_le_one_iff.mpr (by have := Real.sqrt_nonneg (Real.log x); nlinarith)

theorem sqrtLogDecay_antitone {c : ℝ} (hc : 0 ≤ c) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    sqrtLogDecay c y ≤ sqrtLogDecay c x := by
  unfold sqrtLogDecay
  refine Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left ?_ hc))
  exact Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hxy)

theorem sqrtLogDecay_sq (c x : ℝ) : sqrtLogDecay (2 * c) x = sqrtLogDecay c x ^ 2 := by
  unfold sqrtLogDecay
  rw [sq, ← Real.exp_add]; ring_nf

/-- **The de la Vallée Poussin rate.** `|M(x)| ≤ B x e^{-√(log x)/12}` for `x ≥ N₀`. -/
theorem exists_abs_mertensRow_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ x : ℕ, N₀ ≤ x →
      |mertensRow x| ≤ B * x * sqrtLogDecay (1 / 12) x := by
  obtain ⟨B, hB, N₀, h⟩ := BezoutValuationIncidence.exists_abs_sum_moebiusReal_le_sqrtLog
  refine ⟨B, hB, N₀ + 1, by omega, fun x hx => ?_⟩
  have hbridge : mertensRow x = ∑ e ∈ Icc 1 x, BezoutValuationIncidence.moebiusReal e :=
    BezoutValuationIncidence.sum_range_moebius_eq_sum_Icc_moebiusReal x
  rw [hbridge, sqrtLogDecay, show (1 / 12 : ℝ) * Real.sqrt (Real.log x) =
    Real.sqrt (Real.log x) / 12 by ring]
  exact h x (by omega)

theorem mertensRow_zero : mertensRow 0 = 0 := by simp [mertensRow, partialSumRow]

theorem tendsto_sqrtLogDecay {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => sqrtLogDecay c x) atTop (𝓝 0) := by
  unfold sqrtLogDecay
  refine Real.tendsto_exp_atBot.comp ?_
  refine tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hc ?_)
  exact (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)

/-- `Σ e^{-c√(log m)}/m < ∞`. -/
theorem summable_sqrtLogDecay_div {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℕ => sqrtLogDecay c m / m :=
  HTGeometry.summable_exp_neg_sqrt_log_div hc

/-- **Absorbing a logarithm.** `(3 + log x) e^{-c√(log x)} ≤ (3 + 8/c²) e^{-(c/2)√(log x)}`. -/
theorem three_add_log_mul_sqrtLogDecay_le {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 1 ≤ x) :
    (3 + Real.log x) * sqrtLogDecay c x ≤ (3 + 8 / c ^ 2) * sqrtLogDecay (c / 2) x := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  set u := Real.sqrt (Real.log x) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have huL : u ^ 2 = Real.log x := Real.sq_sqrt hL
  have hexp : c ^ 2 * u ^ 2 / 8 ≤ Real.exp (c / 2 * u) := by
    have h := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ c / 2 * u)
    nlinarith [sq_nonneg (c / 2 * u)]
  have hsplit : sqrtLogDecay c x = sqrtLogDecay (c / 2) x * sqrtLogDecay (c / 2) x := by
    unfold sqrtLogDecay; rw [← Real.exp_add]; ring_nf
  have hinv : sqrtLogDecay (c / 2) x * Real.exp (c / 2 * u) = 1 := by
    unfold sqrtLogDecay; rw [← Real.exp_add, ← hu]; ring_nf; exact Real.exp_zero
  have hd := sqrtLogDecay_pos (c / 2) x
  have hle1 : sqrtLogDecay (c / 2) x ≤ 1 := sqrtLogDecay_le_one (by positivity)
  rw [hsplit, ← huL]
  have hkey : u ^ 2 * sqrtLogDecay (c / 2) x ≤ 8 / c ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc u ^ 2 * sqrtLogDecay (c / 2) x * c ^ 2 = (c ^ 2 * u ^ 2 / 8) * sqrtLogDecay (c / 2) x * 8 := by
          ring
      _ ≤ Real.exp (c / 2 * u) * sqrtLogDecay (c / 2) x * 8 := by gcongr
      _ = 8 := by rw [mul_comm (Real.exp _), hinv, one_mul]
  nlinarith

/-- For `n ≥ 16`, `log ⌊√n⌋ ≥ (log n)/4`. -/
theorem log_natSqrt_ge {n : ℕ} (hn : 16 ≤ n) : Real.log n / 4 ≤ Real.log (Nat.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hq : (Nat.sqrt n : ℝ) + 1 > Real.sqrt n := Real.real_sqrt_lt_nat_sqrt_succ
  have hs4 : (4 : ℝ) ≤ Real.sqrt n := by
    rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hhalf : Real.sqrt n / 2 ≤ (Nat.sqrt n : ℝ) := by linarith
  have hlogs : Real.log (Real.sqrt n) = Real.log n / 2 := by
    rw [Real.log_sqrt hn0.le]
  have h2 : Real.log 2 ≤ Real.log n / 4 := by
    have : Real.log 16 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
    push_cast at this; linarith
  calc Real.log n / 4 ≤ Real.log n / 2 - Real.log 2 := by linarith
    _ = Real.log (Real.sqrt n / 2) := by
        rw [Real.log_div (by positivity) (by norm_num), hlogs]
    _ ≤ Real.log (Nat.sqrt n) := Real.log_le_log (by positivity) hhalf

/-- `e^{-c√(log ⌊√n⌋)} ≤ e^{-(c/2)√(log n)}` for `n ≥ 16`. -/
theorem sqrtLogDecay_natSqrt_le {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 16 ≤ n) :
    sqrtLogDecay c (Nat.sqrt n) ≤ sqrtLogDecay (c / 2) n := by
  unfold sqrtLogDecay
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  have hL := log_natSqrt_ge hn
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hsq : Real.sqrt (Real.log n) / 2 ≤ Real.sqrt (Real.log (Nat.sqrt n)) := by
    rw [show Real.sqrt (Real.log n) / 2 = Real.sqrt (Real.log n / 4) by
      rw [Real.sqrt_div hlog0, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hL
  calc c / 2 * Real.sqrt (Real.log n) = c * (Real.sqrt (Real.log n) / 2) := by ring
    _ ≤ c * Real.sqrt (Real.log (Nat.sqrt n)) := mul_le_mul_of_nonneg_left hsq hc

/-! ### The Möbius harmonic sums -/

/-- `m(D) = Σ_{d≤D} μ(d)/d`. -/
def moebiusHarmonic (D : ℕ) : ℝ := ∑ n ∈ range (D + 1), (ArithmeticFunction.moebius n : ℝ) / n

/-- The Abel coefficients `t(d) = M(d)(1/d − 1/(d+1))`. -/
def harmonicAbelCoeff (d : ℕ) : ℝ := mertensRow d * (1 / (d : ℝ) - 1 / ((d + 1 : ℕ) : ℝ))

theorem moebiusHarmonic_eq_abel (D : ℕ) :
    moebiusHarmonic D = mertensRow D / ((D + 1 : ℕ) : ℝ) +
      ∑ d ∈ range (D + 1), harmonicAbelCoeff d := by
  have h := sum_Ioc_mul_eq_abel (fun e => (ArithmeticFunction.moebius e : ℝ))
    (fun d => 1 / (d : ℝ)) (Nat.zero_le D)
  have hrange : ∀ g : ℕ → ℝ, g 0 = 0 → ∑ d ∈ range (D + 1), g d = ∑ d ∈ Ioc 0 D, g d := by
    intro g hg0
    symm
    refine Finset.sum_subset (fun d hd => by simp only [mem_Ioc, mem_range] at hd ⊢; omega) ?_
    intro d hd hnot
    simp only [mem_Ioc, mem_range, not_and, not_le] at hd hnot
    rw [show d = 0 by omega, hg0]
  rw [moebiusHarmonic, hrange _ (by simp), hrange _ (by simp [harmonicAbelCoeff, mertensRow_zero])]
  simp only [div_eq_mul_one_div ((ArithmeticFunction.moebius _ : ℝ))] at h ⊢
  rw [h]
  simp only [harmonicAbelCoeff, mertensRow]
  rw [show partialSumRow (fun e => (ArithmeticFunction.moebius e : ℝ)) 0 = 0 from mertensRow_zero]
  push_cast
  ring

theorem summable_harmonicAbelCoeff : Summable harmonicAbelCoeff := by
  obtain ⟨B, hB, N₀, hN₀1, hM⟩ := exists_abs_mertensRow_le
  refine Summable.of_norm_bounded_eventually
    ((summable_sqrtLogDecay_div (by norm_num : (0 : ℝ) < 1 / 12)).mul_left B) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop N₀] with d hd
  have hd1 : 1 ≤ d := hN₀1.trans hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hcoef : 1 / (d : ℝ) - 1 / ((d + 1 : ℕ) : ℝ) = 1 / ((d : ℝ) * (d + 1)) := by
    push_cast; field_simp; ring
  rw [Real.norm_eq_abs, harmonicAbelCoeff, hcoef, abs_mul,
    abs_of_pos (one_div_pos.mpr (mul_pos hd0 (by linarith)))]
  calc |mertensRow d| * (1 / ((d : ℝ) * (d + 1))) ≤ (B * d * sqrtLogDecay (1 / 12) d) *
        (1 / ((d : ℝ) * (d + 1))) := mul_le_mul_of_nonneg_right (hM d hd) (by positivity)
    _ ≤ B * (sqrtLogDecay (1 / 12) d / d) := by
        rw [div_eq_mul_one_div (sqrtLogDecay _ _)]
        have hs := sqrtLogDecay_pos (1 / 12) (d : ℝ)
        rw [show B * d * sqrtLogDecay (1 / 12) d * (1 / (d * (d + 1))) =
          B * (sqrtLogDecay (1 / 12) d * (1 / (d : ℝ))) * (d / (d + 1)) by field_simp]
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [div_le_one (by positivity)]; linarith

/-- **`Σ_d M(d)/(d(d+1)) = 0`**, the prime number theorem in Abel form. -/
theorem tsum_harmonicAbelCoeff : ∑' d, harmonicAbelCoeff d = 0 := by
  obtain ⟨B, hB, N₀, hN₀1, hM⟩ := exists_abs_mertensRow_le
  have hM0 : Tendsto (fun D : ℕ => mertensRow D / ((D + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hdec := (tendsto_sqrtLogDecay (by norm_num : (0 : ℝ) < 1 / 12)).comp
      tendsto_natCast_atTop_atTop
    have hg := hdec.const_mul B
    rw [mul_zero] at hg
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
    · filter_upwards [eventually_ge_atTop N₀] with D hD
      have hD1 : 1 ≤ D := hN₀1.trans hD
      have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((D + 1 : ℕ) : ℝ)),
        div_le_iff₀ (by positivity)]
      calc |mertensRow D| ≤ B * D * sqrtLogDecay (1 / 12) D := hM D hD
        _ ≤ B * ((sqrtLogDecay (1 / 12)) ((D : ℕ) : ℝ)) * ((D + 1 : ℕ) : ℝ) := by
            push_cast
            have := sqrtLogDecay_pos (1 / 12) (D : ℝ)
            nlinarith
  have hpart : Tendsto (fun D : ℕ => ∑ d ∈ range (D + 1), harmonicAbelCoeff d) atTop (𝓝 0) := by
    have h := RHTower.tendsto_sum_range_succ_moebius_div.sub hM0
    rw [sub_zero] at h
    refine h.congr fun D => ?_
    rw [← moebiusHarmonic, moebiusHarmonic_eq_abel]
    ring
  have hlim := summable_harmonicAbelCoeff.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hlim hpart

theorem sqrtLogDecay_twelfth (x : ℝ) : sqrtLogDecay (1 / 12) x = sqrtLogDecay (1 / 24) x ^ 2 := by
  rw [← sqrtLogDecay_sq]; norm_num

/-- `M(D)/(D+1)` is bounded by `B e^{-√(log D)/24}`. -/
theorem abs_mertensRow_div_le {B : ℝ} (hB : 0 ≤ B) {N₀ : ℕ}
    (hM : ∀ x : ℕ, N₀ ≤ x → |mertensRow x| ≤ B * x * sqrtLogDecay (1 / 12) x) {D : ℕ}
    (hD : N₀ ≤ D) (hD1 : 1 ≤ D) :
    |mertensRow D / ((D + 1 : ℕ) : ℝ)| ≤ B * sqrtLogDecay (1 / 24) D := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have hhalf : sqrtLogDecay (1 / 24) D ≤ 1 := sqrtLogDecay_le_one (by norm_num)
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((D + 1 : ℕ) : ℝ)), div_le_iff₀ (by positivity)]
  have h1 := hM D hD
  rw [sqrtLogDecay_twelfth] at h1
  have hpos := sqrtLogDecay_pos (1 / 24) (D : ℝ)
  calc |mertensRow D| ≤ B * D * sqrtLogDecay (1 / 24) D ^ 2 := h1
    _ ≤ B * sqrtLogDecay (1 / 24) D * ((D + 1 : ℕ) : ℝ) := by
        push_cast
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hB hD0.le) hpos.le) (sub_nonneg.mpr hhalf),
          mul_nonneg hB hpos.le]

/-- Each Abel coefficient beyond `D` is `≤ B e^{-√(log D)/24} · e^{-√(log d)/24}/d`. -/
theorem abs_harmonicAbelCoeff_le {B : ℝ} (hB : 0 ≤ B) {N₀ : ℕ}
    (hM : ∀ x : ℕ, N₀ ≤ x → |mertensRow x| ≤ B * x * sqrtLogDecay (1 / 12) x) {D d : ℕ}
    (hD : N₀ ≤ D) (hD1 : 1 ≤ D) (hDd : D ≤ d) :
    |harmonicAbelCoeff d| ≤ B * sqrtLogDecay (1 / 24) D * (sqrtLogDecay (1 / 24) d / d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hcoef : 1 / (d : ℝ) - 1 / ((d + 1 : ℕ) : ℝ) = 1 / ((d : ℝ) * (d + 1)) := by
    push_cast; field_simp; ring
  have hmono : sqrtLogDecay (1 / 24) d ≤ sqrtLogDecay (1 / 24) D :=
    sqrtLogDecay_antitone (by norm_num) (by exact_mod_cast hD1) (by exact_mod_cast hDd)
  have h1 := hM d (hD.trans hDd)
  rw [sqrtLogDecay_twelfth] at h1
  rw [harmonicAbelCoeff, hcoef, abs_mul, abs_of_pos (one_div_pos.mpr (mul_pos hd0 (by linarith)))]
  have hpd := sqrtLogDecay_pos (1 / 24) (d : ℝ)
  set s := sqrtLogDecay (1 / 24) (d : ℝ)
  calc |mertensRow d| * (1 / ((d : ℝ) * (d + 1))) ≤ (B * d * s ^ 2) * (1 / ((d : ℝ) * (d + 1))) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = B * s * (s / d) * (d / (d + 1)) := by field_simp
    _ ≤ B * s * (s / d) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_one (by positivity)]; linarith
    _ ≤ B * sqrtLogDecay (1 / 24) D * (s / d) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hB) (by positivity)

/-- The Abel tail beyond `D` is `≤ B S e^{-√(log D)/24}`, `S = Σ e^{-√(log m)/24}/m`. -/
theorem abs_tsum_harmonicAbelCoeff_tail_le {B : ℝ} (hB : 0 ≤ B) {N₀ : ℕ}
    (hM : ∀ x : ℕ, N₀ ≤ x → |mertensRow x| ≤ B * x * sqrtLogDecay (1 / 12) x) {D : ℕ}
    (hD : N₀ ≤ D) (hD1 : 1 ≤ D) :
    |∑' k, harmonicAbelCoeff (k + (D + 1))| ≤
      B * sqrtLogDecay (1 / 24) D * ∑' m : ℕ, sqrtLogDecay (1 / 24) m / m := by
  have hSsum := summable_sqrtLogDecay_div (by norm_num : (0 : ℝ) < 1 / 24)
  set g : ℕ → ℝ := fun m => sqrtLogDecay (1 / 24) m / m with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    have := sqrtLogDecay_pos (1 / 24) (m : ℝ); simp only [hg]; positivity
  have hsumd := (summable_nat_add_iff (D + 1)).mpr summable_harmonicAbelCoeff
  have hsumtail : Summable fun k : ℕ => g (k + (D + 1)) := (summable_nat_add_iff (D + 1)).mpr hSsum
  have htailS : ∑' k : ℕ, g (k + (D + 1)) ≤ ∑' m, g m := by
    have h := hSsum.sum_add_tsum_nat_add (D + 1)
    have hnn : 0 ≤ ∑ m ∈ range (D + 1), g m := sum_nonneg fun m _ => hg0 m
    linarith
  have hterm : ∀ k : ℕ, |harmonicAbelCoeff (k + (D + 1))| ≤
      B * sqrtLogDecay (1 / 24) D * g (k + (D + 1)) := fun k => by
    have h := abs_harmonicAbelCoeff_le hB hM hD hD1 (d := k + (D + 1)) (by omega)
    simpa only [hg] using h
  have hK0 : 0 ≤ B * sqrtLogDecay (1 / 24) D := by
    have := sqrtLogDecay_pos (1 / 24) (D : ℝ); positivity
  have hnorm : |∑' k, harmonicAbelCoeff (k + (D + 1))| ≤ ∑' k, |harmonicAbelCoeff (k + (D + 1))| := by
    have h := norm_tsum_le_tsum_norm hsumd.norm
    simpa only [Real.norm_eq_abs] using h
  have hcmp : ∑' k, |harmonicAbelCoeff (k + (D + 1))| ≤
      ∑' k : ℕ, B * sqrtLogDecay (1 / 24) D * g (k + (D + 1)) :=
    Summable.tsum_le_tsum hterm hsumd.abs (hsumtail.mul_left _)
  have hmul : ∑' k : ℕ, B * sqrtLogDecay (1 / 24) D * g (k + (D + 1)) =
      B * sqrtLogDecay (1 / 24) D * ∑' k : ℕ, g (k + (D + 1)) := by
    rw [tsum_mul_left]
  calc _ ≤ _ := hnorm
    _ ≤ _ := hcmp
    _ = _ := hmul
    _ ≤ B * sqrtLogDecay (1 / 24) D * ∑' m, g m := mul_le_mul_of_nonneg_left htailS hK0

/-- **The Möbius harmonic sums decay.** `|m(D)| ≤ C e^{-√(log D)/24}` for `D ≥ N₀`. -/
theorem exists_abs_moebiusHarmonic_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ D : ℕ, N₀ ≤ D →
      |moebiusHarmonic D| ≤ C * sqrtLogDecay (1 / 24) D := by
  obtain ⟨B, hB, N₀, hN₀1, hM⟩ := exists_abs_mertensRow_le
  set S := ∑' m : ℕ, sqrtLogDecay (1 / 24) m / m with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun m => by have := sqrtLogDecay_pos (1 / 24) (m : ℝ); positivity
  refine ⟨B * (1 + S), by positivity, N₀, hN₀1, fun D hD => ?_⟩
  have hD1 : 1 ≤ D := hN₀1.trans hD
  -- the tail representation
  have htail : moebiusHarmonic D = mertensRow D / ((D + 1 : ℕ) : ℝ) -
      ∑' k, harmonicAbelCoeff (k + (D + 1)) := by
    have h := summable_harmonicAbelCoeff.sum_add_tsum_nat_add (D + 1)
    rw [tsum_harmonicAbelCoeff] at h
    rw [moebiusHarmonic_eq_abel]
    linarith
  have hb := abs_mertensRow_div_le hB hM hD hD1
  have habs := abs_tsum_harmonicAbelCoeff_tail_le hB hM hD hD1
  rw [htail]
  calc |mertensRow D / ((D + 1 : ℕ) : ℝ) - ∑' k, harmonicAbelCoeff (k + (D + 1))| ≤
        |mertensRow D / ((D + 1 : ℕ) : ℝ)| + |∑' k, harmonicAbelCoeff (k + (D + 1))| := abs_sub _ _
    _ ≤ B * sqrtLogDecay (1 / 24) D + B * sqrtLogDecay (1 / 24) D * S := add_le_add hb habs
    _ = B * (1 + S) * sqrtLogDecay (1 / 24) D := by ring

/-! ### The inverse pole power is `O(n^{1−ε} e^{-c√(log n)})` -/

/-- `q_ε(n) = Σ_{d≤n} μ(d) d^{-ε} ⌊n/d⌋^{1−ε}`. -/
theorem inversePolePower_eq (ε : SubcriticalDamping) (n : ℕ) :
    inversePolePower ε n = ∑ d ∈ Icc 1 n, (ArithmeticFunction.moebius d : ℝ) *
      ((d : ℝ) ^ (-(ε : ℝ)) * ((n / d : ℕ) : ℝ) ^ (1 - (ε : ℝ))) := by
  simp only [inversePolePower, RHTower.floorTransform, RHTower.moebiusPowerWeight, mul_assoc]

/-- The floor weight `w(d) = d^{-ε} ⌊n/d⌋^{1−ε}` is nonincreasing and vanishes beyond `n`. -/
def inverseFloorWeight (ε : ℝ) (n d : ℕ) : ℝ := (d : ℝ) ^ (-ε) * ((n / d : ℕ) : ℝ) ^ (1 - ε)

theorem inverseFloorWeight_nonneg (ε : ℝ) (n d : ℕ) : 0 ≤ inverseFloorWeight ε n d := by
  unfold inverseFloorWeight; positivity

theorem inverseFloorWeight_antitone {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ) {d : ℕ}
    (hd : 1 ≤ d) : inverseFloorWeight ε n (d + 1) ≤ inverseFloorWeight ε n d := by
  unfold inverseFloorWeight
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hd0 (by push_cast; linarith) (by linarith))
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_div_left (by omega) hd)
      (by linarith)) (by positivity) (by positivity)

theorem inverseFloorWeight_succ_self {ε : ℝ} (hε1 : ε < 1) (n : ℕ) :
    inverseFloorWeight ε n (n + 1) = 0 := by
  unfold inverseFloorWeight
  rw [Nat.div_eq_of_lt (by omega), Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]

/-- `d · w(d) ≤ n^{1−ε}`. -/
theorem natCast_mul_inverseFloorWeight_le {ε : ℝ} (hε1 : ε < 1) (n : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) * inverseFloorWeight ε n d ≤ (n : ℝ) ^ (1 - ε) := by
  unfold inverseFloorWeight
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hle : ((n / d : ℕ) : ℝ) ^ (1 - ε) ≤ ((n : ℝ) / d) ^ (1 - ε) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le (by linarith)
  calc (d : ℝ) * ((d : ℝ) ^ (-ε) * ((n / d : ℕ) : ℝ) ^ (1 - ε))
      ≤ (d : ℝ) * ((d : ℝ) ^ (-ε) * ((n : ℝ) / d) ^ (1 - ε)) := by gcongr
    _ = (n : ℝ) ^ (1 - ε) := by
        rw [Real.div_rpow (Nat.cast_nonneg n) hd0.le, ← mul_assoc, ← Real.rpow_one_add' hd0.le
          (by linarith)]
        rw [show 1 + -ε = 1 - ε by ring]
        have hne : (d : ℝ) ^ (1 - ε) ≠ 0 := (Real.rpow_pos_of_pos hd0 _).ne'
        field_simp

/-- **The pointwise bound.** With `D = ⌊√n⌋ ≥ N₀`,
`|q_ε(n)| ≤ n^α |m(D)| + D + B n^α e^{-√(log D)/12}(3 + log n)`. -/
theorem abs_inversePolePower_le (ε : SubcriticalDamping) {B : ℝ} (hB : 0 ≤ B) {N₀ : ℕ}
    (hN₀1 : 1 ≤ N₀) (hM : ∀ x : ℕ, N₀ ≤ x → |mertensRow x| ≤ B * x * sqrtLogDecay (1 / 12) x)
    {n : ℕ} (hn : N₀ ≤ Nat.sqrt n) :
    |inversePolePower ε n| ≤ (n : ℝ) ^ (1 - (ε : ℝ)) * |moebiusHarmonic (Nat.sqrt n)| +
      (Nat.sqrt n : ℝ) + B * sqrtLogDecay (1 / 12) (Nat.sqrt n) *
        ((n : ℝ) ^ (1 - (ε : ℝ)) * (3 + Real.log n)) := by
  have hε0 := ε.property.1
  have hε1 : (ε : ℝ) < 1 := by linarith [ε.property.2]
  set α : ℝ := 1 - (ε : ℝ) with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α ≤ 1 := by rw [hα]; linarith
  set D := Nat.sqrt n with hD
  have hD1 : 1 ≤ D := hN₀1.trans hn
  have hDn : D ≤ n := Nat.sqrt_le_self n
  have hDD : D * D ≤ n := Nat.sqrt_le n
  have hn1 : 1 ≤ n := hD1.trans hDn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  -- split at `D`
  have hsplit : Icc 1 n = Icc 1 D ∪ Ioc D n := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  rw [inversePolePower_eq, hsplit, sum_union (disjoint_left.mpr fun d h1 h2 => by
    simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
  -- the head: main term and rounding
  have hhead : ∑ d ∈ Icc 1 D, (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-(ε : ℝ)) *
      ((n / d : ℕ) : ℝ) ^ α) = (n : ℝ) ^ α * moebiusHarmonic D +
      ∑ d ∈ Icc 1 D, (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-(ε : ℝ)) *
        (((n / d : ℕ) : ℝ) ^ α - ((n : ℝ) / d) ^ α)) := by
    have hmH : moebiusHarmonic D = ∑ d ∈ Icc 1 D, (ArithmeticFunction.moebius d : ℝ) / d := by
      rw [moebiusHarmonic]
      symm
      refine Finset.sum_subset (fun d hd => by simp only [mem_Icc, mem_range] at hd ⊢; omega) ?_
      intro d hd hnot
      simp only [mem_Icc, mem_range, not_and, not_le] at hd hnot
      rw [show d = 0 by omega]; simp
    rw [hmH, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have hpow : (d : ℝ) ^ (-(ε : ℝ)) * ((n : ℝ) / d) ^ α = (n : ℝ) ^ α / d := by
      rw [Real.div_rpow hn0.le hd0.le, hα, show (1 : ℝ) - ε = -(ε : ℝ) + 1 by ring,
        Real.rpow_add hd0, Real.rpow_one]
      have hne : (d : ℝ) ^ (-(ε : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hd0 _).ne'
      field_simp
    have : (n : ℝ) ^ α * ((ArithmeticFunction.moebius d : ℝ) / d) =
        (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-(ε : ℝ)) * ((n : ℝ) / d) ^ α) := by
      rw [hpow]; ring
    rw [this]; ring
  have hround : |∑ d ∈ Icc 1 D, (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-(ε : ℝ)) *
      (((n / d : ℕ) : ℝ) ^ α - ((n : ℝ) / d) ^ α))| ≤ D := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Icc 1 D, |(ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-(ε : ℝ)) *
        (((n / d : ℕ) : ℝ) ^ α - ((n : ℝ) / d) ^ α))| ≤ 1 := by
      intro d hd
      obtain ⟨hd1, hdD⟩ := mem_Icc.mp hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      have hq1 : 1 ≤ n / d := (Nat.le_div_iff_mul_le hd1).mpr (by nlinarith)
      have hq0 : (0 : ℝ) < ((n / d : ℕ) : ℝ) := by exact_mod_cast hq1
      have hle : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
      have hlt : (n : ℝ) / d - ((n / d : ℕ) : ℝ) ≤ 1 := by
        have := (abs_le.mp (RHTower.Sieve.abs_natDiv_sub_div_le (N := n) hd1)).1
        linarith
      -- mean value: `|x^α − ⌊x⌋^α| ≤ α ⌊x⌋^{α−1}(x − ⌊x⌋) ≤ 1`
      have hmv : |((n / d : ℕ) : ℝ) ^ α - ((n : ℝ) / d) ^ α| ≤ 1 := by
        have h := norm_ofReal_cpow_sub_le (z := (α : ℂ)) (by simpa using hα1) hq0 le_rfl hle
        rw [← Complex.ofReal_cpow (div_nonneg hn0.le hd0.le) α, ← Complex.ofReal_cpow hq0.le α,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hα0, Complex.ofReal_re] at h
        rw [abs_sub_comm]
        have hp : ((n / d : ℕ) : ℝ) ^ (α - 1) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq1) (by linarith)
        have hp0 : 0 ≤ ((n / d : ℕ) : ℝ) ^ (α - 1) := Real.rpow_nonneg hq0.le _
        have hgap : 0 ≤ (n : ℝ) / d - ((n / d : ℕ) : ℝ) := by linarith
        calc _ ≤ α * ((n / d : ℕ) : ℝ) ^ (α - 1) * ((n : ℝ) / d - ((n / d : ℕ) : ℝ)) := h
          _ ≤ 1 * 1 * 1 := by gcongr
          _ = 1 := by norm_num
      have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.abs_moebius_le_one (n := d)
        exact_mod_cast this
      have hdε : (d : ℝ) ^ (-(ε : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by linarith)
      rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hd0 _)]
      calc |(ArithmeticFunction.moebius d : ℝ)| * ((d : ℝ) ^ (-(ε : ℝ)) *
            |((n / d : ℕ) : ℝ) ^ α - ((n : ℝ) / d) ^ α|) ≤ 1 * (1 * 1) := by
            gcongr
        _ = 1 := by norm_num
    calc _ ≤ ∑ _d ∈ Icc 1 D, (1 : ℝ) := sum_le_sum hterm
      _ = D := by simp
  -- the tail: Abel summation against the de la Vallée Poussin rate
  have htail : |∑ d ∈ Ioc D n, (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-(ε : ℝ)) *
      ((n / d : ℕ) : ℝ) ^ α)| ≤ B * sqrtLogDecay (1 / 12) D * ((n : ℝ) ^ α * (3 + Real.log n)) := by
    have hsum_eq : ∑ d ∈ Ioc D n, (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-(ε : ℝ)) *
        ((n / d : ℕ) : ℝ) ^ α) =
        ∑ d ∈ Ioc D n, (ArithmeticFunction.moebius d : ℝ) * inverseFloorWeight ε n d := rfl
    rw [hsum_eq, sum_Ioc_mul_eq_abel _ _ hDn, inverseFloorWeight_succ_self hε1 n, mul_zero,
      zero_sub]
    have hψ : ∀ d : ℕ, D ≤ d → sqrtLogDecay (1 / 12) d ≤ sqrtLogDecay (1 / 12) D := fun d hd =>
      sqrtLogDecay_antitone (by norm_num) (by exact_mod_cast hD1) (by exact_mod_cast hd)
    set K := B * sqrtLogDecay (1 / 12) D with hK
    have hK0 : 0 ≤ K := by rw [hK]; have := sqrtLogDecay_pos (1 / 12) (D : ℝ); positivity
    have hMd : ∀ d : ℕ, D ≤ d →
        |partialSumRow (fun e => (ArithmeticFunction.moebius e : ℝ)) d| ≤ K * d := by
      intro d hd
      have h1 : |mertensRow d| ≤ B * d * sqrtLogDecay (1 / 12) d := hM d (hn.trans hd)
      calc |partialSumRow (fun e => (ArithmeticFunction.moebius e : ℝ)) d| = |mertensRow d| := rfl
        _ ≤ B * d * sqrtLogDecay (1 / 12) d := h1
        _ ≤ B * d * sqrtLogDecay (1 / 12) D :=
            mul_le_mul_of_nonneg_left (hψ d hd) (by positivity)
        _ = K * d := by rw [hK]; ring
    have hsum : |∑ d ∈ Ioc D n, partialSumRow (fun e => (ArithmeticFunction.moebius e : ℝ)) d *
        (inverseFloorWeight ε n d - inverseFloorWeight ε n (d + 1))| ≤
        K * ((D : ℝ) * inverseFloorWeight ε n (D + 1) + ∑ d ∈ Ioc D n, inverseFloorWeight ε n d) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ d ∈ Ioc D n, |partialSumRow (fun e => (ArithmeticFunction.moebius e : ℝ)) d *
          (inverseFloorWeight ε n d - inverseFloorWeight ε n (d + 1))| ≤
          K * ((d : ℝ) * (inverseFloorWeight ε n d - inverseFloorWeight ε n (d + 1))) := by
        intro d hd
        obtain ⟨hDd, -⟩ := mem_Ioc.mp hd
        have hmono := inverseFloorWeight_antitone hε0 hε1 n (d := d) (by omega)
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hmono)]
        calc |partialSumRow (fun e => (ArithmeticFunction.moebius e : ℝ)) d| *
              (inverseFloorWeight ε n d - inverseFloorWeight ε n (d + 1)) ≤
            (K * d) * (inverseFloorWeight ε n d - inverseFloorWeight ε n (d + 1)) :=
              mul_le_mul_of_nonneg_right (hMd d hDd.le) (by linarith)
          _ = _ := by ring
      refine (sum_le_sum hterm).trans ?_
      rw [← mul_sum, sum_Ioc_mul_sub_eq _ hDn, inverseFloorWeight_succ_self hε1 n, mul_zero,
        sub_zero]
    have hDw : (D : ℝ) * inverseFloorWeight ε n (D + 1) ≤ (n : ℝ) ^ α := by
      calc (D : ℝ) * inverseFloorWeight ε n (D + 1) ≤
            ((D + 1 : ℕ) : ℝ) * inverseFloorWeight ε n (D + 1) := by
            push_cast; have := inverseFloorWeight_nonneg (ε : ℝ) n (D + 1); nlinarith
        _ ≤ (n : ℝ) ^ α := natCast_mul_inverseFloorWeight_le hε1 n (by omega)
    have hharm : ∑ d ∈ Ioc D n, inverseFloorWeight ε n d ≤ (n : ℝ) ^ α * (1 + Real.log n) := by
      have hterm : ∀ d ∈ Ioc D n, inverseFloorWeight ε n d ≤ (n : ℝ) ^ α * (1 / (d : ℝ)) := by
        intro d hd
        have hd1 : 1 ≤ d := by have := (mem_Ioc.mp hd).1; omega
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
        have h := natCast_mul_inverseFloorWeight_le hε1 n hd1
        rw [mul_one_div, le_div_iff₀ hd0, mul_comm]
        exact h
      refine (sum_le_sum hterm).trans ?_
      rw [← mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hn0.le _)
      have hsub : ∑ d ∈ Ioc D n, 1 / (d : ℝ) ≤ ∑ d ∈ Icc 1 n, 1 / (d : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (fun d hd => by
          simp only [mem_Ioc, mem_Icc] at hd ⊢; omega) fun _ _ _ => by positivity
      have hh := harmonic_le_one_add_log n
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
      simp only [one_div] at hsub ⊢
      linarith
    have hboundary : |partialSumRow (fun e => (ArithmeticFunction.moebius e : ℝ)) D *
        inverseFloorWeight ε n (D + 1)| ≤ K * (n : ℝ) ^ α := by
      rw [abs_mul, abs_of_nonneg (inverseFloorWeight_nonneg _ _ _)]
      calc |partialSumRow (fun e => (ArithmeticFunction.moebius e : ℝ)) D| *
            inverseFloorWeight ε n (D + 1) ≤ (K * D) * inverseFloorWeight ε n (D + 1) :=
            mul_le_mul_of_nonneg_right (hMd D le_rfl) (inverseFloorWeight_nonneg _ _ _)
        _ = K * ((D : ℝ) * inverseFloorWeight ε n (D + 1)) := by ring
        _ ≤ K * (n : ℝ) ^ α := mul_le_mul_of_nonneg_left hDw hK0
    calc _ ≤ K * (n : ℝ) ^ α + K * ((n : ℝ) ^ α + (n : ℝ) ^ α * (1 + Real.log n)) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_neg]; exact hboundary
          · exact hsum.trans (mul_le_mul_of_nonneg_left (add_le_add hDw hharm) hK0)
      _ = K * ((n : ℝ) ^ α * (3 + Real.log n)) := by ring
  rw [hhead]
  calc |(n : ℝ) ^ α * moebiusHarmonic D + ∑ d ∈ Icc 1 D, (ArithmeticFunction.moebius d : ℝ) *
        ((d : ℝ) ^ (-(ε : ℝ)) * (((n / d : ℕ) : ℝ) ^ α - ((n : ℝ) / d) ^ α)) +
        ∑ d ∈ Ioc D n, (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-(ε : ℝ)) *
          ((n / d : ℕ) : ℝ) ^ α)|
      ≤ |(n : ℝ) ^ α * moebiusHarmonic D| + |∑ d ∈ Icc 1 D, (ArithmeticFunction.moebius d : ℝ) *
        ((d : ℝ) ^ (-(ε : ℝ)) * (((n / d : ℕ) : ℝ) ^ α - ((n : ℝ) / d) ^ α))| +
        |∑ d ∈ Ioc D n, (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-(ε : ℝ)) *
          ((n / d : ℕ) : ℝ) ^ α)| := abs_add_three _ _ _
    _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hn0.le _)]
        linarith

/-! ### Trace-domain membership -/

theorem inversePolePower_zero (ε : SubcriticalDamping) : inversePolePower ε 0 = 0 := by
  simp [inversePolePower, RHTower.floorTransform]

/-- **The inverse pole power has an absolutely summable trace.** -/
theorem summable_abs_inversePolePower_mul_rpow (ε : SubcriticalDamping) :
    Summable fun n : ℕ => |inversePolePower ε n| * (n : ℝ) ^ (-(1 - (ε : ℝ)) - 1) := by
  obtain ⟨B, hB, N₀, hN₀1, hM⟩ := exists_abs_mertensRow_le
  obtain ⟨C, hC, N₁, hN₁1, hm⟩ := exists_abs_moebiusHarmonic_le
  set α : ℝ := 1 - (ε : ℝ) with hα
  have hα2 : 1 / 2 < α := by rw [hα]; linarith [ε.property.2]
  set N₂ := max N₀ N₁ with hN₂
  set G := C + B * 4611 with hG
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hmaj : Summable fun n : ℕ => G * (sqrtLogDecay (1 / 48) n / n) +
      (n : ℝ) ^ (-(α + 1 / 2)) :=
    ((summable_sqrtLogDecay_div (by norm_num)).mul_left G).add
      (Real.summable_nat_rpow.mpr (by linarith))
  refine Summable.of_norm_bounded_eventually hmaj ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (max (N₂ * N₂) 16)] with n hn
  have hn16 : 16 ≤ n := le_of_max_le_right hn
  have hD : N₂ ≤ Nat.sqrt n := Nat.le_sqrt.mpr (le_of_max_le_left hn)
  have hDN₀ : N₀ ≤ Nat.sqrt n := (le_max_left _ _).trans hD
  have hDN₁ : N₁ ≤ Nat.sqrt n := (le_max_right _ _).trans hD
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hq := abs_inversePolePower_le ε hB hN₀1 hM hDN₀
  have hmD := hm _ hDN₁
  have hψ1 := sqrtLogDecay_natSqrt_le (c := 1 / 24) (by norm_num) hn16
  have hψ2 := sqrtLogDecay_natSqrt_le (c := 1 / 12) (by norm_num) hn16
  have habs : (3 + Real.log n) * sqrtLogDecay (1 / 24) n ≤ 4611 * sqrtLogDecay (1 / 48) n := by
    have h := three_add_log_mul_sqrtLogDecay_le (c := 1 / 24) (by norm_num) hnR
    convert h using 2 <;> norm_num
  norm_num at hψ1 hψ2
  have hsqrt : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hpow : (n : ℝ) ^ α * (n : ℝ) ^ (-α - 1) = 1 / n := by
    rw [← Real.rpow_add hn0, show α + (-α - 1) = -1 by ring, Real.rpow_neg_one, one_div]
  have hsq : Real.sqrt n * (n : ℝ) ^ (-α - 1) = (n : ℝ) ^ (-(α + 1 / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]; ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hrp : 0 ≤ (n : ℝ) ^ (-α - 1) := Real.rpow_nonneg hn0.le _
  have hd1 := sqrtLogDecay_pos (1 / 48) (n : ℝ)
  have hd2 := sqrtLogDecay_pos (1 / 24) (n : ℝ)
  have hd12 := sqrtLogDecay_pos (1 / 12) ((Nat.sqrt n : ℕ) : ℝ)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
  calc |inversePolePower ε n| * (n : ℝ) ^ (-α - 1)
      ≤ ((n : ℝ) ^ α * (C * sqrtLogDecay (1 / 24) (Nat.sqrt n)) + Real.sqrt n +
          B * sqrtLogDecay (1 / 12) (Nat.sqrt n) * ((n : ℝ) ^ α * (3 + Real.log n))) *
          (n : ℝ) ^ (-α - 1) := by
        refine mul_le_mul_of_nonneg_right (hq.trans ?_) hrp
        gcongr
    _ = C * sqrtLogDecay (1 / 24) (Nat.sqrt n) * (1 / n) + Real.sqrt n * (n : ℝ) ^ (-α - 1) +
          B * (sqrtLogDecay (1 / 12) (Nat.sqrt n) * (3 + Real.log n)) * (1 / n) := by
        rw [← hpow]; ring
    _ ≤ C * sqrtLogDecay (1 / 48) n * (1 / n) + (n : ℝ) ^ (-(α + 1 / 2)) +
          B * (4611 * sqrtLogDecay (1 / 48) n) * (1 / n) := by
        rw [hsq]
        have hB' : sqrtLogDecay (1 / 12) (Nat.sqrt n) * (3 + Real.log n) ≤
            4611 * sqrtLogDecay (1 / 48) n :=
          calc sqrtLogDecay (1 / 12) (Nat.sqrt n) * (3 + Real.log n) ≤
              sqrtLogDecay (1 / 24) n * (3 + Real.log n) :=
                mul_le_mul_of_nonneg_right hψ2 (by linarith)
            _ = (3 + Real.log n) * sqrtLogDecay (1 / 24) n := by ring
            _ ≤ _ := habs
        have hn1' : 0 ≤ 1 / (n : ℝ) := by positivity
        refine add_le_add (add_le_add ?_ le_rfl) ?_
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hψ1 hC) hn1'
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB' hB) hn1'
    _ = G * (sqrtLogDecay (1 / 48) n / n) + (n : ℝ) ^ (-(α + 1 / 2)) := by rw [hG]; ring

theorem inversePolePower_mem_poleTraceDomain (ε : SubcriticalDamping) :
    inversePolePower ε ∈ poleTraceDomain ε := by
  have hα : 0 < 1 - (ε : ℝ) := by linarith [ε.property.2]
  refine ⟨inversePolePower_zero ε, ?_⟩
  refine ((summable_abs_inversePolePower_mul_rpow ε).mul_left (1 - (ε : ℝ))).of_norm_bounded
    fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [inversePolePower_zero]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mellinCell_nonneg hα hn)]
  calc |inversePolePower ε n| * mellinCell (1 - (ε : ℝ)) n ≤
      |inversePolePower ε n| * ((1 - (ε : ℝ)) * (n : ℝ) ^ (-(1 - (ε : ℝ)) - 1)) :=
        mul_le_mul_of_nonneg_left (mellinCell_bounds hα hn).2 (abs_nonneg _)
    _ = _ := by ring

/-- The inverse pole power as a vector of the trace domain. -/
def inversePoleVector (ε : SubcriticalDamping) : poleTraceDomain ε :=
  ⟨inversePolePower ε, inversePolePower_mem_poleTraceDomain ε⟩

/-! ### The Mellin trace of a dilated row -/

/-- Block telescoping: `Σ_{r<d} cell_w(md + r) = d^{-w} cell_w(m)`. -/
theorem sum_range_mellinCell_block (w : ℝ) {d : ℕ} (m : ℕ) :
    ∑ r ∈ range d, mellinCell w (m * d + r) = (d : ℝ) ^ (-w) * mellinCell w m := by
  have htel : ∀ k, ∑ r ∈ range k, mellinCell w (m * d + r) =
      ((m * d : ℕ) : ℝ) ^ (-w) - ((m * d + k : ℕ) : ℝ) ^ (-w) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih, mellinCell]; push_cast; ring
  rw [htel d, mellinCell]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  push_cast
  rw [show (m : ℝ) * d + d = ((m : ℝ) + 1) * d by ring, Real.mul_rpow (Nat.cast_nonneg m) hd0,
    Real.mul_rpow (by positivity) hd0]
  ring

/-- Partial sums over complete blocks: `Σ_{n < Nd} v(⌊n/d⌋) cell_w(n) = d^{-w} Σ_{m<N} v(m) cell_w(m)`. -/
theorem sum_range_mul_dil_mellinCell (v : ℕ → ℝ) (w : ℝ) {d : ℕ} (hd : 1 ≤ d)
    (N : ℕ) : ∑ n ∈ range (N * d), v (n / d) * mellinCell w n =
      (d : ℝ) ^ (-w) * ∑ m ∈ range N, v m * mellinCell w m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show (N + 1) * d = N * d + d by ring, Finset.sum_range_add, ih, Finset.sum_range_succ,
      mul_add]
    congr 1
    have hdiv : ∀ r ∈ range d, (N * d + r) / d = N := fun r hr => by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (mem_range.mp hr),
        zero_add]
    rw [sum_congr rfl fun r hr => by rw [hdiv r hr], ← mul_sum, sum_range_mellinCell_block]
    ring

/-- **Mellin intertwining of floor dilations.** For `v(0) = 0` with absolutely summable trace,
`Σ_n v(⌊n/d⌋) cell_w(n) = d^{-w} Σ_m v(m) cell_w(m)`. -/
theorem hasSum_dil_mul_mellinCell {v : ℕ → ℝ} (hv0 : v 0 = 0) {w : ℝ} (hw : 0 < w)
    (hv : Summable fun m => |v m| * mellinCell w m) {d : ℕ} (hd : 1 ≤ d) :
    HasSum (fun n => v (n / d) * mellinCell w n) ((d : ℝ) ^ (-w) * ∑' m, v m * mellinCell w m) := by
  have hnn : ∀ n, 0 ≤ |v (n / d)| * mellinCell w n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hv0]
    · exact mul_nonneg (abs_nonneg _) (mellinCell_nonneg hw hn)
  have hvsum : Summable fun m => v m * mellinCell w m := by
    refine hv.of_norm_bounded fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hv0]
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mellinCell_nonneg hw hm)]
  have hsumm : Summable fun n => v (n / d) * mellinCell w n := by
    refine Summable.of_norm_bounded (g := fun n => |v (n / d)| * mellinCell w n) ?_ fun n => ?_
    · refine summable_of_sum_range_le hnn (c := (d : ℝ) ^ (-w) * ∑' m, |v m| * mellinCell w m)
        fun K => ?_
      have hsub : ∑ n ∈ range K, |v (n / d)| * mellinCell w n ≤
          ∑ n ∈ range (K * d), |v (n / d)| * mellinCell w n :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.le_mul_of_pos_right K hd))
          fun n _ _ => hnn n
      refine hsub.trans ?_
      rw [sum_range_mul_dil_mellinCell (fun m => |v m|) w hd K]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hnn' : ∀ m, 0 ≤ |v m| * mellinCell w m := fun m => by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp [hv0]
        · exact mul_nonneg (abs_nonneg _) (mellinCell_nonneg hw hm)
      exact hv.sum_le_tsum _ (fun m _ => hnn' m)
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hv0]
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mellinCell_nonneg hw hn)]
  have hmul : Tendsto (fun N : ℕ => N * d) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => ha.trans (Nat.le_mul_of_pos_right a hd)⟩
  have hlim1 := hsumm.hasSum.tendsto_sum_nat.comp hmul
  have hlim2 : Tendsto (fun N => ∑ n ∈ range (N * d), v (n / d) * mellinCell w n) atTop
      (𝓝 ((d : ℝ) ^ (-w) * ∑' m, v m * mellinCell w m)) := by
    simp_rw [sum_range_mul_dil_mellinCell v w hd]
    exact hvsum.hasSum.tendsto_sum_nat.const_mul _
  have heq : ∑' n, v (n / d) * mellinCell w n = (d : ℝ) ^ (-w) * ∑' m, v m * mellinCell w m :=
    tendsto_nhds_unique hlim1 hlim2
  rw [← heq]; exact hsumm.hasSum

/-! ### The Mellin trace of the inverse pole power off the pole -/

/-- The trace of the pole power `Δ(w) = Σ_m m^α cell_w(m)`. -/
def polePowerTrace (α w : ℝ) : ℝ := ∑' m : ℕ, (m : ℝ) ^ α * mellinCell w m

theorem summable_rpow_mul_mellinCell {α w : ℝ} (hα : 0 < α) (hw : α < w) :
    Summable fun m : ℕ => |(m : ℝ) ^ α| * mellinCell w m := by
  have hw0 : 0 < w := lt_trans hα hw
  refine Summable.of_norm_bounded (g := fun m : ℕ => w * (m : ℝ) ^ (α - w - 1))
    ((Real.summable_nat_rpow.mpr (by linarith)).mul_left w) fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Real.zero_rpow hα.ne']
    exact mul_nonneg hw0.le (Real.rpow_nonneg le_rfl _)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (mellinCell_nonneg hw0 hm)),
    abs_of_pos (Real.rpow_pos_of_pos hm0 _)]
  calc (m : ℝ) ^ α * mellinCell w m ≤ (m : ℝ) ^ α * (w * (m : ℝ) ^ (-w - 1)) :=
        mul_le_mul_of_nonneg_left (mellinCell_bounds hw0 hm).2 (Real.rpow_nonneg hm0.le _)
    _ = w * ((m : ℝ) ^ α * (m : ℝ) ^ (-w - 1)) := by ring
    _ = w * (m : ℝ) ^ (α - w - 1) := by rw [← Real.rpow_add hm0]; ring_nf

/-- **The Mellin trace of `q_ε` off the pole factors.** For real `w > 1 − ε`,
`Σ_n q_ε(n) cell_w(n) = Δ(w) · Σ_d μ(d) d^{-(ε+w)}`. -/
theorem hasSum_inversePolePower_mul_mellinCell (ε : SubcriticalDamping) {w : ℝ}
    (hw : 1 - (ε : ℝ) < w) :
    HasSum (fun n => inversePolePower ε n * mellinCell w n)
      (polePowerTrace (1 - ε) w * ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) *
        (d : ℝ) ^ (-((ε : ℝ) + w))) := by
  set α : ℝ := 1 - (ε : ℝ) with hα
  have hα0 : 0 < α := by rw [hα]; linarith [ε.property.2]
  have hw0 : 0 < w := lt_trans hα0 hw
  have hεw : 1 < (ε : ℝ) + w := by rw [hα] at hw; linarith
  set e : ℕ → ℝ := fun m => (m : ℝ) ^ α with he
  have he0 : e 0 = 0 := by simp [he, Real.zero_rpow hα0.ne']
  set a : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-(ε : ℝ)) with ha
  set F : ℕ → ℕ → ℝ := fun d n => a d * (e (n / d) * mellinCell w n) with hF
  have hesum := summable_rpow_mul_mellinCell hα0 hw
  -- inner sums
  have hinner : ∀ d, HasSum (F d) (a d * ((d : ℝ) ^ (-w) * polePowerTrace α w)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [hF, ha]
    · exact (hasSum_dil_mul_mellinCell he0 hw0 hesum hd).mul_left (a d)
  -- each row is a finite sum over moduli `1 ≤ d ≤ n`
  have hvanish : ∀ n d, d ∉ Icc 1 n → F d n = 0 := by
    intro n d hd
    simp only [mem_Icc, not_and_or, not_le] at hd
    rcases hd with hd | hd
    · have : d = 0 := by omega
      simp [hF, ha, this]
    · simp [hF, he, Nat.div_eq_of_lt hd, Real.zero_rpow hα0.ne']
  have hrow : ∀ n, inversePolePower ε n * mellinCell w n = ∑' d, F d n := by
    intro n
    rw [tsum_eq_sum (s := Icc 1 n) (fun d hd => hvanish n d hd), inversePolePower_eq, sum_mul]
    exact sum_congr rfl fun d _ => by simp only [hF, ha, he]; ring
  -- absolute summability on pairs
  have habsF : ∀ d n, |F d n| ≤ (d : ℝ) ^ (-(ε : ℝ)) * (|e (n / d)| * mellinCell w n) := by
    intro d n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, he0]
    simp only [hF, ha]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (mellinCell_nonneg hw0 hn),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have := mul_nonneg (abs_nonneg (e (n / d))) (mellinCell_nonneg hw0 hn)
    calc |(ArithmeticFunction.moebius d : ℝ)| * (d : ℝ) ^ (-(ε : ℝ)) * (|e (n / d)| * mellinCell w n)
        ≤ 1 * (d : ℝ) ^ (-(ε : ℝ)) * (|e (n / d)| * mellinCell w n) := by gcongr
      _ = _ := by ring
  have hpoleT0 : 0 ≤ polePowerTrace α w := tsum_nonneg fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [Real.zero_rpow hα0.ne']
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (mellinCell_nonneg hw0 hm)
  have habs_e : ∀ m, |e m| = e m := fun m => abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hsumAbs : Summable (Function.uncurry fun d n => |F d n|) := by
    refine (summable_prod_of_nonneg fun _ => abs_nonneg _).mpr ⟨fun d => ?_, ?_⟩
    · exact (hinner d).summable.abs
    · refine Summable.of_nonneg_of_le (fun d => tsum_nonneg fun n => abs_nonneg _) (fun d => ?_)
        (((Real.summable_nat_rpow.mpr (by linarith : -((ε : ℝ) + w) < -1)).mul_left
          (polePowerTrace α w)))
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp [hF, ha]; positivity
      have hdil := hasSum_dil_mul_mellinCell (v := fun m => |e m|) (by simp [he0]) hw0
        (hesum.congr fun m => by simp only [abs_abs, he]) hd
      calc ∑' n, |F d n| ≤ ∑' n, (d : ℝ) ^ (-(ε : ℝ)) * (|e (n / d)| * mellinCell w n) :=
            Summable.tsum_le_tsum (habsF d) (hinner d).summable.abs (hdil.summable.mul_left _)
        _ = (d : ℝ) ^ (-(ε : ℝ)) * ((d : ℝ) ^ (-w) * ∑' m, |e m| * mellinCell w m) := by
            rw [tsum_mul_left, hdil.tsum_eq]
        _ = polePowerTrace α w * (d : ℝ) ^ (-((ε : ℝ) + w)) := by
            have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
            simp only [habs_e]
            simp only [polePowerTrace, he]
            rw [show -((ε : ℝ) + w) = -(ε : ℝ) + -w by ring, Real.rpow_add hd0]
            ring
  have hsumF : Summable (Function.uncurry F) := hsumAbs.of_norm_bounded fun x => by
    rw [Real.norm_eq_abs]; exact le_of_eq rfl
  have hS := hsumF.hasSum
  -- fibres over the modulus `d`
  have h1 := hS.prod_fiberwise fun d => hinner d
  -- fibres over the row index `n`
  have hS' : HasSum (Function.uncurry F ∘ (Equiv.prodComm ℕ ℕ)) (∑' x, Function.uncurry F x) :=
    (Equiv.hasSum_iff (Equiv.prodComm ℕ ℕ)).mpr hS
  have hfin : ∀ n, HasSum (fun d => F d n) (∑' d, F d n) := fun n =>
    (summable_of_ne_finset_zero (s := Icc 1 n) fun d hd => hvanish n d hd).hasSum
  have h2 : HasSum (fun n => ∑' d, F d n) (∑' x, Function.uncurry F x) :=
    hS'.prod_fiberwise fun n => hfin n
  have hval : ∑' d, a d * ((d : ℝ) ^ (-w) * polePowerTrace α w) =
      polePowerTrace α w * ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) *
        (d : ℝ) ^ (-((ε : ℝ) + w)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun d => ?_
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [ha]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    simp only [ha]
    rw [show -((ε : ℝ) + w) = -(ε : ℝ) + -w by ring, Real.rpow_add hd0]
    ring
  have hfun : (fun n => inversePolePower ε n * mellinCell w n) = fun n => ∑' d, F d n :=
    funext hrow
  rw [hfun, ← hval, h1.tsum_eq]
  exact h2

/-! ### The trace is one -/

/-- `Σ_d μ(d) d^{-x} = 1/ζ(x)` for real `x > 1`. -/
theorem ofReal_tsum_moebius_rpow {x : ℝ} (hx : 1 < x) :
    ((∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-x) : ℝ) : ℂ) =
      1 / riemannZeta x := by
  have hxC : 1 < (x : ℂ).re := by simpa using hx
  have hL : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) x = 1 / riemannZeta x := by
    have h := LSeries_one_mul_Lseries_moebius hxC
    rw [LSeries_one_eq_riemannZeta hxC] at h
    exact eq_one_div_of_mul_eq_one_right h
  rw [← hL, LSeries, Complex.ofReal_tsum]
  refine tsum_congr fun d => ?_
  rw [LSeries.term_def₀ (by simp) x d]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg d)]
  push_cast
  rfl

/-- `|Δ(w) − w/(w − α)| ≤ wα(1 + 1/(w + 1 − α))` for `0 < α < w`, `α ≤ 1`. -/
theorem abs_polePowerTrace_sub_le {α w : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hw : α < w) :
    |polePowerTrace α w - w / (w - α)| ≤ w * α * (1 + 1 / (w + 1 - α)) := by
  have hw0 : 0 < w := lt_trans hα hw
  have h := norm_powerPoleSum_sub_partial_le (s := (α : ℂ)) hw0 (by simpa using hα)
    (by simpa using hw) (by simpa using hα1) (q := 0)
  have hP : powerPoleSum w (α : ℂ) = ((polePowerTrace α w : ℝ) : ℂ) := by
    rw [powerPoleSum, polePowerTrace, Complex.ofReal_tsum]
    refine tsum_congr fun m => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg m)]
  simp only [Nat.cast_zero, zero_add, Complex.ofReal_one, Complex.one_cpow,
    mul_one, Nat.cast_one, Real.one_rpow, Finset.Icc_eq_empty_of_lt one_pos, sum_empty,
    sub_zero] at h
  rw [hP] at h
  have hwα : ((w : ℂ) - (α : ℂ)) = ((w - α : ℝ) : ℂ) := by push_cast; ring
  rw [hwα, ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα] at h
  exact h

/-- `(w − α) Δ(w) → α` as `w → α⁺`. -/
theorem tendsto_sub_mul_polePowerTrace {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Tendsto (fun w => (w - α) * polePowerTrace α w) (𝓝[>] α) (𝓝 α) := by
  have hmain : Tendsto (fun w : ℝ => w) (𝓝[>] α) (𝓝 α) := tendsto_nhdsWithin_of_tendsto_nhds
    tendsto_id
  have herr : Tendsto (fun w => (w - α) * polePowerTrace α w - w) (𝓝[>] α) (𝓝 0) := by
    have hbound : ∀ᶠ w in 𝓝[>] α, |(w - α) * polePowerTrace α w - w| ≤
        (w - α) * ((α + 1) * α * 2) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds
        (by linarith : α < α + 1))] with w hw hw1
      have hw : α < w := hw
      have h := abs_polePowerTrace_sub_le hα hα1 hw
      have hwα : 0 < w - α := by linarith
      have heq : (w - α) * polePowerTrace α w - w = (w - α) * (polePowerTrace α w - w / (w - α)) := by
        field_simp
      rw [heq, abs_mul, abs_of_pos hwα]
      refine mul_le_mul_of_nonneg_left (h.trans ?_) hwα.le
      have h1 : 1 / (w + 1 - α) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      have hw1' : w < α + 1 := hw1
      have : w * α ≤ (α + 1) * α := mul_le_mul_of_nonneg_right hw1'.le hα.le
      have hwpos : 0 < w * α := mul_pos (by linarith) hα
      calc w * α * (1 + 1 / (w + 1 - α)) ≤ w * α * 2 :=
            mul_le_mul_of_nonneg_left (by linarith) hwpos.le
        _ ≤ (α + 1) * α * 2 := by linarith
    have hz : Tendsto (fun w => (w - α) * ((α + 1) * α * 2)) (𝓝[>] α) (𝓝 0) := by
      have : Tendsto (fun w : ℝ => (w - α) * ((α + 1) * α * 2)) (𝓝 α) (𝓝 ((α - α) * ((α + 1) * α * 2))) :=
        ((continuous_id.sub continuous_const).mul continuous_const).tendsto α
      rw [sub_self, zero_mul] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hz
    filter_upwards [hbound] with w hw
    rwa [Real.norm_eq_abs]
  have := herr.add hmain
  simpa using this

/-- `(w − α) ζ(w + ε) → 1` as `w → α⁺`, `α = 1 − ε`. -/
theorem tendsto_sub_mul_riemannZeta_add {ε : ℝ} :
    Tendsto (fun w : ℝ => ((w - (1 - ε) : ℝ) : ℂ) * riemannZeta ((w + ε : ℝ) : ℂ))
      (𝓝[>] (1 - ε)) (𝓝 1) := by
  have hres := riemannZeta_residue_one
  have hmap : Tendsto (fun w : ℝ => ((w + ε : ℝ) : ℂ)) (𝓝[>] (1 - ε)) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun w : ℝ => ((w + ε : ℝ) : ℂ)) (𝓝 (1 - ε)) (𝓝 (((1 - ε) + ε : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.comp (continuous_id.add continuous_const)).tendsto _
      rw [show (1 - ε) + ε = (1 : ℝ) by ring, Complex.ofReal_one] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin] with w hw
      have hw : 1 - ε < w := hw
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
  refine (hres.comp hmap).congr fun w => ?_
  simp only [Function.comp]
  push_cast
  ring_nf

/-- **The inverse pole power has unit trace.** -/
theorem poleTrace_inversePoleVector (ε : SubcriticalDamping) :
    poleTrace ε (inversePoleVector ε) = 1 := by
  set α : ℝ := 1 - (ε : ℝ) with hα
  have hα0 : 0 < α := by rw [hα]; linarith [ε.property.2]
  have hα1 : α ≤ 1 := by rw [hα]; linarith [ε.property.1]
  set Fw : ℝ → ℝ := fun w => ∑' n, inversePolePower ε n * mellinCell w n with hFw
  -- off the pole: `Fw w = Δ(w)/ζ(w+ε)`
  have hoff : ∀ w : ℝ, α < w → ((Fw w : ℝ) : ℂ) =
      (((w - α) * polePowerTrace α w : ℝ) : ℂ) / (((w - α : ℝ) : ℂ) * riemannZeta ((w + ε : ℝ) : ℂ)) := by
    intro w hw
    have hεw : 1 < (ε : ℝ) + w := by rw [hα] at hw; linarith
    have hwα : ((w - α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hF : Fw w = polePowerTrace α w * ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) *
        (d : ℝ) ^ (-(w + (ε : ℝ))) := by
      rw [show w + (ε : ℝ) = (ε : ℝ) + w by ring]
      exact (hasSum_inversePolePower_mul_mellinCell ε hw).tsum_eq
    rw [hF, Complex.ofReal_mul (polePowerTrace α w), ofReal_tsum_moebius_rpow (by linarith),
      Complex.ofReal_mul (w - α), mul_div_mul_left _ _ hwα, mul_one_div]
  -- the limit through the off-pole formula
  have hlim1 : Tendsto (fun w => ((Fw w : ℝ) : ℂ)) (𝓝[>] α) (𝓝 ((α : ℝ) : ℂ)) := by
    have hnum : Tendsto (fun w => (((w - α) * polePowerTrace α w : ℝ) : ℂ)) (𝓝[>] α)
        (𝓝 ((α : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (tendsto_sub_mul_polePowerTrace hα0 hα1)
    have hden := tendsto_sub_mul_riemannZeta_add (ε := (ε : ℝ))
    rw [← hα] at hden
    have h := hnum.div hden one_ne_zero
    rw [div_one] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hoff w hw).symm
  -- the limit by dominated convergence
  have hlim2 : Tendsto Fw (𝓝[>] α) (𝓝 (∑' n, inversePolePower ε n * mellinCell α n)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n =>
      (α + 1) * (|inversePolePower ε n| * (n : ℝ) ^ (-α - 1)))
      ((summable_abs_inversePolePower_mul_rpow ε).mul_left _) (fun n => ?_) ?_
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [inversePolePower_zero]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      refine tendsto_nhdsWithin_of_tendsto_nhds (Tendsto.const_mul _ ?_)
      unfold mellinCell
      exact ((Real.continuousAt_const_rpow hn0.ne').comp continuousAt_neg).sub
        ((Real.continuousAt_const_rpow (by positivity)).comp continuousAt_neg) |>.tendsto
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds
        (by linarith : α < α + 1))] with w hw hw1 n
      have hw : α < w := hw
      have hw1' : w < α + 1 := hw1
      have hw0 : 0 < w := lt_trans hα0 hw
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [inversePolePower_zero]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mellinCell_nonneg hw0 hn)]
      have hc := (mellinCell_bounds hw0 hn).2
      have hp : (n : ℝ) ^ (-w - 1) ≤ (n : ℝ) ^ (-α - 1) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
      calc |inversePolePower ε n| * mellinCell w n ≤
          |inversePolePower ε n| * (w * (n : ℝ) ^ (-w - 1)) :=
            mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        _ ≤ |inversePolePower ε n| * ((α + 1) * (n : ℝ) ^ (-α - 1)) := by
            gcongr
        _ = _ := by ring
  have hlim2C : Tendsto (fun w => ((Fw w : ℝ) : ℂ)) (𝓝[>] α)
      (𝓝 (((∑' n, inversePolePower ε n * mellinCell α n : ℝ)) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hlim2
  have heq := tendsto_nhds_unique hlim2C hlim1
  have heqR : ∑' n, inversePolePower ε n * mellinCell α n = α := by exact_mod_cast heq
  change (∑' n, inversePolePower ε n * mellinCell (1 - (ε : ℝ)) n) / (1 - (ε : ℝ)) = 1
  rw [← hα, heqR, div_self hα0.ne']

/-! ### The kernel -/

/-- The total cofactor sum of `q_ε` is the pole power. -/
theorem floorTransform_power_inversePolePower (ε : SubcriticalDamping) {n : ℕ} (hn : 1 ≤ n) :
    RHTower.floorTransform (RHTower.powerWeight ε) (inversePolePower ε) n =
      (n : ℝ) ^ (1 - (ε : ℝ)) := by
  rw [inversePolePower, RHTower.floorTransform_comp,
    ArithmeticOrientationTheory.dirichletConv_comm]
  have h : RHTower.floorTransform (RHTower.dirichletConv (RHTower.moebiusPowerWeight ε)
      (RHTower.powerWeight ε)) (fun m => (m : ℝ) ^ (1 - (ε : ℝ))) n =
      RHTower.floorTransform RHTower.unitWeight (fun m => (m : ℝ) ^ (1 - (ε : ℝ))) n := by
    unfold RHTower.floorTransform
    refine sum_congr rfl fun d hd => ?_
    rw [RHTower.dirichletConv_moebiusPower_power ε (by have := (mem_Icc.mp hd).1; omega)]
  rw [h, RHTower.floorTransform_unitWeight _ hn]

/-- `(I + D̃)v(n) = Σ_{j≤n} j^{-ε} v(⌊n/j⌋) − 𝓛(v) n^{1−ε}`. -/
theorem renormalizedResidualOperator_apply (ε : SubcriticalDamping) (v : poleTraceDomain ε)
    {n : ℕ} (hn : 1 ≤ n) :
    renormalizedResidualOperator ε v n =
      RHTower.floorTransform (RHTower.powerWeight ε) v n - poleTrace ε v * (n : ℝ) ^ (1 - (ε : ℝ)) := by
  change v n + ((∑ j ∈ Icc 2 n, (j : ℝ) ^ (-(ε : ℝ)) * v (n / j)) -
    poleTrace ε v * (n : ℝ) ^ (1 - (ε : ℝ))) = _
  have hIcc : (Icc 1 n : Finset ℕ) = insert 1 (Icc 2 n) := by
    ext j; simp only [mem_insert, mem_Icc]; omega
  rw [RHTower.floorTransform, hIcc, sum_insert (by simp)]
  simp only [RHTower.powerWeight, Nat.cast_one, Real.one_rpow, one_mul, Nat.div_one]
  ring

/-- **`q_ε` is an exact `(−1)`-eigenvector of the renormalized cofactor.** -/
theorem renormalizedResidualOperator_inversePoleVector (ε : SubcriticalDamping) :
    renormalizedResidualOperator ε (inversePoleVector ε) = 0 := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · change inversePolePower ε 0 + ((∑ j ∈ Icc (2 : ℕ) 0, (j : ℝ) ^ (-(ε : ℝ)) *
      inversePolePower ε (0 / j)) -
      poleTrace ε (inversePoleVector ε) * ((0 : ℕ) : ℝ) ^ (1 - (ε : ℝ))) = 0
    have hα : 1 - (ε : ℝ) ≠ 0 := by linarith [ε.property.2]
    simp [inversePolePower_zero, Real.zero_rpow hα]
  rw [renormalizedResidualOperator_apply ε _ hn, poleTrace_inversePoleVector, one_mul]
  change RHTower.floorTransform (RHTower.powerWeight ε) (inversePolePower ε) n - _ = 0
  rw [floorTransform_power_inversePolePower ε hn, sub_self]

/-- **The kernel of the renormalized residual is exactly the inverse-power line.** A trace-domain
row satisfies `v + D̃v = 0` iff `v = 𝓛(v) q_ε`. -/
theorem renormalizedResidual_eq_zero_iff (ε : SubcriticalDamping) (v : poleTraceDomain ε) :
    renormalizedResidualOperator ε v = 0 ↔ v = poleTrace ε v • inversePoleVector ε := by
  constructor
  · intro h
    apply Subtype.ext
    rw [residual_zero_implies_inversePolePower ε v h]
    funext n
    rfl
  · intro h
    rw [h, map_smul, renormalizedResidualOperator_inversePoleVector, smul_zero]

/-- The kernel as a submodule: the line spanned by `q_ε`. -/
theorem ker_renormalizedResidualOperator (ε : SubcriticalDamping) :
    LinearMap.ker (renormalizedResidualOperator ε) = Submodule.span ℝ {inversePoleVector ε} := by
  ext v
  rw [LinearMap.mem_ker, renormalizedResidual_eq_zero_iff, Submodule.mem_span_singleton]
  constructor
  · intro h; exact ⟨poleTrace ε v, h.symm⟩
  · rintro ⟨c, rfl⟩
    rw [map_smul, poleTrace_inversePoleVector, smul_eq_mul, mul_one]

end GaloisForLFunctions.ArithmeticDefectRigidity
