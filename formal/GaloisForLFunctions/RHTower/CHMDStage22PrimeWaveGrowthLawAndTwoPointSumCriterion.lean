import GaloisForLFunctions.RHTower.CHMDStage21DualSinhCoshExactSquareIdentities
import GaloisForLFunctions.RHTower.CHMDGrowthPositivityCollapseAndTwoPointCriterion

/-!
# CHMD Stage 22: Prime-Wave Growth Law, Dual Two-Point Sum Criterion, and Unconditional Off-Line `sinh²` Excess Bound

This module establishes **Stage 22** of the Causal Hyperbolic–Modular Duality (CHMD) route by
uniting the Laplace/Landau growth–positivity collapse of `CHMDGrowthCollapse` with the exact
spectral decomposition of `CHMDStage11` and the dual `sinh`/`cosh` square identities of
`CHMDStage20`–`CHMDStage21`:

1. **Section 1 (Decomposition of `chmdWave` into `chmdPoleWave`, `chmdArchWave`, and
   `chmdPrimeWave`, Uniform Pole+Archimedean Bound, and Sharp $O(e^{|u|/2})$ Prime-Wave Bound):**
   - We decompose the causal wave `chmdWave u = cosineShiftFn Λ sechHalf u` into its three explicit
     components:
     `chmdWave u = chmdPoleWave u + 1 / (2 * π) * chmdArchWave u - chmdPrimeWave u`
     (`chmdWave_eq_pole_add_arch_sub_prime`).
   - We prove that `chmdPoleWave u` and `chmdArchWave u` are **uniformly bounded on all of $\mathbb{R}$**:
     `|chmdPoleWave u| ≤ 2 / cos(1/4)²`,
     `|chmdArchWave u| ≤ ∫ r, sechSqHalf r * |EF.gammaBracket r|`, and
     `|chmdPoleWave u + 1 / (2 * π) * chmdArchWave u| ≤ chmdPoleArchBound`
     (`abs_chmdPoleWave_le`, `abs_chmdArchWave_le`, `abs_chmdPoleWave_add_archWave_le`).
   - Combining this uniform bound with `abs_chmdWave_le` (`|chmdWave u| ≤ kgMass * exp(|u| / 2)`)
     yields the **Unconditional Sharp $O(e^{|u|/2})$ Growth Bound on the Prime Wave**:
     `|chmdPrimeWave u| ≤ (chmdPoleArchBound + kgMass) * Real.exp (|u| / 2)`
     (`abs_chmdPrimeWave_le_exp_half`), sharpening the $O(e^{5/4 |u|})$ contour estimate of
     `CHMDStage3` down to the critical exponent $1/2$, and proving integrability of
     `t ↦ κ t * chmdWave t` and `t ↦ κ t * chmdPrimeWave t` for every continuous kernel $\kappa$
     with $|\kappa(t)| \le C_\kappa e^{-b|t|}$ and $b > 1/2$ (`integrable_mul_chmdWave_of_half_lt`,
     `integrable_mul_chmdPrimeWave_of_half_lt`).

2. **Section 2 (Exact Growth Law of the Prime Wave `chmdPrimeWave` and Pure Prime-Wave Equivalences
   for `RiemannHypothesis`):**
   - Because `chmdPoleWave + (1 / 2π) chmdArchWave` is uniformly bounded on $\mathbb{R}$, the pole
     and archimedean terms drop out of all exponential growth and boundedness criteria. For every
     $0 \le a < 1/2$, an upper bound `chmdPrimeWave u ≤ M * exp(a * u)` on $u \ge 0$, a lower bound
     `-M * exp(a * u) ≤ chmdPrimeWave u` on $u \ge 0$, and a two-sided bound
     `|chmdPrimeWave u| ≤ K * exp(a * |u|)` on $\mathbb{R}$ are each equivalent to
     `∀ ρ, |(kgFreq ρ).im| ≤ a` (`chmdPrimeWave_growth_law`).
   - At $a = 0$, `RiemannHypothesis` is equivalent to `chmdPrimeWave` being bounded below on
     $[0, \infty)$, bounded above on $[0, \infty)$, or bounded on $\mathbb{R}$
     (`riemannHypothesis_iff_chmdPrimeWave_bddBelow`,
     `riemannHypothesis_iff_chmdPrimeWave_bddAbove`,
     `riemannHypothesis_iff_chmdPrimeWave_bounded`).

3. **Section 3 (Dual Two-Point Sum Criterion and Unconditional Off-Line `sinh²` Excess Bound):**
   - We prove the **Dual Two-Point Sum Criterion** (`riemannHypothesis_iff_forall_neg_zero_value_le_chmdWave`,
     `riemannHypothesis_iff_forall_twoPointSum_nonneg`): `RiemannHypothesis` holds if and only if
     `-chmdWave 0 ≤ chmdWave y` for all $y \in \mathbb{R}$, if and only if all 2-point sum packets
     (`twoPointSumCoeff = ![1, 1]`) are nonnegative.
   - Defining the nonnegative off-line hyperbolic defect series
     `chmdOffLineSinhDefect y = ∑' ρ, m_ρ * (Real.sinh (y * (kgFreq ρ).im) ^ 2 / (Complex.cosh (gammaOf ρ / 2) ^ 2).re)`,
     whose summands vanish identically at every critical-line zero $\operatorname{Re} \rho = 1/2$,
     we combine `CHMDStage21` with the zero-side 2-point formulas to prove **unconditionally** for
     all $y \in \mathbb{R}$ that:
     * `-chmdOffLineSinhDefect y ≤ 2 * (chmdWave 0 - chmdWave y)`,
     * `-chmdOffLineSinhDefect y ≤ 2 * (chmdWave 0 + chmdWave y)`,
     * `|chmdWave y| ≤ chmdWave 0 + (1 / 2) * chmdOffLineSinhDefect y`
       (`abs_chmdWave_le_zero_value_add_half_offLineSinhDefect`), and
     * `RiemannHypothesis ↔ chmdOffLineSinhDefect 1 = 0`
       (`riemannHypothesis_iff_chmdOffLineSinhDefect_one_eq_zero`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped Real ComplexConjugate Nat BigOperators

noncomputable section

namespace RHTower.CHMDStage22

open WeilOneSided WeilSpectral RHTower.EvenSector RHTower.WeilPolarMajorant
open RHTower.CHMDStage1 RHTower.CHMDStage2 RHTower.CHMDStage3 RHTower.CHMDStage4
open RHTower.CHMDStage11 RHTower.CHMDStage12 RHTower.CHMDStage13 RHTower.CHMDStage14
open RHTower.CHMDStage15 RHTower.CHMDStage16 RHTower.CHMDStage17 RHTower.CHMDStage18
open RHTower.CHMDStage19 RHTower.CHMDStage20 RHTower.CHMDStage21
open RHTower.CHMDGrowthCollapse
open GaloisForLFunctions.HTGeometry

/-! ## Section 1: Explicit Decomposition of `chmdWave` and Uniform Bounds on `chmdPoleWave` and `chmdArchWave` -/

/-- The pole component `(2 / cos(1/4)²) * cos(u * √(7/4))` of the CHMD causal wave `chmdWave u`. -/
def chmdPoleWave (u : ℝ) : ℝ :=
  evenPolePart (rhoCosShift u sechHalf)

/-- The archimedean component `∫ r, cos(u * √(r² + 2)) * sechSqHalf r * EF.gammaBracket r` of
the CHMD causal wave `chmdWave u`. -/
def chmdArchWave (u : ℝ) : ℝ :=
  evenArchPart (rhoCosShift u sechHalf)

/-- The prime component `evenPrimePart Λ (rhoCosShift u sechHalf)` of the CHMD causal wave
`chmdWave u`. -/
def chmdPrimeWave (u : ℝ) : ℝ :=
  evenPrimePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (rhoCosShift u sechHalf)

/-- Exact closed form of `chmdPoleWave u`. -/
theorem chmdPoleWave_eq (u : ℝ) :
    chmdPoleWave u = (2 / Real.cos (1 / 4 : ℝ) ^ 2) * Real.cos (u * Real.sqrt (7 / 4)) :=
  CHMDStage11.evenPolePart_rhoCosShift_sechHalf u

/-- Exact integral representation of `chmdArchWave u`. -/
theorem chmdArchWave_eq (u : ℝ) :
    chmdArchWave u =
      ∫ r : ℝ, Real.cos (u * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * EF.gammaBracket r :=
  CHMDStage11.evenArchPart_rhoCosShift_sechHalf u

/-- Exact prime-series representation of `chmdPrimeWave u`. -/
theorem chmdPrimeWave_eq (u : ℝ) :
    chmdPrimeWave u =
      ∑' n : ℕ,
        (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ,
            Real.cos (u * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * Real.log n)) := by
  unfold chmdPrimeWave evenPrimePart
  refine tsum_congr fun n => ?_
  congr 2
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  dsimp only
  rw [cosShift_ofReal_re, norm_sechHalf_ofReal_sq]

/-- **Exact Three-Part Decomposition of `chmdWave`**:
`chmdWave u = chmdPoleWave u + 1 / (2 * π) * chmdArchWave u - chmdPrimeWave u`. -/
theorem chmdWave_eq_pole_add_arch_sub_prime (u : ℝ) :
    chmdWave u = chmdPoleWave u + 1 / (2 * Real.pi) * chmdArchWave u - chmdPrimeWave u :=
  rfl

/-- Expressing `chmdPrimeWave u` in terms of `chmdPoleWave u`, `chmdArchWave u`, and `chmdWave u`. -/
theorem chmdPrimeWave_eq_pole_add_arch_sub_chmdWave (u : ℝ) :
    chmdPrimeWave u = chmdPoleWave u + 1 / (2 * Real.pi) * chmdArchWave u - chmdWave u := by
  rw [chmdWave_eq_pole_add_arch_sub_prime]
  ring

theorem chmdPoleWave_neg (u : ℝ) : chmdPoleWave (-u) = chmdPoleWave u := by
  rw [chmdPoleWave_eq, chmdPoleWave_eq, neg_mul, Real.cos_neg]

theorem chmdArchWave_neg (u : ℝ) : chmdArchWave (-u) = chmdArchWave u := by
  rw [chmdArchWave_eq, chmdArchWave_eq]
  congr 1; funext r
  rw [neg_mul, Real.cos_neg]

theorem chmdPrimeWave_neg (u : ℝ) : chmdPrimeWave (-u) = chmdPrimeWave u := by
  rw [chmdPrimeWave_eq_pole_add_arch_sub_chmdWave, chmdPrimeWave_eq_pole_add_arch_sub_chmdWave,
    chmdPoleWave_neg, chmdArchWave_neg, chmdWave_neg]

/-- Continuity of `chmdPoleWave`. -/
theorem continuous_chmdPoleWave : Continuous chmdPoleWave := by
  simp_rw [chmdPoleWave_eq]
  fun_prop

/-- Continuity of `chmdPrimeWave`. -/
theorem continuous_chmdPrimeWave : Continuous chmdPrimeWave :=
  continuous_evenPrimePart_cosShift abs_vonMangoldt_le_sqrt_mul_one_add_log evenStrip_sechHalf

/-- Continuity of `chmdArchWave`. -/
theorem continuous_chmdArchWave : Continuous chmdArchWave := by
  have h : chmdArchWave = fun u => (2 * Real.pi) * (chmdWave u + chmdPrimeWave u - chmdPoleWave u) := by
    funext u
    rw [chmdWave_eq_pole_add_arch_sub_prime]
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    calc chmdArchWave u = (2 * Real.pi) * (1 / (2 * Real.pi)) * chmdArchWave u := by
          rw [mul_one_div_cancel h2pi, one_mul]
      _ = (2 * Real.pi) * (chmdPoleWave u + 1 / (2 * Real.pi) * chmdArchWave u - chmdPrimeWave u +
            chmdPrimeWave u - chmdPoleWave u) := by ring
  rw [h]
  exact continuous_const.mul
    ((continuous_chmdWave.add continuous_chmdPrimeWave).sub continuous_chmdPoleWave)

/-- **Uniform Bound on `chmdPoleWave`**:
for every $u \in \mathbb{R}$, `|chmdPoleWave u| ≤ 2 / Real.cos (1 / 4 : ℝ) ^ 2`. -/
theorem abs_chmdPoleWave_le (u : ℝ) :
    |chmdPoleWave u| ≤ 2 / Real.cos (1 / 4 : ℝ) ^ 2 := by
  have hpos : 0 < 2 / Real.cos (1 / 4 : ℝ) ^ 2 := by
    rw [← evenPolePart_specSq_sechHalf]
    exact evenPolePart_specSq_sechHalf_pos
  rw [chmdPoleWave_eq, abs_mul, abs_of_pos hpos]
  exact mul_le_of_le_one_right hpos.le (Real.abs_cos_le_one _)

/-- Integrability of `r ↦ sechSqHalf r * |EF.gammaBracket r|`. -/
theorem integrable_sechSqHalf_mul_abs_gammaBracket :
    Integrable fun r : ℝ => sechSqHalf r * |EF.gammaBracket r| := by
  have hK := goodDensity_specSq evenStrip_sechHalf
  have h := hK.integrable_mul continuous_abs_gammaBracket (M := |gammaLogConst| + 2)
    abs_abs_gammaBracket_le_linear
  simpa [specSq_sechHalf_ofReal_re] using h

/-- **Uniform Bound on `chmdArchWave`**:
for every $u \in \mathbb{R}$,
`|chmdArchWave u| ≤ ∫ r : ℝ, sechSqHalf r * |EF.gammaBracket r|`. -/
theorem abs_chmdArchWave_le (u : ℝ) :
    |chmdArchWave u| ≤ ∫ r : ℝ, sechSqHalf r * |EF.gammaBracket r| := by
  rw [chmdArchWave_eq]
  refine abs_integral_le_integral_abs.trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
    integrable_sechSqHalf_mul_abs_gammaBracket (Eventually.of_forall fun r => ?_)
  dsimp only
  rw [abs_mul, abs_mul, abs_of_pos (sechSqHalf_pos r)]
  calc |Real.cos (u * Real.sqrt (r ^ 2 + 2))| * sechSqHalf r * |EF.gammaBracket r|
      ≤ 1 * sechSqHalf r * |EF.gammaBracket r| := by
        gcongr
        exact Real.abs_cos_le_one _
    _ = sechSqHalf r * |EF.gammaBracket r| := by ring

/-- The uniform bound constant for the combined Pole + Archimedean wave:
`chmdPoleArchBound = 2 / cos(1/4)² + (1 / 2π) ∫ r, sechSqHalf r * |EF.gammaBracket r|`. -/
def chmdPoleArchBound : ℝ :=
  2 / Real.cos (1 / 4 : ℝ) ^ 2 +
    1 / (2 * Real.pi) * ∫ r : ℝ, sechSqHalf r * |EF.gammaBracket r|

theorem chmdPoleArchBound_nonneg : 0 ≤ chmdPoleArchBound := by
  unfold chmdPoleArchBound
  have hp : 0 < 2 / Real.cos (1 / 4 : ℝ) ^ 2 := by
    rw [← evenPolePart_specSq_sechHalf]
    exact evenPolePart_specSq_sechHalf_pos
  have hint : 0 ≤ ∫ r : ℝ, sechSqHalf r * |EF.gammaBracket r| :=
    integral_nonneg fun r => mul_nonneg (sechSqHalf_pos r).le (abs_nonneg _)
  positivity

/-- **Uniform Bound on the Combined Pole + Archimedean Wave**:
for every $u \in \mathbb{R}$,
`|chmdPoleWave u + 1 / (2 * π) * chmdArchWave u| ≤ chmdPoleArchBound`. -/
theorem abs_chmdPoleWave_add_archWave_le (u : ℝ) :
    |chmdPoleWave u + 1 / (2 * Real.pi) * chmdArchWave u| ≤ chmdPoleArchBound := by
  unfold chmdPoleArchBound
  refine (abs_add_le _ _).trans (add_le_add (abs_chmdPoleWave_le u) ?_)
  rw [abs_mul, abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left (abs_chmdArchWave_le u) (by positivity)

/-- **Unconditional Sharp $O(e^{|u|/2})$ Growth Bound on the Prime Wave `chmdPrimeWave`**:
for every $u \in \mathbb{R}$,
`|chmdPrimeWave u| ≤ (chmdPoleArchBound + kgMass) * Real.exp (|u| / 2)`.
This sharpens the $O(e^{5/4 |u|})$ contour estimate of `CHMDStage3` down to the critical exponent
$1/2$ unconditionally. -/
theorem abs_chmdPrimeWave_le_exp_half (u : ℝ) :
    |chmdPrimeWave u| ≤ (chmdPoleArchBound + kgMass) * Real.exp (|u| / 2) := by
  rw [chmdPrimeWave_eq_pole_add_arch_sub_chmdWave]
  have h1 := (abs_sub (chmdPoleWave u + 1 / (2 * Real.pi) * chmdArchWave u) (chmdWave u)).trans
    (add_le_add (abs_chmdPoleWave_add_archWave_le u) (abs_chmdWave_le u))
  have hexp : 1 ≤ Real.exp (|u| / 2) := Real.one_le_exp (by positivity)
  have hB : chmdPoleArchBound ≤ chmdPoleArchBound * Real.exp (|u| / 2) :=
    le_mul_of_one_le_right chmdPoleArchBound_nonneg hexp
  linarith

/-- **Unconditional Integrability of `t ↦ κ t * chmdWave t` for Any Decay Rate $b > 1/2$**:
relaxing the `5 / 4 < b` requirement to `1 / 2 < b`. -/
theorem integrable_mul_chmdWave_of_half_lt {κ : ℝ → ℝ} (hκc : Continuous κ) {Cκ b : ℝ}
    (hb : 1 / 2 < b) (hκb : ∀ t, |κ t| ≤ Cκ * Real.exp (-(b * |t|))) :
    Integrable fun t : ℝ => κ t * chmdWave t := by
  have hCκ := nonneg_of_abs_le_exp hκb
  have hbound : ∀ t : ℝ, |κ t * chmdWave t| ≤
      (Cκ * kgMass) * Real.exp (-((b - 1 / 2) * |t|)) := fun t => by
    rw [abs_mul]
    calc |κ t| * |chmdWave t|
        ≤ (Cκ * Real.exp (-(b * |t|))) * (kgMass * Real.exp (|t| / 2)) :=
          mul_le_mul (hκb t) (abs_chmdWave_le t) (abs_nonneg _) (by positivity)
      _ = Cκ * kgMass * (Real.exp (-(b * |t|)) * Real.exp (|t| / 2)) := by ring
      _ = (Cκ * kgMass) * Real.exp (-((b - 1 / 2) * |t|)) := by rw [← Real.exp_add]; ring_nf
  exact integrable_of_exp_bound (hκc.mul continuous_chmdWave) (by linarith) hbound

/-- **Unconditional Integrability of `t ↦ κ t * chmdPrimeWave t` for Any Decay Rate $b > 1/2$**:
relaxing the `5 / 4 < b` requirement of `CHMDStage3.integrable_mul_evenPrimePart_cosShift` to
`1 / 2 < b`. -/
theorem integrable_mul_chmdPrimeWave_of_half_lt {κ : ℝ → ℝ} (hκc : Continuous κ) {Cκ b : ℝ}
    (hb : 1 / 2 < b) (hκb : ∀ t, |κ t| ≤ Cκ * Real.exp (-(b * |t|))) :
    Integrable fun t : ℝ => κ t * chmdPrimeWave t := by
  have hCκ := nonneg_of_abs_le_exp hκb
  have hM : 0 ≤ chmdPoleArchBound + kgMass := add_nonneg chmdPoleArchBound_nonneg kgMass_nonneg
  have hbound : ∀ t : ℝ, |κ t * chmdPrimeWave t| ≤
      (Cκ * (chmdPoleArchBound + kgMass)) * Real.exp (-((b - 1 / 2) * |t|)) := fun t => by
    rw [abs_mul]
    calc |κ t| * |chmdPrimeWave t|
        ≤ (Cκ * Real.exp (-(b * |t|))) * ((chmdPoleArchBound + kgMass) * Real.exp (|t| / 2)) :=
          mul_le_mul (hκb t) (abs_chmdPrimeWave_le_exp_half t) (abs_nonneg _) (by positivity)
      _ = Cκ * (chmdPoleArchBound + kgMass) *
            (Real.exp (-(b * |t|)) * Real.exp (|t| / 2)) := by ring
      _ = (Cκ * (chmdPoleArchBound + kgMass)) * Real.exp (-((b - 1 / 2) * |t|)) := by
          rw [← Real.exp_add]; ring_nf
  exact integrable_of_exp_bound (hκc.mul continuous_chmdPrimeWave) (by linarith) hbound

/-! ## Section 2: Exact Growth Law of `chmdPrimeWave` and Pure Prime-Wave Equivalences for `RiemannHypothesis` -/

/-- Upper bound transfer between `chmdWave` and `-chmdPrimeWave`. -/
theorem chmdWave_le_add_poleArchBound (u : ℝ) :
    chmdWave u ≤ -chmdPrimeWave u + chmdPoleArchBound := by
  rw [chmdWave_eq_pole_add_arch_sub_prime]
  have h := (le_abs_self _).trans (abs_chmdPoleWave_add_archWave_le u)
  linarith

/-- Upper bound transfer between `chmdPrimeWave` and `-chmdWave`. -/
theorem chmdPrimeWave_le_neg_chmdWave_add_poleArchBound (u : ℝ) :
    chmdPrimeWave u ≤ -chmdWave u + chmdPoleArchBound := by
  rw [chmdPrimeWave_eq_pole_add_arch_sub_chmdWave]
  have h := (le_abs_self _).trans (abs_chmdPoleWave_add_archWave_le u)
  linarith

/-- Lower bound transfer between `chmdWave` and `-chmdPrimeWave`. -/
theorem neg_chmdPrimeWave_sub_poleArchBound_le_chmdWave (u : ℝ) :
    -chmdPrimeWave u - chmdPoleArchBound ≤ chmdWave u := by
  rw [chmdWave_eq_pole_add_arch_sub_prime]
  have h := (neg_abs_le _).trans' (neg_le_neg (abs_chmdPoleWave_add_archWave_le u))
  linarith

/-- Lower bound transfer between `chmdPrimeWave` and `-chmdWave`. -/
theorem neg_chmdWave_sub_poleArchBound_le_chmdPrimeWave (u : ℝ) :
    -chmdWave u - chmdPoleArchBound ≤ chmdPrimeWave u := by
  rw [chmdPrimeWave_eq_pole_add_arch_sub_chmdWave]
  have h := (neg_abs_le _).trans' (neg_le_neg (abs_chmdPoleWave_add_archWave_le u))
  linarith

/-- **The Exact Growth Law of the CHMD Prime Wave `chmdPrimeWave`**:
for every $0 \le a < 1/2$, an upper exponential bound on `chmdPrimeWave` on $[0, \infty)$, a lower
exponential bound on `chmdPrimeWave` on $[0, \infty)$, and a two-sided exponential bound on
`chmdPrimeWave` on $\mathbb{R}$ are each equivalent to the zero-side frequency displacement bound
`∀ ρ, |(kgFreq ρ).im| ≤ a` (with the pole and archimedean terms dropping out completely). -/
theorem chmdPrimeWave_growth_law {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    ((∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → chmdPrimeWave u ≤ M * Real.exp (a * u)) ↔
      ∀ ρ : zetaZeroConfig.carrier, |(kgFreq ρ).im| ≤ a) ∧
    ((∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → -(M * Real.exp (a * u)) ≤ chmdPrimeWave u) ↔
      ∀ ρ : zetaZeroConfig.carrier, |(kgFreq ρ).im| ≤ a) ∧
    ((∃ K : ℝ, ∀ u : ℝ, |chmdPrimeWave u| ≤ K * Real.exp (a * |u|)) ↔
      ∀ ρ : zetaZeroConfig.carrier, |(kgFreq ρ).im| ≤ a) := by
  obtain ⟨h1, h2, h3⟩ := chmdWave_growth_law ha0 ha
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨M, hM⟩
    rw [← h2]
    refine ⟨M + chmdPoleArchBound, fun u hu => ?_⟩
    have hexp : 1 ≤ Real.exp (a * u) := Real.one_le_exp (mul_nonneg ha0 hu)
    have hB : chmdPoleArchBound ≤ chmdPoleArchBound * Real.exp (a * u) :=
      le_mul_of_one_le_right chmdPoleArchBound_nonneg hexp
    have hlow := neg_chmdPrimeWave_sub_poleArchBound_le_chmdWave u
    have hMu := hM u hu
    linarith
  · intro hρ
    obtain ⟨M, hM⟩ := h2.mpr hρ
    refine ⟨M + chmdPoleArchBound, fun u hu => ?_⟩
    have hexp : 1 ≤ Real.exp (a * u) := Real.one_le_exp (mul_nonneg ha0 hu)
    have hB : chmdPoleArchBound ≤ chmdPoleArchBound * Real.exp (a * u) :=
      le_mul_of_one_le_right chmdPoleArchBound_nonneg hexp
    have hup := chmdPrimeWave_le_neg_chmdWave_add_poleArchBound u
    have hMu := hM u hu
    linarith
  · rintro ⟨M, hM⟩
    rw [← h1]
    refine ⟨M + chmdPoleArchBound, fun u hu => ?_⟩
    have hexp : 1 ≤ Real.exp (a * u) := Real.one_le_exp (mul_nonneg ha0 hu)
    have hB : chmdPoleArchBound ≤ chmdPoleArchBound * Real.exp (a * u) :=
      le_mul_of_one_le_right chmdPoleArchBound_nonneg hexp
    have hup := chmdWave_le_add_poleArchBound u
    have hMu := hM u hu
    linarith
  · intro hρ
    obtain ⟨M, hM⟩ := h1.mpr hρ
    refine ⟨M + chmdPoleArchBound, fun u hu => ?_⟩
    have hexp : 1 ≤ Real.exp (a * u) := Real.one_le_exp (mul_nonneg ha0 hu)
    have hB : chmdPoleArchBound ≤ chmdPoleArchBound * Real.exp (a * u) :=
      le_mul_of_one_le_right chmdPoleArchBound_nonneg hexp
    have hlow := neg_chmdWave_sub_poleArchBound_le_chmdPrimeWave u
    have hMu := hM u hu
    linarith
  · rintro ⟨K, hK⟩
    rw [← h2]
    refine ⟨K + chmdPoleArchBound, fun u hu => ?_⟩
    have hexp : 1 ≤ Real.exp (a * u) := Real.one_le_exp (mul_nonneg ha0 hu)
    have hB : chmdPoleArchBound ≤ chmdPoleArchBound * Real.exp (a * u) :=
      le_mul_of_one_le_right chmdPoleArchBound_nonneg hexp
    have hKu : chmdPrimeWave u ≤ K * Real.exp (a * u) := by
      have := (le_abs_self _).trans (hK u)
      rwa [abs_of_nonneg hu] at this
    have hlow := neg_chmdPrimeWave_sub_poleArchBound_le_chmdWave u
    linarith
  · intro hρ
    obtain ⟨K, hK⟩ := h3.mpr hρ
    refine ⟨K + chmdPoleArchBound, fun u => ?_⟩
    have hexp : 1 ≤ Real.exp (a * |u|) := Real.one_le_exp (mul_nonneg ha0 (abs_nonneg u))
    have hB : chmdPoleArchBound ≤ chmdPoleArchBound * Real.exp (a * |u|) :=
      le_mul_of_one_le_right chmdPoleArchBound_nonneg hexp
    rw [chmdPrimeWave_eq_pole_add_arch_sub_chmdWave]
    have h1' := (abs_sub (chmdPoleWave u + 1 / (2 * Real.pi) * chmdArchWave u) (chmdWave u)).trans
      (add_le_add (abs_chmdPoleWave_add_archWave_le u) (hK u))
    linarith

/-- **Pure Prime-Wave Lower-Bound Equivalence for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if the Klein–Gordon prime wave `chmdPrimeWave` is bounded
below on `[0, ∞)`. -/
theorem riemannHypothesis_iff_chmdPrimeWave_bddBelow :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → -M ≤ chmdPrimeWave u := by
  rw [riemannHypothesis_iff_forall_im_kgFreq_eq_zero]
  have h := (chmdPrimeWave_growth_law (a := 0) le_rfl (by norm_num)).2.1
  simp only [ zero_mul, Real.exp_zero, mul_one] at h
  exact (forall_congr' fun ρ =>
    ⟨fun h0 => by rw [h0, abs_zero], im_kgFreq_eq_zero_of_abs_le_zero⟩).trans h.symm

/-- **Pure Prime-Wave Upper-Bound Equivalence for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if the Klein–Gordon prime wave `chmdPrimeWave` is bounded
above on `[0, ∞)`. -/
theorem riemannHypothesis_iff_chmdPrimeWave_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → chmdPrimeWave u ≤ M := by
  rw [riemannHypothesis_iff_forall_im_kgFreq_eq_zero]
  have h := (chmdPrimeWave_growth_law (a := 0) le_rfl (by norm_num)).1
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  exact (forall_congr' fun ρ =>
    ⟨fun h0 => by rw [h0, abs_zero], im_kgFreq_eq_zero_of_abs_le_zero⟩).trans h.symm

/-- **Pure Prime-Wave Two-Sided Boundedness Equivalence for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if the Klein–Gordon prime wave `chmdPrimeWave` is bounded
on `ℝ`. -/
theorem riemannHypothesis_iff_chmdPrimeWave_bounded :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ u : ℝ, |chmdPrimeWave u| ≤ K := by
  rw [riemannHypothesis_iff_forall_im_kgFreq_eq_zero]
  have h := (chmdPrimeWave_growth_law (a := 0) le_rfl (by norm_num)).2.2
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  exact (forall_congr' fun ρ =>
    ⟨fun h0 => by rw [h0, abs_zero], im_kgFreq_eq_zero_of_abs_le_zero⟩).trans h.symm

/-! ## Section 3: Dual Two-Point Sum Criterion and Unconditional Off-Line `sinh²` Excess Bound -/

/-- **`RiemannHypothesis` ⟺ `-chmdWave 0 ≤ chmdWave y` for every `y ∈ ℝ`** (dual one-sided bound at
the origin). -/
theorem riemannHypothesis_iff_forall_neg_zero_value_le_chmdWave :
    RiemannHypothesis ↔ ∀ y : ℝ, -chmdWave 0 ≤ chmdWave y := by
  constructor
  · intro h y
    have := abs_chmdWave_le_zero_value_of_rh h y
    linarith [neg_abs_le (chmdWave y)]
  · intro h
    exact riemannHypothesis_iff_chmdWave_bddBelow.mpr ⟨chmdWave 0, fun u _ => h u⟩

/-- **`RiemannHypothesis` ⟺ every two-point sum packet of Stage 13 is nonnegative**:
dual to `riemannHypothesis_iff_forall_twoPointDiff_nonneg`, the whole Toeplitz hierarchy also
collapses to the 2-point sum packets `![0, y]`, `![1, 1]`. -/
theorem riemannHypothesis_iff_forall_twoPointSum_nonneg :
    RiemannHypothesis ↔ ∀ y : ℝ, 0 ≤ ∑ i, ∑ j, twoPointSumCoeff i * twoPointSumCoeff j *
      cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf
        (twoPointShift y j - twoPointShift y i) := by
  rw [riemannHypothesis_iff_forall_neg_zero_value_le_chmdWave]
  refine forall_congr' fun y => ?_
  rw [sum_sum_twoPointSum_cosineShiftFn]
  change -chmdWave 0 ≤ chmdWave y ↔ 0 ≤ 2 * (chmdWave 0 + chmdWave y)
  constructor <;> intro h <;> linarith

/-- At every nontrivial zero `ρ`, `(1 / 2) / ‖kgWeight ρ‖ ≤ (Complex.cosh (gammaOf ρ / 2) ^ 2).re`. -/
theorem half_div_norm_kgWeight_le_re_cosh_half_sq_gammaOf (ρ : zetaZeroConfig.carrier) :
    (1 / 2 : ℝ) / ‖kgWeight ρ‖ ≤
      (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).re := by
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 := abs_im_gammaOf_lt ρ
  have hc : 1 / 2 < Real.cos (Zeta23.gammaOf (ρ : ℂ)).im :=
    half_lt_cos_of_abs_le_one (by linarith)
  have hre : (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).re =
      Real.cos ((Zeta23.gammaOf (ρ : ℂ)).im / 2) ^ 2 +
        Real.sinh ((Zeta23.gammaOf (ρ : ℂ)).re / 2) ^ 2 *
          Real.cos (Zeta23.gammaOf (ρ : ℂ)).im := re_cosh_half_sq _
  have hdiv : (1 / 2 : ℝ) / ‖kgWeight ρ‖ =
      (1 / 2 : ℝ) *
        (Real.cos ((Zeta23.gammaOf (ρ : ℂ)).im / 2) ^ 2 +
          Real.sinh ((Zeta23.gammaOf (ρ : ℂ)).re / 2) ^ 2) := by
    rw [show kgWeight ρ = specSq sechHalf (Zeta23.gammaOf (ρ : ℂ)) from rfl,
      norm_specSq_sechHalf, div_inv_eq_mul]
  rw [hdiv, hre]
  nlinarith [sq_nonneg (Real.cos ((Zeta23.gammaOf (ρ : ℂ)).im / 2)),
    sq_nonneg (Real.sinh ((Zeta23.gammaOf (ρ : ℂ)).re / 2))]

/-- At every nontrivial zero `ρ`,
`1 / (Complex.cosh (gammaOf ρ / 2) ^ 2).re ≤ 2 * ‖kgWeight ρ‖`. -/
theorem one_div_re_cosh_half_sq_gammaOf_le_two_mul_norm_kgWeight (ρ : zetaZeroConfig.carrier) :
    1 / (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).re ≤ 2 * ‖kgWeight ρ‖ := by
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 := abs_im_gammaOf_lt ρ
  have hre : 0 < (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).re :=
    re_cosh_half_sq_pos (by linarith)
  have hnorm : 0 < ‖kgWeight ρ‖ := norm_kgWeight_pos ρ
  have h := half_div_norm_kgWeight_le_re_cosh_half_sq_gammaOf ρ
  rw [div_le_iff₀ hnorm] at h
  rw [div_le_iff₀ hre]
  linarith

/-- For every $y \in \mathbb{R}$ and every nontrivial zero `ρ`,
`Real.sinh (y * (kgFreq ρ).im) ^ 2 ≤ Real.sinh (|y| / 2) ^ 2`. -/
theorem sinh_mul_im_kgFreq_sq_le (y : ℝ) (ρ : zetaZeroConfig.carrier) :
    Real.sinh (y * (kgFreq ρ).im) ^ 2 ≤ Real.sinh (|y| / 2) ^ 2 := by
  rw [← sq_abs (Real.sinh (y * (kgFreq ρ).im))]
  have habs : |y * (kgFreq ρ).im| ≤ |y| / 2 := by
    rw [abs_mul]
    have := (abs_im_kgFreq_lt ρ).le
    nlinarith [abs_nonneg y]
  obtain ⟨h1, h2⟩ := abs_le.mp habs
  have hle : |Real.sinh (y * (kgFreq ρ).im)| ≤ Real.sinh (|y| / 2) := by
    refine abs_le.mpr ⟨?_, Real.sinh_le_sinh.mpr h2⟩
    rw [← Real.sinh_neg]
    exact Real.sinh_le_sinh.mpr h1
  exact pow_le_pow_left₀ (abs_nonneg _) hle 2

/-- Unconditional summability of the off-line `sinh²` defect series at every shift $y \in \mathbb{R}$. -/
theorem summable_offLineSinhDefectTerm (y : ℝ) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        (Real.sinh (y * (kgFreq ρ).im) ^ 2 /
          (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).re) := by
  refine Summable.of_nonneg_of_le
    (fun ρ => mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (sq_nonneg _)
        (re_cosh_half_sq_pos (by linarith [abs_im_gammaOf_lt ρ])).le))
    (fun ρ => ?_)
    (summable_mult_mul_norm_kgWeight.mul_right (2 * Real.sinh (|y| / 2) ^ 2))
  have h1 := sinh_mul_im_kgFreq_sq_le y ρ
  have h2 := one_div_re_cosh_half_sq_gammaOf_le_two_mul_norm_kgWeight ρ
  have hre : 0 < (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).re :=
    re_cosh_half_sq_pos (by linarith [abs_im_gammaOf_lt ρ])
  calc (zetaZeroConfig.mult ρ : ℝ) *
        (Real.sinh (y * (kgFreq ρ).im) ^ 2 /
          (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).re)
      = (zetaZeroConfig.mult ρ : ℝ) *
          (Real.sinh (y * (kgFreq ρ).im) ^ 2 *
            (1 / (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).re)) := by ring
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
          (Real.sinh (|y| / 2) ^ 2 * (2 * ‖kgWeight ρ‖)) := by
        gcongr
    _ = (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * (2 * Real.sinh (|y| / 2) ^ 2) := by ring

/-- The nonnegative off-line hyperbolic defect series
`chmdOffLineSinhDefect y = ∑' ρ, m_ρ * (sinh(y * (kgFreq ρ).im)² / (cosh(γ_ρ / 2)²).re)`.
Every critical-line zero (`Re ρ = 1/2`) has `(kgFreq ρ).im = 0` and contributes `0`. -/
def chmdOffLineSinhDefect (y : ℝ) : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) *
      (Real.sinh (y * (kgFreq ρ).im) ^ 2 /
        (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).re)

theorem chmdOffLineSinhDefect_nonneg (y : ℝ) : 0 ≤ chmdOffLineSinhDefect y :=
  tsum_nonneg fun ρ => mul_nonneg (Nat.cast_nonneg _)
    (div_nonneg (sq_nonneg _) (re_cosh_half_sq_pos (by linarith [abs_im_gammaOf_lt ρ])).le)

theorem chmdOffLineSinhDefect_zero : chmdOffLineSinhDefect 0 = 0 := by
  unfold chmdOffLineSinhDefect
  simp

theorem chmdOffLineSinhDefect_neg (y : ℝ) :
    chmdOffLineSinhDefect (-y) = chmdOffLineSinhDefect y := by
  unfold chmdOffLineSinhDefect
  refine tsum_congr fun ρ => ?_
  rw [neg_mul, Real.sinh_neg, neg_sq]

/-- **Unconditional Off-Line `sinh²` Lower Bound for `2 * (chmdWave 0 - chmdWave y)`**:
for every $y \in \mathbb{R}$,
`-chmdOffLineSinhDefect y ≤ 2 * (chmdWave 0 - chmdWave y)`. -/
theorem neg_chmdOffLineSinhDefect_le_two_mul_sub (y : ℝ) :
    -chmdOffLineSinhDefect y ≤ 2 * (chmdWave 0 - chmdWave y) := by
  have hdiff : 2 * (chmdWave 0 - chmdWave y) =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          (4 * Complex.sin ((y : ℂ) * kgFreq ρ / 2) ^ 2 * kgWeight ρ).re := by
    unfold chmdWave CHMDGrowthCollapse.kgFreq kgWeight
    exact two_mul_cosineShiftFn_sechHalf_zero_sub_eq_tsum_four_sin_sq y
  rw [hdiff]
  unfold chmdOffLineSinhDefect
  rw [← tsum_neg]
  have hs1 := (summable_offLineSinhDefectTerm y).neg
  have hs2 : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        (4 * Complex.sin ((y : ℂ) * kgFreq ρ / 2) ^ 2 * kgWeight ρ).re := by
    have h := (summable_re_zeroSide_of_goodDensity
      (goodDensity_specSq (evenStrip_cosComb (twoPointShift y) twoPointDiffCoeff evenStrip_sechHalf))).add
      (summable_re_zeroSide_of_goodDensity
        (goodDensity_specSq (evenStrip_sinComb (twoPointShift y) twoPointDiffCoeff evenStrip_sechHalf)))
    refine h.congr fun ρ => ?_
    rw [← mul_add, ← Complex.add_re,
      specSq_cosComb_add_specSq_sinComb_gammaOf_eq_complexTrigPacketWeight_mul,
      complexTrigPacketWeight_twoPointDiff_eq_four_mul_sin_sq]
    rfl
  refine hs1.tsum_le_tsum (fun ρ => ?_) hs2
  rw [neg_mul_eq_mul_neg]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact neg_sinh_sq_div_le_re_four_sin_sq_mul_specSq_sechHalf
    (by linarith [abs_im_gammaOf_lt ρ]) y

/-- **Unconditional Off-Line `sinh²` Lower Bound for `2 * (chmdWave 0 + chmdWave y)`**:
for every $y \in \mathbb{R}$,
`-chmdOffLineSinhDefect y ≤ 2 * (chmdWave 0 + chmdWave y)`. -/
theorem neg_chmdOffLineSinhDefect_le_two_mul_add (y : ℝ) :
    -chmdOffLineSinhDefect y ≤ 2 * (chmdWave 0 + chmdWave y) := by
  have hsum : 2 * (chmdWave 0 + chmdWave y) =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          (4 * Complex.cos ((y : ℂ) * kgFreq ρ / 2) ^ 2 * kgWeight ρ).re := by
    unfold chmdWave CHMDGrowthCollapse.kgFreq kgWeight
    exact two_mul_cosineShiftFn_sechHalf_zero_add_eq_tsum_four_cos_sq y
  rw [hsum]
  unfold chmdOffLineSinhDefect
  rw [← tsum_neg]
  have hs1 := (summable_offLineSinhDefectTerm y).neg
  have hs2 : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        (4 * Complex.cos ((y : ℂ) * kgFreq ρ / 2) ^ 2 * kgWeight ρ).re := by
    have h := (summable_re_zeroSide_of_goodDensity
      (goodDensity_specSq (evenStrip_cosComb (twoPointShift y) twoPointSumCoeff evenStrip_sechHalf))).add
      (summable_re_zeroSide_of_goodDensity
        (goodDensity_specSq (evenStrip_sinComb (twoPointShift y) twoPointSumCoeff evenStrip_sechHalf)))
    refine h.congr fun ρ => ?_
    rw [← mul_add, ← Complex.add_re,
      specSq_cosComb_add_specSq_sinComb_gammaOf_eq_complexTrigPacketWeight_mul,
      complexTrigPacketWeight_twoPointSum_eq_four_mul_cos_sq]
    rfl
  refine hs1.tsum_le_tsum (fun ρ => ?_) hs2
  rw [neg_mul_eq_mul_neg]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact neg_sinh_sq_div_le_re_four_cos_sq_mul_specSq_sechHalf
    (by linarith [abs_im_gammaOf_lt ρ]) y

/-- **Unconditional Off-Line `sinh²` Excess Bound on `|chmdWave y|`**:
for every $y \in \mathbb{R}$ (without assuming `RiemannHypothesis`),
`|chmdWave y| ≤ chmdWave 0 + (1 / 2) * chmdOffLineSinhDefect y`. -/
theorem abs_chmdWave_le_zero_value_add_half_offLineSinhDefect (y : ℝ) :
    |chmdWave y| ≤ chmdWave 0 + (1 / 2) * chmdOffLineSinhDefect y := by
  have h1 := neg_chmdOffLineSinhDefect_le_two_mul_sub y
  have h2 := neg_chmdOffLineSinhDefect_le_two_mul_add y
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Single-Point Off-Line `sinh²` Defect Characterization of `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if `chmdOffLineSinhDefect 1 = 0`. -/
theorem riemannHypothesis_iff_chmdOffLineSinhDefect_one_eq_zero :
    RiemannHypothesis ↔ chmdOffLineSinhDefect 1 = 0 := by
  rw [riemannHypothesis_iff_forall_im_kgFreq_eq_zero]
  constructor
  · intro h
    unfold chmdOffLineSinhDefect
    simp [h]
  · intro h0 ρ
    have hnn : ∀ σ : zetaZeroConfig.carrier,
        0 ≤ (zetaZeroConfig.mult σ : ℝ) *
          (Real.sinh (1 * (kgFreq σ).im) ^ 2 /
            (Complex.cosh (Zeta23.gammaOf (σ : ℂ) / 2) ^ 2).re) := fun σ =>
      mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (sq_nonneg _) (re_cosh_half_sq_pos (by linarith [abs_im_gammaOf_lt σ])).le)
    have hle := (summable_offLineSinhDefectTerm 1).le_tsum ρ (fun σ _ => hnn σ)
    change _ ≤ chmdOffLineSinhDefect 1 at hle
    rw [h0] at hle
    have hterm0 : (zetaZeroConfig.mult ρ : ℝ) *
        (Real.sinh (1 * (kgFreq ρ).im) ^ 2 /
          (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).re) = 0 :=
      le_antisymm hle (hnn ρ)
    have hm : (0 : ℝ) < zetaZeroConfig.mult ρ := by
      have : 1 ≤ zetaZeroConfig.mult ρ := zetaZeroConfig.one_le_mult _ ρ.2
      exact_mod_cast (by omega : 0 < zetaZeroConfig.mult ρ)
    have hre : 0 < (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).re :=
      re_cosh_half_sq_pos (by linarith [abs_im_gammaOf_lt ρ])
    rcases mul_eq_zero.mp hterm0 with hm0 | hdiv0
    · linarith
    · rw [div_eq_zero_iff] at hdiv0
      rcases hdiv0 with hsq0 | hre0
      · have hsinh0 : Real.sinh (1 * (kgFreq ρ).im) = 0 := sq_eq_zero_iff.mp hsq0
        rw [one_mul] at hsinh0
        exact Real.sinh_injective (by rw [hsinh0, Real.sinh_zero])
      · linarith

end RHTower.CHMDStage22

end
