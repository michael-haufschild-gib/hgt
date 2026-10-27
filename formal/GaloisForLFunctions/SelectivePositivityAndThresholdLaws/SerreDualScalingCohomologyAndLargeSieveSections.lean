import GaloisForLFunctions.ArithmeticEffectivityTheory.TheThetaSurface
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheEffectivityCalculus
import GaloisForLFunctions.ArithmeticOrientationTheory.AnEffectivityFromSectionsThatDoesNotReadTheForm
import GaloisForLFunctions.ArithmeticOrientationTheory.TheWidthDictionary
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheBudgetIsFreeItsSufficiencyIsNot

/-!
# Real-Valued Serre-Dual Cohomology on the Scaling Surface and Large-Sieve Sections

This module constructs real-valued, sign-independent cohomology `(h⁰, h¹)` on polar boxes and on
polar surfaces, verifies the calibration battery across Weil curves over `𝔽_q`, `goldenDatum`, and
`shiftedPairVonMangoldt`, and proves the geometric square-root threshold equivalence identifying
section supply beyond the large-sieve diagonal with zero-free strips (`OQ1 ↔ OQ3`):

1. **Theta log-volume cohomology on polar boxes (`thetaBoxH0`, `thetaBoxH1`):**
   Twisting the 1D Euclidean lattice `ℤ` by the arithmetic box-minus-node divisor
   `E_w(s) = (e^s + s - 1) - ∑_{k ≤ e^s} w(k)` (`generalizedTwoPoleDefect w s`) defines genuine
   strictly positive Gaussian log-volumes `thetaBoxH0 w s > 0` and `thetaBoxH1 w s > 0`
   independently of any quadratic-form sign. Poisson summation (`thetaH0_riemannRoch`) yields
   exact Serre duality under `d ↦ -d` (`thetaH0Dual 0 = thetaH0 0`) and the exact identity
   `thetaBoxH0 w s - thetaBoxH1 w s = E_w(s)` (`= e^s + s - 1 - ψ(e^s)` at `w = Λ`).
   Strict monotonicity of `thetaH0 0` separates `Λ` from `shiftedPairVonMangoldt a` (`a ≠ 0`) for
   every `s ≥ log 2` where rank-based `h0` is blind.

2. **Sign-free polar-box cohomology on surfaces (`surfaceBoxH0`, `surfaceBoxH1`) & Battery:**
   Given any polar surface `S : PolarSurface E`, canonical divisor `K : E`, and sign-free source
   node-cost `Φ : E → ℝ` (never reading `S.pair x x`), `surfaceBoxH0` measures the nonnegative
   volume excess inside the polar box `[0, D · H] × [0, D · V]`, and
   `surfaceBoxH1 S K χ₀ Φ D := surfaceBoxH0 S K χ₀ Φ (K - D)` enforces exact Serre duality.
   - **Weil curves over `𝔽_q`:** With `Φ = frobMassSourceEnergy D W`, the diagonal node budget is
     `2g = Fintype.card ι` (even on non-unitary data), and when `D` is unitary (`‖β_i‖ = 1`),
     `surfaceBoxH0` reproduces `max 0 χ(x)` on the nef quadrant and grows quadratically as
     `(½ x · x) n² + O(n)` along every nef class with `x · x > 0`.
   - **Failure on `goldenDatum`:** On `goldenDatum.windowSurface {0, 1}`, the positive-self-intersection
     nef class `goldenCounterexample` (`x · H = 0, x · V = 0, x · x = 2 > 0`) has
     `surfaceBoxH0 (n • x) + surfaceBoxH1 (n • x) = 0` while `eulerChar (n • x) = n² → +∞`,
     failing the surface Riemann–Roch inequality on the positive cone.

3. **Geometric Square-Root Threshold Equivalence (`OQ1 ↔ OQ3`):**
   - **Graded strip equivalence (`sections_beyond_largeSieve_iff_zetaZeroWidth_le`):** For any
     `σ ∈ [0, 1 / 2)`, existence of a sign-free source obstruction `Φ` on
     `scalingSubsurface (oddRealTestsAt r)` beating the unconditional `12 e^r` large-sieve ceiling
     at rate `O(e^{2σ r} ‖f‖_{H¹}²)` is unconditionally equivalent to `zetaZeroWidth ≤ σ`.
   - **Global RH equivalence (`serreDual_section_growth_iff_riemannHypothesis`):** Existence of a
     nonnegative Serre-dual pair `(h⁰, h¹)` on `scalingSurface` whose sum dominates `χ - o(n²)`
     along rays and whose degree-zero growth is subquadratic (`o(n²)`) is unconditionally
     equivalent to `scalingSurface.HodgeIndex` and `RiemannHypothesis`.
-/

open Complex Filter Real HurwitzZeta Finset Matrix MeasureTheory Set Zeta23
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticEffectivityTheory
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.ArithmeticCorrespondencePositivity
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.SquareRootThreshold
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.SelectivePositivityAndThresholdLaws

set_option autoImplicit false

/-! ### 1. Theta Log-Volume Cohomology on Polar Boxes and Shifted-Pair Selectivity -/

/-- At characteristic `0`, the modulated dual count `thetaH0Dual 0 d` coincides identically with
`thetaH0 0 d`. -/
theorem thetaH0Dual_zero_eq (d : ℝ) : thetaH0Dual 0 d = thetaH0 0 d := by
  unfold thetaH0Dual thetaH0
  simp only [QuotientAddGroup.mk_zero, evenKernel_eq_cosKernel_of_zero]

/-- At characteristic `0`, `thetaH0 0 d > 0` for every real degree `d : ℝ`: the `n = 0` lattice
vector contributes `1` and every `n ≠ 0` contributes a strictly positive Gaussian weight. -/
theorem thetaH0_zero_pos (d : ℝ) : 0 < thetaH0 0 d := by
  unfold thetaH0
  set t : ℝ := Real.exp (-2 * d)
  have ht : 0 < t := Real.exp_pos _
  have hsum := hasSum_int_evenKernel (0 : ℝ) ht
  have hle := hsum.summable.sum_le_tsum ({0, 1} : Finset ℤ)
    (fun j _ => (Real.exp_pos _).le)
  rw [hsum.tsum_eq] at hle
  rw [Finset.sum_pair (by omega : (0 : ℤ) ≠ 1)] at hle
  have hgt1 : 1 < evenKernel (0 : ℝ) t := by
    have h0 : Real.exp (-Real.pi * ((0 : ℤ) + (0 : ℝ)) ^ 2 * t) = 1 := by simp
    have h1 : 0 < Real.exp (-Real.pi * ((1 : ℤ) + (0 : ℝ)) ^ 2 * t) := Real.exp_pos _
    linarith
  exact Real.log_pos hgt1

/-- `d ↦ thetaH0 0 d` is strictly increasing on `ℝ`. -/
theorem thetaH0_zero_strictMono : StrictMono (thetaH0 0) := by
  intro d₁ d₂ hd
  unfold thetaH0
  set t₁ : ℝ := Real.exp (-2 * d₁)
  set t₂ : ℝ := Real.exp (-2 * d₂)
  have ht₁ : 0 < t₁ := Real.exp_pos _
  have ht₂ : 0 < t₂ := Real.exp_pos _
  have ht_lt : t₂ < t₁ := Real.exp_lt_exp.mpr (by linarith)
  have hs₁ := hasSum_int_evenKernel (0 : ℝ) ht₁
  have hs₂ := hasSum_int_evenKernel (0 : ℝ) ht₂
  have hterm_le : ∀ n : ℤ,
      Real.exp (-Real.pi * ((n : ℝ) + 0) ^ 2 * t₁) ≤
        Real.exp (-Real.pi * ((n : ℝ) + 0) ^ 2 * t₂) := fun n => by
    apply Real.exp_le_exp.mpr
    have hsq : 0 ≤ ((n : ℝ) + 0) ^ 2 := sq_nonneg _
    have hpi : 0 ≤ Real.pi * ((n : ℝ) + 0) ^ 2 := mul_nonneg Real.pi_pos.le hsq
    nlinarith
  have hterm_lt_one :
      Real.exp (-Real.pi * (((1 : ℤ) : ℝ) + 0) ^ 2 * t₁) <
        Real.exp (-Real.pi * (((1 : ℤ) : ℝ) + 0) ^ 2 * t₂) := by
    apply Real.exp_lt_exp.mpr
    simp only [Int.cast_one, add_zero, one_pow, mul_one]
    nlinarith [Real.pi_pos]
  have hker_lt : evenKernel (0 : ℝ) t₁ < evenKernel (0 : ℝ) t₂ := by
    have hdiff := hs₂.sub hs₁
    have hpos_diff : 0 < evenKernel (0 : ℝ) t₂ - evenKernel (0 : ℝ) t₁ := by
      have hle1 := hdiff.summable.le_tsum (1 : ℤ) fun n _ => sub_nonneg.mpr (hterm_le n)
      rw [hdiff.tsum_eq] at hle1
      linarith
    linarith
  exact Real.log_lt_log (evenKernel_pos 0 ht₁) hker_lt

/-- **Real-valued theta log-volume `h⁰` of the polar box `[0, s]` with node weight `w`:**
`log ∑_{n ∈ ℤ} exp(-π n² exp(-2 E_w(s)))`, where `E_w(s) = generalizedTwoPoleDefect w s`. -/
def thetaBoxH0 (w : ℕ → ℝ) (s : ℝ) : ℝ :=
  thetaH0 0 (generalizedTwoPoleDefect w s)

/-- **Real-valued Serre-dual theta log-volume `h¹` of the polar box `[0, s]` with node weight `w`:**
defined via the Poisson functional-equation involution `d ↦ -d` as `thetaH0 0 (-E_w(s))`. -/
def thetaBoxH1 (w : ℕ → ℝ) (s : ℝ) : ℝ :=
  thetaH0 0 (-generalizedTwoPoleDefect w s)

/-- **Exact Sign-Free Box Riemann–Roch and Serre Duality (`thetaBox_riemannRoch_and_serreDuality`):**
For **every** arithmetic weight `w : ℕ → ℝ` and **every** box scale `s : ℝ` (defined without
reading any quadratic-form sign):
1. `0 < thetaBoxH0 w s` and `0 < thetaBoxH1 w s`;
2. `thetaBoxH1 w s = thetaH0Dual 0 (-generalizedTwoPoleDefect w s)` (functional-equation Serre duality);
3. `thetaBoxH0 w s - thetaBoxH1 w s = generalizedTwoPoleDefect w s`;
4. At `w = Λ`, `thetaBoxH0 Λ s - thetaBoxH1 Λ s = chebyshevTwoPoleDefect s = e^s + s - 1 - ψ(e^s)`. -/
theorem thetaBox_riemannRoch_and_serreDuality (w : ℕ → ℝ) (s : ℝ) :
    0 < thetaBoxH0 w s ∧
    0 < thetaBoxH1 w s ∧
    thetaBoxH1 w s = thetaH0Dual 0 (-generalizedTwoPoleDefect w s) ∧
    thetaBoxH0 w s - thetaBoxH1 w s = generalizedTwoPoleDefect w s ∧
    thetaBoxH0 (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s -
        thetaBoxH1 (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s =
      chebyshevTwoPoleDefect s := by
  refine ⟨thetaH0_zero_pos _, thetaH0_zero_pos _, (thetaH0Dual_zero_eq _).symm, ?_, ?_⟩
  · unfold thetaBoxH0 thetaBoxH1
    rw [← thetaH0Dual_zero_eq (-generalizedTwoPoleDefect w s)]
    exact thetaH0_riemannRoch 0 (generalizedTwoPoleDefect w s)
  · unfold thetaBoxH0 thetaBoxH1
    rw [← thetaH0Dual_zero_eq (-generalizedTwoPoleDefect _ s),
      thetaH0_riemannRoch 0 _, generalizedTwoPoleDefect, weightedNodeCount]
    rfl

/-- For every nonzero shift `a ≠ 0`, `(2 : ℝ)^a + (2 : ℝ)^(-a) > 2`. -/
theorem two_lt_two_rpow_add_neg {a : ℝ} (ha : a ≠ 0) :
    2 < (2 : ℝ) ^ a + (2 : ℝ) ^ (-a) := by
  have hpos : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  have hprod : (2 : ℝ) ^ a * (2 : ℝ) ^ (-a) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
  have hne1 : (2 : ℝ) ^ a ≠ 1 := by
    intro h1
    have hlog := congrArg Real.log h1
    rw [Real.log_rpow (by norm_num), Real.log_one] at hlog
    exact ha ((mul_eq_zero.mp hlog).resolve_right (Real.log_pos (by norm_num)).ne')
  have hsq : 0 < ((2 : ℝ) ^ a - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne1)
  nlinarith

/-- **Strict Selectivity of `thetaBoxH0` and `thetaBoxH1` Against `shiftedPairVonMangoldt a` (`a ≠ 0`):**
At every scale `s ≥ log 2` and every `a ≠ 0`, whereas rank-based Dirichlet `h0` and `h1` are blind
to replacing `Λ` by `shiftedPairVonMangoldt a`, the theta log-volumes strictly separate them:
`thetaBoxH0 (shiftedPairVonMangoldt a) s < thetaBoxH0 Λ s` and
`thetaBoxH1 Λ s < thetaBoxH1 (shiftedPairVonMangoldt a) s`. -/
theorem thetaBox_strict_selectivity_shiftedPair {a : ℝ} (ha : a ≠ 0) {s : ℝ}
    (hs : Real.log 2 ≤ s) :
    thetaBoxH0 (shiftedPairVonMangoldt a) s <
      thetaBoxH0 (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s ∧
    thetaBoxH1 (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s <
      thetaBoxH1 (shiftedPairVonMangoldt a) s := by
  have hexp2 : (2 : ℝ) ≤ Real.exp s := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp s := Real.exp_le_exp.mpr hs
  have hfl2 : 2 ≤ ⌊Real.exp s⌋₊ := (Nat.le_floor_iff (by positivity)).mpr hexp2
  have h2_mem : (2 : ℕ) ∈ Finset.Icc 0 ⌊Real.exp s⌋₊ := Finset.mem_Icc.mpr ⟨Nat.zero_le 2, hfl2⟩
  have hgt2 : 2 < (2 : ℝ) ^ a + (2 : ℝ) ^ (-a) := two_lt_two_rpow_add_neg ha
  have hterm_le : ∀ k ∈ Finset.Icc 0 ⌊Real.exp s⌋₊,
      (ArithmeticFunction.vonMangoldt k : ℝ) ≤ shiftedPairVonMangoldt a k := fun k _ => by
    have h := two_rpow_mul_vonMangoldt_le_shiftedPair a k
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := k)]
  have hterm_lt : (ArithmeticFunction.vonMangoldt 2 : ℝ) < shiftedPairVonMangoldt a 2 := by
    have h := two_rpow_mul_vonMangoldt_le_shiftedPair a 2
    have hΛ2 : 0 < (ArithmeticFunction.vonMangoldt 2 : ℝ) := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact Real.log_pos (by norm_num)
    nlinarith
  have hsum_lt : weightedNodeCount (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s <
      weightedNodeCount (shiftedPairVonMangoldt a) s :=
    Finset.sum_lt_sum hterm_le ⟨2, h2_mem, hterm_lt⟩
  have hdef_lt : generalizedTwoPoleDefect (shiftedPairVonMangoldt a) s <
      generalizedTwoPoleDefect (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s := by
    unfold generalizedTwoPoleDefect
    linarith
  exact ⟨thetaH0_zero_strictMono hdef_lt, thetaH0_zero_strictMono (neg_lt_neg hdef_lt)⟩

/-! ### 2. Sign-Free Polar-Box Cohomology on Polar Surfaces and the Full Calibration Battery -/

section PolarSurfaceCohomology

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Sign-free polar-box `h⁰` on a polar surface:**
Given a polar surface `S : PolarSurface E`, canonical class `K : E`, constant `χ₀ : ℝ`, and any
source node-cost `Φ : E → ℝ` (built from source evaluations without reading `S.pair D D`),
`surfaceBoxH0` is `0` outside the polar quadrant `{D · H ≥ 0 ∧ D · V ≥ 0}` (where the polar box
`[0, D · H] × [0, D · V]` is empty) and `max 0 (χ₀ + ½ (S.polar D D - Φ D - D · K))` inside it. -/
def surfaceBoxH0 (S : PolarSurface E) (K : E) (χ₀ : ℝ) (Φ : E → ℝ) (D : E) : ℝ :=
  if 0 ≤ S.pair D S.H ∧ 0 ≤ S.pair D S.V then
    max 0 (χ₀ + (S.polar D D - Φ D - S.pair D K) / 2)
  else 0

/-- **Serre-dual polar-box cohomology `h¹(D) := h⁰(K - D)`:**
defined via the canonical involution `D ↦ K - D` (on curves/boxes `h¹`, on surfaces the Serre-dual
top cohomology `h²(D) = h⁰(K - D)`). -/
def surfaceBoxH1 (S : PolarSurface E) (K : E) (χ₀ : ℝ) (Φ : E → ℝ) (D : E) : ℝ :=
  surfaceBoxH0 S K χ₀ Φ (K - D)

theorem surfaceBoxH0_nonneg (S : PolarSurface E) (K : E) (χ₀ : ℝ) (Φ : E → ℝ) (D : E) :
    0 ≤ surfaceBoxH0 S K χ₀ Φ D := by
  unfold surfaceBoxH0
  split_ifs
  · exact le_max_left 0 _
  · exact le_rfl

theorem surfaceBoxH1_nonneg (S : PolarSurface E) (K : E) (χ₀ : ℝ) (Φ : E → ℝ) (D : E) :
    0 ≤ surfaceBoxH1 S K χ₀ Φ D :=
  surfaceBoxH0_nonneg S K χ₀ Φ (K - D)

/-- **Exact Serre Duality Involution (`surfaceBox_serreDuality`):**
`surfaceBoxH1(D) = surfaceBoxH0(K - D)`, `surfaceBoxH1(K - D) = surfaceBoxH0(D)`, and
`surfaceBoxH0(D) + surfaceBoxH1(D)` is invariant under `D ↦ K - D`. -/
theorem surfaceBox_serreDuality (S : PolarSurface E) (K : E) (χ₀ : ℝ) (Φ : E → ℝ) (D : E) :
    surfaceBoxH1 S K χ₀ Φ D = surfaceBoxH0 S K χ₀ Φ (K - D) ∧
    surfaceBoxH1 S K χ₀ Φ (K - D) = surfaceBoxH0 S K χ₀ Φ D ∧
    surfaceBoxH0 S K χ₀ Φ (K - D) + surfaceBoxH1 S K χ₀ Φ (K - D) =
      surfaceBoxH0 S K χ₀ Φ D + surfaceBoxH1 S K χ₀ Φ D := by
  refine ⟨rfl, ?_, ?_⟩
  · unfold surfaceBoxH1
    rw [sub_sub_cancel]
  · unfold surfaceBoxH1
    rw [sub_sub_cancel, add_comm]

/-- When `Φ` represents `S.defect` (`∀ z, S.defect z z = Φ z`), `surfaceBoxH0` satisfies the
Riemann–Roch lower bound `eulerChar S K χ₀ D ≤ surfaceBoxH0 S K χ₀ Φ D + surfaceBoxH1 S K χ₀ Φ D`
on every class `D` in the polar quadrant `{0 ≤ D · H ∧ 0 ≤ D · V}`, and grows quadratically along
every nef class with `D · D > 0`. -/
theorem surfaceBox_riemannInequality_and_growth_of_eq_defect (S : PolarSurface E) (K : E)
    (χ₀ : ℝ) (Φ : E → ℝ) (hrep : ∀ z : E, S.defect z z = Φ z) :
    (∀ D : E, 0 ≤ S.pair D S.H → 0 ≤ S.pair D S.V →
      eulerChar S K χ₀ D ≤ surfaceBoxH0 S K χ₀ Φ D + surfaceBoxH1 S K χ₀ Φ D) ∧
    (∀ D : E, 0 ≤ S.pair D S.H → 0 ≤ S.pair D S.V → 0 < S.pair D D →
      ∀ c : ℝ, c < S.pair D D / 2 →
        ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ 2 ≤ surfaceBoxH0 S K χ₀ Φ ((n : ℝ) • D)) := by
  have hchar : ∀ z : E, χ₀ + (S.polar z z - Φ z - S.pair z K) / 2 = eulerChar S K χ₀ z := by
    intro z
    rw [← hrep z]
    have hd : S.polar z z - S.defect z z = S.pair z z := by
      unfold PolarSurface.defect; ring
    rw [hd]
    unfold eulerChar
    simp only [map_sub]
    ring
  refine ⟨fun D hDH hDV => ?_, fun D hDH hDV hDD c hc => ?_⟩
  · unfold surfaceBoxH0
    rw [if_pos ⟨hDH, hDV⟩, hchar D]
    have h0 := surfaceBoxH1_nonneg S K χ₀ Φ D
    have h1 := le_max_right 0 (eulerChar S K χ₀ D)
    linarith
  · have hgap : 0 < S.pair D D / 2 - c := by linarith
    filter_upwards [eventually_affine_lt_quadratic hgap (|S.pair D K| / 2) |χ₀|] with n hn
    have hnH : 0 ≤ S.pair ((n : ℝ) • D) S.H := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (Nat.cast_nonneg n) hDH
    have hnV : 0 ≤ S.pair ((n : ℝ) • D) S.V := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (Nat.cast_nonneg n) hDV
    unfold surfaceBoxH0
    rw [if_pos ⟨hnH, hnV⟩, hchar ((n : ℝ) • D), eulerChar_smul]
    refine le_trans ?_ (le_max_right 0 _)
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hDK : -(n : ℝ) * S.pair D K ≥ -(n : ℝ) * |S.pair D K| := by
      nlinarith [le_abs_self (S.pair D K)]
    have hχ : -|χ₀| ≤ χ₀ := neg_abs_le χ₀
    nlinarith [sq_nonneg (n : ℝ)]

end PolarSurfaceCohomology

/-- **Battery Check 1 — Weil Curves over `𝔽_q` (`curve_frobMass_cohomology_calibration`):**
For any `CurveDatum D`:
1. The Frobenius-mass source cost on `{0}` assigns the exact genus budget `2g = Fintype.card ι` to
   the diagonal `(0, 0, Pi.single 0 1)` without assuming unitarity;
2. When `D` is unitary (`∀ i, ‖D.β i‖ = 1`), `surfaceBoxH0` and `surfaceBoxH1` with
   `Φ = frobMassSourceEnergy D W` satisfy the Riemann inequality on the nef quadrant and grow
   quadratically along every nef class with positive self-intersection. -/
theorem curve_frobMass_cohomology_calibration {ι : Type*} [Fintype ι] (D : CurveDatum ι) :
    frobMassSourceEnergy D {0} (0, 0, Pi.single 0 1) = Fintype.card ι ∧
    ((∀ i : ι, ‖D.β i‖ = 1) → ∀ (W : Finset ℕ) (K : SpanCycle) (χ₀ : ℝ),
      (∀ x : SpanCycle, 0 ≤ (D.windowSurface W).pair x (D.windowSurface W).H →
        0 ≤ (D.windowSurface W).pair x (D.windowSurface W).V →
        eulerChar (D.windowSurface W) K χ₀ x ≤
          surfaceBoxH0 (D.windowSurface W) K χ₀ (frobMassSourceEnergy D W) x +
            surfaceBoxH1 (D.windowSurface W) K χ₀ (frobMassSourceEnergy D W) x) ∧
      (∀ x : SpanCycle, 0 ≤ (D.windowSurface W).pair x (D.windowSurface W).H →
        0 ≤ (D.windowSurface W).pair x (D.windowSurface W).V →
        0 < (D.windowSurface W).pair x x →
        ∀ c : ℝ, c < (D.windowSurface W).pair x x / 2 →
          ∀ᶠ n : ℕ in atTop,
            c * (n : ℝ) ^ 2 ≤
              surfaceBoxH0 (D.windowSurface W) K χ₀ (frobMassSourceEnergy D W) ((n : ℝ) • x))) := by
  refine ⟨?_, fun hβ W K χ₀ => ?_⟩
  · unfold frobMassSourceEnergy
    rw [frobeniusMass_frobEvalMatrix_eq_frobSquareMass]
    unfold CurveDatum.frobSquareMass frobPoly
    simp
  · have hrep := (frobMassSectionCone_bezout_and_eq_of_unitary D hβ W).2.1
    exact surfaceBox_riemannInequality_and_growth_of_eq_defect
      (D.windowSurface W) K χ₀ (frobMassSourceEnergy D W) hrep

/-- **Battery Check 2 — Refutation of Riemann–Roch on `goldenDatum`'s Positive Cone:**
On `S = goldenDatum.windowSurface {0, 1}` (`K = 0, χ₀ = 0`), the nef cycle `goldenCounterexample`
has `0 ≤ x · H`, `0 ≤ x · V`, and `x · x = 2 > 0`, so `eulerChar S 0 0 ((n : ℝ) • x) = n²` for
every `n ≥ 1`, yet `surfaceBoxH0 S 0 0 (frobMassSourceEnergy goldenDatum {0, 1}) ((n : ℝ) • x) +
surfaceBoxH1 S 0 0 (frobMassSourceEnergy goldenDatum {0, 1}) ((n : ℝ) • x) = 0` for every `n : ℕ`. -/
theorem goldenDatum_frobMass_cohomology_refutes_riemannRoch :
    let W : Finset ℕ := {0, 1}
    let S := goldenDatum.windowSurface W
    let x := goldenCounterexample
    0 ≤ S.pair x S.H ∧
    0 ≤ S.pair x S.V ∧
    S.pair x x = 2 ∧
    (∀ n : ℕ, eulerChar S 0 0 ((n : ℝ) • x) = (n : ℝ) ^ 2) ∧
    (∀ n : ℕ,
      surfaceBoxH0 S 0 0 (frobMassSourceEnergy goldenDatum W) ((n : ℝ) • x) +
        surfaceBoxH1 S 0 0 (frobMassSourceEnergy goldenDatum W) ((n : ℝ) • x) = 0) := by
  intro W S x
  obtain ⟨hH0, hV0, hxx⟩ := goldenCounterexample_violates_hodgeIndex
  refine ⟨hH0.ge, hV0.ge, hxx, fun n => ?_, fun n => ?_⟩
  · rw [eulerChar_smul, hxx]
    simp
  · have h0_general : ∀ c : ℝ,
        surfaceBoxH0 S 0 0 (frobMassSourceEnergy goldenDatum W) (c • x) = 0 := by
      intro c
      have hcH : S.pair (c • x) S.H = 0 := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hH0, mul_zero]
      have hcV : S.pair (c • x) S.V = 0 := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hV0, mul_zero]
      have hcpol : S.polar (c • x) (c • x) = 0 := by
        rw [S.polar_self, hcH, mul_zero, zero_mul]
      have hcK : S.pair (c • x) 0 = 0 := map_zero _
      have hnn : 0 ≤ frobMassSourceEnergy goldenDatum W (c • x) :=
        (defect_eq_frobReflected_and_le_frobMass goldenDatum W (c • x)).1
      unfold surfaceBoxH0
      rw [if_pos ⟨hcH.ge, hcV.ge⟩, hcpol, hcK]
      exact max_eq_left (by linarith)
    have h1 := h0_general (n : ℝ)
    have h2 : surfaceBoxH1 S 0 0 (frobMassSourceEnergy goldenDatum W) ((n : ℝ) • x) = 0 := by
      unfold surfaceBoxH1
      rw [zero_sub, ← neg_smul]
      exact h0_general (-(n : ℝ))
    linarith

/-! ### 3. The Geometric Square-Root Threshold Equivalence (`OQ1 ↔ OQ3`) -/

/-- **Graded Geometric Square-Root Threshold Equivalence (`OQ1 ↔ OQ3` at Width `σ`):**
For every `σ ≥ 0`, the following are unconditionally equivalent:
1. `zetaZeroWidth ≤ σ` (analytic zero-free strip of width `1/2 - σ`, strictly beating the
   large-sieve `X = T` boundary `σ = 1/2` whenever `σ < 1/2`);
2. `oddDefectFloorRate ≤ σ` (Castelnuovo–Severi odd-sector defect growth rate);
3. For every `β > σ`, there exist `C ≥ 0` and a nonnegative sub-large-sieve shortfall bound
   `Φ : (r : ℝ) → (ℝ × ℝ × oddRealTestsAt r) → ℝ` satisfying
   `0 ≤ (scalingSubsurface (oddRealTestsAt r)).defect x x + Φ r x` (equivalently, paying
   `apertureH1ChebyshevCorrection r F ≤ archGaugeBudget r R F + Φ r x`) and
   `Φ r x ≤ C e^{2β r} (∫ f² + ∫ (f')²)`. -/
theorem sections_beyond_largeSieve_iff_zetaZeroWidth_le {σ : ℝ} (hσ : 0 ≤ σ) :
    List.TFAE [zetaZeroWidth ≤ σ,
      oddDefectFloorRate ≤ σ,
      ∀ β : ℝ, σ < β → ∃ C : ℝ, 0 ≤ C ∧
        ∃ Φ : (r : ℝ) → (ℝ × ℝ × oddRealTestsAt r) → ℝ,
          (∀ r > 0, ∀ x, 0 ≤ Φ r x) ∧
          (∀ r > 0, ∀ x, 0 ≤ (scalingSubsurface (oddRealTestsAt r)).defect x x + Φ r x) ∧
          (∀ r > 0, ∀ x : ℝ × ℝ × oddRealTestsAt r,
            Φ r x ≤ C * Real.exp (2 * β * r) *
              ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2))] := by
  tfae_have 1 ↔ 2 := by rw [oddDefectFloorRate_eq_zetaZeroWidth]
  tfae_have 1 → 3 := by
    intro hle β hβ
    obtain ⟨C, hC0, hfloor⟩ :=
      (zetaZeroWidth_le_iff_scalingSubsurface_odd_sobolev_defect_floor hσ).mp hle β hβ
    refine ⟨C, hC0, fun r x => C * Real.exp (2 * β * r) *
        ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2),
      fun r _ x => ?_, fun r hr x => ?_, fun _ _ _ => le_rfl⟩
    · have hsob : 0 ≤ (∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2 :=
        add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
      exact mul_nonneg (mul_nonneg hC0 (Real.exp_nonneg _)) hsob
    · have hf := hfloor r hr x
      linarith
  tfae_have 3 → 1 := by
    intro h3
    refine (zetaZeroWidth_le_iff_scalingSubsurface_odd_sobolev_defect_floor hσ).mpr fun β hβ => ?_
    obtain ⟨C, hC0, Φ, _, hdef, hbd⟩ := h3 β hβ
    refine ⟨C, hC0, fun r hr x => ?_⟩
    linarith [hdef r hr x, hbd r hr x]
  tfae_finish

/-- **Global Serre-Dual Section-Growth Equivalence to `RiemannHypothesis` (`OQ1 = OQ3` at `σ = 0`):**
The following are unconditionally equivalent on `scalingSurface`:
1. `RiemannHypothesis`;
2. `scalingSurface.HodgeIndex`;
3. Existence of real-valued nonnegative `h⁰, h¹ : ScalingCycle → ℝ` satisfying exact Serre duality
   `h¹(D) = h⁰(K - D)`, asymptotic Riemann–Roch lower bound
   `h⁰(n • D) + h¹(n • D) ≥ eulerChar scalingSurface K χ₀ (n • D) - o(n²)` along every ray, and
   subquadratic degree-zero growth `DegreeZeroSubquadratic scalingSurface K h⁰`. -/
theorem serreDual_section_growth_iff_riemannHypothesis (K : ScalingCycle) (χ₀ : ℝ) :
    List.TFAE [RiemannHypothesis,
      scalingSurface.HodgeIndex,
      ∃ h0_fn h1_fn : ScalingCycle → ℝ,
        (∀ D, 0 ≤ h0_fn D) ∧
        (∀ D, h1_fn D = h0_fn (K - D)) ∧
        (∀ D : ScalingCycle, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
          eulerChar scalingSurface K χ₀ ((n : ℝ) • D) - ε * (n : ℝ) ^ 2 ≤
            h0_fn ((n : ℝ) • D) + h1_fn ((n : ℝ) • D)) ∧
        DegreeZeroSubquadratic scalingSurface K h0_fn] := by
  tfae_have 1 ↔ 2 := scalingSurface_hodgeIndex_iff.symm
  tfae_have 2 → 3 := by
    intro hHI
    refine ⟨optimalEffectivity scalingSurface K χ₀,
      fun D => optimalEffectivity scalingSurface K χ₀ (K - D),
      fun D => div_nonneg (le_max_left 0 _) (by norm_num),
      fun _ => rfl,
      fun D ε hε => ?_, ?_⟩
    · filter_upwards with n
      have hri := riemannInequality_optimalEffectivity scalingSurface K χ₀ ((n : ℝ) • D)
      have hnn : 0 ≤ ε * (n : ℝ) ^ 2 := mul_nonneg hε.le (sq_nonneg _)
      linarith
    · intro x hx c hc
      have hAmple : scalingSurface.AmpleHodgeIndex :=
        scalingSurface.ampleHodgeIndex_iff_castelnuovoSeveri.mpr
          (scalingSurface.hodgeIndex_iff_castelnuovoSeveri.mp hHI)
      have hxx : scalingSurface.pair x x ≤ 0 := hAmple x hx
      have hmax0 : max 0 (scalingSurface.pair x x / 2) = 0 := max_eq_left (by linarith)
      refine Eventually.frequently ?_
      filter_upwards [eventually_optimalEffectivity_le scalingSurface K χ₀ x (half_pos hc),
        eventually_ge_atTop (1 : ℕ)] with n hn hn1
      rw [hmax0, zero_add] at hn
      have hn_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        nlinarith
      nlinarith
  tfae_have 3 → 2 := by
    rintro ⟨h0_fn, h1_fn, _, hserre, hari, hsub⟩
    suffices hAmple : scalingSurface.AmpleHodgeIndex from
      scalingSurface.hodgeIndex_iff_castelnuovoSeveri.mpr
        (scalingSurface.ampleHodgeIndex_iff_castelnuovoSeveri.mp hAmple)
    intro x hx
    by_contra hpos
    push Not at hpos
    have hq : 0 < scalingSurface.pair x x / 8 := by linarith
    have hev_lo : ∀ᶠ n : ℕ in atTop,
        (scalingSurface.pair x x / 4) * (n : ℝ) ^ 2 ≤
          h0_fn ((n : ℝ) • x) + h0_fn (K - (n : ℝ) • x) := by
      filter_upwards [hari x (scalingSurface.pair x x / 8) hq,
        eventually_affine_lt_quadratic hq (scalingSurface.pair x K / 2) (-χ₀)] with n h1 h2
      rw [eulerChar_smul, hserre ((n : ℝ) • x)] at h1
      nlinarith
    obtain ⟨n, hn_hi, hn_lo⟩ := ((hsub x hx (scalingSurface.pair x x / 8) hq).and_eventually hev_lo).exists
    nlinarith [sq_nonneg (n : ℝ)]
  tfae_finish

end GaloisForLFunctions.SelectivePositivityAndThresholdLaws
