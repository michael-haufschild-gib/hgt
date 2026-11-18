import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheExplicitFormulaHoldsForTwoSidedTests
import GaloisForLFunctions.ExclusionOfTheCriticalState.WeilsFormOnProbesIsTheCaratheodoryKernelOfXi
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheExponentialProbesLieInTheEnergyDomain
import GaloisForLFunctions.RHTower.XiCosineShiftLaguerrePolya

/-!
# Single-Functional Rank-Two Completion of Weil's Form, RH Separation, and Shifted-Probe Resonance

This module establishes the rank-two completion structure of Weil's half-line bare form
`bareMixedEnergy` under `HasSingleOffLineQuartet ρ₀`, separates its weak positivity law from its
cosh-surplus lower bound relative to `RiemannHypothesis`, and proves exponential resonance of
translated probes:

1. **Multiplicity-rank-invariant rank-two completion and hyperplane dichotomy**
   (`rankTwoCompletedWeil_eq_onLineMixed_add_cosh`,
   `bareMixedEnergy_add_sinhFunctional_sq_eq`,
   `coshFunctional_sq_le_bareMixedEnergy_add_sinhFunctional_sq`,
   `bareMixedEnergy_sinhOrthogonal_eq_and_ge`,
   `bareMixedEnergy_coshOrthogonal_eq`,
   `rankTwoCompletedWeil_cauchy_schwarz`):
   With `Δ_{ρ₀}(G) = L G(1/2 - conj ρ₀) - L G(ρ₀ - 1/2)` (`quartetSinhFunctional`) and
   `Σ_{ρ₀}(G) = L G(1/2 - conj ρ₀) + L G(ρ₀ - 1/2)` (`quartetCoshFunctional`), for arbitrary
   quartet multiplicity `m = quartetCopyMult ρ₀ ≥ 1` and every `G ∈ CriticalHalfLineEnergyDomain`:
   `bareMixedEnergy G G + m ‖Δ_{ρ₀}(G)‖² = onLineEnergy G + m ‖Σ_{ρ₀}(G)‖² ≥ m ‖Σ_{ρ₀}(G)‖² ≥ 0`.
   Thus a single complex linear functional (real rank `2`, independent of `m`) completes Weil's
   form to a positive-semidefinite bilinear form satisfying global Cauchy–Schwarz.

2. **RH consistency of the weak completion vs. uniform lag bound on `RiemannHypothesis`**
   (`bareMixedEnergy_eq_onLineMixed_of_riemannHypothesis`,
   `rankTwoCompletedWeil_nonneg_of_riemannHypothesis`,
   `abs_onLineMixed_shiftProfile_le`,
   `abs_bareMixedEnergy_probe_shiftProfile_le_of_riemannHypothesis`):
   Under `RiemannHypothesis`, `bareMixedEnergy G G = onLineEnergy G ≥ 0`, so the weak completion
   `0 ≤ bareMixedEnergy G G + m ‖Δ_{ρ₀}(G)‖²` holds for **every** `(ρ₀, m)`, proving unconditionally
   that no contradiction can be derived from the weak completion alone without refuting
   `RiemannHypothesis`. Moreover, for every `p > 4` and `R ≥ 0`,
   `|bareMixedEnergy (probe p) (shiftProfile (probe p) R)| ≤ probeSymbol p / p`.

3. **Shifted-probe resonance and refutation of cosh-surplus under `RiemannHypothesis`**
   (`probe_shiftProfile_unbounded_above_and_below_of_singleQuartet`,
   `not_hasSingleOffLineQuartet_of_probeShift_bddAbove`,
   `not_hasSingleOffLineQuartet_of_probeShift_bddBelow`,
   `exists_coshSurplus_violation_of_riemannHypothesis`):
   Under `HasSingleOffLineQuartet ρ₀`, `R ↦ bareMixedEnergy (probe p) (shiftProfile (probe p) R)`
   (`p > 4`) is unbounded both above and below on `[0, ∞)`, so either an upper bound or a lower
   bound on `[0, ∞)` excludes all single off-line quartets. Under `RiemannHypothesis`, for every
   `ρ₀` with `1/2 < Re ρ₀ < 1`, `Im ρ₀ ≠ 0`, and `m ≥ 1`, an explicit shifted-probe sum
   `G = probe p + shiftProfile (probe p) R` violates the cosh-surplus inequality
   `m ‖Σ_{ρ₀}(G)‖² ≤ bareMixedEnergy G G + m ‖Δ_{ρ₀}(G)‖²`.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter Zeta23 Complex Metric Topology Finset Matrix
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState

open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis HTGeometry _root_.RHTower

/-! ## 1. Single-functional rank-two completion and hyperplane dichotomy -/

/-- Complex sinh-type Laplace functional `L G(1/2 - conj ρ₀) - L G(ρ₀ - 1/2)` of a profile `G`. -/
def quartetSinhFunctional (ρ₀ : ℂ) (G : ℝ → ℝ) : ℂ :=
  negativeHalfLineLaplace (cx G) (1 / 2 - conj ρ₀) -
    negativeHalfLineLaplace (cx G) (ρ₀ - 1 / 2)

/-- Complex cosh-type Laplace functional `L G(1/2 - conj ρ₀) + L G(ρ₀ - 1/2)` of a profile `G`. -/
def quartetCoshFunctional (ρ₀ : ℂ) (G : ℝ → ℝ) : ℂ :=
  negativeHalfLineLaplace (cx G) (1 / 2 - conj ρ₀) +
    negativeHalfLineLaplace (cx G) (ρ₀ - 1 / 2)

/-- Rank-two completed Weil bilinear form `B(F, G) + m Re(Δ_{ρ₀}(F) conj(Δ_{ρ₀}(G)))`. -/
def rankTwoCompletedWeil (ρ₀ : ℂ) (m : ℕ) (F G : ℝ → ℝ) : ℝ :=
  bareMixedEnergy F G +
    (m : ℝ) * (quartetSinhFunctional ρ₀ F * conj (quartetSinhFunctional ρ₀ G)).re

/-- Complex polarization `4 Re(u v̄) = ‖v + u‖² - ‖v - u‖²`. -/
theorem four_mul_re_mul_conj_eq_norm_add_sq_sub_norm_sub_sq (u v : ℂ) :
    4 * (u * conj v).re = ‖v + u‖ ^ 2 - ‖v - u‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Polarized algebraic identity between the `4 × 4` swap pairing and `Δ_{ρ₀}, Σ_{ρ₀}`. -/
theorem two_mul_dotProduct_quartetSwap_add_re_sinh_eq_re_cosh (ρ₀ : ℂ) (F G : ℝ → ℝ) :
    2 * dotProduct (quartetEvalVec ρ₀ F) (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ G) +
      (quartetSinhFunctional ρ₀ F * conj (quartetSinhFunctional ρ₀ G)).re =
      (quartetCoshFunctional ρ₀ F * conj (quartetCoshFunctional ρ₀ G)).re := by
  rw [quartetSwapMatrix_mulVec]
  unfold quartetSinhFunctional quartetCoshFunctional quartetEvalVec
  simp only [dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **Polarized rank-two completion under a single off-line quartet.** On the energy domain,
`rankTwoCompletedWeil ρ₀ m F G = onLineMixed F G + m Re(Σ_{ρ₀}(F) conj(Σ_{ρ₀}(G)))`. -/
theorem rankTwoCompletedWeil_eq_onLineMixed_add_cosh {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    rankTwoCompletedWeil ρ₀ (quartetCopyMult ρ₀) F G =
      onLineMixed F G +
        (quartetCopyMult ρ₀ : ℝ) *
          (quartetCoshFunctional ρ₀ F * conj (quartetCoshFunctional ρ₀ G)).re := by
  unfold rankTwoCompletedWeil
  rw [bareMixedEnergy_singleQuartet hq hF hG]
  have hid := two_mul_dotProduct_quartetSwap_add_re_sinh_eq_re_cosh ρ₀ F G
  linear_combination (quartetCopyMult ρ₀ : ℝ) * hid

/-- **Diagonal rank-two completion.** For arbitrary quartet multiplicity `m = quartetCopyMult ρ₀`,
adding the single complex norm square `m ‖Δ_{ρ₀}(G)‖²` turns Weil's bare energy into the sum of
squares `onLineEnergy G + m ‖Σ_{ρ₀}(G)‖²`. -/
theorem bareMixedEnergy_add_sinhFunctional_sq_eq {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    bareMixedEnergy G G + (quartetCopyMult ρ₀ : ℝ) * ‖quartetSinhFunctional ρ₀ G‖ ^ 2 =
      onLineEnergy G + (quartetCopyMult ρ₀ : ℝ) * ‖quartetCoshFunctional ρ₀ G‖ ^ 2 := by
  have hre : ∀ z : ℂ, (z * conj z).re = ‖z‖ ^ 2 := fun z => by
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have h := rankTwoCompletedWeil_eq_onLineMixed_add_cosh hq hG hG
  unfold rankTwoCompletedWeil at h
  rwa [onLineMixed_self, hre, hre] at h

/-- **Cosh-surplus lower bound and global nonnegativity under `HasSingleOffLineQuartet ρ₀`.** -/
theorem coshFunctional_sq_le_bareMixedEnergy_add_sinhFunctional_sq {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    0 ≤ (quartetCopyMult ρ₀ : ℝ) * ‖quartetCoshFunctional ρ₀ G‖ ^ 2 ∧
      (quartetCopyMult ρ₀ : ℝ) * ‖quartetCoshFunctional ρ₀ G‖ ^ 2 ≤
        bareMixedEnergy G G + (quartetCopyMult ρ₀ : ℝ) * ‖quartetSinhFunctional ρ₀ G‖ ^ 2 := by
  refine ⟨by positivity, ?_⟩
  rw [bareMixedEnergy_add_sinhFunctional_sq_eq hq hG]
  linarith [onLineEnergy_nonneg G]

/-- **Sinh-orthogonal hyperplane coercivity.** On the real codimension-`2` subspace
`quartetSinhFunctional ρ₀ G = 0`, `bareMixedEnergy G G = onLineEnergy G + 4 m ‖L G(ρ₀ - 1/2)‖²`. -/
theorem bareMixedEnergy_sinhOrthogonal_eq_and_ge {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (hker : quartetSinhFunctional ρ₀ G = 0) :
    bareMixedEnergy G G =
        onLineEnergy G +
          4 * (quartetCopyMult ρ₀ : ℝ) *
            ‖negativeHalfLineLaplace (cx G) (ρ₀ - 1 / 2)‖ ^ 2 ∧
      4 * (quartetCopyMult ρ₀ : ℝ) *
          ‖negativeHalfLineLaplace (cx G) (ρ₀ - 1 / 2)‖ ^ 2 ≤ bareMixedEnergy G G := by
  have heq_L : negativeHalfLineLaplace (cx G) (1 / 2 - conj ρ₀) =
      negativeHalfLineLaplace (cx G) (ρ₀ - 1 / 2) := sub_eq_zero.mp hker
  have hcosh : quartetCoshFunctional ρ₀ G =
      2 * negativeHalfLineLaplace (cx G) (ρ₀ - 1 / 2) := by
    unfold quartetCoshFunctional
    rw [heq_L, two_mul]
  have h := bareMixedEnergy_add_sinhFunctional_sq_eq hq hG
  rw [hker, norm_zero, sq, mul_zero, mul_zero, add_zero, hcosh, norm_mul,
    Complex.norm_ofNat, mul_pow] at h
  have hmain : bareMixedEnergy G G =
      onLineEnergy G +
        4 * (quartetCopyMult ρ₀ : ℝ) *
          ‖negativeHalfLineLaplace (cx G) (ρ₀ - 1 / 2)‖ ^ 2 := by linarith
  exact ⟨hmain, by linarith [onLineEnergy_nonneg G]⟩

/-- **Cosh-orthogonal hyperplane identity.** On the complementary real codimension-`2` subspace
`quartetCoshFunctional ρ₀ G = 0`, `bareMixedEnergy G G = onLineEnergy G - 4 m ‖L G(ρ₀ - 1/2)‖²`. -/
theorem bareMixedEnergy_coshOrthogonal_eq {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (hker : quartetCoshFunctional ρ₀ G = 0) :
    bareMixedEnergy G G =
      onLineEnergy G -
        4 * (quartetCopyMult ρ₀ : ℝ) *
          ‖negativeHalfLineLaplace (cx G) (ρ₀ - 1 / 2)‖ ^ 2 := by
  have heq_L : negativeHalfLineLaplace (cx G) (1 / 2 - conj ρ₀) =
      -negativeHalfLineLaplace (cx G) (ρ₀ - 1 / 2) := add_eq_zero_iff_eq_neg.mp hker
  have hsinh : quartetSinhFunctional ρ₀ G =
      -(2 * negativeHalfLineLaplace (cx G) (ρ₀ - 1 / 2)) := by
    unfold quartetSinhFunctional
    rw [heq_L]; ring
  have h := bareMixedEnergy_add_sinhFunctional_sq_eq hq hG
  rw [hker, norm_zero, hsinh, norm_neg, norm_mul, Complex.norm_ofNat, mul_pow] at h
  linarith

private theorem summable_mul_and_norm_tsum_le_gen {ι : Type*} {a b : ι → ℂ}
    (ha : Summable fun q => ‖a q‖ ^ 2) (hb : Summable fun q => ‖b q‖ ^ 2) :
    Summable (fun q => a q * b q) ∧
      ‖∑' q, a q * b q‖ ≤ Real.sqrt (∑' q, ‖a q‖ ^ 2) * Real.sqrt (∑' q, ‖b q‖ ^ 2) := by
  have hn : Summable fun q => ‖a q * b q‖ :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => by
      rw [norm_mul]; nlinarith [sq_nonneg (‖a q‖ - ‖b q‖)]) ((ha.add hb).div_const 2)
  refine ⟨hn.of_norm, (norm_tsum_le_tsum_norm hn).trans ?_⟩
  refine Real.tsum_le_of_sum_le (fun q => norm_nonneg _) fun s => ?_
  simp_rw [norm_mul]
  exact (Real.sum_mul_le_sqrt_mul_sqrt s (fun q => ‖a q‖) (fun q => ‖b q‖)).trans
    (mul_le_mul (Real.sqrt_le_sqrt (ha.sum_le_tsum s fun q _ => sq_nonneg _))
      (Real.sqrt_le_sqrt (hb.sum_le_tsum s fun q _ => sq_nonneg _)) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))

/-- On-line Cauchy–Schwarz inequality under `FiniteOffLine`. -/
theorem abs_onLineMixed_le_sqrt_mul_sqrt {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hfin : BacklundConverse.FiniteOffLine) :
    |onLineMixed F G| ≤ Real.sqrt (onLineEnergy F) * Real.sqrt (onLineEnergy G) := by
  have hsF : Summable (fun q : onLineCopies =>
      ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ ^ 2) :=
    (domain_zeroParseval_of_finiteOffLine hF hfin).1
  have hsG : Summable (fun q : onLineCopies =>
      ‖conj (negativeHalfLineLaplace (cx G) (centredZero q))‖ ^ 2) := by
    refine (domain_zeroParseval_of_finiteOffLine hG hfin).1.congr fun q => ?_
    rw [Complex.norm_conj]; rfl
  obtain ⟨hsum, hcs⟩ := summable_mul_and_norm_tsum_le_gen hsF hsG
  have hon_eq : onLineMixed F G =
      (∑' q : onLineCopies, negativeHalfLineLaplace (cx F) (centredZero q) *
        conj (negativeHalfLineLaplace (cx G) (centredZero q))).re := by
    unfold onLineMixed
    exact (Complex.re_tsum hsum).symm
  have hG_eq : (∑' q : onLineCopies,
      ‖conj (negativeHalfLineLaplace (cx G) (centredZero q))‖ ^ 2) = onLineEnergy G := by
    unfold onLineEnergy zeroValueMass
    refine tsum_congr fun q => ?_
    rw [Complex.norm_conj]
  rw [hon_eq]
  refine (Complex.abs_re_le_norm _).trans (hcs.trans ?_)
  rw [hG_eq]
  rfl

/-- **Global Cauchy–Schwarz inequality for the rank-two completed Weil form** under
`HasSingleOffLineQuartet ρ₀`. -/
theorem rankTwoCompletedWeil_cauchy_schwarz {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    rankTwoCompletedWeil ρ₀ (quartetCopyMult ρ₀) F G ^ 2 ≤
      rankTwoCompletedWeil ρ₀ (quartetCopyMult ρ₀) F F *
        rankTwoCompletedWeil ρ₀ (quartetCopyMult ρ₀) G G := by
  set m : ℝ := (quartetCopyMult ρ₀ : ℝ)
  have hm_nn : 0 ≤ m := Nat.cast_nonneg _
  have hre : ∀ z : ℂ, (z * conj z).re = ‖z‖ ^ 2 := fun z => by
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hFG := rankTwoCompletedWeil_eq_onLineMixed_add_cosh hq hF hG
  have hFF : rankTwoCompletedWeil ρ₀ (quartetCopyMult ρ₀) F F =
      onLineEnergy F + m * ‖quartetCoshFunctional ρ₀ F‖ ^ 2 := by
    unfold rankTwoCompletedWeil
    rw [hre]
    exact bareMixedEnergy_add_sinhFunctional_sq_eq hq hF
  have hGG : rankTwoCompletedWeil ρ₀ (quartetCopyMult ρ₀) G G =
      onLineEnergy G + m * ‖quartetCoshFunctional ρ₀ G‖ ^ 2 := by
    unfold rankTwoCompletedWeil
    rw [hre]
    exact bareMixedEnergy_add_sinhFunctional_sq_eq hq hG
  set a₁ : ℝ := Real.sqrt (onLineEnergy F)
  set b₁ : ℝ := Real.sqrt (onLineEnergy G)
  set a₂ : ℝ := Real.sqrt m * ‖quartetCoshFunctional ρ₀ F‖
  set b₂ : ℝ := Real.sqrt m * ‖quartetCoshFunctional ρ₀ G‖
  have ha₁_sq : a₁ ^ 2 = onLineEnergy F := Real.sq_sqrt (onLineEnergy_nonneg F)
  have hb₁_sq : b₁ ^ 2 = onLineEnergy G := Real.sq_sqrt (onLineEnergy_nonneg G)
  have ha₂_sq : a₂ ^ 2 = m * ‖quartetCoshFunctional ρ₀ F‖ ^ 2 := by
    dsimp [a₂]; rw [mul_pow, Real.sq_sqrt hm_nn]
  have hb₂_sq : b₂ ^ 2 = m * ‖quartetCoshFunctional ρ₀ G‖ ^ 2 := by
    dsimp [b₂]; rw [mul_pow, Real.sq_sqrt hm_nn]
  have hon_le : |onLineMixed F G| ≤ a₁ * b₁ :=
    abs_onLineMixed_le_sqrt_mul_sqrt hF hG hq.finiteOffLine
  have hcosh_le : |m * (quartetCoshFunctional ρ₀ F *
      conj (quartetCoshFunctional ρ₀ G)).re| ≤ a₂ * b₂ := by
    rw [abs_mul, abs_of_nonneg hm_nn]
    have hre_le : |(quartetCoshFunctional ρ₀ F * conj (quartetCoshFunctional ρ₀ G)).re| ≤
        ‖quartetCoshFunctional ρ₀ F‖ * ‖quartetCoshFunctional ρ₀ G‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
    have hm_sqrt : m = Real.sqrt m * Real.sqrt m := (Real.mul_self_sqrt hm_nn).symm
    calc m * |(quartetCoshFunctional ρ₀ F * conj (quartetCoshFunctional ρ₀ G)).re|
        ≤ m * (‖quartetCoshFunctional ρ₀ F‖ * ‖quartetCoshFunctional ρ₀ G‖) :=
          mul_le_mul_of_nonneg_left hre_le hm_nn
      _ = (Real.sqrt m * Real.sqrt m) *
          (‖quartetCoshFunctional ρ₀ F‖ * ‖quartetCoshFunctional ρ₀ G‖) := by rw [← hm_sqrt]
      _ = a₂ * b₂ := by dsimp [a₂, b₂]; ring
  have habs : |rankTwoCompletedWeil ρ₀ (quartetCopyMult ρ₀) F G| ≤ a₁ * b₁ + a₂ * b₂ := by
    rw [hFG]
    exact (abs_add_le _ _).trans (add_le_add hon_le hcosh_le)
  have hnn : 0 ≤ a₁ * b₁ + a₂ * b₂ := by
    dsimp [a₁, b₁, a₂, b₂]; positivity
  have hsq_le : rankTwoCompletedWeil ρ₀ (quartetCopyMult ρ₀) F G ^ 2 ≤
      (a₁ * b₁ + a₂ * b₂) ^ 2 := by
    rw [← sq_abs (rankTwoCompletedWeil ρ₀ (quartetCopyMult ρ₀) F G)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [hFF, hGG, ← ha₁_sq, ← hb₁_sq, ← ha₂_sq, ← hb₂_sq]
  nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁), hsq_le]

/-! ## 2. RH consistency of the weak completion and uniform lag bounds -/

/-- Under `RiemannHypothesis`, `FiniteOffLine` holds with empty off-line copy set. -/
theorem finiteOffLine_of_riemannHypothesis (hRH : RiemannHypothesis) :
    BacklundConverse.FiniteOffLine := by
  have hemp : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0} = ∅ :=
    Set.eq_empty_of_forall_notMem fun q hne =>
      hne (RHTower.xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q)
  unfold BacklundConverse.FiniteOffLine
  rw [hemp]
  exact Set.finite_empty

/-- Under `RiemannHypothesis`, `bareMixedEnergy F G = onLineMixed F G` on the energy domain. -/
theorem bareMixedEnergy_eq_onLineMixed_of_riemannHypothesis (hRH : RiemannHypothesis)
    {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    bareMixedEnergy F G = onLineMixed F G := by
  have hfin := finiteOffLine_of_riemannHypothesis hRH
  rw [bareMixedEnergy_eq_onLineMixed_add_re_offLine hF hG hfin]
  have hemp : offLineCopyFinset hfin = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun q hq => ?_
    have hne : (centredZero q).re ≠ 0 := mem_offLineCopyFinset.mp hq
    have him0 := RHTower.xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q
    have hrel : (xiSpectralPoint q).im = -(centredZero q).re := by
      simp [xiSpectralPoint, centredZero, Complex.mul_im]
    exact hne (by linarith)
  rw [hemp, Finset.sum_empty, Complex.zero_re, add_zero]

/-- **RH consistency of the weak rank-two completion.** Under `RiemannHypothesis`, for **every**
`ρ₀ ∈ ℂ`, `m ∈ ℕ`, and `G ∈ CriticalHalfLineEnergyDomain`, `bareMixedEnergy G G = onLineEnergy G ≥ 0`
and `0 ≤ bareMixedEnergy G G + m ‖Δ_{ρ₀}(G)‖²`. Consequently, no contradiction can ever be deduced
from the weak rank-two completion alone without disproving `RiemannHypothesis`. -/
theorem rankTwoCompletedWeil_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    (ρ₀ : ℂ) (m : ℕ) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    bareMixedEnergy G G = onLineEnergy G ∧
      0 ≤ bareMixedEnergy G G ∧
      0 ≤ bareMixedEnergy G G + (m : ℝ) * ‖quartetSinhFunctional ρ₀ G‖ ^ 2 := by
  have heq : bareMixedEnergy G G = onLineEnergy G := by
    rw [bareMixedEnergy_eq_onLineMixed_of_riemannHypothesis hRH hG hG, onLineMixed_self]
  refine ⟨heq, heq ▸ onLineEnergy_nonneg G, ?_⟩
  rw [heq]
  linarith [onLineEnergy_nonneg G,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sq_nonneg ‖quartetSinhFunctional ρ₀ G‖)]

/-- Left translation preserves `onLineEnergy` identically (`‖cexp(-(z_q R))‖ = 1` on `Re z_q = 0`). -/
theorem onLineEnergy_shiftProfile_eq (F : ℝ → ℝ) (R : ℝ) :
    onLineEnergy (shiftProfile F R) = onLineEnergy F := by
  unfold onLineEnergy zeroValueMass
  refine tsum_congr fun q => ?_
  rw [laplace_shiftProfile, norm_mul, Complex.norm_exp]
  have hre0 : (-(centredZero q.1 * (R : ℂ))).re = 0 := by
    have hq0 : (centredZero q.1).re = 0 := q.2
    simp [Complex.mul_re, hq0]
  rw [hre0, Real.exp_zero, one_mul]

/-- Under `FiniteOffLine`, `|onLineMixed F (shiftProfile F R)| ≤ onLineEnergy F` for all `R ≥ 0`. -/
theorem abs_onLineMixed_shiftProfile_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hfin : BacklundConverse.FiniteOffLine) {R : ℝ} (hR : 0 ≤ R) :
    |onLineMixed F (shiftProfile F R)| ≤ onLineEnergy F := by
  have hcs := abs_onLineMixed_le_sqrt_mul_sqrt hF
    (criticalHalfLineEnergyDomain_shiftProfile hF hR) hfin
  rwa [onLineEnergy_shiftProfile_eq, Real.mul_self_sqrt (onLineEnergy_nonneg F)] at hcs

/-- **Uniform probe-lag bound under `RiemannHypothesis`.** For every `p > 4` and `R ≥ 0`,
`|bareMixedEnergy (probe p) (shiftProfile (probe p) R)| ≤ probeSymbol p / p`. -/
theorem abs_bareMixedEnergy_probe_shiftProfile_le_of_riemannHypothesis (hRH : RiemannHypothesis)
    {p : ℝ} (hp : 4 < p) {R : ℝ} (hR : 0 ≤ R) :
    |bareMixedEnergy (probe p) (shiftProfile (probe p) R)| ≤ probeSymbol p / p := by
  have hFp := criticalHalfLineEnergyDomain_probe hp
  have hFs := criticalHalfLineEnergyDomain_shiftProfile hFp hR
  rw [bareMixedEnergy_eq_onLineMixed_of_riemannHypothesis hRH hFp hFs]
  have hle := abs_onLineMixed_shiftProfile_le hFp (finiteOffLine_of_riemannHypothesis hRH) hR
  have hself : onLineEnergy (probe p) = probeSymbol p / p := by
    rw [← (rankTwoCompletedWeil_nonneg_of_riemannHypothesis hRH 0 0 hFp).1,
      bareMixedEnergy_probe (by linarith) (by linarith)]
    ring
  rwa [hself] at hle

/-! ## 3. Quarter-turn shifted-probe resonance and cosh-surplus refutation under RH -/

private theorem negativeHalfLineLaplace_probe {p : ℝ} {w : ℂ} (h : 0 < p + w.re) :
    negativeHalfLineLaplace (cx (probe p)) w = 1 / ((p : ℂ) + w) := by
  unfold negativeHalfLineLaplace
  have heq : (fun u : ℝ => cexp (w * u) * cx (probe p) u) =
      fun u : ℝ => (probe p u : ℂ) * cexp (w * u) := by
    funext u; simp [cx, mul_comm]
  rw [heq, integral_probe_mul_cexp h]

private theorem cexp_quarter_turns (N : ℕ) :
    cexp (I * ((0 : ℝ) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ))) = 1 ∧
      cexp (I * (Real.pi + 2 * Real.pi * ((N + 1 : ℕ) : ℝ))) = -1 ∧
      cexp (I * (Real.pi / 2 + 2 * Real.pi * ((N + 1 : ℕ) : ℝ))) = I ∧
      cexp (I * (-(Real.pi / 2) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ))) = -I := by
  have hper : ∀ θ : ℝ,
      cexp (I * ((θ : ℂ) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ))) = cexp ((θ : ℂ) * I) := by
    intro θ
    have hsplit : I * ((θ : ℂ) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ)) =
        (θ : ℂ) * I + ((N + 1 : ℕ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hper 0
  · rw [show (Real.pi : ℂ) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ) =
      ((Real.pi : ℝ) : ℂ) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ) from rfl, hper Real.pi,
      Complex.exp_pi_mul_I]
  · rw [show (Real.pi : ℂ) / 2 + 2 * Real.pi * ((N + 1 : ℕ) : ℝ) =
      ((Real.pi / 2 : ℝ) : ℂ) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ) by push_cast; ring,
      hper (Real.pi / 2), Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  · rw [show -((Real.pi : ℂ) / 2) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ) =
      ((-(Real.pi / 2) : ℝ) : ℂ) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ) by push_cast; ring,
      hper (-(Real.pi / 2)), Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring

/-- Quarter-turn exponential growth lemma: for any `w ≠ 0`, `γ ≠ 0`, `δ > 0`, and threshold `K`,
some `R ≥ 0` satisfies `K < exp(δ R) Re(w e^{i γ R})`. -/
theorem exists_nonneg_exp_mul_re_gt {w : ℂ} (hw : w ≠ 0) {γ : ℝ} (hγ : γ ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (K : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ K < Real.exp (δ * R) * (w * cexp (I * ((γ : ℂ) * (R : ℂ)))).re := by
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hsum_norm : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
  -- Choose a quarter-turn angle `θ₀ ∈ [-π, π]` making `Re(w e^{i θ₀}) ≥ ‖w‖ / 2` (and for `-γ` via `conj`).
  have hex_θ : ∀ u : ℂ, u ≠ 0 → ∃ θ₀ : ℝ, -Real.pi ≤ θ₀ ∧ θ₀ ≤ Real.pi ∧
      ∀ N : ℕ, ‖u‖ / 2 ≤ (u * cexp (I * ((θ₀ : ℂ) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ)))).re := by
    intro u hu
    have hpi : 0 < Real.pi := Real.pi_pos
    have hu_sum : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
    by_cases hre_im : |u.im| ≤ |u.re|
    · by_cases hre_sgn : 0 ≤ u.re
      · refine ⟨0, by linarith, by linarith, fun N => ?_⟩
        rw [abs_of_nonneg hre_sgn] at hre_im hu_sum
        have h1 := (cexp_quarter_turns N).1
        push_cast at h1 ⊢
        rw [h1, mul_one]; linarith
      · refine ⟨Real.pi, by linarith, le_rfl, fun N => ?_⟩
        rw [abs_of_neg (not_le.mp hre_sgn)] at hre_im hu_sum
        have h1 := (cexp_quarter_turns N).2.1
        push_cast at h1 ⊢
        rw [h1]; simp; linarith
    · rw [not_le] at hre_im
      by_cases him_sgn : 0 ≤ u.im
      · refine ⟨-(Real.pi / 2), by linarith, by linarith, fun N => ?_⟩
        rw [abs_of_nonneg him_sgn] at hre_im hu_sum
        have h1 := (cexp_quarter_turns N).2.2.2
        push_cast at h1 ⊢
        rw [h1]; simp; linarith
      · refine ⟨Real.pi / 2, by linarith, by linarith, fun N => ?_⟩
        rw [abs_of_neg (not_le.mp him_sgn)] at hre_im hu_sum
        have h1 := (cexp_quarter_turns N).2.2.1
        push_cast at h1 ⊢
        rw [h1]; simp; linarith
  have hγ_abs : 0 < |γ| := abs_pos.mpr hγ
  have hstep_pos : 0 < δ * (Real.pi / |γ|) := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt ((max K 0 + 1) / (‖w‖ / 2) / (δ * (Real.pi / |γ|)))
  rcases lt_or_gt_of_ne hγ with hγ_neg | hγ_pos
  · have hcw_ne : conj w ≠ 0 := by
      intro hc; exact hw (by simpa using congrArg conj hc)
    obtain ⟨θ₀, hθ_lo, hθ_hi, hθ_re⟩ := hex_θ (conj w) hcw_ne
    set R : ℝ := (θ₀ + 2 * Real.pi * ((N + 1 : ℕ) : ℝ)) / (-γ)
    have hR_ge : Real.pi * ((N + 1 : ℕ) : ℝ) / |γ| ≤ R := by
      rw [abs_of_neg hγ_neg]
      refine div_le_div_of_nonneg_right ?_ (by linarith)
      have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
      nlinarith [Real.pi_pos]
    have hR_nn : 0 ≤ R := le_trans (by positivity) hR_ge
    have hre_eq : (w * cexp (I * ((γ : ℂ) * (R : ℂ)))).re =
        (conj w * cexp (I * ((θ₀ : ℂ) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ)))).re := by
      have hmul : (γ : ℂ) * (R : ℂ) = -((θ₀ : ℂ) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ)) := by
        have hreal : γ * R = -(θ₀ + 2 * Real.pi * ((N + 1 : ℕ) : ℝ)) := by
          dsimp [R]; field_simp [ne_of_lt hγ_neg]
        exact_mod_cast hreal
      rw [hmul]
      set α : ℝ := θ₀ + 2 * Real.pi * ((N + 1 : ℕ) : ℝ)
      have hc : conj (w * cexp (I * -((α : ℝ) : ℂ))) = conj w * cexp (I * (α : ℂ)) := by
        rw [map_mul, ← Complex.exp_conj]
        congr 2
        simp [map_mul, Complex.conj_I]
      have hre_c := Complex.conj_re (w * cexp (I * -((α : ℝ) : ℂ)))
      rw [hc] at hre_c
      simpa [α] using hre_c.symm
    have hw_re_ge : ‖w‖ / 2 ≤ (w * cexp (I * ((γ : ℂ) * (R : ℂ)))).re := by
      rw [hre_eq, ← Complex.norm_conj w]
      exact hθ_re N
    have hexp_gt : (max K 0 + 1) / (‖w‖ / 2) < Real.exp (δ * R) := by
      have h1 : (max K 0 + 1) / (‖w‖ / 2) < (N : ℝ) * (δ * (Real.pi / |γ|)) :=
        (div_lt_iff₀ hstep_pos).mp hN
      have h2 : δ * (Real.pi / |γ|) * (N : ℝ) ≤ δ * R := by
        calc δ * (Real.pi / |γ|) * (N : ℝ)
            ≤ δ * (Real.pi * ((N + 1 : ℕ) : ℝ) / |γ|) := by
              have hleN : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
              have : Real.pi / |γ| * (N : ℝ) ≤ Real.pi * ((N + 1 : ℕ) : ℝ) / |γ| := by
                rw [div_mul_eq_mul_div]
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hleN Real.pi_pos.le) hγ_abs.le
              linarith [mul_le_mul_of_nonneg_left this hδ.le]
          _ ≤ δ * R := mul_le_mul_of_nonneg_left hR_ge hδ.le
      linarith [Real.add_one_le_exp (δ * R)]
    refine ⟨R, hR_nn, ?_⟩
    have hmul_gt : max K 0 + 1 < Real.exp (δ * R) * (‖w‖ / 2) :=
      (div_lt_iff₀ (by positivity)).mp hexp_gt
    have hprod_le : Real.exp (δ * R) * (‖w‖ / 2) ≤
        Real.exp (δ * R) * (w * cexp (I * ((γ : ℂ) * (R : ℂ)))).re :=
      mul_le_mul_of_nonneg_left hw_re_ge (Real.exp_pos _).le
    linarith [le_max_left K 0]
  · obtain ⟨θ₀, hθ_lo, _, hθ_re⟩ := hex_θ w hw
    set R : ℝ := (θ₀ + 2 * Real.pi * ((N + 1 : ℕ) : ℝ)) / γ
    have hR_ge : Real.pi * ((N + 1 : ℕ) : ℝ) / |γ| ≤ R := by
      rw [abs_of_pos hγ_pos]
      refine div_le_div_of_nonneg_right ?_ hγ_pos.le
      have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
      nlinarith [Real.pi_pos]
    have hR_nn : 0 ≤ R := le_trans (by positivity) hR_ge
    have hmul : (γ : ℂ) * (R : ℂ) = (θ₀ : ℂ) + 2 * Real.pi * ((N + 1 : ℕ) : ℝ) := by
      have hreal : γ * R = θ₀ + 2 * Real.pi * ((N + 1 : ℕ) : ℝ) := by
        dsimp [R]; field_simp [ne_of_gt hγ_pos]
      exact_mod_cast hreal
    have hw_re_ge : ‖w‖ / 2 ≤ (w * cexp (I * ((γ : ℂ) * (R : ℂ)))).re := by
      rw [hmul]; exact hθ_re N
    have hexp_gt : (max K 0 + 1) / (‖w‖ / 2) < Real.exp (δ * R) := by
      have h1 : (max K 0 + 1) / (‖w‖ / 2) < (N : ℝ) * (δ * (Real.pi / |γ|)) :=
        (div_lt_iff₀ hstep_pos).mp hN
      have h2 : δ * (Real.pi / |γ|) * (N : ℝ) ≤ δ * R := by
        calc δ * (Real.pi / |γ|) * (N : ℝ)
            ≤ δ * (Real.pi * ((N + 1 : ℕ) : ℝ) / |γ|) := by
              have hleN : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
              have : Real.pi / |γ| * (N : ℝ) ≤ Real.pi * ((N + 1 : ℕ) : ℝ) / |γ| := by
                rw [div_mul_eq_mul_div]
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hleN Real.pi_pos.le) hγ_abs.le
              linarith [mul_le_mul_of_nonneg_left this hδ.le]
          _ ≤ δ * R := mul_le_mul_of_nonneg_left hR_ge hδ.le
      linarith [Real.add_one_le_exp (δ * R)]
    refine ⟨R, hR_nn, ?_⟩
    have hmul_gt : max K 0 + 1 < Real.exp (δ * R) * (‖w‖ / 2) :=
      (div_lt_iff₀ (by positivity)).mp hexp_gt
    have hprod_le : Real.exp (δ * R) * (‖w‖ / 2) ≤
        Real.exp (δ * R) * (w * cexp (I * ((γ : ℂ) * (R : ℂ)))).re :=
      mul_le_mul_of_nonneg_left hw_re_ge (Real.exp_pos _).le
    linarith [le_max_left K 0]

private theorem probe_quartetSwap_pairing_eq {p : ℝ} (hp : 4 < p) {ρ₀ : ℂ}
    (hlo : 1 / 2 < ρ₀.re) (hhi : ρ₀.re < 1) (R : ℝ) :
    let zPos : ℂ := ρ₀ - 1 / 2
    let c₀ : ℂ := 1 / ((p : ℂ) ^ 2 - zPos ^ 2)
    c₀ ≠ 0 ∧
      dotProduct (quartetEvalVec ρ₀ (probe p))
          (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ (shiftProfile (probe p) R)) =
        Real.exp ((ρ₀.re - 1 / 2) * R) * (c₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re +
          (conj c₀ * cexp (-(conj zPos * (R : ℂ)))).re := by
  intro zPos c₀
  set zNeg : ℂ := 1 / 2 - conj ρ₀
  have hzPos_re : zPos.re = ρ₀.re - 1 / 2 := by simp [zPos]
  have hzPos_im : zPos.im = ρ₀.im := by simp [zPos]
  have hzNeg_re : zNeg.re = 1 / 2 - ρ₀.re := by simp [zNeg]
  have hczNeg : conj zNeg = -zPos := by
    dsimp [zPos, zNeg]; apply Complex.ext <;> simp
  have hp_pos_ne : (p : ℂ) + zPos ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hzPos_re] at this; linarith
  have hp_neg_ne : (p : ℂ) - zPos ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hzPos_re] at this; linarith
  have hdiff_sq : (p : ℂ) ^ 2 - zPos ^ 2 = ((p : ℂ) + zPos) * ((p : ℂ) - zPos) := by ring
  have hc₀_ne : c₀ ≠ 0 := by
    dsimp [c₀]; rw [hdiff_sq]
    exact one_div_ne_zero (mul_ne_zero hp_pos_ne hp_neg_ne)
  refine ⟨hc₀_ne, ?_⟩
  have hLF_pos : negativeHalfLineLaplace (cx (probe p)) zPos = 1 / ((p : ℂ) + zPos) :=
    negativeHalfLineLaplace_probe (by rw [hzPos_re]; linarith)
  have hLF_neg : negativeHalfLineLaplace (cx (probe p)) zNeg = 1 / ((p : ℂ) + zNeg) :=
    negativeHalfLineLaplace_probe (by rw [hzNeg_re]; linarith)
  have hLG_pos : negativeHalfLineLaplace (cx (shiftProfile (probe p) R)) zPos =
      cexp (-(zPos * (R : ℂ))) * (1 / ((p : ℂ) + zPos)) := by
    rw [laplace_shiftProfile, hLF_pos]
  have hLG_neg : negativeHalfLineLaplace (cx (shiftProfile (probe p) R)) zNeg =
      cexp (-(zNeg * (R : ℂ))) * (1 / ((p : ℂ) + zNeg)) := by
    rw [laplace_shiftProfile, hLF_neg]
  have hdot : dotProduct (quartetEvalVec ρ₀ (probe p))
      (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ (shiftProfile (probe p) R)) =
      (negativeHalfLineLaplace (cx (probe p)) zPos *
          conj (negativeHalfLineLaplace (cx (shiftProfile (probe p) R)) zNeg) +
        negativeHalfLineLaplace (cx (probe p)) zNeg *
          conj (negativeHalfLineLaplace (cx (shiftProfile (probe p) R)) zPos)).re := by
    rw [quartetSwapMatrix_mulVec]
    unfold quartetEvalVec
    simp only [dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hdot, hLF_pos, hLF_neg, hLG_pos, hLG_neg]
  have hterm1 : (1 / ((p : ℂ) + zPos)) *
      conj (cexp (-(zNeg * (R : ℂ))) * (1 / ((p : ℂ) + zNeg))) =
      c₀ * cexp (zPos * (R : ℂ)) := by
    rw [map_mul, ← Complex.exp_conj, map_neg, map_mul, hczNeg, Complex.conj_ofReal,
      neg_mul, neg_neg, map_div₀, map_one, map_add, Complex.conj_ofReal, hczNeg]
    dsimp [c₀]
    rw [hdiff_sq, show (p : ℂ) + -zPos = (p : ℂ) - zPos by ring]
    field_simp [hp_pos_ne, hp_neg_ne]
  have hterm2 : (1 / ((p : ℂ) + zNeg)) *
      conj (cexp (-(zPos * (R : ℂ))) * (1 / ((p : ℂ) + zPos))) =
      conj c₀ * cexp (-(conj zPos * (R : ℂ))) := by
    have hzNeg_eq : zNeg = -conj zPos := by
      have hc := congrArg conj hczNeg
      rw [Complex.conj_conj, map_neg] at hc
      exact hc
    rw [map_mul, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal,
      map_div₀, map_one, map_add, Complex.conj_ofReal, hzNeg_eq]
    have hconj_c₀ : conj c₀ = 1 / (((p : ℂ) + conj zPos) * ((p : ℂ) - conj zPos)) := by
      have hc₀_eq : c₀ = 1 / (((p : ℂ) + zPos) * ((p : ℂ) - zPos)) := by
        rw [← hdiff_sq]
      simp only [hc₀_eq, map_div₀, map_one, map_mul, map_add, map_sub, Complex.conj_ofReal]
    rw [hconj_c₀, show (p : ℂ) + -conj zPos = (p : ℂ) - conj zPos by ring]
    have hc_pos_ne : (p : ℂ) + conj zPos ≠ 0 := by
      intro h; apply hp_pos_ne; simpa [map_add, Complex.conj_ofReal] using congrArg conj h
    have hc_neg_ne : (p : ℂ) - conj zPos ≠ 0 := by
      intro h; apply hp_neg_ne; simpa [map_sub, Complex.conj_ofReal] using congrArg conj h
    field_simp [hc_pos_ne, hc_neg_ne]
  have hexp_split : cexp (zPos * (R : ℂ)) =
      (Real.exp ((ρ₀.re - 1 / 2) * R) : ℂ) * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ))) := by
    have hzR : zPos * (R : ℂ) =
        (((ρ₀.re - 1 / 2) * R : ℝ) : ℂ) + I * ((ρ₀.im : ℂ) * (R : ℂ)) := by
      apply Complex.ext <;> simp [hzPos_re, hzPos_im]
    rw [hzR, Complex.exp_add, ← Complex.ofReal_exp]
  rw [hterm1, hterm2, hexp_split, Complex.add_re]
  congr 1
  rw [← mul_assoc, mul_comm c₀, mul_assoc, Complex.re_ofReal_mul]

/-- **Two-sided exponential resonance of translated probes under a single off-line quartet.**
Under `HasSingleOffLineQuartet ρ₀`, for every `p > 4` and every `M : ℝ`, there exist `R₊, R₋ ≥ 0`
such that `M < bareMixedEnergy (probe p) (shiftProfile (probe p) R₊)` and
`bareMixedEnergy (probe p) (shiftProfile (probe p) R₋) < -M`. -/
theorem probe_shiftProfile_unbounded_above_and_below_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {p : ℝ} (hp : 4 < p) (M : ℝ) :
    (∃ R : ℝ, 0 ≤ R ∧ M < bareMixedEnergy (probe p) (shiftProfile (probe p) R)) ∧
      (∃ R : ℝ, 0 ≤ R ∧ bareMixedEnergy (probe p) (shiftProfile (probe p) R) < -M) := by
  have hFp := criticalHalfLineEnergyDomain_probe hp
  set zPos : ℂ := ρ₀ - 1 / 2
  set c₀ : ℂ := 1 / ((p : ℂ) ^ 2 - zPos ^ 2)
  obtain ⟨hc₀_ne, _⟩ := probe_quartetSwap_pairing_eq hp hq.1 hq.re_lt_one 0
  have hδ_pos : 0 < ρ₀.re - 1 / 2 := by linarith [hq.1]
  have hm_pos : (0 : ℝ) < (quartetCopyMult ρ₀ : ℝ) := by exact_mod_cast hq.quartetCopyMult_pos
  have hdecay_le : ∀ R : ℝ, 0 ≤ R →
      |(conj c₀ * cexp (-(conj zPos * (R : ℂ)))).re| ≤ ‖c₀‖ := by
    intro R hR
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj, Complex.norm_exp]
    have hre_nonpos : (-(conj zPos * (R : ℂ))).re ≤ 0 := by
      have hzre : (conj zPos).re = ρ₀.re - 1 / 2 := by simp [zPos]
      have : (-(conj zPos * (R : ℂ))).re = -((ρ₀.re - 1 / 2) * R) := by
        simp [Complex.mul_re, hzre]
      rw [this]
      nlinarith
    calc ‖c₀‖ * Real.exp (-(conj zPos * (R : ℂ))).re
        ≤ ‖c₀‖ * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hre_nonpos)
          (norm_nonneg c₀)
      _ = ‖c₀‖ := mul_one _
  set B : ℝ := (|M| + onLineEnergy (probe p)) / (2 * (quartetCopyMult ρ₀ : ℝ)) + ‖c₀‖
  constructor
  · obtain ⟨R, hR, hgt⟩ := exists_nonneg_exp_mul_re_gt hc₀_ne hq.im_ne_zero hδ_pos B
    refine ⟨R, hR, ?_⟩
    have hFs := criticalHalfLineEnergyDomain_shiftProfile hFp hR
    rw [bareMixedEnergy_singleQuartet hq hFp hFs,
      (probe_quartetSwap_pairing_eq hp hq.1 hq.re_lt_one R).2]
    have hon := (abs_le.mp (abs_onLineMixed_shiftProfile_le hFp hq.finiteOffLine hR)).1
    have hdec := (abs_le.mp (hdecay_le R hR)).1
    have hm_gt : (|M| + onLineEnergy (probe p)) / (2 * (quartetCopyMult ρ₀ : ℝ)) <
        Real.exp ((ρ₀.re - 1 / 2) * R) * (c₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re +
          (conj c₀ * cexp (-(conj zPos * (R : ℂ)))).re := by
      dsimp [B] at hgt; linarith
    have hmul_gt := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (quartetCopyMult ρ₀ : ℝ))).mp hm_gt
    have hM_le : M ≤ |M| := le_abs_self M
    nlinarith
  · have hnc₀_ne : -c₀ ≠ 0 := neg_ne_zero.mpr hc₀_ne
    obtain ⟨R, hR, hgt⟩ := exists_nonneg_exp_mul_re_gt hnc₀_ne hq.im_ne_zero hδ_pos B
    refine ⟨R, hR, ?_⟩
    have hFs := criticalHalfLineEnergyDomain_shiftProfile hFp hR
    rw [bareMixedEnergy_singleQuartet hq hFp hFs,
      (probe_quartetSwap_pairing_eq hp hq.1 hq.re_lt_one R).2]
    have hon := (abs_le.mp (abs_onLineMixed_shiftProfile_le hFp hq.finiteOffLine hR)).2
    have hdec := (abs_le.mp (hdecay_le R hR)).2
    have hneg_re : ((-c₀) * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re =
        -(c₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re := by simp
    rw [hneg_re, mul_neg] at hgt
    have hm_lt : Real.exp ((ρ₀.re - 1 / 2) * R) * (c₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re +
        (conj c₀ * cexp (-(conj zPos * (R : ℂ)))).re <
        -((|M| + onLineEnergy (probe p)) / (2 * (quartetCopyMult ρ₀ : ℝ))) := by
      dsimp [B] at hgt; linarith
    have hmul_lt : 2 * (quartetCopyMult ρ₀ : ℝ) *
        (Real.exp ((ρ₀.re - 1 / 2) * R) * (c₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re +
          (conj c₀ * cexp (-(conj zPos * (R : ℂ)))).re) <
        -(|M| + onLineEnergy (probe p)) := by
      have hpos : (0 : ℝ) < 2 * (quartetCopyMult ρ₀ : ℝ) := by positivity
      have := mul_lt_mul_of_pos_left hm_lt hpos
      have hsimp : 2 * (quartetCopyMult ρ₀ : ℝ) *
          -((|M| + onLineEnergy (probe p)) / (2 * (quartetCopyMult ρ₀ : ℝ))) =
          -(|M| + onLineEnergy (probe p)) := by field_simp [ne_of_gt hpos]
      rwa [hsimp] at this
    have hM_le : M ≤ |M| := le_abs_self M
    linarith

/-- **One-sided upper-bound exclusion.** If `R ↦ bareMixedEnergy (probe p) (shiftProfile (probe p) R)`
(`p > 4`) is bounded above on `[0, ∞)` (which holds under `RiemannHypothesis` with bound
`probeSymbol p / p`), then no single off-line quartet exists anywhere in `ℂ`. -/
theorem not_hasSingleOffLineQuartet_of_probeShift_bddAbove {p : ℝ} (hp : 4 < p)
    (hbdd : ∃ M : ℝ, ∀ R : ℝ, 0 ≤ R →
      bareMixedEnergy (probe p) (shiftProfile (probe p) R) ≤ M) :
    ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ := by
  obtain ⟨M, hM⟩ := hbdd
  intro ρ₀ hq
  obtain ⟨⟨R, hR, hgt⟩, -⟩ := probe_shiftProfile_unbounded_above_and_below_of_singleQuartet hq hp M
  exact not_lt.mpr (hM R hR) hgt

/-- **One-sided lower-bound exclusion.** Symmetrically, if
`R ↦ bareMixedEnergy (probe p) (shiftProfile (probe p) R)` (`p > 4`) is bounded below on `[0, ∞)`,
then no single off-line quartet exists anywhere in `ℂ`. -/
theorem not_hasSingleOffLineQuartet_of_probeShift_bddBelow {p : ℝ} (hp : 4 < p)
    (hbdd : ∃ M : ℝ, ∀ R : ℝ, 0 ≤ R →
      M ≤ bareMixedEnergy (probe p) (shiftProfile (probe p) R)) :
    ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ := by
  obtain ⟨M, hM⟩ := hbdd
  intro ρ₀ hq
  obtain ⟨-, ⟨R, hR, hlt⟩⟩ :=
    probe_shiftProfile_unbounded_above_and_below_of_singleQuartet hq hp (-M)
  rw [neg_neg] at hlt
  exact not_lt.mpr (hM R hR) hlt

/-- **Refutation of the cosh-surplus lower bound under `RiemannHypothesis`.** While the weak
completion `0 ≤ bareMixedEnergy G G + m ‖Δ_{ρ₀}(G)‖²` holds under `RiemannHypothesis`, for every
`ρ₀ ∈ ℂ` with `1/2 < Re ρ₀ < 1`, `Im ρ₀ ≠ 0`, `m ≥ 1`, and `p > 4`, there exists an explicit
two-probe profile `G = probe p + shiftProfile (probe p) R ∈ CriticalHalfLineEnergyDomain` (`R ≥ 0`)
such that `bareMixedEnergy G G + m ‖Δ_{ρ₀}(G)‖² < m ‖Σ_{ρ₀}(G)‖²`. -/
theorem exists_coshSurplus_violation_of_riemannHypothesis (hRH : RiemannHypothesis)
    {ρ₀ : ℂ} (hlo : 1 / 2 < ρ₀.re) (hhi : ρ₀.re < 1) (him : ρ₀.im ≠ 0)
    {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : 4 < p) :
    ∃ R : ℝ, 0 ≤ R ∧
      CriticalHalfLineEnergyDomain (fun u => probe p u + shiftProfile (probe p) R u) ∧
      bareMixedEnergy (fun u => probe p u + shiftProfile (probe p) R u)
          (fun u => probe p u + shiftProfile (probe p) R u) +
        (m : ℝ) * ‖quartetSinhFunctional ρ₀
          (fun u => probe p u + shiftProfile (probe p) R u)‖ ^ 2 <
        (m : ℝ) * ‖quartetCoshFunctional ρ₀
          (fun u => probe p u + shiftProfile (probe p) R u)‖ ^ 2 := by
  have hFp := criticalHalfLineEnergyDomain_probe hp
  set zPos : ℂ := ρ₀ - 1 / 2
  set zNeg : ℂ := 1 / 2 - conj ρ₀
  set c₀ : ℂ := 1 / ((p : ℂ) ^ 2 - zPos ^ 2)
  obtain ⟨hc₀_ne, _⟩ := probe_quartetSwap_pairing_eq hp hlo hhi 0
  have hδ_pos : 0 < ρ₀.re - 1 / 2 := by linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set K : ℝ := (|4 * (probeSymbol p / p)| + 1) / (4 * (m : ℝ)) + 3 * ‖c₀‖
  obtain ⟨R, hR, hgt⟩ := exists_nonneg_exp_mul_re_gt hc₀_ne him hδ_pos K
  have hFs := criticalHalfLineEnergyDomain_shiftProfile hFp hR
  let G : ℝ → ℝ := fun u => probe p u + shiftProfile (probe p) R u
  have hG : CriticalHalfLineEnergyDomain G := by
    have heq : G = fun u => probe p u + 1 * shiftProfile (probe p) R u := by
      funext u; dsimp [G]; ring
    rw [heq]
    exact hFp.add_const_mul hFs 1
  -- Upper bound on `bareMixedEnergy G G` under `RiemannHypothesis`.
  have hB_le : bareMixedEnergy G G ≤ 4 * (probeSymbol p / p) := by
    have hadd1 := bareMixedEnergy_add_right hG hFp hFs
    have hadd2 : bareMixedEnergy (probe p) G =
        bareMixedEnergy (probe p) (probe p) +
          bareMixedEnergy (probe p) (shiftProfile (probe p) R) :=
      bareMixedEnergy_add_right hFp hFp hFs
    have hadd3 : bareMixedEnergy (shiftProfile (probe p) R) G =
        bareMixedEnergy (shiftProfile (probe p) R) (probe p) +
          bareMixedEnergy (shiftProfile (probe p) R) (shiftProfile (probe p) R) :=
      bareMixedEnergy_add_right hFs hFp hFs
    have hcomm1 : bareMixedEnergy G (probe p) = bareMixedEnergy (probe p) G :=
      bareMixedEnergy_comm G (probe p)
    have hcomm2 : bareMixedEnergy G (shiftProfile (probe p) R) =
        bareMixedEnergy (shiftProfile (probe p) R) G :=
      bareMixedEnergy_comm G (shiftProfile (probe p) R)
    have hcomm3 : bareMixedEnergy (shiftProfile (probe p) R) (probe p) =
        bareMixedEnergy (probe p) (shiftProfile (probe p) R) :=
      bareMixedEnergy_comm _ _
    have hshift_self : bareMixedEnergy (shiftProfile (probe p) R) (shiftProfile (probe p) R) =
        bareMixedEnergy (probe p) (probe p) :=
      bareMixedEnergy_shiftProfile (integrable_mul_cosh_half_of_domain hFp)
        (integrable_mul_sinh_half_of_domain hFp)
        (integrable_mul_cosh_half_of_domain hFp)
        (integrable_mul_sinh_half_of_domain hFp) R
    have hself_eq : bareMixedEnergy (probe p) (probe p) = probeSymbol p / p := by
      rw [bareMixedEnergy_probe (by linarith) (by linarith)]; ring
    have hcross_le := (abs_le.mp
      (abs_bareMixedEnergy_probe_shiftProfile_le_of_riemannHypothesis hRH hp hR)).2
    linarith
  -- Exact evaluation of `L G zPos` and `L G zNeg`.
  have hint_probe : ∀ w : ℂ, 0 < p + w.re →
      Integrable (fun u : ℝ => cexp (w * u) * cx (probe p) u) := by
    intro w hw
    have heq : (fun u : ℝ => cexp (w * u) * cx (probe p) u) =
        (Iio (0 : ℝ)).indicator (fun u : ℝ => cexp (((p : ℂ) + w) * u)) := by
      funext u
      rcases lt_or_ge u 0 with hu | hu
      · rw [Set.indicator_of_mem (Set.mem_Iio.mpr hu), cx, probe_of_neg hu,
          Complex.ofReal_exp, ← Complex.exp_add]
        push_cast; ring_nf
      · rw [Set.indicator_of_notMem (fun h => (not_lt.mpr hu) (Set.mem_Iio.mp h)),
          cx, probe_of_nonneg hu, Complex.ofReal_zero, mul_zero]
    rw [heq]
    exact ((integrableOn_exp_mul_complex_Iic (by simpa using hw) 0).mono_set
      Iio_subset_Iic_self).integrable_indicator measurableSet_Iio
  have hint_shift : ∀ w : ℂ, 0 < p + w.re →
      Integrable (fun u : ℝ => cexp (w * u) * cx (shiftProfile (probe p) R) u) := by
    intro w hw
    have heq : (fun u : ℝ => cexp (w * u) * cx (shiftProfile (probe p) R) u) =
        fun u : ℝ =>
          cexp (-(w * (R : ℂ))) * (cexp (w * ((u + R : ℝ) : ℂ)) * cx (probe p) (u + R)) := by
      funext u
      simp only [shiftProfile, cx, ← mul_assoc, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [heq]
    exact ((hint_probe w hw).comp_add_right R).const_mul _
  have hLG : ∀ w : ℂ, 0 < p + w.re →
      negativeHalfLineLaplace (cx G) w =
        (1 + cexp (-(w * (R : ℂ)))) * (1 / ((p : ℂ) + w)) := by
    intro w hw
    have hsum : negativeHalfLineLaplace (cx G) w =
        negativeHalfLineLaplace (cx (probe p)) w +
          negativeHalfLineLaplace (cx (shiftProfile (probe p) R)) w := by
      unfold negativeHalfLineLaplace
      have heq : (fun u : ℝ => cexp (w * u) * cx G u) =
          fun u : ℝ => cexp (w * u) * cx (probe p) u +
            cexp (w * u) * cx (shiftProfile (probe p) R) u := by
        funext u; simp [G, cx, mul_add]
      rw [heq, integral_add (hint_probe w hw) (hint_shift w hw)]
    rw [hsum, laplace_shiftProfile, negativeHalfLineLaplace_probe hw]
    ring
  have hzPos_re : zPos.re = ρ₀.re - 1 / 2 := by simp [zPos]
  have hzPos_im : zPos.im = ρ₀.im := by simp [zPos]
  have hzNeg_re : zNeg.re = 1 / 2 - ρ₀.re := by simp [zNeg]
  have hczNeg : conj zNeg = -zPos := by
    dsimp [zPos, zNeg]; apply Complex.ext <;> simp
  have hp_pos_ne : (p : ℂ) + zPos ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hzPos_re] at this; linarith
  have hp_neg_ne : (p : ℂ) - zPos ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hzPos_re] at this; linarith
  have hdiff_sq : (p : ℂ) ^ 2 - zPos ^ 2 = ((p : ℂ) + zPos) * ((p : ℂ) - zPos) := by ring
  have hprod : negativeHalfLineLaplace (cx G) zPos *
      conj (negativeHalfLineLaplace (cx G) zNeg) =
      c₀ * (2 + cexp (-(zPos * (R : ℂ)))) + c₀ * cexp (zPos * (R : ℂ)) := by
    rw [hLG zPos (by rw [hzPos_re]; linarith), hLG zNeg (by rw [hzNeg_re]; linarith),
      map_mul, map_add, map_one, ← Complex.exp_conj, map_neg, map_mul, hczNeg,
      Complex.conj_ofReal, neg_mul, neg_neg, map_div₀, map_one, map_add,
      Complex.conj_ofReal, hczNeg]
    have hmul_exp : (1 + cexp (-(zPos * (R : ℂ)))) * (1 + cexp (zPos * (R : ℂ))) =
        (2 + cexp (-(zPos * (R : ℂ)))) + cexp (zPos * (R : ℂ)) := by
      have hc : cexp (-(zPos * (R : ℂ))) * cexp (zPos * (R : ℂ)) = 1 := by
        rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
      linear_combination hc
    dsimp [c₀]
    rw [hdiff_sq, show (p : ℂ) + -zPos = (p : ℂ) - zPos by ring]
    calc (1 + cexp (-(zPos * (R : ℂ)))) * (1 / ((p : ℂ) + zPos)) *
          ((1 + cexp (zPos * (R : ℂ))) * (1 / ((p : ℂ) - zPos)))
        = (1 / (((p : ℂ) + zPos) * ((p : ℂ) - zPos))) *
            ((1 + cexp (-(zPos * (R : ℂ)))) * (1 + cexp (zPos * (R : ℂ)))) := by
          field_simp [hp_pos_ne, hp_neg_ne]
      _ = _ := by rw [hmul_exp]; ring
  have hsmall : |(c₀ * (2 + cexp (-(zPos * (R : ℂ))))).re| ≤ 3 * ‖c₀‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, mul_comm (3 : ℝ) ‖c₀‖]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c₀)
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_ofNat, Complex.norm_exp]
    have hre_nonpos : (-(zPos * (R : ℂ))).re ≤ 0 := by
      have : (-(zPos * (R : ℂ))).re = -((ρ₀.re - 1 / 2) * R) := by
        simp [Complex.mul_re, hzPos_re]
      rw [this]; nlinarith
    linarith [Real.exp_le_one_iff.mpr hre_nonpos]
  have hexp_re : (c₀ * cexp (zPos * (R : ℂ))).re =
      Real.exp ((ρ₀.re - 1 / 2) * R) * (c₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re := by
    have hzR : zPos * (R : ℂ) =
        (((ρ₀.re - 1 / 2) * R : ℝ) : ℂ) + I * ((ρ₀.im : ℂ) * (R : ℂ)) := by
      apply Complex.ext <;> simp [hzPos_re, hzPos_im]
    rw [hzR, Complex.exp_add, ← Complex.ofReal_exp, ← mul_assoc, mul_comm c₀, mul_assoc,
      Complex.re_ofReal_mul]
  have hdiff_norm : ‖quartetCoshFunctional ρ₀ G‖ ^ 2 - ‖quartetSinhFunctional ρ₀ G‖ ^ 2 =
      4 * ((c₀ * (2 + cexp (-(zPos * (R : ℂ))))).re +
        Real.exp ((ρ₀.re - 1 / 2) * R) * (c₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re) := by
    have hpol := four_mul_re_mul_conj_eq_norm_add_sq_sub_norm_sub_sq
      (negativeHalfLineLaplace (cx G) zPos) (negativeHalfLineLaplace (cx G) zNeg)
    unfold quartetCoshFunctional quartetSinhFunctional
    rw [← hpol, hprod, Complex.add_re, hexp_re]
  refine ⟨R, hR, hG, ?_⟩
  have hsm_lo := (abs_le.mp hsmall).1
  have hsum_gt : (|4 * (probeSymbol p / p)| + 1) / (4 * (m : ℝ)) <
      (c₀ * (2 + cexp (-(zPos * (R : ℂ))))).re +
        Real.exp ((ρ₀.re - 1 / 2) * R) * (c₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re := by
    dsimp [K] at hgt; linarith
  have h4m_gt : |4 * (probeSymbol p / p)| + 1 <
      (m : ℝ) * (‖quartetCoshFunctional ρ₀ G‖ ^ 2 - ‖quartetSinhFunctional ρ₀ G‖ ^ 2) := by
    rw [hdiff_norm]
    have hmul := (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ))).mp hsum_gt
    linarith
  have hB_abs : 4 * (probeSymbol p / p) ≤ |4 * (probeSymbol p / p)| := le_abs_self _
  linarith

end GaloisForLFunctions.ExclusionOfTheCriticalState
