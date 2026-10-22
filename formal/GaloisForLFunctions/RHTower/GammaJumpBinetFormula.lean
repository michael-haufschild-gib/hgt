import GaloisForLFunctions.RHTower.GammaJumpSymbolIdentity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaFrequencySymbol

/-!
# The Gamma jump operator has the multiplier `r`

The physical jump operator is the second-difference average

`(RF)(L) = ∫₀^∞ [2F(L) − F(L+s) − F(L−s)] / (e^s − 1) ds`,

and on a character `e^{iLη}` its integrand is `e^{iLη}(2 − 2cos(ηs))/(e^s − 1)`.  Expanding the
Laplace weight as the geometric series `Σ_{n≥1} e^{-ns}` and integrating term by term gives

`∫₀^∞ (2 − 2cos(ηs))/(e^s − 1) ds = 2 Σ_{n≥1} [1/n − n/(n²+η²)] = 2 Σ_{n≥1} η²/(n(n²+η²))`,

which is exactly the jump multiplier.  The interchange is legitimate because every term is
nonnegative and the term integrals are summable — the crude bound `4/n` on each term is not, so the
exact term integral is what makes the interchange available.

This is the Binet-type formula behind the identity `r(η) = ψ(1+iη) + ψ(1−iη) + 2γ`, the symbol side
of which is proved separately.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The `n`-th term of the Binet expansion of the jump multiplier. -/
def jumpBinetTerm (η : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  (2 - 2 * Real.cos (η * s)) * Real.exp (-(((n : ℝ) + 1) * s))

theorem jumpBinetTerm_nonneg (η : ℝ) (n : ℕ) (s : ℝ) : 0 ≤ jumpBinetTerm η n s := by
  have h : Real.cos (η * s) ≤ 1 := Real.cos_le_one _
  have h2 : (0 : ℝ) ≤ 2 - 2 * Real.cos (η * s) := by linarith
  rw [jumpBinetTerm]
  positivity

theorem integrableOn_jumpBinetTerm (η : ℝ) (n : ℕ) :
    IntegrableOn (jumpBinetTerm η n) (Ioi (0 : ℝ)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hexp : IntegrableOn (fun s : ℝ => Real.exp (-(((n : ℝ) + 1) * s))) (Ioi (0 : ℝ)) := by
    have h : (fun s : ℝ => Real.exp (-(((n : ℝ) + 1) * s)))
        = fun s : ℝ => Real.exp (-((n : ℝ) + 1) * s) := by
      funext s; ring_nf
    rw [h]
    exact exp_neg_integrableOn_Ioi 0 hn
  refine Integrable.bdd_mul (c := 4) hexp ?_ ?_
  · have hcont : Continuous fun s : ℝ => 2 - 2 * Real.cos (η * s) := by fun_prop
    exact hcont.aestronglyMeasurable.restrict
  · filter_upwards with s
    have h1 : Real.cos (η * s) ≤ 1 := Real.cos_le_one _
    have h2 : -1 ≤ Real.cos (η * s) := Real.neg_one_le_cos _
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith

theorem integral_jumpBinetTerm (η : ℝ) (n : ℕ) :
    (∫ s in Ioi (0 : ℝ), jumpBinetTerm η n s) = 2 * gammaJumpTerm η n := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hexp : IntegrableOn (fun s : ℝ => Real.exp (-(((n : ℝ) + 1) * s))) (Ioi (0 : ℝ)) := by
    have h : (fun s : ℝ => Real.exp (-(((n : ℝ) + 1) * s)))
        = fun s : ℝ => Real.exp (-((n : ℝ) + 1) * s) := by
      funext s; ring_nf
    rw [h]
    exact exp_neg_integrableOn_Ioi 0 hn
  have hcos : IntegrableOn
      (fun s : ℝ => Real.exp (-(((n : ℝ) + 1) * s)) * Real.cos (η * s)) (Ioi (0 : ℝ)) := by
    have h : IntegrableOn
        (fun s : ℝ => Real.cos (η * s) * Real.exp (-(((n : ℝ) + 1) * s))) (Ioi (0 : ℝ)) := by
      refine Integrable.bdd_mul (c := 1) hexp ?_ ?_
      · have hcont : Continuous fun s : ℝ => Real.cos (η * s) := by fun_prop
        exact hcont.aestronglyMeasurable.restrict
      · filter_upwards with s
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
    exact h.congr (Filter.Eventually.of_forall fun s => mul_comm _ _)
  have hsplit : (∫ s in Ioi (0 : ℝ), jumpBinetTerm η n s)
      = 2 * (∫ s in Ioi (0 : ℝ), Real.exp (-(((n : ℝ) + 1) * s)))
        - 2 * ∫ s in Ioi (0 : ℝ), Real.exp (-(((n : ℝ) + 1) * s)) * Real.cos (η * s) := by
    have hrw : (fun s : ℝ => jumpBinetTerm η n s)
        = fun s : ℝ => 2 * Real.exp (-(((n : ℝ) + 1) * s))
            - 2 * (Real.exp (-(((n : ℝ) + 1) * s)) * Real.cos (η * s)) := by
      funext s
      rw [jumpBinetTerm]
      ring
    rw [hrw, integral_sub (hexp.const_mul 2) (hcos.const_mul 2), integral_const_mul,
      integral_const_mul]
  rw [hsplit, _root_.RHTower.gammaSymbol_integral_Ioi_exp_neg_mul hn,
    _root_.RHTower.gammaSymbol_integral_Ioi_exp_neg_mul_cos hn η, gammaJumpTerm]
  have hA : (((n : ℝ) + 1) ^ 2 + η ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The Laplace weight is the geometric series of exponentials. -/
theorem gammaJumpWeight_eq_tsum {s : ℝ} (hs : 0 < s) :
    _root_.RHTower.gammaJumpWeight s = ∑' n : ℕ, Real.exp (-(((n : ℝ) + 1) * s)) := by
  have hr : Real.exp (-s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hr0 : (0 : ℝ) ≤ Real.exp (-s) := (Real.exp_pos _).le
  have hterm : ∀ n : ℕ, Real.exp (-(((n : ℝ) + 1) * s))
      = Real.exp (-s) * Real.exp (-s) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr,
    _root_.RHTower.gammaJumpWeight, Real.exp_neg]
  have hexpos : (0 : ℝ) < Real.exp s := Real.exp_pos _
  have hne : Real.exp s - 1 ≠ 0 := by
    have : (1 : ℝ) < Real.exp s := Real.one_lt_exp_iff.mpr hs
    linarith
  field_simp

/-- **The Binet formula for the Gamma jump multiplier.**  The physical jump operator `(26)` has the
Fourier multiplier `r`. -/
theorem integral_jumpBinet (η : ℝ) :
    (∫ s in Ioi (0 : ℝ), (2 - 2 * Real.cos (η * s)) * _root_.RHTower.gammaJumpWeight s)
      = gammaJumpMultiplier η := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (jumpBinetTerm η n)
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    have hcont : Continuous (jumpBinetTerm η n) := by
      unfold jumpBinetTerm
      fun_prop
    exact hcont.aestronglyMeasurable.restrict
  have hnorm : ∀ n : ℕ, (∫⁻ s in Ioi (0 : ℝ), ‖jumpBinetTerm η n s‖ₑ)
      = ENNReal.ofReal (2 * gammaJumpTerm η n) := by
    intro n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (integrableOn_jumpBinetTerm η n)]
    congr 1
    rw [← integral_jumpBinetTerm η n]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    exact Real.norm_of_nonneg (jumpBinetTerm_nonneg η n s)
  have hsum : (∑' n : ℕ, ∫⁻ s in Ioi (0 : ℝ), ‖jumpBinetTerm η n s‖ₑ) ≠ ⊤ := by
    rw [tsum_congr hnorm, ← ENNReal.ofReal_tsum_of_nonneg
      (fun n => by
        have := gammaJumpTerm_nonneg η n
        linarith) ((summable_gammaJumpTerm η).mul_left 2)]
    exact ENNReal.ofReal_ne_top
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      (2 - 2 * Real.cos (η * s)) * _root_.RHTower.gammaJumpWeight s
        = ∑' n : ℕ, jumpBinetTerm η n s := by
    intro s hs
    rw [gammaJumpWeight_eq_tsum hs, ← tsum_mul_left]
    exact tsum_congr fun n => rfl
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_tsum hmeas hsum,
    tsum_congr (integral_jumpBinetTerm η), tsum_mul_left, gammaJumpMultiplier]

/-- The Binet integrand, as the sum of its terms. -/
theorem jumpBinetIntegrand_eq_tsum {η s : ℝ} (hs : 0 < s) :
    (2 - 2 * Real.cos (η * s)) * _root_.RHTower.gammaJumpWeight s
      = ∑' n : ℕ, jumpBinetTerm η n s := by
  rw [gammaJumpWeight_eq_tsum hs, ← tsum_mul_left]
  exact tsum_congr fun n => rfl

/-- **The Binet integrand is integrable on the positive half-line.**  Its extended mass is the sum
of the term masses, which is the multiplier itself. -/
theorem integrableOn_jumpBinetIntegrand (η : ℝ) :
    IntegrableOn (fun s : ℝ => (2 - 2 * Real.cos (η * s)) * _root_.RHTower.gammaJumpWeight s)
      (Ioi (0 : ℝ)) := by
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => (2 - 2 * Real.cos (η * s)) * _root_.RHTower.gammaJumpWeight s)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have h1 : Measurable fun s : ℝ => 2 - 2 * Real.cos (η * s) := by fun_prop
    have h2 : Measurable fun s : ℝ => _root_.RHTower.gammaJumpWeight s := by
      unfold _root_.RHTower.gammaJumpWeight
      fun_prop
    exact ((h1.mul h2).aestronglyMeasurable).restrict
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      ‖(2 - 2 * Real.cos (η * s)) * _root_.RHTower.gammaJumpWeight s‖ₑ
        = ∑' n : ℕ, ‖jumpBinetTerm η n s‖ₑ := by
    intro s hs
    rw [jumpBinetIntegrand_eq_tsum hs]
    have hnn : ∀ n : ℕ, (0 : ℝ) ≤ jumpBinetTerm η n s := fun n => jumpBinetTerm_nonneg η n s
    have hsum : Summable fun n : ℕ => jumpBinetTerm η n s := by
      refine Summable.of_nonneg_of_le hnn (fun n => ?_)
        (((summable_geometric_of_lt_one (Real.exp_pos (-s)).le
          (Real.exp_lt_one_iff.mpr (by linarith [mem_Ioi.mp hs]))).mul_left 4))
      have hcos : Real.cos (η * s) ≤ 1 := Real.cos_le_one _
      have hcos' : -1 ≤ Real.cos (η * s) := Real.neg_one_le_cos _
      have hexp : Real.exp (-(((n : ℝ) + 1) * s)) ≤ Real.exp (-s) ^ n := by
        rw [← Real.exp_nat_mul]
        refine Real.exp_le_exp.mpr ?_
        have hs0 : (0 : ℝ) < s := mem_Ioi.mp hs
        have : (0 : ℝ) ≤ (n : ℝ) * s := by positivity
        nlinarith
      have hpos : (0 : ℝ) ≤ Real.exp (-(((n : ℝ) + 1) * s)) := (Real.exp_pos _).le
      rw [jumpBinetTerm]
      nlinarith [Real.exp_pos (-s), pow_nonneg (Real.exp_pos (-s)).le n]
    rw [← ofReal_norm, Real.norm_of_nonneg (tsum_nonneg hnn),
      ENNReal.ofReal_tsum_of_nonneg hnn hsum]
    refine tsum_congr fun n => ?_
    rw [← ofReal_norm, Real.norm_of_nonneg (hnn n)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  have hmeasn : ∀ n : ℕ, AEMeasurable (fun s : ℝ => ‖jumpBinetTerm η n s‖ₑ)
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    have hcont : Continuous (jumpBinetTerm η n) := by
      unfold jumpBinetTerm
      fun_prop
    exact (hcont.aestronglyMeasurable.restrict).enorm
  rw [lintegral_tsum hmeasn]
  have hval : ∀ n : ℕ, (∫⁻ s in Ioi (0 : ℝ), ‖jumpBinetTerm η n s‖ₑ)
      = ENNReal.ofReal (2 * gammaJumpTerm η n) := by
    intro n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (integrableOn_jumpBinetTerm η n)]
    congr 1
    rw [← integral_jumpBinetTerm η n]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    exact Real.norm_of_nonneg (jumpBinetTerm_nonneg η n s)
  rw [tsum_congr hval, ← ENNReal.ofReal_tsum_of_nonneg
    (fun n => by have := gammaJumpTerm_nonneg η n; linarith)
    ((summable_gammaJumpTerm η).mul_left 2)]
  exact ENNReal.ofReal_lt_top

end GaloisForLFunctions.RHTower
