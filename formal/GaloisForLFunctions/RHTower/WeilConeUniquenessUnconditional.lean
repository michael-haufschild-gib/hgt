import GaloisForLFunctions.RHTower.TwistedArcMinimumPrincipleProof

/-!
# The Weil cone has at most one point

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull`).  Every weight `lam : ℕ → ℝ` whose full Weil
functional `A(k_f) − Σ_{n≥2} lam(n) ℓ_n(f)` is nonnegative on every autocorrelation `k_f = f ⋆ f̃`
of a compactly supported `C²` test is the von Mangoldt function: `lam(n) = Λ(n)` for every `n ≥ 2`.
No hypothesis on `lam` (sign, growth, multiplicativity) and no hypothesis on `ζ` is used.

Proof.  The twisted arc minimum principle (`twistedArcMinimumPrinciple_holds`) gives a probability
measure on the modular bottom arc annihilating every twisted integer moment.  Its arc Gamma weights
`w_j = arcGammaWeight m_j j` are nonnegative, `w_0 > 0`, and jointly blind
(`shiftedGamma_blind_of_twistedArc`), so the shifted-Gamma family `Ξ Q_j` is a jointly
prime-blind `Ξ`-divisible family.  Its member `j = 0` is `Ξ` itself, whose real zeros are critical
ordinates.  The family rigidity theorem `eq_vonMangoldt_of_xiDivisibleBlindFamily` then forces
`lam = Λ`.

Together with the Weil criterion: the Weil cone is `{Λ}` if RH holds and empty otherwise
(`weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`).
-/

open MeasureTheory Filter Topology Set
open scoped Nat

namespace RHTower.WeilSpectral

noncomputable section

/-- **Uniqueness for a blind shifted-Gamma family.** -/
theorem eq_vonMangoldt_of_shiftedGamma_weights_of_pos {w : ℕ → ℝ}
    (hw : ∀ j, 0 ≤ w j) {j₀ : ℕ} (hj₀ : 0 < w j₀)
    (hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2)
    (hblind : ∀ n : ℕ, 2 ≤ n →
      ∑' j, w j * ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n) = 0)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨C, hC, hF⟩ := exists_decayBound_xiShiftedGammaTest
  refine eq_vonMangoldt_of_xiDivisibleBlindFamily
    (by norm_num : (0 : ℝ) < 1 / 4) hF hw ?_ (fun j ρ => paperFT_xiShiftedGammaTest_gammaOf j ρ) ?_
    hj₀ (fun r hr => riemannZeta_eq_zero_of_paperFT_xiShiftedGammaTest_zero_of j₀ hr) hW
  · refine (hsum.mul_left (C ^ 2)).congr fun j => ?_
    ring
  · intro n hn
    simp_rw [crossCorr_xiShiftedGammaTest]
    have e : ∀ j, w j * (1 / (2 * Real.pi) *
        ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) =
        1 / (2 * Real.pi) * (w j *
          ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) := fun j => by ring
    simp_rw [e]
    rw [tsum_mul_left, hblind n hn, mul_zero]

/-- The constant density has nonnegative weighted even moments. -/
theorem twArcEvenMoment_one_nonneg (μ : ProbabilityMeasure ArcParam) (j : ℕ) :
    0 ≤ twArcEvenMoment (μ : Measure ArcParam) (fun _ => 1) j := by
  unfold twArcEvenMoment
  refine integral_nonneg fun u => mul_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _) ?_)
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

/-- The constant density has positive zeroth weighted moment. -/
theorem twArcEvenMoment_one_zero_pos (μ : ProbabilityMeasure ArcParam) :
    0 < twArcEvenMoment (μ : Measure ArcParam) (fun _ => 1) 0 := by
  have hc : Continuous fun u : ArcParam => Real.sqrt (modularArcHeight u / 2) :=
    (continuous_modularArcHeight_param.div_const 2).sqrt
  unfold twArcEvenMoment
  simp only [one_mul, mul_zero, pow_zero, mul_one]
  have hi : Integrable (fun u : ArcParam => Real.sqrt (modularArcHeight u / 2))
      (μ : Measure ArcParam) :=
    (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact sqrt_modularArcHeight_half_le_one u)
  have hle := integral_mono (integrable_const (1 / 2 : ℝ)) hi fun u =>
    Real.le_sqrt_of_sq_le (by linarith [modularArcHeight_ge_half u] : (1 / 2 : ℝ) ^ 2 ≤ _)
  simp only [integral_const, probReal_univ, one_smul] at hle
  linarith

/-- **The Weil cone has at most one point.**  Every full-cone Weil-positive weight is `Λ` on
`n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_twArc_annihilating twistedArcMinimumPrinciple_holds
  set ν : Measure ArcParam := (μ : Measure ArcParam) with hν
  have hmom : ∀ j, 0 ≤ twArcEvenMoment ν (fun _ => 1) j := twArcEvenMoment_one_nonneg μ
  have hblind : ∀ n : ℕ, ∫ u, (fun _ : ArcParam => (1 : ℝ)) u * twArcMoment n u ∂ν = 0 :=
    fun n => by simpa using hμ n
  set w : ℕ → ℝ := fun j => arcGammaWeight (twArcEvenMoment ν (fun _ => 1) j) j with hw_def
  have hw : ∀ j, 0 ≤ w j := fun j => arcGammaWeight_nonneg (hmom j) j
  have hw0 : 0 < w 0 := by
    simp only [hw_def, arcGammaWeight]
    exact div_pos (mul_pos (by positivity) (twArcEvenMoment_one_zero_pos μ))
      (by exact_mod_cast Nat.factorial_pos _)
  have hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 :=
    summable_arcGammaWeight hmom
      (twArcEvenMoment_le (ν := ν) (g := fun _ => 1) (B := 1) fun _ => by norm_num)
  exact eq_vonMangoldt_of_shiftedGamma_weights_of_pos hw hw0 hsum
    (shiftedGamma_blind_of_twistedArc (B := 1) measurable_const (fun _ => by norm_num) hblind
      hmom) hW

/-- **The Weil cone is `{Λ}` under RH and empty otherwise.**  A weight sequence is full-cone
Weil-positive exactly when the Riemann hypothesis holds and the weights are the von Mangoldt
function on `n ≥ 2`. -/
theorem weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt {lam : ℕ → ℝ} :
    WeilPositiveFull lam ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  have hcongr : ∀ {l l' : ℕ → ℝ}, (∀ n, 2 ≤ n → l n = l' n) → WeilPositiveFull l →
      WeilPositiveFull l' := fun h hW f hf hfc => by
    rw [← weilFullFunctional_congr h]; exact hW f hf hfc
  constructor
  · intro hW
    have heq := eq_vonMangoldt_of_weilPositiveFull hW
    exact ⟨riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr (hcongr heq hW), heq⟩
  · rintro ⟨hRH, heq⟩
    exact hcongr (fun n hn => (heq n hn).symm)
      (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH)

end

end RHTower.WeilSpectral
