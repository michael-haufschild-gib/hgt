import GaloisForLFunctions.OrderSixMetaplecticTheory.TheTwistedUnitLayersAreGaussSumMultiplesOfTheUntwistedResidue
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheWeilIndexIsAKleinCombination
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCubicTwistAtTwoOfTheThetaSquareHasADoublePole
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheOrderSixFamilyTwistsThePlainSquares

/-!
# The cubic layer of the family at column one reaches the unit layer

The order-six weight is `ω₆(c) = Γ(c)χ₂(c)G̃(c)²` with `G̃(c)² = \overline{ξ(c)σ(c)}`, `ξ(c) = (ω²λ²/c)₃²`
(`twisted_coefficient_eq_plain_square`); this `ξ` puts every Klein layer of the family at the 3-adic layer `ω²λ²`. Reweight
the column by `ξ` (a character of conductor `9`, `|ξ| = 1` on primary `c`): `G̃(c)²ξ(c) = σ̄(c)` (`gauss_sq_mul_xi`), so the
reweighted column is the same Klein combination of **unit** layers (`unitColumnSeries_eq_of_expansion`). At column `1`
(`unitColumnSeries_one_eq_klein`):

`Σ_A ξω₆(gen A)N(A)^{−w} = ½\overline{S^{Ξ₀}_1(w̄)} + ½\overline{S^{Ξ₁}_1(w̄)} + (i/2)\overline{S^{Ξ_{ω²}}_1(w̄)} − (i/2)\overline{S^{Ξ_ω}_1(w̄)}`.

The cubic layer `Ξ₀ = \overline{χ₂} = (·/−2)₃` is the cubic character at the inert prime `2` (`cubicKleinLayer_eq`), so the
shifted Hecke trace at `p = −2` gives (`unitColumnCubicLayer_simple_pole`): **`S^{Ξ₀}_1` has a simple pole at `w = 2/3` with
residue `(2·2^{5/3}/5)\overline{(9/−2)₃}G̃(−2)·Res S₁ ≠ 0`.** The `ξ`-reweighting does not kill the cubic grade of the
first column; what remains open there are the three Klein layers (quadratic grade).
-/

noncomputable section

open Filter Topology
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource FamilyContinuationTheory

/-- The inert prime `−2` as a primary prime. -/
def twoPrimary : PrimaryPrime := ⟨-2, negTwo_prime, primary_neg_two⟩

/-! ### The unit-layer column -/

/-- **`G̃(c)²ξ(c) = σ̄(c)`** on primary `c`, `ξ(c) = (ω²λ²/c)₃²`. -/
theorem gauss_sq_mul_xi (c : O) (hc : lambda ^ 2 ∣ c - 1) :
    normalizedCubicUnitGauss c ^ 2 * ringComplex (symbol (omega ^ 2 * lambda ^ 2) c) ^ 2 =
      star (thetaSquareWeight (Ideal.span {c})) := by
  have hG := congrArg star (twisted_coefficient_eq_plain_square c hc)
  simp only [star_mul', star_pow, star_star] at hG
  have hcop : IsCoprime (omega ^ 2 * lambda ^ 2) c :=
    (IsCoprime.pow_left_iff (by norm_num : 0 < 2)).mp (by rw [omega_sq_mul_lambda_sq_sq]; exact nine_coprime_of_primary hc)
  have hn := symbol_norm_one _ c hc hcop
  set s := ringComplex (symbol (omega ^ 2 * lambda ^ 2) c)
  have hss : star s * s = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  rw [← hG]
  linear_combination (star (thetaSquareWeight (Ideal.span {c})) * (star s * s + 1)) * hss

/-- The column coefficient reweighted by `ξ`: `ξ(c)g_c(n)/|c|` on squarefree odd rows. -/
def unitColumnCoefficient (n : O) (A : Ideal O) : ℂ :=
  if Squarefree A ∧ primaryIdealGenerator A ≠ 0 ∧ ¬ (2 : O) ∣ primaryIdealGenerator A then
    columnWeight n (primaryIdealGenerator A) *
      ringComplex (symbol (omega ^ 2 * lambda ^ 2) (primaryIdealGenerator A)) ^ 2 else 0

/-- The `ξ`-reweighted `n`-th column `Σ_A ξ(gen A)g_{gen A}(n)/|gen A| N(A)^{−w}`. -/
def unitColumnSeries (n : O) (w : ℂ) : ℂ := ∑' A : Ideal O, unitColumnCoefficient n A * unramifiedNormWeight w A

/-- The summand of the unit layer `S^ψ_1`. -/
abbrev unitLayerTerm (ψ : O →* ℂ) (w : ℂ) (A : Ideal O) : ℂ :=
  if Squarefree A then unramifiedNormWeight w A * (ψ (primaryIdealGenerator A) *
    (ringComplex (symbol 1 (primaryIdealGenerator A)) ^ 2 * thetaSquareWeight A)) else 0

theorem summable_unitLayerTerm (ψ : O →* ℂ) (hψ : ∀ x, ‖ψ x‖ ≤ 1) (w : ℂ) (hw : 1 < w.re) :
    Summable (unitLayerTerm ψ w) := by
  refine Summable.of_norm_bounded (unramifiedNormWeight_summable_norm w hw) (fun A => ?_)
  simp only [unitLayerTerm]
  split_ifs with hsq
  · by_cases hA : primaryIdealGenerator A = 0
    · rw [unramifiedNormWeight_of_bad w A hA, zero_mul, norm_zero]
    · rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_thetaSquareWeight A hA hsq, mul_one]
      refine mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ (hψ _) (by positivity) ?_)
      exact pow_le_one₀ (norm_nonneg _) (norm_symbol_le _ _ (primaryIdealGenerator_spec A hA).2)
  · rw [norm_zero]
    exact norm_nonneg _

/-- **A 2-adic expansion of the weight turns a reweighted column into unit layers, coefficient by coefficient.** -/
theorem unitColumnCoefficient_eq_of_expansion {ι : Type*} (S : Finset ι) (γ : ι → ℂ) (μ : ι → O →* ℂ)
    (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn0 : n ≠ 0) (hn2 : IsCoprime n 2)
    (hμ0 : ∀ i c, (2 : O) ∣ c → μ i c = 0)
    (hW : ∀ c, ¬ (2 : O) ∣ c → twoAdicWeight n c = ∑ i ∈ S, γ i * μ i c) (w : ℂ) (A : Ideal O) :
    unitColumnCoefficient n A * unramifiedNormWeight w A =
      ∑ i ∈ S, γ i * star (unitLayerTerm (layerTwist (μ i) n hn hn0 hn2) (star w) A) := by
  by_cases hsq : Squarefree A
  swap
  · simp only [unitColumnCoefficient, unitLayerTerm, hsq, false_and, if_false, zero_mul, star_zero, mul_zero,
      Finset.sum_const_zero]
  by_cases hg : primaryIdealGenerator A = 0
  · simp only [unitColumnCoefficient, unitLayerTerm, hsq, hg, unramifiedNormWeight_of_bad _ A hg, mul_zero,
      zero_mul, star_zero, if_true, Finset.sum_const_zero]
  set c := primaryIdealGenerator A with hc
  by_cases h2 : (2 : O) ∣ c
  · have hz : ∀ i, μ i c = 0 := fun i => hμ0 i c h2
    simp only [unitColumnCoefficient, unitLayerTerm, hsq, layerTwist_apply, hz, zero_mul, star_zero, mul_zero,
      if_true, Finset.sum_const_zero, ← hc, h2, not_true_eq_false, and_false, if_false]
  · have hp := (primaryIdealGenerator_spec A hg).2
    have hspan : Ideal.span {c} = A := (primaryIdealGenerator_spec A hg).1
    have hX := gauss_sq_mul_xi c hp
    rw [hspan] at hX
    rw [unitColumnCoefficient, if_pos ⟨hsq, hg, h2⟩]
    simp only [unitLayerTerm, if_pos hsq, layerTwist_apply, ← hc, symbol_one_numerator c hp, map_one, one_pow,
      one_mul]
    simp only [star_mul', star_star]
    rw [star_unramifiedNormWeight]
    unfold columnWeight orderSixWeight
    have hrhs : ∀ i, γ i * (unramifiedNormWeight w A *
        (μ i c * (ringComplex (symbol c n) * quadSymbol c n) * star (thetaSquareWeight A))) =
        (γ i * μ i c) * (unramifiedNormWeight w A *
          ((ringComplex (symbol c n) * quadSymbol c n) * star (thetaSquareWeight A))) := by
      intro i
      ring
    rw [Finset.sum_congr rfl (fun i _ => hrhs i), ← Finset.sum_mul, ← hW c h2, ← hX]
    unfold twoAdicWeight
    ring

/-- **The `ξ`-reweighted column is a combination of unit layers.** -/
theorem unitColumnSeries_eq_of_expansion {ι : Type*} (S : Finset ι) (γ : ι → ℂ) (μ : ι → O →* ℂ)
    (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn0 : n ≠ 0) (hn2 : IsCoprime n 2)
    (hμ : ∀ i c, ‖μ i c‖ ≤ 1) (hμ0 : ∀ i c, (2 : O) ∣ c → μ i c = 0)
    (hW : ∀ c, ¬ (2 : O) ∣ c → twoAdicWeight n c = ∑ i ∈ S, γ i * μ i c) (w : ℂ) (hw : 1 < w.re) :
    unitColumnSeries n w = ∑ i ∈ S, γ i *
      star (twistedSquarefreeSeriesG (layerTwist (μ i) n hn hn0 hn2) 1 (star w)) := by
  have hw' : 1 < (star w).re := by rwa [Complex.star_def, Complex.conj_re]
  have hs : ∀ i ∈ S, Summable (fun A => γ i *
      star (unitLayerTerm (layerTwist (μ i) n hn hn0 hn2) (star w) A)) := fun i _ =>
    ((summable_unitLayerTerm _ (norm_layerTwist_le (μ i) (hμ i) n hn hn0 hn2) _ hw').star).mul_left _
  rw [unitColumnSeries, tsum_congr (unitColumnCoefficient_eq_of_expansion S γ μ n hn hn0 hn2 hμ0 hW w),
    Summable.tsum_finsetSum hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left, ← tsum_star]
  rfl

/-- **The `ξ`-reweighted first column is one cubic and three Klein unit layers.** -/
theorem unitColumnSeries_one_eq_klein (w : ℂ) (hw : 1 < w.re) :
    unitColumnSeries 1 w = ∑ i : Fin 4, kleinCoeff i *
      star (twistedSquarefreeSeriesG
        (layerTwist (kleinFactor 1 (not_mem_two_of_isCoprime isCoprime_one_left) i) 1 (by simp) one_ne_zero
          isCoprime_one_left) 1 (star w)) :=
  unitColumnSeries_eq_of_expansion Finset.univ kleinCoeff (kleinFactor 1 _) 1 (by simp) one_ne_zero
    isCoprime_one_left (kleinFactor_norm_le 1 _) (kleinFactor_even 1 _) (twoAdicWeight_klein 1 _) w hw

/-! ### The cubic layer is the cubic character at two -/

/-- **`Ξ₀ = \overline{χ₂} = (·/−2)₃`**: the cubic Klein layer of column `1` is the cubic twist at `−2`. -/
theorem cubicKleinLayer_eq :
    layerTwist (kleinFactor 1 (not_mem_two_of_isCoprime isCoprime_one_left) 0) 1 (by simp) one_ne_zero
      isCoprime_one_left = twoPrimary.resTwist twoPrimary.chi := by
  ext c
  have hr : twoPrimary.resTwist twoPrimary.chi c = ringComplex (symbol c (-2)) := twoPrimary.chi_res c
  rw [layerTwist_apply, kleinFactor_zero, hr, MonoidHom.mul_apply, MonoidHom.mul_apply, symbol_one, map_one,
    quadSymbol_one_denominator, mul_one, mul_one]
  by_cases h2 : c ∈ Ideal.span {(2 : O)}
  · have hp0 : phaseTwist 1 (not_mem_two_of_isCoprime isCoprime_one_left) c = 0 := by
      change (if c ∈ Ideal.span {(2 : O)} then 0 else _) = (0 : ℂ)
      rw [if_pos h2]
    have hd : twoPrimary.p ∣ c := neg_dvd.mpr (Ideal.mem_span_singleton.mp h2)
    have hres : twoPrimary.res c = 0 := (twoPrimary.res_eq_zero_iff c).mpr hd
    have h0 := twoPrimary.chi_res c
    rw [hres, MulChar.map_zero] at h0
    rw [hp0, zero_mul, zero_mul, star_zero]
    exact h0
  · have hp1 : phaseTwist 1 (not_mem_two_of_isCoprime isCoprime_one_left) c = 1 := by
      change (if c ∈ Ideal.span {(2 : O)} then 0 else star (quadraticPhase 1 c)) = (1 : ℂ)
      rw [if_neg h2, quadraticPhase_comm, quadraticPhase_one_right c h2, star_one]
    have hk : kleinZero c = 1 := by
      change (if c ∈ Ideal.span {(2 : O)} then 0 else ((oddZ _ _ : ℤ) : ℂ)) = (1 : ℂ)
      rw [if_neg h2]
      simp [oddZ]
    have hcop : IsCoprime c (-2) :=
      ((Prime.coprime_iff_not_dvd negTwo_prime).mpr fun hd => h2 (Ideal.mem_span_singleton.mpr (neg_dvd.mp hd))).symm
    have h3 : ringComplex (symbol c (-2)) ^ 3 = 1 := by
      rw [← map_pow, symbol_cube_of_isCoprime c (-2) primary_neg_two hcop, map_one]
    have hn := symbol_norm_one c (-2) primary_neg_two hcop
    have hc2 : cubicTwoHom c = ringComplex (symbol c (-2)) ^ 2 := rfl
    rw [hp1, hk, hc2, one_mul, one_mul]
    set t := ringComplex (symbol c (-2))
    have hst : star t * t = 1 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      norm_num
    have hst' : star t = t ^ 2 := by linear_combination (-star t) * h3 + t ^ 2 * hst
    rw [star_pow, hst']
    linear_combination t * h3

/-- **The cubic layer of the `ξ`-reweighted first column has a simple pole.** `M(s)S^{Ξ₀}_1(s/2)` continues to
`{4/3 < Re s < 13/3, Im s > 0}` and a punctured neighbourhood of `4/3`, and `(s − 4/3)M(s)S^{Ξ₀}_1(s/2)` tends to
`(2·2^{5/3}/5)\overline{(9/−2)₃}G̃(−2)·Res S₁ ≠ 0`. -/
theorem unitColumnCubicLayer_simple_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * twistedSquarefreeSeriesG
          (layerTwist (kleinFactor 1 (not_mem_two_of_isCoprime isCoprime_one_left) 0) 1 (by simp) one_ne_zero
            isCoprime_one_left) 1 (s / 2)) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 twoPrimary.twistUnitResidue) ∧
      twoPrimary.twistUnitResidue = 2 * ((2 : ℝ) : ℂ) ^ (5 / 3 : ℂ) / 5 *
        (star (ringComplex (symbol 9 (-2))) * normalizedCubicUnitGauss (-2)) * untwistedSResidue ∧
      twoPrimary.twistUnitResidue ≠ 0 := by
  obtain ⟨Λ, h1, h2, h3, h4, h5⟩ := twoPrimary.cubicUnitLayer_simple_pole
  refine ⟨Λ, fun s hs4 hs hi => ?_, h2, h3, h4, ?_, h5⟩
  · rw [h1 s hs4 hs hi, cubicKleinLayer_eq]
    rfl
  · rw [twoPrimary.twistUnitResidue_closed, show ‖ringComplex twoPrimary.p‖ = 2 from norm_ringComplex_neg_two,
      show ((2 : ℝ) : ℂ) ^ 2 + 1 = 5 by norm_num]
    rfl

end GaloisForLFunctions.OrderSixMetaplecticTheory
