import GaloisForLFunctions.RHTower.XiGaussianPolarInterpolation
import GaloisForLFunctions.RHTower.XiGaussianExactOrbitRemainder
import GaloisForLFunctions.RHTower.XiGaussianRealChannelEnergy

/-!
# Full signed orbit localization with an exactly vanishing polar term

At one fixed positive heat time, removing the polar value preserves the
entire finite head exactly. The remaining native energy is exponentially
small in the cutoff with a constant independent of polynomial degree.
An off-critical orbit would therefore survive inside the pole-free source
class. No such orbit is asserted to exist.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators Real
noncomputable section
namespace RHTower

/-- Exact pole cancellation and exact head interpolation coexist with a
degree-independent exponential bound on the complete infinite remainder. -/
theorem exists_xiGaussian_poleFree_exponential_orbit_localization
    (t : {t : ℝ // 0 < t})
    (q₀ : {q : XiZeroCopy // (xiSpectralPoint q ^ 2).im ≠ 0}) :
    ∃ C : ℝ, 0 < C ∧
      ∀ R : {R : ℝ // (xiSpectralPoint q₀.1 ^ 2).re ≤ R},
        ∃ Q : Polynomial ℝ,
          Q.eval (-(1 / 4 : ℝ)) = 0 ∧
          (∀ q ∈ (finite_xiHeatShell R).toFinset,
            xiPolynomialGaussianHeatTerm Q t q =
              if q ∈ xiGaussianConjugateOrbit q₀.1 then -1 else 0) ∧
          xiGaussianNativeEnergy Q t = ((xiGaussianConjugateOrbit q₀.1).card : ℝ) +
            xiGaussianTailEnergy Q t R ∧
          xiGaussianTailEnergy Q t R ≤ C * Real.exp (-((t : ℝ) / 2 * (R : ℝ))) ∧
          ‖xiPolynomialGaussianHeatTrace Q t +
            ((xiGaussianConjugateOrbit q₀.1).card : ℂ)‖ ≤ xiGaussianTailEnergy Q t R ∧
          xiGaussianRealChannelEnergy Q t ≤ xiGaussianTailEnergy Q t R ∧
          ((xiGaussianConjugateOrbit q₀.1).card : ℝ) ≤
            ∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom Q t q ∧
          |xiGaussianPrimeGammaDifference Q t -
            π * ((xiGaussianConjugateOrbit q₀.1).card : ℝ)| ≤
              π * C * Real.exp (-((t : ℝ) / 2 * (R : ℝ))) := by
  classical
  let z : {z : ℂ // z.im ≠ 0} := ⟨xiSpectralPoint q₀.1 ^ 2, q₀.property⟩
  let v := Complex.I * Complex.exp (((t : ℝ) : ℂ) * z / 2)
  obtain ⟨C, hC, htail⟩ := exists_xiGaussianNormalizedOrbit_exponential_tail z v t
  refine ⟨2 * C, mul_pos (by positivity) hC, fun R => ?_⟩
  let B := (finite_xiHeatShell R).toFinset
  let m : ℝ := (xiGaussianConjugateOrbit q₀.1).card
  let E := C * Real.exp (-((t : ℝ) / 2 * (R : ℝ)))
  have hE : 0 < E := mul_pos hC (Real.exp_pos _)
  obtain ⟨F, hF, hcut⟩ := (htail.and (eventually_ge_atTop B)).exists
  let P := xiGaussianNegativeOrbitPolynomial t q₀.1 F
  have hPtail : xiGaussianTailEnergy P t R ≤ E := hF R
  obtain ⟨Q, hQpole, hQeval, hQcontrol⟩ :=
    exists_xiGaussian_poleFree_interpolating_approximation P B t ⟨E, hE⟩
  have hterms (q : XiZeroCopy) (hq : q ∈ B) :
      xiPolynomialGaussianHeatTerm Q t q = xiPolynomialGaussianHeatTerm P t q := by
    simp only [xiPolynomialGaussianHeatTerm, hQeval q hq]
  have hQhead (q : XiZeroCopy) (hq : q ∈ B) :
      xiPolynomialGaussianHeatTerm Q t q =
        if q ∈ xiGaussianConjugateOrbit q₀.1 then -1 else 0 := by
    rw [hterms q hq]
    by_cases ho : q ∈ xiGaussianConjugateOrbit q₀.1
    · rw [if_pos ho]
      exact xiGaussianNegativeOrbitPolynomial_term_on_orbit t q₀ F ⟨q, ho⟩
    · rw [if_neg ho]
      exact xiGaussianNegativeOrbitPolynomial_term_off_orbit t q₀.1 F ⟨q, hcut hq, ho⟩
  obtain ⟨hPhead, hPnorm⟩ := xiGaussianNegativeOrbitPolynomial_exact_head t q₀ R ⟨F, hcut⟩
  have hQsum : (∑ q ∈ B, xiPolynomialGaussianHeatTerm Q t q) =
      -((xiGaussianConjugateOrbit q₀.1).card : ℂ) :=
    (Finset.sum_congr rfl hterms).trans hPhead
  have hQnorm : (∑ q ∈ B, ‖xiPolynomialGaussianHeatTerm Q t q‖) = m :=
    (Finset.sum_congr rfl (fun q hq => congrArg norm (hterms q hq))).trans hPnorm
  have hset : (B : Set XiZeroCopy)ᶜ =
      {q : XiZeroCopy | (R : ℝ) < (xiSpectralPoint q ^ 2).re} := by
    ext q
    simp only [Set.mem_compl_iff, Finset.mem_coe, B, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq, not_le]
  have hs := summable_xiPolynomialGaussianHeatTerm t.property Q
  have hcomplex := hs.sum_add_tsum_compl (s := B)
  have henergy := hs.norm.sum_add_tsum_compl (s := B)
  rw [hset, hQsum] at hcomplex
  rw [hset, hQnorm] at henergy
  have hK : xiGaussianNativeEnergy Q t = m + xiGaussianTailEnergy Q t R := henergy.symm
  have hKP : xiGaussianNativeEnergy P t = m + xiGaussianTailEnergy P t R :=
    (xiGaussianNegativeOrbitPolynomial_exact_remainder t q₀ R ⟨F, hcut⟩).2
  have hKdiff : |xiGaussianNativeEnergy Q t - xiGaussianNativeEnergy P t| < E :=
    (hQcontrol ⟨(t : ℝ), show (t : ℝ) ≤ (t : ℝ) from le_rfl⟩).2.2.1
  have hQt : xiGaussianTailEnergy Q t R ≤ 2 * E := by
    have hdiff := (abs_lt.mp hKdiff).2
    linarith only [hK, hKP, hdiff, hPtail]
  have hH : ‖xiPolynomialGaussianHeatTrace Q t +
      ((xiGaussianConjugateOrbit q₀.1).card : ℂ)‖ ≤ xiGaussianTailEnergy Q t R := by
    calc
      _ = ‖∑' q : {q : XiZeroCopy // (R : ℝ) < (xiSpectralPoint q ^ 2).re},
          xiPolynomialGaussianHeatTerm Q t q.1‖ := by
        change ‖(∑' q, xiPolynomialGaussianHeatTerm Q t q) + _‖ = _
        rw [← hcomplex]
        congr 1
        rw [neg_add_eq_sub, sub_add_cancel]
        rfl
      _ ≤ _ := norm_tsum_le_tsum_norm (hs.subtype _).norm
  have hHreal : |xiPolynomialGaussianHeatTraceReal Q t + m| ≤ xiGaussianTailEnergy Q t R :=
    (Complex.abs_re_le_norm
      (xiPolynomialGaussianHeatTrace Q t +
        ((xiGaussianConjugateOrbit q₀.1).card : ℂ))).trans hH
  have hupper := (abs_le.mp hHreal).2
  refine ⟨Q, hQpole, hQhead, hK, ?_, hH, ?_, ?_, ?_⟩
  · exact hQt.trans_eq (by dsimp only [E]; ring)
  · rw [xiGaussianRealChannelEnergy_eq_half_energy_add_trace]
    change (xiGaussianNativeEnergy Q t + xiPolynomialGaussianHeatTraceReal Q t) / 2 ≤ _
    linarith only [hK, hupper]
  · rw [xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace]
    linarith only [hK, hupper]
  · rw [xiGaussianPrimeGammaDifference_eq_polar_sub_residual, hQpole,
      zero_pow two_ne_zero, mul_zero, zero_mul, zero_sub,
      xiGaussianCompletedSourceResidual_eq_trace]
    have he : - (π * xiPolynomialGaussianHeatTraceReal Q t) - π * m =
        -(π * (xiPolynomialGaussianHeatTraceReal Q t + m)) := by ring
    change |-(π * xiPolynomialGaussianHeatTraceReal Q t) - π * m| ≤ _
    rw [he, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left (hHreal.trans hQt) Real.pi_pos.le).trans_eq
      (by dsimp only [E]; ring)

/-- Either RH holds or every prescribed positive time admits pole-free
tests whose prime-minus-Gamma excess approaches a positive orbit mass.
The bound includes every divisor copy and every polynomial cross term. -/
theorem xiGaussian_poleFree_exponential_source_alternative :
    RiemannHypothesis ∨ ∀ t : {t : ℝ // 0 < t},
      ∃ m C R₀ : ℝ, 0 < m ∧ 0 < C ∧ ∀ R : Set.Ici R₀,
        ∃ Q : Polynomial ℝ,
          Q.eval (-(1 / 4 : ℝ)) = 0 ∧
          m ≤ xiGaussianNativeEnergy Q t ∧
          xiGaussianNativeEnergy Q t ≤ m + C * Real.exp (-((t : ℝ) / 2 * (R : ℝ))) ∧
          xiGaussianRealChannelEnergy Q t ≤ C * Real.exp (-((t : ℝ) / 2 * (R : ℝ))) ∧
          |xiGaussianPrimeGammaDifference Q t - π * m| ≤
            π * C * Real.exp (-((t : ℝ) / 2 * (R : ℝ))) := by
  classical
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · refine Or.inr fun t => ?_
    obtain ⟨q, hq⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
    let q₀ : {q : XiZeroCopy // (xiSpectralPoint q ^ 2).im ≠ 0} := ⟨q, ne_of_gt hq⟩
    obtain ⟨C, hC, hloc⟩ := exists_xiGaussian_poleFree_exponential_orbit_localization t q₀
    have hm : (0 : ℝ) < (xiGaussianConjugateOrbit q).card := by
      exact_mod_cast xiGaussianConjugateOrbit_card_pos q
    refine ⟨(xiGaussianConjugateOrbit q).card, C, (xiSpectralPoint q ^ 2).re,
      hm, hC, fun R => ?_⟩
    obtain ⟨Q, hpole, _, hK, htail, _, hJ, _, hG⟩ := hloc R
    have htail0 := xiGaussianTailEnergy_nonneg Q t R
    refine ⟨Q, hpole, ?_, ?_, hJ.trans htail, hG⟩
    · linarith only [hK, htail0]
    · linarith only [hK, htail]

end RHTower
