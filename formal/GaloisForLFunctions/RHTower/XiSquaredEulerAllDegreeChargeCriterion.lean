import GaloisForLFunctions.RHTower.XiSquaredEulerApertureHilbertCorrelation
import GaloisForLFunctions.RHTower.XiTraceHankelCountableCriterion
import GaloisForLFunctions.RHTower.XiOffLineQuartetThermalOrientationBound
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm

/-!
# All-degree squared-Euler charge criterion

The pointwise squared-Euler identity is promoted to the complete multiplicity-exact Xi divisor.
Both its positive Hilbert channel and transverse charge channel are unconditionally summable at
every polynomial degree.  Their difference is exactly the real Xi trace-Hankel form.

Consequently the all-degree charge-domination condition is equivalent to RH.  By coefficient
density, it is enough to test the countable family of integer polynomials.  This is the exact
right-edge consumer for any proposed source proof of the all-degree aperture inequality.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The reciprocal-square sector bounds its transverse coefficient by its positive real mass. -/
theorem xiZeroCopyReciprocalSquare_normSq_div_re_le
    (q : XiZeroCopy) :
    Complex.normSq (xiZeroCopyReciprocalSquare q) /
        (xiZeroCopyReciprocalSquare q).re ≤
      (85 / 84 : ℝ) * (xiZeroCopyReciprocalSquare q).re := by
  let z := xiZeroCopyReciprocalSquare q
  have hx : 0 < z.re := xiZeroCopyReciprocalSquare_re_pos q
  have hsector : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2 := by
    simpa only [z, xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  have hnorm : Complex.normSq z ≤ (85 / 84 : ℝ) * z.re ^ 2 := by
    rw [Complex.normSq_apply]
    nlinarith
  apply (div_le_iff₀ hx).2
  nlinarith

/-- The complete multiplicity-exact trace-Hankel summand is absolutely summable at every
polynomial degree. -/
theorem summable_xiSquaredEulerApertureHankelTerm
    (p : Polynomial ℝ) :
    Summable (xiSquaredEulerApertureHankelTerm p) := by
  obtain ⟨M, hMone, hM⟩ := exists_xi_central_reciprocal_square_norm_bound
  let C := evalRealPolynomialNormBound p M
  have hC : 0 ≤ C :=
    evalRealPolynomialNormBound_nonneg p (le_trans zero_le_one hMone)
  have hbase : Summable (fun q : XiZeroCopy =>
      ‖xiZeroCopyReciprocalSquare q‖ * C ^ 2) :=
    summable_xiZeroCopyReciprocalSquare.norm.mul_right (C ^ 2)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _)
    (fun q => ?_) hbase
  let z := xiZeroCopyReciprocalSquare q
  let w := evalRealPolynomial p z
  have hw : ‖w‖ ≤ C := by
    apply norm_evalRealPolynomial_le p
    simpa only [z, xiZeroCopyReciprocalSquare_eq] using hM q.1
  calc
    ‖xiSquaredEulerApertureHankelTerm p q‖ = |(z * w ^ 2).re| := by
      rw [Real.norm_eq_abs]
      rfl
    _ ≤ ‖z * w ^ 2‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ * ‖w‖ ^ 2 := by rw [norm_mul, norm_pow]
    _ ≤ ‖z‖ * C ^ 2 := by
      gcongr

/-- Complex parent of the trace-Hankel summand is absolutely summable. -/
theorem summable_xiSquaredEulerApertureComplexHankelTerm
    (p : Polynomial ℝ) :
    Summable (fun q : XiZeroCopy =>
      xiZeroCopyReciprocalSquare q *
        evalRealPolynomial p (xiZeroCopyReciprocalSquare q) ^ 2) := by
  obtain ⟨M, hMone, hM⟩ := exists_xi_central_reciprocal_square_norm_bound
  let C := evalRealPolynomialNormBound p M
  have hC : 0 ≤ C :=
    evalRealPolynomialNormBound_nonneg p (le_trans zero_le_one hMone)
  have hbase : Summable (fun q : XiZeroCopy =>
      ‖xiZeroCopyReciprocalSquare q‖ * C ^ 2) :=
    summable_xiZeroCopyReciprocalSquare.norm.mul_right (C ^ 2)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _)
    (fun q => ?_) hbase
  have hw : ‖evalRealPolynomial p (xiZeroCopyReciprocalSquare q)‖ ≤ C := by
    apply norm_evalRealPolynomial_le p
    simpa only [xiZeroCopyReciprocalSquare_eq] using hM q.1
  rw [norm_mul, norm_pow]
  gcongr

/-- The complete transverse charge is summable.  Uniform sector control turns its apparently
singular coefficient `normSq λ / re λ` into a constant multiple of the summable positive mass
`re λ`. -/
theorem summable_xiSquaredEulerApertureTransverseTerm
    (p : Polynomial ℝ) :
    Summable (xiSquaredEulerApertureTransverseTerm p) := by
  obtain ⟨M, hMone, hM⟩ := exists_xi_central_reciprocal_square_norm_bound
  let C := evalRealPolynomialNormBound p M
  have hC : 0 ≤ C :=
    evalRealPolynomialNormBound_nonneg p (le_trans zero_le_one hMone)
  have hre : Summable (fun q : XiZeroCopy =>
      (xiZeroCopyReciprocalSquare q).re) :=
    Complex.reCLM.summable summable_xiZeroCopyReciprocalSquare
  have hbound : Summable (fun q : XiZeroCopy =>
      ((85 / 84 : ℝ) * C ^ 2) *
        (xiZeroCopyReciprocalSquare q).re) :=
    hre.mul_left ((85 / 84 : ℝ) * C ^ 2)
  apply Summable.of_nonneg_of_le
    (fun q => xiSquaredEulerApertureTransverseTerm_nonneg p q)
    (fun q => ?_) hbound
  let z := xiZeroCopyReciprocalSquare q
  let w := evalRealPolynomial p z
  have hw : ‖w‖ ≤ C := by
    apply norm_evalRealPolynomial_le p
    simpa only [z, xiZeroCopyReciprocalSquare_eq] using hM q.1
  have him : w.im ^ 2 ≤ C ^ 2 := by
    have hi := Complex.abs_im_le_norm w
    have habs : |w.im| ≤ C := hi.trans hw
    have hprod : 0 ≤ (C - |w.im|) * (C + |w.im|) :=
      mul_nonneg (sub_nonneg.mpr habs) (add_nonneg hC (abs_nonneg _))
    nlinarith [sq_abs w.im]
  have hratio := xiZeroCopyReciprocalSquare_normSq_div_re_le q
  unfold xiSquaredEulerApertureTransverseTerm
  change Complex.normSq z / z.re * w.im ^ 2 ≤
    ((85 / 84 : ℝ) * C ^ 2) * z.re
  have hratio0 : 0 ≤ Complex.normSq z / z.re := by
    exact div_nonneg (Complex.normSq_nonneg z)
      (xiZeroCopyReciprocalSquare_re_pos q).le
  calc
    Complex.normSq z / z.re * w.im ^ 2 ≤
        Complex.normSq z / z.re * C ^ 2 := by gcongr
    _ ≤ ((85 / 84 : ℝ) * z.re) * C ^ 2 := by gcongr
    _ = ((85 / 84 : ℝ) * C ^ 2) * z.re := by ring

/-- The complete positive Hilbert channel is summable at every degree. -/
theorem summable_xiSquaredEulerApertureHilbertTerm
    (p : Polynomial ℝ) :
    Summable (xiSquaredEulerApertureHilbertTerm p) := by
  have hh := summable_xiSquaredEulerApertureHankelTerm p
  have ht := summable_xiSquaredEulerApertureTransverseTerm p
  apply (hh.add ht).congr
  intro q
  have hsplit := xiSquaredEulerApertureHankelTerm_eq_hilbert_sub_transverse p q
  linarith

/-- Complete positive squared-Euler aperture energy. -/
def xiSquaredEulerApertureHilbertEnergy (p : Polynomial ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiSquaredEulerApertureHilbertTerm p q

/-- Complete squared-Euler transverse charge. -/
def xiSquaredEulerApertureTransverseEnergy (p : Polynomial ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiSquaredEulerApertureTransverseTerm p q

/-- Complete copied-divisor trace-Hankel value. -/
def xiSquaredEulerApertureHankelValue (p : Polynomial ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiSquaredEulerApertureHankelTerm p q

/-- Global all-degree Hilbert-minus-charge decomposition. -/
theorem xiSquaredEulerApertureHankelValue_eq_hilbert_sub_transverse
    (p : Polynomial ℝ) :
    xiSquaredEulerApertureHankelValue p =
      xiSquaredEulerApertureHilbertEnergy p -
        xiSquaredEulerApertureTransverseEnergy p := by
  rw [xiSquaredEulerApertureHankelValue,
    xiSquaredEulerApertureHilbertEnergy,
    xiSquaredEulerApertureTransverseEnergy,
    ← (summable_xiSquaredEulerApertureHilbertTerm p).tsum_sub
      (summable_xiSquaredEulerApertureTransverseTerm p)]
  apply tsum_congr
  exact xiSquaredEulerApertureHankelTerm_eq_hilbert_sub_transverse p

/-- Grouping multiplicity copies recovers the existing divisor-weighted Xi trace-Hankel value. -/
theorem tsum_xiSquaredEulerApertureComplexHankelTerm_eq
    (p : Polynomial ℝ) :
    (∑' q : XiZeroCopy,
      xiZeroCopyReciprocalSquare q *
        evalRealPolynomial p (xiZeroCopyReciprocalSquare q) ^ 2) =
      xiCentralTraceHankel p := by
  have hcopy := summable_xiSquaredEulerApertureComplexHankelTerm p
  rw [hcopy.tsum_sigma, xiCentralTraceHankel]
  apply tsum_congr
  intro ρ
  rw [tsum_fintype]
  simp only [xiZeroCopyReciprocalSquare_eq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnonneg : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) :=
    le_of_lt (xi_divisor_pos_on_support ρ)
  have hcastR :
      (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat : ℝ) =
        ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  have hcast :
      (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat : ℂ) =
        ((((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ)) : ℂ) := by
    exact_mod_cast hcastR
  rw [xiCentralTraceHankelTerm, hcast]
  ring

/-- The copied-divisor real Hankel value is exactly the established Xi trace-Hankel form. -/
theorem xiSquaredEulerApertureHankelValue_eq_traceHankel_re
    (p : Polynomial ℝ) :
    xiSquaredEulerApertureHankelValue p =
      (xiCentralTraceHankel p).re := by
  have hsum := summable_xiSquaredEulerApertureComplexHankelTerm p
  calc
    xiSquaredEulerApertureHankelValue p =
        ∑' q : XiZeroCopy,
          (xiZeroCopyReciprocalSquare q *
            evalRealPolynomial p (xiZeroCopyReciprocalSquare q) ^ 2).re := by
      rfl
    _ = (∑' q : XiZeroCopy,
          xiZeroCopyReciprocalSquare q *
            evalRealPolynomial p (xiZeroCopyReciprocalSquare q) ^ 2).re := by
      exact (Complex.re_tsum hsum).symm
    _ = (xiCentralTraceHankel p).re := by
      rw [tsum_xiSquaredEulerApertureComplexHankelTerm_eq]

/-- All-degree squared-Euler transverse-charge domination. -/
def XiSquaredEulerApertureChargeDominated : Prop :=
  ∀ p : Polynomial ℝ,
    xiSquaredEulerApertureTransverseEnergy p ≤
      xiSquaredEulerApertureHilbertEnergy p

/-- Countable integer-polynomial form of all-degree transverse-charge domination. -/
def XiSquaredEulerApertureIntChargeDominated : Prop :=
  ∀ p : Polynomial ℤ,
    xiSquaredEulerApertureTransverseEnergy
        (p.map (Int.castRingHom ℝ)) ≤
      xiSquaredEulerApertureHilbertEnergy
        (p.map (Int.castRingHom ℝ))

/-- **Source discharge of the all-degree charge condition.**  Integer-polynomial squared-Euler
charge domination is exactly positivity of the zero-free normalized prime--Gamma source Hankel
form.  This connector is proved from the two exact value identities, without passing through RH. -/
theorem xiSquaredEulerApertureIntChargeDominated_iff_primeArchSourceTraceHankelIntNonnegative :
    XiSquaredEulerApertureIntChargeDominated ↔
      PrimeArchSourceTraceHankelIntNonnegative := by
  constructor
  · intro hdom p
    rw [← xiCentralTraceHankel_eq_primeArchSourceTraceHankel,
      ← xiSquaredEulerApertureHankelValue_eq_traceHankel_re,
      xiSquaredEulerApertureHankelValue_eq_hilbert_sub_transverse]
    exact sub_nonneg.mpr (hdom p)
  · intro hsource p
    have hp := hsource p
    rw [← xiCentralTraceHankel_eq_primeArchSourceTraceHankel,
      ← xiSquaredEulerApertureHankelValue_eq_traceHankel_re,
      xiSquaredEulerApertureHankelValue_eq_hilbert_sub_transverse] at hp
    exact sub_nonneg.mp hp

/-- A coherent prime--Gamma source positivity theorem discharges the complete squared-Euler
transverse charge inequality. -/
theorem xiSquaredEulerApertureIntChargeDominated_of_primeArchSourceTraceHankelIntNonnegative
    (hsource : PrimeArchSourceTraceHankelIntNonnegative) :
    XiSquaredEulerApertureIntChargeDominated :=
  xiSquaredEulerApertureIntChargeDominated_iff_primeArchSourceTraceHankelIntNonnegative.mpr hsource

/-- **Exact all-degree charge criterion.**  Domination of the transverse channel by the positive
Hilbert channel for every real polynomial is equivalent to RH. -/
theorem xiSquaredEulerApertureChargeDominated_iff_riemannHypothesis :
    XiSquaredEulerApertureChargeDominated ↔ RiemannHypothesis := by
  constructor
  · intro hdom
    apply xiCentralTraceHankelNonnegative_iff_riemannHypothesis.mp
    intro p
    rw [← xiSquaredEulerApertureHankelValue_eq_traceHankel_re,
      xiSquaredEulerApertureHankelValue_eq_hilbert_sub_transverse]
    exact sub_nonneg.mpr (hdom p)
  · intro hRH p
    have htrace := xiCentralTraceHankelNonnegative_of_riemannHypothesis hRH p
    rw [← xiSquaredEulerApertureHankelValue_eq_traceHankel_re,
      xiSquaredEulerApertureHankelValue_eq_hilbert_sub_transverse] at htrace
    exact sub_nonneg.mp htrace

/-- **Countable all-degree charge criterion.**  It is enough, and necessary, to establish the
same charge inequality on `ℤ[X]`. -/
theorem xiSquaredEulerApertureIntChargeDominated_iff_riemannHypothesis :
    XiSquaredEulerApertureIntChargeDominated ↔ RiemannHypothesis := by
  constructor
  · intro hdom
    apply xiCentralTraceHankelIntNonnegative_iff_riemannHypothesis.mp
    intro p
    rw [← xiSquaredEulerApertureHankelValue_eq_traceHankel_re,
      xiSquaredEulerApertureHankelValue_eq_hilbert_sub_transverse]
    exact sub_nonneg.mpr (hdom p)
  · intro hRH p
    have htrace := xiCentralTraceHankelNonnegative_of_riemannHypothesis hRH
      (p.map (Int.castRingHom ℝ))
    rw [← xiSquaredEulerApertureHankelValue_eq_traceHankel_re,
      xiSquaredEulerApertureHankelValue_eq_hilbert_sub_transverse] at htrace
    exact sub_nonneg.mp htrace

/-- Integer-polynomial squared-Euler charge domination discharges the complete square-summable
Xi Weil positivity theorem. -/
theorem xiWeilPolarization_nonneg_of_xiSquaredEulerApertureIntChargeDominated
    (hdom : XiSquaredEulerApertureIntChargeDominated) :
    ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
      0 ≤ (xiWeilPolarization F F).re := by
  apply riemannHypothesis_iff_xiWeilPolarization_nonneg.mp
  exact xiSquaredEulerApertureIntChargeDominated_iff_riemannHypothesis.mp hdom

/-- Exact connector from the countable squared-Euler charge condition to the full Xi Weil cone. -/
theorem xiSquaredEulerApertureIntChargeDominated_iff_fullWeil_nonneg :
    XiSquaredEulerApertureIntChargeDominated ↔
      ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
        0 ≤ (xiWeilPolarization F F).re :=
  xiSquaredEulerApertureIntChargeDominated_iff_riemannHypothesis.trans
    riemannHypothesis_iff_xiWeilPolarization_nonneg

end

end RHTower
