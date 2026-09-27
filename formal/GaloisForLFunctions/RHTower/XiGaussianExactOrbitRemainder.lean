import GaloisForLFunctions.RHTower.XiGaussianNormalizedOrbitTail

/-!
# Exact head and full remainder of a negative orbit test

For a nonreal squared node, every copy of its conjugate orbit contributes
exactly minus one. Other selected copies contribute zero. The remaining
infinite tail is retained, both in the signed trace and positive energy.
No existence of a nonreal squared Xi node is asserted.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The target value makes the half-heat amplitude purely imaginary. -/
def xiGaussianNegativeOrbitPolynomial (t : ℝ) (q₀ : XiZeroCopy)
    (F : Finset XiZeroCopy) : Polynomial ℝ :=
  xiGaussianNormalizedOrbitPolynomial (xiSpectralPoint q₀ ^ 2)
    (Complex.I * Complex.exp ((t : ℂ) * xiSpectralPoint q₀ ^ 2 / 2)) F

theorem xiGaussianNegativeOrbitPolynomial_term_on_orbit
    (t : ℝ) (q₀ : {q : XiZeroCopy // (xiSpectralPoint q ^ 2).im ≠ 0})
    (F : Finset XiZeroCopy) (q : {q : XiZeroCopy // q ∈ xiGaussianConjugateOrbit q₀.1}) :
    xiPolynomialGaussianHeatTerm (xiGaussianNegativeOrbitPolynomial t q₀.1 F) t q.1 = -1 := by
  let z := xiSpectralPoint q₀.1 ^ 2
  let v := Complex.I * Complex.exp ((t : ℂ) * z / 2)
  let P := xiGaussianNegativeOrbitPolynomial t q₀.1 F
  have hv : evalRealPolynomial P z = v :=
    eval_xiGaussianNormalizedOrbitPolynomial_target ⟨z, q₀.property⟩ v F
  have ht : evalRealPolynomial P z ^ 2 * Complex.exp (-(t : ℂ) * z) = -1 := by
    rw [hv]
    dsimp only [v]
    rw [mul_pow, Complex.I_sq, pow_two, ← Complex.exp_add, mul_assoc, ← Complex.exp_add]
    have he : (t : ℂ) * z / 2 + (t : ℂ) * z / 2 + -(t : ℂ) * z = 0 := by ring
    rw [he, Complex.exp_zero, mul_one]
  rcases (mem_xiGaussianConjugateOrbit q₀.1 q.1).mp q.property with hz | hz
  · simpa only [xiPolynomialGaussianHeatTerm, xiGaussianHeatTerm, hz, z, P] using ht
  · change xiSpectralPoint q.1 ^ 2 = (starRingEnd ℂ) z at hz
    have heq : xiPolynomialGaussianHeatTerm P t q.1 =
        (starRingEnd ℂ) (evalRealPolynomial P z ^ 2 * Complex.exp (-(t : ℂ) * z)) := by
      rw [xiPolynomialGaussianHeatTerm, xiGaussianHeatTerm, hz,
        evalRealPolynomial_conj, map_mul, map_pow, ← Complex.exp_conj]
      simp only [map_mul, map_neg, Complex.conj_ofReal, map_pow, z]
    rw [heq, ht, map_neg, map_one]

theorem xiGaussianNegativeOrbitPolynomial_term_off_orbit
    (t : ℝ) (q₀ : XiZeroCopy) (F : Finset XiZeroCopy)
    (q : {q : XiZeroCopy // q ∈ F ∧ q ∉ xiGaussianConjugateOrbit q₀}) :
    xiPolynomialGaussianHeatTerm (xiGaussianNegativeOrbitPolynomial t q₀ F) t q.1 = 0 := by
  have hS : q.1 ∈ xiGaussianOrbitComplement (xiSpectralPoint q₀ ^ 2) := by
    simpa only [xiGaussianOrbitComplement, Set.mem_setOf_eq, not_or] using
      (not_congr (mem_xiGaussianConjugateOrbit q₀ q.1)).mp q.property.2
  have hv := xiGaussianNormalizedOrbitPolynomial_vanishes (xiSpectralPoint q₀ ^ 2)
    (Complex.I * Complex.exp ((t : ℂ) * xiSpectralPoint q₀ ^ 2 / 2)) F
    ⟨q.1, q.property.1, hS⟩
  simp only [xiPolynomialGaussianHeatTerm, xiGaussianNegativeOrbitPolynomial,
    hv, zero_pow two_ne_zero, zero_mul]

/-- Exact signed head and exact positive head, retaining all orbit multiplicities. -/
theorem xiGaussianNegativeOrbitPolynomial_exact_head
    (t : ℝ) (q₀ : {q : XiZeroCopy // (xiSpectralPoint q ^ 2).im ≠ 0})
    (R : {R : ℝ // (xiSpectralPoint q₀.1 ^ 2).re ≤ R})
    (F : {F : Finset XiZeroCopy // (finite_xiHeatShell R).toFinset ⊆ F}) :
    (∑ q ∈ (finite_xiHeatShell R).toFinset,
      xiPolynomialGaussianHeatTerm (xiGaussianNegativeOrbitPolynomial t q₀.1 F) t q) =
        -((xiGaussianConjugateOrbit q₀.1).card : ℂ) ∧
    (∑ q ∈ (finite_xiHeatShell R).toFinset,
      ‖xiPolynomialGaussianHeatTerm (xiGaussianNegativeOrbitPolynomial t q₀.1 F) t q‖) =
        ((xiGaussianConjugateOrbit q₀.1).card : ℝ) := by
  classical
  let O := xiGaussianConjugateOrbit q₀.1
  let B := (finite_xiHeatShell R).toFinset
  let f := xiPolynomialGaussianHeatTerm (xiGaussianNegativeOrbitPolynomial t q₀.1 F) t
  have hsub : O ⊆ B := by
    intro q hq
    rw [Set.Finite.mem_toFinset]
    change (xiSpectralPoint q ^ 2).re ≤ (R : ℝ)
    rcases (mem_xiGaussianConjugateOrbit q₀.1 q).mp hq with hz | hz
    · simpa only [hz] using R.property
    · simpa only [hz, Complex.conj_re] using R.property
  have hon (q : XiZeroCopy) (hq : q ∈ O) : f q = -1 :=
    xiGaussianNegativeOrbitPolynomial_term_on_orbit t q₀ F ⟨q, hq⟩
  have hoff (q : XiZeroCopy) (hq : q ∈ B) (hqo : q ∉ O) : f q = 0 :=
    xiGaussianNegativeOrbitPolynomial_term_off_orbit t q₀.1 F ⟨q, F.property hq, hqo⟩
  have he : (∑ q ∈ B, f q) = ∑ q ∈ O, f q := (Finset.sum_subset hsub hoff).symm
  have hn : (∑ q ∈ B, ‖f q‖) = ∑ q ∈ O, ‖f q‖ :=
    (Finset.sum_subset hsub (fun q hq hqo => by rw [hoff q hq hqo, norm_zero])).symm
  constructor
  · change (∑ q ∈ B, f q) = _
    rw [he, Finset.sum_congr rfl hon]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one, O]
  · change (∑ q ∈ B, ‖f q‖) = _
    rw [hn, Finset.sum_congr rfl (fun q hq => congrArg norm (hon q hq))]
    simp only [norm_neg, norm_one, Finset.sum_const, nsmul_eq_mul, mul_one, O]

/-- The actual complex trace and native energy split into their exact orbit
contribution and the entire unsimplified infinite tail. -/
theorem xiGaussianNegativeOrbitPolynomial_exact_remainder
    (t : {t : ℝ // 0 < t})
    (q₀ : {q : XiZeroCopy // (xiSpectralPoint q ^ 2).im ≠ 0})
    (R : {R : ℝ // (xiSpectralPoint q₀.1 ^ 2).re ≤ R})
    (F : {F : Finset XiZeroCopy // (finite_xiHeatShell R).toFinset ⊆ F}) :
    xiPolynomialGaussianHeatTrace (xiGaussianNegativeOrbitPolynomial t q₀.1 F) t =
        -((xiGaussianConjugateOrbit q₀.1).card : ℂ) +
          ∑' q : {q : XiZeroCopy // (R : ℝ) < (xiSpectralPoint q ^ 2).re},
            xiPolynomialGaussianHeatTerm (xiGaussianNegativeOrbitPolynomial t q₀.1 F) t q.1 ∧
    xiGaussianNativeEnergy (xiGaussianNegativeOrbitPolynomial t q₀.1 F) t =
        ((xiGaussianConjugateOrbit q₀.1).card : ℝ) +
          xiGaussianTailEnergy (xiGaussianNegativeOrbitPolynomial t q₀.1 F) t R := by
  classical
  let B := (finite_xiHeatShell R).toFinset
  have hset : (B : Set XiZeroCopy)ᶜ =
      {q : XiZeroCopy | (R : ℝ) < (xiSpectralPoint q ^ 2).re} := by
    ext q
    simp only [Set.mem_compl_iff, Finset.mem_coe, B, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq, not_le]
  obtain ⟨hh, hn⟩ := xiGaussianNegativeOrbitPolynomial_exact_head t q₀ R F
  have hs := summable_xiPolynomialGaussianHeatTerm t.property
    (xiGaussianNegativeOrbitPolynomial t q₀.1 F)
  have hc := hs.sum_add_tsum_compl (s := B)
  have hk := hs.norm.sum_add_tsum_compl (s := B)
  rw [hset, hh] at hc
  rw [hset, hn] at hk
  exact ⟨hc.symm, hk.symm⟩

/-- The error in the full complex trace is at most the complete positive tail. -/
theorem norm_xiGaussianNegativeOrbitPolynomial_remainder_le_tail
    (t : {t : ℝ // 0 < t})
    (q₀ : {q : XiZeroCopy // (xiSpectralPoint q ^ 2).im ≠ 0})
    (R : {R : ℝ // (xiSpectralPoint q₀.1 ^ 2).re ≤ R})
    (F : {F : Finset XiZeroCopy // (finite_xiHeatShell R).toFinset ⊆ F}) :
    ‖xiPolynomialGaussianHeatTrace (xiGaussianNegativeOrbitPolynomial t q₀.1 F) t +
      ((xiGaussianConjugateOrbit q₀.1).card : ℂ)‖ ≤
        xiGaussianTailEnergy (xiGaussianNegativeOrbitPolynomial t q₀.1 F) t R := by
  classical
  have he := (xiGaussianNegativeOrbitPolynomial_exact_remainder t q₀ R F).1
  have hs := (summable_xiPolynomialGaussianHeatTerm t.property
    (xiGaussianNegativeOrbitPolynomial t q₀.1 F)).subtype
      {q : XiZeroCopy | (R : ℝ) < (xiSpectralPoint q ^ 2).re}
  calc
    _ = ‖∑' q : {q : XiZeroCopy // (R : ℝ) < (xiSpectralPoint q ^ 2).re},
        xiPolynomialGaussianHeatTerm (xiGaussianNegativeOrbitPolynomial t q₀.1 F) t q.1‖ := by
      rw [he]
      congr 1
      ring
    _ ≤ _ := norm_tsum_le_tsum_norm hs.norm

end RHTower
