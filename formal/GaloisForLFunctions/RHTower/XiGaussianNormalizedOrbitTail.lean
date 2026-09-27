import GaloisForLFunctions.RHTower.XiGaussianNormalizedOrbit
import GaloisForLFunctions.RHTower.XiGaussianCoefficientTail

/-!
# A degree-independent exponential tail for exactly normalized orbit polynomials

The constants and heat time are fixed before the finite annihilator grows.
The estimate controls the full squared polynomial on every divisor copy;
it does not split or discard any coefficient cross term.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Exact finite interpolation admits one summable majorant at a smaller,
fixed positive heat time, uniformly over all later finite products. -/
theorem exists_xiGaussianNormalizedOrbit_dominating_head
    (z : {z : ℂ // z.im ≠ 0}) (v : ℂ) (t : {t : ℝ // 0 < t}) :
    ∃ (M : ℝ) (H : Finset XiZeroCopy), 0 < M ∧
      ∀ᶠ F : Finset XiZeroCopy in atTop, ∀ q : XiZeroCopy,
        ‖xiPolynomialGaussianHeatTerm (xiGaussianNormalizedOrbitPolynomial z v F) t q‖ ≤
          M ^ 2 * ‖xiPolynomialGaussianHeatTerm
            ((1 + Polynomial.X) *
              xiGaussianSelectedAnnihilator (xiGaussianOrbitComplement z) H)
            ((t : ℝ) / 2) q‖ := by
  obtain ⟨M, hM, hbound⟩ := exists_xiGaussianOrbitNormalizer_linear_bound z v
  obtain ⟨H, hH⟩ := exists_xiGaussianSelectedAnnihilator_dominating_head
    (xiGaussianOrbitComplement z) (1 + Polynomial.X) t
  refine ⟨M, H, hM, ?_⟩
  filter_upwards [hbound, hH] with F hF hHF q
  apply le_trans _ (mul_le_mul_of_nonneg_left (hHF q) (sq_nonneg M))
  rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm,
    xiGaussianNormalizedOrbitPolynomial, evalRealPolynomial_mul,
    evalRealPolynomial_mul, norm_mul, norm_mul, mul_pow, mul_pow]
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hF q) 2
  rw [mul_pow] at hs
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hs (sq_nonneg _)) (Real.exp_pos _).le).trans_eq
      (by ring)

/-- Every tail beyond a cutoff has an exponential bound with constants
independent of the finite interpolation stage and its polynomial degree. -/
theorem exists_xiGaussianNormalizedOrbit_exponential_tail
    (z : {z : ℂ // z.im ≠ 0}) (v : ℂ) (t : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ F : Finset XiZeroCopy in atTop, ∀ R : ℝ,
      xiGaussianTailEnergy (xiGaussianNormalizedOrbitPolynomial z v F) t R ≤
        C * Real.exp (-((t : ℝ) / 2 * R)) := by
  classical
  let s : {s : ℝ // 0 < s} := ⟨(t : ℝ) / 2, half_pos t.property⟩
  obtain ⟨M, H, hM, hH⟩ := exists_xiGaussianNormalizedOrbit_dominating_head z v s
  let Q := (1 + Polynomial.X) *
    xiGaussianSelectedAnnihilator (xiGaussianOrbitComplement z) H
  let u : {u : ℝ // 0 < u} := ⟨(s : ℝ) / 2, half_pos s.property⟩
  let C := M ^ 2 * xiGaussianNativeEnergy Q u + 1
  have hC : 0 < C := by
    have hK : 0 ≤ xiGaussianNativeEnergy Q u := tsum_nonneg fun _ => norm_nonneg _
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hH] with F hF R
  let P := xiGaussianNormalizedOrbitPolynomial z v F
  let S : Set XiZeroCopy := {q | R < (xiSpectralPoint q ^ 2).re}
  have hs := summable_norm_xiPolynomialGaussianHeatTerm u.property Q
  have ht := summable_norm_xiPolynomialGaussianHeatTerm t.property P
  have hp (q : S) : ‖xiPolynomialGaussianHeatTerm P t q.1‖ ≤
      Real.exp (-((t : ℝ) / 2 * R)) * (M ^ 2 *
        ‖xiPolynomialGaussianHeatTerm Q u q.1‖) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left (hF q.1) (Real.exp_pos _).le)
    rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm]
    have he : Real.exp (-((t : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) ≤
        Real.exp (-((t : ℝ) / 2 * R)) *
          Real.exp (-((s : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have hm := mul_le_mul_of_nonneg_left q.property.le s.property.le
      dsimp only [s] at hm ⊢
      linarith
    exact (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq (mul_left_comm _ _ _)
  have hb : (∑' q : S, ‖xiPolynomialGaussianHeatTerm P t q.1‖) ≤
      ∑' q : S, Real.exp (-((t : ℝ) / 2 * R)) *
        (M ^ 2 * ‖xiPolynomialGaussianHeatTerm Q u q.1‖) :=
    Summable.tsum_le_tsum hp (ht.subtype S)
      (((hs.subtype S).mul_left (M ^ 2)).mul_left (Real.exp (-((t : ℝ) / 2 * R))))
  rw [tsum_mul_left, tsum_mul_left] at hb
  have hsub := Summable.tsum_subtype_le _ S (fun _ => norm_nonneg _) hs
  change _ ≤ xiGaussianNativeEnergy Q u at hsub
  change xiGaussianTailEnergy P t R ≤ _ at hb
  calc
    _ ≤ Real.exp (-((t : ℝ) / 2 * R)) *
        (M ^ 2 * ∑' q : S, ‖xiPolynomialGaussianHeatTerm Q u q.1‖) := hb
    _ ≤ Real.exp (-((t : ℝ) / 2 * R)) * (M ^ 2 * xiGaussianNativeEnergy Q u) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsub (sq_nonneg M)) (Real.exp_pos _).le
    _ ≤ C * Real.exp (-((t : ℝ) / 2 * R)) := by
      dsimp only [C]
      nlinarith [Real.exp_pos (-((t : ℝ) / 2 * R))]

end RHTower
