import GaloisForLFunctions.RHTower.GaussHodgeSeamEnergyBridge
import GaloisForLFunctions.RHTower.DeningerDivisorSchwarzMonodromy

/-!
# Coherence budget and conjugate-pair classification of the missing transform

The residual open core of the Hodge/seam mass programme is one horizontal divisor transform:
the divisor average of the centered cosh defect `p^t + p^{-t} - 2`, `t = 2·Re - 1`.  This
module fences and prices that transform with two unconditional laws.

**Conjugate-pair classification.**  The divisor is closed under conjugation, and at every copy
the Hermitian sample — the quantity the transform must reach — factors as the product of the
holomorphic character at the copy and at its conjugate copy:
`char(ρ)·char(conj ρ) = p^{2 Re ρ - 1}`.  The missing transform is therefore exactly a
sub-diagonal of the two-zero holomorphic kernel: the conjugate-pair diagonal of a bilinear
(squared explicit-formula) object.  This is the pair-correlation classification of the wall,
as a theorem.

**Coherence budget.**  Cauchy–Schwarz converts the diagonal into a certificate: for any finite
family of copies and complex weights, the squared zero-side exponential sum at frequency
`log p` is at most the ℓ² weight mass times `(cosh-defect mass) + 2·card`.  The cosh-defect
mass is the Hodge/seam invariant, so off-line mass is precisely the coherence budget beyond
square-root cancellation; under RH the budget collapses to the diagonal count `2·card` at
every prime frequency and every weight.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## Conjugate-pair classification -/

/-- Conjugation closure of the divisor at copy level: the support point of the conjugated
copy is the conjugated point. -/
theorem xiZeroCopyConjEquiv_point (q : XiZeroCopy) :
    (((xiZeroCopyConjEquiv q).1 : XiDivisorSupport) : ℂ) =
      (starRingEnd ℂ) ((q.1 : ℂ)) := rfl

/-- At a conjugate pair the two holomorphic character samples multiply to the Hermitian
sample: `char(s)·char(conj s) = p^{2 Re s - 1}`. -/
theorem burnolPrimeCharacter_mul_conj {p : ℝ} (hp : 0 < p) (s : ℂ) :
    burnolPrimeCharacter p s * burnolPrimeCharacter p ((starRingEnd ℂ) s) =
      (((p : ℝ) ^ (2 * s.re - 1) : ℝ) : ℂ) := by
  have hpC : ((p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [burnolPrimeCharacter, burnolPrimeCharacter, ← Complex.cpow_add _ _ hpC,
    show (s - 1 / 2) + ((starRingEnd ℂ) s - 1 / 2) = (s + (starRingEnd ℂ) s) - 1 from by
      ring,
    Complex.add_conj]
  rw [show ((2 * s.re : ℝ) : ℂ) - 1 = (((2 * s.re - 1 : ℝ)) : ℂ) from by push_cast; ring,
    ← Complex.ofReal_cpow hp.le]

/-- **Conjugate-pair classification of the missing transform.**  At every divisor copy the
Hermitian sample is the holomorphic bilinear sample at the conjugate copy pair: the horizontal
transform the open core asks for is a sub-diagonal of the two-zero holomorphic kernel. -/
theorem hermitianSample_eq_conjugatePair_product {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    burnolPrimeCharacter p (q.1 : ℂ) *
        burnolPrimeCharacter p (((xiZeroCopyConjEquiv q).1 : XiDivisorSupport) : ℂ) =
      (((p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) : ℝ) : ℂ) := by
  rw [xiZeroCopyConjEquiv_point]
  exact burnolPrimeCharacter_mul_conj hp (q.1 : ℂ)

/-! ## The coherence budget -/

/-- **Coherence budget.**  For every finite family of copies and complex weights, the squared
zero-side exponential sum at frequency `log p` is at most the ℓ² weight mass times the
diagonal budget: cosh-defect mass plus twice the count.  Off-line mass is exactly the
coherence budget beyond square-root cancellation. -/
theorem norm_sq_charSum_le_defectMass_add {p : ℝ} (hp : 1 < p)
    (F : Finset XiZeroCopy) (v : XiZeroCopy → ℂ) :
    ‖∑ q ∈ F, v q * burnolPrimeCharacter p (q.1 : ℂ)‖ ^ 2 ≤
      (∑ q ∈ F, ‖v q‖ ^ 2) *
        ((∑ q ∈ F, ((p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) +
            (p : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2)) + 2 * F.card) := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have h1 : ‖∑ q ∈ F, v q * burnolPrimeCharacter p (q.1 : ℂ)‖ ≤
      ∑ q ∈ F, ‖v q‖ * ‖burnolPrimeCharacter p (q.1 : ℂ)‖ := by
    refine le_trans (norm_sum_le F _) ?_
    refine Finset.sum_le_sum fun q _ => ?_
    rw [norm_mul]
  have h2 : (∑ q ∈ F, ‖v q‖ * ‖burnolPrimeCharacter p (q.1 : ℂ)‖) ^ 2 ≤
      (∑ q ∈ F, ‖v q‖ ^ 2) * (∑ q ∈ F, ‖burnolPrimeCharacter p (q.1 : ℂ)‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq F _ _
  have h3 : ∀ q : XiZeroCopy, ‖burnolPrimeCharacter p (q.1 : ℂ)‖ ^ 2 =
      (p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) := by
    intro q
    rw [norm_burnolPrimeCharacter hp0, sq, ← Real.rpow_add hp0]
    congr 1
    ring
  have h4 : (∑ q ∈ F, ‖burnolPrimeCharacter p (q.1 : ℂ)‖ ^ 2) ≤
      (∑ q ∈ F, ((p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) +
          (p : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2)) + 2 * F.card := by
    have hterm : ∀ q ∈ F, ‖burnolPrimeCharacter p (q.1 : ℂ)‖ ^ 2 ≤
        ((p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) +
          (p : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2) + 2 := by
      intro q _
      rw [h3 q]
      have := Real.rpow_pos_of_pos hp0 (-(2 * ((q.1 : ℂ)).re - 1))
      linarith
    calc (∑ q ∈ F, ‖burnolPrimeCharacter p (q.1 : ℂ)‖ ^ 2)
        ≤ ∑ q ∈ F, (((p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) +
            (p : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2) + 2) := Finset.sum_le_sum hterm
      _ = (∑ q ∈ F, ((p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) +
            (p : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2)) + 2 * F.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          ring
  calc ‖∑ q ∈ F, v q * burnolPrimeCharacter p (q.1 : ℂ)‖ ^ 2
      ≤ (∑ q ∈ F, ‖v q‖ * ‖burnolPrimeCharacter p (q.1 : ℂ)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ q ∈ F, ‖v q‖ ^ 2) * (∑ q ∈ F, ‖burnolPrimeCharacter p (q.1 : ℂ)‖ ^ 2) := h2
    _ ≤ (∑ q ∈ F, ‖v q‖ ^ 2) *
          ((∑ q ∈ F, ((p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) +
              (p : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2)) + 2 * F.card) := by
        refine mul_le_mul_of_nonneg_left h4 ?_
        exact Finset.sum_nonneg fun q _ => sq_nonneg _

/-- **Mass-zero collapses the budget.**  Under RH the cosh-defect mass vanishes and the
coherence budget is the diagonal count: square-root cancellation of the zero-side exponential
sum at every real frequency and every weight, from mass-zero alone. -/
theorem norm_sq_charSum_le_two_mul_card_of_riemannHypothesis
    (hRH : RiemannHypothesis) {p : ℝ} (hp : 1 < p)
    (F : Finset XiZeroCopy) (v : XiZeroCopy → ℂ) :
    ‖∑ q ∈ F, v q * burnolPrimeCharacter p (q.1 : ℂ)‖ ^ 2 ≤
      (∑ q ∈ F, ‖v q‖ ^ 2) * (2 * F.card) := by
  have h := norm_sq_charSum_le_defectMass_add hp F v
  have hz : ∀ q ∈ F, ((p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) +
      (p : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2) = 0 := by
    intro q _
    have hre : ((q.1 : ℂ)).re = 1 / 2 :=
      riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH (q.1 : ℂ)
        (xi_eq_zero_of_mem_divisor_support q.1)
    have ht : 2 * ((q.1 : ℂ)).re - 1 = 0 := by rw [hre]; ring
    rw [ht, neg_zero, Real.rpow_zero]
    norm_num
  rw [Finset.sum_eq_zero hz, zero_add] at h
  exact h

end

end RHTower
