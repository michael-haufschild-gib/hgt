import GaloisForLFunctions.RHTower.LocalHermitePositivity

/-!
# The monomial witness: the test vector that suppresses the on-line contribution

The localised Hermite form is nonnegative under the hypothesis, and a single negative value refutes
it. What was missing was a test vector making the on-line contribution small. Here it is.

**Take the monomial `P(x) = x^{2n+1}` of high odd degree, and anchor at the ordinate of the
suspected zero.** The test vector is then supported on the single index `2n`, and the Hermite form
collapses to one power sum,

  `Σ_{i,j} c_i c_j p_{i+j+2}(t) = p_{4n+2}(t)`.

Two facts make this the right choice.

*The sign is automatic.* At the ordinate of an off-line zero the resolvent of that zero and of its
functional-equation partner is **purely imaginary**, `±i/δ`, because the spectral point sits at
`γ ∓ iδ` and the base point is `γ`. A purely imaginary number raised to an exponent congruent to two
modulo four is a negative real, of size `δ^{-(4n+2)}`. So the off-line orbit contributes
`−2/δ^{4n+2}`, with no cancellation and no choice of coefficients required.

*The on-line contribution is suppressed geometrically.* Every other zero has resolvent of modulus at
most `1/δ'` for some `δ' > δ`, provided the suspected zero is strictly closer to the base point than
anything else — which is exactly the statement that it is closer to the critical line than to its
neighbours in ordinate. Raising to the power `4n+2` multiplies each such term by `(1/δ')^{4n}` while
the off-line term is multiplied by `(1/δ)^{4n}`, and `δ < δ'`. The ratio is `(δ/δ')^{4n} → 0`, so for
large `n` the negative term wins by any margin.

The conclusion is a genuine detection theorem: **an off-line zero that is isolated at the scale of
its own displacement is certified by a single evaluation of a single derivative of the logarithmic
derivative of `Ξ`.** The degree `n` is not a free parameter to be optimised — it only has to be large
enough that `(δ/δ')^{4n}` beats a fixed constant.

What this does not do is remove the isolation hypothesis. A zero at displacement `δ` whose ordinate
has another zero within `δ` is not separated by this test vector, and that regime is the local
clustering that has blocked this field before. The gain is that the obstruction is now confined to
clustered configurations, and the non-clustered ones are decided.
-/

open Complex

namespace RHTower

noncomputable section

/-- The monomial test vector: all the weight on a single index. -/
def monomialTestVector (n : ℕ) : ℕ → ℝ := fun i => if i = 2 * n then 1 else 0

/-- With the monomial test vector the localised Hermite form collapses to one power sum. -/
theorem hermiteForm_monomialTestVector (t : ℝ) (n : ℕ) :
    ∑ i ∈ ({2 * n} : Finset ℕ), ∑ j ∈ ({2 * n} : Finset ℕ),
        ((monomialTestVector n i * monomialTestVector n j : ℝ) : ℂ)
          * spectralPowerSum t (i + j + 2)
      = spectralPowerSum t (4 * n + 2) := by
  rw [Finset.sum_singleton, Finset.sum_singleton, show 2 * n + 2 * n + 2 = 4 * n + 2 by ring]
  simp [monomialTestVector]

/-- **The sign law.** A purely imaginary number raised to an exponent congruent to two modulo four
is a negative real. -/
theorem pow_of_imaginary {u : ℂ} {δ : ℝ} (hδ : δ ≠ 0)
    (hu : u = Complex.I / (δ : ℂ) ∨ u = -(Complex.I / (δ : ℂ))) (n : ℕ) :
    u ^ (4 * n + 2) = -(((δ : ℂ)) ^ (4 * n + 2))⁻¹ := by
  have hbase : (Complex.I / (δ : ℂ)) ^ (2 : ℕ) = -(((δ : ℂ)) ^ (2 : ℕ))⁻¹ := by
    rw [div_pow, Complex.I_sq, neg_div, one_div]
  have hu2 : u ^ (2 : ℕ) = -(((δ : ℂ)) ^ (2 : ℕ))⁻¹ := by
    rcases hu with h | h
    · rw [h, hbase]
    · rw [h, neg_pow, hbase]
      simp
  rw [show 4 * n + 2 = 2 * (2 * n + 1) by ring, pow_mul, hu2,
    Odd.neg_pow (odd_two_mul_add_one n), inv_pow, ← pow_mul]

/-- **The base point.** At the ordinate of a zero, the resolvent of that zero is purely imaginary,
of modulus the reciprocal of its displacement. -/
theorem spectralResolvent_at_own_ordinate (ρ : XiDivisorSupport) (q : XiZeroCopy) (hq : q.1 = ρ) :
    spectralResolvent ((ρ : ℂ).im) q
      = -(Complex.I / ((((ρ : ℂ).re - 1 / 2 : ℝ)) : ℂ)) := by
  have hz : ((((ρ : ℂ).im : ℝ)) : ℂ) - xiSpectralPoint q
      = Complex.I * ((((ρ : ℂ).re - 1 / 2 : ℝ)) : ℂ) := by
    rw [xiSpectralPoint_eq_support, hq]
    refine Complex.ext ?_ ?_ <;> simp
  rw [spectralResolvent, hz]
  rw [mul_comm, mul_inv, inv_I]
  ring

/-- **The monomial witness.** If at the base point a nonempty finite set of copies has purely
imaginary resolvent of modulus `1/δ`, and every other copy has resolvent of modulus at most `1/δ'`
with `δ < δ'`, then a monomial test vector of high enough odd degree makes the localised Hermite
form negative. -/
theorem exists_monomial_hermite_witness {t : ℝ} (ht : OffSpectralDivisor t)
    {A : Finset XiZeroCopy} (hA : A.Nonempty) {δ δ' : ℝ} (hδ : 0 < δ) (hδδ' : δ < δ')
    (hin : ∀ q ∈ A, spectralResolvent t q = Complex.I / (δ : ℂ) ∨
      spectralResolvent t q = -(Complex.I / (δ : ℂ)))
    (hout : ∀ q ∉ A, ‖spectralResolvent t q‖ ≤ 1 / δ') :
    ∃ n : ℕ, (spectralPowerSum t (4 * n + 2)).re < 0 := by
  classical
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hδ'0 : 0 < δ' := hδ.trans hδδ'
  have hSsum : Summable (fun q : XiZeroCopy => ‖spectralResolvent t q‖ ^ (2 : ℕ)) :=
    summable_norm_sq_spectralResolvent ht
  have hS0 : (0 : ℝ) ≤ ∑' q : XiZeroCopy, ‖spectralResolvent t q‖ ^ (2 : ℕ) :=
    tsum_nonneg fun q => by positivity
  have hcard : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hratio0 : (0 : ℝ) ≤ δ / δ' := by positivity
  have hratio : δ / δ' < 1 := (div_lt_one hδ'0).mpr hδδ'
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < (A.card : ℝ)
      / ((∑' q : XiZeroCopy, ‖spectralResolvent t q‖ ^ (2 : ℕ)) * δ ^ (2 : ℕ) + 1) by positivity)
    hratio
  refine ⟨n, ?_⟩
  -- the norms on the exceptional set
  have hnormA : ∀ q ∈ A, ‖spectralResolvent t q‖ ^ (2 : ℕ) = (δ ^ (2 : ℕ))⁻¹ := by
    intro q hq
    have : ‖spectralResolvent t q‖ = 1 / δ := by
      rcases hin q hq with h | h <;> rw [h] <;>
        simp [Complex.norm_div, Complex.norm_I, abs_of_pos hδ]
    rw [this]
    field_simp
  -- pointwise majorant
  have hmaj : ∀ q : XiZeroCopy, (spectralResolvent t q ^ (4 * n + 2)).re
      ≤ (1 / δ') ^ (4 * n) * ‖spectralResolvent t q‖ ^ (2 : ℕ)
        + (if q ∈ A then
            -((δ ^ (4 * n + 2))⁻¹) - (1 / δ') ^ (4 * n) * (δ ^ (2 : ℕ))⁻¹ else 0) := by
    intro q
    by_cases hq : q ∈ A
    · rw [if_pos hq, hnormA q hq, pow_of_imaginary hδ0 (hin q hq) n]
      have hre : (-(((δ : ℂ)) ^ (4 * n + 2))⁻¹).re = -((δ ^ (4 * n + 2))⁻¹) := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_neg,
          Complex.ofReal_re]
      rw [hre]
      have heq : (1 / δ') ^ (4 * n) * (δ ^ (2 : ℕ))⁻¹
          + (-((δ ^ (4 * n + 2))⁻¹) - (1 / δ') ^ (4 * n) * (δ ^ (2 : ℕ))⁻¹)
          = -((δ ^ (4 * n + 2))⁻¹) := by ring
      rw [heq]
    · rw [if_neg hq, add_zero]
      calc (spectralResolvent t q ^ (4 * n + 2)).re
          ≤ ‖spectralResolvent t q ^ (4 * n + 2)‖ := Complex.re_le_norm _
        _ = ‖spectralResolvent t q‖ ^ (4 * n) * ‖spectralResolvent t q‖ ^ (2 : ℕ) := by
            rw [norm_pow, ← pow_add]
        _ ≤ (1 / δ') ^ (4 * n) * ‖spectralResolvent t q‖ ^ (2 : ℕ) := by
            gcongr
            exact hout q hq
  -- summability
  have hL : Summable (fun q : XiZeroCopy => (spectralResolvent t q ^ (4 * n + 2)).re) :=
    (Complex.hasSum_re (summable_spectralResolvent_pow ht (by omega)).hasSum).summable
  have hE : Summable (fun q : XiZeroCopy => (if q ∈ A then
      -((δ ^ (4 * n + 2))⁻¹) - (1 / δ') ^ (4 * n) * (δ ^ (2 : ℕ))⁻¹ else 0)) :=
    summable_of_ne_finset_zero (s := A) (fun q hq => if_neg hq)
  have hR : Summable (fun q : XiZeroCopy => (1 / δ') ^ (4 * n) * ‖spectralResolvent t q‖ ^ (2 : ℕ)
      + (if q ∈ A then
          -((δ ^ (4 * n + 2))⁻¹) - (1 / δ') ^ (4 * n) * (δ ^ (2 : ℕ))⁻¹ else 0)) :=
    (hSsum.mul_left _).add hE
  -- compare
  have hcmp := Summable.tsum_le_tsum hmaj hL hR
  rw [re_tsum (summable_spectralResolvent_pow ht (by omega))] at *
  rw [Summable.tsum_add (hSsum.mul_left _) hE, tsum_mul_left,
    tsum_eq_sum (s := A) (fun q hq => if_neg hq), Finset.sum_congr rfl
      (fun q hq => if_pos hq), Finset.sum_const, nsmul_eq_mul] at hcmp
  -- the final numeric estimate
  have hkey : (1 / δ') ^ (4 * n) * (∑' q : XiZeroCopy, ‖spectralResolvent t q‖ ^ (2 : ℕ))
      < (A.card : ℝ) * (δ ^ (4 * n + 2))⁻¹ := by
    rw [← sub_pos]
    have hpow : (δ / δ') ^ (4 * n) ≤ (δ / δ') ^ n :=
      pow_le_pow_of_le_one hratio0 hratio.le (by omega)
    have hlt : (δ / δ') ^ (4 * n)
        < (A.card : ℝ)
          / ((∑' q : XiZeroCopy, ‖spectralResolvent t q‖ ^ (2 : ℕ)) * δ ^ (2 : ℕ) + 1) :=
      lt_of_le_of_lt hpow hn
    have hid : (1 / δ') ^ (4 * n) * δ ^ (4 * n + 2) = δ ^ (2 : ℕ) * (δ / δ') ^ (4 * n) := by
      field_simp
      ring
    have hδpow : (0 : ℝ) < δ ^ (4 * n + 2) := by positivity
    rw [lt_div_iff₀ (by positivity)] at hlt
    have hstep : (1 / δ') ^ (4 * n)
        * (∑' q : XiZeroCopy, ‖spectralResolvent t q‖ ^ (2 : ℕ)) * δ ^ (4 * n + 2)
        < (A.card : ℝ) := by
      calc (1 / δ') ^ (4 * n) * (∑' q : XiZeroCopy, ‖spectralResolvent t q‖ ^ (2 : ℕ))
            * δ ^ (4 * n + 2)
          = (∑' q : XiZeroCopy, ‖spectralResolvent t q‖ ^ (2 : ℕ)) * δ ^ (2 : ℕ)
              * (δ / δ') ^ (4 * n) := by
            rw [mul_comm ((1 / δ') ^ (4 * n)) _, mul_assoc, hid]; ring
        _ ≤ (∑' q : XiZeroCopy, ‖spectralResolvent t q‖ ^ (2 : ℕ)) * δ ^ (2 : ℕ)
              * (δ / δ') ^ (4 * n) + (δ / δ') ^ (4 * n) := by
            have : (0 : ℝ) ≤ (δ / δ') ^ (4 * n) := by positivity
            linarith
        _ = ((∑' q : XiZeroCopy, ‖spectralResolvent t q‖ ^ (2 : ℕ)) * δ ^ (2 : ℕ) + 1)
              * (δ / δ') ^ (4 * n) := by ring
        _ < (A.card : ℝ) := by linarith [hlt]
    nlinarith [hδpow, inv_pos.mpr hδpow]
  have hEval : (A.card : ℝ) * (-((δ ^ (4 * n + 2))⁻¹)
      - (1 / δ') ^ (4 * n) * (δ ^ (2 : ℕ))⁻¹) ≤ -((A.card : ℝ) * (δ ^ (4 * n + 2))⁻¹) := by
    have : (0 : ℝ) ≤ (A.card : ℝ) * ((1 / δ') ^ (4 * n) * (δ ^ (2 : ℕ))⁻¹) := by positivity
    nlinarith
  linarith

/-- **Refutation by a single monomial evaluation.** -/
theorem not_riemannHypothesis_of_monomial_witness {t : ℝ} (ht : OffSpectralDivisor t)
    {A : Finset XiZeroCopy} (hA : A.Nonempty) {δ δ' : ℝ} (hδ : 0 < δ) (hδδ' : δ < δ')
    (hin : ∀ q ∈ A, spectralResolvent t q = Complex.I / (δ : ℂ) ∨
      spectralResolvent t q = -(Complex.I / (δ : ℂ)))
    (hout : ∀ q ∉ A, ‖spectralResolvent t q‖ ≤ 1 / δ') :
    ¬ RiemannHypothesis := by
  obtain ⟨n, hn⟩ := exists_monomial_hermite_witness ht hA hδ hδδ' hin hout
  refine not_riemannHypothesis_of_hermiteForm_re_neg ht ({2 * n} : Finset ℕ)
    (monomialTestVector n) ?_
  rw [hermiteForm_monomialTestVector]
  exact hn

end

end RHTower
