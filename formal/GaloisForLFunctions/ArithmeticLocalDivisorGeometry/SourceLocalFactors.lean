import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.LocalFactors
import GaloisForLFunctions.RHTower.XiSliceCoeffNearDoublePositivity
import GaloisForLFunctions.RHTower.XiSliceGaussianFiniteHeadPositivity

/-!
# Unnormalized real local factors of the Xi divisor

Critical copies give linear factors in squared horizontal displacement; upper spectral copies
and their mirrors give real quadratic factors. The resulting polynomial retains central zeros
and agrees exactly with the finite canonical-product head, without division by `XiC t`.
-/

open Polynomial Complex
open GaloisForLFunctions.HTGeometry
open RHTower

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- The real, monic local divisor polynomial, with every critical and paired multiplicity. -/
def localDivisorPolynomial (t : ℝ) (S : Finset XiZeroCopy) : ℝ[X] :=
  (∏ q ∈ sliceTruncCrit S, (X + C (((xiSpectralPoint q).re - t) ^ 2))) *
    ∏ q ∈ sliceTruncUp S, pairFactor ((xiSpectralPoint q).re - t) (xiSpectralPoint q).im

/-- The real quadratic is exactly the product of its two conjugate spectral factors. -/
theorem pairFactor_eval₂ (u δ : ℝ) (y : ℂ) :
    (pairFactor u δ).eval₂ (algebraMap ℝ ℂ) y =
      (y + ((u : ℂ) + (δ : ℂ) * I) ^ 2) *
        (y + ((u : ℂ) - (δ : ℂ) * I) ^ 2) := by
  simp only [pairFactor, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X]
  push_cast
  have hI4 : (I : ℂ) ^ 4 = 1 := by
    calc
      _ = (I ^ 2) ^ 2 := by ring
      _ = 1 := by rw [I_sq]; norm_num
  ring_nf
  simp only [hI4, I_sq]
  ring

/-- Exact evaluation at a complex squared displacement, including central zero factors. -/
theorem localDivisorPolynomial_eval₂ (t : ℝ) (S : Finset XiZeroCopy) (y : ℂ) :
    (localDivisorPolynomial t S).eval₂ (algebraMap ℝ ℂ) y =
      ∏ q ∈ sliceTrunc S, (y + (xiSpectralPoint q - t) ^ 2) := by
  rw [prod_sliceTrunc, localDivisorPolynomial, eval₂_mul, eval₂_finsetProd, eval₂_finsetProd]
  congr 1
  · refine Finset.prod_congr rfl fun q hq => ?_
    have him := (mem_sliceTruncCrit.mp hq).2
    change (xiSpectralPoint q).im = 0 at him
    have hz : xiSpectralPoint q - t = (((xiSpectralPoint q).re - t : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    simp [hz]
  · refine Finset.prod_congr rfl fun q _ => ?_
    rw [pairFactor_eval₂]
    have hz : xiSpectralPoint q - t =
        (((xiSpectralPoint q).re - t : ℝ) : ℂ) + ((xiSpectralPoint q).im : ℂ) * I := by
      apply Complex.ext <;> simp
    have hz' : xiSpectralPoint (xiZeroCopyLineConjEquiv q) - t =
        (((xiSpectralPoint q).re - t : ℝ) : ℂ) - ((xiSpectralPoint q).im : ℂ) * I := by
      rw [xiSpectralPoint_lineConj]
      apply Complex.ext <;> simp
    rw [hz, hz']

theorem mem_radiusHead_lineConj_iff (t R : ℝ) (q : XiZeroCopy) :
    xiZeroCopyLineConjEquiv q ∈ xiSliceGaussianRadiusHead t R ↔
      q ∈ xiSliceGaussianRadiusHead t R := by
  rw [mem_xiSliceGaussianRadiusHead, mem_xiSliceGaussianRadiusHead, xiSpectralPoint_lineConj]
  have hc : (starRingEnd ℂ) (t : ℂ) = t := by simp
  rw [← hc, ← map_sub, Complex.norm_conj, hc]

/-- A radius head is already closed under the exact multiplicity-copy pairing. -/
theorem sliceTrunc_radiusHead (t R : ℝ) :
    sliceTrunc (xiSliceGaussianRadiusHead t R) = xiSliceGaussianRadiusHead t R := by
  classical
  ext q
  simp only [sliceTrunc, Finset.mem_union, mem_sliceTruncCrit, mem_sliceTruncUp,
    Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ((⟨hq, _⟩ | ⟨hq, _⟩) | ⟨r, ⟨hr, _⟩, rfl⟩)
    · exact hq
    · exact hq
    · exact (mem_radiusHead_lineConj_iff t R r).mpr hr
  · intro hq
    rcases lt_trichotomy (xiSpectralPoint q).im 0 with hi | hi | hi
    · right
      refine ⟨xiZeroCopyLineConjEquiv.symm q, ⟨?_, ?_⟩, Equiv.apply_symm_apply _ _⟩
      · apply (mem_radiusHead_lineConj_iff t R (xiZeroCopyLineConjEquiv.symm q)).mp
        simpa only [Equiv.apply_symm_apply] using hq
      · change 0 < (xiSpectralPoint (xiZeroCopyLineConjEquiv.symm q)).im
        have h := im_xiSpectralPoint_lineConj (xiZeroCopyLineConjEquiv.symm q)
        rw [Equiv.apply_symm_apply] at h
        linarith
    · exact Or.inl (Or.inl ⟨hq, hi⟩)
    · exact Or.inl (Or.inr ⟨hq, hi⟩)

/-- The exact head retains its canonical normalization and the unnormalized real divisor. -/
theorem xiFiniteHead_eq_localDivisorPolynomial (t R : ℝ) (z : ℂ) :
    xiSliceGaussianFiniteHead t R z = xiSliceGaussianFiniteHeadScalar t R *
      (localDivisorPolynomial t (xiSliceGaussianRadiusHead t R)).eval₂ (algebraMap ℝ ℂ) (z ^ 2) := by
  rw [localDivisorPolynomial_eval₂, sliceTrunc_radiusHead]
  rfl

/-- The real normalization is strictly positive once the radius retains every central copy. -/
theorem exists_pos_xiFiniteHead_normalization (t : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, xiSliceGaussianFiniteHead t R z = (c : ℂ) *
      (localDivisorPolynomial t (xiSliceGaussianRadiusHead t R)).eval₂ (algebraMap ℝ ℂ) (z ^ 2) := by
  refine ⟨(xiSliceGaussianFiniteHeadScalar t R).re,
    xiSliceGaussianFiniteHeadScalar_re_pos t hR, ?_⟩
  intro z
  have hs : xiSliceGaussianFiniteHeadScalar t R =
      ((xiSliceGaussianFiniteHeadScalar t R).re : ℂ) :=
    Complex.ext rfl (xiSliceGaussianFiniteHeadScalar_im_eq_zero t R)
  rw [xiFiniteHead_eq_localDivisorPolynomial]
  exact congrArg (fun c : ℂ => c *
    (localDivisorPolynomial t (xiSliceGaussianRadiusHead t R)).eval₂ (algebraMap ℝ ℂ) (z ^ 2)) hs

/-- The exact canonical head as an even complex polynomial, including its scalar. -/
def sourceHeadPolynomial (t R : ℝ) : ℂ[X] :=
  C (xiSliceGaussianFiniteHeadScalar t R) *
    expand ℂ 2 ((localDivisorPolynomial t (xiSliceGaussianRadiusHead t R)).map (algebraMap ℝ ℂ))

theorem xiFiniteHead_eq_eval_sourceHeadPolynomial (t R : ℝ) :
    xiSliceGaussianFiniteHead t R = fun z => (sourceHeadPolynomial t R).eval z := by
  funext z
  simp only [sourceHeadPolynomial, eval_mul, eval_C, expand_eval, eval_map]
  exact xiFiniteHead_eq_localDivisorPolynomial t R z

/-- Each even Taylor coefficient is its unnormalized real divisor coefficient times the
canonical scalar. This remains valid at a multiple central zero. -/
theorem xiFiniteHead_even_taylor (t R : ℝ) (k : ℕ) :
    (((2 * k).factorial : ℂ))⁻¹ *
      iteratedDeriv (2 * k) (xiSliceGaussianFiniteHead t R) 0 =
    xiSliceGaussianFiniteHeadScalar t R *
      (((localDivisorPolynomial t (xiSliceGaussianRadiusHead t R)).coeff k : ℝ) : ℂ) := by
  rw [xiFiniteHead_eq_eval_sourceHeadPolynomial, factorial_inv_mul_iteratedDeriv_polynomial_eval]
  unfold sourceHeadPolynomial
  rw [coeff_C_mul, show 2 * k = k * 2 by omega,
    coeff_expand_mul (by norm_num), coeff_map]
  rfl

/-- Every odd Taylor coefficient vanishes by the exact squared-displacement factorization. -/
theorem xiFiniteHead_odd_taylor (t R : ℝ) (k : ℕ) :
    (((2 * k + 1).factorial : ℂ))⁻¹ *
      iteratedDeriv (2 * k + 1) (xiSliceGaussianFiniteHead t R) 0 = 0 := by
  rw [xiFiniteHead_eq_eval_sourceHeadPolynomial, factorial_inv_mul_iteratedDeriv_polynomial_eval]
  unfold sourceHeadPolynomial
  rw [coeff_C_mul, coeff_expand (by norm_num)]
  have hodd : ¬2 ∣ 2 * k + 1 := by rintro ⟨n, hn⟩; omega
  rw [if_neg hodd, mul_zero]

/-- Real-axis nonnegativity follows factor by factor and imposes no coefficient signs. -/
theorem localDivisorPolynomial_eval_nonneg (t : ℝ) (S : Finset XiZeroCopy) (x : ℝ) :
    0 ≤ (localDivisorPolynomial t S).eval (x ^ 2) := by
  rw [localDivisorPolynomial, eval_mul, eval_prod, eval_prod]
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro q hq
    simp only [eval_add, eval_X, eval_C]
    positivity
  · exact Finset.prod_nonneg fun q _ => pairFactor_eval_nonneg _ _ x

/-- Disjoint divisor copies multiply exactly, with no nonvanishing assumption on the center. -/
theorem localDivisorPolynomial_union (t : ℝ) {S T : Finset XiZeroCopy} (hST : Disjoint S T) :
    localDivisorPolynomial t (S ∪ T) = localDivisorPolynomial t S * localDivisorPolynomial t T := by
  classical
  have hc : sliceTruncCrit (S ∪ T) = sliceTruncCrit S ∪ sliceTruncCrit T := by
    ext q
    simp only [mem_sliceTruncCrit, Finset.mem_union, or_and_right]
  have hu : sliceTruncUp (S ∪ T) = sliceTruncUp S ∪ sliceTruncUp T := by
    ext q
    simp only [mem_sliceTruncUp, Finset.mem_union, or_and_right]
  have hcd : Disjoint (sliceTruncCrit S) (sliceTruncCrit T) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    exact Finset.disjoint_left.mp hST (mem_sliceTruncCrit.mp hq).1 (mem_sliceTruncCrit.mp hq').1
  have hud : Disjoint (sliceTruncUp S) (sliceTruncUp T) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    exact Finset.disjoint_left.mp hST (mem_sliceTruncUp.mp hq).1 (mem_sliceTruncUp.mp hq').1
  unfold localDivisorPolynomial
  rw [hc, hu, Finset.prod_union hcd, Finset.prod_union hud]
  ring

/-- Retained and removed copies form an unconditional exact transition, even at central zeros. -/
theorem localDivisorPolynomial_split (t : ℝ) (S T : Finset XiZeroCopy) :
    localDivisorPolynomial t S =
      localDivisorPolynomial t (S ∩ T) * localDivisorPolynomial t (S \ T) := by
  classical
  have heq : (S ∩ T) ∪ (S \ T) = S := by ext q; simp; tauto
  have hdisj : Disjoint (S ∩ T) (S \ T) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    exact (Finset.mem_sdiff.mp hq').2 (Finset.mem_inter.mp hq).2
  rw [← localDivisorPolynomial_union t hdisj, heq]

/-- Every transition coefficient retains the full convolution, including signed mixed terms. -/
theorem localDivisorPolynomial_split_coeff (t : ℝ) (S T : Finset XiZeroCopy) (n : ℕ) :
    (localDivisorPolynomial t S).coeff n =
      ∑ ij ∈ Finset.antidiagonal n,
        (localDivisorPolynomial t (S ∩ T)).coeff ij.1 *
          (localDivisorPolynomial t (S \ T)).coeff ij.2 := by
  rw [localDivisorPolynomial_split t S T, coeff_mul]

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry

#print axioms GaloisForLFunctions.ArithmeticLocalDivisorGeometry.exists_pos_xiFiniteHead_normalization
#print axioms GaloisForLFunctions.ArithmeticLocalDivisorGeometry.xiFiniteHead_even_taylor
#print axioms GaloisForLFunctions.ArithmeticLocalDivisorGeometry.xiFiniteHead_odd_taylor
#print axioms GaloisForLFunctions.ArithmeticLocalDivisorGeometry.localDivisorPolynomial_split_coeff
