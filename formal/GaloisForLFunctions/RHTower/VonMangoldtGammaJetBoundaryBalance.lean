import GaloisForLFunctions.RHTower.VonMangoldtGammaAffineBoundaryBalance

/-!
# Arbitrary-order two-boundary jet balance

The affine two-boundary residual cancels the two boundary values but gains only two extra inverse
powers of the prime-log rate.  That is insufficient for unbounded Gamma-jet depth.  The source
constraint itself supplies the canonical order-growing replacement.

At boundary radius `a`, order `k`, spectral character `w`, and Cauchy rate `lambda`, use the monic
two-boundary divisor

`P_{k,a}(w) = (w^2-a^2)^k = (w-a)^k (w+a)^k`.

Normalize it at the Cauchy pole `w=-lambda` and retain the original Cauchy denominator.  The
resulting cell is

`((w^2-a^2)/(lambda^2-a^2))^k / (w+lambda)`.

Thus the cell has multiplicity `k` at both boundary characters, its regularized pole coefficient
is exactly one, order one is the affine balance, and every finite packet is a literal prefix of a
single cutoff-independent source packet.  Choosing the order to grow with Gamma depth removes the
fixed-order decay obstruction algebraically.  Cofinal summability and identification with the
completed prime--Gamma moment germ remain separate analytic theorems.
-/

open scoped ComplexOrder

namespace RHTower

noncomputable section

open Polynomial

/-- Monic divisor encoding order-`k` vanishing at both boundary characters `+a` and `-a`. -/
def twoBoundaryCauchyJetPolynomial (k : ℕ) (a : ℂ) : Polynomial ℂ :=
  (X ^ 2 - C (a ^ 2)) ^ k

/-- Exact factorization exhibiting multiplicity `k` at both boundary characters. -/
theorem twoBoundaryCauchyJetPolynomial_factor (k : ℕ) (a : ℂ) :
    twoBoundaryCauchyJetPolynomial k a =
      (X - C a) ^ k * (X + C a) ^ k := by
  rw [twoBoundaryCauchyJetPolynomial]
  have hquad : (X ^ 2 - C (a ^ 2) : Polynomial ℂ) =
      (X - C a) * (X + C a) := by
    rw [map_pow]
    ring
  rw [hquad, mul_pow]

/-- Evaluation of the two-boundary divisor. -/
theorem twoBoundaryCauchyJetPolynomial_eval (k : ℕ) (a w : ℂ) :
    (twoBoundaryCauchyJetPolynomial k a).eval w = (w ^ 2 - a ^ 2) ^ k := by
  simp [twoBoundaryCauchyJetPolynomial]

theorem twoBoundaryCauchyJetPolynomial_monic (k : ℕ) (a : ℂ) :
    (twoBoundaryCauchyJetPolynomial k a).Monic := by
  rw [twoBoundaryCauchyJetPolynomial_factor]
  apply Polynomial.Monic.mul
  · exact (monic_X_sub_C a).pow k
  · simpa [sub_neg_eq_add] using (monic_X_sub_C (-a)).pow k

theorem twoBoundaryCauchyJetPolynomial_natDegree (k : ℕ) (a : ℂ) :
    (twoBoundaryCauchyJetPolynomial k a).natDegree = 2 * k := by
  have hplusMonic : (X - C a : Polynomial ℂ).Monic := monic_X_sub_C a
  have hminusMonic : (X + C a : Polynomial ℂ).Monic := by
    simpa [sub_neg_eq_add] using monic_X_sub_C (-a)
  have hplusDegree : (X - C a : Polynomial ℂ).natDegree = 1 :=
    natDegree_X_sub_C a
  have hminusDegree : (X + C a : Polynomial ℂ).natDegree = 1 := by
    simpa [sub_neg_eq_add] using natDegree_X_sub_C (-a)
  rw [twoBoundaryCauchyJetPolynomial_factor]
  rw [(hplusMonic.pow k).natDegree_mul (hminusMonic.pow k)]
  rw [hplusMonic.natDegree_pow, hminusMonic.natDegree_pow,
    hplusDegree, hminusDegree]
  omega

/-- Constraint uniqueness.  At nonzero boundary radius, this is the unique monic polynomial of
degree at most `2*k` having multiplicity at least `k` at both boundary characters. -/
theorem twoBoundaryCauchyJetPolynomial_unique
    (k : ℕ) {a : ℂ} (ha : a ≠ 0) (Q : Polynomial ℂ)
    (hQ : Q.Monic) (hdegree : Q.natDegree ≤ 2 * k)
    (hplus : (X - C a) ^ k ∣ Q)
    (hminus : (X + C a) ^ k ∣ Q) :
    Q = twoBoundaryCauchyJetPolynomial k a := by
  have hne : a ≠ -a := by
    intro h
    apply ha
    linear_combination h / 2
  have hcop : IsCoprime ((X - C a) ^ k) ((X + C a) ^ k) := by
    have hbase : IsCoprime (X - C a) (X - C (-a)) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hne).isUnit
    simpa [sub_neg_eq_add] using hbase.pow
  have hdvd : twoBoundaryCauchyJetPolynomial k a ∣ Q := by
    rw [twoBoundaryCauchyJetPolynomial_factor]
    exact hcop.mul_dvd hplus hminus
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (twoBoundaryCauchyJetPolynomial_monic k a) hQ hdvd
  simpa [twoBoundaryCauchyJetPolynomial_natDegree] using hdegree

/-- Boundary-divisor normalizer.  Its value at the Cauchy pole is one whenever the two boundary
poles are absent. -/
def twoBoundaryCauchyJetNormalizer (k : ℕ) (a w lambda : ℂ) : ℂ :=
  ((w ^ 2 - a ^ 2) / (lambda ^ 2 - a ^ 2)) ^ k

/-- The normalizer is precisely evaluation of the boundary divisor divided by its evaluation at
the Cauchy pole. -/
theorem twoBoundaryCauchyJetNormalizer_eq_polynomial_ratio
    (k : ℕ) (a w lambda : ℂ) :
    twoBoundaryCauchyJetNormalizer k a w lambda =
      (twoBoundaryCauchyJetPolynomial k a).eval w /
        (twoBoundaryCauchyJetPolynomial k a).eval (-lambda) := by
  rw [twoBoundaryCauchyJetNormalizer, twoBoundaryCauchyJetPolynomial_eval,
    twoBoundaryCauchyJetPolynomial_eval, div_pow]
  congr 2
  ring

/-- Source-pole normalization: after the Cauchy pole is regularized, its coefficient remains one.
This rules out inserting an arbitrary scalar damping into the boundary cancellation. -/
theorem twoBoundaryCauchyJetNormalizer_at_pole
    (k : ℕ) {a lambda : ℂ} (hboundary : lambda ^ 2 - a ^ 2 ≠ 0) :
    twoBoundaryCauchyJetNormalizer k a (-lambda) lambda = 1 := by
  simp [twoBoundaryCauchyJetNormalizer, hboundary]

/-- Cauchy cell with arbitrary-order two-boundary jet cancellation. -/
def twoBoundaryCauchyJetResidual (k : ℕ) (a w lambda : ℂ) : ℂ :=
  twoBoundaryCauchyJetNormalizer k a w lambda / (w + lambda)

/-- Order zero recovers the unbalanced Cauchy cell. -/
@[simp] theorem twoBoundaryCauchyJetResidual_zero (a w lambda : ℂ) :
    twoBoundaryCauchyJetResidual 0 a w lambda = 1 / (w + lambda) := by
  simp [twoBoundaryCauchyJetResidual, twoBoundaryCauchyJetNormalizer]

/-- Increasing the jet order multiplies by the uniquely normalized quadratic boundary divisor. -/
theorem twoBoundaryCauchyJetResidual_succ (k : ℕ) (a w lambda : ℂ) :
    twoBoundaryCauchyJetResidual (k + 1) a w lambda =
      twoBoundaryCauchyJetResidual k a w lambda *
        ((w ^ 2 - a ^ 2) / (lambda ^ 2 - a ^ 2)) := by
  simp only [twoBoundaryCauchyJetResidual, twoBoundaryCauchyJetNormalizer, pow_succ]
  ring

/-- Every positive jet order vanishes at the positive boundary character. -/
@[simp] theorem twoBoundaryCauchyJetResidual_succ_plus
    (k : ℕ) (a lambda : ℂ) :
    twoBoundaryCauchyJetResidual (k + 1) a a lambda = 0 := by
  simp [twoBoundaryCauchyJetResidual, twoBoundaryCauchyJetNormalizer]

/-- Every positive jet order vanishes at the negative boundary character. -/
@[simp] theorem twoBoundaryCauchyJetResidual_succ_minus
    (k : ℕ) (a lambda : ℂ) :
    twoBoundaryCauchyJetResidual (k + 1) a (-a) lambda = 0 := by
  simp [twoBoundaryCauchyJetResidual, twoBoundaryCauchyJetNormalizer]

/-- Jet order one is exactly the previously forced affine two-boundary residual. -/
theorem twoBoundaryCauchyJetResidual_one_eq_affine
    {a w lambda : ℂ} (ha : a ≠ 0)
    (hw : w + lambda ≠ 0) (hp : a + lambda ≠ 0)
    (hm : -a + lambda ≠ 0) :
    twoBoundaryCauchyJetResidual 1 a w lambda =
      twoBoundaryCauchyAffineResidual a w lambda := by
  rw [twoBoundaryCauchyAffineResidual_eq ha hw hp hm]
  simp [twoBoundaryCauchyJetResidual, twoBoundaryCauchyJetNormalizer]
  have hfactor : lambda ^ 2 - a ^ 2 = (a + lambda) * (-a + lambda) := by ring
  rw [hfactor]
  field_simp

/-- Arbitrary-order jet-balanced all-depth source feature. -/
def finiteExponentialAllDepthJetBalancedCauchyFeature
    {P : Type*} (weight rate : P → ℝ) (N : ℕ) (i : Fin N)
    (k : ℕ) (a w : ℂ) (p : P) : ℂ :=
  (Real.sqrt (weight p) * rate p ^ (i : ℕ) *
      expNegOrientedRemainder (N - (i : ℕ)) (rate p) : ℝ) *
    twoBoundaryCauchyJetResidual k a w (rate p : ℂ)

/-- Order zero is the original all-depth Cauchy source feature. -/
theorem finiteExponentialAllDepthJetBalancedCauchyFeature_zero
    {P : Type*} (weight rate : P → ℝ) (N : ℕ) (i : Fin N)
    (a w : ℂ) (p : P) :
    finiteExponentialAllDepthJetBalancedCauchyFeature
        weight rate N i 0 a w p =
      finiteExponentialAllDepthCauchyFeature weight rate N i w p := by
  rw [finiteExponentialAllDepthJetBalancedCauchyFeature,
    twoBoundaryCauchyJetResidual_zero,
    finiteExponentialAllDepthCauchyFeature]
  ring

/-- Order one is the affine-balanced source feature. -/
theorem finiteExponentialAllDepthJetBalancedCauchyFeature_one_eq_affine
    {P : Type*} (weight rate : P → ℝ) (N : ℕ) (i : Fin N)
    {a w : ℂ} (p : P) (ha : a ≠ 0)
    (hw : w + (rate p : ℂ) ≠ 0) (hp : a + (rate p : ℂ) ≠ 0)
    (hm : -a + (rate p : ℂ) ≠ 0) :
    finiteExponentialAllDepthJetBalancedCauchyFeature
        weight rate N i 1 a w p =
      finiteExponentialAllDepthAffineBalancedCauchyFeature
        weight rate N i a w p := by
  rw [finiteExponentialAllDepthJetBalancedCauchyFeature,
    finiteExponentialAllDepthAffineBalancedCauchyFeature_eq_residual,
    twoBoundaryCauchyJetResidual_one_eq_affine ha hw hp hm]

@[simp] theorem finiteExponentialAllDepthJetBalancedCauchyFeature_succ_plus_eq_zero
    {P : Type*} (weight rate : P → ℝ) (N : ℕ) (i : Fin N)
    (k : ℕ) (a : ℂ) (p : P) :
    finiteExponentialAllDepthJetBalancedCauchyFeature
        weight rate N i (k + 1) a a p = 0 := by
  rw [finiteExponentialAllDepthJetBalancedCauchyFeature,
    twoBoundaryCauchyJetResidual_succ_plus, mul_zero]

@[simp] theorem finiteExponentialAllDepthJetBalancedCauchyFeature_succ_minus_eq_zero
    {P : Type*} (weight rate : P → ℝ) (N : ℕ) (i : Fin N)
    (k : ℕ) (a : ℂ) (p : P) :
    finiteExponentialAllDepthJetBalancedCauchyFeature
        weight rate N i (k + 1) a (-a) p = 0 := by
  rw [finiteExponentialAllDepthJetBalancedCauchyFeature,
    twoBoundaryCauchyJetResidual_succ_minus, mul_zero]

/-- Actual von Mangoldt specialization at boundary characters `±1/2`. -/
def finiteVonMangoldtAllDepthJetBalancedCauchyFeature
    (N : ℕ) (i : Fin N) (k : ℕ) (w : ℂ) (n : ℕ) : ℂ :=
  finiteExponentialAllDepthJetBalancedCauchyFeature
    finiteVonMangoldtRealWeight (fun n : ℕ => Real.log n)
    N i k (1 / 2) w n

/-- Finite prefix of the cutoff-independent order-`k` two-boundary jet packet. -/
def finiteVonMangoldtAllDepthJetBalancedCauchyVector
    (M N k : ℕ) (w : ℂ) : EuclideanSpace ℂ (Fin M × Fin N) :=
  WithLp.toLp 2 fun pi =>
    star (finiteVonMangoldtAllDepthJetBalancedCauchyFeature
      N pi.2 k w ((pi.1 : ℕ) + 2))

theorem finiteVonMangoldtAllDepthJetBalancedCauchyVector_apply
    (M N k : ℕ) (w : ℂ) (pi : Fin M × Fin N) :
    WithLp.ofLp (finiteVonMangoldtAllDepthJetBalancedCauchyVector M N k w) pi =
      star (finiteVonMangoldtAllDepthJetBalancedCauchyFeature
        N pi.2 k w ((pi.1 : ℕ) + 2)) := by
  rfl

@[simp] theorem finiteVonMangoldtAllDepthJetBalancedCauchyVector_succ_plus_eq_zero
    (M N k : ℕ) :
    finiteVonMangoldtAllDepthJetBalancedCauchyVector M N (k + 1) (1 / 2) = 0 := by
  apply WithLp.ofLp_injective 2
  funext pi
  simp only [finiteVonMangoldtAllDepthJetBalancedCauchyVector, WithLp.ofLp_toLp]
  rw [finiteVonMangoldtAllDepthJetBalancedCauchyFeature,
    finiteExponentialAllDepthJetBalancedCauchyFeature_succ_plus_eq_zero]
  simp

@[simp] theorem finiteVonMangoldtAllDepthJetBalancedCauchyVector_succ_minus_eq_zero
    (M N k : ℕ) :
    finiteVonMangoldtAllDepthJetBalancedCauchyVector M N (k + 1) (-1 / 2) = 0 := by
  apply WithLp.ofLp_injective 2
  funext pi
  simp only [finiteVonMangoldtAllDepthJetBalancedCauchyVector, WithLp.ofLp_toLp]
  have hminus : (-1 / 2 : ℂ) = -(1 / 2 : ℂ) := by ring
  rw [hminus, finiteVonMangoldtAllDepthJetBalancedCauchyFeature,
    finiteExponentialAllDepthJetBalancedCauchyFeature_succ_minus_eq_zero]
  simp

/-- Prefix compatibility survives at every boundary-jet order. -/
theorem finiteVonMangoldtAllDepthJetBalancedCauchyVector_prefix
    {M M' : ℕ} (hMM' : M ≤ M') (N k : ℕ) (w : ℂ)
    (p : Fin M) (i : Fin N) :
    WithLp.ofLp (finiteVonMangoldtAllDepthJetBalancedCauchyVector M' N k w)
        (Fin.castLE hMM' p, i) =
      WithLp.ofLp (finiteVonMangoldtAllDepthJetBalancedCauchyVector M N k w) (p, i) := by
  simp only [finiteVonMangoldtAllDepthJetBalancedCauchyVector_apply]
  rfl

/-- Positive finite Gram at arbitrary boundary-jet order. -/
def finiteVonMangoldtAllDepthJetBalancedCauchyGram
    (M N k : ℕ) {K : ℕ} (w : Fin K → ℂ) : Matrix (Fin K) (Fin K) ℂ :=
  Matrix.gram ℂ
    (fun b => finiteVonMangoldtAllDepthJetBalancedCauchyVector M N k (w b))

theorem finiteVonMangoldtAllDepthJetBalancedCauchyGram_posSemidef
    (M N k : ℕ) {K : ℕ} (w : Fin K → ℂ) :
    (finiteVonMangoldtAllDepthJetBalancedCauchyGram M N k w).PosSemidef :=
  Matrix.posSemidef_gram ℂ _

/-- The canonical unbounded-depth packet matches boundary-jet order `N` to Gamma depth `N`. -/
def finiteVonMangoldtAllDepthOrderGrowingCauchyVector
    (M N : ℕ) (w : ℂ) : EuclideanSpace ℂ (Fin M × Fin N) :=
  finiteVonMangoldtAllDepthJetBalancedCauchyVector M N N w

theorem finiteVonMangoldtAllDepthOrderGrowingCauchyVector_prefix
    {M M' : ℕ} (hMM' : M ≤ M') (N : ℕ) (w : ℂ)
    (p : Fin M) (i : Fin N) :
    WithLp.ofLp (finiteVonMangoldtAllDepthOrderGrowingCauchyVector M' N w)
        (Fin.castLE hMM' p, i) =
      WithLp.ofLp (finiteVonMangoldtAllDepthOrderGrowingCauchyVector M N w) (p, i) := by
  exact finiteVonMangoldtAllDepthJetBalancedCauchyVector_prefix hMM' N N w p i

@[simp] theorem finiteVonMangoldtAllDepthOrderGrowingCauchyVector_plus_eq_zero
    (M N : ℕ) :
    finiteVonMangoldtAllDepthOrderGrowingCauchyVector M N (1 / 2) = 0 := by
  rcases N with _ | N
  · exact Subsingleton.elim _ _
  · exact finiteVonMangoldtAllDepthJetBalancedCauchyVector_succ_plus_eq_zero M (N + 1) N

@[simp] theorem finiteVonMangoldtAllDepthOrderGrowingCauchyVector_minus_eq_zero
    (M N : ℕ) :
    finiteVonMangoldtAllDepthOrderGrowingCauchyVector M N (-1 / 2) = 0 := by
  rcases N with _ | N
  · exact Subsingleton.elim _ _
  · exact finiteVonMangoldtAllDepthJetBalancedCauchyVector_succ_minus_eq_zero M (N + 1) N

/-- Positive finite Gram of the concrete order-growing packet. -/
def finiteVonMangoldtAllDepthOrderGrowingCauchyGram
    (M N : ℕ) {K : ℕ} (w : Fin K → ℂ) : Matrix (Fin K) (Fin K) ℂ :=
  Matrix.gram ℂ
    (fun b => finiteVonMangoldtAllDepthOrderGrowingCauchyVector M N (w b))

theorem finiteVonMangoldtAllDepthOrderGrowingCauchyGram_posSemidef
    (M N : ℕ) {K : ℕ} (w : Fin K → ℂ) :
    (finiteVonMangoldtAllDepthOrderGrowingCauchyGram M N w).PosSemidef :=
  Matrix.posSemidef_gram ℂ _

end


end RHTower
