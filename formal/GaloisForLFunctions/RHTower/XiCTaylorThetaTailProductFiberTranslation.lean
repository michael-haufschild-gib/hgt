import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslation
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticTranslate

/-!
# Product-fibre cancellation of the finite sine translation channel

Positive square-index pairs with fixed product are closed under divisor reflection
`(m,n) ↔ (n,m)`.  In logarithmic coordinates this negates the centered displacement

`δ(m,n) = (log m - log n) / 2`.

The finite sine section is exactly odd in this displacement.  Therefore its whole fixed-product
packet cancels algebraically.  Summing the exact finite cosine translation law over a product
fibre leaves a pure cosine packet and only the explicit truncation top edge.  This isolates the
remaining finite edge without estimating the sine channel or invoking any Xi divisor data.
-/

open Finset Polynomial Complex

namespace RHTower

noncomputable section

/-- A swap-closed finite packet of polynomial values of opposite sign sums to zero. -/
private theorem polynomial_sum_eq_zero_of_swap_neg
    (s : Finset (ℕ × ℕ)) (F : (ℕ × ℕ) → Polynomial ℂ)
    (hmem : ∀ q, q ∈ s → q.swap ∈ s)
    (hneg : ∀ q, q ∈ s → F q.swap = -F q) :
    ∑ q ∈ s, F q = 0 := by
  have hswap : (∑ q ∈ s, F q) = ∑ q ∈ s, F q.swap := by
    refine Finset.sum_bij' (fun q _ => q.swap) (fun q _ => q.swap)
      hmem hmem ?_ ?_ ?_
    · intro q _hq
      exact Prod.swap_swap q
    · intro q _hq
      exact Prod.swap_swap q
    · intro q _hq
      rw [Prod.swap_swap]
  have hnegSum : (∑ q ∈ s, F q.swap) = -(∑ q ∈ s, F q) := by
    calc
      (∑ q ∈ s, F q.swap) = ∑ q ∈ s, -F q := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hneg q hq
      _ = -(∑ q ∈ s, F q) := by
        rw [Finset.sum_neg_distrib]
  have hself : (∑ q ∈ s, F q) = -(∑ q ∈ s, F q) :=
    hswap.trans hnegSum
  linear_combination (1 / 2 : ℂ) * hself

/-- Zero-based positive factor pairs: `q` represents `(q.1 + 1, q.2 + 1)`. -/
def thetaPositiveFactorPairs (k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range k).product (Finset.range k)).filter
    (fun q => (q.1 + 1) * (q.2 + 1) = k)

/-- A fixed positive-product fibre is closed under divisor reflection. -/
theorem thetaPositiveFactorPairs_swap_mem
    {k : ℕ} {q : ℕ × ℕ} (hq : q ∈ thetaPositiveFactorPairs k) :
    q.swap ∈ thetaPositiveFactorPairs k := by
  rcases q with ⟨a, b⟩
  simpa [thetaPositiveFactorPairs, mul_comm] using hq

/-- Centered logarithmic displacement of a positive factor pair. -/
def thetaFactorPairLogDisplacement (q : ℕ × ℕ) : ℝ :=
  (Real.log (q.1 + 1 : ℕ) - Real.log (q.2 + 1 : ℕ)) / 2

/-- Divisor reflection reverses the centered logarithmic displacement. -/
theorem thetaFactorPairLogDisplacement_swap (q : ℕ × ℕ) :
    thetaFactorPairLogDisplacement q.swap =
      -thetaFactorPairLogDisplacement q := by
  rcases q with ⟨a, b⟩
  unfold thetaFactorPairLogDisplacement
  simp only [Prod.swap_prod_mk, Prod.fst, Prod.snd]
  ring

/-- On a product fibre, the two logarithmic shifts are the common centre `log k / 2` plus and
minus the reflected displacement. -/
theorem thetaFactorPair_log_decomposition
    {k : ℕ} {q : ℕ × ℕ} (hq : q ∈ thetaPositiveFactorPairs k) :
    Real.log (q.1 + 1 : ℕ) =
        Real.log k / 2 + thetaFactorPairLogDisplacement q ∧
      Real.log (q.2 + 1 : ℕ) =
        Real.log k / 2 - thetaFactorPairLogDisplacement q := by
  have hprod : (q.1 + 1) * (q.2 + 1) = k := by
    simpa [thetaPositiveFactorPairs] using hq
  have ha : (((q.1 + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hb : (((q.2 + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hlog : Real.log k =
      Real.log (q.1 + 1 : ℕ) + Real.log (q.2 + 1 : ℕ) := by
    rw [← hprod]
    push_cast
    exact Real.log_mul ha hb
  unfold thetaFactorPairLogDisplacement
  constructor <;> linarith

/-- The critical atom weights become constant on a product fibre.  The two copies of the first
canonical atom are translated by the common centre and opposite reflected displacements. -/
theorem thetaCuspTailSecondDensityAtom_mul_eq_productFiberCenteredTranslate
    {k : ℕ} {q : ℕ × ℕ} (hq : q ∈ thetaPositiveFactorPairs k)
    (x y : ℝ) :
    thetaCuspTailSecondDensityAtom (q.1 + 1) x *
        thetaCuspTailSecondDensityAtom (q.2 + 1) y =
      (k : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspTailSecondDensityAtom 1
          (x + Real.log k / 2 + thetaFactorPairLogDisplacement q) *
        thetaCuspTailSecondDensityAtom 1
          (y + Real.log k / 2 - thetaFactorPairLogDisplacement q) := by
  have hdecomp := thetaFactorPair_log_decomposition hq
  have hprod : (q.1 + 1) * (q.2 + 1) = k := by
    simpa [thetaPositiveFactorPairs] using hq
  rw [thetaCuspTailSecondDensityAtom_eq_rpow_mul_translate (Nat.succ_pos q.1),
    thetaCuspTailSecondDensityAtom_eq_rpow_mul_translate (Nat.succ_pos q.2),
    hdecomp.1, hdecomp.2]
  have hweight :
      ((q.1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((q.2 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
        (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    norm_cast
  rw [hweight]
  ring

/-- Finite product-fibre form of the complete square-index atom packet. -/
theorem sum_densityAtomPair_productFiber_eq_centeredTranslates
    (k : ℕ) (x y : ℝ) :
    (∑ q ∈ thetaPositiveFactorPairs k,
      thetaCuspTailSecondDensityAtom (q.1 + 1) x *
        thetaCuspTailSecondDensityAtom (q.2 + 1) y) =
      (k : ℝ) ^ (-(1 / 2 : ℝ)) *
        ∑ q ∈ thetaPositiveFactorPairs k,
          thetaCuspTailSecondDensityAtom 1
              (x + Real.log k / 2 + thetaFactorPairLogDisplacement q) *
            thetaCuspTailSecondDensityAtom 1
              (y + Real.log k / 2 - thetaFactorPairLogDisplacement q) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact thetaCuspTailSecondDensityAtom_mul_eq_productFiberCenteredTranslate hq x y

/-- The finite sine section retains exact odd parity at every truncation depth. -/
theorem finiteSinePolynomial_neg (d : ℕ) (x : ℝ) :
    finiteSinePolynomial d (-x) = -finiteSinePolynomial d x := by
  unfold finiteSinePolynomial
  calc
    (∑ j ∈ Finset.range d,
        Polynomial.C (((-1 : ℂ) ^ j * ((-x : ℝ) : ℂ) ^ (2 * j + 1)) /
          (2 * j + 1).factorial) * Polynomial.X ^ (2 * j + 1)) =
      ∑ j ∈ Finset.range d,
        -(Polynomial.C (((-1 : ℂ) ^ j * (x : ℂ) ^ (2 * j + 1)) /
          (2 * j + 1).factorial) * Polynomial.X ^ (2 * j + 1)) := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [ofReal_neg, neg_pow, (odd_two_mul_add_one j).neg_one_pow]
            ring
    _ = -(∑ j ∈ Finset.range d,
        Polynomial.C (((-1 : ℂ) ^ j * (x : ℂ) ^ (2 * j + 1)) /
          (2 * j + 1).factorial) * Polynomial.X ^ (2 * j + 1)) := by
            rw [Finset.sum_neg_distrib]

/-- The full finite sine packet cancels on every positive product fibre. -/
theorem sum_finiteSinePolynomial_thetaFactorPairLogDisplacement
    (k d : ℕ) :
    ∑ q ∈ thetaPositiveFactorPairs k,
      finiteSinePolynomial d (thetaFactorPairLogDisplacement q) = 0 := by
  apply polynomial_sum_eq_zero_of_swap_neg
  · intro q hq
    exact thetaPositiveFactorPairs_swap_mem hq
  · intro q _hq
    rw [thetaFactorPairLogDisplacement_swap, finiteSinePolynomial_neg]

/-- Product-fibre averaging removes the sine component of the untruncated two-component
translation packet exactly. -/
theorem sum_finiteCosineTranslationPacket_factorPairs
    (k d : ℕ) (x : ℝ) :
    (∑ q ∈ thetaPositiveFactorPairs k,
      finiteCosineTranslationPacket d x (thetaFactorPairLogDisplacement q)) =
      finiteCosinePolynomial d x *
        ∑ q ∈ thetaPositiveFactorPairs k,
          finiteCosinePolynomial d (thetaFactorPairLogDisplacement q) := by
  unfold finiteCosineTranslationPacket
  have hs := sum_finiteSinePolynomial_thetaFactorPairLogDisplacement k d
  calc
    (∑ q ∈ thetaPositiveFactorPairs k,
        (finiteCosinePolynomial d x *
            finiteCosinePolynomial d (thetaFactorPairLogDisplacement q) -
          finiteSinePolynomial d x *
            finiteSinePolynomial d (thetaFactorPairLogDisplacement q))) =
      finiteCosinePolynomial d x *
          ∑ q ∈ thetaPositiveFactorPairs k,
            finiteCosinePolynomial d (thetaFactorPairLogDisplacement q) -
        finiteSinePolynomial d x *
          ∑ q ∈ thetaPositiveFactorPairs k,
            finiteSinePolynomial d (thetaFactorPairLogDisplacement q) := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by rw [hs, mul_zero, sub_zero]

/-- Exact divisor-fibre translation law.  After arithmetic reflection, the explicit finite top
edge is the only deviation from pure cosine transport. -/
theorem sum_finiteCosinePolynomial_add_factorPairs
    (k d : ℕ) (x : ℝ) :
    (∑ q ∈ thetaPositiveFactorPairs k,
      finiteCosinePolynomial d (x + thetaFactorPairLogDisplacement q)) =
      finiteCosinePolynomial d x *
          ∑ q ∈ thetaPositiveFactorPairs k,
            finiteCosinePolynomial d (thetaFactorPairLogDisplacement q) -
        ∑ q ∈ thetaPositiveFactorPairs k,
          finiteCosineTranslationTopEdge d x
            (thetaFactorPairLogDisplacement q) := by
  rw [show (∑ q ∈ thetaPositiveFactorPairs k,
      finiteCosinePolynomial d (x + thetaFactorPairLogDisplacement q)) =
      ∑ q ∈ thetaPositiveFactorPairs k,
        (finiteCosineTranslationPacket d x (thetaFactorPairLogDisplacement q) -
          finiteCosineTranslationTopEdge d x (thetaFactorPairLogDisplacement q)) by
    apply Finset.sum_congr rfl
    intro q _hq
    rw [finiteCosinePolynomial_add_eq_product_sub_topEdge]
    rfl]
  rw [Finset.sum_sub_distrib,
    sum_finiteCosineTranslationPacket_factorPairs]

end

end RHTower
