import GaloisForLFunctions.RHTower.XiResolventNodalSingleMinorCriterion
import GaloisForLFunctions.HTGeometry.PrimeEulerProductAperture

/-!
# The rational-node criterion: RH as a countable family of real inequalities

The single-minor datum of a shifted nodal polynomial is Lipschitz in the node positions with the
explicit constant `8j·S²·16^j` (`S` = total resolvent mass, `j` = number of nodes): each nodal
factor is bounded by `2` on the closed unit disk, a product of `j` factors moves by at most
`j·2^j` times the node displacement, and the datum is a quadratic expression in three moments
each bounded by `S·4^j`.

Since the nodes range in `(0,1]` and every real node is approximable from below by rationals,
nonnegativity of the data at *rational* nodes forces it at all real nodes, and the nodal
single-minor criterion densifies: at any one interior shift, the Riemann hypothesis is
equivalent to the countable family of real inequalities indexed by `(j, m, c : Fin j → ℚ)` —
one `(0,2,1)` Turán minor per rational node tuple and shift index.
-/

open Complex

namespace RHTower

noncomputable section

/-- The monic real polynomial with the prescribed tuple of real nodes as roots. -/
def finNodalPolynomial {j : ℕ} (c : Fin j → ℝ) : Polynomial ℝ :=
  ∏ i, (Polynomial.X - Polynomial.C (c i))

/-- Complex evaluation of a tuple-nodal polynomial is the product of the node offsets. -/
theorem evalRealPolynomial_finNodalPolynomial {j : ℕ} (c : Fin j → ℝ) (z : ℂ) :
    evalRealPolynomial (finNodalPolynomial c) z = ∏ i, (z - ((c i : ℝ) : ℂ)) := by
  rw [finNodalPolynomial, evalRealPolynomial, Polynomial.map_prod, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

/-- Complex evaluation of a shifted tuple-nodal polynomial. -/
theorem evalRealPolynomial_shiftedFinNodal {j m : ℕ} (c : Fin j → ℝ) (z : ℂ) :
    evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c) z =
      z ^ m * ∏ i, (z - ((c i : ℝ) : ℂ)) := by
  rw [evalRealPolynomial_mul, evalRealPolynomial_pow, evalRealPolynomial_X,
    evalRealPolynomial_finNodalPolynomial]

/-- A nodal factor is bounded by `2` on the closed unit disk. -/
theorem norm_sub_node_le {z : ℂ} (hz : ‖z‖ ≤ 1) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    ‖z - ((r : ℝ) : ℂ)‖ ≤ 2 := by
  calc ‖z - ((r : ℝ) : ℂ)‖ ≤ ‖z‖ + ‖((r : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
        refine add_le_add hz ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
        exact h1
    _ = 2 := by norm_num

/-- A shifted nodal polynomial with nodes in `[0,1]` is bounded by `2^j` on the unit disk. -/
theorem norm_evalRealPolynomial_shiftedFinNodal_le {j m : ℕ} {c : Fin j → ℝ}
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c) z‖ ≤ 2 ^ j := by
  rw [evalRealPolynomial_shiftedFinNodal, norm_mul, norm_pow, norm_prod]
  have h2 : ∏ i, ‖z - ((c i : ℝ) : ℂ)‖ ≤ 2 ^ j := by
    calc ∏ i, ‖z - ((c i : ℝ) : ℂ)‖ ≤ ∏ _i : Fin j, (2 : ℝ) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _)
            (fun i _ => norm_sub_node_le hz (hc i).1 (hc i).2)
      _ = 2 ^ j := by rw [Finset.prod_const, Finset.card_fin]
  calc ‖z‖ ^ m * ∏ i, ‖z - ((c i : ℝ) : ℂ)‖ ≤ 1 * 2 ^ j :=
        mul_le_mul (pow_le_one₀ (norm_nonneg _) hz) h2
          (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one
    _ = 2 ^ j := one_mul _

/-- Moving each node by at most `ε` moves a shifted nodal evaluation by at most `j·2^j·ε` on
the unit disk. -/
theorem norm_evalRealPolynomial_shiftedFinNodal_sub_le {j m : ℕ} {c c' : Fin j → ℝ}
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) (hc' : ∀ i, 0 ≤ c' i ∧ c' i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hdist : ∀ i, |c i - c' i| ≤ ε) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c) z -
      evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c') z‖ ≤
      j * 2 ^ j * ε := by
  rw [evalRealPolynomial_shiftedFinNodal, evalRealPolynomial_shiftedFinNodal, ← mul_sub,
    norm_mul, norm_pow]
  have hprod : ‖(∏ i, (z - ((c i : ℝ) : ℂ))) - ∏ i, (z - ((c' i : ℝ) : ℂ))‖ ≤
      ((Finset.univ : Finset (Fin j)).card : ℝ) *
        2 ^ (Finset.univ : Finset (Fin j)).card * ε := by
    refine GaloisForLFunctions.norm_prod_sub_prod_le _ _ (by norm_num : (1 : ℝ) ≤ 2) hε
      Finset.univ (fun i _ => norm_sub_node_le hz (hc i).1 (hc i).2)
      (fun i _ => norm_sub_node_le hz (hc' i).1 (hc' i).2) (fun i _ => ?_)
    have heq : (z - ((c i : ℝ) : ℂ)) - (z - ((c' i : ℝ) : ℂ)) =
        (((c' i - c i : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact hdist i
  rw [Finset.card_fin] at hprod
  calc ‖z‖ ^ m * ‖(∏ i, (z - ((c i : ℝ) : ℂ))) - ∏ i, (z - ((c' i : ℝ) : ℂ))‖
      ≤ 1 * ((j : ℝ) * 2 ^ j * ε) :=
        mul_le_mul (pow_le_one₀ (norm_nonneg _) hz) hprod (norm_nonneg _) zero_le_one
    _ = (j : ℝ) * 2 ^ j * ε := one_mul _

/-- The shifted nodal moments are bounded by `S·4^j`. -/
theorem norm_xiPolyMoment_shiftedFinNodal_le {X : ℝ} (hX : 0 ≤ X) {j m : ℕ}
    {c : Fin j → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) {S : ℝ}
    (hS : ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ S) (k : ℕ) :
    ‖xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) k X‖ ≤ S * 4 ^ j := by
  have hsum := summable_norm_polyAtom hX (Polynomial.X ^ m * finNodalPolynomial c) k
  have hmass : Summable (fun q : XiZeroCopy => ‖xiResolventPoint X q‖ * 4 ^ j) :=
    (summable_norm_xiResolventPoint hX).mul_right _
  have hpow4 : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
  calc ‖xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) k X‖
      = ‖∑' q : XiZeroCopy, xiResolventPoint X q ^ (k + 1) *
          evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
            (xiResolventPoint X q) ^ 2‖ := rfl
    _ ≤ ∑' q : XiZeroCopy, ‖xiResolventPoint X q ^ (k + 1) *
          evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
            (xiResolventPoint X q) ^ 2‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ * 4 ^ j := by
        refine Summable.tsum_le_tsum (fun q => ?_) hsum hmass
        rw [norm_mul, norm_pow]
        have hu1 : ‖xiResolventPoint X q‖ ≤ 1 := norm_xiResolventPoint_le_one hX q
        have hupow : ‖xiResolventPoint X q‖ ^ (k + 1) ≤ ‖xiResolventPoint X q‖ := by
          calc ‖xiResolventPoint X q‖ ^ (k + 1)
              = ‖xiResolventPoint X q‖ * ‖xiResolventPoint X q‖ ^ k := pow_succ' _ _
            _ ≤ ‖xiResolventPoint X q‖ * 1 := mul_le_mul_of_nonneg_left
                (pow_le_one₀ (norm_nonneg _) hu1) (norm_nonneg _)
            _ = ‖xiResolventPoint X q‖ := mul_one _
        have hev : ‖evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
            (xiResolventPoint X q) ^ 2‖ ≤ 4 ^ j := by
          rw [norm_pow, ← hpow4]
          exact pow_le_pow_left₀ (norm_nonneg _)
            (norm_evalRealPolynomial_shiftedFinNodal_le hc hu1) 2
        exact mul_le_mul hupow hev (norm_nonneg _) (norm_nonneg _)
    _ = (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖) * 4 ^ j := tsum_mul_right
    _ ≤ S * 4 ^ j := mul_le_mul_of_nonneg_right hS (by positivity)

/-- Moving each node by at most `ε` moves each shifted nodal moment by at most
`S·j·2^(2j+1)·ε`. -/
theorem norm_xiPolyMoment_shiftedFinNodal_sub_le {X : ℝ} (hX : 0 ≤ X) {j m : ℕ}
    {c c' : Fin j → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) (hc' : ∀ i, 0 ≤ c' i ∧ c' i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hdist : ∀ i, |c i - c' i| ≤ ε) {S : ℝ}
    (hS : ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ S) (k : ℕ) :
    ‖xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) k X -
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') k X‖ ≤
      S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε) := by
  have hsc : Summable (fun q : XiZeroCopy => xiResolventPoint X q ^ (k + 1) *
      evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
        (xiResolventPoint X q) ^ 2) :=
    (summable_norm_polyAtom hX _ k).of_norm
  have hsc' : Summable (fun q : XiZeroCopy => xiResolventPoint X q ^ (k + 1) *
      evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c')
        (xiResolventPoint X q) ^ 2) :=
    (summable_norm_polyAtom hX _ k).of_norm
  have hK0 : 0 ≤ (j : ℝ) * 2 ^ (2 * j + 1) * ε :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (by positivity)) hε
  have hpowsplit : (2 : ℝ) ^ (2 * j + 1) = 2 ^ j * 2 ^ j * 2 := by
    rw [pow_succ, two_mul, pow_add]
  have hnormdiff : ∀ q : XiZeroCopy,
      ‖(xiResolventPoint X q ^ (k + 1) *
          evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
            (xiResolventPoint X q) ^ 2) -
        (xiResolventPoint X q ^ (k + 1) *
          evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c')
            (xiResolventPoint X q) ^ 2)‖ ≤
      ‖xiResolventPoint X q‖ * ((j : ℝ) * 2 ^ (2 * j + 1) * ε) := by
    intro q
    have hu1 : ‖xiResolventPoint X q‖ ≤ 1 := norm_xiResolventPoint_le_one hX q
    have hfac : (xiResolventPoint X q ^ (k + 1) *
        evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
          (xiResolventPoint X q) ^ 2) -
        (xiResolventPoint X q ^ (k + 1) *
          evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c')
            (xiResolventPoint X q) ^ 2) =
        xiResolventPoint X q ^ (k + 1) *
          ((evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
              (xiResolventPoint X q) +
            evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c')
              (xiResolventPoint X q)) *
           (evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
              (xiResolventPoint X q) -
            evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c')
              (xiResolventPoint X q))) := by
      ring
    rw [hfac, norm_mul, norm_pow, norm_mul]
    have hupow : ‖xiResolventPoint X q‖ ^ (k + 1) ≤ ‖xiResolventPoint X q‖ := by
      calc ‖xiResolventPoint X q‖ ^ (k + 1)
          = ‖xiResolventPoint X q‖ * ‖xiResolventPoint X q‖ ^ k := pow_succ' _ _
        _ ≤ ‖xiResolventPoint X q‖ * 1 := mul_le_mul_of_nonneg_left
            (pow_le_one₀ (norm_nonneg _) hu1) (norm_nonneg _)
        _ = ‖xiResolventPoint X q‖ := mul_one _
    have hsumb : ‖evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
        (xiResolventPoint X q) +
        evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c')
          (xiResolventPoint X q)‖ ≤ 2 ^ j + 2 ^ j := by
      calc ‖_ + _‖ ≤ ‖evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
              (xiResolventPoint X q)‖ +
            ‖evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c')
              (xiResolventPoint X q)‖ := norm_add_le _ _
        _ ≤ 2 ^ j + 2 ^ j := add_le_add
            (norm_evalRealPolynomial_shiftedFinNodal_le hc hu1)
            (norm_evalRealPolynomial_shiftedFinNodal_le hc' hu1)
    have hdiffb := norm_evalRealPolynomial_shiftedFinNodal_sub_le (m := m)
      hc hc' hε hdist hu1
    have hcore : ‖evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
        (xiResolventPoint X q) +
        evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c')
          (xiResolventPoint X q)‖ *
        ‖evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
          (xiResolventPoint X q) -
          evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c')
            (xiResolventPoint X q)‖ ≤ (j : ℝ) * 2 ^ (2 * j + 1) * ε := by
      refine le_trans (mul_le_mul hsumb hdiffb (norm_nonneg _) (by positivity))
        (le_of_eq ?_)
      rw [hpowsplit]
      ring
    exact mul_le_mul hupow hcore
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hmass : Summable (fun q : XiZeroCopy =>
      ‖xiResolventPoint X q‖ * ((j : ℝ) * 2 ^ (2 * j + 1) * ε)) :=
    (summable_norm_xiResolventPoint hX).mul_right _
  have hsubsum : Summable (fun q : XiZeroCopy =>
      ‖(xiResolventPoint X q ^ (k + 1) *
          evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
            (xiResolventPoint X q) ^ 2) -
        (xiResolventPoint X q ^ (k + 1) *
          evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c')
            (xiResolventPoint X q) ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) hnormdiff hmass
  have heq : xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) k X -
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') k X =
      ∑' q : XiZeroCopy, ((xiResolventPoint X q ^ (k + 1) *
          evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
            (xiResolventPoint X q) ^ 2) -
        (xiResolventPoint X q ^ (k + 1) *
          evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c')
            (xiResolventPoint X q) ^ 2)) :=
    (hsc.tsum_sub hsc').symm
  rw [heq]
  calc ‖∑' q : XiZeroCopy, _‖
      ≤ ∑' q : XiZeroCopy, ‖(xiResolventPoint X q ^ (k + 1) *
          evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c)
            (xiResolventPoint X q) ^ 2) -
        (xiResolventPoint X q ^ (k + 1) *
          evalRealPolynomial (Polynomial.X ^ m * finNodalPolynomial c')
            (xiResolventPoint X q) ^ 2)‖ := norm_tsum_le_tsum_norm hsubsum
    _ ≤ ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ *
          ((j : ℝ) * 2 ^ (2 * j + 1) * ε) :=
        Summable.tsum_le_tsum hnormdiff hsubsum hmass
    _ = (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖) *
          ((j : ℝ) * 2 ^ (2 * j + 1) * ε) := tsum_mul_right
    _ ≤ S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε) := mul_le_mul_of_nonneg_right hS hK0

/-- **Node stability of the single-minor datum**: moving each node by at most `ε` moves the
`(0,2,1)` Turán datum by at most `8j·S²·16^j·ε`. -/
theorem abs_re_datum_shiftedFinNodal_sub_le {X : ℝ} (hX : 0 ≤ X) {j m : ℕ}
    {c c' : Fin j → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) (hc' : ∀ i, 0 ≤ c' i ∧ c' i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hdist : ∀ i, |c i - c' i| ≤ ε) {S : ℝ}
    (hS : ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ S) :
    |(xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X *
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 2 X -
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X ^ 2).re -
      (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 0 X *
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 2 X -
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X ^ 2).re| ≤
      8 * (j : ℝ) * S ^ 2 * 16 ^ j * ε := by
  have hS0 : 0 ≤ S := le_trans (tsum_nonneg fun q => norm_nonneg _) hS
  have hb0 := norm_xiPolyMoment_shiftedFinNodal_le (m := m) hX hc hS 0
  have hb1 := norm_xiPolyMoment_shiftedFinNodal_le (m := m) hX hc hS 1
  have hb1' := norm_xiPolyMoment_shiftedFinNodal_le (m := m) hX hc' hS 1
  have hb2' := norm_xiPolyMoment_shiftedFinNodal_le (m := m) hX hc' hS 2
  have hd0 := norm_xiPolyMoment_shiftedFinNodal_sub_le (m := m) hX hc hc' hε hdist hS 0
  have hd1 := norm_xiPolyMoment_shiftedFinNodal_sub_le (m := m) hX hc hc' hε hdist hS 1
  have hd2 := norm_xiPolyMoment_shiftedFinNodal_sub_le (m := m) hX hc hc' hε hdist hS 2
  have hK0 : 0 ≤ S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε) :=
    mul_nonneg hS0 (mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (by positivity)) hε)
  have habs : |(xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X *
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 2 X -
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X ^ 2).re -
      (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 0 X *
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 2 X -
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X ^ 2).re| ≤
      ‖(xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X *
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 2 X -
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X ^ 2) -
      (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 0 X *
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 2 X -
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X ^ 2)‖ := by
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  refine le_trans habs ?_
  have hsplit : (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X *
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 2 X -
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X ^ 2) -
      (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 0 X *
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 2 X -
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X ^ 2) =
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X *
        (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 2 X -
          xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 2 X) +
      (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X -
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 0 X) *
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 2 X -
      (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X +
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X) *
        (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X -
          xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X) := by
    ring
  rw [hsplit]
  have hterm1 : ‖xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X *
      (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 2 X -
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 2 X)‖ ≤
      S * 4 ^ j * (S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε)) := by
    rw [norm_mul]
    exact mul_le_mul hb0 hd2 (norm_nonneg _) (by positivity)
  have hterm2 : ‖(xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X -
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 0 X) *
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 2 X‖ ≤
      S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε) * (S * 4 ^ j) := by
    rw [norm_mul]
    exact mul_le_mul hd0 hb2' (norm_nonneg _) hK0
  have hterm3 : ‖(xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X +
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X) *
      (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X -
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X)‖ ≤
      (S * 4 ^ j + S * 4 ^ j) * (S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε)) := by
    rw [norm_mul]
    refine mul_le_mul ?_ hd1 (norm_nonneg _) (by positivity)
    calc ‖xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X +
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X‖
        ≤ ‖xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X‖ +
          ‖xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X‖ := norm_add_le _ _
      _ ≤ S * 4 ^ j + S * 4 ^ j := add_le_add hb1 hb1'
  have hnorm3 : ‖xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X *
      (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 2 X -
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 2 X) +
      (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X -
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 0 X) *
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 2 X -
      (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X +
        xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X) *
        (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X -
          xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X)‖ ≤
      S * 4 ^ j * (S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε)) +
      S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε) * (S * 4 ^ j) +
      (S * 4 ^ j + S * 4 ^ j) * (S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε)) := by
    calc ‖_ + _ - _‖ ≤ ‖xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X *
          (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 2 X -
            xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 2 X) +
          (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X -
            xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 0 X) *
            xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 2 X‖ +
          ‖(xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X +
            xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X) *
            (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X -
              xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c') 1 X)‖ :=
          norm_sub_le _ _
      _ ≤ (S * 4 ^ j * (S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε)) +
            S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε) * (S * 4 ^ j)) +
          (S * 4 ^ j + S * 4 ^ j) * (S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε)) := by
          refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hterm1 hterm2)) hterm3
      _ = S * 4 ^ j * (S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε)) +
          S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε) * (S * 4 ^ j) +
          (S * 4 ^ j + S * 4 ^ j) * (S * ((j : ℝ) * 2 ^ (2 * j + 1) * ε)) := by ring
  refine le_trans hnorm3 (le_of_eq ?_)
  have h16 : (16 : ℝ) ^ j = 4 ^ j * 4 ^ j := by
    rw [show (16 : ℝ) = 4 * 4 by norm_num, mul_pow]
  have h4 : (2 : ℝ) ^ (2 * j + 1) = 2 * 4 ^ j := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h16, h4]
  ring

/-- **Rational density**: nonnegativity of the single-minor data at all rational node tuples in
`(0,1]` forces it at all real node tuples in `(0,1]`. -/
theorem finNodal_datum_re_nonneg_of_rational {X : ℝ} (hX : 0 ≤ X)
    (h0 : ∀ (j m : ℕ) (c : Fin j → ℚ), (∀ i, 0 < c i ∧ (c i : ℝ) ≤ 1) →
      0 ≤ (xiPolyMoment (Polynomial.X ^ m *
          finNodalPolynomial (fun i => ((c i : ℝ)))) 0 X *
        xiPolyMoment (Polynomial.X ^ m *
          finNodalPolynomial (fun i => ((c i : ℝ)))) 2 X -
        xiPolyMoment (Polynomial.X ^ m *
          finNodalPolynomial (fun i => ((c i : ℝ)))) 1 X ^ 2).re)
    {j m : ℕ} {c : Fin j → ℝ} (hc : ∀ i, 0 < c i ∧ c i ≤ 1) :
    0 ≤ (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X *
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 2 X -
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X ^ 2).re := by
  classical
  set S : ℝ := ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ with hSdef
  have hS : ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ S := hSdef.ge
  have hS0 : 0 ≤ S := le_trans (tsum_nonneg fun q => norm_nonneg _) hS
  have hL0 : 0 ≤ 8 * (j : ℝ) * S ^ 2 * 16 ^ j := by positivity
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε : ℝ := δ / (8 * (j : ℝ) * S ^ 2 * 16 ^ j + 1) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    positivity
  have happrox : ∀ i : Fin j, ∃ q : ℚ, 0 < q ∧ (q : ℝ) ≤ 1 ∧ |c i - (q : ℝ)| ≤ ε := by
    intro i
    have hlow : max (c i - ε) (c i / 2) < c i :=
      max_lt (by linarith) (by linarith [(hc i).1])
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlow
    refine ⟨q, ?_, le_of_lt (lt_of_lt_of_le hq2 (hc i).2), ?_⟩
    · have hq0 : (0 : ℝ) < q :=
        lt_of_le_of_lt (by linarith [(hc i).1] : (0 : ℝ) ≤ c i / 2)
          (lt_of_le_of_lt (le_max_right _ _) hq1)
      exact_mod_cast hq0
    · have h1 : c i - ε ≤ (q : ℝ) :=
        le_of_lt (lt_of_le_of_lt (le_max_left _ _) hq1)
      have h2 : (q : ℝ) ≤ c i := le_of_lt hq2
      rw [abs_of_nonneg (by linarith)]
      linarith
  choose qf hqf using happrox
  have hdat := h0 j m qf (fun i => ⟨(hqf i).1, (hqf i).2.1⟩)
  have hstab := abs_re_datum_shiftedFinNodal_sub_le hX (m := m)
    (c := c) (c' := fun i => ((qf i : ℝ)))
    (fun i => ⟨le_of_lt (hc i).1, (hc i).2⟩)
    (fun i => ⟨by exact_mod_cast le_of_lt (hqf i).1, (hqf i).2.1⟩)
    (le_of_lt hεpos) (fun i => (hqf i).2.2) hS
  have hLε : 8 * (j : ℝ) * S ^ 2 * 16 ^ j * ε ≤ δ := by
    rw [hεdef, show 8 * (j : ℝ) * S ^ 2 * 16 ^ j *
        (δ / (8 * (j : ℝ) * S ^ 2 * 16 ^ j + 1)) =
        8 * (j : ℝ) * S ^ 2 * 16 ^ j * δ / (8 * (j : ℝ) * S ^ 2 * 16 ^ j + 1) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  have habs := abs_le.mp hstab
  linarith [habs.1, habs.2]

/-- Rational nodal single-minor data at one shift prove RH. -/
theorem riemannHypothesis_of_forall_rational_nodal_single_minor {X : ℝ} (hX : 0 ≤ X)
    (h0 : ∀ (j m : ℕ) (c : Fin j → ℚ), (∀ i, 0 < c i ∧ (c i : ℝ) ≤ 1) →
      0 ≤ (xiPolyMoment (Polynomial.X ^ m *
          finNodalPolynomial (fun i => ((c i : ℝ)))) 0 X *
        xiPolyMoment (Polynomial.X ^ m *
          finNodalPolynomial (fun i => ((c i : ℝ)))) 2 X -
        xiPolyMoment (Polynomial.X ^ m *
          finNodalPolynomial (fun i => ((c i : ℝ)))) 1 X ^ 2).re) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_nodal_single_minor hX (fun R hR m => ?_)
  have hbridge : nodalPolynomial R =
      finNodalPolynomial (fun i : Fin R.card => ((R.orderIsoOfFin rfl i : ℝ))) := by
    rw [nodalPolynomial, finNodalPolynomial, ← Finset.prod_coe_sort R
      (fun r => Polynomial.X - Polynomial.C r)]
    exact (Equiv.prod_comp (R.orderIsoOfFin rfl).toEquiv
      (fun x : {x // x ∈ R} => Polynomial.X - Polynomial.C (x : ℝ))).symm
  rw [hbridge]
  exact finNodal_datum_re_nonneg_of_rational hX h0
    (fun i => hR _ (R.orderIsoOfFin rfl i).2)

/-- **The rational-node criterion**: at any one interior shift, the Riemann hypothesis is
equivalent to the countable family of real inequalities indexed by a node count, a shift index,
and a rational node tuple in `(0,1]` — one single `(0,2,1)` Turán minor per index. -/
theorem riemannHypothesis_iff_forall_rational_nodal_single_minor {X : ℝ} (hX : 0 ≤ X) :
    RiemannHypothesis ↔ ∀ (j m : ℕ) (c : Fin j → ℚ),
      (∀ i, 0 < c i ∧ (c i : ℝ) ≤ 1) →
      0 ≤ (xiPolyMoment (Polynomial.X ^ m *
          finNodalPolynomial (fun i => ((c i : ℝ)))) 0 X *
        xiPolyMoment (Polynomial.X ^ m *
          finNodalPolynomial (fun i => ((c i : ℝ)))) 2 X -
        xiPolyMoment (Polynomial.X ^ m *
          finNodalPolynomial (fun i => ((c i : ℝ)))) 1 X ^ 2).re :=
  ⟨fun hRH j m c _ => by
      simpa only [Nat.zero_add] using
        polyTuranMinor_re_nonneg_of_riemannHypothesis hRH hX
          (Polynomial.X ^ m * finNodalPolynomial (fun i => ((c i : ℝ)))) 0,
    riemannHypothesis_of_forall_rational_nodal_single_minor hX⟩

/-- The index family of the rational-node criterion is countable. -/
theorem rational_nodal_index_countable : Countable ((j : ℕ) × ℕ × (Fin j → ℚ)) :=
  inferInstance

end

end RHTower
