import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedFullDerivativeIdentity

/-!
# Explicit tail of the differentiated reflected Gaussian AFE edge

The fixed left contour gives exponent `3/2+d`; its single logarithm is
absorbed by half of the `d` margin.  The resulting tail decays like
`L^(-(1/2+d/2))`.
-/

noncomputable section

namespace RHTower

open Complex

theorem norm_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm_eq
    {d eta x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) (n : ℕ) :
    ‖smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
        d x tau n‖ =
      ‖smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x tau n‖ := by
  rw [smoothAFEZetaDisplacedDualCoefficientHeightDerivative_eq_neg_weighted
    hd hdquarter heta hetaquarter hx tau n, norm_neg]

theorem summable_norm_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
    {d eta x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) :
    Summable (fun n : ℕ =>
      ‖smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
        d x tau n‖) := by
  refine (summable_norm_smoothAFEZetaDisplacedDualCoefficientHeightDerivative
    hd hdquarter hx tau).congr fun n => ?_
  exact (norm_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm_eq
    hd hdquarter heta hetaquarter hx tau n).symm

theorem exists_norm_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm_le_rpow
    {d eta x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ tau : ℝ, ∀ n : ℕ,
      ‖smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
          d x tau n‖ ≤
        K * (1 + |tau|) ^ 3 *
          (n + 1 : ℝ) ^ (-(3 / 2 + d / 2)) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_norm_smoothAFEZetaDisplacedDualCoefficientHeightDerivative_le
      hd hdquarter hx
  let K : ℝ := C * (1 + 2 / d)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, fun tau n => ?_⟩
  let r : ℝ := n + 1
  have hr : 1 ≤ r := by
    dsimp only [r]
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hdhalf : 0 < d / 2 := by linarith
  have hlogRaw := Real.log_le_rpow_div hr0.le hdhalf
  have hlog : Real.log r ≤ (2 / d) * r ^ (d / 2) := by
    calc
      Real.log r ≤ r ^ (d / 2) / (d / 2) := hlogRaw
      _ = (2 / d) * r ^ (d / 2) := by
        field_simp [hd.ne']
  have hone : 1 ≤ r ^ (d / 2) := Real.one_le_rpow hr hdhalf.le
  have hlogFactor :
      1 + Real.log r ≤ (1 + 2 / d) * r ^ (d / 2) := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 / d)
      (Real.rpow_nonneg hr0.le (d / 2))]
  rw [norm_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm_eq
    hd hdquarter heta hetaquarter hx]
  calc
    ‖smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x tau n‖
      ≤ C * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
          (1 + Real.log (n + 1 : ℝ)) * (1 + |tau|) ^ 3 :=
        hcoeff tau n
    _ ≤ C * r ^ (-(3 / 2 + d)) *
          ((1 + 2 / d) * r ^ (d / 2)) * (1 + |tau|) ^ 3 := by
        dsimp only [r]
        gcongr
    _ = C * (1 + 2 / d) * (1 + |tau|) ^ 3 *
          (r ^ (-(3 / 2 + d)) * r ^ (d / 2)) := by ring
    _ = K * (1 + |tau|) ^ 3 * r ^ (-(3 / 2 + d / 2)) := by
        rw [← Real.rpow_add hr0]
        dsimp only [K]
        congr 2
        ring
    _ = K * (1 + |tau|) ^ 3 *
          (n + 1 : ℝ) ^ (-(3 / 2 + d / 2)) := by rfl

/-- Explicit differentiated reflected-series tail. -/
theorem exists_norm_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeSourceField_sub_sum_le
    {d eta x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ tau : ℝ, ∀ L : ℕ, 1 ≤ L →
      ‖smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeSourceField
          d x tau -
        ∑ n ∈ Finset.range L,
          smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
            d x tau n‖ ≤
      K * (1 + |tau|) ^ 3 *
        ((L : ℝ) ^ (-(1 / 2 + d / 2)) / (1 / 2 + d / 2)) := by
  obtain ⟨K, hK, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm_le_rpow
      hd hdquarter heta hetaquarter hx
  refine ⟨K, hK, fun tau L hL => ?_⟩
  let f : ℕ → ℂ := fun n =>
    smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm d x tau n
  let A : ℝ := K * (1 + |tau|) ^ 3
  let p : ℝ := 3 / 2 + d / 2
  have hp : 1 < p := by dsimp only [p]; linarith
  have hnorm : Summable (fun n : ℕ => ‖f n‖) := by
    simpa only [f] using
      summable_norm_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
        hd hdquarter heta hetaquarter hx tau
  have hsum : Summable f := Summable.of_norm hnorm
  have hsplit := hsum.sum_add_tsum_nat_add L
  have heq :
      (∑' n : ℕ, f n) - ∑ n ∈ Finset.range L, f n =
        ∑' j : ℕ, f (j + L) := by
    rw [← hsplit, add_sub_cancel_left]
  rw [smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeSourceField,
    show (fun n : ℕ =>
      smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
        d x tau n) = f by rfl, heq]
  have hnormTail : Summable (fun j : ℕ => ‖f (j + L)‖) :=
    (summable_nat_add_iff L).2 hnorm
  have hpow : Summable (fun j : ℕ =>
      (((j + L + 1 : ℕ) : ℝ)) ^ (-p)) := by
    have hbase := Real.summable_nat_rpow.mpr (by linarith : -p < -1)
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff (L + 1)).2 hbase
  have hmajor : Summable (fun j : ℕ =>
      A * (((j + L + 1 : ℕ) : ℝ)) ^ (-p)) := hpow.mul_left A
  calc
    ‖∑' j : ℕ, f (j + L)‖
      ≤ ∑' j : ℕ, ‖f (j + L)‖ := norm_tsum_le_tsum_norm hnormTail
    _ ≤ ∑' j : ℕ,
        A * (((j + L + 1 : ℕ) : ℝ)) ^ (-p) := by
      exact Summable.tsum_le_tsum (fun j => by
        calc
          ‖f (j + L)‖
            ≤ K * (1 + |tau|) ^ 3 *
                (j + L + 1 : ℝ) ^ (-(3 / 2 + d / 2)) := by
              simpa only [f, Nat.cast_add, Nat.cast_one, add_assoc] using
                hpoint tau (j + L)
          _ = A * (((j + L + 1 : ℕ) : ℝ)) ^ (-p) := by
              dsimp only [A, p]
              push_cast
              ring) hnormTail hmajor
    _ = A * ∑' j : ℕ,
        (((j + L + 1 : ℕ) : ℝ)) ^ (-p) := by rw [tsum_mul_left]
    _ ≤ A * ((L : ℝ) ^ (1 - p) / (p - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (Sieve.tsum_tail_rpow_neg_le hp hL) (by dsimp only [A]; positivity)
    _ = K * (1 + |tau|) ^ 3 *
        ((L : ℝ) ^ (-(1 / 2 + d / 2)) / (1 / 2 + d / 2)) := by
      dsimp only [A, p]
      ring_nf

end RHTower
