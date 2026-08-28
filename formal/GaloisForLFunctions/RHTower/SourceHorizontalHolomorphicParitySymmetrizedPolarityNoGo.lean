import GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicUnitizationOddCompoundNoGo
import GaloisForLFunctions.RHTower.XiCentralDiscBound
import GaloisForLFunctions.RHTower.SuzukiWeilVerticalDecay
import GaloisForLFunctions.HTGeometry.RealEvenFactorizationSignTransfer

/-!
# Polarity obstruction to parity-symmetrized holomorphic SC unitization

The product `U_m(z) U_m(-z)` is the strongest direct escape from the odd-compound obstruction:
it is entire, even, and centrally normalized.  This file computes its real polarity exactly.

For `R = I - 𝟙𝟙ᵀ`, the matrix determinant lemma gives

`det(I + R diag(b)) = ∏ᵢ (1+bᵢ) · (1 - ∑ᵢ bᵢ/(1+bᵢ))`.

At transverse input one, the exact prime Gamma-Bockstein coefficient is
`-(p-1)/(p+1)`.  The forward unitized determinant is therefore positive.  Under reflection the
weights become positive, and their rank-one polarity index eventually exceeds one, forcing the
reflected determinant negative.  Hence the parity-symmetrized determinant is eventually negative
at `z=1`.

The normalized centered Xi value at `z=1` is positive: Xi is real on the real axis and the
certified central unit disc is zero-free, so its real values at zero and one have the same sign.
Thus the even, entire, center-normalized symmetrized SC determinants cannot converge compact-open
to normalized Xi.  No RH assumption or zero-location hypothesis is used.
-/

open Complex Filter Topology Set
open scoped BigOperators Matrix

namespace RHTower

noncomputable section

/-- Exact diagonal-plus-rank-one factorization of the unitized real reservoir determinant. -/
theorem unitizedRealReservoirDeterminant_eq_product_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (hb : ∀ i, 1 + b i ≠ 0) :
    unitizedRealReservoirDeterminant b =
      (∏ i, (1 + b i)) * (1 - ∑ i, b i / (1 + b i)) := by
  let d : ι → ℝ := fun i => 1 + b i
  let A : Matrix ι ι ℝ := Matrix.diagonal d
  let u : ι → ℝ := fun _ => -1
  let v : ι → ℝ := b
  have hmatrix :
      1 + realReservoirDiagonalMatrix b =
        A + Matrix.replicateCol Unit u * Matrix.replicateRow Unit v := by
    ext i j
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply,
      realReservoirDiagonalMatrix_apply]
    by_cases hij : i = j
    · subst j
      simp [A, d, u, v, realReservoirBaseMatrix, realReservoirOnesMatrix]
    · simp [A, d, u, v, realReservoirBaseMatrix, realReservoirOnesMatrix, hij]
  have hA : IsUnit A.det := by
    change IsUnit (Matrix.diagonal d).det
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i hi
    exact hb i
  rw [unitizedRealReservoirDeterminant, hmatrix,
    Matrix.det_add_replicateCol_mul_replicateRow hA]
  change (Matrix.diagonal d).det *
      (1 + Matrix.replicateRow Unit v * (Matrix.diagonal d)⁻¹ *
        Matrix.replicateCol Unit u).det = _
  rw [Matrix.det_diagonal, Matrix.inv_diagonal]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply,
    Matrix.replicateRow_apply, Matrix.replicateCol_apply, u, v, mul_neg,
    Finset.sum_neg_distrib]
  simp only [mul_one]
  rw [← sub_eq_add_neg]
  change 1 - (∑ x, ∑ y, b y * Matrix.diagonal (Ring.inverse d) y x) =
    1 - ∑ i, b i / (1 + b i)
  have hdunit : IsUnit d := by
    apply Matrix.isUnit_diagonal.mp
    exact (Matrix.isUnit_iff_isUnit_det _).mpr hA
  have hinverse (i : ι) : Ring.inverse d i = (1 + b i)⁻¹ := by
    have hcancel := congrFun (Ring.inverse_mul_cancel d hdunit) i
    simp only [Pi.mul_apply, Pi.one_apply] at hcancel
    exact (mul_eq_one_iff_eq_inv₀ (hb i)).mp (by simpa [d] using hcancel)
  have hsum :
      (∑ x, ∑ y, b y * Matrix.diagonal (Ring.inverse d) y x) =
        ∑ i, b i * (1 + b i)⁻¹ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp [hinverse]
    · intro j hj hji
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hji), mul_zero]
    · simp
  rw [hsum]
  simp [div_eq_mul_inv]

/-- Exact positive/zero/negative classification by the rank-one polarity index. -/
theorem unitizedRealReservoirDeterminant_sign_classification
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (hfactor : ∀ i, 0 < 1 + b i) :
    (0 < unitizedRealReservoirDeterminant b ↔
        (∑ i, b i / (1 + b i)) < 1) ∧
      (unitizedRealReservoirDeterminant b = 0 ↔
        (∑ i, b i / (1 + b i)) = 1) ∧
      (unitizedRealReservoirDeterminant b < 0 ↔
        1 < ∑ i, b i / (1 + b i)) := by
  rw [unitizedRealReservoirDeterminant_eq_product_mul b
    (fun i => ne_of_gt (hfactor i))]
  have hprod : 0 < ∏ i, (1 + b i) :=
    Finset.prod_pos fun i hi => hfactor i
  constructor
  · rw [mul_pos_iff_of_pos_left hprod, sub_pos]
  constructor
  · rw [mul_eq_zero, or_iff_right (ne_of_gt hprod), sub_eq_zero]
    exact eq_comm
  · constructor
    · intro hmul
      by_contra hsum
      have hnonneg : 0 ≤ 1 - ∑ i, b i / (1 + b i) := by linarith
      exact (not_lt_of_ge (mul_nonneg hprod.le hnonneg)) hmul
    · intro hsum
      exact mul_neg_of_pos_of_neg hprod (sub_neg.mpr hsum)

/-- A diagonal in `(-1,0)` lies on the positive side of the reservoir polarity wall. -/
theorem unitizedRealReservoirDeterminant_pos_of_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → ℝ} (hbneg : ∀ i, b i < 0) (hblt : ∀ i, -1 < b i) :
    0 < unitizedRealReservoirDeterminant b := by
  have hfactor (i : ι) : 0 < 1 + b i := by linarith [hblt i]
  rw [unitizedRealReservoirDeterminant_eq_product_mul b
    (fun i => ne_of_gt (hfactor i))]
  apply mul_pos
  · exact Finset.prod_pos fun i hi => hfactor i
  · have hsum : ∑ i, b i / (1 + b i) ≤ 0 := by
      exact Finset.sum_nonpos fun i hi => (div_nonpos_of_nonpos_of_nonneg
        (hbneg i).le (hfactor i).le)
    linarith

/-- A positive diagonal beyond polarity index one has negative unitized determinant. -/
theorem unitizedRealReservoirDeterminant_neg_of_pos_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → ℝ} (hbpos : ∀ i, 0 < b i)
    (hsum : 1 < ∑ i, b i / (1 + b i)) :
    unitizedRealReservoirDeterminant b < 0 := by
  have hfactor (i : ι) : 0 < 1 + b i := by linarith [hbpos i]
  rw [unitizedRealReservoirDeterminant_eq_product_mul b
    (fun i => ne_of_gt (hfactor i))]
  exact mul_neg_of_pos_of_neg
    (Finset.prod_pos fun i hi => hfactor i) (sub_neg.mpr hsum)

/-- At transverse input one, the Gamma-Bockstein coefficient is a negative Möbius weight. -/
theorem primeGammaCofinalBocksteinCoefficient_one (p : Nat.Primes) :
    primeGammaCofinalBocksteinCoefficient 1 p =
      -(((p.1 : ℝ) - 1) / ((p.1 : ℝ) + 1)) := by
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  simp only [primeGammaCofinalBocksteinCoefficient,
    primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherDensity_eq]
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (p.1 : ℝ)), Real.rpow_one]
  field_simp [hp0]
  ring

/-- Positive weight exposed by reflecting the transverse-one Gamma-Bockstein coefficient. -/
def primeGammaBocksteinUnitWeight (p : Nat.Primes) : ℝ :=
  ((p.1 : ℝ) - 1) / ((p.1 : ℝ) + 1)

theorem primeGammaCofinalBocksteinCoefficient_one_eq_neg_weight
    (p : Nat.Primes) :
    primeGammaCofinalBocksteinCoefficient 1 p =
      -primeGammaBocksteinUnitWeight p := by
  exact primeGammaCofinalBocksteinCoefficient_one p

theorem primeGammaBocksteinUnitWeight_pos (p : Nat.Primes) :
    0 < primeGammaBocksteinUnitWeight p := by
  have hp1 : (1 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  exact div_pos (sub_pos.mpr hp1) (by positivity)

theorem primeGammaBocksteinUnitWeight_lt_one (p : Nat.Primes) :
    primeGammaBocksteinUnitWeight p < 1 := by
  have hp1 : (1 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  rw [primeGammaBocksteinUnitWeight, div_lt_one (by positivity)]
  linarith

/-- Exact contribution of one reflected prime to the reservoir polarity index. -/
theorem primeGammaBocksteinUnitWeight_ratio_eq (p : Nat.Primes) :
    primeGammaBocksteinUnitWeight p /
        (1 + primeGammaBocksteinUnitWeight p) =
      ((p.1 : ℝ) - 1) / (2 * (p.1 : ℝ)) := by
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hp1 : (p.1 : ℝ) + 1 ≠ 0 := by positivity
  rw [primeGammaBocksteinUnitWeight]
  field_simp [hp0, hp1]
  ring

private theorem primeGammaBocksteinUnitWeight_ratio_uniformlyPositive
    (p : Nat.Primes) :
    (1 / 4 : ℝ) ≤ primeGammaBocksteinUnitWeight p /
      (1 + primeGammaBocksteinUnitWeight p) := by
  rw [primeGammaBocksteinUnitWeight_ratio_eq]
  have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
  have hp0 : 0 < 2 * (p.1 : ℝ) := by positivity
  rw [le_div_iff₀ hp0]
  nlinarith

/-- Every forward transverse-one prime packet has positive unitized determinant. -/
theorem unitized_primeBockstein_positive (m : ℕ) :
    0 < unitizedRealReservoirDeterminant
      (preDivisorRiggedPrimeRealBocksteinVector m) := by
  apply unitizedRealReservoirDeterminant_pos_of_neg
    (preDivisorRiggedPrimeRealBocksteinVector_neg m)
  intro i
  rw [preDivisorRiggedPrimeRealBocksteinVector,
    primeGammaCofinalBocksteinCoefficient_one_eq_neg_weight]
  linarith [primeGammaBocksteinUnitWeight_lt_one (nthPrimePoint i)]

/-- Cofinal reflected prime packets lie strictly beyond the rank-one polarity wall. -/
theorem primeBockstein_reflected_ratio_sum_gt_one
    {m : ℕ} (hm : 2 ≤ m) :
    1 < ∑ i : Fin (m + 3),
      primeGammaBocksteinUnitWeight (nthPrimePoint i) /
        (1 + primeGammaBocksteinUnitWeight (nthPrimePoint i)) := by
  have hconst :
      1 < ∑ _i : Fin (m + 3), (1 / 4 : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hm5 : (5 : ℝ) ≤ (m + 3 : ℕ) := by exact_mod_cast (by omega : 5 ≤ m + 3)
    nlinarith
  exact hconst.trans_le (Finset.sum_le_sum fun i hi =>
    primeGammaBocksteinUnitWeight_ratio_uniformlyPositive (nthPrimePoint i))

/-- Every sufficiently large reflected transverse-one packet has negative unitized determinant. -/
theorem unitized_reflected_primeBockstein_negative
    {m : ℕ} (hm : 2 ≤ m) :
    unitizedRealReservoirDeterminant
      (-(preDivisorRiggedPrimeRealBocksteinVector m)) < 0 := by
  have hb_eq :
      -(preDivisorRiggedPrimeRealBocksteinVector m) =
        fun i : Fin (m + 3) =>
          primeGammaBocksteinUnitWeight (nthPrimePoint i) := by
    funext i
    rw [Pi.neg_apply, preDivisorRiggedPrimeRealBocksteinVector,
      primeGammaCofinalBocksteinCoefficient_one_eq_neg_weight]
    simp
  rw [hb_eq]
  apply unitizedRealReservoirDeterminant_neg_of_pos_sum
  · intro i
    exact primeGammaBocksteinUnitWeight_pos _
  · exact primeBockstein_reflected_ratio_sum_gt_one hm

/-- Even entire product of the forward and reflected holomorphic unitized SC determinants. -/
def preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant
    (m : ℕ) (z : ℂ) : ℂ :=
  preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m z *
    preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m (-z)

theorem preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant_zero
    (m : ℕ) :
    preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant m 0 = 1 := by
  simp [preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant,
    preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_zero]

theorem preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant_even
    (m : ℕ) (z : ℂ) :
    preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant m (-z) =
      preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant m z := by
  simp [preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant, mul_comm]

theorem differentiable_preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant
    (m : ℕ) :
    Differentiable ℂ
      (preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant m) := by
  unfold preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant
  exact (differentiable_preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m).mul
    ((differentiable_preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m).comp
      differentiable_neg)

/-- The parity-symmetrized prime determinant has eventually negative real polarity at one. -/
theorem preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant_one_re_neg
    {m : ℕ} (hm : 2 ≤ m) :
    (preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant m 1).re < 0 := by
  have hone :=
    preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_ofReal m (1 : ℝ)
  have hnegone :=
    preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_ofReal m (-1 : ℝ)
  norm_num at hone hnegone
  rw [preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant,
    hone, hnegone]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  change unitizedRealReservoirDeterminant
      (preDivisorRiggedPrimeRealBocksteinVector m) *
    unitizedRealReservoirDeterminant
      (-(preDivisorRiggedPrimeRealBocksteinVector m)) < 0
  exact mul_neg_of_pos_of_neg
    (unitized_primeBockstein_positive m)
    (unitized_reflected_primeBockstein_negative hm)

/-- Normalized centered Xi has positive real polarity at one, unconditionally. -/
theorem normalizedXiC_one_re_pos :
    0 < (XiC (1 : ℂ) / XiC 0).re := by
  let u : ℝ → ℝ := fun t => (XiC (t : ℂ)).re
  have hucont : ContinuousOn u (Icc 0 1) := by
    exact (Complex.continuous_re.comp
      (XiC_differentiable.continuous.comp continuous_ofReal)).continuousOn
  have hune : ∀ t ∈ Icc (0 : ℝ) 1, u t ≠ 0 := by
    intro t ht hut
    have hnorm : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)
    apply XiC_ne_zero_of_norm_le_one hnorm
    apply Complex.ext
    · simpa [u] using hut
    · simpa using XiC_ofReal_im t
  have hprod : 0 < u 0 * u 1 :=
    HTGeometry.continuousOn_nonzero_endpoint_product_pos
      (by norm_num) hucont hune
  have hnum : 0 < (XiC (1 : ℂ)).re * (XiC 0).re := by
    simpa [u, mul_comm] using hprod
  have hden : 0 < (XiC 0).re ^ 2 := by
    apply sq_pos_of_ne_zero
    intro hzero
    rw [hzero, mul_zero] at hnum
    exact (lt_irrefl 0) hnum
  have him1 : (XiC (1 : ℂ)).im = 0 := by
    simpa using XiC_ofReal_im 1
  have him0 : (XiC (0 : ℂ)).im = 0 := by
    simpa using XiC_ofReal_im 0
  rw [Complex.div_re, him1, him0]
  simpa [Complex.normSq_apply, him0, pow_two] using div_pos hnum hden

/-- **Parity-symmetrized unitization no-go.**  Evenness, entireness, and center normalization do
not repair the coefficient-faithful SC unitization: its polarity at one is eventually opposite to
that of normalized centered Xi. -/
theorem not_tendstoLocallyUniformly_normalizedXiC_of_paritySymmetrizedUnitization :
    ¬ TendstoLocallyUniformly
      preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant
      (fun z => XiC z / XiC 0) atTop := by
  intro hconv
  have hconvOn : TendstoLocallyUniformlyOn
      preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant
      (fun z => XiC z / XiC 0) atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr hconv
  have hpoint := hconvOn.tendsto_at (Set.mem_univ (1 : ℂ))
  have hre : Tendsto
      (fun m =>
        (preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant m 1).re)
      atTop (nhds (XiC (1 : ℂ) / XiC 0).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hpoint
  have hevent : ∀ᶠ m : ℕ in atTop,
      (preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant m 1).re ≤ 0 := by
    filter_upwards [eventually_ge_atTop 2] with m hm
    exact (preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant_one_re_neg hm).le
  have hle : (XiC (1 : ℂ) / XiC 0).re ≤ 0 := le_of_tendsto hre hevent
  exact (not_lt_of_ge hle) normalizedXiC_one_re_pos

end
end RHTower
