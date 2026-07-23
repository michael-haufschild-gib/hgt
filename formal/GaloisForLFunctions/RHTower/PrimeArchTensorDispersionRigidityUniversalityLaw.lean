import GaloisForLFunctions.RHTower.LowTemperatureDispersionIdentity
import GaloisForLFunctions.RHTower.PrimeArchDualCauchyTensor

/-!
# Prime--archimedean tensor-dispersion rigidity universality law

The curvature dispersion `M₂ M₄ - M₃²` has an exact product rule on a pair-product alphabet.
For nonempty positive factors, its vanishing detects simultaneous collapse of both alphabets to
constant values.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The unweighted `M₂ M₄ - M₃²` dispersion of a finite real alphabet. -/
def finiteAlphabetDispersion {ι : Type*}
    (S : Finset ι) (x : ι → ℝ) : ℝ :=
  (∑ i ∈ S, x i ^ 2) * (∑ i ∈ S, x i ^ 4) -
    (∑ i ∈ S, x i ^ 3) ^ 2

/-- The same dispersion formed from the pair-product moments of finite prime and archimedean
alphabets. -/
def finitePrimeArchPairDispersion {ι κ : Type*}
    (P : Finset ι) (A : Finset κ) (x : ι → ℝ) (y : κ → ℝ) : ℝ :=
  finitePrimeArchPairPowerSum P A x y 2 *
      finitePrimeArchPairPowerSum P A x y 4 -
    finitePrimeArchPairPowerSum P A x y 3 ^ 2

/-- Every finite real alphabet has nonnegative power dispersion. -/
theorem finiteAlphabetDispersion_nonneg {ι : Type*}
    (S : Finset ι) (x : ι → ℝ) :
    0 ≤ finiteAlphabetDispersion S x := by
  simpa [finiteAlphabetDispersion] using
    (ZetaFisher.dispersion_nonneg (R := ℝ) S (fun _ => 1) x (by simp))

/-- For a positive alphabet, zero dispersion is equivalent to pairwise equality of all entries. -/
theorem finiteAlphabetDispersion_eq_zero_iff_constant
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 < x i) :
    finiteAlphabetDispersion S x = 0 ↔
      ∀ i ∈ S, ∀ j ∈ S, x i = x j := by
  have hid : 2 * finiteAlphabetDispersion S x =
      ∑ i ∈ S, ∑ j ∈ S, x i ^ 2 * x j ^ 2 * (x i - x j) ^ 2 := by
    simpa [finiteAlphabetDispersion] using
      (ZetaFisher.two_mul_dispersion S (fun _ => (1 : ℝ)) x)
  constructor
  · intro hzero i hi j hj
    have hsumzero :
        (∑ a ∈ S, ∑ b ∈ S, x a ^ 2 * x b ^ 2 * (x a - x b) ^ 2) = 0 := by
      rw [← hid, hzero, mul_zero]
    have houter : ∀ a ∈ S,
        0 ≤ ∑ b ∈ S, x a ^ 2 * x b ^ 2 * (x a - x b) ^ 2 := by
      intro a ha
      exact Finset.sum_nonneg fun b hb =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
    have hiZero := (Finset.sum_eq_zero_iff_of_nonneg houter).mp hsumzero i hi
    have hinner : ∀ b ∈ S,
        0 ≤ x i ^ 2 * x b ^ 2 * (x i - x b) ^ 2 := by
      intro b hb
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg hinner).mp hiZero j hj
    have hcoeff : x i ^ 2 * x j ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (hx i hi).ne') (pow_ne_zero _ (hx j hj).ne')
    have hgap : (x i - x j) ^ 2 = 0 :=
      (mul_eq_zero.mp hij).resolve_left hcoeff
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hgap)
  · intro hconstant
    have hsumzero :
        (∑ i ∈ S, ∑ j ∈ S, x i ^ 2 * x j ^ 2 * (x i - x j) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      rw [hconstant i hi j hj, sub_self, zero_pow (by norm_num), mul_zero]
    rw [hsumzero] at hid
    linarith

/-- **Tensor-dispersion product law.**  Pair-product dispersion splits into the dispersion of the
first alphabet times the second alphabet's even moment product, plus the squared third moment of
the first alphabet times the dispersion of the second. -/
theorem finitePrimeArchPairDispersion_decomposition
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : Finset ι) (A : Finset κ) (x : ι → ℝ) (y : κ → ℝ) :
    finitePrimeArchPairDispersion P A x y =
      finiteAlphabetDispersion P x *
          ((∑ j ∈ A, y j ^ 2) * (∑ j ∈ A, y j ^ 4)) +
        (∑ i ∈ P, x i ^ 3) ^ 2 * finiteAlphabetDispersion A y := by
  rw [finitePrimeArchPairDispersion,
    finitePrimeArchPairPowerSum_eq_mul P A x y 2,
    finitePrimeArchPairPowerSum_eq_mul P A x y 4,
    finitePrimeArchPairPowerSum_eq_mul P A x y 3]
  unfold finiteAlphabetDispersion
  ring

/-- **Prime--archimedean tensor-dispersion rigidity.**  For nonempty positive alphabets, pair
dispersion vanishes exactly when both factors are constant on their finite supports. -/
theorem finitePrimeArchPairDispersion_eq_zero_iff_both_constant
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : Finset ι) (A : Finset κ) (x : ι → ℝ) (y : κ → ℝ)
    (hP : P.Nonempty) (hA : A.Nonempty)
    (hx : ∀ i ∈ P, 0 < x i) (hy : ∀ j ∈ A, 0 < y j) :
    finitePrimeArchPairDispersion P A x y = 0 ↔
      (∀ i ∈ P, ∀ k ∈ P, x i = x k) ∧
        ∀ j ∈ A, ∀ l ∈ A, y j = y l := by
  have hdec := finitePrimeArchPairDispersion_decomposition P A x y
  have hDP : 0 ≤ finiteAlphabetDispersion P x :=
    finiteAlphabetDispersion_nonneg P x
  have hDA : 0 ≤ finiteAlphabetDispersion A y :=
    finiteAlphabetDispersion_nonneg A y
  have hy2 : 0 < ∑ j ∈ A, y j ^ 2 :=
    Finset.sum_pos (fun j hj => pow_pos (hy j hj) _) hA
  have hy4 : 0 < ∑ j ∈ A, y j ^ 4 :=
    Finset.sum_pos (fun j hj => pow_pos (hy j hj) _) hA
  have hx3 : 0 < ∑ i ∈ P, x i ^ 3 :=
    Finset.sum_pos (fun i hi => pow_pos (hx i hi) _) hP
  constructor
  · intro hzero
    have hsumzero :
        finiteAlphabetDispersion P x *
            ((∑ j ∈ A, y j ^ 2) * (∑ j ∈ A, y j ^ 4)) +
          (∑ i ∈ P, x i ^ 3) ^ 2 * finiteAlphabetDispersion A y = 0 := by
      rw [← hdec, hzero]
    have hfirstNonneg : 0 ≤ finiteAlphabetDispersion P x *
        ((∑ j ∈ A, y j ^ 2) * (∑ j ∈ A, y j ^ 4)) :=
      mul_nonneg hDP (mul_nonneg hy2.le hy4.le)
    have hsecondNonneg : 0 ≤
        (∑ i ∈ P, x i ^ 3) ^ 2 * finiteAlphabetDispersion A y :=
      mul_nonneg (sq_nonneg _) hDA
    have hfirstZero : finiteAlphabetDispersion P x *
        ((∑ j ∈ A, y j ^ 2) * (∑ j ∈ A, y j ^ 4)) = 0 := by
      nlinarith
    have hsecondZero :
        (∑ i ∈ P, x i ^ 3) ^ 2 * finiteAlphabetDispersion A y = 0 := by
      nlinarith
    have hDPzero : finiteAlphabetDispersion P x = 0 :=
      (mul_eq_zero.mp hfirstZero).resolve_right (mul_pos hy2 hy4).ne'
    have hDAzero : finiteAlphabetDispersion A y = 0 :=
      (mul_eq_zero.mp hsecondZero).resolve_left (sq_pos_of_pos hx3).ne'
    exact ⟨(finiteAlphabetDispersion_eq_zero_iff_constant P x hx).mp hDPzero,
      (finiteAlphabetDispersion_eq_zero_iff_constant A y hy).mp hDAzero⟩
  · rintro ⟨hxconstant, hyconstant⟩
    have hDPzero :=
      (finiteAlphabetDispersion_eq_zero_iff_constant P x hx).mpr hxconstant
    have hDAzero :=
      (finiteAlphabetDispersion_eq_zero_iff_constant A y hy).mpr hyconstant
    rw [hdec, hDPzero, hDAzero]
    ring

end

end RHTower
