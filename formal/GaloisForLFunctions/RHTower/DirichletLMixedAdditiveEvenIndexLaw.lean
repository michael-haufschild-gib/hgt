import GaloisForLFunctions.RHTower.DirichletLMixedAdditiveZeroAbscissaLaw

/-!
# Even-index Hermitian additive projection

The unrestricted mixed Cauchy power is already formalized in
`DirichletLMixedAdditiveZeroAbscissaLaw`.  This module proves the genuinely new connector: the
order-two character projector extracts the even output indices while remaining the sum of the
Hermitian Abel values at `r` and `-r`.  It also records the dyadic Gram parallelogram identity used
for completely multiplicative coefficient sequences.

No Dirichlet character, Mellin continuation, zero-abscissa, or RH assertion is postulated here.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- Exact order-two projection of the Hermitian additive Cauchy power onto even output indices.
The left side is the sum of two radial Hermitian squares; the right side is twice the even-index
Abel series. -/
theorem add_pos_neg_hermitianAbel_eq_two_mul_tsum_evenIndex
    (a : ℕ → ℂ) (r : ℝ)
    (ha : Summable (fun N : ℕ => ‖a N * (r : ℂ) ^ N‖)) (k : ℕ) :
    (∑' N : ℕ, a N * (r : ℂ) ^ N) ^ k *
          (starRingEnd ℂ) ((∑' N : ℕ, a N * (r : ℂ) ^ N) ^ k) +
        (∑' N : ℕ, a N * (-(r : ℂ)) ^ N) ^ k *
          (starRingEnd ℂ) ((∑' N : ℕ, a N * (-(r : ℂ)) ^ N) ^ k) =
      2 * ∑' q : ℕ,
        mixedAdditiveConvolutionPower a k (2 * q) * (r : ℂ) ^ (2 * q) := by
  have haNeg : Summable (fun N : ℕ => ‖a N * (-(r : ℂ)) ^ N‖) := by
    convert ha using 1
    funext N
    simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hplus :=
    pow_mul_star_pow_eq_tsum_mixedAdditiveConvolutionPower_mul_pow
      a (r : ℂ) (by simp) ha k
  have hminus :=
    pow_mul_star_pow_eq_tsum_mixedAdditiveConvolutionPower_mul_pow
      a (-(r : ℂ)) (by simp) haNeg k
  let c : ℕ → ℂ := fun N =>
    mixedAdditiveConvolutionPower a k N * (r : ℂ) ^ N
  let d : ℕ → ℂ := fun N =>
    mixedAdditiveConvolutionPower a k N * (-(r : ℂ)) ^ N
  have hc : Summable c := by
    exact (summable_norm_mixedAdditiveConvolutionPower_mul_pow
      a (r : ℂ) ha k).of_norm
  have hd : Summable d := by
    exact (summable_norm_mixedAdditiveConvolutionPower_mul_pow
      a (-(r : ℂ)) haNeg k).of_norm
  have hcEven : Summable (fun q : ℕ => c (2 * q)) := by
    refine (hc.comp_injective (by
        intro x y h
        exact Nat.mul_left_cancel (by norm_num) h)).congr fun _ => rfl
  have hcOdd : Summable (fun q : ℕ => c (2 * q + 1)) := by
    refine (hc.comp_injective (by
        intro x y h
        have hmul : 2 * x = 2 * y := Nat.add_right_cancel h
        exact Nat.mul_left_cancel (by norm_num) hmul)).congr fun _ => rfl
  have hdEven : Summable (fun q : ℕ => d (2 * q)) := by
    refine (hd.comp_injective (by
        intro x y h
        exact Nat.mul_left_cancel (by norm_num) h)).congr fun _ => rfl
  have hdOdd : Summable (fun q : ℕ => d (2 * q + 1)) := by
    refine (hd.comp_injective (by
        intro x y h
        have hmul : 2 * x = 2 * y := Nat.add_right_cancel h
        exact Nat.mul_left_cancel (by norm_num) hmul)).congr fun _ => rfl
  have hcSplit := tsum_even_add_odd hcEven hcOdd
  have hdSplit := tsum_even_add_odd hdEven hdOdd
  have hEvenEq : (∑' q : ℕ, d (2 * q)) = ∑' q : ℕ, c (2 * q) := by
    apply tsum_congr
    intro q
    have he : (-1 : ℂ) ^ (2 * q) = 1 := (even_two_mul q).neg_one_pow
    change mixedAdditiveConvolutionPower a k (2 * q) * (-(r : ℂ)) ^ (2 * q) =
      mixedAdditiveConvolutionPower a k (2 * q) * (r : ℂ) ^ (2 * q)
    rw [neg_pow, he, one_mul]
  have hOddEq : (∑' q : ℕ, d (2 * q + 1)) = -(∑' q : ℕ, c (2 * q + 1)) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro q
    have ho : (-1 : ℂ) ^ (2 * q + 1) = -1 := (odd_two_mul_add_one q).neg_one_pow
    change mixedAdditiveConvolutionPower a k (2 * q + 1) *
        (-(r : ℂ)) ^ (2 * q + 1) =
      -(mixedAdditiveConvolutionPower a k (2 * q + 1) *
        (r : ℂ) ^ (2 * q + 1))
    rw [neg_pow, ho, neg_one_mul]
    ring
  rw [hplus, hminus]
  change (∑' N : ℕ, c N) + ∑' N : ℕ, d N = 2 * ∑' q : ℕ, c (2 * q)
  rw [← hcSplit, ← hdSplit, hEvenEq, hOddEq]
  ring

/-- The even-index Hermitian Abel series has nonnegative real part.  This is the formal parity
positivity surface used before the paper-level Mellin pole argument. -/
theorem re_tsum_evenIndex_mixedAdditiveConvolutionPower_nonneg
    (a : ℕ → ℂ) (r : ℝ)
    (ha : Summable (fun N : ℕ => ‖a N * (r : ℂ) ^ N‖)) (k : ℕ) :
    0 ≤ (∑' q : ℕ,
      mixedAdditiveConvolutionPower a k (2 * q) * (r : ℂ) ^ (2 * q)).re := by
  have h := add_pos_neg_hermitianAbel_eq_two_mul_tsum_evenIndex a r ha k
  rw [Complex.mul_conj', Complex.mul_conj'] at h
  have hre := congrArg Complex.re h
  norm_cast at hre
  simp only [Complex.mul_re] at hre
  norm_num at hre
  nlinarith [sq_nonneg ‖(∑' N : ℕ, a N * (r : ℂ) ^ N) ^ k‖,
    sq_nonneg ‖(∑' N : ℕ, a N * (-(r : ℂ)) ^ N) ^ k‖]

/-- Pure algebra behind the completely multiplicative dyadic Gram law.  Substituting
`y = 2 * c * z - x` turns the average of the two Hermitian squares into the sum of two adjacent
dyadic squares. -/
theorem hermitian_dyadic_parallelogram (x c z : ℂ) :
    x * (starRingEnd ℂ) x +
        (2 * c * z - x) * (starRingEnd ℂ) (2 * c * z - x) =
      2 * ((x - c * z) * (starRingEnd ℂ) (x - c * z) +
        (c * z) * (starRingEnd ℂ) (c * z)) := by
  simp only [map_sub, map_mul, map_ofNat]
  ring

/-- Even/odd generating-function split: `A(x) = E(x²) + x·O(x²)`, where `E` and `O` are the
even- and odd-index Abel series.  The summand is kept folded so the even/odd tsum split unifies
cheaply. -/
theorem generatingFunction_even_odd_split (a : ℕ → ℂ) (x : ℂ)
    (hx : Summable (fun N : ℕ => ‖a N * x ^ N‖)) :
    (∑' N : ℕ, a N * x ^ N)
      = (∑' q : ℕ, a (2 * q) * (x ^ (2 : ℕ)) ^ q)
        + x * ∑' q : ℕ, a (2 * q + 1) * (x ^ (2 : ℕ)) ^ q := by
  set f : ℕ → ℂ := fun N => a N * x ^ N with hf
  have hs : Summable f := hx.of_norm
  have hE : Summable (fun q : ℕ => f (2 * q)) :=
    hs.comp_injective (by intro p q h; exact Nat.mul_left_cancel (by norm_num) h)
  have hO : Summable (fun q : ℕ => f (2 * q + 1)) :=
    hs.comp_injective (by
      intro p q h
      exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel h))
  rw [← tsum_even_add_odd hE hO]
  congr 1
  · apply tsum_congr; intro q; rw [hf]; simp only []; rw [pow_mul]
  · rw [← tsum_mul_left]; apply tsum_congr; intro q; rw [hf]; simp only []
    rw [pow_succ, pow_mul]; ring

/-- **Binary even-index parity Gram decomposition (equation (13)).**  For `k = 1` the even-index
Hermitian Abel series is the exact sum of two adjacent parity squares:
`∑_q R₁(2q) r^{2q} = |E(r²)|² + r²·|O(r²)|²`, with `E`, `O` the even/odd Abel series.  Sharper than
mere radial nonnegativity: the even channel is an exact parity Gram decomposition. -/
theorem tsum_evenIndex_binary_eq_evenOddGram (a : ℕ → ℂ) (r : ℝ)
    (ha : Summable (fun N : ℕ => ‖a N * (r : ℂ) ^ N‖)) :
    (∑' q : ℕ, mixedAdditiveConvolutionPower a 1 (2 * q) * (r : ℂ) ^ (2 * q))
      = (∑' q : ℕ, a (2 * q) * ((r : ℂ) ^ (2 : ℕ)) ^ q)
          * (starRingEnd ℂ) (∑' q : ℕ, a (2 * q) * ((r : ℂ) ^ (2 : ℕ)) ^ q)
        + (r : ℂ) ^ (2 : ℕ) * ((∑' q : ℕ, a (2 * q + 1) * ((r : ℂ) ^ (2 : ℕ)) ^ q)
          * (starRingEnd ℂ) (∑' q : ℕ, a (2 * q + 1) * ((r : ℂ) ^ (2 : ℕ)) ^ q)) := by
  have haNeg : Summable (fun N : ℕ => ‖a N * (-(r : ℂ)) ^ N‖) := by
    convert ha using 1; funext N
    simp only [norm_mul, norm_pow, norm_neg]
  have hAr := generatingFunction_even_odd_split a (r : ℂ) ha
  have hAnegr := generatingFunction_even_odd_split a (-(r : ℂ)) haNeg
  rw [show (-(r : ℂ)) ^ (2 : ℕ) = (r : ℂ) ^ (2 : ℕ) from by ring] at hAnegr
  have hproj := add_pos_neg_hermitianAbel_eq_two_mul_tsum_evenIndex a r ha 1
  simp only [pow_one] at hproj
  rw [hAr, hAnegr] at hproj
  have hconj : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  simp only [map_add, map_mul, map_neg, hconj] at hproj
  linear_combination -hproj / 2

end

end RHTower
