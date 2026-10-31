import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorPlancherel

/-!
# Positive autocorrelation weights for Ramanujan modes

The Ramanujan lag Gram matrix is the sum of primitive Fourier squares.
A finite signed source therefore has nonnegative compressed conductor
weights. Exact shifted orthogonality identifies those same weights with
complete-period square masses of the smoothed modes.
-/

open Finset
open scoped ComplexConjugate
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence RenormalizedBiarithmeticGeometry ArithmeticEffectivityTheory
  TransThresholdPairCorrelation
noncomputable section


private theorem unit_power_mul_conj_re {z : ℂ} (hz : ‖z‖ = 1) (i j : ℕ) :
    (z ^ i * conj (z ^ j)).re = (z ^ (Nat.dist i j)).re := by
  have hunit (a : ℕ) : z ^ a * conj (z ^ a) = 1 := by
    rw [Complex.mul_conj', norm_pow, hz]
    norm_num
  rcases le_total j i with hji | hij
  · have hi : i = (i - j) + j := (Nat.sub_add_cancel hji).symm
    rw [Nat.dist_eq_sub_of_le_right hji]
    calc
      _ = ((z ^ (i - j) * z ^ j) * conj (z ^ j)).re := by rw [← pow_add, ← hi]
      _ = (z ^ (i - j)).re := by rw [mul_assoc, hunit, mul_one]
  · have hj : j = (j - i) + i := (Nat.sub_add_cancel hij).symm
    have hswap : (z ^ i * conj (z ^ j)).re = (z ^ j * conj (z ^ i)).re := by
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [hswap, Nat.dist_eq_sub_of_le hij]
    calc
      _ = ((z ^ (j - i) * z ^ i) * conj (z ^ i)).re := by rw [← pow_add, ← hj]
      _ = (z ^ (j - i)).re := by rw [mul_assoc, hunit, mul_one]

/-- A Ramanujan lag Gram matrix is exactly the square mass of the primitive Fourier coefficients. -/
theorem sum_ramanujanLagCoefficient_dist_eq_normSq {k : ℕ} (hk : 0 < k)
    (S : Finset ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ S, ∑ j ∈ S, a i * a j * ramanujanLagCoefficient k (Nat.dist i j)) =
      ∑ z ∈ primitiveRoots k ℂ, Complex.normSq (∑ i ∈ S, (a i : ℂ) * z ^ i) := by
  have hlag (i j : ℕ) : ramanujanLagCoefficient k (Nat.dist i j) =
      ∑ z ∈ primitiveRoots k ℂ, (z ^ i * conj (z ^ j)).re := by
    have he := congrArg Complex.re (ramanujanSum_eq_ramanujanLagCoefficient hk (Nat.dist i j))
    rw [Complex.ofReal_re] at he
    rw [← he, ramanujanSum, Complex.re_sum]
    apply sum_congr rfl
    intro z hz
    have hzNorm : ‖z‖ = 1 := ((mem_primitiveRoots hk).mp hz).norm'_eq_one hk.ne'
    exact (unit_power_mul_conj_re hzNorm i j).symm
  have hgram (z : ℂ) : (∑ i ∈ S, ∑ j ∈ S,
      a i * a j * (z ^ i * conj (z ^ j)).re) =
        Complex.normSq (∑ i ∈ S, (a i : ℂ) * z ^ i) := by
    have he := congrArg Complex.re (Complex.mul_conj (∑ i ∈ S, (a i : ℂ) * z ^ i))
    rw [Complex.ofReal_re] at he
    rw [← he, map_sum, sum_mul]
    simp only [mul_sum, Complex.re_sum, map_mul, Complex.conj_ofReal]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [show (a i : ℂ) * z ^ i * ((a j : ℂ) * conj (z ^ j)) =
      ((a i * a j : ℝ) : ℂ) * (z ^ i * conj (z ^ j)) by push_cast; ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S, ∑ z ∈ primitiveRoots k ℂ,
        a i * a j * (z ^ i * conj (z ^ j)).re := by simp_rw [hlag, mul_sum]
    _ = ∑ i ∈ S, ∑ z ∈ primitiveRoots k ℂ, ∑ j ∈ S,
        a i * a j * (z ^ i * conj (z ^ j)).re := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ z ∈ primitiveRoots k ℂ, ∑ i ∈ S, ∑ j ∈ S,
        a i * a j * (z ^ i * conj (z ^ j)).re := by rw [sum_comm]
    _ = _ := sum_congr rfl fun z _ => hgram z

/-- The compression of a finite source autocorrelation to conductor `k`. -/
def ramanujanAutocorrelationWeight (S : Finset ℕ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ S, ∑ j ∈ S, a i * a j * ramanujanLagCoefficient k (Nat.dist i j)) /
    (k.totient : ℝ)

/-- Autocorrelation gives nonnegative conductor weights, even for signed sources. -/
theorem ramanujanAutocorrelationWeight_nonneg (S : Finset ℕ) (a : ℕ → ℝ) (k : ℕ) :
    0 ≤ ramanujanAutocorrelationWeight S a k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [ramanujanAutocorrelationWeight]
  · rw [ramanujanAutocorrelationWeight, sum_ramanujanLagCoefficient_dist_eq_normSq hk]
    exact div_nonneg (sum_nonneg fun z _ => Complex.normSq_nonneg _) (Nat.cast_nonneg _)

private theorem shifted_ramanujanSum_gram {k l M : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hkM : k ∣ M) (hlM : l ∣ M) (i j : ℕ) :
    (∑ n ∈ range M, ramanujanSum k (n + i) * ramanujanSum l (n + j)) =
      if k = l then (M : ℂ) * ∑ z ∈ primitiveRoots k ℂ, z ^ i * (z⁻¹) ^ j else 0 := by
  have hterm (z w : ℂ) (n : ℕ) :
      z ^ (n + i) * w ^ (n + j) = (z * w) ^ n * (z ^ i * w ^ j) := by
    rw [pow_add, pow_add, mul_pow]
    ring
  have hpow : ∀ z ∈ primitiveRoots k ℂ, ∀ w ∈ primitiveRoots l ℂ, (z * w) ^ M = 1 := by
    intro z hz w hw
    have hz' := (mem_primitiveRoots hk).mp hz
    have hw' := (mem_primitiveRoots hl).mp hw
    rw [mul_pow, (hz'.pow_eq_one_iff_dvd M).mpr hkM,
      (hw'.pow_eq_one_iff_dvd M).mpr hlM, one_mul]
  have he : (∑ n ∈ range M, ramanujanSum k (n + i) * ramanujanSum l (n + j)) =
      ∑ z ∈ primitiveRoots k ℂ, ∑ w ∈ primitiveRoots l ℂ,
        (if z * w = 1 then (M : ℂ) else 0) * (z ^ i * w ^ j) := by
    simp only [ramanujanSum, sum_mul_sum, hterm]
    rw [sum_comm]
    apply sum_congr rfl
    intro z hz
    rw [sum_comm]
    apply sum_congr rfl
    intro w hw
    rw [← sum_mul, sum_range_pow_of_pow_eq_one (hpow z hz w hw)]
  rw [he]
  split_ifs with hkl
  · subst l
    rw [mul_sum]
    apply sum_congr rfl
    intro z hz
    have hz' := (mem_primitiveRoots hk).mp hz
    rw [sum_eq_single z⁻¹]
    · rw [if_pos (mul_inv_cancel₀ (hz'.ne_zero hk.ne'))]
    · intro w _ hne
      rw [if_neg (fun h => hne (eq_inv_of_mul_eq_one_right h)), zero_mul]
    · intro hn
      exact False.elim (hn ((mem_primitiveRoots hk).mpr hz'.inv))
  · apply sum_eq_zero
    intro z hz
    apply sum_eq_zero
    intro w hw
    rw [if_neg, zero_mul]
    intro h
    have hz' := (mem_primitiveRoots hk).mp hz
    have hw' := (mem_primitiveRoots hl).mp hw
    rw [eq_inv_of_mul_eq_one_right h] at hw'
    exact hkl (hz'.inv.unique hw')

/-- Exact shifted orthogonality: only equal conductors retain the source autocorrelation. -/
theorem sum_range_ramanujanLagCoefficient_shift_mul {k l M : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hkM : k ∣ M) (hlM : l ∣ M) (i j : ℕ) :
    (∑ n ∈ range M,
      ramanujanLagCoefficient k (n + i) * ramanujanLagCoefficient l (n + j)) =
      if k = l then (M : ℝ) * ramanujanLagCoefficient k (Nat.dist i j) else 0 := by
  have he := congrArg Complex.re (shifted_ramanujanSum_gram hk hl hkM hlM i j)
  simp only [ramanujanSum_eq_ramanujanLagCoefficient hk,
    ramanujanSum_eq_ramanujanLagCoefficient hl, ← Complex.ofReal_mul,
    Complex.re_sum, Complex.ofReal_re] at he
  by_cases hkl : k = l
  · subst l
    simp only [ite_true] at he
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.re_sum] at he
    have hs : (∑ z ∈ primitiveRoots k ℂ, (z ^ i * (z⁻¹) ^ j).re) =
        ramanujanLagCoefficient k (Nat.dist i j) := by
      calc
        _ = ∑ z ∈ primitiveRoots k ℂ, (z ^ Nat.dist i j).re := by
          apply sum_congr rfl
          intro z hz
          have hzNorm := ((mem_primitiveRoots hk).mp hz).norm'_eq_one hk.ne'
          have hc : conj z = z⁻¹ := eq_inv_of_mul_eq_one_right (by
            rw [Complex.mul_conj', hzNorm]
            norm_num)
          rw [← hc, ← map_pow]
          exact unit_power_mul_conj_re hzNorm i j
        _ = _ := by
          simpa only [ramanujanSum, Complex.re_sum, Complex.ofReal_re] using
            congrArg Complex.re (ramanujanSum_eq_ramanujanLagCoefficient hk (Nat.dist i j))
    simpa only [hs, ite_true] using he
  · simpa only [if_neg hkl, Complex.zero_re] using he

/-- The finite source weight is also an exact complete-period square mass. -/
theorem ramanujanAutocorrelationWeight_eq_period_squares {k : ℕ} (hk : 0 < k)
    (S : Finset ℕ) (a : ℕ → ℝ) :
    ramanujanAutocorrelationWeight S a k =
      (1 / ((k : ℝ) * k.totient)) * ∑ n ∈ range k,
        (∑ i ∈ S, a i * ramanujanLagCoefficient k (n + i)) ^ 2 := by
  have he : (∑ n ∈ range k, (∑ i ∈ S, a i * ramanujanLagCoefficient k (n + i)) ^ 2) =
      (k : ℝ) * ∑ i ∈ S, ∑ j ∈ S,
        a i * a j * ramanujanLagCoefficient k (Nat.dist i j) := by
    calc
      _ = ∑ n ∈ range k, ∑ i ∈ S, ∑ j ∈ S,
          a i * a j * (ramanujanLagCoefficient k (n + i) *
            ramanujanLagCoefficient k (n + j)) := by
        apply sum_congr rfl
        intro n _
        rw [pow_two, sum_mul]
        apply sum_congr rfl
        intro i _
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = ∑ i ∈ S, ∑ j ∈ S, a i * a j *
          (∑ n ∈ range k, ramanujanLagCoefficient k (n + i) *
            ramanujanLagCoefficient k (n + j)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        rw [sum_comm]
        simp only [mul_sum]
      _ = _ := by
        simp only [sum_range_ramanujanLagCoefficient_shift_mul hk hk dvd_rfl dvd_rfl,
          ite_true]
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
  rw [he, ramanujanAutocorrelationWeight]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hphi : (k.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hk).ne'
  field_simp [hkR, hphi]

/-- Smoothing by a finite signed source on integer translates. -/
def finiteSourceSmoothing (S : Finset ℕ) (a F : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ S, a i * F (n + i)

theorem finiteSourceSmoothing_sum (S : Finset ℕ) (a : ℕ → ℝ)
    (T : Finset ℕ) (F : ℕ → ℕ → ℝ) (n : ℕ) :
    finiteSourceSmoothing S a (fun k => ∑ j ∈ T, F j k) n =
      ∑ j ∈ T, finiteSourceSmoothing S a (F j) n := by
  simp only [finiteSourceSmoothing, mul_sum]
  rw [sum_comm]

theorem finiteSourceSmoothing_const_mul (S : Finset ℕ) (a F : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    finiteSourceSmoothing S a (fun k => c * F k) n = c * finiteSourceSmoothing S a F n := by
  rw [finiteSourceSmoothing, finiteSourceSmoothing, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

/-- The smoothed complete-period Gram remains diagonal, with its actual autocorrelation weights. -/
theorem sum_range_smoothedRamanujan_mul {k l M : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hkM : k ∣ M) (hlM : l ∣ M)
    (S : Finset ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ range M,
      finiteSourceSmoothing S a (ramanujanLagCoefficient k) n *
        finiteSourceSmoothing S a (ramanujanLagCoefficient l) n) =
      if k = l then (M : ℝ) * l.totient * ramanujanAutocorrelationWeight S a l else 0 := by
  have he : (∑ n ∈ range M,
      finiteSourceSmoothing S a (ramanujanLagCoefficient k) n *
        finiteSourceSmoothing S a (ramanujanLagCoefficient l) n) =
      ∑ i ∈ S, ∑ j ∈ S, a i * a j *
        (if k = l then (M : ℝ) * ramanujanLagCoefficient k (Nat.dist i j) else 0) := by
    calc
      _ = ∑ n ∈ range M, ∑ i ∈ S, ∑ j ∈ S,
          a i * a j * (ramanujanLagCoefficient k (n + i) *
            ramanujanLagCoefficient l (n + j)) := by
        apply sum_congr rfl
        intro n _
        rw [finiteSourceSmoothing, finiteSourceSmoothing, sum_mul]
        apply sum_congr rfl
        intro i _
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = ∑ i ∈ S, ∑ j ∈ S, a i * a j *
          (∑ n ∈ range M, ramanujanLagCoefficient k (n + i) *
            ramanujanLagCoefficient l (n + j)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        rw [sum_comm]
        simp only [mul_sum]
      _ = _ := by simp_rw [sum_range_ramanujanLagCoefficient_shift_mul hk hl hkM hlM]
  rw [he]
  by_cases hkl : k = l
  · subst l
    simp only [ite_true]
    have hp : (k.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hk).ne'
    have hc : (M : ℝ) * k.totient * ramanujanAutocorrelationWeight S a k =
        (M : ℝ) * ∑ i ∈ S, ∑ j ∈ S,
          a i * a j * ramanujanLagCoefficient k (Nat.dist i j) := by
      rw [ramanujanAutocorrelationWeight]
      field_simp [hp]
    rw [hc, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  · simp only [if_neg hkl, mul_zero, sum_const_zero]

#print axioms sum_ramanujanLagCoefficient_dist_eq_normSq
#print axioms ramanujanAutocorrelationWeight_nonneg
#print axioms sum_range_ramanujanLagCoefficient_shift_mul
#print axioms ramanujanAutocorrelationWeight_eq_period_squares
#print axioms sum_range_smoothedRamanujan_mul
end
end GaloisForLFunctions.SuccessorShellArithmetic
