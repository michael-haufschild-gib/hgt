import GaloisForLFunctions.RHTower.CCM.CCMShannonFourierFactorization
import GaloisForLFunctions.RHTower.CCM.CCMPublishedRestrictedWeilParityBlocks

/-!
# Real Fourier zeros of a simple odd ground of the published parity packet

The cross-frequency block of the centered parity frames is the explicit inclusion-times-mode
matrix, so its squared frequency is the diagonal matrix of squared modes and its `delta` vector is
`√2` times the mode.  Consequently the finite-matrix resolvent numerator of the odd ground is, up
to the nonvanishing characteristic determinant, the first-order Fourier resolvent

`∑_{j=-N}^{N} ξ_j /(z − j)`

of the centered coefficient vector.  Combining this with the reality of the numerator zeros and
with the Shannon factorization of the band-limited Fourier transform gives the finite odd
theorem: the trigonometric polynomial of a simple odd ground has only real Fourier zeros.
-/

open Matrix Complex Filter Topology
open scoped Matrix ComplexOrder

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ## Explicit values of the centered clock and of the parity frames -/

@[simp] theorem ccmParityCenteredClock_none (N : ℕ) : ccmParityCenteredClock N none = 0 := by
  simp [ccmParityCenteredClock, ccmParityCenteredMode]

@[simp] theorem ccmParityCenteredClock_false (N : ℕ) (l : Fin N) :
    ccmParityCenteredClock N (some (l, false)) = (((l : ℕ) + 1 : ℕ) : ℝ) := by
  simp [ccmParityCenteredClock, ccmParityCenteredMode]

@[simp] theorem ccmParityCenteredClock_true (N : ℕ) (l : Fin N) :
    ccmParityCenteredClock N (some (l, true)) = -(((l : ℕ) + 1 : ℕ) : ℝ) := by
  simp [ccmParityCenteredClock, ccmParityCenteredMode]

@[simp] theorem ccmEvenParityFrame_none_none (N : ℕ) :
    ccmEvenParityFrame N none none = 1 := rfl

@[simp] theorem ccmEvenParityFrame_none_some (N : ℕ) (l : Fin N) :
    ccmEvenParityFrame N none (some l) = 0 := rfl

@[simp] theorem ccmEvenParityFrame_some_none (N : ℕ) (l : Fin N) (b : Bool) :
    ccmEvenParityFrame N (some (l, b)) none = 0 := rfl

@[simp] theorem ccmEvenParityFrame_some_some (N : ℕ) (l m : Fin N) (b : Bool) :
    ccmEvenParityFrame N (some (l, b)) (some m)
      = if l = m then ccmParityFrameScale else 0 := rfl

@[simp] theorem star_ccmEvenParityFrame (N : ℕ) (p : CCMCenteredParityIndex N)
    (i : CCMEvenParityIndex N) :
    star (ccmEvenParityFrame N p i) = ccmEvenParityFrame N p i := by
  rcases p with _ | ⟨l, b⟩
  · rcases i with _ | m <;> simp
  · rcases i with _ | m
    · simp
    · rw [ccmEvenParityFrame_some_some]
      by_cases h : l = m <;> simp [h]

@[simp] theorem ccmOddParityFrame_none_apply (N : ℕ) (k : Fin N) :
    ccmOddParityFrame N none k = 0 := rfl

@[simp] theorem ccmOddParityFrame_false_apply (N : ℕ) (l k : Fin N) :
    ccmOddParityFrame N (some (l, false)) k
      = if l = k then ccmParityFrameScale else 0 := rfl

@[simp] theorem ccmOddParityFrame_true_apply (N : ℕ) (l k : Fin N) :
    ccmOddParityFrame N (some (l, true)) k
      = if l = k then -ccmParityFrameScale else 0 := rfl

/-! ## The cross-frequency block is inclusion times mode -/

theorem ccmPublishedParityCrossFrequency_eq_sum (N : ℕ) (i : CCMEvenParityIndex N) (k : Fin N) :
    ccmPublishedParityCrossFrequency N i k
      = ∑ p : CCMCenteredParityIndex N,
          star (ccmEvenParityFrame N p i)
            * ((ccmParityCenteredClock N p : ℂ) * ccmOddParityFrame N p k) := by
  rw [ccmPublishedParityCrossFrequency, Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.conjTranspose_apply, ccmParityClockMatrix_eq_diagonal, Matrix.diagonal_mul]

theorem ccmPublishedParityCrossFrequency_none (N : ℕ) (k : Fin N) :
    ccmPublishedParityCrossFrequency N none k = 0 := by
  rw [ccmPublishedParityCrossFrequency_eq_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rcases p with _ | ⟨l, b⟩
  · simp
  · rcases b <;> simp

theorem ccmPublishedParityCrossFrequency_some (N : ℕ) (l k : Fin N) :
    ccmPublishedParityCrossFrequency N (some l) k
      = if l = k then (((l : ℕ) + 1 : ℕ) : ℂ) else 0 := by
  have hscale : ccmParityFrameScale * ccmParityFrameScale = (1 / 2 : ℂ) := ccmParityFrameScale_sq
  rw [ccmPublishedParityCrossFrequency_eq_sum, Fintype.sum_option, Fintype.sum_prod_type]
  have hnone : star (ccmEvenParityFrame N none (some l))
      * ((ccmParityCenteredClock N none : ℂ) * ccmOddParityFrame N none k) = 0 := by
    simp
  rw [hnone, zero_add, Finset.sum_eq_single l]
  · rw [Fintype.sum_bool]
    by_cases hlk : l = k
    · subst k
      simp only [star_ccmEvenParityFrame]
      rw [ccmEvenParityFrame_some_some, ccmEvenParityFrame_some_some,
        ccmOddParityFrame_true_apply, ccmOddParityFrame_false_apply,
        if_pos (rfl : l = l), if_pos (rfl : l = l),
        ccmParityCenteredClock_true, ccmParityCenteredClock_false]
      push_cast
      linear_combination (2 * ((l : ℕ) + 1 : ℂ)) * hscale
    · simp [hlk]
  · intro l' _ hl'
    rw [Fintype.sum_bool]
    simp [hl']
  · simp

/-! ## The squared frequency and the delta vector -/

theorem ccmPublishedParity_squaredFrequency (N : ℕ) :
    (ccmPublishedParityCrossFrequency N)ᴴ * ccmPublishedParityCrossFrequency N
      = Matrix.diagonal (fun k : Fin N => ((((k : ℕ) + 1 : ℕ) : ℂ)) ^ 2) := by
  ext k k'
  rw [Matrix.mul_apply, Fintype.sum_option]
  simp only [Matrix.conjTranspose_apply, ccmPublishedParityCrossFrequency_none,
    ccmPublishedParityCrossFrequency_some, star_zero, zero_mul, zero_add]
  rw [Finset.sum_eq_single k]
  · by_cases hkk : k = k'
    · subst k'
      rw [Matrix.diagonal_apply_eq]
      simp [pow_two]
    · rw [Matrix.diagonal_apply_ne _ hkk]
      simp [hkk]
  · intro l _ hl
    simp [hl]
  · simp

theorem ccmPublishedParityEta_none (N : ℕ) : ccmPublishedParityEta N none = 1 := by
  rw [ccmPublishedParityEta]
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, mul_one]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [ccmEvenParityFrame_none_none, ccmEvenParityFrame_some_none, star_one, star_zero]
  simp

theorem ccmPublishedParityEta_some (N : ℕ) (l : Fin N) :
    ccmPublishedParityEta N (some l) = ((Real.sqrt 2 : ℝ) : ℂ) := by
  have hsqrt_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2))
  rw [ccmPublishedParityEta]
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, mul_one]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [ccmEvenParityFrame_none_some, star_zero, zero_add]
  rw [Finset.sum_eq_single l]
  · rw [Fintype.sum_bool]
    simp only [star_ccmEvenParityFrame]
    rw [ccmEvenParityFrame_some_some, ccmEvenParityFrame_some_some, if_pos (rfl : l = l),
      ccmParityFrameScale, ← two_mul, inv_eq_one_div, mul_one_div, div_eq_iff hsqrt_ne]
    linear_combination -h2
  · intro l' _ hl'
    rw [Fintype.sum_bool]
    simp [hl']
  · simp

theorem ccmPublishedParity_delta (N : ℕ) :
    (ccmPublishedParityCrossFrequency N)ᴴ *ᵥ ccmPublishedParityEta N
      = fun k : Fin N => ((Real.sqrt 2 : ℝ) : ℂ) * (((k : ℕ) + 1 : ℕ) : ℂ) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  rw [Fintype.sum_option]
  simp only [ccmPublishedParityCrossFrequency_none, star_zero, zero_mul, zero_add]
  rw [Finset.sum_eq_single k]
  · rw [ccmPublishedParityCrossFrequency_some, if_pos rfl, ccmPublishedParityEta_some]
    rw [Complex.star_def, ← Complex.ofReal_natCast, Complex.conj_ofReal]
    push_cast
    ring
  · intro l _ hl
    rw [ccmPublishedParityCrossFrequency_some, if_neg hl]
    simp
  · simp

/-! ## The centered coefficient vector of an odd ground -/

theorem two_mul_ccmParityFrameScale : 2 * ccmParityFrameScale = ((Real.sqrt 2 : ℝ) : ℂ) := by
  have hsqrt_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2))
  rw [ccmParityFrameScale, inv_eq_one_div, mul_one_div, div_eq_iff hsqrt_ne]
  linear_combination -h2

def ccmOddGroundCoeffAux (N : ℕ) (c : Fin N → ℂ) (n : ℕ) : ℂ :=
  if h : n < N then c ⟨n, h⟩ else 0

/-- The centered coefficient vector of an odd ground vector: mode `k+1` carries `c k/√2`, mode
`-(k+1)` carries its negative, and the zero mode is empty. -/
def ccmOddGroundCoeff (N : ℕ) (c : Fin N → ℂ) (j : ℤ) : ℂ :=
  if 0 < j then ccmParityFrameScale * ccmOddGroundCoeffAux N c (j.toNat - 1)
  else if j < 0 then -(ccmParityFrameScale * ccmOddGroundCoeffAux N c ((-j).toNat - 1))
  else 0

theorem ccmOddGroundCoeff_zero (N : ℕ) (c : Fin N → ℂ) : ccmOddGroundCoeff N c 0 = 0 := by
  rw [ccmOddGroundCoeff, if_neg (by omega), if_neg (by omega)]

theorem ccmOddGroundCoeff_odd (N : ℕ) (c : Fin N → ℂ) (j : ℤ) :
    ccmOddGroundCoeff N c (-j) = -ccmOddGroundCoeff N c j := by
  rcases lt_trichotomy j 0 with h | h | h
  · rw [ccmOddGroundCoeff, ccmOddGroundCoeff, if_pos (by omega), if_neg (by omega),
      if_pos h, neg_neg]
  · subst h
    rw [neg_zero, ccmOddGroundCoeff_zero, neg_zero]
  · rw [ccmOddGroundCoeff, ccmOddGroundCoeff, if_neg (by omega), if_pos h, if_pos (by omega),
      neg_neg]

theorem ccmOddGroundCoeffAux_coe (N : ℕ) (c : Fin N → ℂ) (k : Fin N) :
    ccmOddGroundCoeffAux N c (k : ℕ) = c k := by
  rw [ccmOddGroundCoeffAux, dif_pos k.isLt]

theorem ccmOddGroundCoeff_pos_aux (N : ℕ) (c : Fin N → ℂ) (n : ℕ) :
    ccmOddGroundCoeff N c ((n : ℤ) + 1) = ccmParityFrameScale * ccmOddGroundCoeffAux N c n := by
  have hidx : (((n : ℤ) + 1).toNat - 1) = n := by omega
  rw [ccmOddGroundCoeff, if_pos (by omega), hidx]

theorem ccmOddGroundCoeff_neg_aux (N : ℕ) (c : Fin N → ℂ) (n : ℕ) :
    ccmOddGroundCoeff N c (-((n : ℤ) + 1))
      = -(ccmParityFrameScale * ccmOddGroundCoeffAux N c n) := by
  rw [ccmOddGroundCoeff_odd, ccmOddGroundCoeff_pos_aux]

/-! ## Nonvanishing of the shifted modes off the real axis -/

theorem ccmMode_sq_sub_ne_zero (n : ℕ) {z : ℂ} (him : z.im ≠ 0) :
    ((n : ℂ) + 1) ^ 2 - z ^ 2 ≠ 0 := by
  intro hcon
  have hz2 : z ^ 2 = ((n : ℂ) + 1) ^ 2 := by linear_combination -hcon
  have hmim : ((((n : ℂ)) + 1) ^ 2).im = 0 := by
    simp [pow_two, Complex.mul_im]
  have hmre : ((((n : ℂ)) + 1) ^ 2).re = ((n : ℝ) + 1) ^ 2 := by
    simp [pow_two, Complex.mul_re]
  have him2 : (z ^ 2).im = 2 * (z.re * z.im) := by
    simp [pow_two, Complex.mul_im]
    ring
  have hre2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp [pow_two, Complex.mul_re]
  have hzero : 2 * (z.re * z.im) = 0 := by rw [← him2, hz2, hmim]
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.1 (by linarith : z.re * z.im = 0) with h | h
    · exact h
    · exact absurd h him
  have hval : z.re ^ 2 - z.im ^ 2 = ((n : ℝ) + 1) ^ 2 := by
    rw [← hre2, hz2, hmre]
  rw [hre0] at hval
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  nlinarith [sq_nonneg z.im]

theorem ccmMode_sub_ne_zero {n : ℕ} {z : ℂ} (him : z.im ≠ 0) :
    z - (((n : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := by
  intro hcon
  apply him
  have := congrArg Complex.im hcon
  simpa using this

theorem ccmMode_add_ne_zero {n : ℕ} {z : ℂ} (him : z.im ≠ 0) :
    z - ((-((n : ℤ) + 1) : ℤ) : ℂ) ≠ 0 := by
  intro hcon
  apply him
  have := congrArg Complex.im hcon
  simpa using this

/-! ## The first-order Fourier resolvent of an odd ground -/

theorem sum_ccmOddGroundCoeff_eq (N : ℕ) (c : Fin N → ℂ) {z : ℂ} (him : z.im ≠ 0) :
    ∑ j ∈ ccmModeWindow N, ccmOddGroundCoeff N c j / (z - (j : ℂ))
      = -∑ k : Fin N, ((Real.sqrt 2 : ℝ) : ℂ) * (((k : ℕ) : ℂ) + 1) * c k
          / (((((k : ℕ) : ℂ) + 1)) ^ 2 - z ^ 2) := by
  have hconv : ∑ k : Fin N, ((Real.sqrt 2 : ℝ) : ℂ) * (((k : ℕ) : ℂ) + 1) * c k
        / (((((k : ℕ) : ℂ) + 1)) ^ 2 - z ^ 2)
      = ∑ n ∈ Finset.range N, ((Real.sqrt 2 : ℝ) : ℂ) * ((n : ℂ) + 1)
          * ccmOddGroundCoeffAux N c n / (((n : ℂ) + 1) ^ 2 - z ^ 2) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun n : ℕ => ((Real.sqrt 2 : ℝ) : ℂ) * ((n : ℂ) + 1) * ccmOddGroundCoeffAux N c n
        / (((n : ℂ) + 1) ^ 2 - z ^ 2)) N]
    exact Finset.sum_congr rfl fun k _ => by rw [ccmOddGroundCoeffAux_coe]
  rw [sum_ccmModeWindow_eq, ccmOddGroundCoeff_zero,
    show ((0 : ℤ) : ℂ) = 0 by norm_num, zero_div, zero_add, hconv, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ccmOddGroundCoeff_pos_aux, ccmOddGroundCoeff_neg_aux]
  have hm1 : z - (((n : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := ccmMode_sub_ne_zero him
  have hm2 : z - ((-((n : ℤ) + 1) : ℤ) : ℂ) ≠ 0 := ccmMode_add_ne_zero him
  have hm3 : (((n : ℂ)) + 1) ^ 2 - z ^ 2 ≠ 0 := ccmMode_sq_sub_ne_zero n him
  push_cast at hm1 hm2 ⊢
  rw [← two_mul_ccmParityFrameScale]
  field_simp
  ring

/-! ## The resolvent numerator of a published odd ground -/

theorem ccmPublishedParity_squaredFrequency' (N : ℕ) :
    (ccmPublishedParityCrossFrequency N)ᴴ * ccmPublishedParityCrossFrequency N
      = Matrix.diagonal (fun k : Fin N => (((k : ℕ) : ℂ) + 1) ^ 2) := by
  rw [ccmPublishedParity_squaredFrequency]
  congr 1
  funext k
  push_cast
  ring

theorem ccmPublishedParity_delta' (N : ℕ) :
    (ccmPublishedParityCrossFrequency N)ᴴ *ᵥ ccmPublishedParityEta N
      = fun k : Fin N => ((Real.sqrt 2 : ℝ) : ℂ) * (((k : ℕ) : ℂ) + 1) := by
  rw [ccmPublishedParity_delta]
  funext k
  push_cast
  ring

theorem ccmModeShift_det_ne_zero {N : ℕ} {z : ℂ} (him : z.im ≠ 0) :
    (Matrix.diagonal (fun k : Fin N => (((k : ℕ) : ℂ) + 1) ^ 2 - z ^ 2)).det ≠ 0 := by
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun k _ => ccmMode_sq_sub_ne_zero (k : ℕ) him

theorem ccmModeShift_inv {N : ℕ} {z : ℂ} (him : z.im ≠ 0) :
    (Matrix.diagonal (fun k : Fin N => (((k : ℕ) : ℂ) + 1) ^ 2 - z ^ 2))⁻¹
      = Matrix.diagonal (fun k : Fin N => ((((k : ℕ) : ℂ) + 1) ^ 2 - z ^ 2)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  ext k k'
  by_cases h : k = k'
  · subst k'
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      mul_inv_cancel₀ (ccmMode_sq_sub_ne_zero (k : ℕ) him)]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem ccmPublishedParity_squaredFrequency_shift {N : ℕ}
    (S : CCMParityFreeOddGroundData (CCMEvenParityIndex N) (Fin N))
    (hfreq : S.frequency = ccmPublishedParityCrossFrequency N) (z : ℂ) :
    S.squaredFrequency - z ^ 2 • (1 : Matrix (Fin N) (Fin N) ℂ)
      = Matrix.diagonal (fun k : Fin N => (((k : ℕ) : ℂ) + 1) ^ 2 - z ^ 2) := by
  rw [CCMParityFreeOddGroundData.squaredFrequency, hfreq, ccmPublishedParity_squaredFrequency']
  ext k k'
  by_cases h : k = k'
  · subst k'
    rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h,
      Matrix.smul_apply, Matrix.one_apply_ne h, smul_eq_mul, mul_zero, sub_zero]

theorem ccmPublishedParity_squaredResolventNumerator_eq {N : ℕ} {c : Fin N → ℂ}
    (S : CCMParityFreeOddGroundData (CCMEvenParityIndex N) (Fin N))
    (hfreq : S.frequency = ccmPublishedParityCrossFrequency N)
    (heta : S.eta = ccmPublishedParityEta N)
    (hground : S.ground = c) {z : ℂ} (him : z.im ≠ 0) :
    S.squaredResolventNumerator (z ^ 2)
      = -((Matrix.diagonal (fun k : Fin N => (((k : ℕ) : ℂ) + 1) ^ 2 - z ^ 2)).det
          * ∑ j ∈ ccmModeWindow N, ccmOddGroundCoeff N c j / (z - (j : ℂ))) := by
  have hdelta : star S.delta
      = fun k : Fin N => ((Real.sqrt 2 : ℝ) : ℂ) * (((k : ℕ) : ℂ) + 1) := by
    rw [CCMParityFreeOddGroundData.delta, hfreq, heta, ccmPublishedParity_delta']
    funext k
    simp
  rw [CCMParityFreeOddGroundData.squaredResolventNumerator,
    ccmPublishedParity_squaredFrequency_shift S hfreq z, ccmModeShift_inv him, hground,
    sum_ccmOddGroundCoeff_eq N c him, mul_neg, neg_neg, hdelta]
  congr 1
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_eq_mul_inv]
  ring

/-- **The finite odd theorem.**  The band-limited trigonometric polynomial of a simple odd ground
of the published parity packet has only real Fourier zeros. -/
theorem ccmPublishedParityOddGround_compactFourier_zero_im_eq_zero {N : ℕ} {c : Fin N → ℂ}
    (S : CCMParityFreeOddGroundData (CCMEvenParityIndex N) (Fin N))
    (hfreq : S.frequency = ccmPublishedParityCrossFrequency N)
    (heta : S.eta = ccmPublishedParityEta N)
    (hground : S.ground = c) {z : ℂ}
    (hzero : compactFourier (ccmTrigPoly N (ccmOddGroundCoeff N c)) 0 (2 * Real.pi) z = 0) :
    z.im = 0 := by
  by_contra him
  have hsum := sum_eq_zero_of_compactFourier_ccmTrigPoly_eq_zero
    (ccmOddGroundCoeff_odd N c) him hzero
  have hnum : S.oddFourierResolventNumerator z = 0 := by
    rw [CCMParityFreeOddGroundData.oddFourierResolventNumerator,
      ccmPublishedParity_squaredResolventNumerator_eq S hfreq heta hground him, hsum,
      mul_zero, neg_zero]
  have hreg : IsUnit (S.squaredFrequency - z ^ 2 • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by
    rw [ccmPublishedParity_squaredFrequency_shift S hfreq z]
    exact isUnit_iff_ne_zero.2 (ccmModeShift_det_ne_zero him)
  exact him (S.oddFourierResolventNumerator_zero_im_eq_zero hreg hnum)

/-! ## The packaged finite theorem and its analytic limit -/

theorem ccmParityFreeOddGroundData_compactFourier_zero_im_eq_zero {N : ℕ}
    (S : CCMParityFreeOddGroundData (CCMEvenParityIndex N) (Fin N))
    (hfreq : S.frequency = ccmPublishedParityCrossFrequency N)
    (heta : S.eta = ccmPublishedParityEta N) {z : ℂ}
    (hzero :
      compactFourier (ccmTrigPoly N (ccmOddGroundCoeff N S.ground)) 0 (2 * Real.pi) z = 0) :
    z.im = 0 :=
  ccmPublishedParityOddGround_compactFourier_zero_im_eq_zero S hfreq heta rfl hzero

/-- **Every aperture has an unconditional positive semidefinite spectral-floor shift whose simple
odd ground has a real-rooted band-limited Fourier transform.** -/
theorem exists_ccmPublishedParityGroundShift_oddGroundRealFourierZeros (a : ℝ) (N : ℕ) :
    ∃ mu : ℝ,
      (ccmPublishedParityShift a mu N).PosSemidef ∧
      (∃ c : CCMCenteredParityIndex N → ℂ,
        ccmPublishedParityShift a mu N *ᵥ c = 0 ∧ c ≠ 0) ∧
      (CCMPublishedSimpleOddGroundBranch a mu N →
        ∃ S : CCMParityFreeOddGroundData (CCMEvenParityIndex N) (Fin N),
          S.Qminus = ccmPublishedParityOddBlock a mu N ∧
          ∀ z : ℂ,
            compactFourier (ccmTrigPoly N (ccmOddGroundCoeff N S.ground)) 0 (2 * Real.pi) z = 0 →
              z.im = 0) := by
  obtain ⟨mu, hT, hkernel, hbranch⟩ := exists_ccmPublishedParityGroundShift_simpleOddAdapter a N
  refine ⟨mu, hT, hkernel, fun hsimple => ?_⟩
  obtain ⟨S, _, hQm, hfreq, heta, _⟩ := hbranch hsimple
  exact ⟨S, hQm, fun z hz =>
    ccmParityFreeOddGroundData_compactFourier_zero_im_eq_zero S hfreq heta hz⟩

/-- **The parity-free simple-ground Fourier real-zero law.**  A mean-square limit of odd grounds of
published parity packets, with a nonvanishing Fourier transform, again has only real Fourier
zeros. -/
theorem ccmOddGroundLimit_compactFourier_zero_im_eq_zero
    {N : ℕ → ℕ} (S : ∀ n : ℕ, CCMParityFreeOddGroundData (CCMEvenParityIndex (N n)) (Fin (N n)))
    (hfreq : ∀ n, (S n).frequency = ccmPublishedParityCrossFrequency (N n))
    (heta : ∀ n, (S n).eta = ccmPublishedParityEta (N n))
    (f : ℝ → ℂ) (hf : Continuous f)
    (hmean : Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(2 * Real.pi),
        ‖ccmTrigPoly (N n) (ccmOddGroundCoeff (N n) (S n).ground) x - f x‖ ^ 2) atTop (nhds 0))
    {w z : ℂ} (hw : compactFourier f 0 (2 * Real.pi) w ≠ 0)
    (hz : compactFourier f 0 (2 * Real.pi) z = 0) :
    z.im = 0 := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  refine compactFourier_limit_zero_im_eq_zero_of_meanSquare
    (fun n => ccmTrigPoly (N n) (ccmOddGroundCoeff (N n) (S n).ground)) f
    (fun n => continuous_ccmTrigPoly _ _) hf hpi hmean ?_ hw hz
  intro n u hu
  exact ccmParityFreeOddGroundData_compactFourier_zero_im_eq_zero (S n) (hfreq n) (heta n) hu

end

end RHTower
