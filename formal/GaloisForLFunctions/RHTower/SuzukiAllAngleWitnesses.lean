import GaloisForLFunctions.RHTower.SuzukiFiniteApertureHermiteBiehler

/-!
# All-angle reality is a modulus separation, and the Cayley powers realize it

The all-angle real-zero interface quantifies over the whole unitary circle of the characteristic
pencil `A + uE`.  Since `A z + u E z = 0` is solvable in a unimodular `u` exactly when
`‖A z‖ = ‖E z‖`, the interface is equivalent to the pointwise separation
`‖A z‖ ≠ ‖E z‖` off the real axis.

That criterion is checkable, and the Cayley powers `A = (z - i) ^ n`, `E = (z + i) ^ n` satisfy it
for every `n ≠ 0`, because `i` and `-i` are equidistant from a point only on the real axis.  These
pairs are Schwarz-reflected, so every Cayley power is a Hermite--Biehler function and carries the
whole finite-aperture Livšic surface with no interface premise.
-/

namespace GaloisForLFunctions.RHTower

open Complex

/-- **All-angle reality is a modulus separation.**  The unitary pencil has a nonreal zero exactly
where the two characteristic moduli agree. -/
theorem suzukiAllAngleRealZeros_iff_norm_ne (A E : ℂ → ℂ) :
    SuzukiAllAngleRealZeros A E ↔ ∀ z : ℂ, z.im ≠ 0 → ‖A z‖ ≠ ‖E z‖ := by
  constructor
  · intro h z hz hnorm
    by_cases hE : E z = 0
    · have hA : A z = 0 := by
        have hzero : ‖A z‖ = 0 := by rw [hnorm, hE, norm_zero]
        exact norm_eq_zero.mp hzero
      exact hz (h 1 norm_one z (by simp [suzukiCharacteristicPencil, hA, hE]))
    · have hu : ‖-A z / E z‖ = 1 := by
        rw [norm_div, norm_neg, hnorm, div_self (norm_ne_zero_iff.mpr hE)]
      have hzero : suzukiCharacteristicPencil A E (-A z / E z) z = 0 := by
        unfold suzukiCharacteristicPencil
        rw [neg_div, neg_mul, div_mul_cancel₀ _ hE, add_neg_cancel]
      exact hz (h _ hu z hzero)
  · intro h u hu z hzero
    by_contra hz
    apply h z hz
    have hA : A z = -(u * E z) := by
      unfold suzukiCharacteristicPencil at hzero
      exact eq_neg_of_add_eq_zero_left hzero
    rw [hA, norm_neg, norm_mul, hu, one_mul]

/-- A strict modulus separation off the real axis realizes the interface. -/
theorem suzukiAllAngleRealZeros_of_norm_ne {A E : ℂ → ℂ}
    (h : ∀ z : ℂ, z.im ≠ 0 → ‖A z‖ ≠ ‖E z‖) :
    SuzukiAllAngleRealZeros A E :=
  (suzukiAllAngleRealZeros_iff_norm_ne A E).mpr h

/-! ## The Cayley separation -/

theorem norm_sub_I_lt_norm_add_I {z : ℂ} (hz : 0 < z.im) : ‖z - I‖ < ‖z + I‖ := by
  have hsq : ‖z - I‖ ^ 2 < ‖z + I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im]
    nlinarith [hz]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

theorem norm_add_I_lt_norm_sub_I {z : ℂ} (hz : z.im < 0) : ‖z + I‖ < ‖z - I‖ := by
  have hsq : ‖z + I‖ ^ 2 < ‖z - I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im]
    nlinarith [hz]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

theorem norm_sub_I_ne_norm_add_I {z : ℂ} (hz : z.im ≠ 0) : ‖z - I‖ ≠ ‖z + I‖ := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · exact (norm_add_I_lt_norm_sub_I hneg).ne'
  · exact (norm_sub_I_lt_norm_add_I hpos).ne

/-! ## The Cayley powers -/

theorem norm_sub_I_pow_ne_norm_add_I_pow {n : ℕ} (hn : n ≠ 0) {z : ℂ} (hz : z.im ≠ 0) :
    ‖(z - I) ^ n‖ ≠ ‖(z + I) ^ n‖ := by
  rw [norm_pow, norm_pow]
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · exact (pow_lt_pow_left₀ (norm_add_I_lt_norm_sub_I hneg) (norm_nonneg _) hn).ne'
  · exact (pow_lt_pow_left₀ (norm_sub_I_lt_norm_add_I hpos) (norm_nonneg _) hn).ne

/-- Every Cayley power pair realizes the all-angle real-zero interface. -/
theorem suzukiAllAngleRealZeros_cayleyPow {n : ℕ} (hn : n ≠ 0) :
    SuzukiAllAngleRealZeros (fun z => (z - I) ^ n) (fun z => (z + I) ^ n) :=
  suzukiAllAngleRealZeros_of_norm_ne fun _ hz =>
    norm_sub_I_pow_ne_norm_add_I_pow hn hz

/-- The Cayley powers are Schwarz reflections of each other. -/
theorem suzukiEntireSharp_addI_pow (n : ℕ) :
    suzukiEntireSharp (fun z => (z + I) ^ n) = fun z => (z - I) ^ n := by
  funext z
  unfold suzukiEntireSharp
  rw [map_pow, map_add, Complex.conj_I, Complex.conj_conj]
  ring

theorem continuous_sub_I_pow (n : ℕ) : Continuous fun z : ℂ => (z - I) ^ n := by
  fun_prop

theorem continuous_add_I_pow (n : ℕ) : Continuous fun z : ℂ => (z + I) ^ n := by
  fun_prop

theorem differentiable_sub_I_pow (n : ℕ) : Differentiable ℂ fun z : ℂ => (z - I) ^ n := by
  fun_prop

theorem differentiable_add_I_pow (n : ℕ) : Differentiable ℂ fun z : ℂ => (z + I) ^ n := by
  fun_prop

theorem sub_I_pow_I_eq_zero {n : ℕ} (hn : n ≠ 0) : ((I : ℂ) - I) ^ n = 0 := by
  rw [sub_self, zero_pow hn]

/-! ## Consequences with no interface premise -/

/-- **Every Cayley power is Hermite--Biehler.** -/
theorem suzukiHermiteBiehler_addI_pow {n : ℕ} (hn : n ≠ 0) :
    SuzukiHermiteBiehler fun z : ℂ => (z + I) ^ n := by
  refine suzukiHermiteBiehler_of_allAngleRealZeros
    (continuous_sub_I_pow n) (continuous_add_I_pow n)
    (sub_I_pow_I_eq_zero hn) (suzukiAllAngleRealZeros_cayleyPow hn) ?_
  exact (suzukiEntireSharp_addI_pow n).symm

/-- The Livšic quotient of a Cayley power pair lies strictly inside the unit disk on the upper
half-plane, with no interface premise. -/
theorem norm_suzukiLivsicQuotient_cayleyPow_lt_one {n : ℕ} (hn : n ≠ 0)
    {z : ℂ} (hz : 0 < z.im) :
    ‖suzukiLivsicQuotient (fun w => (w - I) ^ n) (fun w => (w + I) ^ n) z‖ < 1 :=
  norm_suzukiLivsicQuotient_lt_one (continuous_sub_I_pow n) (continuous_add_I_pow n)
    (sub_I_pow_I_eq_zero hn) (suzukiAllAngleRealZeros_cayleyPow hn) hz

/-- The Cayley-power Livšic quotient obeys the aperture-uniform Schwarz--Pick bound, with no
interface premise. -/
theorem norm_suzukiLivsicQuotient_cayleyPow_le_lineCayley {n : ℕ} (hn : n ≠ 0)
    {z : ℂ} (hz : 0 < z.im) :
    ‖suzukiLivsicQuotient (fun w => (w - I) ^ n) (fun w => (w + I) ^ n) z‖ ≤
      ‖GaloisForLFunctions.HTGeometry.lineCayley z‖ :=
  norm_suzukiLivsicQuotient_le_lineCayley (differentiable_sub_I_pow n)
    (differentiable_add_I_pow n) (sub_I_pow_I_eq_zero hn)
    (suzukiAllAngleRealZeros_cayleyPow hn) hz

/-- The Herglotz property of the anchored Cayley inverse, with no interface premise. -/
theorem suzukiHerglotz_cayleyPow_im_nonneg {n : ℕ} (hn : n ≠ 0)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (suzukiHerglotz (fun w => (w - I) ^ n) (fun w => (w + I) ^ n) z).im :=
  suzukiHerglotz_im_nonneg (continuous_sub_I_pow n) (continuous_add_I_pow n)
    (sub_I_pow_I_eq_zero hn) (suzukiAllAngleRealZeros_cayleyPow hn) hz

/-- The linear Cayley pair has real zeros for every unitary characteristic angle. -/
theorem suzukiAllAngleRealZeros_cayleyLinear :
    SuzukiAllAngleRealZeros (fun z : ℂ => z - I) (fun z => z + I) := by
  simpa using (suzukiAllAngleRealZeros_cayleyPow (n := 1) one_ne_zero)

/-- The linear Cayley factor is Hermite--Biehler. -/
theorem suzukiHermiteBiehler_addI_linear :
    SuzukiHermiteBiehler (fun z : ℂ => z + I) := by
  simpa using (suzukiHermiteBiehler_addI_pow (n := 1) one_ne_zero)

/-- The quadratic Cayley pair has real zeros for every unitary characteristic angle. -/
theorem suzukiAllAngleRealZeros_cayleyQuadratic :
    SuzukiAllAngleRealZeros (fun z : ℂ => (z - I) ^ 2) (fun z => (z + I) ^ 2) := by
  simpa using (suzukiAllAngleRealZeros_cayleyPow (n := 2) (by norm_num))

/-- The quadratic Cayley factor is Hermite--Biehler. -/
theorem suzukiHermiteBiehler_addI_quadratic :
    SuzukiHermiteBiehler (fun z : ℂ => (z + I) ^ 2) := by
  simpa using (suzukiHermiteBiehler_addI_pow (n := 2) (by norm_num))

end GaloisForLFunctions.RHTower
