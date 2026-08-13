import GaloisForLFunctions.RHTower.XiWardSourceWindowMultiplicity

/-!
# Multiscale Hellinger--Cauchy positive-shift separator

The dyadic horizontal semigroup difference `exp (-a r) - exp (-2 a r)`, integrated across all
logarithmic scales, has closed Gram kernel

`log (((a + 2b) (2a + b)) / (2 (a + b)^2))`.

For positive shifts every mixed entry is strictly positive, while each self-entry is the same
constant `log (9/8)`, independently of shift size. Tensoring with the positive vertical Cauchy
kernel therefore yields an all-depth finite-packet energy whose diagonal charges multiplicity and
whose off-diagonal terms cannot cancel it. Critical displacement is totalized to zero.

The module proves this zero-side separator and its exact three-quarters receiver unconditionally.
It does not assert the missing prime--Gamma source upper bound for the resulting all-scale energy.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Closed Frullani kernel of the dyadic horizontal semigroup difference. -/
def dyadicHellingerHorizontalKernel (a b : ℝ) : ℝ :=
  if a = 0 ∨ b = 0 then 0
  else Real.log (((a + 2 * b) * (2 * a + b)) / (2 * (a + b) ^ 2))

theorem dyadicHellingerHorizontalKernel_zero_left (b : ℝ) :
    dyadicHellingerHorizontalKernel 0 b = 0 := by
  simp [dyadicHellingerHorizontalKernel]

theorem dyadicHellingerHorizontalKernel_zero_right (a : ℝ) :
    dyadicHellingerHorizontalKernel a 0 = 0 := by
  simp [dyadicHellingerHorizontalKernel]

theorem dyadicHellingerHorizontalKernel_symm (a b : ℝ) :
    dyadicHellingerHorizontalKernel a b =
      dyadicHellingerHorizontalKernel b a := by
  by_cases ha : a = 0
  · simp [ha, dyadicHellingerHorizontalKernel]
  by_cases hb : b = 0
  · simp [hb, dyadicHellingerHorizontalKernel]
  rw [dyadicHellingerHorizontalKernel, dyadicHellingerHorizontalKernel,
    if_neg (not_or_intro ha hb), if_neg (not_or_intro hb ha)]
  congr 1
  ring

theorem dyadicHellingerHorizontalKernel_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < dyadicHellingerHorizontalKernel a b := by
  rw [dyadicHellingerHorizontalKernel,
    if_neg (not_or_intro ha.ne' hb.ne')]
  apply Real.log_pos
  have hab : 0 < a + b := add_pos ha hb
  have hden : 0 < 2 * (a + b) ^ 2 := by positivity
  rw [lt_div_iff₀ hden]
  nlinarith [mul_pos ha hb]

theorem dyadicHellingerHorizontalKernel_self
    {a : ℝ} (ha : 0 < a) :
    dyadicHellingerHorizontalKernel a a = Real.log (9 / 8 : ℝ) := by
  rw [dyadicHellingerHorizontalKernel,
    if_neg (not_or_intro ha.ne' ha.ne')]
  congr 1
  field_simp [ha.ne']
  ring

/-- Real Gram kernel of vertically damped characters. -/
def dampedVerticalCauchyKernel (h delta : ℝ) : ℝ :=
  h / (h ^ 2 + delta ^ 2)

theorem dampedVerticalCauchyKernel_pos
    {h : ℝ} (hh : 0 < h) (delta : ℝ) :
    0 < dampedVerticalCauchyKernel h delta := by
  rw [dampedVerticalCauchyKernel]
  exact div_pos hh (by nlinarith [sq_pos_of_pos hh, sq_nonneg delta])

/-- Tensor product of horizontal dyadic Hellinger and vertical Cauchy Gram kernels. -/
def multiscaleHellingerCauchyKernel
    (h a b delta : ℝ) : ℝ :=
  dyadicHellingerHorizontalKernel a b *
    dampedVerticalCauchyKernel h delta

theorem multiscaleHellingerCauchyKernel_pos
    {h a b : ℝ} (hh : 0 < h) (ha : 0 < a) (hb : 0 < b)
    (delta : ℝ) :
    0 < multiscaleHellingerCauchyKernel h a b delta := by
  exact mul_pos (dyadicHellingerHorizontalKernel_pos ha hb)
    (dampedVerticalCauchyKernel_pos hh delta)

theorem multiscaleHellingerCauchyKernel_self
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    multiscaleHellingerCauchyKernel h a a 0 =
      Real.log (9 / 8 : ℝ) / h := by
  rw [multiscaleHellingerCauchyKernel,
    dyadicHellingerHorizontalKernel_self ha,
    dampedVerticalCauchyKernel]
  field_simp [hh.ne']
  ring

/-- Finite multiplicity-exact energy of the multiscale separator. -/
def finiteMultiscaleHellingerCauchyEnergy
    {n : ℕ} (h : ℝ) (a gamma : Fin n → ℝ) (m : Fin n → ℕ) : ℝ :=
  ∑ j, ∑ k,
    (m j : ℝ) * (m k : ℝ) *
      multiscaleHellingerCauchyKernel h (a j) (a k) (gamma j - gamma k)

theorem finiteMultiscaleHellingerCauchyEnergy_nonneg
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) :
    0 ≤ finiteMultiscaleHellingerCauchyEnergy h a gamma m := by
  rw [finiteMultiscaleHellingerCauchyEnergy]
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (multiscaleHellingerCauchyKernel_pos hh (ha j) (ha k) _).le

/-- Every positive horizontal shift contributes the same `log(9/8)/h` diagonal quantum;
all mixed entries are nonnegative. -/
theorem finiteMultiscaleHellingerCauchyEnergy_ge_diagonal
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) :
    (Real.log (9 / 8 : ℝ) / h) * ∑ j, (m j : ℝ) ^ 2 ≤
      finiteMultiscaleHellingerCauchyEnergy h a gamma m := by
  rw [finiteMultiscaleHellingerCauchyEnergy]
  calc
    (Real.log (9 / 8 : ℝ) / h) * ∑ j, (m j : ℝ) ^ 2 =
        ∑ j, (m j : ℝ) * (m j : ℝ) *
          multiscaleHellingerCauchyKernel h (a j) (a j)
            (gamma j - gamma j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [sub_self, multiscaleHellingerCauchyKernel_self hh (ha j)]
      ring
    _ ≤ ∑ j, ∑ k,
        (m j : ℝ) * (m k : ℝ) *
          multiscaleHellingerCauchyKernel h (a j) (a k)
            (gamma j - gamma k) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.single_le_sum
        (f := fun k =>
          (m j : ℝ) * (m k : ℝ) *
            multiscaleHellingerCauchyKernel h (a j) (a k)
              (gamma j - gamma k))
        (fun k _ => mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (multiscaleHellingerCauchyKernel_pos hh (ha j) (ha k) _).le)
        (Finset.mem_univ j)

/-- Multiplicity-faithful all-depth separator. No lower depth cutoff is needed. -/
theorem sum_multiplicity_le_multiscaleHellingerCauchyEnergy
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) :
    (∑ j, (m j : ℝ)) ≤
      (h / Real.log (9 / 8 : ℝ)) *
        finiteMultiscaleHellingerCauchyEnergy h a gamma m := by
  have hlog : 0 < Real.log (9 / 8 : ℝ) := Real.log_pos (by norm_num)
  have hdiag := finiteMultiscaleHellingerCauchyEnergy_ge_diagonal
    (gamma := gamma) hh m ha
  have hmass_sq : (∑ j, (m j : ℝ)) ≤ ∑ j, (m j : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hm0 : m j = 0
    · simp [hm0]
    · have hmone : (1 : ℝ) ≤ m j := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
      have hmnonneg : (0 : ℝ) ≤ m j := by positivity
      nlinarith
  have hdiag_scaled :
      Real.log (9 / 8 : ℝ) * ∑ j, (m j : ℝ) ^ 2 ≤
        h * finiteMultiscaleHellingerCauchyEnergy h a gamma m := by
    have hmul := mul_le_mul_of_nonneg_left hdiag hh.le
    calc
      Real.log (9 / 8 : ℝ) * ∑ j, (m j : ℝ) ^ 2 =
          h * ((Real.log (9 / 8 : ℝ) / h) * ∑ j, (m j : ℝ) ^ 2) := by
        field_simp [hh.ne']
      _ ≤ h * finiteMultiscaleHellingerCauchyEnergy h a gamma m := hmul
  have hmass_scaled :
      Real.log (9 / 8 : ℝ) * ∑ j, (m j : ℝ) ≤
        h * finiteMultiscaleHellingerCauchyEnergy h a gamma m :=
    (mul_le_mul_of_nonneg_left hmass_sq hlog.le).trans hdiag_scaled
  rw [show (h / Real.log (9 / 8 : ℝ)) *
      finiteMultiscaleHellingerCauchyEnergy h a gamma m =
      (h * finiteMultiscaleHellingerCauchyEnergy h a gamma m) /
        Real.log (9 / 8 : ℝ) by ring]
  exact (le_div_iff₀ hlog).2 (by simpa [mul_comm] using hmass_scaled)

/-- Actual strict-right Xi packets satisfy the all-depth count law with unit weights. -/
theorem xiRight_card_le_multiscaleHellingerCauchyEnergy
    {n : ℕ} {h : ℝ} (hh : 0 < h) (q : Fin n → XiRightUpperZeroCopy) :
    (n : ℝ) ≤
      (h / Real.log (9 / 8 : ℝ)) *
        finiteMultiscaleHellingerCauchyEnergy h
          (fun j => (xiRightCenteredZero (q j).1).re)
          (fun j => (xiRightCenteredZero (q j).1).im)
          (fun _ => 1) := by
  have h := sum_multiplicity_le_multiscaleHellingerCauchyEnergy hh
    (m := fun _ : Fin n => 1)
    (a := fun j => (xiRightCenteredZero (q j).1).re)
    (gamma := fun j => (xiRightCenteredZero (q j).1).im)
    (fun j => xiRightCenteredZero_re_pos (q j).1)
  simpa using h

/-- Exact `75%` receiver for the multiscale all-depth energy. -/
theorem three_quarters_line_of_multiscaleHellingerCauchyEnergy
    {N N₀ R h E : ℝ} (_hN : 0 ≤ N)
    (hsplit : N = N₀ + 2 * R)
    (hsep : R ≤ (h / Real.log (9 / 8 : ℝ)) * E)
    (hbudget : (h / Real.log (9 / 8 : ℝ)) * E ≤ N / 8) :
    3 * N / 4 ≤ N₀ := by
  nlinarith

end

end RHTower
