import GaloisForLFunctions.RHTower.XiWardMultiscaleHellingerCauchySeparator

/-!
# Cubic log-moment Hellinger--Cauchy separator

Replacing the dilation-invariant horizontal measure `dr/r` by the cubic log-moment measure
`r^(2 : ℕ) dr` suppresses high Euler frequencies while strengthening the zero-side response near the
critical line.  The closed horizontal Gram is positive on every pair of positive shifts and has
self-charge `115 / (864 a^(3 : ℕ))`.  Since every strict-right centered Xi zero has `a < 1/2`, each copy
therefore costs at least `115 / 108`, uniformly and with increasing cost as `a -> 0+`.

This module proves the finite-packet census and exact `75%` receiver.  The companion Euler module
proves that the same cubic diagonal is summable on the literal balanced primitive source.
-/

open scoped BigOperators
open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Closed positive form of the cubic log-moment Gram
`integral r^(2 : ℕ) (exp (-a r) - exp (-2 a r)) (exp (-b r) - exp (-2 b r)) dr`.
Critical displacement is totalized to zero. -/
def cubicLogMomentHellingerHorizontalKernel (a b : ℝ) : ℝ :=
  if a = 0 ∨ b = 0 then 0
  else
    9 * (a * b) *
        (20 * (a + b) ^ 4 + 6 * (a + b) ^ 2 * (a * b) + (a * b) ^ 2) /
      (4 * (a + b) ^ 3 * (2 * (a + b) ^ 2 + a * b) ^ 3)

theorem cubicLogMomentHellingerHorizontalKernel_zero_left (b : ℝ) :
    cubicLogMomentHellingerHorizontalKernel 0 b = 0 := by
  simp [cubicLogMomentHellingerHorizontalKernel]

theorem cubicLogMomentHellingerHorizontalKernel_zero_right (a : ℝ) :
    cubicLogMomentHellingerHorizontalKernel a 0 = 0 := by
  simp [cubicLogMomentHellingerHorizontalKernel]

theorem cubicLogMomentHellingerHorizontalKernel_symm (a b : ℝ) :
    cubicLogMomentHellingerHorizontalKernel a b =
      cubicLogMomentHellingerHorizontalKernel b a := by
  by_cases ha : a = 0
  · simp [ha, cubicLogMomentHellingerHorizontalKernel]
  by_cases hb : b = 0
  · simp [hb, cubicLogMomentHellingerHorizontalKernel]
  rw [cubicLogMomentHellingerHorizontalKernel,
    cubicLogMomentHellingerHorizontalKernel,
    if_neg (not_or_intro ha hb), if_neg (not_or_intro hb ha)]
  congr 1
  all_goals ring

/-- The factorized closed form is strictly positive on positive shifts. -/
theorem cubicLogMomentHellingerHorizontalKernel_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < cubicLogMomentHellingerHorizontalKernel a b := by
  rw [cubicLogMomentHellingerHorizontalKernel,
    if_neg (not_or_intro ha.ne' hb.ne')]
  positivity

/-- Equivalent four-Laplace-term form of the cubic moment. -/
theorem cubicLogMomentHellingerHorizontalKernel_eq_laplace
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    cubicLogMomentHellingerHorizontalKernel a b =
      2 / (a + b) ^ 3 - 2 / (a + 2 * b) ^ 3 -
        2 / (2 * a + b) ^ 3 + 2 / (2 * a + 2 * b) ^ 3 := by
  rw [cubicLogMomentHellingerHorizontalKernel,
    if_neg (not_or_intro ha.ne' hb.ne')]
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  have ha2b : a + 2 * b ≠ 0 := (add_pos ha (mul_pos two_pos hb)).ne'
  have h2ab : 2 * a + b ≠ 0 := (add_pos (mul_pos two_pos ha) hb).ne'
  have h2a2b : 2 * a + 2 * b ≠ 0 :=
    (add_pos (mul_pos two_pos ha) (mul_pos two_pos hb)).ne'
  have hcore : 2 * (a + b) ^ 2 + a * b ≠ 0 := by positivity
  field_simp [hab, ha2b, h2ab, h2a2b, hcore]
  ring

private theorem integral_cubic_exp {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-(r * t))) = 2 / r ^ 3 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (3 : ℝ)) (r := r) (by norm_num) hr
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two] at h
  have hgamma : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num,
      Real.Gamma_nat_eq_factorial]
    norm_num
  rw [hgamma] at h
  norm_num at h ⊢
  rw [h]
  field_simp [hr.ne']

private theorem integrableOn_cubic_exp {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-(r * t))) (Ioi 0) := by
  have hvalue := integral_cubic_exp hr
  have hne : (∫ t : ℝ in Ioi 0,
      t ^ 2 * Real.exp (-(r * t))) ≠ 0 := by
    rw [hvalue]
    positivity
  exact Integrable.of_integral_ne_zero hne

/-- The closed kernel is exactly the cubic log-moment Gram on positive shifts. -/
theorem integral_cubicLogMomentHellingerHorizontalKernel
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ r : ℝ in Ioi 0, r ^ 2 *
      (Real.exp (-(a * r)) - Real.exp (-((2 * a) * r))) *
      (Real.exp (-(b * r)) - Real.exp (-((2 * b) * r)))) =
      cubicLogMomentHellingerHorizontalKernel a b := by
  have hab : 0 < a + b := add_pos ha hb
  have ha2b : 0 < a + 2 * b := add_pos ha (mul_pos two_pos hb)
  have h2ab : 0 < 2 * a + b := add_pos (mul_pos two_pos ha) hb
  have h2a2b : 0 < 2 * a + 2 * b :=
    add_pos (mul_pos two_pos ha) (mul_pos two_pos hb)
  have hpoint :
      (fun r : ℝ => r ^ 2 *
        (Real.exp (-(a * r)) - Real.exp (-((2 * a) * r))) *
        (Real.exp (-(b * r)) - Real.exp (-((2 * b) * r)))) =
      fun r : ℝ =>
        (r ^ 2 * Real.exp (-((a + b) * r)) -
          r ^ 2 * Real.exp (-((a + 2 * b) * r))) -
        r ^ 2 * Real.exp (-((2 * a + b) * r)) +
          r ^ 2 * Real.exp (-((2 * a + 2 * b) * r)) := by
    funext r
    rw [show -((a + b) * r) = -(a * r) + -(b * r) by ring,
      show -((a + 2 * b) * r) = -(a * r) + -((2 * b) * r) by ring,
      show -((2 * a + b) * r) = -((2 * a) * r) + -(b * r) by ring,
      show -((2 * a + 2 * b) * r) = -((2 * a) * r) + -((2 * b) * r) by ring]
    simp only [Real.exp_add]
    ring
  rw [hpoint]
  change
    (∫ r : ℝ in Ioi 0,
      (((fun t : ℝ => t ^ 2 * Real.exp (-((a + b) * t))) -
        (fun t : ℝ => t ^ 2 * Real.exp (-((a + 2 * b) * t))) -
        (fun t : ℝ => t ^ 2 * Real.exp (-((2 * a + b) * t))) +
        (fun t : ℝ => t ^ 2 * Real.exp (-((2 * a + 2 * b) * t)))) r)) = _
  simp only [Pi.add_apply, Pi.sub_apply]
  have hsum := integral_add
    ((integrableOn_cubic_exp hab).sub (integrableOn_cubic_exp ha2b) |>.sub
      (integrableOn_cubic_exp h2ab))
    (integrableOn_cubic_exp h2a2b)
  have hsubOuter := integral_sub
    ((integrableOn_cubic_exp hab).sub (integrableOn_cubic_exp ha2b))
    (integrableOn_cubic_exp h2ab)
  have hsubInner := integral_sub
    (integrableOn_cubic_exp hab) (integrableOn_cubic_exp ha2b)
  simp only [Pi.sub_apply] at hsum hsubOuter hsubInner
  rw [hsum, hsubOuter, hsubInner,
    integral_cubic_exp hab, integral_cubic_exp ha2b,
    integral_cubic_exp h2ab, integral_cubic_exp h2a2b]
  rw [cubicLogMomentHellingerHorizontalKernel_eq_laplace ha hb]

/-- Exact cubic self-charge. -/
theorem cubicLogMomentHellingerHorizontalKernel_self
    {a : ℝ} (ha : 0 < a) :
    cubicLogMomentHellingerHorizontalKernel a a = 115 / (864 * a ^ 3) := by
  rw [cubicLogMomentHellingerHorizontalKernel,
    if_neg (not_or_intro ha.ne' ha.ne')]
  field_simp [ha.ne']
  ring

/-- Every horizontal depth in the zeta strip has a fixed cubic-moment quantum. -/
theorem cubicLogMomentHellingerHorizontalKernel_self_ge
    {a : ℝ} (ha : 0 < a) (hhalf : a ≤ 1 / 2) :
    115 / 108 ≤ cubicLogMomentHellingerHorizontalKernel a a := by
  rw [cubicLogMomentHellingerHorizontalKernel_self ha]
  have hfactor :
      0 ≤ (1 / 2 - a) * ((1 / 2 : ℝ) ^ 2 + (1 / 2 : ℝ) * a + a ^ 2) := by
    apply mul_nonneg (sub_nonneg.mpr hhalf)
    nlinarith [sq_nonneg a]
  have hcube : a ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := by
    nlinarith
  have hden : 0 < 864 * a ^ 3 := by positivity
  apply (div_le_div_iff_of_pos_left (by norm_num) (by norm_num) hden).2
  norm_num at hcube
  nlinarith

/-- **Regular-landing obstruction.**  The totalized cubic self-charge is not continuous at the
critical boundary.  Hence no bounded regular source landing with a continuous diagonal matrix
coefficient can realize this separator while assigning zero charge to critical-line
multiplicity.  Source-diagonal summability alone does not imply boundary closability. -/
theorem not_continuousAt_zero_cubicLogMomentHellingerHorizontalKernel_self :
    ¬ ContinuousAt
      (fun a : ℝ => cubicLogMomentHellingerHorizontalKernel a a) 0 := by
  intro hcontinuous
  let g : ℝ → ℝ := fun a => a / (2 * (1 + a))
  let F : ℝ → ℝ := fun a =>
    cubicLogMomentHellingerHorizontalKernel (g a) (g a)
  have hg : ContinuousAt g 0 := by
    dsimp only [g]
    have hdencont : ContinuousAt (fun a : ℝ => 2 * (1 + a)) 0 :=
      continuousAt_const.mul (continuousAt_const.add continuousAt_id)
    exact continuousAt_id.div hdencont (by norm_num)
  have hF : ContinuousAt F 0 := by
    have hcomp := hcontinuous.comp_of_eq hg (by simp [g])
    change ContinuousAt
      ((fun a : ℝ => cubicLogMomentHellingerHorizontalKernel a a) ∘ g) 0
    exact hcomp
  have hF0 : F 0 = 0 := by
    simp [F, g, cubicLogMomentHellingerHorizontalKernel_zero_left]
  apply not_exists_uniform_positive_continuous_boundarySeparator F hF hF0
  refine ⟨115 / 108, by norm_num, ?_⟩
  intro a ha
  have hden : 0 < 2 * (1 + a) := by positivity
  have hgpos : 0 < g a := by
    dsimp only [g]
    positivity
  have hgle : g a ≤ 1 / 2 := by
    dsimp only [g]
    rw [div_le_iff₀ hden]
    nlinarith
  exact cubicLogMomentHellingerHorizontalKernel_self_ge hgpos hgle

/-- The positive horizontal kernel is not a function of the combined half-plane abscissa `a+b`.
In particular it cannot itself be the translation-covariant one-complex-variable Laplace kernel:
two positive pairs with the same sum have different cubic Hellinger charge. -/
theorem not_exists_cubicLogMomentHellingerHorizontalKernel_eq_fun_add :
    ¬ ∃ F : ℝ → ℝ, ∀ a b : ℝ, 0 < a → 0 < b →
      cubicLogMomentHellingerHorizontalKernel a b = F (a + b) := by
  rintro ⟨F, hF⟩
  have h11 := hF 1 1 (by norm_num) (by norm_num)
  have h13 := hF (1 / 2) (3 / 2) (by norm_num) (by norm_num)
  have hne :
      cubicLogMomentHellingerHorizontalKernel 1 1 ≠
        cubicLogMomentHellingerHorizontalKernel (1 / 2) (3 / 2) := by
    norm_num [cubicLogMomentHellingerHorizontalKernel]
  apply hne
  calc
    cubicLogMomentHellingerHorizontalKernel 1 1 = F 2 := by
      convert h11 using 1
      all_goals norm_num
    _ = cubicLogMomentHellingerHorizontalKernel (1 / 2) (3 / 2) := by
      convert h13.symm using 1
      all_goals norm_num

/-- Real cross entry of the source-compatible holomorphic cubic Laplace kernel
`2 / (x + i delta)^(3 : ℕ)`.  Unlike the horizontally split tensor kernel above, it couples abscissa
and height in one complex coordinate. -/
def holomorphicCubicLaplaceCrossKernel (x delta : ℝ) : ℝ :=
  2 * x * (x ^ 2 - 3 * delta ^ 2) / (x ^ 2 + delta ^ 2) ^ 3

/-- Source-compatible cubic weighting loses entrywise positivity as soon as the ordinate gap is
wider than `x / sqrt 3`.  Thus restoring one-variable holomorphy destroys the diagonal-discarding
argument used by the positive tensor packet. -/
theorem holomorphicCubicLaplaceCrossKernel_neg
    {x delta : ℝ} (hx : 0 < x) (hwide : x ^ 2 < 3 * delta ^ 2) :
    holomorphicCubicLaplaceCrossKernel x delta < 0 := by
  rw [holomorphicCubicLaplaceCrossKernel]
  have hden : 0 < (x ^ 2 + delta ^ 2) ^ 3 := by positivity
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (mul_pos two_pos hx) (sub_neg.mpr hwide)) hden

/-- Exact rational witness for the holomorphic cubic cross-sign obstruction. -/
theorem holomorphicCubicLaplaceCrossKernel_one_one :
    holomorphicCubicLaplaceCrossKernel 1 1 = -1 / 2 := by
  norm_num [holomorphicCubicLaplaceCrossKernel]

/-- Tensor product of the cubic horizontal Gram and vertical Cauchy Gram. -/
def cubicLogMomentHellingerCauchyKernel
    (h a b delta : ℝ) : ℝ :=
  cubicLogMomentHellingerHorizontalKernel a b *
    dampedVerticalCauchyKernel h delta

theorem cubicLogMomentHellingerCauchyKernel_pos
    {h a b : ℝ} (hh : 0 < h) (ha : 0 < a) (hb : 0 < b)
    (delta : ℝ) :
    0 < cubicLogMomentHellingerCauchyKernel h a b delta := by
  exact mul_pos (cubicLogMomentHellingerHorizontalKernel_pos ha hb)
    (dampedVerticalCauchyKernel_pos hh delta)

theorem cubicLogMomentHellingerCauchyKernel_self_ge
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (hhalf : a ≤ 1 / 2) :
    115 / (108 * h) ≤
      cubicLogMomentHellingerCauchyKernel h a a 0 := by
  have hhorizontal :=
    cubicLogMomentHellingerHorizontalKernel_self_ge ha hhalf
  have hinv : 0 ≤ 1 / h := (one_div_pos.mpr hh).le
  rw [cubicLogMomentHellingerCauchyKernel,
    dampedVerticalCauchyKernel]
  have hvertical : h / (h ^ 2 + 0 ^ 2) = 1 / h := by
    norm_num
    field_simp [hh.ne']
  rw [hvertical]
  have hmul := mul_le_mul_of_nonneg_right hhorizontal hinv
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Finite multiplicity-exact cubic log-moment energy. -/
def finiteCubicLogMomentHellingerCauchyEnergy
    {n : ℕ} (h : ℝ) (a gamma : Fin n → ℝ) (m : Fin n → ℕ) : ℝ :=
  ∑ j, ∑ k,
    (m j : ℝ) * (m k : ℝ) *
      cubicLogMomentHellingerCauchyKernel h (a j) (a k)
        (gamma j - gamma k)

theorem finiteCubicLogMomentHellingerCauchyEnergy_nonneg
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) :
    0 ≤ finiteCubicLogMomentHellingerCauchyEnergy h a gamma m := by
  rw [finiteCubicLogMomentHellingerCauchyEnergy]
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (cubicLogMomentHellingerCauchyKernel_pos hh (ha j) (ha k) _).le

/-- The positive mixed Gram cannot cancel its uniform strict-right diagonal. -/
theorem finiteCubicLogMomentHellingerCauchyEnergy_ge_diagonal
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) (hhalf : ∀ j, a j ≤ 1 / 2) :
    (115 / (108 * h)) * ∑ j, (m j : ℝ) ^ 2 ≤
      finiteCubicLogMomentHellingerCauchyEnergy h a gamma m := by
  rw [finiteCubicLogMomentHellingerCauchyEnergy]
  calc
    (115 / (108 * h)) * ∑ j, (m j : ℝ) ^ 2 =
        ∑ j, (m j : ℝ) * (m j : ℝ) * (115 / (108 * h)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j, (m j : ℝ) * (m j : ℝ) *
        cubicLogMomentHellingerCauchyKernel h (a j) (a j)
          (gamma j - gamma j) := by
      apply Finset.sum_le_sum
      intro j _
      rw [sub_self]
      exact mul_le_mul_of_nonneg_left
        (cubicLogMomentHellingerCauchyKernel_self_ge hh (ha j) (hhalf j))
        (mul_nonneg (by positivity) (by positivity))
    _ ≤ ∑ j, ∑ k,
        (m j : ℝ) * (m k : ℝ) *
          cubicLogMomentHellingerCauchyKernel h (a j) (a k)
            (gamma j - gamma k) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.single_le_sum
        (f := fun k =>
          (m j : ℝ) * (m k : ℝ) *
            cubicLogMomentHellingerCauchyKernel h (a j) (a k)
              (gamma j - gamma k))
        (fun k _ => mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (cubicLogMomentHellingerCauchyKernel_pos hh (ha j) (ha k) _).le)
        (Finset.mem_univ j)

/-- Multiplicity-faithful all-depth census with cubic Euler-frequency decay. -/
theorem sum_multiplicity_le_finiteCubicLogMomentHellingerCauchyEnergy
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) (hhalf : ∀ j, a j ≤ 1 / 2) :
    (∑ j, (m j : ℝ)) ≤
      (108 * h / 115) *
        finiteCubicLogMomentHellingerCauchyEnergy h a gamma m := by
  have hdiag := finiteCubicLogMomentHellingerCauchyEnergy_ge_diagonal
    (gamma := gamma) hh m ha hhalf
  have hmassSq : (∑ j, (m j : ℝ)) ≤ ∑ j, (m j : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hm0 : m j = 0
    · simp [hm0]
    · have hmone : (1 : ℝ) ≤ m j := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
      have hmnonneg : (0 : ℝ) ≤ m j := by positivity
      nlinarith
  have hcoefficient : 0 < 115 / (108 * h) := by positivity
  have hmassDiagonal :
      (115 / (108 * h)) * ∑ j, (m j : ℝ) ≤
        finiteCubicLogMomentHellingerCauchyEnergy h a gamma m :=
    (mul_le_mul_of_nonneg_left hmassSq hcoefficient.le).trans hdiag
  rw [show (108 * h / 115) *
      finiteCubicLogMomentHellingerCauchyEnergy h a gamma m =
      finiteCubicLogMomentHellingerCauchyEnergy h a gamma m /
        (115 / (108 * h)) by field_simp [hh.ne']]
  exact (le_div_iff₀ hcoefficient).2 (by simpa [mul_comm] using hmassDiagonal)

/-- Actual strict-right Xi packets satisfy the cubic all-depth count law. -/
theorem xiRight_card_le_finiteCubicLogMomentHellingerCauchyEnergy
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    (q : Fin n → XiRightUpperZeroCopy) :
    (n : ℝ) ≤
      (108 * h / 115) *
        finiteCubicLogMomentHellingerCauchyEnergy h
          (fun j => (xiRightCenteredZero (q j).1).re)
          (fun j => (xiRightCenteredZero (q j).1).im)
          (fun _ => 1) := by
  have h := sum_multiplicity_le_finiteCubicLogMomentHellingerCauchyEnergy
    hh (m := fun _ : Fin n => 1)
    (a := fun j => (xiRightCenteredZero (q j).1).re)
    (gamma := fun j => (xiRightCenteredZero (q j).1).im)
    (fun j => xiRightCenteredZero_re_pos (q j).1)
    (fun j => le_of_lt (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half (q j).1)).2)
  simpa using h

/-- Exact `75%` receiver for the cubic log-moment energy. -/
theorem three_quarters_line_of_cubicLogMomentHellingerCauchyEnergy
    {N N₀ R h E : ℝ} (_hN : 0 ≤ N)
    (hsplit : N = N₀ + 2 * R)
    (hsep : R ≤ (108 * h / 115) * E)
    (hbudget : (108 * h / 115) * E ≤ N / 8) :
    3 * N / 4 ≤ N₀ := by
  nlinarith

end

end RHTower
