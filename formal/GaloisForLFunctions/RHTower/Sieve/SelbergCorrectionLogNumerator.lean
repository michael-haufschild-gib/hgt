import GaloisForLFunctions.RHTower.Sieve.SelbergCorrectionLogLocal
import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCoefficientIdentity

/-!
# The numerator identity for the differentiated Euler correction

The local identity behind the gcd-logarithmic Selberg family reduces, after clearing the
denominator `D = 1 − XY/p`, to

`corr^{log} ∗ N = (log p / p²)·XY(X + Y − 2XY)`,  where `N = (1 − X/p)(1 − Y/p)`.

Both sides factor over the two variables, so the two-dimensional convolution collapses to the two
one-dimensional identities

`(g₂ ∗ n)(i) = [i = 2]`  and  `(g₁ ∗ n)(j) = [j = 1]`,

where `g₂ = geomTailTwo p`, `g₁ = geomTailOne p` and `n` is the local Möbius factor.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- One-dimensional additive convolution. -/
def additiveConvolution (f g : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (i + 1), f k * g (i - k)

/-- A product of one-variable factors convolves componentwise. -/
theorem additiveBivariateConvolution_product
    (f₁ f₂ g₁ g₂ : ℕ → ℝ) (i j : ℕ) :
    additiveBivariateConvolution (fun a b => f₁ a * f₂ b)
        (fun a b => g₁ a * g₂ b) i j =
      additiveConvolution f₁ g₁ i * additiveConvolution f₂ g₂ j := by
  rw [additiveBivariateConvolution, additiveConvolution, additiveConvolution,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The one-variable Möbius factor `1 − X/p`. -/
def localMoebiusFactor (p : ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 1 else if i = 1 then -(1 / (p : ℝ)) else 0

/-- Convolving with `1 − X/p` is the first difference. -/
theorem additiveConvolution_localMoebiusFactor (p : ℕ) (f : ℕ → ℝ) (i : ℕ) :
    additiveConvolution f (localMoebiusFactor p) i =
      f i - (if i = 0 then 0 else f (i - 1) / (p : ℝ)) := by
  rw [additiveConvolution]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [localMoebiusFactor]
  · have hpair : ({i - 1, i} : Finset ℕ) ⊆ Finset.range (i + 1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rw [Finset.mem_range]
      rcases hk with rfl | rfl <;> omega
    have hzero : ∀ k ∈ Finset.range (i + 1), k ∉ ({i - 1, i} : Finset ℕ) →
        f k * localMoebiusFactor p (i - k) = 0 := by
      intro k hk hkn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkn
      have hkle : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hsub : 2 ≤ i - k := by omega
      rw [localMoebiusFactor, if_neg (by omega), if_neg (by omega)]
      ring
    rw [← Finset.sum_subset hpair hzero]
    have hne : i - 1 ≠ i := by omega
    rw [Finset.sum_pair hne]
    have h1 : i - (i - 1) = 1 := by omega
    have h2 : i - i = 0 := by omega
    rw [h1, h2, localMoebiusFactor, localMoebiusFactor, if_neg (by omega),
      if_pos rfl, if_pos rfl, if_neg (by omega)]
    ring

theorem additiveConvolution_geomTailTwo {p : ℕ} (hp : 0 < p) (i : ℕ) :
    additiveConvolution (geomTailTwo p) (localMoebiusFactor p) i =
      if i = 2 then 1 else 0 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [additiveConvolution_localMoebiusFactor]
  match i with
  | 0 => simp [geomTailTwo]
  | 1 => simp [geomTailTwo]
  | 2 =>
      rw [if_neg (by omega), if_pos rfl, geomTailTwo, geomTailTwo,
        if_pos (by omega), if_neg (by omega)]
      field_simp
      ring
  | (k + 3) =>
      rw [if_neg (by omega), if_neg (by omega), geomTailTwo, geomTailTwo,
        if_pos (by omega), if_pos (by omega)]
      have hstep : k + 3 - 1 = k + 2 := by omega
      rw [hstep]
      field_simp
      ring

theorem additiveConvolution_geomTailOne {p : ℕ} (hp : 0 < p) (j : ℕ) :
    additiveConvolution (geomTailOne p) (localMoebiusFactor p) j =
      if j = 1 then 1 else 0 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [additiveConvolution_localMoebiusFactor]
  match j with
  | 0 => simp [geomTailOne]
  | 1 =>
      rw [if_neg (by omega), if_pos rfl, geomTailOne, geomTailOne,
        if_pos (by omega), if_neg (by omega)]
      field_simp
      ring
  | (k + 2) =>
      rw [if_neg (by omega), if_neg (by omega), geomTailOne, geomTailOne,
        if_pos (by omega), if_pos (by omega)]
      have hstep : k + 2 - 1 = k + 1 := by omega
      rw [hstep]
      field_simp
      ring

/-- The local Möbius numerator `N = (1 − X/p)(1 − Y/p)`. -/
def localMoebiusPairFactor (p : ℕ) (i j : ℕ) : ℝ :=
  localMoebiusFactor p i * localMoebiusFactor p j

/-- The differentiated local numerator `(log p / p²)·XY(X + Y − 2XY)`. -/
def selbergCorrectionLogNumerator (p : ℕ) (i j : ℕ) : ℝ :=
  (Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ)) *
    ((if i = 2 then (1 : ℝ) else 0) * (if j = 1 then (1 : ℝ) else 0) +
      (if i = 1 then (1 : ℝ) else 0) * (if j = 2 then (1 : ℝ) else 0) -
      2 * ((if i = 2 then (1 : ℝ) else 0) * (if j = 2 then (1 : ℝ) else 0)))

/-- **The numerator identity: `corr^{log} ∗ N = (log p/p²)·XY(X + Y − 2XY)`.** -/
theorem additiveBivariateConvolution_selbergCorrectionLogLocal_moebius
    {p : ℕ} (hp : 0 < p) (i j : ℕ) :
    additiveBivariateConvolution (selbergCorrectionLogLocal p)
        (localMoebiusPairFactor p) i j =
      selbergCorrectionLogNumerator p i j := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  set c : ℝ := Real.log (p : ℝ) * (1 / (p : ℝ) ^ (2 : ℕ)) with hc
  rw [additiveBivariateConvolution]
  have hterm : ∀ a ∈ Finset.range (i + 1),
      (∑ b ∈ Finset.range (j + 1),
        selbergCorrectionLogLocal p a b *
          localMoebiusPairFactor p (i - a) (j - b)) =
      ∑ b ∈ Finset.range (j + 1),
        (c * ((geomTailTwo p a * localMoebiusFactor p (i - a)) *
              (geomTailOne p b * localMoebiusFactor p (j - b))) +
          c * ((geomTailOne p a * localMoebiusFactor p (i - a)) *
              (geomTailTwo p b * localMoebiusFactor p (j - b))) -
          c * (2 * ((geomTailTwo p a * localMoebiusFactor p (i - a)) *
              (geomTailTwo p b * localMoebiusFactor p (j - b))))) := by
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [selbergCorrectionLogLocal_eq_geomTails hp, localMoebiusPairFactor, hc]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hsplit : ∀ a ∈ Finset.range (i + 1),
      (∑ b ∈ Finset.range (j + 1),
        (c * ((geomTailTwo p a * localMoebiusFactor p (i - a)) *
              (geomTailOne p b * localMoebiusFactor p (j - b))) +
          c * ((geomTailOne p a * localMoebiusFactor p (i - a)) *
              (geomTailTwo p b * localMoebiusFactor p (j - b))) -
          c * (2 * ((geomTailTwo p a * localMoebiusFactor p (i - a)) *
              (geomTailTwo p b * localMoebiusFactor p (j - b)))))) =
      (c * (geomTailTwo p a * localMoebiusFactor p (i - a))) *
          (∑ b ∈ Finset.range (j + 1),
            geomTailOne p b * localMoebiusFactor p (j - b)) +
        (c * (geomTailOne p a * localMoebiusFactor p (i - a))) *
          (∑ b ∈ Finset.range (j + 1),
            geomTailTwo p b * localMoebiusFactor p (j - b)) -
        (2 * c * (geomTailTwo p a * localMoebiusFactor p (i - a))) *
          (∑ b ∈ Finset.range (j + 1),
            geomTailTwo p b * localMoebiusFactor p (j - b)) := by
    intro a _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [Finset.sum_congr rfl hsplit]
  have hone : (∑ b ∈ Finset.range (j + 1),
      geomTailOne p b * localMoebiusFactor p (j - b)) =
      if j = 1 then (1 : ℝ) else 0 := by
    rw [← additiveConvolution]
    exact additiveConvolution_geomTailOne hp j
  have htwo : (∑ b ∈ Finset.range (j + 1),
      geomTailTwo p b * localMoebiusFactor p (j - b)) =
      if j = 2 then (1 : ℝ) else 0 := by
    rw [← additiveConvolution]
    exact additiveConvolution_geomTailTwo hp j
  rw [hone, htwo]
  have houter : (∑ a ∈ Finset.range (i + 1),
      ((c * (geomTailTwo p a * localMoebiusFactor p (i - a))) *
          (if j = 1 then (1 : ℝ) else 0) +
        (c * (geomTailOne p a * localMoebiusFactor p (i - a))) *
          (if j = 2 then (1 : ℝ) else 0) -
        (2 * c * (geomTailTwo p a * localMoebiusFactor p (i - a))) *
          (if j = 2 then (1 : ℝ) else 0))) =
      (c * (if j = 1 then (1 : ℝ) else 0)) *
          (∑ a ∈ Finset.range (i + 1),
            geomTailTwo p a * localMoebiusFactor p (i - a)) +
        (c * (if j = 2 then (1 : ℝ) else 0)) *
          (∑ a ∈ Finset.range (i + 1),
            geomTailOne p a * localMoebiusFactor p (i - a)) -
        (2 * c * (if j = 2 then (1 : ℝ) else 0)) *
          (∑ a ∈ Finset.range (i + 1),
            geomTailTwo p a * localMoebiusFactor p (i - a)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [houter]
  have honeI : (∑ a ∈ Finset.range (i + 1),
      geomTailOne p a * localMoebiusFactor p (i - a)) =
      if i = 1 then (1 : ℝ) else 0 := by
    rw [← additiveConvolution]
    exact additiveConvolution_geomTailOne hp i
  have htwoI : (∑ a ∈ Finset.range (i + 1),
      geomTailTwo p a * localMoebiusFactor p (i - a)) =
      if i = 2 then (1 : ℝ) else 0 := by
    rw [← additiveConvolution]
    exact additiveConvolution_geomTailTwo hp i
  rw [honeI, htwoI, selbergCorrectionLogNumerator, hc]
  field_simp

end

end RHTower.Sieve
