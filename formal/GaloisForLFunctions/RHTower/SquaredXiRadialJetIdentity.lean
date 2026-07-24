import Mathlib
import GaloisForLFunctions.RHTower.SquaredXiRadialJetSourceAlignment

/-!
# Radial-derivative identity for squared-Xi jets: analytic core

The squared-radial jet identity (equation (4) of the source-alignment card) applies the operator
`D = (1/(2w)) d/dw` iteratively to `F(w) = L(1/2+w)/w` and re-expresses `D^n F` through the shifted
derivatives `L^(j)(1/2+w)` weighted by the reverse-Bessel magnitudes.  This file formalizes the exact
calculus content of the induction step (equation (6)) for an arbitrary smooth `L`, unconditionally:
the chain rule for a shifted iterated derivative and the single-term product rule
`d/dw [w^m L^(j)(1/2+w)] = m w^(m-1) L^(j)(1/2+w) + w^m L^(j+1)(1/2+w)`.
-/

open scoped Topology

namespace RHTower

/-- The radial operator `D f = f'/(2w)`. -/
noncomputable def radialOp (f : ℝ → ℝ) (w : ℝ) : ℝ := deriv f w / (2 * w)

/-- The radial profile `F(w) = L(1/2+w)/w`. -/
noncomputable def radialProfile (L : ℝ → ℝ) (w : ℝ) : ℝ := L (1 / 2 + w) / w

/-- Chain rule for a shifted iterated derivative: `d/dw [L^(j)(c+w)] = L^(j+1)(c+w)`. -/
theorem deriv_iteratedDeriv_shift
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (j : ℕ) (c w : ℝ) :
    deriv (fun v => iteratedDeriv j L (c + v)) w = iteratedDeriv (j + 1) L (c + w) := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j L) (c + w) :=
    (hL.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt
  rw [show (fun v => iteratedDeriv j L (c + v)) = (iteratedDeriv j L) ∘ (fun v => c + v) from rfl,
    deriv_comp w hd (by fun_prop), ← iteratedDeriv_succ]
  simp

/-- **Single-term radial derivative (equation (6) core).**  For a smooth `L`,
`d/dw [w^m · L^(j)(1/2+w)] = m·w^(m-1)·L^(j)(1/2+w) + w^m·L^(j+1)(1/2+w)`. -/
theorem deriv_pow_mul_iteratedDeriv_shift
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (m j : ℕ) (w : ℝ) :
    deriv (fun v => v ^ m * iteratedDeriv j L (1 / 2 + v)) w =
      (m : ℝ) * w ^ (m - 1) * iteratedDeriv j L (1 / 2 + w) +
        w ^ m * iteratedDeriv (j + 1) L (1 / 2 + w) := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j L) (1 / 2 + w) :=
    (hL.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt
  have hg : DifferentiableAt ℝ (fun v => iteratedDeriv j L (1 / 2 + v)) w :=
    hd.comp w (by fun_prop)
  have hpow : HasDerivAt (fun v : ℝ => v ^ m) ((m : ℝ) * w ^ (m - 1)) w := by
    simpa using hasDerivAt_pow m w
  have hshift : HasDerivAt (fun v => iteratedDeriv j L (1 / 2 + v))
      (iteratedDeriv (j + 1) L (1 / 2 + w)) w := by
    have h := hg.hasDerivAt
    rwa [deriv_iteratedDeriv_shift hL j (1 / 2) w] at h
  have hmul : HasDerivAt (fun v => v ^ m * iteratedDeriv j L (1 / 2 + v))
      ((m : ℝ) * w ^ (m - 1) * iteratedDeriv j L (1 / 2 + w) +
        w ^ m * iteratedDeriv (j + 1) L (1 / 2 + w)) w := by
    have h := hpow.mul hshift
    convert h using 1
  exact hmul.deriv

/-- HasDerivAt form of the single-term radial derivative. -/
theorem hasDerivAt_pow_mul_iteratedDeriv_shift
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (m j : ℕ) (w : ℝ) :
    HasDerivAt (fun v => v ^ m * iteratedDeriv j L (1 / 2 + v))
      ((m : ℝ) * w ^ (m - 1) * iteratedDeriv j L (1 / 2 + w) +
        w ^ m * iteratedDeriv (j + 1) L (1 / 2 + w)) w := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j L) (1 / 2 + w) :=
    (hL.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt
  have hg : DifferentiableAt ℝ (fun v => iteratedDeriv j L (1 / 2 + v)) w :=
    hd.comp w (by fun_prop)
  have hpow : HasDerivAt (fun v : ℝ => v ^ m) ((m : ℝ) * w ^ (m - 1)) w := by
    simpa using hasDerivAt_pow m w
  have hshift : HasDerivAt (fun v => iteratedDeriv j L (1 / 2 + v))
      (iteratedDeriv (j + 1) L (1 / 2 + w)) w := by
    have h := hg.hasDerivAt
    rwa [deriv_iteratedDeriv_shift hL j (1 / 2) w] at h
  have h := hpow.mul hshift
  convert h using 1

/-- Radial jet sum with abstract real coefficients (for a fixed order): `∑_{j≤N} c j·w^j·L^(j)(1/2+w)`. -/
noncomputable def jetSum (L : ℝ → ℝ) (c : ℕ → ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), c j * (w ^ j * iteratedDeriv j L (1 / 2 + w))

/-- The derivative of the radial jet sum is the coefficientwise single-term derivative. -/
theorem hasDerivAt_jetSum
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (c : ℕ → ℝ) (N : ℕ) (w : ℝ) :
    HasDerivAt (fun v => jetSum L c N v)
      (∑ j ∈ Finset.range (N + 1), c j *
        ((j : ℝ) * w ^ (j - 1) * iteratedDeriv j L (1 / 2 + w) +
          w ^ j * iteratedDeriv (j + 1) L (1 / 2 + w))) w := by
  have h := HasDerivAt.sum (fun j (_ : j ∈ Finset.range (N + 1)) =>
    (hasDerivAt_pow_mul_iteratedDeriv_shift hL j j w).const_mul (c j))
  have hfe : (∑ j ∈ Finset.range (N + 1),
      fun v => c j * (v ^ j * iteratedDeriv j L (1 / 2 + v))) = fun v => jetSum L c N v := by
    funext v; simp only [jetSum, Finset.sum_apply]
  rwa [hfe] at h

/-- Signed radial-jet coefficient `(-1)^(n-j)·b_{n,j}`. -/
noncomputable def jetCoeff (n j : ℕ) : ℝ :=
  (-1) ^ (n - j) * (squaredRadialJetWeight n j : ℝ)

theorem jetCoeff_succ_zero (n : ℕ) :
    jetCoeff (n + 1) 0 = -(2 * (n : ℝ) + 1) * jetCoeff n 0 := by
  rw [jetCoeff, jetCoeff, Nat.sub_zero, Nat.sub_zero, squaredRadialJetWeight_succ_zero, pow_succ]
  push_cast
  ring

theorem jetCoeff_succ_top (n : ℕ) :
    jetCoeff (n + 1) (n + 1) = jetCoeff n n := by
  have hz : squaredRadialJetWeight n (n + 1) = 0 :=
    squaredRadialJetWeight_eq_zero_of_lt n (n + 1) (by omega)
  simp only [jetCoeff, Nat.sub_self, pow_zero, one_mul, squaredRadialJetWeight_succ_succ, hz,
    mul_zero, zero_add]

theorem jetCoeff_succ_mid (n i : ℕ) (hi : i < n) :
    jetCoeff n (i + 1) * ((i + 1 : ℝ) - (2 * n + 1)) + jetCoeff n i = jetCoeff (n + 1) (i + 1) := by
  have h2 : i ≤ 2 * n := by omega
  have hcast : ((2 * n - i : ℕ) : ℝ) = 2 * (n : ℝ) - i := by
    rw [Nat.cast_sub h2]; push_cast; ring
  have he1 : n - i = (n - (i + 1)) + 1 := by omega
  have he2 : (n + 1) - (i + 1) = (n - (i + 1)) + 1 := by omega
  rw [jetCoeff, jetCoeff, jetCoeff, squaredRadialJetWeight_succ_succ, he1, he2]
  simp only [pow_succ]
  push_cast [hcast]
  ring

end RHTower
