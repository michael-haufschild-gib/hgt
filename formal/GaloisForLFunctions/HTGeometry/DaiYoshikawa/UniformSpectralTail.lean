import GaloisForLFunctions.HTGeometry.DaiYoshikawa.PowerExpSup
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The uniform tail of a spectral sum

Proposition 3.5 (2) of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), truncates the spectral expansion
`K(t,x,x) = Σ_m e^{−tλ_m}|φ_m(x)|²` at a level `N` chosen uniformly in the deformation parameter.
What makes that possible is a bound on the tail that depends only on the linear growth
`λ_m ≥ C m` of the spectrum (Lemma 3.3) and on the pointwise bound `|φ_m|² ≤ D(λ_m + 1)`:

```text
Σ_{m > N} e^{−tλ_m} |φ_m|²  ≤  D (2/(e t) + 1) · e^{−tC(N+1)/2} / (1 − e^{−tC/2}) .
```

The right-hand side is a geometric tail: it is independent of the deformation parameter and tends to
zero as `N → ∞` for each fixed `t > 0`.
-/

open Real Filter

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- **The weighted heat factor.**  `(λ+1) e^{−tλ} ≤ (2/(e t) + 1) e^{−tλ/2}` for `λ ≥ 0`, `t > 0`. -/
theorem weight_mul_exp_le {t lam : ℝ} (ht : 0 < t) (hlam : 0 ≤ lam) :
    (lam + 1) * exp (-(t * lam)) ≤ (2 / (Real.exp 1 * t) + 1) * exp (-(t * lam / 2)) := by
  have hhalf : exp (-(t * lam)) = exp (-(t * lam / 2)) * exp (-(t * lam / 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have hkey : lam * exp (-(t * lam / 2)) ≤ 2 / (Real.exp 1 * t) := by
    have h := pow_mul_exp_neg_div_le 1 (a := 2 / t) (by positivity) hlam
    have harg : lam / (2 / t) = t * lam / 2 := by field_simp
    rw [harg, pow_one] at h
    refine h.trans (le_of_eq ?_)
    push_cast
    rw [Real.exp_neg]
    field_simp
  have hle1 : exp (-(t * lam / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hpos : (0 : ℝ) < exp (-(t * lam / 2)) := Real.exp_pos _
  calc (lam + 1) * exp (-(t * lam))
      = (lam * exp (-(t * lam / 2)) + exp (-(t * lam / 2))) * exp (-(t * lam / 2)) := by
        rw [hhalf]; ring
    _ ≤ (2 / (Real.exp 1 * t) + 1) * exp (-(t * lam / 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ hpos.le
        linarith [hkey, hle1]

/-- **The uniform spectral tail estimate.**

With linear eigenvalue growth `λ_m ≥ C m` and pointwise weights `a_m ≤ D(λ_m+1)`, the tail of the
spectral sum beyond `N` is a geometric quantity depending only on `C`, `D` and `t`. -/
theorem tsum_spectral_tail_le
    {lam a : ℕ → ℝ} {C D t : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (ht : 0 < t)
    (hlam0 : ∀ m, 0 ≤ lam m) (hlamC : ∀ m, C * m ≤ lam m)
    (ha0 : ∀ m, 0 ≤ a m) (haD : ∀ m, a m ≤ D * (lam m + 1)) (N : ℕ) :
    ∑' k : ℕ, exp (-(t * lam (N + 1 + k))) * a (N + 1 + k)
      ≤ D * (2 / (Real.exp 1 * t) + 1)
          * (exp (-(t * C / 2)) ^ (N + 1) / (1 - exp (-(t * C / 2)))) := by
  set r : ℝ := exp (-(t * C / 2)) with hr
  have hrpos : 0 < r := Real.exp_pos _
  have hrlt : r < 1 := by
    rw [hr]
    refine Real.exp_lt_one_iff.mpr ?_
    have : 0 < t * C := mul_pos ht hC
    linarith
  set K : ℝ := D * (2 / (Real.exp 1 * t) + 1) with hK
  have hKnonneg : 0 ≤ K := by
    have : (0 : ℝ) ≤ 2 / (Real.exp 1 * t) + 1 := by positivity
    exact mul_nonneg hD this
  have hterm : ∀ m : ℕ, exp (-(t * lam m)) * a m ≤ K * r ^ m := by
    intro m
    have h1 : exp (-(t * lam m)) * a m ≤ exp (-(t * lam m)) * (D * (lam m + 1)) :=
      mul_le_mul_of_nonneg_left (haD m) (Real.exp_pos _).le
    have h2 : exp (-(t * lam m)) * (D * (lam m + 1))
        = D * ((lam m + 1) * exp (-(t * lam m))) := by ring
    have h3 : D * ((lam m + 1) * exp (-(t * lam m)))
        ≤ D * ((2 / (Real.exp 1 * t) + 1) * exp (-(t * lam m / 2))) :=
      mul_le_mul_of_nonneg_left (weight_mul_exp_le ht (hlam0 m)) hD
    have h4 : exp (-(t * lam m / 2)) ≤ r ^ m := by
      rw [hr, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      have := hlamC m
      nlinarith [ht.le, this]
    have h5 : D * ((2 / (Real.exp 1 * t) + 1) * exp (-(t * lam m / 2))) ≤ K * r ^ m := by
      rw [hK]
      have hcoef : (0 : ℝ) ≤ D * (2 / (Real.exp 1 * t) + 1) := hKnonneg
      calc D * ((2 / (Real.exp 1 * t) + 1) * exp (-(t * lam m / 2)))
          = (D * (2 / (Real.exp 1 * t) + 1)) * exp (-(t * lam m / 2)) := by ring
        _ ≤ (D * (2 / (Real.exp 1 * t) + 1)) * r ^ m :=
            mul_le_mul_of_nonneg_left h4 hcoef
    linarith [h1, h3, h5, h2.le, h2.ge]
  have hmaj : Summable fun k : ℕ => K * r ^ (N + 1) * r ^ k :=
    (summable_geometric_of_lt_one hrpos.le hrlt).mul_left _
  have hbound : ∀ k : ℕ,
      exp (-(t * lam (N + 1 + k))) * a (N + 1 + k) ≤ K * r ^ (N + 1) * r ^ k := by
    intro k
    have := hterm (N + 1 + k)
    rwa [pow_add, ← mul_assoc] at this
  have hnonneg : ∀ k : ℕ, 0 ≤ exp (-(t * lam (N + 1 + k))) * a (N + 1 + k) := fun k =>
    mul_nonneg (Real.exp_pos _).le (ha0 _)
  have hsum : Summable fun k : ℕ => exp (-(t * lam (N + 1 + k))) * a (N + 1 + k) :=
    Summable.of_nonneg_of_le hnonneg hbound hmaj
  calc ∑' k : ℕ, exp (-(t * lam (N + 1 + k))) * a (N + 1 + k)
      ≤ ∑' k : ℕ, K * r ^ (N + 1) * r ^ k := hsum.tsum_le_tsum hbound hmaj
    _ = K * r ^ (N + 1) * ∑' k : ℕ, r ^ k := by rw [tsum_mul_left]
    _ = K * (r ^ (N + 1) / (1 - r)) := by
        rw [tsum_geometric_of_lt_one hrpos.le hrlt]
        field_simp

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
