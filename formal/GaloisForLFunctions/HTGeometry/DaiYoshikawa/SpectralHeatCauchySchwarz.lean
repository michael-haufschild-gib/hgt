import GaloisForLFunctions.HTGeometry.DaiYoshikawa.PowerExpSup
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator

/-!
# The spectral bound `|□ₓ K(t,x,y)| ≤ B^{1/2} t⁻¹ K(t/2,x,x)^{1/2} K(t,y,y)^{1/2}`

Lemma 2.1 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), bounds the Laplacian of a heat kernel by the kernel itself on the
diagonal.  Stripped of its geometry the statement is a pure inequality about a nonnegative spectral
sequence: writing `K(t,x,y) = Σᵢ e^{−tλᵢ} φᵢ(x)⊗⟨·,φᵢ(y)⟩`, the estimate is

```text
Σᵢ λᵢ e^{−tλᵢ} aᵢ bᵢ  ≤  B^{1/2} t⁻¹ (Σᵢ e^{−tλᵢ/2} aᵢ²)^{1/2} (Σᵢ e^{−tλᵢ} bᵢ²)^{1/2},
```

`aᵢ = |φᵢ(x)|`, `bᵢ = |φᵢ(y)|`, with `B = sup_{x≥0} x² e^{−x/2} = 16 e^{−2}`, so that
`B^{1/2} = 4 e^{−1}`.

The proof is Cauchy–Schwarz applied to the splitting
`λᵢ e^{−tλᵢ} aᵢ bᵢ = (λᵢ e^{−tλᵢ/2} aᵢ)(e^{−tλᵢ/2} bᵢ)`, followed by the extremal inequality
`λ² e^{−tλ/2} ≤ B t^{−2}` of `PowerExpSup`.
-/

open Real

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- `√(16 e^{−2}) = 4 e^{−1}`: the square root of Dai–Yoshikawa's constant `B`. -/
theorem sqrt_sixteen_mul_exp_neg_two : Real.sqrt (16 * exp (-2)) = 4 * exp (-1) := by
  have h : (16 : ℝ) * exp (-2) = (4 * exp (-1)) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num
  rw [h, Real.sqrt_sq (by positivity)]

/-- **The extremal estimate behind Lemma 2.1.**  For `t > 0` and `μ ≥ 0`,
`μ² e^{−tμ/2} ≤ 16 e^{−2} / t²`. -/
theorem sq_mul_exp_neg_half_mul_le {t μ : ℝ} (ht : 0 < t) (hμ : 0 ≤ μ) :
    μ ^ 2 * exp (-(t / 2 * μ)) ≤ 16 * exp (-2) / t ^ 2 := by
  have h := pow_mul_exp_neg_div_le 2 (a := 2 / t) (by positivity) hμ
  have harg : μ / (2 / t) = t / 2 * μ := by field_simp
  rw [harg] at h
  refine h.trans (le_of_eq ?_)
  have : ((2 : ℕ) : ℝ) * (2 / t) = 4 / t := by push_cast; ring
  rw [this]
  rw [div_pow]
  push_cast
  field_simp
  ring

/-- **Lemma 2.1 of Dai–Yoshikawa, spectral form.**

For a nonnegative spectrum `λ` and coefficient families `a`, `b` whose weighted square sums
converge,

```text
Σᵢ λᵢ e^{−tλᵢ} aᵢ bᵢ ≤ (4/e) t⁻¹ (Σᵢ e^{−tλᵢ/2} aᵢ²)^{1/2} (Σᵢ e^{−tλᵢ} bᵢ²)^{1/2}.
```

Applied to `aᵢ = |φᵢ(x)|`, `bᵢ = |φᵢ(y)|` for an orthonormal eigenbasis `φᵢ` of the Hodge–Kodaira
Laplacian this is exactly `|□ₓ K^L(t,x,y)| ≤ B^{1/2} t⁻¹ K^L(t/2,x,x)^{1/2} K^L(t,y,y)^{1/2}`. -/
theorem tsum_eigenvalue_heat_mul_le
    {ι : Type*} {lam a b : ι → ℝ} {t : ℝ} (ht : 0 < t)
    (hlam : ∀ i, 0 ≤ lam i)
    (hA : Summable fun i => exp (-(t / 2 * lam i)) * a i ^ 2)
    (hB : Summable fun i => exp (-(t * lam i)) * b i ^ 2) :
    ∑' i, lam i * exp (-(t * lam i)) * (a i * b i)
      ≤ (4 * exp (-1)) / t
          * (Real.sqrt (∑' i, exp (-(t / 2 * lam i)) * a i ^ 2)
              * Real.sqrt (∑' i, exp (-(t * lam i)) * b i ^ 2)) := by
  set u : ι → ℝ := fun i => lam i * exp (-(t / 2 * lam i)) * a i with hu
  set v : ι → ℝ := fun i => exp (-(t / 2 * lam i)) * b i with hv
  -- the splitting
  have hsplit : ∀ i, u i * v i = lam i * exp (-(t * lam i)) * (a i * b i) := by
    intro i
    have : exp (-(t / 2 * lam i)) * exp (-(t / 2 * lam i)) = exp (-(t * lam i)) := by
      rw [← Real.exp_add]; ring_nf
    simp only [hu, hv]
    calc lam i * exp (-(t / 2 * lam i)) * a i * (exp (-(t / 2 * lam i)) * b i)
        = lam i * (exp (-(t / 2 * lam i)) * exp (-(t / 2 * lam i))) * (a i * b i) := by ring
      _ = lam i * exp (-(t * lam i)) * (a i * b i) := by rw [this]
  -- the square of the first factor
  have hu2 : ∀ i, u i ^ 2 ≤ (16 * exp (-2) / t ^ 2) * (exp (-(t / 2 * lam i)) * a i ^ 2) := by
    intro i
    have hkey := sq_mul_exp_neg_half_mul_le ht (hlam i)
    have hrewrite : u i ^ 2
        = (lam i ^ 2 * exp (-(t / 2 * lam i))) * (exp (-(t / 2 * lam i)) * a i ^ 2) := by
      simp only [hu]; ring
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_right hkey (by positivity)
  have hu2nonneg : ∀ i, 0 ≤ u i ^ 2 := fun i => sq_nonneg _
  have hsumu : Summable fun i => u i ^ 2 :=
    Summable.of_nonneg_of_le hu2nonneg hu2 (hA.mul_left _)
  have hvsq : ∀ i, v i ^ 2 = exp (-(t * lam i)) * b i ^ 2 := by
    intro i
    have h2 : exp (-(t / 2 * lam i)) ^ 2 = exp (-(t * lam i)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    simp only [hv]
    rw [mul_pow, h2]
  have hsumv : Summable fun i => v i ^ 2 := hB.congr fun i => (hvsq i).symm
  -- Cauchy–Schwarz
  have hCS : ∑' i, u i * v i ≤ Real.sqrt (∑' i, u i ^ 2) * Real.sqrt (∑' i, v i ^ 2) :=
    ContinuousLinearMap.tsum_mul_le_sqrt_mul_sqrt hsumu hsumv
  -- bound the two square roots
  have hUle : ∑' i, u i ^ 2
      ≤ (16 * exp (-2) / t ^ 2) * ∑' i, exp (-(t / 2 * lam i)) * a i ^ 2 := by
    rw [← tsum_mul_left]
    exact hsumu.tsum_le_tsum hu2 (hA.mul_left _)
  have hVeq : ∑' i, v i ^ 2 = ∑' i, exp (-(t * lam i)) * b i ^ 2 := tsum_congr hvsq
  have hsqrtU : Real.sqrt (∑' i, u i ^ 2)
      ≤ (4 * exp (-1)) / t * Real.sqrt (∑' i, exp (-(t / 2 * lam i)) * a i ^ 2) := by
    refine (Real.sqrt_le_sqrt hUle).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity)]
    congr 1
    rw [show (16 : ℝ) * exp (-2) / t ^ 2 = (16 * exp (-2)) / t ^ 2 by ring,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq ht.le, sqrt_sixteen_mul_exp_neg_two]
  calc ∑' i, lam i * exp (-(t * lam i)) * (a i * b i)
      = ∑' i, u i * v i := by exact (tsum_congr fun i => (hsplit i).symm)
    _ ≤ Real.sqrt (∑' i, u i ^ 2) * Real.sqrt (∑' i, v i ^ 2) := hCS
    _ = Real.sqrt (∑' i, u i ^ 2) * Real.sqrt (∑' i, exp (-(t * lam i)) * b i ^ 2) := by
        rw [hVeq]
    _ ≤ ((4 * exp (-1)) / t * Real.sqrt (∑' i, exp (-(t / 2 * lam i)) * a i ^ 2))
          * Real.sqrt (∑' i, exp (-(t * lam i)) * b i ^ 2) :=
        mul_le_mul_of_nonneg_right hsqrtU (Real.sqrt_nonneg _)
    _ = (4 * exp (-1)) / t
          * (Real.sqrt (∑' i, exp (-(t / 2 * lam i)) * a i ^ 2)
              * Real.sqrt (∑' i, exp (-(t * lam i)) * b i ^ 2)) := by ring

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
