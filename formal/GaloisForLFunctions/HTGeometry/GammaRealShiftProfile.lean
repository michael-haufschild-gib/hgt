import GaloisForLFunctions.HTGeometry.GammaFactorialNormalization

/-!
# Gamma ratios across a shift, and the profile of a zeta tail

The modulus of the irrational-power zeta tail is a bounded oscillation times the regular profile

```text
Θ(k) = Γ(1 + s k) · β^k .
```

Comparing the profile at two nearby indices is comparing two values of `Γ` across the fixed real
shift `s(μ − ν)`, and the log-convexity bounds already in the tree give that comparison in both
directions:

```text
Γ(x)·(x + t − M)^t ≤ Γ(x + t) ≤ Γ(x)·(x + M)^t ,      0 < t < M .
```

So the ratio of the profile at `n − μ` to the profile at `n − ν` is of exact size `n^{s(ν−μ)}` up
to constants — which is precisely the weight that turns the degree of a shift polynomial into its
weighted level.  No asymptotic expansion of `Γ` is used.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### The two-sided ratio bound -/

theorem Gamma_div_Gamma_add_le {x t : ℝ} (hx : 0 < x) (ht : 0 < t) {M : ℕ} (hM : t < M)
    (hy : 0 < x + t - M) :
    Real.Gamma x / Real.Gamma (x + t) ≤ (x + t - M) ^ (-t) := by
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hGxt : 0 < Real.Gamma (x + t) := Real.Gamma_pos_of_pos (by linarith)
  have h := mul_rpow_le_Gamma_add ht hM hy
  rw [div_le_iff₀ hGxt, Real.rpow_neg (le_of_lt hy), inv_mul_eq_div,
    le_div_iff₀ (Real.rpow_pos_of_pos hy t)]
  exact h

theorem Gamma_add_div_Gamma_le {x t : ℝ} (hx : 0 < x) (ht : 0 < t) {M : ℕ} (hM : t < M) :
    Real.Gamma (x + t) / Real.Gamma x ≤ (x + M) ^ t := by
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  rw [div_le_iff₀ hGx]
  have h := Gamma_add_le_mul_rpow hx ht hM
  linarith [h]

/-! ### The profile -/

/-- The regular profile `Γ(1 + s k)·β^k`. -/
noncomputable def gammaProfile (s β : ℝ) (k : ℕ) : ℝ := Real.Gamma (1 + s * (k : ℝ)) * β ^ k

theorem gammaProfile_pos {s β : ℝ} (hs : 0 ≤ s) (hβ : 0 < β) (k : ℕ) :
    0 < gammaProfile s β k := by
  refine mul_pos (Real.Gamma_pos_of_pos ?_) (pow_pos hβ k)
  have : (0 : ℝ) ≤ s * (k : ℝ) := mul_nonneg hs (Nat.cast_nonneg k)
  linarith

theorem gammaProfile_ne_zero {s β : ℝ} (hs : 0 ≤ s) (hβ : 0 < β) (k : ℕ) :
    gammaProfile s β k ≠ 0 := ne_of_gt (gammaProfile_pos hs hβ k)

/-- The profile at a later index, divided by the profile at an earlier one, in the form the
recursion consumes. -/
theorem gammaProfile_div {s β : ℝ} (hs : 0 ≤ s) (hβ : 0 < β) {n μ ν : ℕ}
    (hν : ν ≤ μ) (hμ : μ ≤ n) :
    gammaProfile s β (n - μ) / gammaProfile s β (n - ν)
      = (Real.Gamma (1 + s * ((n - μ : ℕ) : ℝ)) / Real.Gamma (1 + s * ((n - ν : ℕ) : ℝ)))
        / β ^ (μ - ν) := by
  have hβn : β ^ (n - ν) = β ^ (n - μ) * β ^ (μ - ν) := by
    rw [← pow_add]
    congr 1
    omega
  rw [gammaProfile, gammaProfile, hβn]
  field_simp

/-- **The profile decays like `n^{-s(μ-ν)}` between two shifts.** -/
theorem gammaProfile_div_le {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) {n μ ν : ℕ}
    (hν : ν < μ) (hμ : μ ≤ n) {M : ℕ} (hM : s * ((μ - ν : ℕ) : ℝ) < M)
    (hpos : 0 < 1 + s * ((n - ν : ℕ) : ℝ) - M) :
    gammaProfile s β (n - μ) / gammaProfile s β (n - ν)
      ≤ (1 + s * ((n - ν : ℕ) : ℝ) - M) ^ (-(s * ((μ - ν : ℕ) : ℝ))) / β ^ (μ - ν) := by
  have hνμ : ν ≤ μ := le_of_lt hν
  have hcast : ((n - μ : ℕ) : ℝ) + ((μ - ν : ℕ) : ℝ) = ((n - ν : ℕ) : ℝ) := by
    have h : (n - μ) + (μ - ν) = n - ν := by omega
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
  have hmulsum : s * ((n - μ : ℕ) : ℝ) + s * ((μ - ν : ℕ) : ℝ) = s * ((n - ν : ℕ) : ℝ) := by
    rw [← mul_add, hcast]
  have hxt : (1 + s * ((n - μ : ℕ) : ℝ)) + s * ((μ - ν : ℕ) : ℝ)
      = 1 + s * ((n - ν : ℕ) : ℝ) := by linarith
  have hx : 0 < 1 + s * ((n - μ : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ s * ((n - μ : ℕ) : ℝ) := mul_nonneg (le_of_lt hs) (Nat.cast_nonneg _)
    linarith
  have ht : 0 < s * ((μ - ν : ℕ) : ℝ) := by
    refine mul_pos hs ?_
    have h1 : 1 ≤ μ - ν := by omega
    have h2 : (1 : ℝ) ≤ ((μ - ν : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hy : 0 < (1 + s * ((n - μ : ℕ) : ℝ)) + s * ((μ - ν : ℕ) : ℝ) - M := by
    rw [hxt]; exact hpos
  have hratio := Gamma_div_Gamma_add_le hx ht hM hy
  rw [hxt] at hratio
  rw [gammaProfile_div (le_of_lt hs) hβ hνμ hμ]
  gcongr

/-- **The profile grows at most like `n^{s(ν-μ)}` in the other direction.** -/
theorem gammaProfile_div_le' {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) {n μ ν : ℕ}
    (hμν : μ < ν) (hν : ν ≤ n) {M : ℕ} (hM : s * ((ν - μ : ℕ) : ℝ) < M) :
    gammaProfile s β (n - μ) / gammaProfile s β (n - ν)
      ≤ (1 + s * ((n - ν : ℕ) : ℝ) + M) ^ (s * ((ν - μ : ℕ) : ℝ)) * β ^ (ν - μ) := by
  have hμν' : μ ≤ ν := le_of_lt hμν
  have hcast : ((n - ν : ℕ) : ℝ) + ((ν - μ : ℕ) : ℝ) = ((n - μ : ℕ) : ℝ) := by
    have h : (n - ν) + (ν - μ) = n - μ := by omega
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
  have hmulsum : s * ((n - ν : ℕ) : ℝ) + s * ((ν - μ : ℕ) : ℝ) = s * ((n - μ : ℕ) : ℝ) := by
    rw [← mul_add, hcast]
  have hxt : (1 + s * ((n - ν : ℕ) : ℝ)) + s * ((ν - μ : ℕ) : ℝ)
      = 1 + s * ((n - μ : ℕ) : ℝ) := by linarith
  have hx : 0 < 1 + s * ((n - ν : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ s * ((n - ν : ℕ) : ℝ) := mul_nonneg (le_of_lt hs) (Nat.cast_nonneg _)
    linarith
  have ht : 0 < s * ((ν - μ : ℕ) : ℝ) := by
    refine mul_pos hs ?_
    have h1 : 1 ≤ ν - μ := by omega
    have h2 : (1 : ℝ) ≤ ((ν - μ : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hratio := Gamma_add_div_Gamma_le hx ht hM
  rw [hxt] at hratio
  have hβn : β ^ (n - μ) = β ^ (n - ν) * β ^ (ν - μ) := by
    rw [← pow_add]
    congr 1
    omega
  have hsplit : gammaProfile s β (n - μ) / gammaProfile s β (n - ν)
      = (Real.Gamma (1 + s * ((n - μ : ℕ) : ℝ)) / Real.Gamma (1 + s * ((n - ν : ℕ) : ℝ)))
        * β ^ (ν - μ) := by
    have hG : 0 < Real.Gamma (1 + s * ((n - ν : ℕ) : ℝ)) := Real.Gamma_pos_of_pos hx
    rw [gammaProfile, gammaProfile, hβn]
    field_simp
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hratio (by positivity)

end GaloisForLFunctions.HTGeometry
