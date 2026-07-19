import GaloisForLFunctions.RHTower.ConstrainedProlateSecularVector

/-!
# The raw defect of the exact constrained eigenvector

The exact eigenvector at a constrained root has coordinates `v_j = ℓ_j / (d_j − μ)`, so its pairing
against the raw contrast `r_m = a_0 e_m − a_m e_0` has a closed form:

```text
v_m ℓ_0 − v_0 ℓ_m = ℓ_0 ℓ_m (d_0 − d_m) / ((d_m − μ)(d_0 − μ)).
```

This isolates exactly what has to vanish.  The defect is not controlled by the coordinates at all:
it is controlled by the *scale separation* `d_0 − d_m` measured against the distance of the root
from the poles `d_0` and `d_m`.  In particular the defect vanishes identically when the scales
coincide, and for a root far above both poles it is of relative size `(d_0 − d_m)/μ`.
-/

namespace RHTower

variable {d ℓ : ℕ → ℝ}

/-- **Closed form for the raw defect of the exact eigenvector.** -/
theorem secularVector_raw_defect (μ : ℝ) (m : ℕ)
    (h0 : d 0 - μ ≠ 0) (hm : d m - μ ≠ 0) :
    secularVector d ℓ μ m * ℓ 0 - secularVector d ℓ μ 0 * ℓ m
      = ℓ 0 * ℓ m * (d 0 - d m) / ((d m - μ) * (d 0 - μ)) := by
  rw [secularVector, secularVector]
  field_simp
  ring

/-- The defect vanishes when the two scales agree: a degenerate pole pair carries no contrast. -/
theorem secularVector_raw_defect_eq_zero_of_eq (μ : ℝ) (m : ℕ)
    (h0 : d 0 - μ ≠ 0) (hm : d m - μ ≠ 0) (hd : d 0 = d m) :
    secularVector d ℓ μ m * ℓ 0 - secularVector d ℓ μ 0 * ℓ m = 0 := by
  rw [secularVector_raw_defect μ m h0 hm, hd, sub_self, mul_zero, zero_div]

/-- **The defect relative to the head weight.**  Dividing by `v_0 ℓ_0` removes the coordinates
entirely: what remains is a ratio of scale differences to pole distances. -/
theorem secularVector_raw_defect_div (μ : ℝ) (m : ℕ)
    (h0 : d 0 - μ ≠ 0) (hm : d m - μ ≠ 0) (hℓ0 : ℓ 0 ≠ 0) :
    (secularVector d ℓ μ m * ℓ 0 - secularVector d ℓ μ 0 * ℓ m)
        / (secularVector d ℓ μ 0 * ℓ 0)
      = (ℓ m / ℓ 0) * ((d 0 - d m) / (d m - μ)) := by
  rw [secularVector_raw_defect μ m h0 hm, secularVector]
  field_simp

/-- The raw defect in reciprocal form: the difference of the two pole reciprocals, weighted by the
two coordinates.  No nonvanishing hypothesis is needed, since nothing is cleared. -/
theorem secularVector_mul_self_sub (μ : ℝ) (m : ℕ) :
    secularVector d ℓ μ m * ℓ 0 - secularVector d ℓ μ 0 * ℓ m
      = ℓ 0 * ℓ m * (1 / (d m - μ) - 1 / (d 0 - μ)) := by
  rw [secularVector, secularVector]
  ring

/-! ## The scale ratio vanishes when the root dominates the poles -/

open Filter

/-- **A root far above both poles kills the defect ratio.**  If both scales are negligible against
the root, the scale ratio controlling the raw defect tends to zero. -/
theorem tendsto_scale_defect_zero {D0 Dm M : ℝ → ℝ}
    (hM : ∀ᶠ lam in atTop, M lam ≠ 0)
    (h0 : Tendsto (fun lam => D0 lam / M lam) atTop (nhds 0))
    (hm : Tendsto (fun lam => Dm lam / M lam) atTop (nhds 0)) :
    Tendsto (fun lam => (D0 lam - Dm lam) / (Dm lam - M lam)) atTop (nhds 0) := by
  have hnum : Tendsto (fun lam => D0 lam / M lam - Dm lam / M lam) atTop (nhds (0 - 0)) :=
    h0.sub hm
  rw [sub_zero] at hnum
  have hden : Tendsto (fun lam => Dm lam / M lam - 1) atTop (nhds (0 - 1)) :=
    hm.sub tendsto_const_nhds
  have hdiv : Tendsto (fun lam => (D0 lam / M lam - Dm lam / M lam) / (Dm lam / M lam - 1))
      atTop (nhds (0 / (0 - 1))) := hnum.div hden (by norm_num)
  rw [zero_div] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [hM] with lam h
  rcases eq_or_ne (Dm lam - M lam) 0 with hb | hb
  · have h1 : Dm lam / M lam - 1 = 0 := by
      field_simp
      linarith [hb]
    rw [h1, div_zero, hb, div_zero]
  · field_simp

/-- **The normalized raw defect of the exact eigenvector vanishes.**  Combining the closed form
with the scale-ratio limit: once the root dominates both poles, the exact eigenvector's pairing
against the raw contrast is negligible against its head weight, whatever the coordinates do (they
enter only through a convergent ratio). -/
theorem tendsto_secularVector_raw_defect_div_zero
    {d ℓ : ℝ → ℕ → ℝ} {M : ℝ → ℝ} {m : ℕ} {c : ℝ}
    (hne0 : ∀ᶠ lam in atTop, d lam 0 - M lam ≠ 0)
    (hnem : ∀ᶠ lam in atTop, d lam m - M lam ≠ 0)
    (hl0ne : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0)
    (hM : ∀ᶠ lam in atTop, M lam ≠ 0)
    (h0 : Tendsto (fun lam => d lam 0 / M lam) atTop (nhds 0))
    (hm : Tendsto (fun lam => d lam m / M lam) atTop (nhds 0))
    (hratio : Tendsto (fun lam => ℓ lam m / ℓ lam 0) atTop (nhds c)) :
    Tendsto (fun lam =>
      (secularVector (d lam) (ℓ lam) (M lam) m * ℓ lam 0
        - secularVector (d lam) (ℓ lam) (M lam) 0 * ℓ lam m)
        / (secularVector (d lam) (ℓ lam) (M lam) 0 * ℓ lam 0)) atTop (nhds 0) := by
  have hscale := tendsto_scale_defect_zero hM h0 hm
  have hprod : Tendsto (fun lam =>
      (ℓ lam m / ℓ lam 0) * ((d lam 0 - d lam m) / (d lam m - M lam)))
      atTop (nhds (c * 0)) := hratio.mul hscale
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [hne0, hnem, hl0ne] with lam h0' hm' hl'
  exact (secularVector_raw_defect_div (M lam) m h0' hm' hl').symm

/-! ## Transferring a vanishing ratio across a common reference scale -/

/-- **Ratio transfer.**  If `A` is negligible against a reference scale `B`, and the root `M` is
comparable to `B` with a nonzero limiting proportion, then `A` is negligible against the root.

The nonvanishing of the reference scale is not assumed: it follows from `M/B → θ ≠ 0`, since
`B = 0` would force `M/B = 0`. -/
theorem tendsto_div_zero_of_div_tendsto {A B M : ℝ → ℝ} {θ : ℝ} (hθ : θ ≠ 0)
    (hA : Tendsto (fun lam => A lam / B lam) atTop (nhds 0))
    (hM : Tendsto (fun lam => M lam / B lam) atTop (nhds θ)) :
    Tendsto (fun lam => A lam / M lam) atTop (nhds 0) := by
  have hBne : ∀ᶠ lam in atTop, B lam ≠ 0 := by
    filter_upwards [hM.eventually_ne hθ] with lam h hB
    exact h (by rw [hB, div_zero])
  have hdiv : Tendsto (fun lam => (A lam / B lam) / (M lam / B lam)) atTop (nhds (0 / θ)) :=
    hA.div hM hθ
  rw [zero_div] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [hBne] with lam hB
  rcases eq_or_ne (M lam) 0 with hM0 | hM0
  · rw [hM0, zero_div, div_zero, div_zero]
  · field_simp

/-- **The raw defect vanishes, from reference-scale data alone.**  This is the chain assembled:
negligibility of the two poles against a reference scale, comparability of the root to that scale,
and a convergent coordinate ratio, together force the exact eigenvector's raw defect to vanish
relative to its head weight.

The eventual nonvanishing of the root is derived, not assumed. -/
theorem tendsto_secularVector_raw_defect_div_zero_of_reference
    {d ℓ : ℝ → ℕ → ℝ} {B M : ℝ → ℝ} {m : ℕ} {θ c : ℝ} (hθ : θ ≠ 0)
    (h0B : Tendsto (fun lam => d lam 0 / B lam) atTop (nhds 0))
    (hmB : Tendsto (fun lam => d lam m / B lam) atTop (nhds 0))
    (hMB : Tendsto (fun lam => M lam / B lam) atTop (nhds θ))
    (hne0 : ∀ᶠ lam in atTop, d lam 0 - M lam ≠ 0)
    (hnem : ∀ᶠ lam in atTop, d lam m - M lam ≠ 0)
    (hl0ne : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0)
    (hratio : Tendsto (fun lam => ℓ lam m / ℓ lam 0) atTop (nhds c)) :
    Tendsto (fun lam =>
      (secularVector (d lam) (ℓ lam) (M lam) m * ℓ lam 0
        - secularVector (d lam) (ℓ lam) (M lam) 0 * ℓ lam m)
        / (secularVector (d lam) (ℓ lam) (M lam) 0 * ℓ lam 0)) atTop (nhds 0) := by
  have hMne : ∀ᶠ lam in atTop, M lam ≠ 0 := by
    filter_upwards [hMB.eventually_ne hθ] with lam h hM0
    exact h (by rw [hM0, zero_div])
  exact tendsto_secularVector_raw_defect_div_zero hne0 hnem hl0ne hMne
    (tendsto_div_zero_of_div_tendsto hθ h0B hMB)
    (tendsto_div_zero_of_div_tendsto hθ hmB hMB)
    hratio

end RHTower
