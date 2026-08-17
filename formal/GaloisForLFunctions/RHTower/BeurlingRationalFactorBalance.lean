import Mathlib

/-!
# Realizability constraints on a rational Euler factor

A positive generalized-prime measure with logarithmic density `w` has Laplace transform
`∫_0^∞ e^{-st} w t dt = log ζ`.  When the target `ζ` is a rational function with poles `p_i` and
zeros `z_j` (each listed with multiplicity), the density is forced to be

```
w(t) = ( ∑_i e^{p_i t} − ∑_j e^{z_j t} ) / t.
```

Two constraints follow, and they are the whole obstruction to realizing a prescribed rational Euler
factor by an actual system of generalized primes.

* **Balance.**  Local finiteness of the prime measure requires `w` to be integrable at `0`.  The
  numerator tends to `#poles − #zeros` there, so an imbalance makes `|w(t)| ≥ c/t`: the number of
  poles must equal the number of zeros.

* **Trace.**  Positivity `w ≥ 0` on `(0,∞)`, given balance, forces the numerator's derivative at `0`
  to be nonnegative: `∑_i p_i ≥ ∑_j z_j`.

Consequence for the Riemann hypothesis.  Deforming `ξ` by a factor symmetric about the critical
line, such as `h(s) = (s−β)(s−1+β)`, preserves the functional equation, the order, and reality while
placing zeros at the off-line real points `β` and `1−β`.  But `h` has two zeros and no poles, so by
**Balance** it is not the Euler factor of any positive generalized-prime measure.  The functional
equation alone is therefore blind to the Riemann hypothesis, and it is positivity of the prime
measure that excludes the deformation.
-/

open Set

namespace RHTower.RationalFactor

/-- Numerator of the logarithmic density of a rational Euler factor with poles `p` and zeros `z`. -/
noncomputable def factorNumerator {P Z : ℕ} (p : Fin P → ℝ) (z : Fin Z → ℝ) (t : ℝ) : ℝ :=
  (∑ i, Real.exp (p i * t)) - ∑ j, Real.exp (z j * t)

@[simp] theorem factorNumerator_zero {P Z : ℕ} (p : Fin P → ℝ) (z : Fin Z → ℝ) :
    factorNumerator p z 0 = (P : ℝ) - (Z : ℝ) := by
  simp [factorNumerator]

theorem continuous_factorNumerator {P Z : ℕ} (p : Fin P → ℝ) (z : Fin Z → ℝ) :
    Continuous (factorNumerator p z) := by
  unfold factorNumerator
  fun_prop

/-- **Balance.**  If the pole count differs from the zero count, the logarithmic density has a
genuine `1/t` singularity at the origin: `|w(t)| ≥ c/t` on a right neighbourhood of `0`.  Such a
density is not locally integrable, so the corresponding prime measure is not locally finite. -/
theorem abs_density_ge_of_count_ne {P Z : ℕ} (p : Fin P → ℝ) (z : Fin Z → ℝ)
    (hne : (P : ℝ) ≠ (Z : ℝ)) :
    ∃ c > 0, ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ →
      c / t ≤ |factorNumerator p z t / t| := by
  set c : ℝ := |(P : ℝ) - (Z : ℝ)| / 2 with hc
  have hcpos : 0 < c := by
    have : 0 < |(P : ℝ) - (Z : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hne)
    positivity
  -- continuity at `0` keeps the numerator within `c` of its value there
  have hcont := (continuous_factorNumerator p z).continuousAt (x := (0 : ℝ))
  have hev : ∀ᶠ t in nhds (0 : ℝ), |factorNumerator p z t - ((P : ℝ) - (Z : ℝ))| < c := by
    have h := hcont
    rw [ContinuousAt, factorNumerator_zero] at h
    have h2 := Metric.tendsto_nhds.mp h c hcpos
    filter_upwards [h2] with x hx
    rwa [Real.dist_eq] at hx
  obtain ⟨t₀, ht₀, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨c, hcpos, t₀, ht₀, ?_⟩
  intro t htpos htlt
  have hmem : t ∈ Metric.ball (0 : ℝ) t₀ := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
    rw [abs_of_pos htpos]
    exact htlt
  have hnear : |factorNumerator p z t - ((P : ℝ) - (Z : ℝ))| < c := hball hmem
  have hlow : c ≤ |factorNumerator p z t| := by
    have h1 : |(P : ℝ) - (Z : ℝ)| ≤ |factorNumerator p z t| +
        |factorNumerator p z t - ((P : ℝ) - (Z : ℝ))| := by
      have := abs_sub_abs_le_abs_sub ((P : ℝ) - (Z : ℝ)) (factorNumerator p z t)
      have h2 : |((P : ℝ) - (Z : ℝ)) - factorNumerator p z t| =
          |factorNumerator p z t - ((P : ℝ) - (Z : ℝ))| := abs_sub_comm _ _
      rw [h2] at this
      linarith
    rw [hc]
    linarith
  rw [abs_div, abs_of_pos htpos]
  gcongr

/-- **Trace.**  Under balance, positivity of the logarithmic density forces the pole trace to
dominate the zero trace: `∑ p_i ≥ ∑ z_j`.  The numerator vanishes at the origin, so its derivative
there — which is exactly the trace difference — cannot be negative. -/
theorem sum_pole_ge_sum_zero_of_nonneg {P Z : ℕ} (p : Fin P → ℝ) (z : Fin Z → ℝ)
    (hbal : (P : ℝ) = (Z : ℝ))
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ factorNumerator p z t) :
    ∑ j, z j ≤ ∑ i, p i := by
  have hderiv : HasDerivAt (factorNumerator p z)
      ((∑ i, p i) - ∑ j, z j) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ∑ i, Real.exp (p i * t)) (∑ i, p i) 0 := by
      have hi : ∀ i : Fin P, HasDerivAt (fun t : ℝ => Real.exp (p i * t)) (p i) 0 := by
        intro i
        have h := ((hasDerivAt_id (0 : ℝ)).const_mul (p i)).exp
        simpa using h
      have hsum := HasDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin P))) => hi i)
      have heq : (fun t : ℝ => ∑ i, Real.exp (p i * t)) =
          ∑ i, (fun t : ℝ => Real.exp (p i * t)) := by
        funext t
        simp [Finset.sum_apply]
      rw [heq]
      exact hsum
    have h2 : HasDerivAt (fun t : ℝ => ∑ j, Real.exp (z j * t)) (∑ j, z j) 0 := by
      have hj : ∀ j : Fin Z, HasDerivAt (fun t : ℝ => Real.exp (z j * t)) (z j) 0 := by
        intro j
        have h := ((hasDerivAt_id (0 : ℝ)).const_mul (z j)).exp
        simpa using h
      have hsum := HasDerivAt.sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin Z))) => hj j)
      have heq : (fun t : ℝ => ∑ j, Real.exp (z j * t)) =
          ∑ j, (fun t : ℝ => Real.exp (z j * t)) := by
        funext t
        simp [Finset.sum_apply]
      rw [heq]
      exact hsum
    exact h1.sub h2
  have hzero : factorNumerator p z 0 = 0 := by
    rw [factorNumerator_zero, hbal, sub_self]
  by_contra hcon
  push Not at hcon
  -- the derivative is negative, so the numerator is negative just to the right of `0`
  set d : ℝ := (∑ i, p i) - ∑ j, z j with hd
  have hdneg : d < 0 := by rw [hd]; linarith
  have hlim : Filter.Tendsto (slope (factorNumerator p z) 0)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds d) := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), slope (factorNumerator p z) 0 t < 0 := by
    have hsub : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
      nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
    exact (hlim.mono_left hsub).eventually (eventually_lt_nhds hdneg)
  obtain ⟨t, hslope, htpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have htpos' : (0 : ℝ) < t := htpos
  have hval : slope (factorNumerator p z) 0 t = factorNumerator p z t / t := by
    rw [slope_def_field, hzero]
    simp
  rw [hval] at hslope
  have hnn := hpos t htpos'
  have : 0 ≤ factorNumerator p z t / t := div_nonneg hnn htpos'.le
  linarith

/-- **A factor symmetric about the critical line is not realizable.**  `h(s) = (s−β)(s−1+β)` has two
zeros and no poles, so it violates Balance: no positive generalized-prime measure has it as Euler
factor.  Hence deforming `ξ` by `h` — which preserves the functional equation, the order and reality
while putting zeros at the off-line real points `β` and `1−β` — is barred by positivity alone. -/
theorem symmetric_quadratic_factor_not_balanced (β : ℝ) :
    ∃ c > 0, ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ →
      c / t ≤ |factorNumerator (Fin.elim0 : Fin 0 → ℝ) ![β, 1 - β] t / t| := by
  apply abs_density_ge_of_count_ne
  norm_num

end RHTower.RationalFactor
