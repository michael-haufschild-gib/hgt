import GaloisForLFunctions.RHTower.ProlateIndexedLeakageTwoSided

/-!
# The leakage as an exterior-to-interior mass quotient

The exterior mass identity of the canonical radial datum rearranges into an exact formula for the
signed leakage:

```text
d_n(a) = 2 sigma_n(a)² · (∫_{y>1} R²) / (∫_{-1}^{1} R²) .
```

The interior integral is positive because `R` is continuous with `R 1 = 1`, so the quotient is
well defined.  This is the form in which the leakage separates into three factors that the corpus
controls independently: the signed value (which tends to one), the exterior mass (whose scale is
one inverse bandwidth), and the interior mass (whose scale is one inverse square root of the
bandwidth times the squared central value).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- A continuous function with value one at an endpoint has positive squared mass. -/
theorem interval_integral_sq_pos_of_endpoint_one {R : ℝ → ℝ} (hR : Continuous R) (hR1 : R 1 = 1) :
    0 < ∫ y in (-1 : ℝ)..1, R y ^ (2 : ℕ) := by
  have hcont : Continuous fun y : ℝ => R y ^ (2 : ℕ) := hR.pow 2
  have hone : (fun y : ℝ => R y ^ (2 : ℕ)) 1 = 1 := by
    show R 1 ^ (2 : ℕ) = 1
    rw [hR1]
    norm_num
  have hnb : ∀ᶠ y in nhds (1 : ℝ), (1 : ℝ) / 2 < R y ^ (2 : ℕ) := by
    have := hcont.continuousAt (x := (1 : ℝ))
    have hlt : (1 : ℝ) / 2 < (fun y : ℝ => R y ^ (2 : ℕ)) 1 := by rw [hone]; norm_num
    exact this.eventually (eventually_gt_nhds hlt)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hnb
  set d : ℝ := min (δ / 2) 1 with hd
  have hd0 : 0 < d := by
    rw [hd]
    exact lt_min (by linarith) one_pos
  have hdle : d ≤ 1 := min_le_right _ _
  have hsub : ∀ y ∈ Set.Icc (1 - d) (1 : ℝ), (1 : ℝ) / 2 < R y ^ (2 : ℕ) := by
    intro y hy
    refine hball ?_
    have h1 : 1 - d ≤ y := hy.1
    have h2 : y ≤ 1 := hy.2
    have hdd : d ≤ δ / 2 := min_le_left _ _
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun y : ℝ => R y ^ (2 : ℕ)) volume u v :=
    fun u v => hcont.intervalIntegrable u v
  have hlow : (0 : ℝ) < ∫ y in (1 - d)..(1 : ℝ), R y ^ (2 : ℕ) := by
    have hle : ∫ y in (1 - d)..(1 : ℝ), (1 : ℝ) / 2 ≤ ∫ y in (1 - d)..(1 : ℝ), R y ^ (2 : ℕ) := by
      refine intervalIntegral.integral_mono_on (by linarith) (by
        exact (continuous_const.intervalIntegrable _ _)) (hint _ _) ?_
      intro y hy
      exact (hsub y hy).le
    have hval : (∫ y in (1 - d)..(1 : ℝ), (1 : ℝ) / 2) = d / 2 := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hval] at hle
    linarith
  have hleft : (0 : ℝ) ≤ ∫ y in (-1 : ℝ)..(1 - d), R y ^ (2 : ℕ) :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (f := fun y : ℝ => R y ^ (2 : ℕ)) (μ := volume) (a := (-1 : ℝ)) (b := 1 - d) (c := (1 : ℝ))
    (hint _ _) (hint _ _)
  linarith [hadd, hleft, hlow]

/-- **The signed leakage is twice the signed value squared times the exterior-to-interior mass
quotient.** -/
theorem evenProlateSignedLeakage_eq_mass_quotient {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hvne : evenProlateSignedValue a n ≠ 0) :
    evenProlateSignedLeakage a n
      = 2 * evenProlateSignedValue a n ^ (2 : ℕ)
        * (∫ x in Ioi (1 : ℝ), (signedModeRadialData a n).R x ^ (2 : ℕ))
        / (∫ y in (-1 : ℝ)..1, (signedModeRadialData a n).R y ^ (2 : ℕ)) := by
  have hD := signedModeRadialData_isExact ha n hvne
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signedModeRadialData a n).R := hD.2.2.2.2.2.1
  have hR1 : (signedModeRadialData a n).R 1 = 1 := hD.2.2.2.2.2.2.2.1
  have hpos : 0 < ∫ y in (-1 : ℝ)..1, (signedModeRadialData a n).R y ^ (2 : ℕ) :=
    interval_integral_sq_pos_of_endpoint_one hsm.continuous hR1
  have hmass := integral_Ioi_sq_signedModeRadialData ha n hvne
  have hσ : evenProlateSignedValue a n ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hvne
  rw [hmass]
  field_simp

end RHTower

end
