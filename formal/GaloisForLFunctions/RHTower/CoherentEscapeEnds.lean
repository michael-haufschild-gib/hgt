import GaloisForLFunctions.RHTower.CoherentKernelChart

/-!
# The two escaping ends of the coherent chart

`prime-valuation-dyadic-fermion-normal-cone-law`, equation `(13i)` and the three-face rigging.

The coherent norm `‖F_u‖² = 2 Φ(u)` diverges at both ends of the normal coordinate, but at very
different rates:

* `u → +∞`:  `Φ(u) ≥ (e^{u/2} − 1)²/4`, an exponential of an exponential in the drift;
* `u → −∞`:  `Φ(−V) ≥ ½(1 − e^{−1})² log V`, only logarithmic — the half-normal end.

Cauchy–Schwarz for the prime-scale Gram form then gives `‖F_u − F_v‖ ≥ ‖F_u‖ − ‖F_v‖`, so for every
fixed `v` the coherent kernel `K(u,v)` escapes weakly to zero at both ends.

The positive end is genuinely different from the negative one: pairing `F_V` with the single test
profile `f(t) = t` already grows like `e^V/V`, so `F_V` has no limit in the distributional dual.
-/

open Filter Topology Set intervalIntegral MeasureTheory

namespace RHTower

noncomputable section

theorem divProfile_coherentProfile_nonneg (u v : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ divProfile (coherentProfile u v) t := by
  rw [divProfile]
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (by rw [coherentProfile]; positivity) ht

theorem intervalIntegrable_divProfile_coherentProfile_sub {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (u v : ℝ) :
    IntervalIntegrable (divProfile (coherentProfile u v)) volume a b := by
  refine (intervalIntegrable_divProfile_coherentProfile u v).mono_set ?_
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.uIcc_of_le hab]
  exact Set.Icc_subset_Icc ha hb

/-- **The half-normal end diverges logarithmically.** -/
theorem coherentExponent_neg_ge {V : ℝ} (hV : 1 ≤ V) :
    (1 - Real.exp (-1)) ^ 2 / 2 * Real.log V ≤ coherentExponent (-V) 0 := by
  have hV0 : (0 : ℝ) < V := by linarith
  have hVinv : (0 : ℝ) < 1 / V := by positivity
  have hVinv1 : 1 / V ≤ 1 := by rw [div_le_one hV0]; linarith
  -- the integrand dominates `(1 - e^{-1})²/t` on `[1/V, 1]`
  have hdom : ∀ t ∈ Set.Icc (1 / V) 1,
      (1 - Real.exp (-1)) ^ 2 * (1 / t) ≤ divProfile (coherentProfile (-V) 0) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hVinv ht.1
    have htne : t ≠ 0 := ne_of_gt ht0
    have hVt : V * t ≥ 1 := by
      have h := ht.1
      rw [div_le_iff₀ hV0] at h
      linarith
    have hexp : Real.exp (-V * t) ≤ Real.exp (-1) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hpos : 0 ≤ Real.exp (-V * t) := Real.exp_nonneg _
    have hsq : (1 - Real.exp (-1)) ^ 2 ≤ (Real.exp (-V * t) - Real.exp (0 * t)) ^ 2 := by
      rw [show (0 : ℝ) * t = 0 by ring, Real.exp_zero]
      have h1 : Real.exp (-V * t) - 1 ≤ Real.exp (-1) - 1 := by linarith
      have h2 : Real.exp (-1) - 1 < 0 := by
        have := Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)
        linarith
      nlinarith [hpos]
    rw [divProfile, if_neg htne, coherentProfile]
    rw [show (1 - Real.exp (-1)) ^ 2 * (1 / t) = (1 - Real.exp (-1)) ^ 2 / t by ring]
    gcongr
  have hint1 : IntervalIntegrable (fun t : ℝ => (1 - Real.exp (-1)) ^ 2 * (1 / t))
      volume (1 / V) 1 := by
    refine IntervalIntegrable.const_mul ?_ _
    refine intervalIntegral.intervalIntegrable_one_div (fun x hx => ?_) ?_
    · rw [Set.uIcc_of_le hVinv1] at hx
      exact ne_of_gt (lt_of_lt_of_le hVinv hx.1)
    · exact continuous_id.continuousOn
  have hint2 := intervalIntegrable_divProfile_coherentProfile_sub hVinv.le hVinv1
    (le_refl (1 : ℝ)) (-V) 0
  have hcmp : (∫ t in (1 / V)..1, (1 - Real.exp (-1)) ^ 2 * (1 / t))
      ≤ ∫ t in (1 / V)..1, divProfile (coherentProfile (-V) 0) t := by
    exact intervalIntegral.integral_mono_on hVinv1 hint1 hint2 (fun t ht => hdom t ht)
  have hlogval : (∫ t in (1 / V)..1, (1 - Real.exp (-1)) ^ 2 * (1 / t))
      = (1 - Real.exp (-1)) ^ 2 * Real.log V := by
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hVinv zero_lt_one,
      one_div_one_div]
  have hsplit : (∫ t in (0 : ℝ)..1, divProfile (coherentProfile (-V) 0) t)
      = (∫ t in (0 : ℝ)..(1 / V), divProfile (coherentProfile (-V) 0) t)
        + ∫ t in (1 / V)..1, divProfile (coherentProfile (-V) 0) t := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ hint2).symm
    exact intervalIntegrable_divProfile_coherentProfile_sub (le_refl (0:ℝ)) hVinv.le hVinv1 (-V) 0
  have hhead : 0 ≤ ∫ t in (0 : ℝ)..(1 / V), divProfile (coherentProfile (-V) 0) t :=
    intervalIntegral.integral_nonneg hVinv.le
      (fun t ht => divProfile_coherentProfile_nonneg _ _ ht.1)
  rw [coherentExponent, hsplit]
  rw [hlogval] at hcmp
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [le_div_iff₀ h2]
  nlinarith [hcmp, hhead]

end

end RHTower
