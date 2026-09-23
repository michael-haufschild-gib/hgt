import GaloisForLFunctions.RHTower.BandAmplitudeRatio

/-!
# The prolate band mode against the modified-Bessel model

Putting the passage and the Volterra estimate together: the prolate angular mode of the band,
normalised at the endpoint, is trapped between fixed multiples of `I₀(cΞ)` on a collar of absolute
width.

The two structural facts that make the endpoint harmless are that the Liouville weight is the square
of the amplitude, `m̃ = g²`, so that

```text
m̃ · U' = g (u' - u B/2) = A · ( -y Phi + (1-y²) Phi' - ((1-y²)B/2) Phi ) ,
```

with `w w' = -y` and `w² = 1-y²`; and that `(1-y²)B` extends continuously to the endpoint with value
`-2`, because `(1-y²)Ξ'/Ξ = (1-y²)L - y` with `L` bounded and `(1-y²)Ξ''/Ξ' = y(1-s)/(y²-s)` is
rational.  Neither expression evaluates the singular factors separately.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The first-order coefficient scaled by `1-y²`, extended by its endpoint value `-2`. -/
def bandScaledCoeff (s y : ℝ) : ℝ :=
  if y = 1 then -2 else (1 - y ^ (2 : ℕ)) * bandFirstOrderCoeff s y

/-- The comparison unknown attached to a band mode. -/
def bandComparisonSol (s : ℝ) (Φ : ℝ → ℝ) (y : ℝ) : ℝ := Φ y / bandAmplitudeRatio s y

/-- Its derivative. -/
def bandComparisonSolDeriv (s : ℝ) (Φ DΦ : ℝ → ℝ) : ℝ → ℝ :=
  comparisonQuotientDeriv (driftAmplitude (bandLiouvilleWeight s))
    (driftAmplitudeDeriv (bandLiouvilleWeight s) (bandFirstOrderCoeff s))
    (bandNormalFormSol Φ) (bandNormalFormSolDeriv Φ DΦ)

section

variable {s y α : ℝ} {Φ DΦ DDΦ : ℝ → ℝ}

/-! ## The amplitude ratio on the collar -/

theorem half_le_bandAmplitudeRatio (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 < y)
    (hy1 : y ≤ 1) : 1 / 2 ≤ bandAmplitudeRatio s y := by
  rcases eq_or_lt_of_le hy1 with rfl | hlt
  · rw [bandAmplitudeRatio_one]
    norm_num
  have hys : s < y ^ (2 : ℕ) := by nlinarith
  have hy : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hsq := bandAmplitudeRatio_sq (s := s) (by linarith) hlt hys
  have hm : 1 - y ≤ bandLiouvilleWeight s y :=
    one_sub_le_bandLiouvilleWeight (by linarith) hlt.le hys
  have hA2 : (1 : ℝ) / 2 ≤ bandAmplitudeRatio s y ^ (2 : ℕ) := by
    rw [hsq, le_div_iff₀ hy]
    nlinarith [hm, hlt]
  nlinarith [hA2, bandAmplitudeRatio_nonneg s y]

theorem bandAmplitudeRatio_le_two (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 < y)
    (hy1 : y ≤ 1) : bandAmplitudeRatio s y ≤ 2 := by
  rcases eq_or_lt_of_le hy1 with rfl | hlt
  · rw [bandAmplitudeRatio_one]
    norm_num
  have hys : s < y ^ (2 : ℕ) := by nlinarith
  have hy : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hsq := bandAmplitudeRatio_sq (s := s) (by linarith) hlt hys
  have hm : bandLiouvilleWeight s y ≤ 6 * (1 - y) :=
    bandLiouvilleWeight_le hs0 hs1 (by linarith) hlt.le
  have hA2 : bandAmplitudeRatio s y ^ (2 : ℕ) ≤ 4 := by
    rw [hsq, div_le_iff₀ hy]
    nlinarith [hm, hlt, hy0]
  nlinarith [hA2, bandAmplitudeRatio_nonneg s y]

theorem bandAmplitudeRatio_pos (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 < y) (hy1 : y ≤ 1) :
    0 < bandAmplitudeRatio s y := by
  have := half_le_bandAmplitudeRatio hs1 hy0 hy1
  linarith

theorem continuousOn_bandAmplitudeRatio (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hα : 1 / 2 < α)
    (hα1 : α < 1) :
    ContinuousOn (bandAmplitudeRatio s) (Icc α 1) := by
  intro t ht
  have ht0 : α ≤ t := ht.1
  have htα : (1 : ℝ) / 2 < t := lt_of_lt_of_le hα ht0
  rcases eq_or_lt_of_le ht.2 with rfl | hlt
  · rw [ContinuousWithinAt, bandAmplitudeRatio_one]
    exact tendsto_bandAmplitudeRatio hs1 hα hα1
  · have hys : s < t ^ (2 : ℕ) := by nlinarith
    have hy : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith
    have hev : bandAmplitudeRatio s
        =ᶠ[nhdsWithin t (Icc α 1)]
          fun u : ℝ => Real.sqrt (bandLiouvilleWeight s u) / Real.sqrt (1 - u ^ (2 : ℕ)) := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds (by linarith : t ≠ 1))] with u hu
      exact bandAmplitudeRatio_of_ne hu
    refine ContinuousWithinAt.congr_of_eventuallyEq ?_ hev
      (bandAmplitudeRatio_of_ne (by linarith : t ≠ 1))
    refine ContinuousWithinAt.div ?_ ?_ ?_
    · exact (Real.continuous_sqrt.continuousAt.comp_continuousWithinAt
        ((continuousOn_bandLiouvilleWeight hs0 hs1 hα.le) t ht))
    · exact (Real.continuous_sqrt.comp ((continuous_const.sub (continuous_pow 2)))).continuousWithinAt
    · exact (Real.sqrt_pos.2 hy).ne'

/-! ## The comparison unknown -/

theorem bandComparisonSol_one (Φ : ℝ → ℝ) (s : ℝ) : bandComparisonSol s Φ 1 = Φ 1 := by
  rw [bandComparisonSol, bandAmplitudeRatio_one, div_one]

theorem bandComparisonSol_eq_quotient (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 < y) (hy1 : y < 1) :
    bandComparisonSol s Φ y
      = comparisonQuotient (driftAmplitude (bandLiouvilleWeight s)) (bandNormalFormSol Φ) y := by
  have hys : s < y ^ (2 : ℕ) := by nlinarith
  have hy : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hm : 0 < bandLiouvilleWeight s y := bandLiouvilleWeight_pos (by linarith) hy1 hys
  have hg : 0 < Real.sqrt (bandLiouvilleWeight s y) := Real.sqrt_pos.2 hm
  have hw : 0 < Real.sqrt (1 - y ^ (2 : ℕ)) := Real.sqrt_pos.2 hy
  rw [bandComparisonSol, bandAmplitudeRatio_of_ne (by linarith : y ≠ 1), comparisonQuotient,
    bandNormalFormSol, bandNfWeight, driftAmplitude,
    abs_of_nonneg (bandLiouvilleWeight_nonneg s y), div_div_eq_mul_div]
  ring

theorem prolateBand_eq_mul (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 < y) (hy1 : y ≤ 1) :
    Φ y = bandComparisonSol s Φ y * bandAmplitudeRatio s y := by
  have hA : 0 < bandAmplitudeRatio s y := bandAmplitudeRatio_pos hs1 hy0 hy1
  rw [bandComparisonSol, div_mul_cancel₀ _ hA.ne']

/-! ## The scaled first-order coefficient -/

theorem bandScaledCoeff_eq (hy0 : 1 / 2 < y) (hy1 : y < 1) (hys : s < y ^ (2 : ℕ)) :
    bandScaledCoeff s y
      = (1 - y ^ (2 : ℕ)) * bandPhaseLogDefect s y - y - y * (1 - s) / (y ^ (2 : ℕ) - s) := by
  have hy : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hy2 : (0 : ℝ) < y ^ (2 : ℕ) - s := by linarith
  rw [bandScaledCoeff, if_neg (by linarith : y ≠ 1), bandFirstOrderCoeff, bandPhaseLogDefect,
    bandModelDrift]
  field_simp
  ring

theorem continuousOn_bandScaledCoeff (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hα : 1 / 2 < α) :
    ContinuousOn (bandScaledCoeff s) (Icc α 1) := by
  intro t ht
  have ht0 : α ≤ t := ht.1
  have htα : (1 : ℝ) / 2 < t := lt_of_lt_of_le hα ht.1
  rcases eq_or_lt_of_le ht.2 with rfl | hlt
  · -- endpoint: the bounded part vanishes and the rational part is continuous
    rw [ContinuousWithinAt, bandScaledCoeff, if_pos rfl]
    have hne : (1 : ℝ) - s ≠ 0 := by linarith
    have hrat : Filter.Tendsto (fun u : ℝ => -u - u * (1 - s) / (u ^ (2 : ℕ) - s))
        (nhdsWithin (1:ℝ) (Icc α 1)) (nhds (-2)) := by
      have hne2 : ((1 : ℝ) ^ (2 : ℕ) - s) ≠ 0 := by
        rw [one_pow]
        exact hne
      have hc : ContinuousAt (fun u : ℝ => -u - u * (1 - s) / (u ^ (2 : ℕ) - s)) 1 := by
        refine ContinuousAt.sub continuous_neg.continuousAt (ContinuousAt.div ?_ ?_ hne2)
        · exact (continuous_id.mul continuous_const).continuousAt
        · exact ((continuous_pow 2).sub continuous_const).continuousAt
      have hdiv : (1 - s) / (1 - s) = 1 := div_self hne
      have hval : -(1:ℝ) - 1 * (1 - s) / (1 ^ (2 : ℕ) - s) = -2 := by
        rw [one_pow, one_mul, hdiv]
        norm_num
      have h := hc.tendsto
      rw [hval] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hsmall : Filter.Tendsto (fun u : ℝ => (1 - u ^ (2 : ℕ)) * bandPhaseLogDefect s u)
        (nhdsWithin (1:ℝ) (Icc α 1)) (nhds 0) := by
      refine squeeze_zero_norm' (a := fun u : ℝ => 2 * |1 - u ^ (2 : ℕ)|) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with u hu
        rcases eq_or_lt_of_le hu.2 with rfl | hult
        · rw [Real.norm_eq_abs]
          norm_num
        · have huα : (1 : ℝ) / 2 < u := lt_of_lt_of_le hα hu.1
          have hys : s < u ^ (2 : ℕ) := by nlinarith
          have hL := abs_bandPhaseLogDefect_le hs0 (by linarith) (by linarith) hult hys
          rw [Real.norm_eq_abs, abs_mul]
          nlinarith [hL, abs_nonneg (1 - u ^ (2 : ℕ)), abs_nonneg (bandPhaseLogDefect s u)]
      · have h0 : Filter.Tendsto (fun u : ℝ => 2 * |1 - u ^ (2 : ℕ)|) (nhds (1:ℝ))
            (nhds (2 * |1 - (1:ℝ) ^ (2 : ℕ)|)) :=
          (continuous_const.mul ((continuous_const.sub (continuous_pow 2)).abs)).tendsto (1:ℝ)
        norm_num at h0
        exact h0.mono_left nhdsWithin_le_nhds
    have hsum : Filter.Tendsto (fun u : ℝ => (1 - u ^ (2 : ℕ)) * bandPhaseLogDefect s u
        + (-u - u * (1 - s) / (u ^ (2 : ℕ) - s))) (nhdsWithin (1:ℝ) (Icc α 1)) (nhds (-2)) := by
      have h := hsmall.add hrat
      simpa using h
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    rcases eq_or_lt_of_le hu.2 with rfl | hult
    · rw [bandScaledCoeff, if_pos rfl]
      simp only [one_pow, one_mul]
      field_simp
      norm_num
    · have huα : (1 : ℝ) / 2 < u := lt_of_lt_of_le hα hu.1
      have hys : s < u ^ (2 : ℕ) := by nlinarith
      rw [bandScaledCoeff_eq huα hult hys]
      ring
  · have hys : s < t ^ (2 : ℕ) := by nlinarith
    have hy : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith
    have hev : bandScaledCoeff s
        =ᶠ[nhdsWithin t (Icc α 1)]
          fun u : ℝ => (1 - u ^ (2 : ℕ)) * bandFirstOrderCoeff s u := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds (by linarith : t ≠ 1))] with u hu
      rw [bandScaledCoeff, if_neg hu]
    refine ContinuousWithinAt.congr_of_eventuallyEq ?_ hev ?_
    · refine ContinuousWithinAt.mul (by fun_prop) ?_
      exact ((hasDerivAt_bandFirstOrderCoeff (by linarith) hlt hys).continuousAt).continuousWithinAt
    · rw [bandScaledCoeff, if_neg (by linarith : t ≠ 1)]

/-! ## The transported derivative -/

/-- **The Liouville weight times the comparison derivative is continuous to the endpoint.**  Neither
factor is, but their product only sees `w w' = -y`, `w² = 1-y²` and the scaled coefficient. -/
theorem bandLiouvilleWeight_mul_comparisonSolDeriv (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 < y)
    (hy1 : y ≤ 1) :
    bandLiouvilleWeight s y * bandComparisonSolDeriv s Φ DΦ y
      = bandAmplitudeRatio s y * (-(y * Φ y) + (1 - y ^ (2 : ℕ)) * DΦ y
          - bandScaledCoeff s y / 2 * Φ y) := by
  rcases eq_or_lt_of_le hy1 with rfl | hlt
  · rw [bandLiouvilleWeight_one, zero_mul, bandAmplitudeRatio_one, bandScaledCoeff, if_pos rfl]
    ring
  have hys : s < y ^ (2 : ℕ) := by nlinarith
  have hy : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hm : 0 < bandLiouvilleWeight s y := bandLiouvilleWeight_pos (by linarith) hlt hys
  have hg : 0 < Real.sqrt (bandLiouvilleWeight s y) := Real.sqrt_pos.2 hm
  have hw : 0 < Real.sqrt (1 - y ^ (2 : ℕ)) := Real.sqrt_pos.2 hy
  have hgg : Real.sqrt (bandLiouvilleWeight s y) * Real.sqrt (bandLiouvilleWeight s y)
      = bandLiouvilleWeight s y := Real.mul_self_sqrt hm.le
  have hww : Real.sqrt (1 - y ^ (2 : ℕ)) * Real.sqrt (1 - y ^ (2 : ℕ)) = 1 - y ^ (2 : ℕ) :=
    Real.mul_self_sqrt hy.le
  have hA : bandAmplitudeRatio s y
      = Real.sqrt (bandLiouvilleWeight s y) / Real.sqrt (1 - y ^ (2 : ℕ)) :=
    bandAmplitudeRatio_of_ne (by linarith : y ≠ 1)
  have hSC : bandScaledCoeff s y = (1 - y ^ (2 : ℕ)) * bandFirstOrderCoeff s y := by
    rw [bandScaledCoeff, if_neg (by linarith : y ≠ 1)]
  rw [bandComparisonSolDeriv, comparisonQuotientDeriv, driftAmplitude, driftAmplitudeDeriv,
    driftAmplitude, abs_of_nonneg (bandLiouvilleWeight_nonneg s y), bandNormalFormSol,
    bandNormalFormSolDeriv, bandNfWeight, bandNfWeightDeriv, hA, hSC]
  field_simp
  rw [Real.sq_sqrt hy.le, Real.sq_sqrt hm.le]
  ring

theorem continuousOn_bandLiouvilleWeight_mul_comparisonSolDeriv (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8)
    (hα : 1 / 2 < α) (hα1 : α < 1)
    (hΦc : ContinuousOn Φ (Icc α 1)) (hDΦc : ContinuousOn DΦ (Icc α 1)) :
    ContinuousOn (fun t : ℝ => bandLiouvilleWeight s t * bandComparisonSolDeriv s Φ DΦ t)
      (Icc α 1) := by
  have hcont : ContinuousOn (fun t : ℝ => bandAmplitudeRatio s t * (-(t * Φ t)
      + (1 - t ^ (2 : ℕ)) * DΦ t - bandScaledCoeff s t / 2 * Φ t)) (Icc α 1) := by
    refine (continuousOn_bandAmplitudeRatio hs0 hs1 hα hα1).mul ?_
    refine ((ContinuousOn.neg ((continuousOn_id).mul hΦc)).add
      ((by fun_prop : ContinuousOn (fun t : ℝ => 1 - t ^ (2 : ℕ)) (Icc α 1)).mul hDΦc)).sub ?_
    exact (((continuousOn_bandScaledCoeff hs0 hs1 hα).div_const 2).mul hΦc)
  refine hcont.congr fun t ht => ?_
  have htα : (1 : ℝ) / 2 < t := lt_of_lt_of_le hα ht.1
  exact bandLiouvilleWeight_mul_comparisonSolDeriv hs1 htα ht.2

/-! ## The comparison, for an actual band mode -/

theorem hasDerivAt_bandComparisonSol (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 < y) (hy1 : y < 1)
    (hΦ : HasDerivAt Φ (DΦ y) y) (hDΦ : HasDerivAt DΦ (DDΦ y) y)
    (hode : (1 - y ^ (2 : ℕ)) * DDΦ y - 2 * y * DΦ y + (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * y ^ (2 : ℕ)) * Φ y = 0) :
    HasDerivAt (bandComparisonSol s Φ) (bandComparisonSolDeriv s Φ DΦ y) y := by
  have h := (prolateBand_comparison (c := c) hs1 hy0 hy1 hΦ hDΦ hode).1
  have hev : bandComparisonSol s Φ =ᶠ[nhds y]
      comparisonQuotient (driftAmplitude (bandLiouvilleWeight s)) (bandNormalFormSol Φ) := by
    have hopen : {u : ℝ | 1 / 2 < u ∧ u < 1} ∈ nhds y := by
      refine IsOpen.mem_nhds ?_ ⟨hy0, hy1⟩
      exact (isOpen_lt continuous_const continuous_id).inter
        (isOpen_lt continuous_id continuous_const)
    filter_upwards [hopen] with u hu
    exact bandComparisonSol_eq_quotient hs1 hu.1 hu.2
  exact h.congr_of_eventuallyEq hev

theorem hasDerivAt_bandComparisonSolDeriv (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 < y) (hy1 : y < 1)
    (hΦ : HasDerivAt Φ (DΦ y) y) (hDΦ : HasDerivAt DΦ (DDΦ y) y)
    (hode : (1 - y ^ (2 : ℕ)) * DDΦ y - 2 * y * DΦ y + (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * y ^ (2 : ℕ)) * Φ y = 0) :
    HasDerivAt (bandComparisonSolDeriv s Φ DΦ)
      (-(bandFirstOrderCoeff s y) * bandComparisonSolDeriv s Φ DΦ y
        - (-(c ^ (2 : ℕ) * prolateWKBProfile s y ^ (2 : ℕ)) + bandComparisonDefect s y)
          * bandComparisonSol s Φ y) y := by
  have h := (prolateBand_comparison (c := c) hs1 hy0 hy1 hΦ hDΦ hode).2
  rw [bandComparisonSol_eq_quotient (Φ := Φ) hs1 hy0 hy1]
  exact h

/-- **The prolate band mode is trapped by the modified-Bessel model.**  On a collar of absolute width
the angular mode normalised at the endpoint satisfies `Phi ≍ I₀(cΞ)` with absolute constants. -/
theorem prolateBand_le_and_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hc : 0 < c)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hΦc : ContinuousOn Φ (Icc α 1)) (hDΦc : ContinuousOn DΦ (Icc α 1))
    (hΦ : ∀ x ∈ Ioo α 1, HasDerivAt Φ (DΦ x) x)
    (hDΦ : ∀ x ∈ Ioo α 1, HasDerivAt DΦ (DDΦ x) x)
    (hode : ∀ x ∈ Ioo α 1,
      (1 - x ^ (2 : ℕ)) * DDΦ x - 2 * x * DΦ x + (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * Φ x = 0)
    (hΦ1 : Φ 1 = 1) :
    ∀ y ∈ Icc α 1, 1 / 3 * bandModel s c y ≤ Φ y ∧ Φ y ≤ 3 * bandModel s c y := by
  have hUc : ContinuousOn (bandComparisonSol s Φ) (Icc α 1) := by
    refine hΦc.div (continuousOn_bandAmplitudeRatio hs0 hs1 hα hα1) fun t ht => ?_
    exact (bandAmplitudeRatio_pos hs1 (lt_of_lt_of_le hα ht.1) ht.2).ne'
  have hmDUc := continuousOn_bandLiouvilleWeight_mul_comparisonSolDeriv (Φ := Φ) (DΦ := DΦ)
    hs0 hs1 hα hα1 hΦc hDΦc
  have hU : ∀ x ∈ Ioo α 1, HasDerivAt (bandComparisonSol s Φ)
      (bandComparisonSolDeriv s Φ DΦ x) x := fun x hx =>
    hasDerivAt_bandComparisonSol (c := c) hs1 (lt_trans hα hx.1) hx.2 (hΦ x hx) (hDΦ x hx)
      (hode x hx)
  have hDU : ∀ x ∈ Ioo α 1, HasDerivAt (bandComparisonSolDeriv s Φ DΦ)
      (-(bandFirstOrderCoeff s x) * bandComparisonSolDeriv s Φ DΦ x
        - (-(c ^ (2 : ℕ) * prolateWKBProfile s x ^ (2 : ℕ)) + bandComparisonDefect s x)
          * bandComparisonSol s Φ x) x := fun x hx =>
    hasDerivAt_bandComparisonSolDeriv (c := c) hs1 (lt_trans hα hx.1) hx.2 (hΦ x hx) (hDΦ x hx)
      (hode x hx)
  have hU1 : bandComparisonSol s Φ 1 = 1 := by
    rw [bandComparisonSol_one, hΦ1]
  have hmain := bandModel_le_and_le_bandModel (s := s) (c := c) hs0 hs1 hc hα hα1 hcollar
    hUc hmDUc hU hDU hU1
  intro y hy
  have hyα : (1 : ℝ) / 2 < y := lt_of_lt_of_le hα hy.1
  have hA := hmain y hy
  have hAlow : 1 / 2 ≤ bandAmplitudeRatio s y := half_le_bandAmplitudeRatio hs1 hyα hy.2
  have hAhigh : bandAmplitudeRatio s y ≤ 2 := bandAmplitudeRatio_le_two hs0 hs1 hyα hy.2
  have hV : 0 < bandModel s c y := bandModel_pos
  have heq : Φ y = bandComparisonSol s Φ y * bandAmplitudeRatio s y :=
    prolateBand_eq_mul hs1 hyα hy.2
  have hUpos : 0 < bandComparisonSol s Φ y := by nlinarith [hA.1, hV]
  constructor
  · rw [heq]
    nlinarith [hA.1, hAlow, hV, hUpos]
  · rw [heq]
    nlinarith [hA.2, hAhigh, hV, hUpos]

end

end GaloisForLFunctions.RHTower

end
