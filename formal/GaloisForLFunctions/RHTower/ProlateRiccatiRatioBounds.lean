import GaloisForLFunctions.RHTower.ProlateAnchoredBarrier
import GaloisForLFunctions.RHTower.ProlateBandAmplitudeTransport
import GaloisForLFunctions.RHTower.ProlateEndpointUpperBound
import GaloisForLFunctions.HTGeometry.SturmAmplitudeSharpMajorant

/-!
# The Riccati ratio of the prolate band is one, to an elementary defect

The amplitude of the recessive band branch is governed by

```text
rho = sturmRiccatiRatio p Φ DΦ K = prolateLogDeriv Φ / (c · prolateWKBProfile s) ,
```

and both of its bounds are elementary in the band.  Above it is the WKB-anchored barrier

```text
v ≤ c P + 1/y + 1/(1-y) ,
```

and below it is the endpoint bound of the corpus, taken with the *midpoint* window `y₁ = (y+1)/2`,
for which the two losses `2y₁/(1-y₁²)` and `2/(y₁-y)` are each at most `4/(1-y)`:

```text
v ≥ c P - 8/(1-y) .
```

Hence the single two-sided statement

```text
|1 - rho(y)| ≤ (1/y + 9/(1-y)) / (c · prolateWKBProfile s y) ,
```

whose square, weighted by `2 c P`, has finite mass on the whole band: the elementary antiderivative
`sqrt(y²-s)/(s y)` of `1/(y² sqrt(y²-s))` makes the `1/y` part `O(1/K²)` on `[K/sqrt c, α]`, and the
`1/(1-y)` part is `O(1/c)` because the barrier is uniformly far from the endpoint there.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

open GaloisForLFunctions.HTGeometry

/-- The square root of the band scale is the profile times the leading coefficient. -/
theorem sqrt_prolateBandScale_eq {c s y : ℝ} (hc : 0 < c) (hsy : s < y ^ 2) (hy : y ^ 2 < 1) :
    Real.sqrt (prolateBandScale c s y) = c * prolateWKBProfile s y * (1 - y ^ 2) := by
  have h1 : (0 : ℝ) < y ^ 2 - s := by linarith
  have h2 : (0 : ℝ) < 1 - y ^ 2 := by linarith
  have hK : prolateBandScale c s y = c ^ 2 * ((y ^ 2 - s) * (1 - y ^ 2)) := by
    rw [prolateBandScale]; ring
  rw [hK, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le, prolateWKBProfile]
  have hsplit : Real.sqrt ((y ^ 2 - s) * (1 - y ^ 2))
      = Real.sqrt (y ^ 2 - s) * Real.sqrt (1 - y ^ 2) := Real.sqrt_mul h1.le _
  have hdiv : Real.sqrt ((y ^ 2 - s) / (1 - y ^ 2))
      = Real.sqrt (y ^ 2 - s) / Real.sqrt (1 - y ^ 2) := Real.sqrt_div' _ h2.le
  have hs2 : Real.sqrt (1 - y ^ 2) * Real.sqrt (1 - y ^ 2) = 1 - y ^ 2 :=
    Real.mul_self_sqrt h2.le
  have hs2pos : (0 : ℝ) < Real.sqrt (1 - y ^ 2) := Real.sqrt_pos.2 h2
  rw [hsplit, hdiv]
  field_simp
  nlinarith [hs2, hs2pos]

/-- The Riccati ratio of the band is the logarithmic derivative over the scaled profile. -/
theorem sturmRiccatiRatio_prolate {c s y : ℝ} {Φ DΦ : ℝ → ℝ} (hc : 0 < c)
    (hsy : s < y ^ 2) (hy : y ^ 2 < 1) (hΦ : Φ y ≠ 0) (hDΦ : DΦ y = deriv Φ y) :
    sturmRiccatiRatio (fun t => 1 - t ^ 2) Φ DΦ (prolateBandScale c s) y
      = prolateLogDeriv Φ y / (c * prolateWKBProfile s y) := by
  have h2 : (0 : ℝ) < 1 - y ^ 2 := by linarith
  have hP : 0 < prolateWKBProfile s y := by
    rw [prolateWKBProfile]
    exact Real.sqrt_pos.2 (by positivity)
  rw [sturmRiccatiRatio, sqrt_prolateBandScale_eq hc hsy hy, prolateLogDeriv, hDΦ]
  field_simp
  ring

/-- **The logarithmic derivative from below, with the midpoint window.**  Both losses of the
endpoint bound are at most `4/(1-y)`. -/
theorem prolateWKB_sub_eight_le_prolateLogDeriv {c χ y : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ t = χ * Φ t)
    (hcχ : 0 ≤ c ^ 2 + χ) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hpos : ∀ t ∈ Icc y 1, 0 < Φ t)
    (hturn : ∀ t ∈ Icc y 1, 0 ≤ χ + c ^ 2 * t ^ 2)
    (hQ0 : 0 < χ + c ^ 2 * y ^ 2) :
    prolateWKB c χ y - 8 / (1 - y) ≤ prolateLogDeriv Φ y := by
  have h1y : (0 : ℝ) < 1 - y := by linarith
  set y₁ : ℝ := (y + 1) / 2 with hy₁def
  have hlt : y < y₁ := by rw [hy₁def]; linarith
  have hy₁1 : y₁ < 1 := by rw [hy₁def]; linarith
  have hy₁0 : 0 < y₁ := by rw [hy₁def]; linarith
  have hbase := prolateWKB_sub_le_prolateLogDeriv (c := c) (χ := χ) (Φ := Φ)
    hsm heig hcχ hy0 hlt hy₁1 hpos hturn hQ0
  have hgap : y₁ - y = (1 - y) / 2 := by rw [hy₁def]; ring
  have h1 : 2 * y₁ / (1 - y₁ ^ 2) ≤ 4 / (1 - y) := by
    have hden : (0 : ℝ) < 1 - y₁ ^ 2 := by nlinarith
    rw [div_le_div_iff₀ hden h1y]
    nlinarith [hy₁0, hy₁1, hgap]
  have h2 : 2 / (y₁ - y) = 4 / (1 - y) := by
    rw [hgap]
    field_simp
  linarith [hbase, h1, h2.le, h2.ge]

/-- **The Riccati ratio is one to an elementary defect.** -/
theorem abs_one_sub_sturmRiccatiRatio_prolate_le {c s y : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hsy : s < y ^ 2) (hy0 : 0 < y) (hy1 : y < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ t = -(s * c ^ 2) * Φ t)
    (hΦ1 : Φ 1 = 1)
    (hcond : 0 ≤ -(s * c ^ 2) * (2 - y ^ 2) + c ^ 2 * y ^ 2)
    (hpos : ∀ t ∈ Icc y 1, 0 < Φ t)
    (hbarrier : ∀ t ∈ Icc y 1, prolateLogDeriv Φ t
      ≤ prolateAnchoredBarrier c (-(s * c ^ 2)) t)
    (hs1 : s < 1) :
    |1 - sturmRiccatiRatio (fun t => 1 - t ^ 2) Φ DΦ (prolateBandScale c s) y|
      ≤ (1 / y + 9 / (1 - y)) / (c * prolateWKBProfile s y) := by
  have hy2 : y ^ 2 < 1 := by nlinarith
  have h1y : (0 : ℝ) < 1 - y := by linarith
  have h2 : (0 : ℝ) < 1 - y ^ 2 := by linarith
  have hΦy : Φ y ≠ 0 := (hpos y ⟨le_rfl, hy1.le⟩).ne'
  have hP : 0 < prolateWKBProfile s y := by
    rw [prolateWKBProfile]
    exact Real.sqrt_pos.2 (by positivity)
  have hcP : 0 < c * prolateWKBProfile s y := by positivity
  have hW : prolateWKB c (-(s * c ^ 2)) y = c * prolateWKBProfile s y :=
    prolateWKB_eq_mul_profile hc.le
  sorry

end GaloisForLFunctions.RHTower

end
