import GaloisForLFunctions.RHTower.ProlateEndpointLowerBound
import GaloisForLFunctions.HTGeometry.EnvelopeFromLogDerivative

/-!
# The Sturm energy of the band equation and the uniform flux bound

The prolate equation in Sturm form is `((1−y²)Φ′)′ = (χ + c²y²)Φ`.  Its natural energy is

```text
E = ((1−y²)Φ′)² − (1−y²)(χ + c²y²)Φ² ,
```

whose derivative is exactly `−P′Φ²` with `P(y) = (1−y²)(χ + c²y²)`: the two cross terms produced by
the equation cancel identically.  The weight vanishes at `y = 1`, so `E(1) = 0`.

`P` increases up to `2y² = 1 − χ/c²` and decreases after, so `E` increases on the outer band and
therefore stays nonpositive there; on the inner part the same identity bounds `E` by the *increase*
of `P`, which the monotonicity of `Φ` converts into `Φ(y)²·P(ystar)`.  Either way

```text
((1−y²)Φ′(y))² ≤ (max P) · Φ(y)² ,
```

a uniform bound on the logarithmic derivative that holds across the whole band beyond the turning
point, with no outer-band restriction and no initial data.  Its value is that `max P = c²(1−s)²/4`
is only `O(c)` after the square root, whereas the flux representation gives `O(c²)`; the difference
is a full power of the bandwidth in every mass estimate downstream.
-/

noncomputable section

open Set MeasureTheory
open _root_.RHTower
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

variable {c χ : ℝ} {Φ : ℝ → ℝ}

/-- The weighted potential of the band equation. -/
def prolateWeightedPotential (c χ : ℝ) (y : ℝ) : ℝ := (1 - y ^ 2) * (χ + c ^ 2 * y ^ 2)

/-- The Sturm energy of the band equation. -/
def prolateBandEnergy (c χ : ℝ) (Φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  prolateFlux Φ y ^ 2 - prolateWeightedPotential c χ y * Φ y ^ 2

theorem hasDerivAt_prolateWeightedPotential (c χ y : ℝ) :
    HasDerivAt (prolateWeightedPotential c χ)
      (2 * y * (c ^ 2 - χ - 2 * c ^ 2 * y ^ 2)) y := by
  have hp : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * y)) y := by
    have h := (hasDerivAt_pow 2 y).const_sub (1 : ℝ)
    refine h.congr_deriv ?_
    norm_num
  have hq : HasDerivAt (fun t : ℝ => χ + c ^ 2 * t ^ 2) (2 * c ^ 2 * y) y := by
    have h := ((hasDerivAt_pow 2 y).const_mul (c ^ 2)).const_add χ
    refine h.congr_deriv ?_
    norm_num
    ring
  have h := hp.mul hq
  refine h.congr_deriv ?_
  ring

theorem prolateWeightedPotential_one (c χ : ℝ) : prolateWeightedPotential c χ 1 = 0 := by
  rw [prolateWeightedPotential]
  norm_num

theorem prolateBandEnergy_one (c χ : ℝ) (Φ : ℝ → ℝ) : prolateBandEnergy c χ Φ 1 = 0 := by
  rw [prolateBandEnergy, prolateFlux_one, prolateWeightedPotential_one]
  ring

/-- **The energy identity.**  The cross terms cancel and only the derivative of the weighted
potential survives. -/
theorem hasDerivAt_prolateBandEnergy (hd1 : Differentiable ℝ Φ)
    (hd2 : Differentiable ℝ (deriv Φ))
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt (prolateBandEnergy c χ Φ)
      (-(2 * y * (c ^ 2 - χ - 2 * c ^ 2 * y ^ 2)) * Φ y ^ 2) y := by
  have hflux := hasDerivAt_prolateFlux (c := c) (χ := χ) hd2 heig hy
  have hsq : HasDerivAt (fun t => prolateFlux Φ t ^ 2)
      (2 * prolateFlux Φ y * ((χ + c ^ 2 * y ^ 2) * Φ y)) y := by
    have h := hflux.pow 2
    refine h.congr_deriv ?_
    ring
  have hPot := hasDerivAt_prolateWeightedPotential c χ y
  have hΦsq : HasDerivAt (fun t => Φ t ^ 2) (2 * Φ y * deriv Φ y) y := by
    have h := ((hd1 y).hasDerivAt).pow 2
    refine h.congr_deriv ?_
    ring
  have hprod := hPot.mul hΦsq
  have h := hsq.sub hprod
  refine h.congr_deriv ?_
  rw [prolateFlux, prolateWeightedPotential]
  ring

/-! ## The two sides of the band -/

/-- Beyond the maximum of the weighted potential the energy is nonpositive. -/
theorem prolateBandEnergy_nonpos (hd1 : Differentiable ℝ Φ) (hd2 : Differentiable ℝ (deriv Φ))
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    {ystar : ℝ} (h0 : (-1 : ℝ) ≤ ystar) (hy0 : 0 ≤ ystar)
    (houter : ∀ t ∈ Icc ystar 1, c ^ 2 * (1 - 2 * t ^ 2) ≤ χ)
    {y : ℝ} (hy : y ∈ Icc ystar 1) :
    prolateBandEnergy c χ Φ y ≤ 0 := by
  have hsub : Icc y 1 ⊆ Icc ystar 1 := Icc_subset_Icc hy.1 le_rfl
  have hsub' : Icc y 1 ⊆ Icc (-1 : ℝ) 1 :=
    Icc_subset_Icc (le_trans h0 hy.1) le_rfl
  have hmono := le_of_hasDerivAt_nonneg (a := y) (b := 1) hy.2
    (fun t ht => hasDerivAt_prolateBandEnergy hd1 hd2 heig (hsub' ht))
    (fun t ht => by
      have hto := houter t (hsub ht)
      have ht0 : 0 ≤ t := le_trans hy0 (le_trans hy.1 ht.1)
      have hfac : c ^ 2 - χ - 2 * c ^ 2 * t ^ 2 ≤ 0 := by nlinarith [hto]
      have : 0 ≤ -(2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2)) := by nlinarith [ht0, hfac]
      exact mul_nonneg this (sq_nonneg _))
  rw [prolateBandEnergy_one] at hmono
  exact hmono

/-- Below the maximum of the weighted potential the energy is bounded by the increase of that
potential, weighted by the value of the mode. -/
theorem prolateBandEnergy_le_of_inner (hd1 : Differentiable ℝ Φ)
    (hd2 : Differentiable ℝ (deriv Φ))
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    {y₀ ystar : ℝ} (h0 : 0 ≤ y₀) (h1 : y₀ ≤ ystar) (h2 : ystar ≤ 1)
    (hpos : ∀ t ∈ Icc y₀ 1, 0 ≤ Φ t)
    (hanti : AntitoneOn Φ (Icc y₀ 1))
    (houter : ∀ t ∈ Icc ystar 1, c ^ 2 * (1 - 2 * t ^ 2) ≤ χ)
    (hinner : ∀ t ∈ Icc y₀ ystar, χ ≤ c ^ 2 * (1 - 2 * t ^ 2))
    {y : ℝ} (hy : y ∈ Icc y₀ ystar) :
    prolateBandEnergy c χ Φ y
      ≤ (prolateWeightedPotential c χ ystar - prolateWeightedPotential c χ y) * Φ y ^ 2 := by
  have hy1 : y ≤ ystar := hy.2
  have hyIcc : y ∈ Icc y₀ 1 := ⟨hy.1, le_trans hy.2 h2⟩
  have hsubBand : Icc y ystar ⊆ Icc (-1 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [h0, hy.1, ht.1], le_trans ht.2 h2⟩
  have hsubY : Icc y ystar ⊆ Icc y₀ 1 := by
    intro t ht
    exact ⟨le_trans hy.1 ht.1, le_trans ht.2 h2⟩
  -- the energy at the top of the potential is nonpositive
  have hstar : prolateBandEnergy c χ Φ ystar ≤ 0 :=
    prolateBandEnergy_nonpos hd1 hd2 heig (by linarith) (le_trans h0 h1) houter
      (left_mem_Icc.2 h2)
  -- the energy identity, integrated
  have hderiv : ∀ t ∈ uIcc y ystar,
      HasDerivAt (prolateBandEnergy c χ Φ)
        (-(2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2)) * Φ t ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hy1] at ht
    exact hasDerivAt_prolateBandEnergy hd1 hd2 heig (hsubBand ht)
  have hcont : Continuous fun t : ℝ => -(2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2)) * Φ t ^ 2 := by
    exact (by fun_prop : Continuous fun t : ℝ =>
      -(2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2))).mul (hd1.continuous.pow 2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable _ _)
  -- the integrand is bounded by the same with `Φ y` in place of `Φ t`
  have hcompare : (∫ t in y..ystar, -(2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2)) * Φ t ^ 2)
      ≥ ∫ t in y..ystar, -(2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2)) * Φ y ^ 2 := by
    refine intervalIntegral.integral_mono_on hy1
      ((by fun_prop : Continuous fun t : ℝ =>
        -(2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2)) * Φ y ^ 2).intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) fun t ht => ?_
    have hin := hinner t ⟨le_trans hy.1 ht.1, ht.2⟩
    have ht0 : 0 ≤ t := le_trans h0 (le_trans hy.1 ht.1)
    have hfac : 0 ≤ c ^ 2 - χ - 2 * c ^ 2 * t ^ 2 := by nlinarith [hin]
    have hsign : -(2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2)) ≤ 0 := by nlinarith [ht0, hfac]
    have hΦt : Φ t ≤ Φ y := hanti hyIcc (hsubY ht) ht.1
    have hΦ0 : 0 ≤ Φ t := hpos t (hsubY ht)
    have hsq : Φ t ^ 2 ≤ Φ y ^ 2 := by nlinarith
    nlinarith [hsign, hsq]
  -- and the comparison integral is the change of the potential
  have hPotFTC : (∫ t in y..ystar, -(2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2)))
      = -(prolateWeightedPotential c χ ystar - prolateWeightedPotential c χ y) := by
    have hd : ∀ t ∈ uIcc y ystar,
        HasDerivAt (prolateWeightedPotential c χ) (2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2)) t :=
      fun t _ => hasDerivAt_prolateWeightedPotential c χ t
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ =>
        2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_neg, h]
  have hsplit : (∫ t in y..ystar, -(2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2)) * Φ y ^ 2)
      = (∫ t in y..ystar, -(2 * t * (c ^ 2 - χ - 2 * c ^ 2 * t ^ 2))) * Φ y ^ 2 :=
    intervalIntegral.integral_mul_const _ _
  rw [hsplit, hPotFTC] at hcompare
  linarith [hFTC, hcompare, hstar]

/-! ## The uniform flux bound -/

/-- **The uniform flux bound.**  Across the whole band beyond the turning point the squared flux is
bounded by the maximum of the weighted potential times the squared value of the mode. -/
theorem prolateFlux_sq_le (hd1 : Differentiable ℝ Φ) (hd2 : Differentiable ℝ (deriv Φ))
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    {y₀ ystar K : ℝ} (h0 : 0 ≤ y₀) (h1 : y₀ ≤ ystar) (h2 : ystar ≤ 1)
    (hpos : ∀ t ∈ Icc y₀ 1, 0 ≤ Φ t)
    (hanti : AntitoneOn Φ (Icc y₀ 1))
    (houter : ∀ t ∈ Icc ystar 1, c ^ 2 * (1 - 2 * t ^ 2) ≤ χ)
    (hinner : ∀ t ∈ Icc y₀ ystar, χ ≤ c ^ 2 * (1 - 2 * t ^ 2))
    (hK : ∀ t ∈ Icc y₀ 1, prolateWeightedPotential c χ t ≤ K)
    {y : ℝ} (hy : y ∈ Icc y₀ 1) :
    prolateFlux Φ y ^ 2 ≤ K * Φ y ^ 2 := by
  have hKy := hK y hy
  have hKstar := hK ystar ⟨h1, h2⟩
  have hsq : (0 : ℝ) ≤ Φ y ^ 2 := sq_nonneg _
  rcases le_or_gt y ystar with hcase | hcase
  · have hE := prolateBandEnergy_le_of_inner hd1 hd2 heig h0 h1 h2 hpos hanti houter hinner
      (y := y) ⟨hy.1, hcase⟩
    rw [prolateBandEnergy] at hE
    nlinarith [hE, hKstar, hsq]
  · have hE := prolateBandEnergy_nonpos hd1 hd2 heig (by linarith) (le_trans h0 h1) houter
      (y := y) ⟨hcase.le, hy.2⟩
    rw [prolateBandEnergy] at hE
    nlinarith [hE, hKy, hsq]

/-! ## The mode cannot fall quickly -/

/-- The flux bound as a one-sided bound on the derivative. -/
theorem neg_mul_le_deriv_of_fluxBound {K : ℝ} (hK0 : 0 ≤ K) {t : ℝ}
    (ht1 : t < 1) (htneg : -1 < t) (hΦt : 0 ≤ Φ t)
    (hflux : prolateFlux Φ t ^ 2 ≤ K * Φ t ^ 2) :
    -(Real.sqrt K / (1 - t ^ 2)) * Φ t ≤ deriv Φ t := by
  have hw : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  have habs : |prolateFlux Φ t| ≤ Real.sqrt K * Φ t := by
    have h2 : Real.sqrt (prolateFlux Φ t ^ 2) ≤ Real.sqrt (K * Φ t ^ 2) :=
      Real.sqrt_le_sqrt hflux
    rw [Real.sqrt_sq_eq_abs] at h2
    rwa [Real.sqrt_mul hK0, Real.sqrt_sq hΦt] at h2
  have hlow : -(Real.sqrt K * Φ t) ≤ prolateFlux Φ t := neg_le_of_abs_le habs
  rw [prolateFlux] at hlow
  have hgoal : -(Real.sqrt K / (1 - t ^ 2)) * Φ t = -(Real.sqrt K * Φ t) / (1 - t ^ 2) := by
    field_simp
  rw [hgoal, div_le_iff₀ hw]
  nlinarith [hlow]

/-- **The mode is bounded below by the exponential of the flux bound.** -/
theorem exp_mul_le_prolate {K a b : ℝ} (hK0 : 0 ≤ K) (hab : a ≤ b) (hb1 : b < 1)
    (haneg : -1 < a)
    (hd1 : Differentiable ℝ Φ)
    (hpos : ∀ t ∈ Icc a b, 0 < Φ t)
    (hflux : ∀ t ∈ Icc a b, prolateFlux Φ t ^ 2 ≤ K * Φ t ^ 2) :
    Φ a * Real.exp (-∫ t in a..b, Real.sqrt K / (1 - t ^ 2)) ≤ Φ b := by
  have hwpos : ∀ t ∈ Icc a b, (0 : ℝ) < 1 - t ^ 2 := by
    intro t ht
    have h1 : -1 < t := lt_of_lt_of_le haneg ht.1
    have h2 : t < 1 := lt_of_le_of_lt ht.2 hb1
    nlinarith
  have hLcont : ContinuousOn (fun t : ℝ => -(Real.sqrt K / (1 - t ^ 2))) (Icc a b) := by
    refine ContinuousOn.neg (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
    intro t ht
    exact (hwpos t ht).ne'
  have hres := mul_exp_integral_le_of_logDeriv_ge' (f := Φ) (f' := deriv Φ)
    (L := fun t => -(Real.sqrt K / (1 - t ^ 2))) hab
    (fun t _ => (hd1 t).hasDerivAt) hpos hLcont (fun t ht => ?_)
  · have hneg : (∫ t in a..b, -(Real.sqrt K / (1 - t ^ 2)))
        = -∫ t in a..b, Real.sqrt K / (1 - t ^ 2) := intervalIntegral.integral_neg
    rwa [hneg] at hres
  · have h1 : -1 < t := lt_of_lt_of_le haneg ht.1
    have h2 : t < 1 := lt_of_le_of_lt ht.2 hb1
    exact neg_mul_le_deriv_of_fluxBound hK0 h2 h1 (hpos t ht).le (hflux t ht)

/-- **The interior mass is at least the window length times the exponentially damped endpoint
value.** -/
theorem mass_lower_of_fluxBound {K a b : ℝ} (hK0 : 0 ≤ K) (hab : a ≤ b) (hb1 : b < 1)
    (haneg : -1 < a)
    (hd1 : Differentiable ℝ Φ)
    (hpos : ∀ t ∈ Icc a b, 0 < Φ t)
    (hflux : ∀ t ∈ Icc a b, prolateFlux Φ t ^ 2 ≤ K * Φ t ^ 2) :
    (b - a) * (Φ a * Real.exp (-∫ t in a..b, Real.sqrt K / (1 - t ^ 2))) ^ 2
      ≤ ∫ t in a..b, Φ t ^ 2 := by
  have hwpos : ∀ t ∈ Icc a b, (0 : ℝ) < 1 - t ^ 2 := by
    intro t ht
    have h1 : -1 < t := lt_of_lt_of_le haneg ht.1
    have h2 : t < 1 := lt_of_le_of_lt ht.2 hb1
    nlinarith
  have hnn : ∀ t ∈ Icc a b, 0 ≤ Real.sqrt K / (1 - t ^ 2) := by
    intro t ht
    have := hwpos t ht
    positivity
  set J : ℝ := ∫ t in a..b, Real.sqrt K / (1 - t ^ 2) with hJ
  have hcont : ContinuousOn (fun t : ℝ => Real.sqrt K / (1 - t ^ 2)) (Icc a b) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro t ht
    exact (hwpos t ht).ne'
  have hpoint : ∀ t ∈ Icc a b, Φ a * Real.exp (-J) ≤ Φ t := by
    intro t ht
    have hstep := exp_mul_le_prolate (Φ := Φ) hK0 ht.1 (lt_of_le_of_lt ht.2 hb1) haneg hd1
      (fun u hu => hpos u ⟨hu.1, le_trans hu.2 ht.2⟩)
      (fun u hu => hflux u ⟨hu.1, le_trans hu.2 ht.2⟩)
    have hint1 : IntervalIntegrable (fun u : ℝ => Real.sqrt K / (1 - u ^ 2)) volume a t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.1]
      exact hcont.mono (Icc_subset_Icc le_rfl ht.2)
    have hint2 : IntervalIntegrable (fun u : ℝ => Real.sqrt K / (1 - u ^ 2)) volume t b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.2]
      exact hcont.mono (Icc_subset_Icc ht.1 le_rfl)
    have hsplit : (∫ u in a..b, Real.sqrt K / (1 - u ^ 2))
        = (∫ u in a..t, Real.sqrt K / (1 - u ^ 2))
          + ∫ u in t..b, Real.sqrt K / (1 - u ^ 2) :=
      (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
    have htail : 0 ≤ ∫ u in t..b, Real.sqrt K / (1 - u ^ 2) :=
      intervalIntegral.integral_nonneg ht.2 fun u hu =>
        hnn u ⟨le_trans ht.1 hu.1, hu.2⟩
    have hmono : Real.exp (-J) ≤ Real.exp (-∫ u in a..t, Real.sqrt K / (1 - u ^ 2)) := by
      refine Real.exp_le_exp.2 ?_
      rw [hJ, hsplit]
      linarith
    have hΦa : 0 < Φ a := hpos a ⟨le_rfl, hab⟩
    calc Φ a * Real.exp (-J) ≤ Φ a * Real.exp (-∫ u in a..t, Real.sqrt K / (1 - u ^ 2)) :=
          mul_le_mul_of_nonneg_left hmono hΦa.le
      _ ≤ Φ t := hstep
  have hbase : 0 ≤ Φ a * Real.exp (-J) := by
    have := (hpos a ⟨le_rfl, hab⟩).le
    positivity
  have hsq : ∀ t ∈ Icc a b, (Φ a * Real.exp (-J)) ^ 2 ≤ Φ t ^ 2 := by
    intro t ht
    exact pow_le_pow_left₀ hbase (hpoint t ht) 2
  have hmono : (∫ _t in a..b, (Φ a * Real.exp (-J)) ^ 2) ≤ ∫ t in a..b, Φ t ^ 2 :=
    intervalIntegral.integral_mono_on hab
      ((continuous_const (y := (Φ a * Real.exp (-J)) ^ 2)).intervalIntegrable a b)
      ((hd1.continuous.pow 2).intervalIntegrable _ _) hsq
  have hconst : (∫ _t in a..b, (Φ a * Real.exp (-J)) ^ 2)
      = (b - a) * (Φ a * Real.exp (-J)) ^ 2 := by
    simp
  rw [hconst] at hmono
  exact hmono

end GaloisForLFunctions.RHTower
