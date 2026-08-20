import GaloisForLFunctions.RHTower.RandomEulerObservableFactor
import GaloisForLFunctions.RHTower.SteinhausPrimeHolomorphic
import GaloisForLFunctions.HTGeometry.KolmogorovLowerInequality

/-!
# `Re = 1/2` is the abscissa of almost sure convergence of the random Euler product

On the boundary torus, with one independent uniform phase per prime, the random Euler observable

`𝓛(σ) = -∑_p log (1 - X_p p^{-σ}) = ∑_p ∑_{k ≥ 1} X_p^k p^{-kσ}/k`

converges almost surely exactly when `σ > 1/2`.  Equivalently, `Re = 1/2` is the abscissa of almost
sure convergence of the random Euler product `∏_p (1 - X_p p^{-σ})^{-1}`.

The proof is Kolmogorov's dichotomy for a centred, uniformly bounded, coordinatewise series.  The
factors are centred by the mean value property, and their second moments are trapped between
constant multiples of `p^{-2σ}`, whose prime sum converges exactly when `σ > 1/2`.  Above the
threshold, Kolmogorov's maximal inequality gives almost sure convergence; at or below it,
Kolmogorov's lower inequality gives almost sure divergence.
-/

noncomputable section

open MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower.SteinhausModel

/-! ### The observable and its uniform constants -/

/-- The uniform Taylor constant of the Euler factors at abscissa `σ`. -/
def randomEulerKappa (σ : ℝ) : ℝ :=
  (2 : ℝ) ^ (-σ) * (1 - (2 : ℝ) ^ (-σ))⁻¹ / 2 + 1

/-- The Euler observable term at index `n`, reading only the `n`-th phase coordinate. -/
def randomEulerTerm (σ : ℝ) (n : ℕ) : ℝ → ℂ :=
  fun x => if n.Prime then randomEulerLogFactor ((n : ℝ) ^ (-σ)) x else 0

/-- At a prime coordinate the observable term is the Euler factor of the Steinhaus character. -/
theorem randomEulerTerm_prime_eq {σ : ℝ} {p : ℕ} (hp : p.Prime) (ω : Omega) :
    randomEulerTerm σ p (ω p)
      = -Complex.log (1 - (((p : ℝ) ^ (-σ) : ℝ) : ℂ) * X p ω) := by
  rw [randomEulerTerm, if_pos hp, randomEulerLogFactor, X_prime_eq hp]
  congr 3
  push_cast
  ring

theorem randomEulerRho_pos (σ : ℝ) : (0 : ℝ) < (2 : ℝ) ^ (-σ) :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem randomEulerRho_lt_one {σ : ℝ} (hσ : 0 < σ) : (2 : ℝ) ^ (-σ) < 1 := by
  have h : (1 : ℝ) < (2 : ℝ) ^ σ := by
    have := Real.rpow_lt_rpow_of_exponent_lt (x := (2 : ℝ)) (by norm_num) (y := 0) (z := σ) hσ
    simpa using this
  rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
  exact Or.inr h

theorem prime_rpow_neg_le_rho {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : n.Prime) :
    (n : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
  have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.two_le
  rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num), ← one_div, ← one_div]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_le_rpow (by norm_num) h2 hσ.le)

theorem randomEulerKappa_nonneg {σ : ℝ} (hσ : 0 < σ) : 0 ≤ randomEulerKappa σ := by
  have h0 := randomEulerRho_pos σ
  have h1 := randomEulerRho_lt_one hσ
  have h2 : (0 : ℝ) < 1 - (2 : ℝ) ^ (-σ) := by linarith
  have h3 : (0 : ℝ) < (1 - (2 : ℝ) ^ (-σ))⁻¹ := inv_pos.mpr h2
  rw [randomEulerKappa]
  nlinarith

/-- The prime coefficient profile of the observable. -/
def randomEulerRadius (σ : ℝ) (n : ℕ) : ℝ := if n.Prime then (n : ℝ) ^ (-σ) else 0

theorem randomEulerRadius_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ randomEulerRadius σ n := by
  rw [randomEulerRadius]
  split
  · positivity
  · exact le_rfl

theorem randomEulerRadius_le_rho {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    randomEulerRadius σ n ≤ (2 : ℝ) ^ (-σ) := by
  rw [randomEulerRadius]
  split
  · exact prime_rpow_neg_le_rho hσ (by assumption)
  · exact (randomEulerRho_pos σ).le

/-- The squared prime radius is the Dirichlet monomial at twice the abscissa. -/
theorem randomEuler_rpow_neg_sq (n : ℕ) (σ : ℝ) :
    ((n : ℝ) ^ (-σ)) ^ 2 = (n : ℝ) ^ (-(2 * σ)) := by
  rw [← Real.rpow_natCast ((n : ℝ) ^ (-σ)) 2, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

/-! ### Measurability, boundedness, centring -/

theorem measurable_randomEulerTerm (σ : ℝ) (n : ℕ) : Measurable (randomEulerTerm σ n) := by
  by_cases h : n.Prime
  · have heq : randomEulerTerm σ n = fun x : ℝ =>
        -Complex.log (1 - (((n : ℝ) ^ (-σ) : ℝ) : ℂ) *
          Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) := by
      funext x
      rw [randomEulerTerm, if_pos h, randomEulerLogFactor]
    rw [heq]
    exact (Complex.measurable_log.comp (by fun_prop)).neg
  · have heq : randomEulerTerm σ n = fun _ : ℝ => (0 : ℂ) := by
      funext x
      rw [randomEulerTerm, if_neg h]
    rw [heq]
    exact measurable_const

/-- **The uniform Taylor bound.** -/
theorem norm_randomEulerTerm_le {σ : ℝ} (hσ : 0 < σ) (n : ℕ) (x : ℝ) :
    ‖randomEulerTerm σ n x‖ ≤ randomEulerKappa σ * randomEulerRadius σ n := by
  by_cases h : n.Prime
  · rw [randomEulerTerm, if_pos h, randomEulerRadius, if_pos h, randomEulerKappa]
    set r : ℝ := (n : ℝ) ^ (-σ) with hrdef
    set ρ : ℝ := (2 : ℝ) ^ (-σ) with hρdef
    have hr0 : 0 < r := Real.rpow_pos_of_pos (by exact_mod_cast h.pos) _
    have hrρ : r ≤ ρ := prime_rpow_neg_le_rho hσ h
    have hρ1 : ρ < 1 := randomEulerRho_lt_one hσ
    have hr1 : r < 1 := lt_of_le_of_lt hrρ hρ1
    have hbound := norm_randomEulerLogFactor_le hr0.le hr1 x
    have h1r : (0 : ℝ) < 1 - r := by linarith
    have h1ρ : (0 : ℝ) < 1 - ρ := by linarith
    have hmono : r * (1 - r)⁻¹ ≤ ρ * (1 - ρ)⁻¹ := by
      have hkey : ρ * (1 - ρ)⁻¹ - r * (1 - r)⁻¹ = (ρ - r) * ((1 - ρ)⁻¹ * (1 - r)⁻¹) := by
        field_simp
        ring
      have hprod : 0 ≤ (ρ - r) * ((1 - ρ)⁻¹ * (1 - r)⁻¹) :=
        mul_nonneg (by linarith) (mul_nonneg (inv_nonneg.mpr h1ρ.le) (inv_nonneg.mpr h1r.le))
      linarith
    calc ‖randomEulerLogFactor r x‖ ≤ r ^ 2 * (1 - r)⁻¹ / 2 + r := hbound
      _ ≤ (ρ * (1 - ρ)⁻¹ / 2 + 1) * r := by nlinarith [hmono, hr0.le]
  · rw [randomEulerTerm, if_neg h, randomEulerRadius, if_neg h, norm_zero, mul_zero]

theorem norm_randomEulerTerm_le_const {σ : ℝ} (hσ : 0 < σ) (n : ℕ) (x : ℝ) :
    ‖randomEulerTerm σ n x‖ ≤ randomEulerKappa σ * (2 : ℝ) ^ (-σ) :=
  le_trans (norm_randomEulerTerm_le hσ n x)
    (mul_le_mul_of_nonneg_left (randomEulerRadius_le_rho hσ n) (randomEulerKappa_nonneg hσ))

/-- **The observable terms are centred.** -/
theorem integral_randomEulerTerm {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∫ y, randomEulerTerm σ n y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 := by
  by_cases h : n.Prime
  · have hr0 : 0 < (n : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by exact_mod_cast h.pos) _
    have hr1 : (n : ℝ) ^ (-σ) < 1 :=
      lt_of_le_of_lt (prime_rpow_neg_le_rho hσ h) (randomEulerRho_lt_one hσ)
    have habs : |(n : ℝ) ^ (-σ)| < 1 := by
      rw [abs_of_nonneg hr0.le]; exact hr1
    have heq : ∀ y : ℝ, randomEulerTerm σ n y = randomEulerLogFactor ((n : ℝ) ^ (-σ)) y :=
      fun y => by rw [randomEulerTerm, if_pos h]
    rw [integral_congr_ae (Filter.Eventually.of_forall heq)]
    exact integral_randomEulerLogFactor habs
  · have heq : ∀ y : ℝ, randomEulerTerm σ n y = 0 := fun y => by rw [randomEulerTerm, if_neg h]
    rw [integral_congr_ae (Filter.Eventually.of_forall heq)]
    exact integral_zero _ _

/-! ### Two-sided second moment bounds -/

theorem integrable_normSq_randomEulerTerm {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Integrable (fun y : ℝ => ‖randomEulerTerm σ n y‖ ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  refine Integrable.mono' (integrable_const ((randomEulerKappa σ * (2 : ℝ) ^ (-σ)) ^ 2))
    (((measurable_randomEulerTerm σ n).norm.pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_randomEulerTerm_le_const hσ n y) 2

theorem integral_normSq_randomEulerTerm_le {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∫ y, ‖randomEulerTerm σ n y‖ ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      ≤ (randomEulerKappa σ) ^ 2 * (randomEulerRadius σ n) ^ 2 := by
  have hB : ∀ y : ℝ, ‖randomEulerTerm σ n y‖ ^ 2
      ≤ (randomEulerKappa σ) ^ 2 * (randomEulerRadius σ n) ^ 2 := by
    intro y
    have h := pow_le_pow_left₀ (norm_nonneg (randomEulerTerm σ n y))
      (norm_randomEulerTerm_le hσ n y) 2
    calc ‖randomEulerTerm σ n y‖ ^ 2
        ≤ (randomEulerKappa σ * randomEulerRadius σ n) ^ 2 := h
      _ = (randomEulerKappa σ) ^ 2 * (randomEulerRadius σ n) ^ 2 := by ring
  calc ∫ y, ‖randomEulerTerm σ n y‖ ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      ≤ ∫ _y, (randomEulerKappa σ) ^ 2 * (randomEulerRadius σ n) ^ 2
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        integral_mono (integrable_normSq_randomEulerTerm hσ n) (integrable_const _) hB
    _ = (randomEulerKappa σ) ^ 2 * (randomEulerRadius σ n) ^ 2 := by simp

theorem integral_normSq_randomEulerTerm_ge {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    (randomEulerRadius σ n) ^ 2 / 48
      ≤ ∫ y, ‖randomEulerTerm σ n y‖ ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  by_cases h : n.Prime
  · set r : ℝ := (n : ℝ) ^ (-σ) with hrdef
    have hr0 : 0 < r := Real.rpow_pos_of_pos (by exact_mod_cast h.pos) _
    have hr1 : r ≤ 1 :=
      le_of_lt (lt_of_le_of_lt (prime_rpow_neg_le_rho hσ h) (randomEulerRho_lt_one hσ))
    have hpt : ∀ y ∈ Set.Icc (1 / 3 : ℝ) (2 / 3),
        (r / 4) ^ 2 ≤ ‖randomEulerTerm σ n y‖ ^ 2 := by
      intro y hy
      have hcos := cos_twoPi_le_neg_half hy.1 hy.2
      have hge := norm_randomEulerLogFactor_ge hr0.le hr1 hcos
      rw [randomEulerTerm, if_pos h]
      exact pow_le_pow_left₀ (by positivity) hge 2
    have hsubset : Set.Icc (1 / 3 : ℝ) (2 / 3) ⊆ Set.Icc (0 : ℝ) 1 := by
      intro y hy
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hmeas : MeasurableSet (Set.Icc (1 / 3 : ℝ) (2 / 3)) := measurableSet_Icc
    have hIcc01 : IntegrableOn (fun y : ℝ => ‖randomEulerTerm σ n y‖ ^ 2)
        (Set.Icc (0 : ℝ) 1) volume := integrable_normSq_randomEulerTerm hσ n
    have hIccsub : IntegrableOn (fun y : ℝ => ‖randomEulerTerm σ n y‖ ^ 2)
        (Set.Icc (1 / 3 : ℝ) (2 / 3)) volume := hIcc01.mono_set hsubset
    have h1 : ∫ _y in Set.Icc (1 / 3 : ℝ) (2 / 3), (r / 4) ^ 2
        ≤ ∫ y in Set.Icc (1 / 3 : ℝ) (2 / 3), ‖randomEulerTerm σ n y‖ ^ 2 :=
      setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Icc])) hIccsub hmeas hpt
    have h2 : ∫ y in Set.Icc (1 / 3 : ℝ) (2 / 3), ‖randomEulerTerm σ n y‖ ^ 2
        ≤ ∫ y in Set.Icc (0 : ℝ) 1, ‖randomEulerTerm σ n y‖ ^ 2 :=
      setIntegral_mono_set hIcc01
        (Filter.Eventually.of_forall fun y => by positivity)
        (LE.le.eventuallyLE hsubset)
    have h3 : ∫ _y in Set.Icc (1 / 3 : ℝ) (2 / 3), (r / 4) ^ 2 = (1 / 3) * (r / 4) ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc]
      norm_num
    have h4 : randomEulerRadius σ n ^ 2 / 48 = (1 / 3) * (r / 4) ^ 2 := by
      rw [randomEulerRadius, if_pos h, ← hrdef]
      ring
    rw [h4, ← h3]
    exact le_trans h1 h2
  · have hz : randomEulerRadius σ n = 0 := by rw [randomEulerRadius, if_neg h]
    rw [hz]
    have : (0 : ℝ) ≤ ∫ y, ‖randomEulerTerm σ n y‖ ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      integral_nonneg fun y => by positivity
    simpa using this

/-! ### The prime summability input -/

theorem summable_ite_prime_rpow {t : ℝ} (ht : 1 < t) :
    Summable fun n : ℕ => if n.Prime then (n : ℝ) ^ (-t) else 0 := by
  have h : Summable ((fun n : ℕ => (n : ℝ) ^ (-t)) ∘
      (Subtype.val : {p : ℕ | Nat.Prime p} → ℕ)) := (summable_prime_rpow_neg_iff t).2 ht
  have h2 := summable_subtype_iff_indicator.mp h
  refine h2.congr fun n => ?_
  simp [Set.indicator_apply]

theorem not_summable_ite_prime_rpow {t : ℝ} (ht : t ≤ 1) :
    ¬ Summable fun n : ℕ => if n.Prime then (n : ℝ) ^ (-t) else 0 := by
  intro hs
  have h2 : Summable ({p : ℕ | Nat.Prime p}.indicator fun n : ℕ => (n : ℝ) ^ (-t)) := by
    refine hs.congr fun n => ?_
    simp [Set.indicator_apply]
  have h3 : Summable fun p : {p : ℕ // p.Prime} => ((p : ℕ) : ℝ) ^ (-t) :=
    summable_subtype_iff_indicator.mpr h2
  exact absurd ((summable_prime_rpow_neg_iff t).1 h3) (by linarith)

/-! ### The dichotomy -/

/-- **The random Euler observable converges almost surely past the half line.** -/
theorem measure_coordSeriesConverges_randomEulerTerm_eq_one {σ : ℝ} (hσ : 1 / 2 < σ) :
    steinhausMeasure (coordSeriesConverges (randomEulerTerm σ)) = 1 := by
  have hσ0 : 0 < σ := by linarith
  have hsum : Summable fun n : ℕ =>
      ∫ y, ‖randomEulerTerm σ n y‖ ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hmaj : Summable fun n : ℕ =>
        (randomEulerKappa σ) ^ 2 * (if n.Prime then (n : ℝ) ^ (-(2 * σ)) else 0) :=
      (summable_ite_prime_rpow (by linarith)).mul_left _
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => by positivity)
      (fun n => ?_) hmaj
    refine le_trans (integral_normSq_randomEulerTerm_le hσ0 n) ?_
    have he : (randomEulerRadius σ n) ^ 2 = if n.Prime then (n : ℝ) ^ (-(2 * σ)) else 0 := by
      rw [randomEulerRadius]
      split
      · rw [randomEuler_rpow_neg_sq]
      · norm_num
    rw [he]
  have h := measure_coordSeriesConverges_eq_one (randomEulerTerm σ)
    (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1))
    (c := fun n => randomEulerKappa σ * randomEulerRadius σ n)
    (measurable_randomEulerTerm σ) (norm_randomEulerTerm_le hσ0)
    (fun n => mul_nonneg (randomEulerKappa_nonneg hσ0) (randomEulerRadius_nonneg σ n))
    (integral_randomEulerTerm hσ0) hsum (fun _ => 0)
  rwa [← steinhausMeasure] at h

/-- **The random Euler observable diverges almost surely up to the half line.** -/
theorem measure_coordSeriesConverges_randomEulerTerm_eq_zero {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : σ ≤ 1 / 2) :
    steinhausMeasure (coordSeriesConverges (randomEulerTerm σ)) = 0 := by
  have hunn : ∀ n : ℕ, (0 : ℝ) ≤ (if n.Prime then (n : ℝ) ^ (-(2 * σ)) else 0) / 48 := by
    intro n
    have : (0 : ℝ) ≤ if n.Prime then (n : ℝ) ^ (-(2 * σ)) else 0 := by
      split
      · positivity
      · exact le_rfl
    linarith
  have hnot : ¬ Summable fun n : ℕ => (if n.Prime then (n : ℝ) ^ (-(2 * σ)) else 0) / 48 := by
    intro hs
    have := hs.mul_left (48 : ℝ)
    refine not_summable_ite_prime_rpow (t := 2 * σ) (by linarith) (this.congr fun n => ?_)
    field_simp
  have hut := (not_summable_iff_tendsto_nat_atTop_of_nonneg hunn).1 hnot
  have hdiv : Tendsto (fun N => ∑ n ∈ Finset.range N,
      ∫ y, ‖randomEulerTerm σ n y‖ ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) atTop atTop := by
    refine tendsto_atTop_mono (fun N => Finset.sum_le_sum fun n _ => ?_) hut
    have he : (randomEulerRadius σ n) ^ 2 = if n.Prime then (n : ℝ) ^ (-(2 * σ)) else 0 := by
      rw [randomEulerRadius]
      split
      · rw [randomEuler_rpow_neg_sq]
      · norm_num
    have := integral_normSq_randomEulerTerm_ge hσ0 n
    rwa [he] at this
  have h := measure_coordSeriesConverges_eq_zero_of_variance_atTop (randomEulerTerm σ)
    (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)) (fun _ => 0)
    (measurable_randomEulerTerm σ)
    (c := fun _ => randomEulerKappa σ * (2 : ℝ) ^ (-σ))
    (fun n y => norm_randomEulerTerm_le_const hσ0 n y)
    (integral_randomEulerTerm hσ0)
    (C := randomEulerKappa σ * (2 : ℝ) ^ (-σ)) (fun _ => le_rfl) hdiv
  rwa [← steinhausMeasure] at h

/-- **`Re = 1/2` is the abscissa of almost sure convergence of the random Euler product.** -/
theorem measure_coordSeriesConverges_randomEulerTerm_eq_one_iff {σ : ℝ} (hσ : 0 < σ) :
    steinhausMeasure (coordSeriesConverges (randomEulerTerm σ)) = 1 ↔ 1 / 2 < σ := by
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    rw [measure_coordSeriesConverges_randomEulerTerm_eq_zero hσ hle] at h
    exact zero_ne_one h
  · exact measure_coordSeriesConverges_randomEulerTerm_eq_one

end GaloisForLFunctions.RHTower
