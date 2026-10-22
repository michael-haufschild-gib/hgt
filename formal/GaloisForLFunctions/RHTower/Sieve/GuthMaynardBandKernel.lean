import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSmoothedLagSum
import GaloisForLFunctions.RHTower.ChenGuptaLiSchwartzFourier
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueBasic
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import DifferentialGeometry.External.DeGiorgi.Poincare

set_option autoImplicit false

/-!
# A reproducing kernel for band-limited exponential sums

Let `φ` be a smooth compactly supported function with `φ = 1` on `[-1, 1]` (`innerBump 1`) and
`K = 𝓕φ` its Fourier transform, a Schwartz function. Fourier inversion gives
`∫ K(ξ) e(ξx) dξ = 1` for `|x| ≤ 1`, so the rescaled kernel `k_{a,L}(η) = L K(Lη) e(−aη)`
reproduces every exponential sum whose frequencies lie in `[a − L, a + L]`:

`f(u) = Σ_i c_i e(u x_i) = ∫ k_{a,L}(η) f(u + η) dη`   (`|x_i − a| ≤ L`).

Consequences proved here:
* `|f(u)|^p ≤ ‖K‖₁^{p−1} ∫ |k_{a,L}(η)| |f(u + η)|^p dη` for `p = 1, 2, 3` (weighted
  Cauchy–Schwarz `HTGeometry.sq_integral_weighted_le` and the weighted power mean
  `DeGiorgi.weighted_power_mean_setIntegral`);
* truncation at `|η| = δ`:
  `|f(u)| ≤ L ‖K‖_∞ ∫_{−δ}^{δ} |f(u + η)| dη + (Σ_i |c_i|) ∫_{|ξ| > Lδ} |K(ξ)| dξ`, the tail being
  `O_j((Lδ)^{−j})` by the Schwartz decay of `K` (`bandTail_le`);
* at unit scale, a shift-uniform square bound with the Cauchy weight `3 bandCauchy/(1 + η²)`.

This is the mechanism of Guth–Maynard Lemma 11.3 (`L = 1`, frequencies `log n/2π`) and
Lemma 11.7 (`L = T`, frequencies `t/2π`, `t ∈ W`).
-/

open MeasureTheory Set Finset
open scoped FourierTransform

namespace RHTower.GuthMaynard

noncomputable section

/-! ### The plateau profile and its Fourier transform -/

/-- The plateau `φ = innerBump 1`, complexified: smooth, compactly supported, `= 1` on `[-1, 1]`. -/
def bandPlateauFun (x : ℝ) : ℂ := (innerBump 1 x : ℂ)

theorem contDiff_bandPlateauFun : ContDiff ℝ (↑(⊤ : ℕ∞)) bandPlateauFun :=
  Complex.ofRealCLM.contDiff.comp (contDiff_innerBump 1)

theorem hasCompactSupport_bandPlateauFun : HasCompactSupport bandPlateauFun :=
  (hasCompactSupport_innerBump one_pos).comp_left Complex.ofReal_zero

/-- `φ` as a Schwartz function. -/
def bandPlateau : SchwartzMap ℝ ℂ :=
  hasCompactSupport_bandPlateauFun.toSchwartzMap contDiff_bandPlateauFun

theorem bandPlateau_apply (x : ℝ) : bandPlateau x = (innerBump 1 x : ℂ) := rfl

/-- The profile `K = 𝓕φ`. -/
def bandProfile : ℝ → ℂ := 𝓕 (bandPlateau : ℝ → ℂ)

theorem integrable_bandProfile : Integrable bandProfile := by
  unfold bandProfile
  rw [← SchwartzMap.fourier_coe]
  exact (𝓕 bandPlateau).integrable

theorem continuous_bandProfile : Continuous bandProfile := by
  unfold bandProfile
  rw [← SchwartzMap.fourier_coe]
  exact (𝓕 bandPlateau).continuous

/-- Schwartz decay of the profile: `|ξ|^j |K(ξ)| ≤ B_j`. -/
theorem abs_pow_mul_norm_bandProfile_le (j : ℕ) (ξ : ℝ) :
    |ξ| ^ j * ‖bandProfile ξ‖ ≤ cglSchwartzFourierDecayBudget bandPlateau j :=
  cglSchwartz_abs_pow_mul_norm_fourier_le_decayBudget bandPlateau j ξ

/-- `‖K‖_∞ ≤ bandSup`. -/
def bandSup : ℝ := cglSchwartzFourierDecayBudget bandPlateau 0

theorem norm_bandProfile_le (ξ : ℝ) : ‖bandProfile ξ‖ ≤ bandSup := by
  simpa [bandSup] using abs_pow_mul_norm_bandProfile_le 0 ξ

theorem bandSup_nonneg : 0 ≤ bandSup := (norm_nonneg _).trans (norm_bandProfile_le 0)

/-- The Cauchy-type majorant constant: `|K(ξ)| ≤ bandCauchy / (1 + ξ²)`. -/
def bandCauchy : ℝ :=
  cglSchwartzFourierDecayBudget bandPlateau 0 + cglSchwartzFourierDecayBudget bandPlateau 2

theorem norm_bandProfile_le_cauchy (ξ : ℝ) : ‖bandProfile ξ‖ ≤ bandCauchy / (1 + ξ ^ 2) := by
  rw [le_div_iff₀ (by positivity)]
  have h0 := abs_pow_mul_norm_bandProfile_le 0 ξ
  have h2 := abs_pow_mul_norm_bandProfile_le 2 ξ
  rw [pow_zero, one_mul] at h0
  rw [sq_abs] at h2
  unfold bandCauchy
  nlinarith

theorem bandCauchy_nonneg : 0 ≤ bandCauchy :=
  le_trans (by positivity) ((norm_bandProfile_le_cauchy 0).trans (by norm_num))

/-- The `L¹` mass `‖K‖₁`. -/
def bandMass : ℝ := ∫ ξ, ‖bandProfile ξ‖

theorem bandMass_nonneg : 0 ≤ bandMass := integral_nonneg fun _ => norm_nonneg _

/-- The tail mass `∫_{|ξ| > R} |K(ξ)| dξ`. -/
def bandTail (R : ℝ) : ℝ := ∫ ξ in {ξ : ℝ | R < |ξ|}, ‖bandProfile ξ‖

theorem measurableSet_lt_abs (R : ℝ) : MeasurableSet {ξ : ℝ | R < |ξ|} :=
  measurableSet_lt measurable_const measurable_abs

theorem bandTail_nonneg (R : ℝ) : 0 ≤ bandTail R :=
  setIntegral_nonneg (measurableSet_lt_abs R) fun _ _ => norm_nonneg _

/-- **Rapid decay of the tail**: `∫_{|ξ| > R} |K| ≤ 2π B_{j+2} / R^j` for `R ≥ 1`. -/
theorem bandTail_le (j : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    bandTail R ≤ 2 * Real.pi * cglSchwartzFourierDecayBudget bandPlateau (j + 2) / R ^ j := by
  set B := cglSchwartzFourierDecayBudget bandPlateau (j + 2) with hB
  have hR0 : 0 < R := by linarith
  have hRj : 0 < R ^ j := pow_pos hR0 j
  have hB0 : 0 ≤ B := le_trans (by positivity) (abs_pow_mul_norm_bandProfile_le (j + 2) 0)
  -- pointwise majorant on the tail
  have hpt : ∀ ξ ∈ {ξ : ℝ | R < |ξ|},
      ‖bandProfile ξ‖ ≤ 2 * B / R ^ j * (1 + ξ ^ 2)⁻¹ := by
    intro ξ hξ
    have hξ' : R < |ξ| := hξ
    have h := abs_pow_mul_norm_bandProfile_le (j + 2) ξ
    have hξ1 : 1 ≤ ξ ^ 2 := by
      have : 1 ≤ |ξ| := hR.trans hξ'.le
      nlinarith [sq_abs ξ, abs_nonneg ξ]
    have hpow : R ^ j * (1 + ξ ^ 2) ≤ 2 * |ξ| ^ (j + 2) := by
      have hRξ : R ^ j ≤ |ξ| ^ j := pow_le_pow_left₀ hR0.le hξ'.le j
      have e : |ξ| ^ (j + 2) = |ξ| ^ j * ξ ^ 2 := by rw [pow_add, sq_abs]
      rw [e]
      have hξj : 0 ≤ |ξ| ^ j := by positivity
      nlinarith
    have hpos : 0 < R ^ j * (1 + ξ ^ 2) := by positivity
    rw [show 2 * B / R ^ j * (1 + ξ ^ 2)⁻¹ = 2 * B / (R ^ j * (1 + ξ ^ 2)) by
      field_simp, le_div_iff₀ hpos]
    nlinarith [norm_nonneg (bandProfile ξ)]
  have hmaj : Integrable fun ξ : ℝ => 2 * B / R ^ j * (1 + ξ ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  calc bandTail R ≤ ∫ ξ in {ξ : ℝ | R < |ξ|}, 2 * B / R ^ j * (1 + ξ ^ 2)⁻¹ :=
        setIntegral_mono_on integrable_bandProfile.norm.integrableOn hmaj.integrableOn
          (measurableSet_lt_abs R) hpt
    _ ≤ ∫ ξ, 2 * B / R ^ j * (1 + ξ ^ 2)⁻¹ :=
        setIntegral_le_integral hmaj (Filter.Eventually.of_forall fun ξ => by positivity)
    _ = 2 * Real.pi * B / R ^ j := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq]
        ring

/-! ### Fourier inversion on the plateau -/

/-- `e(y) = exp(2πiy)` written as in `Sieve.finiteFrequencyPoly`. -/
theorem norm_exp_two_pi (y : ℝ) :
    ‖Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- **Fourier inversion on the plateau**: `∫ K(ξ) e(ξx) dξ = φ(x) = 1` for `|x| ≤ 1`. -/
theorem integral_bandProfile_mul_exp {x : ℝ} (hx : |x| ≤ 1) :
    ∫ ξ, bandProfile ξ * Complex.exp (((2 * Real.pi * (ξ * x) : ℝ) : ℂ) * Complex.I) = 1 := by
  have hint : Integrable (𝓕 (bandPlateau : ℝ → ℂ)) := integrable_bandProfile
  have hinv := bandPlateau.continuous.fourierInv_fourier_eq bandPlateau.integrable hint
  have h := congrFun hinv x
  rw [Real.fourierInv_eq', bandPlateau_apply, innerBump_eq_one one_pos hx] at h
  rw [← Complex.ofReal_one, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, bandProfile]
  rw [mul_comm]
  congr 3
  simp [mul_comm]

/-! ### The band kernel -/

/-- The band kernel `k_{a,L}(η) = L K(Lη) e(−aη)`. -/
def bandLimitKernel (a L η : ℝ) : ℂ :=
  (L : ℂ) * bandProfile (L * η) * Complex.exp (((-2 * Real.pi * (η * a) : ℝ) : ℂ) * Complex.I)

theorem norm_bandLimitKernel {L : ℝ} (hL : 0 ≤ L) (a η : ℝ) :
    ‖bandLimitKernel a L η‖ = L * ‖bandProfile (L * η)‖ := by
  rw [bandLimitKernel, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hL]

theorem integrable_bandLimitKernel {L : ℝ} (hL : 0 < L) (a : ℝ) : Integrable (bandLimitKernel a L) := by
  have h : Integrable fun η => (L : ℂ) * bandProfile (L * η) :=
    (integrable_bandProfile.comp_mul_left' hL.ne').const_mul _
  refine h.mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun η => ?_)
  rw [Complex.norm_exp_ofReal_mul_I]

theorem continuous_bandLimitKernel (a L : ℝ) : Continuous (bandLimitKernel a L) := by
  unfold bandLimitKernel
  have := continuous_bandProfile
  fun_prop

/-- `∫ |k_{a,L}| = ‖K‖₁`. -/
theorem integral_norm_bandLimitKernel {L : ℝ} (hL : 0 < L) (a : ℝ) :
    ∫ η, ‖bandLimitKernel a L η‖ = bandMass := by
  simp_rw [norm_bandLimitKernel hL.le]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun ξ => ‖bandProfile ξ‖) L,
    smul_eq_mul, abs_of_pos (inv_pos.mpr hL), ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul,
    bandMass]

/-- **The band kernel reproduces every frequency within `L` of `a`.** -/
theorem integral_bandLimitKernel_mul_exp {a L x : ℝ} (hL : 0 < L) (hx : |x - a| ≤ L) :
    ∫ η, bandLimitKernel a L η * Complex.exp (((2 * Real.pi * (η * x) : ℝ) : ℂ) * Complex.I) = 1 := by
  set g : ℝ → ℂ := fun ξ =>
    bandProfile ξ * Complex.exp (((2 * Real.pi * (ξ * ((x - a) / L)) : ℝ) : ℂ) * Complex.I)
  have hpt : ∀ η, bandLimitKernel a L η * Complex.exp (((2 * Real.pi * (η * x) : ℝ) : ℂ) * Complex.I)
      = (L : ℂ) * g (L * η) := by
    intro η
    have hreal : -2 * Real.pi * (η * a) + 2 * Real.pi * (η * x) =
        2 * Real.pi * (L * η * ((x - a) / L)) := by
      field_simp
      ring
    simp only [bandLimitKernel, g]
    rw [mul_assoc ((L : ℂ) * _), ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, hreal]
    ring
  have hx' : |(x - a) / L| ≤ 1 := by
    rw [abs_div, abs_of_pos hL, div_le_one hL]
    exact hx
  simp_rw [hpt]
  rw [integral_const_mul, Measure.integral_comp_mul_left g L, integral_bandProfile_mul_exp hx',
    abs_of_pos (inv_pos.mpr hL)]
  rw [Complex.real_smul, mul_one, ← Complex.ofReal_mul, mul_inv_cancel₀ hL.ne',
    Complex.ofReal_one]

/-! ### The reproducing identity and its power forms -/

theorem norm_finiteFrequencyPoly_le {ι : Type*} (c : ι → ℂ) (s : Finset ι) (x : ι → ℝ) (u : ℝ) :
    ‖Sieve.finiteFrequencyPoly c s x u‖ ≤ ∑ i ∈ s, ‖c i‖ := by
  unfold Sieve.finiteFrequencyPoly
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **Reproducing identity**: if every frequency satisfies `|x_i − a| ≤ L`, then
`f(u) = ∫ k_{a,L}(η) f(u + η) dη`. -/
theorem finiteFrequencyPoly_eq_integral_bandLimitKernel {ι : Type*} (c : ι → ℂ) (s : Finset ι)
    (x : ι → ℝ) {a L : ℝ} (hL : 0 < L) (hx : ∀ i ∈ s, |x i - a| ≤ L) (u : ℝ) :
    Sieve.finiteFrequencyPoly c s x u =
      ∫ η, bandLimitKernel a L η * Sieve.finiteFrequencyPoly c s x (u + η) := by
  have hterm : ∀ η, bandLimitKernel a L η * Sieve.finiteFrequencyPoly c s x (u + η) =
      ∑ i ∈ s, c i * Complex.exp (((2 * Real.pi * (u * x i) : ℝ) : ℂ) * Complex.I) *
        (bandLimitKernel a L η * Complex.exp (((2 * Real.pi * (η * x i) : ℝ) : ℂ) * Complex.I)) := by
    intro η
    rw [Sieve.finiteFrequencyPoly, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have e : Complex.exp (((2 * Real.pi * ((u + η) * x i) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((2 * Real.pi * (u * x i) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((2 * Real.pi * (η * x i) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e]
    ring
  simp_rw [hterm]
  rw [integral_finsetSum]
  · rw [Sieve.finiteFrequencyPoly]
    refine sum_congr rfl fun i hi => ?_
    rw [integral_const_mul, integral_bandLimitKernel_mul_exp hL (hx i hi), mul_one]
  · intro i _
    refine Integrable.const_mul ?_ _
    refine (integrable_bandLimitKernel hL a).mul_bdd (c := 1) (by fun_prop)
      (Filter.Eventually.of_forall fun η => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]

/-- `|f(u)| ≤ ∫ |k_{a,L}(η)| |f(u + η)| dη`. -/
theorem norm_finiteFrequencyPoly_le_integral {ι : Type*} (c : ι → ℂ) (s : Finset ι)
    (x : ι → ℝ) {a L : ℝ} (hL : 0 < L) (hx : ∀ i ∈ s, |x i - a| ≤ L) (u : ℝ) :
    ‖Sieve.finiteFrequencyPoly c s x u‖ ≤
      ∫ η, ‖bandLimitKernel a L η‖ * ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ := by
  rw [finiteFrequencyPoly_eq_integral_bandLimitKernel c s x hL hx u]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [norm_mul]

/-- Square and cube forms of the reproducing inequality:
`|f(u)|² ≤ ‖K‖₁ ∫ |k| |f(u+·)|²` and `|f(u)|³ ≤ ‖K‖₁² ∫ |k| |f(u+·)|³`. -/
theorem norm_finiteFrequencyPoly_sq_le {ι : Type*} (c : ι → ℂ) (s : Finset ι)
    (x : ι → ℝ) {a L : ℝ} (hL : 0 < L) (hx : ∀ i ∈ s, |x i - a| ≤ L) (u : ℝ) :
    ‖Sieve.finiteFrequencyPoly c s x u‖ ^ 2 ≤
      bandMass * ∫ η, ‖bandLimitKernel a L η‖ * ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ ^ 2 := by
  have hgc : Continuous fun η => ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ :=
    ((Sieve.continuous_finiteFrequencyPoly c s x).comp (continuous_const.add continuous_id)).norm
  have hρi : Integrable fun η => ‖bandLimitKernel a L η‖ := (integrable_bandLimitKernel hL a).norm
  have hgB : ∀ η, ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ ≤ ∑ i ∈ s, ‖c i‖ :=
    fun η => norm_finiteFrequencyPoly_le c s x _
  have h1 := norm_finiteFrequencyPoly_le_integral c s x hL hx u
  have h2 := GaloisForLFunctions.HTGeometry.sq_integral_weighted_le (μ := volume)
    (fun η => norm_nonneg (bandLimitKernel a L η)) hρi.aestronglyMeasurable hgc.aestronglyMeasurable hρi
    (hρi.mul_bdd (c := (∑ i ∈ s, ‖c i‖) ^ 2) (hgc.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgB η) 2))
  rw [integral_norm_bandLimitKernel hL a] at h2
  calc _ ≤ (∫ η, ‖bandLimitKernel a L η‖ * ‖Sieve.finiteFrequencyPoly c s x (u + η)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem norm_finiteFrequencyPoly_cube_le {ι : Type*} (c : ι → ℂ) (s : Finset ι)
    (x : ι → ℝ) {a L : ℝ} (hL : 0 < L) (hx : ∀ i ∈ s, |x i - a| ≤ L) (u : ℝ) :
    ‖Sieve.finiteFrequencyPoly c s x u‖ ^ 3 ≤
      bandMass ^ 2 * ∫ η, ‖bandLimitKernel a L η‖ * ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ ^ 3 := by
  have hgc : Continuous fun η => ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ :=
    ((Sieve.continuous_finiteFrequencyPoly c s x).comp (continuous_const.add continuous_id)).norm
  have hρi : Integrable fun η => ‖bandLimitKernel a L η‖ := (integrable_bandLimitKernel hL a).norm
  have h1 := norm_finiteFrequencyPoly_le_integral c s x hL hx u
  have hr3 : ∀ y : ℝ, y ^ (3 : ℝ) = y ^ 3 := fun y => by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- weighted power mean (corpus `DeGiorgi.weighted_power_mean_setIntegral`, `p = 3`)
  have hint3 : IntegrableOn (fun η => ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ ^ (3 : ℝ) *
      ‖bandLimitKernel a L η‖) univ := by
    rw [integrableOn_univ]
    simp_rw [hr3]
    refine hρi.bdd_mul (c := (∑ i ∈ s, ‖c i‖) ^ 3) (hgc.pow 3).aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_finiteFrequencyPoly_le c s x (u + η)) 3
  have h3 := DeGiorgi.weighted_power_mean_setIntegral (μ := volume) MeasurableSet.univ (p := 3)
    (by norm_num) (fun η => norm_nonneg (Sieve.finiteFrequencyPoly c s x (u + η)))
    (fun η => norm_nonneg (bandLimitKernel a L η)) hgc.aemeasurable hρi.integrableOn hint3
  simp only [Measure.restrict_univ] at h3
  rw [integral_norm_bandLimitKernel hL a, hr3,
    show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h3
  simp_rw [hr3] at h3
  have e1 : ∫ η, ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ * ‖bandLimitKernel a L η‖ =
      ∫ η, ‖bandLimitKernel a L η‖ * ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ := by
    congr 1; funext η; ring
  have e2 : ∫ η, ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ ^ 3 * ‖bandLimitKernel a L η‖ =
      ∫ η, ‖bandLimitKernel a L η‖ * ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ ^ 3 := by
    congr 1; funext η; ring
  rw [e1, e2] at h3
  calc _ ≤ (∫ η, ‖bandLimitKernel a L η‖ * ‖Sieve.finiteFrequencyPoly c s x (u + η)‖) ^ 3 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 3
    _ ≤ _ := h3

/-! ### Truncation of the kernel integral -/

/-- `∫_{|η| > δ} |k_{a,L}(η)| dη = ∫_{|ξ| > Lδ} |K(ξ)| dξ`. -/
theorem setIntegral_norm_bandLimitKernel_tail {L : ℝ} (hL : 0 < L) (a δ : ℝ) :
    ∫ η in {η : ℝ | δ < |η|}, ‖bandLimitKernel a L η‖ = bandTail (L * δ) := by
  have hind : ∀ η, {η : ℝ | δ < |η|}.indicator (fun η => ‖bandLimitKernel a L η‖) η =
      L * {ξ : ℝ | L * δ < |ξ|}.indicator (fun ξ => ‖bandProfile ξ‖) (L * η) := by
    intro η
    have hiff : L * δ < |L * η| ↔ δ < |η| := by
      rw [abs_mul, abs_of_pos hL]
      exact mul_lt_mul_iff_of_pos_left hL
    by_cases h : δ < |η|
    · rw [indicator_of_mem (show η ∈ {η : ℝ | δ < |η|} from h),
        indicator_of_mem (show L * η ∈ {ξ : ℝ | L * δ < |ξ|} from hiff.mpr h),
        norm_bandLimitKernel hL.le]
    · rw [indicator_of_notMem (show η ∉ {η : ℝ | δ < |η|} from h),
        indicator_of_notMem (show L * η ∉ {ξ : ℝ | L * δ < |ξ|} from fun h' => h (hiff.mp h')),
        mul_zero]
  rw [← integral_indicator (measurableSet_lt_abs δ)]
  simp_rw [hind]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun ξ => {ξ : ℝ | L * δ < |ξ|}.indicator (fun ξ => ‖bandProfile ξ‖) ξ) L,
    integral_indicator (measurableSet_lt_abs _), smul_eq_mul, abs_of_pos (inv_pos.mpr hL),
    ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul, bandTail]

/-- **Truncation.** For `0 ≤ g ≤ B` continuous:
`∫ |k_{a,L}| g ≤ L ‖K‖_∞ ∫_{−δ}^{δ} g + B ∫_{|ξ| > Lδ} |K|`. -/
theorem integral_norm_bandLimitKernel_mul_le {a L δ B : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ) {g : ℝ → ℝ}
    (hg : ∀ y, 0 ≤ g y) (hgB : ∀ y, g y ≤ B) (hgc : Continuous g) :
    ∫ η, ‖bandLimitKernel a L η‖ * g η ≤
      L * bandSup * (∫ η in -δ..δ, g η) + B * bandTail (L * δ) := by
  have hρi : Integrable fun η => ‖bandLimitKernel a L η‖ := (integrable_bandLimitKernel hL a).norm
  have hF : Integrable fun η => ‖bandLimitKernel a L η‖ * g η :=
    hρi.mul_bdd (c := B) hgc.aestronglyMeasurable (Filter.Eventually.of_forall fun η => by
      rw [Real.norm_of_nonneg (hg η)]; exact hgB η)
  have hcompl : (Icc (-δ) δ)ᶜ = {η : ℝ | δ < |η|} := by
    ext η
    rw [Set.mem_compl_iff, Set.mem_Icc, Set.mem_setOf_eq, ← abs_le, not_le]
  have hin : ∫ η in Icc (-δ) δ, ‖bandLimitKernel a L η‖ * g η ≤ L * bandSup * (∫ η in -δ..δ, g η) := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      ← integral_const_mul]
    refine setIntegral_mono_on hF.integrableOn
      ((hgc.integrableOn_Icc).const_mul _) measurableSet_Icc fun η _ => ?_
    rw [norm_bandLimitKernel hL.le]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (norm_bandProfile_le _) hL.le) (hg η)
  have hout : ∫ η in {η : ℝ | δ < |η|}, ‖bandLimitKernel a L η‖ * g η ≤ B * bandTail (L * δ) := by
    rw [← setIntegral_norm_bandLimitKernel_tail hL a δ, ← integral_const_mul]
    refine setIntegral_mono_on hF.integrableOn (hρi.const_mul B).integrableOn
      (measurableSet_lt_abs δ) fun η _ => ?_
    rw [mul_comm B]
    exact mul_le_mul_of_nonneg_left (hgB η) (norm_nonneg _)
  calc ∫ η, ‖bandLimitKernel a L η‖ * g η
      = (∫ η in Icc (-δ) δ, ‖bandLimitKernel a L η‖ * g η) +
          ∫ η in {η : ℝ | δ < |η|}, ‖bandLimitKernel a L η‖ * g η := by
        rw [← hcompl]; exact (integral_add_compl measurableSet_Icc hF).symm
    _ ≤ _ := add_le_add hin hout

/-- **Local form, first power.** `|f(u)| ≤ L ‖K‖_∞ ∫_{−δ}^{δ} |f(u+η)| dη + (Σ|c_i|) ∫_{|ξ|>Lδ} |K|`. -/
theorem norm_finiteFrequencyPoly_le_local {ι : Type*} (c : ι → ℂ) (s : Finset ι)
    (x : ι → ℝ) {a L δ : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ) (hx : ∀ i ∈ s, |x i - a| ≤ L) (u : ℝ) :
    ‖Sieve.finiteFrequencyPoly c s x u‖ ≤
      L * bandSup * (∫ η in -δ..δ, ‖Sieve.finiteFrequencyPoly c s x (u + η)‖) +
        (∑ i ∈ s, ‖c i‖) * bandTail (L * δ) :=
  (norm_finiteFrequencyPoly_le_integral c s x hL hx u).trans
    (integral_norm_bandLimitKernel_mul_le hL hδ (fun _ => norm_nonneg _)
      (fun η => norm_finiteFrequencyPoly_le c s x (u + η))
      ((Sieve.continuous_finiteFrequencyPoly c s x).comp (continuous_const.add continuous_id)).norm)

/-- **Local form, third power.**
`|f(u)|³ ≤ ‖K‖₁² (L ‖K‖_∞ ∫_{−δ}^{δ} |f(u+η)|³ dη + (Σ|c_i|)³ ∫_{|ξ|>Lδ} |K|)`. -/
theorem norm_finiteFrequencyPoly_cube_le_local {ι : Type*} (c : ι → ℂ) (s : Finset ι)
    (x : ι → ℝ) {a L δ : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ) (hx : ∀ i ∈ s, |x i - a| ≤ L) (u : ℝ) :
    ‖Sieve.finiteFrequencyPoly c s x u‖ ^ 3 ≤
      bandMass ^ 2 * (L * bandSup * (∫ η in -δ..δ, ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ ^ 3) +
        (∑ i ∈ s, ‖c i‖) ^ 3 * bandTail (L * δ)) := by
  refine (norm_finiteFrequencyPoly_cube_le c s x hL hx u).trans
    (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  exact integral_norm_bandLimitKernel_mul_le hL hδ (fun _ => by positivity)
    (fun η => pow_le_pow_left₀ (norm_nonneg _) (norm_finiteFrequencyPoly_le c s x (u + η)) 3)
    (((Sieve.continuous_finiteFrequencyPoly c s x).comp
      (continuous_const.add continuous_id)).norm.pow 3)

/-- **Shifted square form at unit scale.** For `|s| ≤ 1`:
`|f(u − s)|² ≤ ‖K‖₁ ∫ 3 bandCauchy/(1+η²) · |f(u + η)|² dη`, uniformly in the shift. -/
theorem norm_finiteFrequencyPoly_sub_sq_le {ι : Type*} (c : ι → ℂ) (s : Finset ι)
    (x : ι → ℝ) {a : ℝ} (hx : ∀ i ∈ s, |x i - a| ≤ 1) (u σ : ℝ) (hσ : |σ| ≤ 1) :
    ‖Sieve.finiteFrequencyPoly c s x (u - σ)‖ ^ 2 ≤
      bandMass * ∫ η, 3 * bandCauchy / (1 + η ^ 2) *
        ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ ^ 2 := by
  have hFc : Continuous fun η => ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ ^ 2 :=
    ((Sieve.continuous_finiteFrequencyPoly c s x).comp (continuous_const_add u)).norm.pow 2
  have hFB : ∀ η, ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ ^ 2 ≤ (∑ i ∈ s, ‖c i‖) ^ 2 :=
    fun η => pow_le_pow_left₀ (norm_nonneg _) (norm_finiteFrequencyPoly_le c s x _) 2
  have h := norm_finiteFrequencyPoly_sq_le c s x one_pos hx (u - σ)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ bandMass_nonneg)
  -- shift the variable by `σ`
  have hshift : ∫ η, ‖bandLimitKernel a 1 η‖ * ‖Sieve.finiteFrequencyPoly c s x (u - σ + η)‖ ^ 2 =
      ∫ η, ‖bandLimitKernel a 1 (η + σ)‖ * ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ ^ 2 := by
    rw [← integral_add_right_eq_self
      (fun η => ‖bandLimitKernel a 1 η‖ * ‖Sieve.finiteFrequencyPoly c s x (u - σ + η)‖ ^ 2) σ]
    congr 1; funext η
    congr 4; ring
  rw [hshift]
  have hmaj : Integrable fun η =>
      3 * bandCauchy / (1 + η ^ 2) * ‖Sieve.finiteFrequencyPoly c s x (u + η)‖ ^ 2 := by
    have h1 : Integrable fun η : ℝ => 3 * bandCauchy / (1 + η ^ 2) := by
      simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (3 * bandCauchy)
    refine h1.mul_bdd (c := (∑ i ∈ s, ‖c i‖) ^ 2) hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hFB η
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun η => by positivity) hmaj
    (Filter.Eventually.of_forall fun η => ?_)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [norm_bandLimitKernel zero_le_one, one_mul, one_mul]
  refine (norm_bandProfile_le_cauchy _).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hc := bandCauchy_nonneg
  have hsq : 1 + η ^ 2 ≤ 3 * (1 + (η + σ) ^ 2) := by
    have : σ ^ 2 ≤ 1 := by nlinarith [abs_nonneg σ, sq_abs σ]
    nlinarith [sq_nonneg (η + 2 * σ), sq_nonneg (η + σ)]
  nlinarith

end

end RHTower.GuthMaynard
