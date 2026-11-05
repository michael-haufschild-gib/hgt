import GaloisForLFunctions.FrustratedArithmeticDirichletForms.TheEntryIsLogarithmicallySoft
import GaloisForLFunctions.FrustratedArithmeticDirichletForms.TheWindowEnergyHasNoTrace
import GaloisForLFunctions.RHTower.CHMDEvenSectorPointSpectrum
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic
import GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry.TheSliverPotentialCannotCarryThePrimeThree

/-!
# Soft entry in every stage fibre

`TheEntryIsLogarithmicallySoft` bounds the stage fibre of a newly entered weight from outside: after
the entry of `n₀` the admissible weights satisfy `|λ(n₀)| ≤ √n₀(A log(1/δ) + B)`, `δ = 2c − log n₀`.
This module bounds it from inside, at every entry (SWC proves the planar case of the primes `2, 3`):

* **The lag of the newest power is an edge datum** (`abs_integral_mul_shift_le_edgeKilling`). For a
  real test on `[−c, c]` and a lag `ℓ = 2c − δ`, `Ω(δ)·|∫f(s)f(s − ℓ)ds| ≤ ½𝒦(f) ≤ ½𝒥(f)`: the
  correlation at `ℓ` lives on the two edge slivers of width `δ`, which the edge killing energy pays
  at the Lévy tail rate `Ω(δ) = ∫_δ^∞ ω`.
* **Soft entry** (`withWeight_mem_realCalibration_of_margin`). If the window form with weights `λ` has
  a Lévy margin `η` (`η𝒥(f) ≤ W_λ(f)` on real tests), every weight `t` with
  `|t − λ(n₀)| ≤ √n₀ η Ω(δ)` at the acting `n₀` keeps the window nonnegative.

* **The summed edge law** (`abs_re_weightedPrimePart_le`, `add_mem_calibration_of_edgeLaw`). Summing
  over the acting `n`, `|P_μ(f)| ≤ E_c(μ)𝒥(f)` with the edge-law constant
  `E_c(μ) = Σ_n |μ(n)|/(√n Ω(2c − log n))`; a window form with Lévy margin `E_c(μ)` stays nonnegative
  under the perturbation `μ` of its weights. This is the size-only certificate.
* **It dies at edge-law constant one** (`not_edgeLaw_of_one_le`). On odd tests the archimedean–polar
  form is `H = 2θ′(0)‖f‖² + 𝒥 − 2S² < 𝒥` (`re_archPolar_eq`, `θ′(0) < 0`), so once `E_c(λ) ≥ 1` the
  Lévy energy cannot pay the primes by size: payment must be collective and by sign. For `ζ` this
  happens on every window with `2c ≥ log 2 + 8` (`edgeLaw_fails_for_vonMangoldt`), where the edge
  cost of the prime `2` alone exceeds one.

With `Ω(δ) ≥ (e^{−1/2}/2)log(1/δ)` (SWC) the stage fibre therefore contains an interval of length
`√n₀ η e^{−1/2} log(1/δ)` and lies in one of length `O(√n₀ log(1/δ))`: **the entry of every prime power
is logarithmically soft from both sides**, the inner constant proportional to the margin
(`entry_is_logarithmically_soft`, `stageFibre_two_sided`). Real tests decide the calibration space
(`realCalibration_eq_calibration`). Beyond the sliver (`δ` of order one) both bounds are bounded, and
the only remaining mechanism is the sign of the sliver reflection.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower _root_.Zeta23

/-- The real calibration space: weights for which the window form is nonnegative on real tests. -/
def realCalibration (c : ℝ) : Set (ℕ → ℝ) :=
  {lam | ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c →
    0 ≤ (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re}

theorem calibration_subset_realCalibration (c : ℝ) : calibration c ⊆ realCalibration c :=
  fun _ hlam _ hf hfs => hlam _ (Complex.ofRealCLM.contDiff.comp hf) hfs

/-- The window form of a complex test is the sum over its real and imaginary parts (RHTower), so
real tests decide the calibration space. -/
theorem realCalibration_subset_calibration (c : ℝ) : realCalibration c ⊆ calibration c := by
  intro lam hlam f hf hfs
  have hfc : HasCompactSupport f := HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c))
    fun u hu => image_eq_zero_of_notMem_tsupport fun h => hu (hfs h)
  have hsub : ∀ g : ℂ → ℝ, g 0 = 0 → tsupport (fun u => ((g (f u) : ℝ) : ℂ)) ⊆ Icc (-c) c :=
    fun g hg => closure_minimal (fun u hu => hfs (subset_tsupport _ (Function.mem_support.mpr
      fun h0 => (Function.mem_support.mp hu) (by simp [h0, hg])))) isClosed_Icc
  exact (add_nonneg
    (hlam (fun u => (f u).re) (Complex.reCLM.contDiff.comp hf) (hsub Complex.re Complex.zero_re))
    (hlam (fun u => (f u).im) (Complex.imCLM.contDiff.comp hf) (hsub Complex.im Complex.zero_im))).trans_eq
    (CHMDPolar.re_weilFullFunctional_split lam ⟨f, hf, hfc⟩).symm

theorem realCalibration_eq_calibration (c : ℝ) : realCalibration c = calibration c :=
  (realCalibration_subset_calibration c).antisymm (calibration_subset_realCalibration c)

theorem vanish_of_tsupport {f : ℝ → ℝ} {c : ℝ} (hfs : tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c) :
    ∀ u, u ∉ Icc (-c) c → f u = 0 := fun u hu => by
  have h := image_eq_zero_of_notMem_tsupport (fun h => hu (hfs h))
  exact_mod_cast h

/-- The edge killing energy pays both edge masses at the Lévy tail rate. -/
theorem levyTail_mul_edgeMasses_le_edgeKilling {f : ℝ → ℝ} {a b : ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : HasCompactSupport f) (hab : ∀ u, u ∉ Icc a b → f u = 0) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in Ioi δ, archLevyDensity x) * (leftEdgeMass f a δ + rightEdgeMass f b δ) ≤
      edgeKilling f a b := by
  have hfc := hf.continuous
  have hL := integrableOn_leftEdge hf hfs hab
  have hR := integrableOn_rightEdge hf hfs hab
  have hsum : IntegrableOn (fun x => archLevyDensity x * (leftEdgeMass f a x + rightEdgeMass f b x))
      (Ioi 0) := (hL.add hR).congr_fun (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  have hint : IntegrableOn
      (fun x => (Ioi δ).indicator archLevyDensity x * (leftEdgeMass f a δ + rightEdgeMass f b δ))
      (Ioi 0) := by
    refine Integrable.mul_const ?_ _
    refine (integrable_indicator_iff measurableSet_Ioi).mpr ?_
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi hδ.le)]
    exact WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hδ
  have hle := integral_mono_ae hint hsum (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => by
    beta_reduce
    have hω := (archLevyDensity_pos (show (0 : ℝ) < x from hx)).le
    by_cases hxδ : x ∈ Ioi δ
    · rw [indicator_of_mem hxδ]
      exact mul_le_mul_of_nonneg_left (add_le_add
        (monotone_leftEdgeMass hfc hfs a (le_of_lt hxδ))
        (monotone_rightEdgeMass hfc hfs b (le_of_lt hxδ))) hω
    · rw [indicator_of_notMem hxδ, zero_mul]
      exact mul_nonneg hω (add_nonneg (leftEdgeMass_nonneg f a x) (rightEdgeMass_nonneg f b x)))
  unfold edgeKilling
  refine le_trans (le_of_eq ?_) hle
  rw [integral_mul_const, setIntegral_indicator measurableSet_Ioi,
    inter_eq_self_of_subset_right (Ioi_subset_Ioi hδ.le)]

/-- **The lag of the newest power is an edge datum**: for `f` vanishing off `[−c, c]` and
`ℓ = 2c − δ`, `2Ω(δ)·|∫f(s)f(s − ℓ)ds| ≤ 𝒥(f)`. -/
theorem abs_integral_mul_shift_le_edgeKilling {f : ℝ → ℝ} {c δ : ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : HasCompactSupport f) (hab : ∀ u, u ∉ Icc (-c) c → f u = 0) (hδ : 0 < δ) :
    2 * (∫ x in Ioi δ, archLevyDensity x) * |∫ s, f s * f (s - (2 * c - δ))| ≤ levyEnergy f := by
  set ℓ := 2 * c - δ
  have hfc := hf.continuous
  have hsq := integrable_sq_of_cont hfc hfs
  -- pointwise: the product lives on the two edge slivers
  have hind : ∀ (A : Set ℝ) (x : ℝ), 0 ≤ A.indicator (fun u => f u ^ 2) x :=
    fun A x => indicator_nonneg (fun u _ => sq_nonneg (f u)) x
  have hpt : ∀ s, |f s * f (s - ℓ)| ≤
      (1 / 2) * (Ici (c - δ)).indicator (fun u => f u ^ 2) s +
        (1 / 2) * (Iic (-c + δ)).indicator (fun u => f u ^ 2) (s - ℓ) := by
    intro s
    by_cases h0 : f s = 0 ∨ f (s - ℓ) = 0
    · have hl : |f s * f (s - ℓ)| = 0 := by
        rcases h0 with h | h <;> simp [h]
      rw [hl]
      exact add_nonneg (mul_nonneg (by norm_num) (hind _ _)) (mul_nonneg (by norm_num) (hind _ _))
    · push Not at h0
      have hs : s ∈ Icc (-c) c := by by_contra h; exact h0.1 (hab s h)
      have hs' : s - ℓ ∈ Icc (-c) c := by by_contra h; exact h0.2 (hab _ h)
      have m1 : s ∈ Ici (c - δ) := by simp only [mem_Ici, ℓ] at *; linarith [hs'.1]
      have m2 : s - ℓ ∈ Iic (-c + δ) := by simp only [mem_Iic, ℓ] at *; linarith [hs.2]
      rw [indicator_of_mem m1, indicator_of_mem m2, abs_mul]
      nlinarith [sq_nonneg (|f s| - |f (s - ℓ)|), sq_abs (f s), sq_abs (f (s - ℓ))]
  have hiR : Integrable ((Ici (c - δ)).indicator fun u => f u ^ 2) := hsq.indicator measurableSet_Ici
  have hiL : Integrable fun s => (Iic (-c + δ)).indicator (fun u => f u ^ 2) (s - ℓ) :=
    (hsq.indicator measurableSet_Iic).comp_sub_right ℓ
  have hprod : Integrable fun s => f s * f (s - ℓ) :=
    (hfc.mul (hfc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      hfs.mul_right
  have hbound : |∫ s, f s * f (s - ℓ)| ≤ (1 / 2) * (leftEdgeMass f (-c) δ + rightEdgeMass f c δ) := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ s, |f s * f (s - ℓ)| ≤ ∫ s, ((1 / 2) * (Ici (c - δ)).indicator (fun u => f u ^ 2) s +
          (1 / 2) * (Iic (-c + δ)).indicator (fun u => f u ^ 2) (s - ℓ)) :=
          integral_mono hprod.abs ((hiR.const_mul _).add (hiL.const_mul _)) hpt
      _ = (1 / 2) * (leftEdgeMass f (-c) δ + rightEdgeMass f c δ) := by
          rw [integral_add (hiR.const_mul _) (hiL.const_mul _), integral_const_mul,
            integral_const_mul, integral_sub_right_eq_self (μ := volume)
              (fun s => (Iic (-c + δ)).indicator (fun u => f u ^ 2) s) ℓ,
            integral_indicator measurableSet_Ici, integral_indicator measurableSet_Iic]
          unfold leftEdgeMass rightEdgeMass
          rw [setIntegral_congr_set (Iio_ae_eq_Iic (μ := volume) (a := -c + δ)).symm,
            setIntegral_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := c - δ)).symm]
          ring
  have hk := levyTail_mul_edgeMasses_le_edgeKilling hf hfs hab hδ
  have hJ := edgeKilling_le_levyEnergy hf hfs hab
  have hΩ : 0 ≤ ∫ x in Ioi δ, archLevyDensity x :=
    setIntegral_nonneg measurableSet_Ioi fun x hx => (archLevyDensity_pos (lt_trans hδ hx)).le
  calc 2 * (∫ x in Ioi δ, archLevyDensity x) * |∫ s, f s * f (s - ℓ)|
      ≤ 2 * (∫ x in Ioi δ, archLevyDensity x) *
          ((1 / 2) * (leftEdgeMass f (-c) δ + rightEdgeMass f c δ)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (∫ x in Ioi δ, archLevyDensity x) * (leftEdgeMass f (-c) δ + rightEdgeMass f c δ) := by ring
    _ ≤ levyEnergy f := hk.trans hJ

/-- **Soft entry at every prime power.** If the weights `λ` give the window `[−c, c]` a Lévy margin
`η`, every value `t` of the weight at an acting `n₀` with `|t − λ(n₀)| ≤ √n₀ η Ω(2c − log n₀)` keeps
the window nonnegative. -/
theorem withWeight_mem_realCalibration_of_margin {c η : ℝ} {n₀ : ℕ} (hn₀ : 2 ≤ n₀)
    (hc : Real.log n₀ < 2 * c) (hη : 0 ≤ η) {lam : ℕ → ℝ}
    (hmargin : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c →
      η * levyEnergy f ≤
        (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re)
    {t : ℝ} (ht : |t - lam n₀| ≤
      Real.sqrt n₀ * η * ∫ x in Ioi (2 * c - Real.log n₀), archLevyDensity x) :
    withWeight lam n₀ t ∈ realCalibration c := by
  intro f hf hfs
  have hm := hmargin f hf hfs
  have hab := vanish_of_tsupport hfs
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c)) fun u hu => hab u hu
  set δ := 2 * c - Real.log n₀
  have hδ : 0 < δ := by simp only [δ]; linarith
  obtain ⟨-, -, hsupp, -⟩ := weilTest_self_data (Complex.ofRealCLM.contDiff.comp hf) hfs
  set k := EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))
  set N := ⌊Real.exp (2 * c)⌋₊ + 1
  have hN : ∀ n : ℕ, N ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := by
    intro n hn
    have hn' : Real.exp (2 * c) < n := by
      have := Nat.lt_floor_add_one (Real.exp (2 * c))
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      push_cast [N] at h2
      linarith
    have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hn'
    have hlog : 2 * c < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hn'
    exact ⟨image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).2; linarith,
      image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).1; linarith⟩
  rw [re_weilFullFunctional_withWeight lam hn₀ t hN]
  have hk : ∀ y, k y = ((∫ s, f s * f (s - y) : ℝ) : ℂ) := weilTest_ofReal_ofReal_eq f f
  have hlagneg : ∫ s, f s * f (s - -Real.log n₀) = ∫ s, f s * f (s - Real.log n₀) :=
    integral_mul_shift_neg f (Real.log n₀)
  rw [hk, hk, hlagneg, ← Complex.ofReal_add, Complex.ofReal_re]
  have hlag : Real.log n₀ = 2 * c - δ := by simp only [δ]; ring
  have hedge := abs_integral_mul_shift_le_edgeKilling hf hfc hab hδ
  rw [← hlag] at hedge
  set I := ∫ s, f s * f (s - Real.log n₀)
  set Ω := ∫ x in Ioi δ, archLevyDensity x
  have hΩ : 0 ≤ Ω := setIntegral_nonneg measurableSet_Ioi fun x hx => (archLevyDensity_pos (lt_trans hδ hx)).le
  have hsq : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
  -- `|Δ/√n₀ · 2I| ≤ ηΩ · 2|I| ≤ η𝒥`
  have h1 : |(t - lam n₀) / Real.sqrt n₀ * (I + I)| ≤ η * levyEnergy f := by
    rw [abs_mul, abs_div, abs_of_pos hsq, show I + I = 2 * I by ring, abs_mul, abs_two]
    have h2 : |t - lam n₀| / Real.sqrt n₀ ≤ η * Ω := by
      rw [div_le_iff₀ hsq]; linarith
    calc |t - lam n₀| / Real.sqrt n₀ * (2 * |I|) ≤ η * Ω * (2 * |I|) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = η * (2 * Ω * |I|) := by ring
      _ ≤ η * levyEnergy f := mul_le_mul_of_nonneg_left hedge hη
  have h3 := le_abs_self ((t - lam n₀) / Real.sqrt n₀ * (I + I))
  linarith

/-- **The entry is logarithmically soft from both sides.** For an acting `n₀` with sliver
`δ = 2c − log n₀ ≤ 1` and weights with Lévy margin `η`, the stage fibre of `n₀` contains every `t`
with `|t − λ(n₀)| ≤ √n₀ η (e^{−1/2}/2) log(1/δ)`. -/
theorem entry_is_logarithmically_soft {c η : ℝ} {n₀ : ℕ} (hn₀ : 2 ≤ n₀)
    (hc : Real.log n₀ < 2 * c) (hδ1 : 2 * c - Real.log n₀ ≤ 1) (hη : 0 ≤ η) {lam : ℕ → ℝ}
    (hmargin : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c →
      η * levyEnergy f ≤
        (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re)
    {t : ℝ} (ht : |t - lam n₀| ≤
      Real.sqrt n₀ * η * (Real.exp (-1 / 2) / 2 * Real.log (1 / (2 * c - Real.log n₀)))) :
    withWeight lam n₀ t ∈ realCalibration c := by
  refine withWeight_mem_realCalibration_of_margin hn₀ hc hη hmargin (ht.trans ?_)
  have hΩ := SignedWindowCriticality.PrimeThreeEntry.levyTail_ge_log
    (show 0 < 2 * c - Real.log n₀ by linarith) hδ1
  have hsq : 0 ≤ Real.sqrt n₀ := Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_left hΩ (mul_nonneg hsq hη)

/-- **The two-sided entry law.** For an acting `n₀` there are `δ₀ > 0` and constants `A, B` such that
on every window with sliver `δ = 2c − log n₀ ≤ δ₀` and for all weights `λ` with Lévy margin `η`, the
stage fibre `{t : λ with λ(n₀) := t lies in 𝒜(c)}` contains the interval of radius
`√n₀ η (e^{−1/2}/2) log(1/δ)` about `λ(n₀)` and lies in the interval of radius
`√n₀(A log(1/δ) + B)` about `0`. -/
theorem stageFibre_two_sided {n₀ : ℕ} (hn₀ : 2 ≤ n₀) :
    ∃ δ₀ A B : ℝ, 0 < δ₀ ∧ ∀ c : ℝ, Real.log n₀ < 2 * c → 2 * c - Real.log n₀ ≤ δ₀ →
      ∀ (η : ℝ) (lam : ℕ → ℝ), 0 ≤ η →
      (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c →
        η * levyEnergy f ≤
          (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re) →
      Icc (lam n₀ - Real.sqrt n₀ * η *
            (Real.exp (-1 / 2) / 2 * Real.log (1 / (2 * c - Real.log n₀))))
          (lam n₀ + Real.sqrt n₀ * η *
            (Real.exp (-1 / 2) / 2 * Real.log (1 / (2 * c - Real.log n₀)))) ⊆
        {t | withWeight lam n₀ t ∈ calibration c} ∧
      {t | withWeight lam n₀ t ∈ calibration c} ⊆
        Icc (-(Real.sqrt n₀ * (A * Real.log (1 / (2 * c - Real.log n₀)) + B)))
          (Real.sqrt n₀ * (A * Real.log (1 / (2 * c - Real.log n₀)) + B)) := by
  obtain ⟨δ₀, A, B, hδ₀, hout⟩ := abs_calibration_coord_le_log hn₀
  refine ⟨min δ₀ 1, A, B, lt_min hδ₀ one_pos, fun c hc hδ η lam hη hmargin => ⟨?_, ?_⟩⟩
  · intro t ht
    rw [mem_setOf_eq, ← realCalibration_eq_calibration]
    exact entry_is_logarithmically_soft hn₀ hc (hδ.trans (min_le_right _ _)) hη hmargin
      (abs_sub_le_iff.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  · intro t ht
    have h := hout c hc (hδ.trans (min_le_left _ _)) _ ht
    rw [withWeight, Function.update_self] at h
    exact abs_le.mp h

/-! ### The summed edge law -/

/-- The Lévy tail `Ω(δ) = ∫_δ^∞ ω` is positive. -/
theorem levyTail_pos {δ : ℝ} (hδ : 0 < δ) : 0 < ∫ x in Ioi δ, archLevyDensity x := by
  rw [WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hδ]
  exact WeilLevyPoleGauss.archLevyAntideriv_pos hδ

/-- A lag of at least the window length is invisible: `∫f(s)f(s − ℓ)ds = 0` for `ℓ ≥ 2c`. -/
theorem integral_mul_shift_eq_zero {f : ℝ → ℝ} {c ℓ : ℝ} (hab : ∀ u, u ∉ Icc (-c) c → f u = 0)
    (hℓ : 2 * c ≤ ℓ) : ∫ s, f s * f (s - ℓ) = 0 := by
  refine integral_eq_zero_of_ae (ae_iff.mpr (measure_mono_null (t := {c}) ?_ (measure_singleton c)))
  intro s hs
  simp only [mem_setOf_eq, Pi.zero_apply] at hs
  have h1 : s ∈ Icc (-c) c := by by_contra h; exact hs (by rw [hab s h, zero_mul])
  have h2 : s - ℓ ∈ Icc (-c) c := by by_contra h; exact hs (by rw [hab _ h, mul_zero])
  exact le_antisymm h1.2 (by linarith [h2.1])

/-- The edge cost of the weight `λ(n)` on `[−c, c]`: `|λ(n)|/(√n Ω(2c − log n))` for an acting `n`
(`2 ≤ n`, `log n < 2c`), `0` otherwise. -/
def edgeCost (c : ℝ) (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n ∧ Real.log n < 2 * c then
    |lam n| / (Real.sqrt n * ∫ x in Ioi (2 * c - Real.log n), archLevyDensity x) else 0

/-- The edge-law constant `E_c(λ)`: the sum of the edge costs of all weights acting on `[−c, c]`. -/
def edgeLawConstant (c : ℝ) (lam : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊Real.exp (2 * c)⌋₊ + 1), edgeCost c lam n

/-- Each prime power pays its lag at its edge cost. -/
theorem abs_primeTerm_le_edgeCost {f : ℝ → ℝ} {c : ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hab : ∀ u, u ∉ Icc (-c) c → f u = 0) (lam : ℕ → ℝ) (n : ℕ) :
    |(if 2 ≤ n then lam n / Real.sqrt n else 0) * (2 * ∫ s, f s * f (s - Real.log n))| ≤
      edgeCost c lam n * levyEnergy f := by
  unfold edgeCost
  by_cases hn : 2 ≤ n
  · by_cases hc : Real.log n < 2 * c
    · rw [if_pos hn, if_pos ⟨hn, hc⟩]
      have hδ : 0 < 2 * c - Real.log n := by linarith
      have hΩ := levyTail_pos hδ
      have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
      have hedge := abs_integral_mul_shift_le_edgeKilling hf hfc hab hδ
      rw [show 2 * c - (2 * c - Real.log n) = Real.log n by ring] at hedge
      set Ω := ∫ x in Ioi (2 * c - Real.log n), archLevyDensity x
      set I := ∫ s, f s * f (s - Real.log n)
      have h2I : 2 * |I| ≤ levyEnergy f / Ω := by
        rw [le_div_iff₀ hΩ]; linarith
      calc |lam n / Real.sqrt n * (2 * I)| = |lam n| / Real.sqrt n * (2 * |I|) := by
            rw [abs_mul, abs_div, abs_of_pos hsq, abs_mul, abs_two]
        _ ≤ |lam n| / Real.sqrt n * (levyEnergy f / Ω) :=
            mul_le_mul_of_nonneg_left h2I (div_nonneg (abs_nonneg _) hsq.le)
        _ = |lam n| / (Real.sqrt n * Ω) * levyEnergy f := by ring
    · rw [if_pos hn, if_neg (fun h => hc h.2), integral_mul_shift_eq_zero hab (not_lt.mp hc)]
      simp
  · rw [if_neg hn, if_neg (fun h => hn h.1)]
    simp

/-- **The summed edge law.** On a real test in `[−c, c]` the weighted prime part is at most the
edge-law constant times the Lévy energy: `|P_λ(f)| ≤ E_c(λ)𝒥(f)`. -/
theorem abs_re_weightedPrimePart_le {f : ℝ → ℝ} {c : ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c) (lam : ℕ → ℝ) :
    |(weightedPrimePart lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re| ≤
      edgeLawConstant c lam * levyEnergy f := by
  have hab := vanish_of_tsupport hfs
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c)) fun u hu => hab u hu
  obtain ⟨-, -, hsupp, -⟩ := weilTest_self_data (Complex.ofRealCLM.contDiff.comp hf) hfs
  set k := EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))
  have hN : ∀ n : ℕ, ⌊Real.exp (2 * c)⌋₊ + 1 ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := by
    intro n hn
    have hn' : Real.exp (2 * c) < n := by
      have := Nat.lt_floor_add_one (Real.exp (2 * c))
      have h2 : ((⌊Real.exp (2 * c)⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hn'
    have hlog : 2 * c < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hn'
    exact ⟨image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).2; linarith,
      image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).1; linarith⟩
  have hk : ∀ y, k y = ((∫ s, f s * f (s - y) : ℝ) : ℂ) := weilTest_ofReal_ofReal_eq f f
  have hterm : ∀ n : ℕ, (((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))).re =
      (if 2 ≤ n then lam n / Real.sqrt n else 0) * (2 * ∫ s, f s * f (s - Real.log n)) := by
    intro n
    rw [hk, hk, integral_mul_shift_neg, ← Complex.ofReal_add, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  rw [weightedPrimePart_affine hN lam, Complex.re_sum]
  simp_rw [hterm]
  unfold edgeLawConstant
  rw [Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun n _ => abs_primeTerm_le_edgeCost hf hfc hab lam n)

/-- **The edge-law certificate.** If the window form with weights `λ` dominates `E_c(μ)` times the
Lévy energy on real tests in `[−c, c]`, then `λ + μ` lies in the calibration space: a perturbation of
the weights is paid by size alone up to its edge-law constant. -/
theorem add_mem_calibration_of_edgeLaw {c : ℝ} {lam mu : ℕ → ℝ}
    (h : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c →
      edgeLawConstant c mu * levyEnergy f ≤
        (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re) :
    lam + mu ∈ calibration c := by
  refine realCalibration_subset_calibration c fun f hf hfs => ?_
  obtain ⟨-, -, hsupp, -⟩ := weilTest_self_data (Complex.ofRealCLM.contDiff.comp hf) hfs
  set k := EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))
  have hN : ∀ n : ℕ, ⌊Real.exp (2 * c)⌋₊ + 1 ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := by
    intro n hn
    have hn' : Real.exp (2 * c) < n := by
      have := Nat.lt_floor_add_one (Real.exp (2 * c))
      have h2 : ((⌊Real.exp (2 * c)⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hn'
    have hlog : 2 * c < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hn'
    exact ⟨image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).2; linarith,
      image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).1; linarith⟩
  have hadd : weightedPrimePart (lam + mu) k = weightedPrimePart lam k + weightedPrimePart mu k := by
    rw [weightedPrimePart_affine hN, weightedPrimePart_affine hN, weightedPrimePart_affine hN,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> push_cast [Pi.add_apply] <;> ring
  have hW : (weilFullFunctional (lam + mu) k).re =
      (weilFullFunctional lam k).re - (weightedPrimePart mu k).re := by
    rw [weilFullFunctional_eq_sub_weightedPrimePart (lam + mu),
      weilFullFunctional_eq_sub_weightedPrimePart lam, hadd]
    simp only [Complex.sub_re, Complex.add_re]
    ring
  rw [hW]
  have h1 := h f hf hfs
  have h2 := abs_re_weightedPrimePart_le hf hfs mu
  have h3 := le_abs_self (weightedPrimePart mu k).re
  linarith

/-- The edge-law certificate from the archimedean–polar form: if `H ≥ E_c(λ)𝒥` on real tests in
`[−c, c]`, then `λ ∈ 𝒜(c)`. -/
theorem mem_calibration_of_edgeLaw {c : ℝ} {lam : ℕ → ℝ}
    (h : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c →
      edgeLawConstant c lam * levyEnergy f ≤
        (weilFullFunctional (fun _ => 0) (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re) :
    lam ∈ calibration c := by
  have h' := add_mem_calibration_of_edgeLaw (lam := fun _ => 0) (mu := lam) h
  have e : (fun _ : ℕ => (0 : ℝ)) + lam = lam := by funext n; simp
  rwa [e] at h'

/-! ### The size-only certificate and where it dies -/

theorem weilTest_vanish_far {f : ℝ → ℝ} {c : ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c) :
    ∀ n : ℕ, ⌊Real.exp (2 * c)⌋₊ + 1 ≤ n →
      EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (Real.log n) = 0 ∧
        EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-Real.log n) = 0 := by
  obtain ⟨-, -, hsupp, -⟩ := weilTest_self_data (Complex.ofRealCLM.contDiff.comp hf) hfs
  intro n hn
  have hn' : Real.exp (2 * c) < n := by
    have := Nat.lt_floor_add_one (Real.exp (2 * c))
    have h2 : ((⌊Real.exp (2 * c)⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hn'
  have hlog : 2 * c < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hn'
  exact ⟨image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).2; linarith,
    image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).1; linarith⟩

/-- The prime sum of a real test in `[−c, c]` is the weighted prime part at `Λ`. -/
theorem primeSum_eq_re_weightedPrimePart {f : ℝ → ℝ} {c : ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c) :
    primeSum f = (weightedPrimePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  have hN := weilTest_vanish_far hf hfs
  have hk : ∀ y, EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) y =
      ((∫ s, f s * f (s - y) : ℝ) : ℂ) := weilTest_ofReal_ofReal_eq f f
  rw [weightedPrimePart_affine hN, Complex.re_sum]
  unfold primeSum
  rw [tsum_eq_sum (s := Finset.range (⌊Real.exp (2 * c)⌋₊ + 1)) fun n hn => ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [hk, hk]
    simp only [sub_neg_eq_add, vonMangoldtAtom]
    rw [← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]
  · have h := hN n (by simpa using hn)
    rw [hk, hk, Complex.ofReal_eq_zero, Complex.ofReal_eq_zero] at h
    simp only [sub_neg_eq_add] at h
    rw [h.1, h.2, add_zero, mul_zero]

/-- **The archimedean–polar form of a real window test**:
`H(f) = 2θ′(0)‖f‖² + 𝒥(f) + 2C(f)² − 2S(f)²`. -/
theorem re_archPolar_eq {f : ℝ → ℝ} {c : ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c) :
    (weilFullFunctional (fun _ => 0) (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      2 * gammaHardyPhaseRate 0 * (∫ u, f u ^ 2) + levyEnergy f +
        (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) := by
  have hfc : HasCompactSupport f := HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c))
    fun u hu => vanish_of_tsupport hfs u hu
  have hW := SpacingScaleHarmonicAnalysis.weilQuad_eq hf hfc
  have hsplit := congrArg Complex.re (weilFullFunctional_eq_sub_weightedPrimePart
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))))
  rw [Complex.sub_re, ← primeSum_eq_re_weightedPrimePart hf hfs] at hsplit
  have hQ : SpacingScaleHarmonicAnalysis.weilQuad f =
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := rfl
  linarith

/-- **The size-only certificate dies at edge-law constant one.** If `E_c(λ) ≥ 1`, the odd pair of
bumps at `±c/2` of radius `c/2` has `H(f) < E_c(λ)𝒥(f)`: since `θ′(0) < 0` and the cosh moment of an
odd test vanishes, `H ≤ 2θ′(0)‖f‖² + 𝒥 < 𝒥` on odd tests. Past this point the primes cannot be paid by
the Lévy energy alone. -/
theorem not_edgeLaw_of_one_le {c : ℝ} (hc : 0 < c) {lam : ℕ → ℝ}
    (hE : 1 ≤ edgeLawConstant c lam) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c ∧
      (weilFullFunctional (fun _ => 0) (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re <
        edgeLawConstant c lam * levyEnergy f := by
  have hr : 0 < c / 2 := by positivity
  have hF := contDiff_twoSiteTestAt c hr (-1)
  have hFs : tsupport (fun u => (twoSiteTestAt c (c / 2) hr (-1) u : ℂ)) ⊆ Icc (-c) c :=
    tsupport_twoSiteTestAt_subset hc.le hr (-1) (by linarith)
  refine ⟨_, hF, hFs, ?_⟩
  rw [re_archPolar_eq hF hFs]
  have hodd : ∀ x, twoSiteTestAt c (c / 2) hr (-1) (-x) = -twoSiteTestAt c (c / 2) hr (-1) x := by
    intro x
    simp only [twoSiteTestAt]
    rw [show -x - c / 2 = -(x + c / 2) by ring, show -x + c / 2 = -(x - c / 2) by ring,
      ContDiffBump.neg, ContDiffBump.neg]
    ring
  rw [coshHalfMoment_eq_zero_of_odd hodd]
  have hmass : 0 < ∫ u, twoSiteTestAt c (c / 2) hr (-1) u ^ 2 := by
    have hc' : Continuous fun u => twoSiteTestAt c (c / 2) hr (-1) u ^ 2 := hF.continuous.pow 2
    have hcs : HasCompactSupport fun u => twoSiteTestAt c (c / 2) hr (-1) u ^ 2 :=
      (hasCompactSupport_twoSiteTestAt c hr (-1)).comp_left (g := fun z : ℝ => z ^ 2) (by norm_num)
    refine hc'.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun _ => sq_nonneg _)
      (x := c / 2) ?_
    have h0 : 0 < siteBump (c / 2) hr 0 :=
      (siteBump (c / 2) hr).pos_of_mem_ball (Metric.mem_ball_self hr)
    have h1 : siteBump (c / 2) hr (c / 2 + c / 2) = 0 :=
      siteBump_eq_zero hr (by rw [abs_of_pos (by linarith)]; linarith)
    show twoSiteTestAt c (c / 2) hr (-1) (c / 2) ^ 2 ≠ 0
    refine pow_ne_zero 2 ?_
    rw [twoSiteTestAt, sub_self, h1, mul_zero, add_zero]
    exact h0.ne'
  have hθ := mul_neg_of_neg_of_pos gammaHardyPhaseRate_zero_neg hmass
  have hJ := SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' (twoSiteTestAt c (c / 2) hr (-1))
  have h2 := le_mul_of_one_le_left hJ hE
  have h3 := sq_nonneg (sinhHalfMoment (twoSiteTestAt c (c / 2) hr (-1)))
  have e0 : (2 : ℝ) * (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [e0]
  linarith

theorem edgeCost_nonneg (c : ℝ) (lam : ℕ → ℝ) (n : ℕ) : 0 ≤ edgeCost c lam n := by
  unfold edgeCost
  split_ifs with h
  · have hδ : 0 < 2 * c - Real.log n := by linarith [h.2]
    exact div_nonneg (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (levyTail_pos hδ).le)
  · exact le_rfl

/-- The Lévy tail is exponentially small: `Ω(L) ≤ 14/65` for `L ≥ 8`. -/
theorem levyTail_le_of_eight_le {L : ℝ} (hL : 8 ≤ L) :
    ∫ x in Ioi L, archLevyDensity x ≤ 14 / 65 := by
  have hL0 : 0 < L := by linarith
  have hΩ := SignedWindowCriticality.PrimeThreeEntry.levyTail_le_exp hL0
  have h4 : Real.exp (-(1 / 2) * L) ≤ Real.exp (-4) := Real.exp_le_exp.mpr (by linarith)
  have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num)
  have he4 : Real.exp (-4) ≤ 1 / 13 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 4) (by norm_num)]
    linarith
  have h5 : Real.exp (-(5 / 2) * L) ≤ Real.exp (-(1 / 2) * L) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-2 * L) ≤ 1 / 2 := by
    have : Real.exp (-2 * L) ≤ Real.exp (-4) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hd : 1 / 2 ≤ 1 - Real.exp (-2 * L) := by linarith
  have hfrac : (2 / 5) * Real.exp (-(5 / 2) * L) / (1 - Real.exp (-2 * L)) ≤
      (4 / 5) * Real.exp (-(1 / 2) * L) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (Real.exp_pos (-(1 / 2) * L)).le (sub_nonneg.mpr hd)]
  linarith

/-- **For `ζ` the size-only certificate dies at a finite window**: for `2c ≥ log 2 + 8` the edge
cost of the prime `2` alone is at least one, `E_c(Λ) ≥ 1`. -/
theorem one_le_edgeLawConstant_vonMangoldt {c : ℝ} (hc : Real.log 2 + 8 ≤ 2 * c) :
    1 ≤ edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2mem : 2 ∈ Finset.range (⌊Real.exp (2 * c)⌋₊ + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    refine Nat.le_floor ?_
    have : Real.exp (Real.log 2) ≤ Real.exp (2 * c) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_log (by norm_num)] at this
    exact_mod_cast this
  refine le_trans ?_ (Finset.single_le_sum (fun n _ => edgeCost_nonneg c _ n) h2mem)
  have hact : 2 ≤ 2 ∧ Real.log ((2 : ℕ) : ℝ) < 2 * c := ⟨le_rfl, by push_cast; linarith⟩
  unfold edgeCost
  rw [if_pos hact]
  beta_reduce
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  push_cast
  have hΩ := levyTail_le_of_eight_le (L := 2 * c - Real.log 2) (by linarith)
  have hΩpos := levyTail_pos (show 0 < 2 * c - Real.log 2 by linarith)
  have hsq : Real.sqrt 2 ≤ 3 / 2 := by
    have h := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 / 2) ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h
  rw [abs_of_pos hl2, le_div_iff₀ (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hΩpos), one_mul]
  have := Real.log_two_gt_d9
  nlinarith [mul_nonneg (sub_nonneg.mpr hsq) hΩpos.le,
    mul_nonneg (Real.sqrt_nonneg 2) (sub_nonneg.mpr hΩ)]

/-- On every window with `2c ≥ log 2 + 8` the archimedean–polar form does not dominate
`E_c(Λ)𝒥`: `ζ`'s primes cannot be paid there by the Lévy energy alone. -/
theorem edgeLaw_fails_for_vonMangoldt {c : ℝ} (hc : Real.log 2 + 8 ≤ 2 * c) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c ∧
      (weilFullFunctional (fun _ => 0) (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re <
        edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) * levyEnergy f :=
  not_edgeLaw_of_one_le (by linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)])
    (one_le_edgeLawConstant_vonMangoldt hc)

end GaloisForLFunctions.FrustratedArithmeticDirichletForms
