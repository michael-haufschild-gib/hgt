import GaloisForLFunctions.SignedWindowCriticality.OnReflectionPairsTheCouplingIsTheSmoothedPrimeCount
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover

/-!
# The window edge carries the newest prime

Let `f` vanish on `(−∞, −c)`, the outer edge of a half-window `[−c, 0]`, and let `ℓ > 0` be a lag.
The reflection term `(f⋆f)(−ℓ) = ∫ f(u) f(−ℓ − u) du` of the half-window band sees `f` only on the
**collar sliver** `I = [−c, c − ℓ]`, of width `δ = 2c − ℓ`, which the reflection `ρ(u) = −ℓ − u`
maps onto itself.

* **Signature law** (`selfConv_neg_eq_sliver_signature`, `abs_selfConv_neg_le_sliverMass`):
  `(f⋆f)(−ℓ) = ∫_I (f₊² − f₋²)` with `f± = (f ± f∘ρ)/2`, so the lag couples the sliver through
  the signature of `ρ`: it helps on `ρ`-symmetric profiles and costs on antisymmetric ones, and
  `|(f⋆f)(−ℓ)| ≤ ∫_I f²`.
* **Outward jumps** (`levyTail_mul_edgeMass_le_levyEnergy`): a jump of length `x > δ` from the
  sliver to the left leaves the support, so `Ω(δ) ∫_I f² ≤ levyEnergy f` with the Lévy tail
  `Ω(δ) = ∫_δ^∞ ω ≥ 2e^{−δ/2}` (`two_mul_exp_le_levyTail`).

Together (`vonMangoldtAtom_mul_abs_selfConv_le`): for every `n`,
`w_n |(f⋆f)(−log n)| ≤ (Λ(n) e^c/(2n)) · levyEnergy f`, `w_n = Λ(n)/√n`. Within half-width `h` of
its entry (`2c ≤ log n + 2h`) the factor is at most `w_n e^h/2 ≤ e^{h−1}`
(`vonMangoldtAtom_mul_abs_selfConv_le_of_entry`): the outward jumps of the sliver carry the newest
prime power at ratio `w_n e^h/2`, while the jumps inside the collar carry it only at ratio
`2w_n e^h`, which exceeds `1` for the primes `3 ≤ p ≤ 73` (`TheCollarRatioIsSharp`). Below `log 4`
the primes `2` and `3` together use at most `log 2/2 + log 3/3 < 3/4` of the Lévy energy
(`twoThree_kicks_le_levyEnergy`).
-/

open MeasureTheory Set Filter
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry

open GaloisForLFunctions.SignedWindowCriticality
open _root_.RHTower

variable {f : ℝ → ℝ} {c ℓ : ℝ}

/-! ### The collar sliver and the signature law -/

/-- The collar sliver `[−c, c − ℓ]`: the points of `[−c, ∞)` whose `ℓ`-reflection `−ℓ − u` stays
in `[−c, ∞)`. -/
def sliver (c ℓ : ℝ) : Set ℝ := Icc (-c) (c - ℓ)

theorem measurableSet_sliver : MeasurableSet (sliver c ℓ) := measurableSet_Icc

/-- The reflection `u ↦ −ℓ − u` maps the sliver onto itself. -/
theorem neg_sub_mem_sliver {u : ℝ} (hu : u ∈ sliver c ℓ) : -ℓ - u ∈ sliver c ℓ :=
  ⟨by linarith [hu.2], by linarith [hu.1]⟩

/-- Off the sliver, `f(u) f(−ℓ − u) = 0` for `f` vanishing left of `−c`. -/
theorem mul_reflect_eq_zero_of_notMem (hfL : ∀ u, u < -c → f u = 0) {u : ℝ}
    (hu : u ∉ sliver c ℓ) : f u * f (-ℓ - u) = 0 := by
  simp only [sliver, mem_Icc, not_and_or, not_le] at hu
  rcases hu with h | h
  · rw [hfL u h, zero_mul]
  · rw [hfL (-ℓ - u) (by linarith), mul_zero]

/-- The reflection term lives on the sliver. -/
theorem selfConv_neg_eq_setIntegral_sliver (hfL : ∀ u, u < -c → f u = 0) :
    selfConv f (-ℓ) = ∫ u in sliver c ℓ, f u * f (-ℓ - u) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hu =>
    mul_reflect_eq_zero_of_notMem hfL hu).symm

/-- **Signature law.** The reflection term is the signature of the sliver reflection:
`(f⋆f)(−ℓ) = ∫_I (((f + f∘ρ)/2)² − ((f − f∘ρ)/2)²)`. -/
theorem selfConv_neg_eq_sliver_signature (hfL : ∀ u, u < -c → f u = 0) :
    selfConv f (-ℓ) = ∫ u in sliver c ℓ,
      (((f u + f (-ℓ - u)) / 2) ^ 2 - ((f u - f (-ℓ - u)) / 2) ^ 2) := by
  rw [selfConv_neg_eq_setIntegral_sliver hfL]
  exact setIntegral_congr_fun measurableSet_sliver fun u _ => by ring

/-- **The reflection term is bounded by the sliver mass**: `|(f⋆f)(−ℓ)| ≤ ∫_I f²`. -/
theorem abs_selfConv_neg_le_sliverMass (hf : Continuous f) (hfL : ∀ u, u < -c → f u = 0) :
    |selfConv f (-ℓ)| ≤ ∫ u in sliver c ℓ, f u ^ 2 := by
  let g : ℝ → ℝ := (sliver c ℓ).indicator fun v => f v ^ 2
  have hg0 : ∀ v, 0 ≤ g v := fun v => indicator_nonneg (fun w _ => sq_nonneg (f w)) v
  have hgi : Integrable g :=
    ((hf.pow 2).integrableOn_Icc).integrable_indicator measurableSet_sliver
  have hgr : Integrable fun u => g (-ℓ - u) := hgi.comp_sub_left (-ℓ)
  have hpt : ∀ u, |f u * f (-ℓ - u)| ≤ (g u + g (-ℓ - u)) / 2 := by
    intro u
    by_cases hu : u ∈ sliver c ℓ
    · have e1 : g u = f u ^ 2 := indicator_of_mem hu _
      have e2 : g (-ℓ - u) = f (-ℓ - u) ^ 2 := indicator_of_mem (neg_sub_mem_sliver hu) _
      rw [e1, e2, abs_mul]
      nlinarith [sq_nonneg (|f u| - |f (-ℓ - u)|), sq_abs (f u), sq_abs (f (-ℓ - u))]
    · rw [mul_reflect_eq_zero_of_notMem hfL hu, abs_zero]
      linarith [hg0 u, hg0 (-ℓ - u)]
  have hrefl : (∫ u, g (-ℓ - u)) = ∫ u, g u := integral_sub_left_eq_self g volume (-ℓ)
  have hmass : (∫ u, g u) = ∫ u in sliver c ℓ, f u ^ 2 := integral_indicator measurableSet_sliver
  calc |selfConv f (-ℓ)| = |∫ u, f u * f (-ℓ - u)| := rfl
    _ ≤ ∫ u, |f u * f (-ℓ - u)| := abs_integral_le_integral_abs
    _ ≤ ∫ u, (g u + g (-ℓ - u)) / 2 :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          ((hgi.add hgr).div_const 2) (Eventually.of_forall hpt)
    _ = ∫ u in sliver c ℓ, f u ^ 2 := by
        rw [integral_div, integral_add hgi hgr, hrefl, hmass]; ring

/-- If the lag is at least the window length, `2c ≤ ℓ`, the reflection term vanishes. -/
theorem selfConv_neg_eq_zero_of_le (hf : Continuous f) (hfL : ∀ u, u < -c → f u = 0)
    (hℓ : 2 * c ≤ ℓ) : selfConv f (-ℓ) = 0 := by
  have h := abs_selfConv_neg_le_sliverMass (ℓ := ℓ) hf hfL
  have hz : (∫ u in sliver c ℓ, f u ^ 2) = 0 := by
    refine setIntegral_measure_zero _ ?_
    rw [sliver, Real.volume_Icc, ENNReal.ofReal_eq_zero]
    linarith
  rw [hz] at h
  exact abs_nonpos_iff.mp h

/-! ### Outward jumps of the sliver -/

/-- `e^{−x/2} ≤ ω(x)` on `(0, ∞)`. -/
theorem exp_neg_half_le_archLevyDensity {x : ℝ} (hx : 0 < x) :
    Real.exp (-x / 2) ≤ archLevyDensity x := by
  unfold archLevyDensity
  have h1 : 0 < 1 - Real.exp (-2 * x) := by
    have : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [le_div_iff₀ h1]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (by linarith [Real.exp_pos (-2 * x)])

/-- The Lévy tail `Ω(δ) = ∫_δ^∞ ω` is at least `2e^{−δ/2}`. -/
theorem two_mul_exp_le_levyTail {δ : ℝ} (hδ : 0 < δ) :
    2 * Real.exp (-δ / 2) ≤ ∫ x in Ioi δ, archLevyDensity x := by
  have hexp : (∫ x in Ioi δ, Real.exp (-(1 / 2) * x)) = 2 * Real.exp (-δ / 2) := by
    rw [integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) δ]
    rw [show -(1 / 2 : ℝ) * δ = -δ / 2 by ring]
    ring
  rw [← hexp]
  refine setIntegral_mono_on (exp_neg_integrableOn_Ioi δ (by norm_num : (0 : ℝ) < 1 / 2))
    (WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hδ) measurableSet_Ioi fun x hx => ?_
  have h := exp_neg_half_le_archLevyDensity (lt_trans hδ hx)
  rwa [show -(1 / 2 : ℝ) * x = -x / 2 by ring]

/-- **Outward jumps carry the edge mass.** If `f` vanishes on `(−∞, −c)`, every jump of length
`x > δ` from `[−c, −c + δ]` to the left leaves the support, so
`Ω(δ) · ∫_{[−c, −c+δ]} f² ≤ levyEnergy f`. -/
theorem levyTail_mul_edgeMass_le_levyEnergy (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfL : ∀ u, u < -c → f u = 0) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in Ioi δ, archLevyDensity x) * (∫ y in Icc (-c) (-c + δ), f y ^ 2) ≤ levyEnergy f := by
  set m := ∫ y in Icc (-c) (-c + δ), f y ^ 2 with hm
  have hF := integrableOn_levyIntegrand hf hfc
  -- for `x > δ` the jump energy at length `x` contains the whole edge mass
  have hinner : ∀ x, δ < x → m ≤ ∫ u, (f u - f (u + x)) ^ 2 := by
    intro x hx
    let g : ℝ → ℝ := (Icc (-c) (-c + δ)).indicator fun v => f v ^ 2
    have hgi : Integrable g :=
      ((hf.continuous.pow 2).integrableOn_Icc).integrable_indicator measurableSet_Icc
    have hshift : (∫ u, g (u + x)) = m := by
      rw [integral_add_right_eq_self g x]
      exact integral_indicator measurableSet_Icc
    have hsq : Integrable fun u => (f u - f (u + x)) ^ 2 :=
      (SpacingScaleHarmonicAnalysis.integrable_sub_shift_mul hf.continuous hfc hf.continuous
        x).congr (Eventually.of_forall fun u => (sq _).symm)
    rw [← hshift]
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun u => indicator_nonneg (fun w _ => sq_nonneg (f w)) _) hsq
      (Eventually.of_forall fun u => ?_)
    show g (u + x) ≤ (f u - f (u + x)) ^ 2
    by_cases hu : u + x ∈ Icc (-c) (-c + δ)
    · have e : g (u + x) = f (u + x) ^ 2 := indicator_of_mem hu _
      rw [e, hfL u (by linarith [hu.2]), zero_sub, neg_sq]
    · have e : g (u + x) = 0 := indicator_of_notMem hu _
      rw [e]
      exact sq_nonneg _
  have hsub : (∫ x in Ioi δ, archLevyDensity x * ∫ u, (f u - f (u + x)) ^ 2) ≤ levyEnergy f := by
    unfold levyEnergy
    refine setIntegral_mono_set hF ?_ (Eventually.of_forall fun x hx => ?_)
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
        mul_nonneg (archLevyDensity_pos hx).le (integral_nonneg fun u => sq_nonneg _)
    · exact (lt_trans hδ hx : (0 : ℝ) < x)
  have hlow : (∫ x in Ioi δ, archLevyDensity x) * m ≤
      ∫ x in Ioi δ, archLevyDensity x * ∫ u, (f u - f (u + x)) ^ 2 := by
    rw [← integral_mul_const]
    refine setIntegral_mono_on
      ((WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hδ).mul_const m)
      (hF.mono_set fun x hx => (lt_trans hδ hx : (0 : ℝ) < x)) measurableSet_Ioi fun x hx => ?_
    exact mul_le_mul_of_nonneg_left (hinner x hx) (archLevyDensity_pos (lt_trans hδ hx)).le
  linarith

/-! ### The outward jumps carry every prime lag -/

/-- **The window edge carries the reflection term.** For `f` vanishing on `(−∞, −c)` and a lag
`ℓ < 2c`, `|(f⋆f)(−ℓ)| · Ω(2c − ℓ) ≤ levyEnergy f`. -/
theorem abs_selfConv_neg_mul_levyTail_le (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfL : ∀ u, u < -c → f u = 0) (hℓ : ℓ < 2 * c) :
    |selfConv f (-ℓ)| * (∫ x in Ioi (2 * c - ℓ), archLevyDensity x) ≤ levyEnergy f := by
  have hδ : 0 < 2 * c - ℓ := by linarith
  have h1 := abs_selfConv_neg_le_sliverMass (ℓ := ℓ) hf.continuous hfL
  have h2 := levyTail_mul_edgeMass_le_levyEnergy hf hfc hfL hδ
  have hsl : sliver c ℓ = Icc (-c) (-c + (2 * c - ℓ)) := by
    rw [sliver, show -c + (2 * c - ℓ) = c - ℓ by ring]
  rw [hsl] at h1
  have hΩ : 0 ≤ ∫ x in Ioi (2 * c - ℓ), archLevyDensity x :=
    setIntegral_nonneg measurableSet_Ioi fun x hx => (archLevyDensity_pos (lt_trans hδ hx)).le
  calc |selfConv f (-ℓ)| * (∫ x in Ioi (2 * c - ℓ), archLevyDensity x)
      ≤ (∫ y in Icc (-c) (-c + (2 * c - ℓ)), f y ^ 2) *
          (∫ x in Ioi (2 * c - ℓ), archLevyDensity x) := mul_le_mul_of_nonneg_right h1 hΩ
    _ ≤ levyEnergy f := by rw [mul_comm]; exact h2

/-- Explicit form: `|(f⋆f)(−ℓ)| ≤ (e^{(2c−ℓ)/2}/2) · levyEnergy f` for every lag `ℓ`. -/
theorem abs_selfConv_neg_le_levyEnergy (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfL : ∀ u, u < -c → f u = 0) :
    |selfConv f (-ℓ)| ≤ Real.exp ((2 * c - ℓ) / 2) / 2 * levyEnergy f := by
  have hL := SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' f
  rcases le_or_gt (2 * c) ℓ with hle | hlt
  · rw [selfConv_neg_eq_zero_of_le hf.continuous hfL hle, abs_zero]
    positivity
  have hδ : 0 < 2 * c - ℓ := by linarith
  have h' : |selfConv f (-ℓ)| * (2 * Real.exp (-(2 * c - ℓ) / 2)) ≤ levyEnergy f :=
    le_trans (mul_le_mul_of_nonneg_left (two_mul_exp_le_levyTail hδ) (abs_nonneg _))
      (abs_selfConv_neg_mul_levyTail_le hf hfc hfL hlt)
  have hone : 2 * Real.exp (-(2 * c - ℓ) / 2) * (Real.exp ((2 * c - ℓ) / 2) / 2) = 1 := by
    rw [show 2 * Real.exp (-(2 * c - ℓ) / 2) * (Real.exp ((2 * c - ℓ) / 2) / 2) =
        Real.exp (-(2 * c - ℓ) / 2 + (2 * c - ℓ) / 2) by rw [Real.exp_add]; ring,
      show -(2 * c - ℓ) / 2 + (2 * c - ℓ) / 2 = 0 by ring, Real.exp_zero]
  calc |selfConv f (-ℓ)|
      = |selfConv f (-ℓ)| * (2 * Real.exp (-(2 * c - ℓ) / 2)) *
          (Real.exp ((2 * c - ℓ) / 2) / 2) := by rw [mul_assoc, hone, mul_one]
    _ ≤ levyEnergy f * (Real.exp ((2 * c - ℓ) / 2) / 2) :=
        mul_le_mul_of_nonneg_right h' (by positivity)
    _ = Real.exp ((2 * c - ℓ) / 2) / 2 * levyEnergy f := by ring

/-- `e^{(2c − log n)/2} = e^c/√n` for `n ≥ 1`. -/
theorem exp_half_sub_log_eq {n : ℕ} (hn : 1 ≤ n) :
    Real.exp ((2 * c - Real.log n) / 2) = Real.exp c / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show (2 * c - Real.log n) / 2 = c - Real.log (Real.sqrt n) by
      rw [Real.log_sqrt hn0.le]; ring,
    Real.exp_sub, Real.exp_log (Real.sqrt_pos.mpr hn0)]

/-- **Every prime power is carried by the window edge.** For `f` vanishing on `(−∞, −c)`,
`w_n |(f⋆f)(−log n)| ≤ (w_n e^{(2c − log n)/2}/2) · levyEnergy f`. -/
theorem vonMangoldtAtom_mul_abs_selfConv_le' (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfL : ∀ u, u < -c → f u = 0) (n : ℕ) :
    vonMangoldtAtom n * |selfConv f (-Real.log n)| ≤
      vonMangoldtAtom n * Real.exp ((2 * c - Real.log n) / 2) / 2 * levyEnergy f := by
  have h := abs_selfConv_neg_le_levyEnergy (ℓ := Real.log n) hf hfc hfL
  have hw := vonMangoldtAtom_nonneg' n
  calc vonMangoldtAtom n * |selfConv f (-Real.log n)|
      ≤ vonMangoldtAtom n * (Real.exp ((2 * c - Real.log n) / 2) / 2 * levyEnergy f) :=
        mul_le_mul_of_nonneg_left h hw
    _ = _ := by ring

/-- **The edge coefficient of a prime power** is `Λ(n) e^c / (2n)`:
`w_n |(f⋆f)(−log n)| ≤ (Λ(n) e^c/(2n)) · levyEnergy f`. -/
theorem vonMangoldtAtom_mul_abs_selfConv_le (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfL : ∀ u, u < -c → f u = 0) (n : ℕ) :
    vonMangoldtAtom n * |selfConv f (-Real.log n)| ≤
      (ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp c / (2 * n) * levyEnergy f := by
  have h := vonMangoldtAtom_mul_abs_selfConv_le' hf hfc hfL n
  by_cases hn : 2 ≤ n
  · have hn1 : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hcoef : vonMangoldtAtom n * Real.exp ((2 * c - Real.log n) / 2) / 2 =
        (ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp c / (2 * n) := by
      rw [exp_half_sub_log_eq hn1]
      unfold vonMangoldtAtom
      rw [if_pos hn]
      have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      calc (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n * (Real.exp c / Real.sqrt n) / 2
          = (ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp c /
              (2 * (Real.sqrt n * Real.sqrt n)) := by ring
        _ = _ := by rw [hs]
    rwa [hcoef] at h
  · have h0 : vonMangoldtAtom n = 0 := by unfold vonMangoldtAtom; rw [if_neg hn]
    rw [h0, zero_mul]
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have := SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' f
    positivity

/-- `w_n = Λ(n)/√n ≤ 2/e` for every `n`. -/
theorem vonMangoldtAtom_le_two_div_exp_one (n : ℕ) : vonMangoldtAtom n ≤ 2 / Real.exp 1 := by
  unfold vonMangoldtAtom
  split_ifs with hn
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
      ArithmeticFunction.vonMangoldt_le_log
    -- `log n = 2 log √n ≤ 2 √n / e` from `log y ≤ y/e`
    have hlog : Real.log n ≤ 2 * Real.sqrt n / Real.exp 1 := by
      have hy : Real.log (Real.sqrt n / Real.exp 1) ≤ Real.sqrt n / Real.exp 1 - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hs (Real.exp_pos 1))
      rw [Real.log_div hs.ne' (Real.exp_pos 1).ne', Real.log_exp, Real.log_sqrt hn0.le] at hy
      rw [show 2 * Real.sqrt n / Real.exp 1 = 2 * (Real.sqrt n / Real.exp 1) by ring]
      linarith
    rw [div_le_div_iff₀ hs (Real.exp_pos 1)]
    have := mul_le_mul_of_nonneg_right (hΛ.trans hlog) (Real.exp_pos 1).le
    rw [div_mul_cancel₀ _ (Real.exp_pos 1).ne'] at this
    nlinarith [Real.mul_self_sqrt hn0.le]
  · positivity

/-- **The newest prime power at its entry.** Within half-width `h` of its entry
(`2c ≤ log n + 2h`), the outward jumps carry the lag `log n` at ratio `w_n e^h/2 ≤ e^{h−1}`:
`w_n |(f⋆f)(−log n)| ≤ (w_n e^h/2) · levyEnergy f ≤ e^{h−1} · levyEnergy f`. -/
theorem vonMangoldtAtom_mul_abs_selfConv_le_of_entry (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hfL : ∀ u, u < -c → f u = 0) {n : ℕ} {h : ℝ}
    (hnc : 2 * c ≤ Real.log n + 2 * h) :
    vonMangoldtAtom n * |selfConv f (-Real.log n)| ≤
        vonMangoldtAtom n * Real.exp h / 2 * levyEnergy f ∧
      vonMangoldtAtom n * Real.exp h / 2 * levyEnergy f ≤ Real.exp (h - 1) * levyEnergy f := by
  have hL := SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' f
  have hw := vonMangoldtAtom_nonneg' n
  refine ⟨(vonMangoldtAtom_mul_abs_selfConv_le' hf hfc hfL n).trans ?_, ?_⟩
  · have hexp : Real.exp ((2 * c - Real.log n) / 2) ≤ Real.exp h :=
      Real.exp_le_exp.mpr (by linarith)
    have := mul_le_mul_of_nonneg_left hexp hw
    have h2 : vonMangoldtAtom n * Real.exp ((2 * c - Real.log n) / 2) / 2 ≤
        vonMangoldtAtom n * Real.exp h / 2 := by linarith
    exact mul_le_mul_of_nonneg_right h2 hL
  · refine mul_le_mul_of_nonneg_right ?_ hL
    have hb := vonMangoldtAtom_le_two_div_exp_one n
    have he : Real.exp (h - 1) = Real.exp h / Real.exp 1 := Real.exp_sub h 1
    rw [he]
    have hpos := Real.exp_pos h
    have h1 := Real.exp_pos 1
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) h1]
    have := mul_le_mul_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ Real.exp h * Real.exp 1)
    rw [show 2 / Real.exp 1 * (Real.exp h * Real.exp 1) = 2 * Real.exp h by field_simp] at this
    nlinarith

/-- **Below `log 4` both primes together use less than three quarters of the Lévy energy.** For
`f` vanishing on `(−∞, −c)` with `c ≤ log 2`,
`w₂|(f⋆f)(−log 2)| + w₃|(f⋆f)(−log 3)| ≤ (log 2/2 + log 3/3) · levyEnergy f`. -/
theorem twoThree_kicks_le_levyEnergy (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfL : ∀ u, u < -c → f u = 0) (hc : c ≤ Real.log 2) :
    vonMangoldtAtom 2 * |selfConv f (-Real.log 2)| +
        vonMangoldtAtom 3 * |selfConv f (-Real.log 3)| ≤
      (Real.log 2 / 2 + Real.log 3 / 3) * levyEnergy f := by
  have hL := SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' f
  have h2 := vonMangoldtAtom_mul_abs_selfConv_le hf hfc hfL 2
  have h3 := vonMangoldtAtom_mul_abs_selfConv_le hf hfc hfL 3
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at h2
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three] at h3
  have hec : Real.exp c ≤ 2 := by
    calc Real.exp c ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hc
      _ = 2 := Real.exp_log (by norm_num)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have c2 : Real.log ((2 : ℕ) : ℝ) * Real.exp c / (2 * ((2 : ℕ) : ℝ)) ≤ Real.log 2 / 2 := by
    push_cast
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  have c3 : Real.log ((3 : ℕ) : ℝ) * Real.exp c / (2 * ((3 : ℕ) : ℝ)) ≤ Real.log 3 / 3 := by
    push_cast
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  push_cast at h2 h3 c2 c3
  nlinarith [mul_le_mul_of_nonneg_right c2 hL, mul_le_mul_of_nonneg_right c3 hL]

/-! ### The newest prime enters softly -/

/-- `e^{−x/2}/(2x) ≤ ω(x)` on `(0, ∞)`, from `1 − e^{−2x} ≤ 2x`. -/
theorem exp_neg_half_div_le_archLevyDensity {x : ℝ} (hx : 0 < x) :
    Real.exp (-x / 2) / (2 * x) ≤ archLevyDensity x := by
  unfold archLevyDensity
  have h1 : 1 - Real.exp (-2 * x) ≤ 2 * x := by linarith [Real.add_one_le_exp (-2 * x)]
  have h2 : 0 < 1 - Real.exp (-2 * x) := by
    have : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le h2 h1

/-- **Logarithmic Lévy tail**: `(e^{−1/2}/2) log(1/δ) ≤ Ω(δ)` for `0 < δ ≤ 1`. -/
theorem levyTail_ge_log {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.exp (-1 / 2) / 2 * Real.log (1 / δ) ≤ ∫ x in Ioi δ, archLevyDensity x := by
  have hint : IntegrableOn archLevyDensity (Ioi δ) :=
    WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hδ
  have hsub : (∫ x in Ioc δ 1, archLevyDensity x) ≤ ∫ x in Ioi δ, archLevyDensity x :=
    setIntegral_mono_set hint
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
        (archLevyDensity_pos (lt_trans hδ hx)).le)
      (Eventually.of_forall fun x hx => hx.1)
  have hlow : Real.exp (-1 / 2) / 2 * Real.log (1 / δ) ≤ ∫ x in Ioc δ 1, archLevyDensity x := by
    rw [← intervalIntegral.integral_of_le hδ1, ← integral_inv_of_pos hδ one_pos,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hδ1 ?_ ?_ fun x hx => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.mul (continuousOn_inv₀.mono fun x hx => ?_)
      rw [uIcc_of_le hδ1] at hx
      exact (lt_of_lt_of_le hδ hx.1).ne'
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ1).mpr
        (hint.mono_set Ioc_subset_Ioi_self)
    · have hx0 : 0 < x := lt_of_lt_of_le hδ hx.1
      have h2 : Real.exp (-1 / 2) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith [hx.2])
      calc Real.exp (-1 / 2) / 2 * x⁻¹ = Real.exp (-1 / 2) / (2 * x) := by field_simp
        _ ≤ Real.exp (-x / 2) / (2 * x) := div_le_div_of_nonneg_right h2 (by positivity)
        _ ≤ archLevyDensity x := exp_neg_half_div_le_archLevyDensity hx0
  linarith

/-- **The newest prime enters softly.** For a lag `ℓ` whose sliver width `δ = 2c − ℓ` lies in
`(0, 1]`, `|(f⋆f)(−ℓ)| · (e^{−1/2}/2) log(1/δ) ≤ levyEnergy f`: just after its entry the reflection
term is `O(1/log(1/δ))` of the Lévy energy. -/
theorem abs_selfConv_neg_mul_log_le (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfL : ∀ u, u < -c → f u = 0) (hℓ : ℓ < 2 * c) (hδ1 : 2 * c - ℓ ≤ 1) :
    |selfConv f (-ℓ)| * (Real.exp (-1 / 2) / 2 * Real.log (1 / (2 * c - ℓ))) ≤ levyEnergy f :=
  le_trans (mul_le_mul_of_nonneg_left (levyTail_ge_log (by linarith) hδ1) (abs_nonneg _))
    (abs_selfConv_neg_mul_levyTail_le hf hfc hfL hℓ)

end GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry

end
