import GaloisForLFunctions.EulerFETransportTheory.TheGaussianRoughMeanSurvivesVanishingDamping
import GaloisForLFunctions.EulerFETransportTheory.ThePrimeCurrentPassesAcrossDyadicWindows
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeFluxWindow
import GaloisForLFunctions.RHTower.IntervalMeanSquareTransfer

/-!
# Splitting the continued current into its prime head and rough variance

The small-prime component retains all prime powers. Its absolute admission
allows Gaussian damping to be removed uniformly in height. The rough
component is governed by its complete square mass under a smooth head probe.
-/

open Complex Filter Topology MeasureTheory RHTower XiAtlasFinitePart
open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- The complete von Mangoldt component removed by the rough restriction. -/
def smallPrimeVonMangoldtCoeff (Y : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  (woldVonMangoldtWeightedCoefficient σ n : ℂ) - roughVonMangoldtCoeff Y σ n

theorem smallPrimeVonMangoldtCoeff_zero (Y : ℕ) (σ : ℝ) :
    smallPrimeVonMangoldtCoeff Y σ 0 = 0 := by
  simp [smallPrimeVonMangoldtCoeff, woldVonMangoldtWeightedCoefficient,
    roughVonMangoldtCoeff_zero]

theorem small_add_rough_vonMangoldtCoeff (Y : ℕ) (σ : ℝ) (n : ℕ) :
    smallPrimeVonMangoldtCoeff Y σ n + roughVonMangoldtCoeff Y σ n =
      (woldVonMangoldtWeightedCoefficient σ n : ℂ) := sub_add_cancel _ _

theorem norm_smallPrimeVonMangoldtCoeff_le (Y : ℕ) (σ : ℝ) (n : ℕ) :
    ‖smallPrimeVonMangoldtCoeff Y σ n‖ ≤
      ‖(woldVonMangoldtWeightedCoefficient σ n : ℂ)‖ := by
  unfold smallPrimeVonMangoldtCoeff roughVonMangoldtCoeff woldVonMangoldtWeightedCoefficient
  split_ifs
  · simp only [sub_self, norm_zero]
    exact norm_nonneg _
  · simp only [sub_zero, le_refl]

/-- A prime-power coefficient removed by rough restriction belongs entirely
to the smooth prime head. Mixed smooth–rough integers carry no Mangoldt mass. -/
theorem smallPrimeVonMangoldtCoeff_smooth {Y n : ℕ} {σ : ℝ}
    (hb : smallPrimeVonMangoldtCoeff Y σ n ≠ 0) : n ∈ Nat.smoothNumbers Y := by
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact hb (smallPrimeVonMangoldtCoeff_zero Y σ)
  have hΛ : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    intro h
    apply hb
    simp [smallPrimeVonMangoldtCoeff, roughVonMangoldtCoeff,
      woldVonMangoldtWeightedCoefficient, h]
  have hrough : ¬ ∀ p ∈ Nat.primesBelow Y, ¬ p ∣ n := by
    intro h
    apply hb
    have hh : n ≠ 0 ∧ ∀ p ∈ Nat.primesBelow Y, ¬ p ∣ n := ⟨hn0, h⟩
    rw [smallPrimeVonMangoldtCoeff, roughVonMangoldtCoeff, if_pos hh,
      woldVonMangoldtWeightedCoefficient, sub_self]
  push Not at hrough
  have hpp : IsPrimePow n := by
    by_contra h
    exact hΛ (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h)
  obtain ⟨p, k, hp, _, rfl⟩ := hpp
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  obtain ⟨q, hq, hqn⟩ := hrough
  obtain ⟨hqY, hq⟩ := Nat.mem_primesBelow.mp hq
  have hpY : p < Y := by
    rcases (Nat.dvd_prime hp').mp (hq.dvd_of_dvd_pow hqn) with hq1 | hqp
    · exact False.elim (hq.ne_one hq1)
    · simpa only [hqp] using hqY
  apply Nat.mem_smoothNumbers'.mpr
  intro r hr hrn
  rcases (Nat.dvd_prime hp').mp (hr.dvd_of_dvd_pow hrn) with hr1 | hrp
  · exact False.elim (hr.ne_one hr1)
  · simpa only [hrp] using hpY

/-- All powers of the finitely many small primes are absolutely admitted
at every positive abscissa. -/
theorem summable_norm_smallPrimeVonMangoldtCoeff (Y : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Summable fun n => ‖smallPrimeVonMangoldtCoeff Y σ n‖ := by
  have hb : ∀ n : ℕ, ‖smallPrimeVonMangoldtCoeff Y σ n‖ ≤
      Real.log n * (n : ℝ) ^ (-σ) := by
    intro n
    refine (norm_smallPrimeVonMangoldtCoeff_le Y σ n).trans ?_
    rw [woldVonMangoldtWeightedCoefficient, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))]
    exact mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hs : Summable fun n : Nat.smoothNumbers (Y + 1) =>
      ‖smallPrimeVonMangoldtCoeff Y σ n‖ :=
    (summable_smoothNumbers_log_mul_rpow_neg Y hσ).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun n => hb n)
  apply (Subtype.val_injective.summable_iff (f := fun n => ‖smallPrimeVonMangoldtCoeff Y σ n‖)
    (g := fun n : Nat.smoothNumbers (Y + 1) => (n : ℕ)) ?_).mp hs
  intro n hn
  have hz : smallPrimeVonMangoldtCoeff Y σ n = 0 := by
    by_contra hb
    exact hn ⟨⟨n, Nat.smoothNumbers_mono (Nat.le_succ Y)
      (smallPrimeVonMangoldtCoeff_smooth hb)⟩, rfl⟩
  simp only [hz, norm_zero]

private theorem gaussianCoeff_norm_le {a : ℕ → ℂ} {H : ℝ} (hH : 0 < H) (n : ℕ) :
    ‖gaussianHeightCoeff a H n‖ ≤ ‖a n‖ := by
  rw [norm_gaussianHeightCoeff]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (by positivity) hH.le)))

private theorem norm_gaussianCoeff_sub {a : ℕ → ℂ} {H : ℝ} (hH : 0 < H) (n : ℕ) :
    ‖gaussianHeightCoeff a H n - a n‖ =
      ‖a n‖ * (1 - Real.exp (-((n : ℝ) ^ 2 / H))) := by
  have he : Real.exp (-((n : ℝ) ^ 2 / H)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (by positivity) hH.le))
  have hfactor : gaussianHeightCoeff a H n - a n =
      a n * ((Real.exp (-((n : ℝ) ^ 2 / H)) - 1 : ℝ) : ℂ) := by
    simp only [gaussianHeightCoeff, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr he)]
  ring

private theorem norm_gaussianCoeff_sub_le {a : ℕ → ℂ} {H : ℝ} (hH : 0 < H) (n : ℕ) :
    ‖gaussianHeightCoeff a H n - a n‖ ≤ ‖a n‖ := by
  rw [norm_gaussianCoeff_sub hH]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (by linarith only [Real.exp_pos (-((n : ℝ) ^ 2 / H))])

private theorem norm_integerHeightSeries_le {a : ℕ → ℂ} (ha0 : a 0 = 0)
    (ha : Summable fun n => ‖a n‖) (t : ℝ) :
    ‖integerHeightSeries a t‖ ≤ ∑' n : ℕ, ‖a n‖ := by
  unfold integerHeightSeries
  rw [PhaseSeries.phaseSeries_eq_tsum ha0]
  have hnorm : ∀ n : ℕ,
      ‖a n * Complex.exp (-((((-t) * Real.log n : ℝ) : ℂ) * I))‖ = ‖a n‖ := by
    intro n
    rw [norm_mul, PhaseSeries.norm_exp_neg_phase, mul_one]
  exact (norm_tsum_le_tsum_norm (ha.congr fun n => (hnorm n).symm)).trans_eq
    (tsum_congr hnorm)

private theorem norm_gaussianHeightCurrent_sub_le {a : ℕ → ℂ}
    (ha0 : a 0 = 0) (ha : Summable fun n => ‖a n‖) {H : ℝ} (hH : 0 < H) (t : ℝ) :
    ‖gaussianHeightCurrent a H t - integerHeightSeries a t‖ ≤
      ∑' n : ℕ, ‖gaussianHeightCoeff a H n - a n‖ := by
  have hb0 : gaussianHeightCoeff a H 0 = 0 := by simp [gaussianHeightCoeff, ha0]
  have hb := ha.of_nonneg_of_le (fun _ => norm_nonneg _) (gaussianCoeff_norm_le hH)
  have hd := ha.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_gaussianCoeff_sub_le hH)
  have hadd := PhaseSeries.phaseSeries_add_smul hb0 ha0 hb ha (-1) (-t)
  have hcoeff : gaussianHeightCoeff a H + (-1 : ℂ) • a =
      fun n => gaussianHeightCoeff a H n - a n := by
    funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul, sub_eq_add_neg]
  rw [hcoeff] at hadd
  have heq : gaussianHeightCurrent a H t - integerHeightSeries a t =
      integerHeightSeries (fun n => gaussianHeightCoeff a H n - a n) t := by
    simpa only [gaussianHeightCurrent, integerHeightSeries, neg_one_mul, sub_eq_add_neg]
      using hadd.symm
  rw [heq]
  exact norm_integerHeightSeries_le (by simp only [hb0, ha0, sub_self]) hd t

/-- Absolute admission of the complete small-prime part makes removal of
Gaussian damping uniform over every real height. -/
theorem smallPrime_gaussianDamping_uniformly_vanishes (Y : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ H : ℝ, T ≤ H → ∀ t : ℝ,
      ‖gaussianHeightCurrent (smallPrimeVonMangoldtCoeff Y σ) H t -
        integerHeightSeries (smallPrimeVonMangoldtCoeff Y σ) t‖ < ε := by
  let a := smallPrimeVonMangoldtCoeff Y σ
  have ha := summable_norm_smallPrimeVonMangoldtCoeff Y hσ
  let E : ℝ → ℝ := fun H => ∑' n : ℕ, ‖a n‖ * (1 - Real.exp (-((n : ℝ) ^ 2 / H)))
  have hE : Tendsto E atTop (𝓝 0) := by
    have hpoint : ∀ n : ℕ, Tendsto (fun H : ℝ =>
        ‖a n‖ * (1 - Real.exp (-((n : ℝ) ^ 2 / H)))) atTop (𝓝 (0 : ℝ)) := by
      intro n
      have hi : Tendsto (fun H : ℝ => H⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
      have he : Tendsto (fun H : ℝ => -((n : ℝ) ^ 2 / H)) atTop (𝓝 (0 : ℝ)) := by
        simpa only [mul_zero, div_eq_mul_inv, neg_mul] using hi.const_mul (-((n : ℝ) ^ 2))
      have hx := (Real.continuous_exp.continuousAt.tendsto).comp he
      have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
      have hd := (h1.sub hx).const_mul (‖a n‖)
      simpa only [Function.comp_def, Real.exp_zero, sub_self, mul_zero] using hd
    have hdom : ∀ᶠ H : ℝ in atTop, ∀ n : ℕ,
        ‖‖a n‖ * (1 - Real.exp (-((n : ℝ) ^ 2 / H)))‖ ≤ ‖a n‖ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH n
      rw [← norm_gaussianCoeff_sub hH, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
      exact norm_gaussianCoeff_sub_le hH n
    simpa only [E, tsum_zero] using tendsto_tsum_of_dominated_convergence ha hpoint hdom
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℝ)).and (hE.eventually (eventually_lt_nhds hε)))
  refine ⟨T, by have h := (hT T le_rfl).1; linarith, fun H hHT t => ?_⟩
  have hH : 0 < H := by have h := (hT H hHT).1; linarith
  have hbound := norm_gaussianHeightCurrent_sub_le (smallPrimeVonMangoldtCoeff_zero Y σ) ha hH t
  have heq : (∑' n : ℕ, ‖gaussianHeightCoeff a H n - a n‖) = E H :=
    tsum_congr fun n => norm_gaussianCoeff_sub hH n
  rw [heq] at hbound
  exact hbound.trans_lt (hT H hHT).2

private theorem line_term (a : ℕ → ℂ) (ha0 : a 0 = 0) (σ t : ℝ) (n : ℕ) :
    LSeries.term a ((σ : ℂ) + t * I) n =
      a n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I)) := by
  by_cases hn : n = 0
  · subst n
    simp [ha0]
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let s : ℂ := (σ : ℂ) + t * I
  have hpow : (n : ℂ) ^ s = Complex.exp ((Real.log n : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn)]
    congr 1
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnR.le]
  have he : Complex.exp (-s * (Real.log n : ℂ)) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I)) := by
    rw [Real.rpow_def_of_pos hnR, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp [s]
    push_cast
    ring
  rw [LSeries.term_of_ne_zero hn]
  change a n / (n : ℂ) ^ s = _
  rw [hpow, div_eq_mul_inv, ← Complex.exp_neg,
    show -((Real.log n : ℂ) * s) = -s * (Real.log n : ℂ) by ring, he]
  ring

/-- The phase-series observable is exactly the literal damped von Mangoldt
sum on the vertical line; the sign of height is explicit. -/
theorem gaussianDampedPrimeSum_eq_heightCurrent (σ H t : ℝ) :
    gaussianDampedPrimeSum ((σ : ℂ) + t * I) (1 / H) =
      gaussianHeightCurrent (fun n => (woldVonMangoldtWeightedCoefficient σ n : ℂ)) H (-t) := by
  have h0 : gaussianHeightCoeff (fun n => (woldVonMangoldtWeightedCoefficient σ n : ℂ)) H 0 = 0 := by
    simp [gaussianHeightCoeff, woldVonMangoldtWeightedCoefficient]
  rw [gaussianDampedPrimeSum, gaussianHeightCurrent, integerHeightSeries, neg_neg,
    PhaseSeries.phaseSeries_eq_tsum h0]
  refine tsum_congr fun n => ?_
  rw [line_term _ (by simp), gaussianHeightCoeff,
    show -(1 / H * (n : ℝ) ^ 2) = -((n : ℝ) ^ 2 / H) by ring]
  simp only [woldVonMangoldtWeightedCoefficient, Complex.ofReal_mul]
  ring

private theorem conj_integerHeightSeries {a : ℕ → ℂ} (ha0 : a 0 = 0)
    (ha : Summable fun n => ‖a n‖) (hreal : ∀ n, (starRingEnd ℂ) (a n) = a n) (t : ℝ) :
    (starRingEnd ℂ) (integerHeightSeries a t) = integerHeightSeries a (-t) := by
  have hnorm : ∀ n : ℕ,
      ‖a n * Complex.exp (-((((-t) * Real.log n : ℝ) : ℂ) * I))‖ = ‖a n‖ := by
    intro n
    rw [norm_mul, PhaseSeries.norm_exp_neg_phase, mul_one]
  have hs := (ha.congr fun n => (hnorm n).symm).of_norm
  rw [integerHeightSeries, PhaseSeries.phaseSeries_eq_tsum ha0]
  change Complex.conjCLE.toContinuousLinearMap
    (∑' n : ℕ, a n * Complex.exp (-((((-t) * Real.log n : ℝ) : ℂ) * I))) = _
  rw [Complex.conjCLE.toContinuousLinearMap.map_tsum hs,
    integerHeightSeries, neg_neg, PhaseSeries.phaseSeries_eq_tsum ha0]
  refine tsum_congr fun n => ?_
  change (starRingEnd ℂ) (a n * Complex.exp (-((((-t) * Real.log n : ℝ) : ℂ) * I))) = _
  rw [map_mul, hreal n, ← Complex.exp_conj]
  congr 1
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem norm_gaussianRough_neg (Y : ℕ) {σ H : ℝ} (hσ : 1 / 2 < σ)
    (hH : 0 < H) (t : ℝ) :
    ‖gaussianHeightCurrent (roughVonMangoldtCoeff Y σ) H (-t)‖ =
      ‖gaussianHeightCurrent (roughVonMangoldtCoeff Y σ) H t‖ := by
  let a := gaussianHeightCoeff (roughVonMangoldtCoeff Y σ) H
  have ha0 : a 0 = 0 := by simp [a, gaussianHeightCoeff, roughVonMangoldtCoeff_zero]
  have ha := summable_norm_gaussianHeightCoeff (summable_sq_roughVonMangoldtCoeff Y hσ) hH
  have hreal : ∀ n : ℕ, (starRingEnd ℂ) (a n) = a n := by
    intro n
    dsimp [a, gaussianHeightCoeff]
    rw [map_mul, Complex.conj_ofReal]
    congr 1
    unfold roughVonMangoldtCoeff
    split_ifs <;> simp
  change ‖integerHeightSeries a (-t)‖ = ‖integerHeightSeries a t‖
  rw [← conj_integerHeightSeries ha0 ha hreal t, Complex.norm_conj]

/-- The literal prime current splits into the whole small-prime component
and the whole rough component, with the same damping and observation height. -/
theorem gaussianDampedPrimeSum_eq_small_add_rough (Y : ℕ) {σ H : ℝ}
    (hσ : 1 / 2 < σ) (hH : 0 < H) (t : ℝ) :
    gaussianDampedPrimeSum ((σ : ℂ) + t * I) (1 / H) =
      gaussianHeightCurrent (smallPrimeVonMangoldtCoeff Y σ) H (-t) +
        gaussianHeightCurrent (roughVonMangoldtCoeff Y σ) H (-t) := by
  have hs0 : gaussianHeightCoeff (smallPrimeVonMangoldtCoeff Y σ) H 0 = 0 := by
    simp [gaussianHeightCoeff, smallPrimeVonMangoldtCoeff_zero]
  have hr0 : gaussianHeightCoeff (roughVonMangoldtCoeff Y σ) H 0 = 0 := by
    simp [gaussianHeightCoeff, roughVonMangoldtCoeff_zero]
  have hs := (summable_norm_smallPrimeVonMangoldtCoeff Y (by linarith : 0 < σ)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (gaussianCoeff_norm_le hH)
  have hr := summable_norm_gaussianHeightCoeff (summable_sq_roughVonMangoldtCoeff Y hσ) hH
  have hcoeff : gaussianHeightCoeff (fun n => (woldVonMangoldtWeightedCoefficient σ n : ℂ)) H =
      gaussianHeightCoeff (smallPrimeVonMangoldtCoeff Y σ) H +
        (1 : ℂ) • gaussianHeightCoeff (roughVonMangoldtCoeff Y σ) H := by
    funext n
    simp only [gaussianHeightCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [← add_mul, small_add_rough_vonMangoldtCoeff]
  rw [gaussianDampedPrimeSum_eq_heightCurrent]
  unfold gaussianHeightCurrent integerHeightSeries
  rw [hcoeff]
  simpa only [one_mul] using PhaseSeries.phaseSeries_add_smul hs0 hr0 hs hr (1 : ℂ) (-(-t))

/-- Failure of AAL supplies a regular high line below an actual exceptional
abscissa. On each escaping dyadic window, its continued Euler current plus
the complete small-prime head is uniformly the negative rough Gaussian current. -/
theorem not_asymptoticAbscissaLaw_has_regular_roughPassage
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ σ H : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ 0 < H ∧
      (∃ q : XiZeroCopy, σ < (q.1 : ℂ).re) ∧
      (∀ t : ℝ, H ≤ t → riemannZeta ((σ : ℂ) + t * I) ≠ 0) ∧
      ∀ Y : ℕ, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, H ≤ T ∧
        ∀ L : ℝ, T ≤ L → ∀ t ∈ Set.Icc L (2 * L),
          ‖logDeriv riemannZeta ((σ : ℂ) + t * I) +
            integerHeightSeries (smallPrimeVonMangoldtCoeff Y σ) (-t) +
            gaussianHeightCurrent (roughVonMangoldtCoeff Y σ) L (-t)‖ < ε := by
  classical
  obtain ⟨σ₁, hσ₁, hσ₁1, hq₁, hraw⟩ :=
    not_asymptoticAbscissaLaw_has_rawEuler_dyadicGaussianPassage hnot
  obtain ⟨F, θ, σ₂, _, _, hθ, hgap, hσ₂1, _, _, hq₂, hrest, _, _⟩ :=
    not_asymptoticAbscissaLaw_has_finiteGaussianControl hnot
  let σ : ℝ := max σ₁ σ₂
  have hσ : 1 / 2 < σ := hσ₁.trans_le (le_max_left _ _)
  have hσ1 : σ < 1 := max_lt hσ₁1 hσ₂1
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hq : ∃ q : XiZeroCopy, σ < (q.1 : ℂ).re := by
    rcases le_total σ₁ σ₂ with h | h
    · obtain ⟨q, _, hq⟩ := hq₂
      exact ⟨q, by simpa only [σ, max_eq_right h] using hq⟩
    · obtain ⟨q, hq⟩ := hq₁
      exact ⟨q, by simpa only [σ, max_eq_left h] using hq⟩
  let M : ℝ := ∑ q ∈ F, |(q.1 : ℂ).im|
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM : ∀ q ∈ F, |(q.1 : ℂ).im| ≤ M := fun q hq =>
    Finset.single_le_sum (fun p _ => abs_nonneg (p.1 : ℂ).im) hq
  let H : ℝ := M + 1
  have hH : 0 < H := by dsimp [H]; linarith only [hM0]
  have hregular : ∀ t : ℝ, H ≤ t → riemannZeta ((σ : ℂ) + t * I) ≠ 0 := by
    intro t ht
    let z : ℂ := (σ : ℂ) + t * I
    have hzre : z.re = σ := by simp [z]
    have hzim : z.im = t := by simp [z]
    have hz0 : z ≠ 0 := by
      intro he
      have h := congrArg Complex.re he
      rw [hzre, Complex.zero_re] at h
      linarith only [hσ0, h]
    have hz1 : z ≠ 1 := by
      intro he
      have h := congrArg Complex.re he
      rw [hzre, Complex.one_re] at h
      linarith only [hσ1, h]
    have hxi : xi z ≠ 0 := by
      intro hz
      obtain ⟨q, hqz⟩ := exists_xiZeroCopy_of_xi_eq_zero hz
      by_cases hqF : q ∈ F
      · have hm := hM q hqF
        rw [hqz, hzim] at hm
        dsimp [H] at ht
        linarith only [ht, hm, le_abs_self t]
      · have hr := hrest q hqF
        change (q.1 : ℂ).re ≤ θ at hr
        rw [hqz, hzre] at hr
        have hs₂ : σ₂ ≤ σ := le_max_right _ _
        linarith only [hr, hs₂, hgap]
    intro hζ
    apply hxi
    rw [xi_eq_xiUnit_mul_zeta hz0 hz1 (hσ0.trans_eq hzre.symm), hζ, mul_zero]
  refine ⟨σ, H, hσ, hσ1, hH, hq, hregular, fun Y ε hε => ?_⟩
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨T₁, _, hr⟩ := hraw (ε / 2) hε2
  obtain ⟨T₂, _, hs⟩ := smallPrime_gaussianDamping_uniformly_vanishes Y hσ0 (ε / 2) hε2
  refine ⟨max H (max T₁ T₂), le_max_left _ _, fun L hL t ht => ?_⟩
  have hHL : H ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := hH.trans_le hHL
  have hT₁ : T₁ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hT₂ : T₂ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hp := hr L hT₁ ((σ : ℂ) + t * I)
    (by simpa using (show σ₁ ≤ σ from le_max_left _ _))
    (by simpa using hσ1.le) (by simpa using ht.1) (by simpa using ht.2)
  have hh := hs L hT₂ (-t)
  have heq : logDeriv riemannZeta ((σ : ℂ) + t * I) +
      integerHeightSeries (smallPrimeVonMangoldtCoeff Y σ) (-t) +
      gaussianHeightCurrent (roughVonMangoldtCoeff Y σ) L (-t) =
    (gaussianDampedPrimeSum ((σ : ℂ) + t * I) (1 / L) +
      logDeriv riemannZeta ((σ : ℂ) + t * I)) +
    (integerHeightSeries (smallPrimeVonMangoldtCoeff Y σ) (-t) -
      gaussianHeightCurrent (smallPrimeVonMangoldtCoeff Y σ) L (-t)) := by
    rw [gaussianDampedPrimeSum_eq_small_add_rough Y hσ hL0 t]
    ring
  rw [heq]
  have hh' : ‖integerHeightSeries (smallPrimeVonMangoldtCoeff Y σ) (-t) -
      gaussianHeightCurrent (smallPrimeVonMangoldtCoeff Y σ) L (-t)‖ < ε / 2 := by
    simpa only [norm_sub_rev] using hh
  exact (norm_add_le _ _).trans_lt (by linarith only [hp, hh'])

private theorem tendsto_dyadicMean_of_uniformApproximation {f : ℝ → ℂ} {g : ℝ → ℝ → ℂ}
    (hf : Continuous f) (hg : ∀ T : ℝ, Continuous (g T))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,
      ∀ t ∈ Set.Icc T (2 * T), ‖f t - g T t‖ ≤ ε)
    {c : ℝ} (hmean : Tendsto (fun T => dyadicSquareMean (g T) T) atTop (𝓝 c)) :
    Tendsto (dyadicSquareMean f) atTop (𝓝 c) := by
  have herr : Tendsto (fun T => dyadicSquareMean f T - dyadicSquareMean (g T) T)
      atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let A : ℝ := |c| + 3
    have hA : 0 < A := by dsimp [A]; positivity
    let δ : ℝ := min 1 (ε / (2 * A))
    have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδε : δ * A ≤ ε / 2 := by
      calc
        _ ≤ (ε / (2 * A)) * A :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hA.le
        _ = _ := by field_simp
    have hM := hmean.eventually (eventually_lt_nhds (show c < c + 1 by linarith))
    filter_upwards [eventually_gt_atTop (0 : ℝ), hclose δ hδ, hM] with T hT hTclose hTM
    rw [Real.dist_eq, sub_zero]
    have hb := abs_dyadicSquareMean_sub_le hf (hg T) hT hδ.le hTclose
    refine hb.trans_lt ?_
    have hMA : dyadicSquareMean (g T) T + 1 + δ ≤ A := by
      dsimp [A]
      linarith only [hTM, hδ1, le_abs_self c]
    exact ((mul_le_mul_of_nonneg_left hMA hδ.le).trans hδε).trans_lt (by linarith)
  simpa only [sub_add_cancel, zero_add] using herr.add hmean

#print axioms summable_norm_smallPrimeVonMangoldtCoeff
#print axioms smallPrime_gaussianDamping_uniformly_vanishes
#print axioms gaussianDampedPrimeSum_eq_heightCurrent
#print axioms gaussianDampedPrimeSum_eq_small_add_rough
#print axioms not_asymptoticAbscissaLaw_has_regular_roughPassage

end GaloisForLFunctions.EulerFETransportTheory
