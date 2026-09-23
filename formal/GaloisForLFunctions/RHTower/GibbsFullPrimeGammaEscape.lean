import GaloisForLFunctions.RHTower.RouteEEulerDeficitTransport
import GaloisForLFunctions.RHTower.MobiusCriticalPrimeBlockGammaBand

/-!
# Full-prime Gamma energy escape

For every fixed `1/2 ≤ sigma < 1`, the Gamma-weighted squared modulus of the complete
Euler product over primes through `Y` tends to infinity on the fixed frequency window
`[-1,1]`. This concerns complete prime products, not the integer-prefix Möbius sum.

The existing full-aperture antiscale law supplies the peak. Write `a = 1 - sigma`,
`G = positiveEulerSquare a Y`, and `D = eulerLogDeficit a (antiscaleFrequency a Y) Y`.
The normalized squared product `q(t)` lies in `(0,1]`, equals `exp(-D)` at the peak,
and is `(Y+1) log Y`-Lipschitz. Its half-height interval has radius `q/(4Y²)`.
Any weight with local floor `c` therefore has energy at least
`(c/4) exp(log G - 2D - 2 log Y)`. The existing prime-log sum asymptotic bounds
`log G` below by `Y^a/(a log Y)(1+o(1))`, while `D = O(Y^a/(log Y)^(3 : ℕ))`.

The positive survivor is weight-independent: every continuous nonnegative weight positive
at zero sees this escape. No zero, RH, or zero-free-region premise is used. In particular,
this cannot supply or falsify bounded returns for literal integer-prefix Gamma--Hankel energy.
-/

open Filter Topology Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

private theorem abs_prod_sub_prod_le_sum {ι : Type*} (S : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i ∧ f i ≤ 1)
    (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ 1) :
    |∏ i ∈ S, f i - ∏ i ∈ S, g i| ≤ ∑ i ∈ S, |f i - g i| := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hfS : ∀ j ∈ S, 0 ≤ f j ∧ f j ≤ 1 := fun j hj => hf j (by simp [hj])
    have hgS : ∀ j ∈ S, 0 ≤ g j ∧ g j ≤ 1 := fun j hj => hg j (by simp [hj])
    have hfi := hf i (by simp)
    have hgi := hg i (by simp)
    have hF0 : 0 ≤ ∏ j ∈ S, f j := Finset.prod_nonneg fun j hj => (hfS j hj).1
    have hF1 : ∏ j ∈ S, f j ≤ 1 := Finset.prod_le_one (fun j hj => (hfS j hj).1)
      (fun j hj => (hfS j hj).2)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      |f i * ∏ j ∈ S, f j - g i * ∏ j ∈ S, g j| =
          |(f i - g i) * (∏ j ∈ S, f j) + g i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j)| := by
            congr 1; ring
      _ ≤ |f i - g i| * (∏ j ∈ S, f j) + g i * |(∏ j ∈ S, f j) - ∏ j ∈ S, g j| := by
        simpa [abs_mul, abs_of_nonneg hF0, abs_of_nonneg hgi.1] using
          abs_add_le ((f i - g i) * (∏ j ∈ S, f j))
            (g i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j))
      _ ≤ |f i - g i| + ∑ j ∈ S, |f j - g j| := by
        have h1 := mul_le_mul_of_nonneg_left hF1 (abs_nonneg (f i - g i))
        have h2 := mul_le_mul_of_nonneg_right hgi.2
          (abs_nonneg ((∏ j ∈ S, f j) - ∏ j ∈ S, g j))
        linarith [ih hfS hgS]

def fullEulerEnvelopeRatio (a t Y : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesLE ⌊Y⌋₊, (1 - eulerDeficitCoord a t p)

theorem fullEulerEnvelopeRatio_pos {a : ℝ} (ha : a < 1) (t Y : ℝ) :
    0 < fullEulerEnvelopeRatio a t Y := by
  exact Finset.prod_pos fun p hp =>
    one_sub_eulerDeficitCoord_pos (Nat.prime_of_mem_primesLE hp) ha

theorem fullEulerEnvelopeRatio_le_one {a : ℝ} (ha : a < 1) (t Y : ℝ) :
    fullEulerEnvelopeRatio a t Y ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    exact (one_sub_eulerDeficitCoord_pos (Nat.prime_of_mem_primesLE hp) ha).le
  · intro p hp
    linarith [eulerDeficitCoord_nonneg (a := a) (t := t) (Nat.prime_of_mem_primesLE hp)]

theorem fullEulerEnvelopeRatio_eq_exp {a : ℝ} (ha : a < 1) (t Y : ℝ) :
    fullEulerEnvelopeRatio a t Y = Real.exp (-eulerLogDeficit a t Y) := by
  rw [eulerLogDeficit, Finset.sum_neg_distrib, neg_neg, Real.exp_sum]
  exact Finset.prod_congr rfl fun p hp =>
    (Real.exp_log (one_sub_eulerDeficitCoord_pos (Nat.prime_of_mem_primesLE hp) ha)).symm

private theorem abs_eulerDeficitCoord_sub_le (a t u : ℝ) {p : ℕ} (hp : p.Prime) :
    |eulerDeficitCoord a t p - eulerDeficitCoord a u p| ≤ Real.log p * |t - u| := by
  let v : ℝ := (p : ℝ) ^ (a - 1)
  have hv : 0 < v := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
  have hd : 0 < (1 + v) ^ 2 := by positivity
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hc := Real.abs_cos_sub_cos_le (t * Real.log p) (u * Real.log p)
  rw [← sub_mul, abs_mul, abs_of_nonneg hl] at hc
  have heq : eulerDeficitCoord a t p - eulerDeficitCoord a u p =
      (2 * v / (1 + v) ^ 2) * (Real.cos (t * Real.log p) - Real.cos (u * Real.log p)) := by
    unfold eulerDeficitCoord
    dsimp [v]
    ring
  have hcoef0 : 0 ≤ 2 * v / (1 + v) ^ 2 := by positivity
  have hcoef1 : 2 * v / (1 + v) ^ 2 ≤ 1 := by
    rw [div_le_one hd]
    nlinarith [sq_nonneg v]
  rw [heq, abs_mul, abs_of_nonneg hcoef0]
  calc
    _ ≤ 1 * |Real.cos (t * Real.log p) - Real.cos (u * Real.log p)| :=
      mul_le_mul_of_nonneg_right hcoef1 (abs_nonneg _)
    _ ≤ Real.log p * |t - u| := by simpa [mul_comm] using hc

theorem fullEulerEnvelopeRatio_lipschitz {a Y : ℝ} (ha : a < 1) (hY : 2 ≤ Y) (t u : ℝ) :
    |fullEulerEnvelopeRatio a t Y - fullEulerEnvelopeRatio a u Y| ≤
      ((Y + 1) * Real.log Y) * |t - u| := by
  have hY0 : 0 ≤ Y := by linarith
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hf (v : ℝ) : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      0 ≤ 1 - eulerDeficitCoord a v p ∧ 1 - eulerDeficitCoord a v p ≤ 1 := by
    intro p hp
    exact ⟨(one_sub_eulerDeficitCoord_pos (Nat.prime_of_mem_primesLE hp) ha).le,
      by linarith [eulerDeficitCoord_nonneg (a := a) (t := v) (Nat.prime_of_mem_primesLE hp)]⟩
  have hcard : ((Nat.primesLE ⌊Y⌋₊).card : ℝ) ≤ Y + 1 := by
    have hn : (Nat.primesLE ⌊Y⌋₊).card ≤ ⌊Y⌋₊ + 1 := by
      simpa [Nat.primesLE, Nat.primesBelow] using
        Finset.card_filter_le (Finset.range (⌊Y⌋₊ + 1)) Nat.Prime
    have hnR : ((Nat.primesLE ⌊Y⌋₊).card : ℝ) ≤ (⌊Y⌋₊ : ℝ) + 1 := by exact_mod_cast hn
    linarith [Nat.floor_le hY0]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊,
        |(1 - eulerDeficitCoord a t p) - (1 - eulerDeficitCoord a u p)| :=
      abs_prod_sub_prod_le_sum _ _ _ (hf t) (hf u)
    _ = ∑ p ∈ Nat.primesLE ⌊Y⌋₊, |eulerDeficitCoord a t p - eulerDeficitCoord a u p| := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [show (1 - eulerDeficitCoord a t p) - (1 - eulerDeficitCoord a u p) =
        -(eulerDeficitCoord a t p - eulerDeficitCoord a u p) by ring, abs_neg]
    _ ≤ ∑ _p ∈ Nat.primesLE ⌊Y⌋₊, Real.log Y * |t - u| := by
      apply Finset.sum_le_sum
      intro p hp
      have hpP := Nat.prime_of_mem_primesLE hp
      have hpY : (p : ℝ) ≤ Y := by
        exact (Nat.cast_le.mpr (Nat.mem_primesLE.mp hp).1).trans (Nat.floor_le hY0)
      exact (abs_eulerDeficitCoord_sub_le a t u hpP).trans
        (mul_le_mul_of_nonneg_right (Real.log_le_log (by exact_mod_cast hpP.pos) hpY) (abs_nonneg _))
    _ ≤ ((Y + 1) * Real.log Y) * |t - u| := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_right hcard (mul_nonneg hlogY (abs_nonneg (t - u)))]

theorem positiveEulerSquare_pos (a Y : ℝ) : 0 < positiveEulerSquare a Y := by
  apply Finset.prod_pos
  intro p hp
  have hv : 0 < (p : ℝ) ^ (a - 1) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos) _
  positivity

theorem eulerMellinNormSq_eq_envelope_mul_ratio (a t Y : ℝ) :
    eulerMellinNormSq a t Y = positiveEulerSquare a Y * fullEulerEnvelopeRatio a t Y := by
  have h := eulerMellinNormSq_div_positiveEulerSquare a t Y
  change eulerMellinNormSq a t Y / positiveEulerSquare a Y = fullEulerEnvelopeRatio a t Y at h
  exact (div_eq_iff (positiveEulerSquare_pos a Y).ne').mp h |>.trans (mul_comm _ _)

theorem primeRpowLogSumLE_div_log_le_log_positiveEulerSquare
    {a Y : ℝ} (ha : a < 1) (hY : 2 ≤ Y) :
    primeRpowLogSumLE a Y / Real.log Y ≤ Real.log (positiveEulerSquare a Y) := by
  have hY0 : 0 ≤ Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hterm : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      (p : ℝ) ^ (a - 1) * Real.log p / Real.log Y ≤
        Real.log ((1 + (p : ℝ) ^ (a - 1)) ^ 2) := by
    intro p hp
    have hpP := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    have hv : 0 < (p : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos hp0 _
    have hv1 : (p : ℝ) ^ (a - 1) ≤ 1 :=
      (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpP.one_lt) (by linarith)).le
    have hpY : (p : ℝ) ≤ Y :=
      (Nat.cast_le.mpr (Nat.mem_primesLE.mp hp).1).trans (Nat.floor_le hY0)
    have hlogp : Real.log p ≤ Real.log Y := Real.log_le_log hp0 hpY
    have hlower := Real.le_log_one_add_of_nonneg hv.le
    have hfrac : (p : ℝ) ^ (a - 1) / 2 ≤
        2 * (p : ℝ) ^ (a - 1) / ((p : ℝ) ^ (a - 1) + 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hfirst : (p : ℝ) ^ (a - 1) * Real.log p / Real.log Y ≤ (p : ℝ) ^ (a - 1) := by
      rw [div_le_iff₀ hlogY]
      exact mul_le_mul_of_nonneg_left hlogp hv.le
    rw [Real.log_pow]
    norm_num
    linarith
  rw [positiveEulerSquare, Real.log_prod (fun p hp => by
    have hv : 0 < (p : ℝ) ^ (a - 1) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos) _
    positivity)]
  simpa [primeRpowLogSumLE, Finset.sum_div] using Finset.sum_le_sum hterm

def fullEulerEscapeExponent (a Y : ℝ) : ℝ :=
  Real.log (positiveEulerSquare a Y) -
    2 * eulerLogDeficit a (antiscaleFrequency a Y) Y - 2 * Real.log Y

theorem tendsto_fullEulerEscapeExponent {a : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Tendsto (fullEulerEscapeExponent a) atTop atTop := by
  have ha1 : a < 1 := by linarith
  have hD := tendsto_eulerLogDeficit ha0 ha2
  have hL2 : Tendsto (fun Y : ℝ => Real.log Y ^ 2) atTop atTop := by
    simpa [pow_two] using Real.tendsto_log_atTop.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hDsmall : Tendsto (fun Y : ℝ =>
      eulerLogDeficit a (antiscaleFrequency a Y) Y * Real.log Y / Y ^ a) atTop (nhds 0) := by
    refine (hD.div_atTop hL2).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    have hlog : Real.log Y ≠ 0 := (Real.log_pos hY).ne'
    have hy : Y ^ a ≠ 0 := (Real.rpow_pos_of_pos (by linarith) a).ne'
    field_simp
  have hP := tendsto_primeRpowLogSumLE ha0
  have hsmall := HTGeometry.tendsto_logPow_div_rpow ha0 2
  have hcoefficient : Tendsto (fun Y : ℝ =>
      primeRpowLogSumLE a Y / Y ^ a -
        2 * (eulerLogDeficit a (antiscaleFrequency a Y) Y * Real.log Y / Y ^ a) -
        2 * (Real.log Y ^ 2 / Y ^ a)) atTop (nhds (1 / a)) := by
    simpa using (hP.sub (hDsmall.const_mul 2)).sub (hsmall.const_mul 2)
  have hscale0 : Tendsto (fun Y : ℝ => Real.log Y / Y ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero
  have hscalePositive : ∀ᶠ Y : ℝ in atTop, Real.log Y / Y ^ a ∈ Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    exact div_pos (Real.log_pos hY) (Real.rpow_pos_of_pos (by linarith) a)
  have hscale : Tendsto (fun Y : ℝ => Y ^ a / Real.log Y) atTop atTop := by
    simpa [Function.comp_def] using tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hscale0, hscalePositive⟩)
  have hmajor := hcoefficient.pos_mul_atTop (one_div_pos.mpr ha0) hscale
  apply tendsto_atTop_mono' _ _ hmajor
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  have hlog : Real.log Y ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hy : Y ^ a ≠ 0 := (Real.rpow_pos_of_pos (by linarith) a).ne'
  have heq :
      (primeRpowLogSumLE a Y / Y ^ a -
        2 * (eulerLogDeficit a (antiscaleFrequency a Y) Y * Real.log Y / Y ^ a) -
        2 * (Real.log Y ^ 2 / Y ^ a)) * (Y ^ a / Real.log Y) =
      primeRpowLogSumLE a Y / Real.log Y -
        2 * eulerLogDeficit a (antiscaleFrequency a Y) Y - 2 * Real.log Y := by
    field_simp
  rw [heq, fullEulerEscapeExponent]
  linarith [primeRpowLogSumLE_div_log_le_log_positiveEulerSquare ha1 hY]

def fullEulerPeakWidth (a Y : ℝ) : ℝ :=
  fullEulerEnvelopeRatio a (antiscaleFrequency a Y) Y / (4 * Y ^ 2)

theorem tendsto_fullEulerPeakWidth {a : ℝ} (ha : a < 1) :
    Tendsto (fullEulerPeakWidth a) atTop (nhds 0) := by
  have hsq : Tendsto (fun Y : ℝ => 4 * Y ^ 2) atTop atTop := by
    have h : Tendsto (fun Y : ℝ => Y ^ 2) atTop atTop := by
      simpa [pow_two] using (tendsto_id : Tendsto (fun Y : ℝ => Y) atTop atTop).atTop_mul_atTop₀ tendsto_id
    exact h.const_mul_atTop (by norm_num)
  apply squeeze_zero' _ _ (tendsto_const_nhds.div_atTop hsq :
    Tendsto (fun Y : ℝ => 1 / (4 * Y ^ 2)) atTop (nhds 0))
  · filter_upwards with Y
    exact div_nonneg (fullEulerEnvelopeRatio_pos ha _ _).le (by positivity)
  · filter_upwards with Y
    exact div_le_div_of_nonneg_right (fullEulerEnvelopeRatio_le_one ha _ _) (by positivity)

theorem fullEulerPeak_half_height {a Y : ℝ} (ha : a < 1) (hY : 2 ≤ Y)
    {t : ℝ} (ht : |t - antiscaleFrequency a Y| ≤ fullEulerPeakWidth a Y) :
    fullEulerEnvelopeRatio a (antiscaleFrequency a Y) Y / 2 ≤ fullEulerEnvelopeRatio a t Y := by
  have hY0 : 0 < Y := by linarith
  have hYsq : 0 < 4 * Y ^ 2 := by positivity
  have hlog0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hlogY : Real.log Y ≤ Y := by linarith [Real.log_le_sub_one_of_pos hY0]
  have hL : (Y + 1) * Real.log Y ≤ 2 * Y ^ 2 := by nlinarith
  have hLip := fullEulerEnvelopeRatio_lipschitz ha hY t (antiscaleFrequency a Y)
  have hmul := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ (Y + 1) * Real.log Y)
  have hwidth : 0 ≤ fullEulerPeakWidth a Y :=
    div_nonneg (fullEulerEnvelopeRatio_pos ha _ _).le hYsq.le
  have hscale := mul_le_mul_of_nonneg_right hL hwidth
  have heq : 2 * Y ^ 2 * fullEulerPeakWidth a Y =
      fullEulerEnvelopeRatio a (antiscaleFrequency a Y) Y / 2 := by
    rw [fullEulerPeakWidth]
    field_simp
    ring
  rw [heq] at hscale
  have hdiff := (abs_le.mp (hLip.trans (hmul.trans hscale))).1
  linarith

theorem fullEulerPeak_weighted_integral_lower (w : ℝ → ℝ) (hw : Continuous w)
    {a Y c : ℝ} (ha : a < 1) (hY : 2 ≤ Y) (hc : 0 ≤ c)
    (hwLower : ∀ t ∈ Icc (antiscaleFrequency a Y - fullEulerPeakWidth a Y)
      (antiscaleFrequency a Y + fullEulerPeakWidth a Y), c ≤ w t) :
    c / 4 * Real.exp (fullEulerEscapeExponent a Y) ≤
      ∫ t in (antiscaleFrequency a Y - fullEulerPeakWidth a Y)..
        (antiscaleFrequency a Y + fullEulerPeakWidth a Y), w t * eulerMellinNormSq a t Y := by
  have hY0 : 0 < Y := by linarith
  have hG := positiveEulerSquare_pos a Y
  have hq := fullEulerEnvelopeRatio_pos ha (antiscaleFrequency a Y) Y
  have hd : 0 < fullEulerPeakWidth a Y := div_pos hq (by positivity)
  have hab : antiscaleFrequency a Y - fullEulerPeakWidth a Y ≤
      antiscaleFrequency a Y + fullEulerPeakWidth a Y := by linarith
  have hcont : Continuous (fun t : ℝ => w t * eulerMellinNormSq a t Y) := by
    unfold eulerMellinNormSq
    fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    (intervalIntegrable_const (c := c * positiveEulerSquare a Y *
      fullEulerEnvelopeRatio a (antiscaleFrequency a Y) Y / 2))
    (hcont.intervalIntegrable _ _) (fun t ht => by
      have hdist : |t - antiscaleFrequency a Y| ≤ fullEulerPeakWidth a Y := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      have hf := fullEulerPeak_half_height ha hY hdist
      rw [eulerMellinNormSq_eq_envelope_mul_ratio]
      calc
        _ = c * (positiveEulerSquare a Y *
            (fullEulerEnvelopeRatio a (antiscaleFrequency a Y) Y / 2)) := by ring
        _ ≤ w t * (positiveEulerSquare a Y * fullEulerEnvelopeRatio a t Y) :=
          mul_le_mul (hwLower t ht) (mul_le_mul_of_nonneg_left hf hG.le)
            (by positivity) (hc.trans (hwLower t ht)))
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hexp : Real.exp (fullEulerEscapeExponent a Y) =
      positiveEulerSquare a Y * fullEulerEnvelopeRatio a (antiscaleFrequency a Y) Y ^ 2 / Y ^ 2 := by
    rw [fullEulerEscapeExponent, Real.exp_sub, Real.exp_sub, Real.exp_log hG,
      show 2 * Real.log Y = Real.log (Y ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity : 0 < Y ^ 2), fullEulerEnvelopeRatio_eq_exp ha]
    rw [show 2 * eulerLogDeficit a (antiscaleFrequency a Y) Y =
      eulerLogDeficit a (antiscaleFrequency a Y) Y + eulerLogDeficit a (antiscaleFrequency a Y) Y by ring,
      Real.exp_add, Real.exp_neg]
    ring
  rw [hexp]
  convert hmono using 1
  rw [fullEulerPeakWidth]
  field_simp
  ring

theorem fullEuler_weighted_energy_tendsto (w : ℝ → ℝ) (hw : Continuous w)
    (hwNonneg : ∀ t, 0 ≤ w t) (hw0 : 0 < w 0)
    {a : ℝ} (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Tendsto (fun Y : ℝ => ∫ t in (-1 : ℝ)..1, w t * eulerMellinNormSq a t Y)
      atTop atTop := by
  have ha1 : a < 1 := by linarith
  obtain ⟨δ, hδ, hfloor⟩ := exists_local_half_floor_of_continuousAt_of_pos hw.continuousAt hw0
  have hsmall : Tendsto (fun Y : ℝ => |antiscaleFrequency a Y| + fullEulerPeakWidth a Y)
      atTop (nhds 0) := by
    simpa using (tendsto_antiscaleFrequency ha0).abs.add (tendsto_fullEulerPeakWidth ha1)
  have hnear : ∀ᶠ Y : ℝ in atTop,
      |antiscaleFrequency a Y| + fullEulerPeakWidth a Y < min δ 1 :=
    hsmall.eventually (gt_mem_nhds (lt_min hδ (by norm_num)))
  have hgrowth : Tendsto (fun Y : ℝ => (w 0 / 8) * Real.exp (fullEulerEscapeExponent a Y))
      atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_fullEulerEscapeExponent ha0 ha2)).const_mul_atTop (by positivity)
  apply tendsto_atTop_mono' _ _ hgrowth
  filter_upwards [hnear, eventually_ge_atTop (2 : ℝ)] with Y hnear hY
  have hd : 0 < fullEulerPeakWidth a Y :=
    div_pos (fullEulerEnvelopeRatio_pos ha1 _ _) (by positivity)
  have hnearδ := hnear.trans_le (min_le_left _ _)
  have hnear1 := hnear.trans_le (min_le_right _ _)
  have hbandAbs : ∀ t ∈ Icc (antiscaleFrequency a Y - fullEulerPeakWidth a Y)
      (antiscaleFrequency a Y + fullEulerPeakWidth a Y), |t| < δ := by
    intro t ht
    have hlo := neg_abs_le (antiscaleFrequency a Y)
    have hhi := le_abs_self (antiscaleFrequency a Y)
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hpeak := fullEulerPeak_weighted_integral_lower w hw ha1 hY
    (show 0 ≤ w 0 / 2 by positivity) (fun t ht => hfloor t (hbandAbs t ht))
  have hcont : Continuous (fun t : ℝ => w t * eulerMellinNormSq a t Y) := by
    unfold eulerMellinNormSq
    fun_prop
  have hnonneg : ∀ t, 0 ≤ w t * eulerMellinNormSq a t Y := by
    intro t
    rw [eulerMellinNormSq_eq_envelope_mul_ratio]
    exact mul_nonneg (hwNonneg t)
      (mul_nonneg (positiveEulerSquare_pos _ _).le (fullEulerEnvelopeRatio_pos ha1 _ _).le)
  have hca : (-1 : ℝ) ≤ antiscaleFrequency a Y - fullEulerPeakWidth a Y := by
    linarith [neg_abs_le (antiscaleFrequency a Y)]
  have hab : antiscaleFrequency a Y - fullEulerPeakWidth a Y ≤
      antiscaleFrequency a Y + fullEulerPeakWidth a Y := by linarith
  have hbd : antiscaleFrequency a Y + fullEulerPeakWidth a Y ≤ 1 := by
    linarith [le_abs_self (antiscaleFrequency a Y)]
  have hmono := intervalIntegral.integral_mono_interval (μ := volume) hca hab hbd
    (Filter.Eventually.of_forall hnonneg) (hcont.intervalIntegrable (-1) 1)
  calc
    _ = (w 0 / 2) / 4 * Real.exp (fullEulerEscapeExponent a Y) := by ring
    _ ≤ _ := hpeak.trans hmono

/-- Fixed-window Gamma energy of the complete prime product, not an integer-prefix sum. -/
def fullPrimeEulerGammaEnergy (sigma Y : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1,
    ‖Complex.Gamma ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 *
      eulerMellinNormSq (1 - sigma) t Y

/-- Every full prime aperture escapes on the half-open right critical strip.
The weight and aperture are literal; no zero or zero-free-region premise is used. -/
theorem fullPrimeEulerGammaEnergy_tendsto {sigma : ℝ}
    (hsigma : 1 / 2 ≤ sigma) (hsigma1 : sigma < 1) :
    Tendsto (fullPrimeEulerGammaEnergy sigma) atTop atTop := by
  have hsigma0 : 0 < sigma := by linarith
  have hΓ : Continuous (fun t : ℝ => Complex.Gamma ((sigma : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : ∀ m : ℕ, (sigma : ℂ) + (t : ℂ) * Complex.I ≠ -m := by
      intro m hm
      have h := congrArg Complex.re hm
      simp at h
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have harg : ContinuousAt (fun u : ℝ => (sigma : ℂ) + (u : ℂ) * Complex.I) t := by
      fun_prop
    exact ContinuousAt.comp (f := fun u : ℝ => (sigma : ℂ) + (u : ℂ) * Complex.I)
      (x := t) ((Complex.differentiableAt_Gamma _ hne).continuousAt) harg
  have hw : Continuous (fun t : ℝ => ‖Complex.Gamma ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) :=
    hΓ.norm.pow 2
  have hw0 : 0 < ‖Complex.Gamma ((sigma : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
    simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.Gamma_ofReal,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact sq_pos_of_pos (Real.Gamma_pos_of_pos hsigma0)
  exact fullEuler_weighted_energy_tendsto _ hw (fun t => sq_nonneg _) hw0
    (by linarith : 0 < 1 - sigma) (by linarith : 1 - sigma ≤ 1 / 2)

/-- Closed no-go for transferring bounded returns through unchanged full prime cutoffs. -/
theorem not_fullPrimeEulerGammaEnergy_bounded_returns :
    ¬ ∃ sigma C : ℝ, 1 / 2 ≤ sigma ∧ sigma < 1 ∧
      ∃ᶠ N : ℕ in atTop, fullPrimeEulerGammaEnergy sigma N ≤ C := by
  rintro ⟨sigma, C, hsigma, hsigma1, hreturns⟩
  have hlimit : Tendsto (fun N : ℕ => fullPrimeEulerGammaEnergy sigma N) atTop atTop :=
    (fullPrimeEulerGammaEnergy_tendsto hsigma hsigma1).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN, hNC⟩ := (hreturns.and_eventually (hlimit.eventually_gt_atTop C)).exists
  linarith

end RHTower

