import GaloisForLFunctions.RHTower.ReflectedBiHeatSeparatedSignFiniteRateCone
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Reflected bi-heat countable separated-sign rate cone

A countably infinite negative packet below one rate separator and positive packet
above it has only its forced wall zero exactly when its first wall derivative is
nonnegative. Low weights need finite mass; high weights need finite hyperbolic
moments at every positive time.

The proof establishes countable wall dominated convergence, a strict `tsum`
comparison through `sinh(u)/u`, vanishing of the normalized low packet at infinity,
and local uniform convergence. It then transports the exact cone through countable
real-power RBH apertures to an RH-equivalent receiver.

`[NEW] [COUNTABLE INCOMMENSURATE] [EXACT SIGN CONE] [LEAN-PROVED]`
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

def reflectedBiHeatCountableSeparatedSignReporter
    (p lambda q mu : ℕ → ℝ) (t : ℝ) : ℝ :=
  -(∑' i, p i * Real.sinh (lambda i * t)) +
    ∑' j, q j * Real.sinh (mu j * t)

def reflectedBiHeatCountableSeparatedSignWallDerivative
    (p lambda q mu : ℕ → ℝ) : ℝ :=
  (∑' j, q j * mu j) - ∑' i, p i * lambda i

theorem sinh_rate_mul_div_self_le_sinh_rate
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.sinh (rate * t) / t ≤ Real.sinh rate := by
  rcases eq_or_lt_of_le ht1 with rfl | htlt
  · simp
  · have hrt : 0 < rate * t := mul_pos hrate ht
    have hmono := GaloisForLFunctions.RHTower.sinh_div_self_strictMonoOn
      (show rate * t ∈ Ioi 0 from hrt)
      (show rate ∈ Ioi 0 from hrate)
      (by nlinarith)
    calc
      Real.sinh (rate * t) / t =
          rate * (Real.sinh (rate * t) / (rate * t)) := by
        field_simp [hrate.ne', ht.ne']
      _ ≤ rate * (Real.sinh rate / rate) :=
        mul_le_mul_of_nonneg_left hmono.le hrate.le
      _ = Real.sinh rate := by field_simp [hrate.ne']

theorem summable_reflectedBiHeatCountableLowTerm
    (p lambda : ℕ → ℝ) {kappa t : ℝ}
    (ht : 0 < t)
    (hp : ∀ i, 0 ≤ p i) (hlambda : ∀ i, 0 < lambda i)
    (hlow : ∀ i, lambda i < kappa) (hpsum : Summable p) :
    Summable (fun i => p i * Real.sinh (lambda i * t)) := by
  apply Summable.of_nonneg_of_le
      (fun i => mul_nonneg (hp i)
        (Real.sinh_pos_iff.mpr (mul_pos (hlambda i) ht)).le)
      (fun i => ?_)
      (hpsum.mul_right (Real.sinh (kappa * t)))
  exact mul_le_mul_of_nonneg_left
    (Real.sinh_le_sinh.mpr
      (mul_le_mul_of_nonneg_right (hlow i).le ht.le)) (hp i)

theorem summable_reflectedBiHeatCountableLowMoment
    (p lambda : ℕ → ℝ) {kappa : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hlambda : ∀ i, 0 < lambda i)
    (hlow : ∀ i, lambda i < kappa) (hpsum : Summable p) :
    Summable (fun i => p i * lambda i) := by
  apply Summable.of_nonneg_of_le
      (fun i => mul_nonneg (hp i) (hlambda i).le)
      (fun i => mul_le_mul_of_nonneg_left (hlow i).le (hp i))
      (hpsum.mul_right kappa)

theorem summable_reflectedBiHeatCountableHighMoment
    (q mu : ℕ → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hmu : ∀ j, 0 < mu j)
    (hhigh : ∀ T : ℝ, 0 < T →
      Summable (fun j => q j * Real.sinh (mu j * T))) :
    Summable (fun j => q j * mu j) := by
  apply Summable.of_nonneg_of_le
      (fun j => mul_nonneg (hq j) (hmu j).le)
      (fun j => mul_le_mul_of_nonneg_left (self_lt_sinh (hmu j)).le (hq j))
  simpa using hhigh 1 one_pos

theorem tendsto_reflectedBiHeatCountableLowSum_div_self_nhdsGT_zero
    (p lambda : ℕ → ℝ) {kappa : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hlambda : ∀ i, 0 < lambda i)
    (hlow : ∀ i, lambda i < kappa) (hpsum : Summable p) :
    Tendsto
      (fun t : ℝ => ∑' i, p i * Real.sinh (lambda i * t) / t)
      (𝓝[>] 0) (𝓝 (∑' i, p i * lambda i)) := by
  refine tendsto_tsum_of_dominated_convergence
    (hpsum.mul_right (Real.sinh kappa)) (fun i => ?_) ?_
  · simpa only [mul_div_assoc] using
      (tendsto_sinh_rate_mul_div_self_nhdsGT_zero (hlambda i)).const_mul (p i)
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds one_pos)] with t ht ht1 i
    have hterm : 0 ≤ p i * Real.sinh (lambda i * t) / t :=
      div_nonneg (mul_nonneg (hp i)
        (Real.sinh_pos_iff.mpr (mul_pos (hlambda i) ht)).le) ht.le
    rw [Real.norm_eq_abs, abs_of_nonneg hterm]
    calc
      p i * Real.sinh (lambda i * t) / t =
          p i * (Real.sinh (lambda i * t) / t) := by ring
      _ ≤ p i * Real.sinh (lambda i) :=
        mul_le_mul_of_nonneg_left
          (sinh_rate_mul_div_self_le_sinh_rate (hlambda i) ht ht1.le) (hp i)
      _ ≤ p i * Real.sinh kappa :=
        mul_le_mul_of_nonneg_left
          (Real.sinh_le_sinh.mpr (hlow i).le) (hp i)

theorem tendsto_reflectedBiHeatCountableHighSum_div_self_nhdsGT_zero
    (q mu : ℕ → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hmu : ∀ j, 0 < mu j)
    (hhigh : ∀ T : ℝ, 0 < T →
      Summable (fun j => q j * Real.sinh (mu j * T))) :
    Tendsto
      (fun t : ℝ => ∑' j, q j * Real.sinh (mu j * t) / t)
      (𝓝[>] 0) (𝓝 (∑' j, q j * mu j)) := by
  refine tendsto_tsum_of_dominated_convergence
    (by simpa using hhigh 1 one_pos) (fun j => ?_) ?_
  · simpa only [mul_div_assoc] using
      (tendsto_sinh_rate_mul_div_self_nhdsGT_zero (hmu j)).const_mul (q j)
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds one_pos)] with t ht ht1 j
    have hterm : 0 ≤ q j * Real.sinh (mu j * t) / t :=
      div_nonneg (mul_nonneg (hq j)
        (Real.sinh_pos_iff.mpr (mul_pos (hmu j) ht)).le) ht.le
    rw [Real.norm_eq_abs, abs_of_nonneg hterm]
    calc
      q j * Real.sinh (mu j * t) / t =
          q j * (Real.sinh (mu j * t) / t) := by ring
      _ ≤ q j * Real.sinh (mu j) :=
        mul_le_mul_of_nonneg_left
          (sinh_rate_mul_div_self_le_sinh_rate (hmu j) ht ht1.le) (hq j)

theorem tendsto_reflectedBiHeatCountableSeparatedSignReporter_div_self_nhdsGT_zero
    (p lambda q mu : ℕ → ℝ) {kappa : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hlambda : ∀ i, 0 < lambda i)
    (hlow : ∀ i, lambda i < kappa) (hpsum : Summable p)
    (hq : ∀ j, 0 ≤ q j) (hmu : ∀ j, 0 < mu j)
    (hhigh : ∀ T : ℝ, 0 < T →
      Summable (fun j => q j * Real.sinh (mu j * T))) :
    Tendsto
      (fun t : ℝ =>
        reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t / t)
      (𝓝[>] 0)
      (𝓝 (reflectedBiHeatCountableSeparatedSignWallDerivative p lambda q mu)) := by
  have hlowLim := tendsto_reflectedBiHeatCountableLowSum_div_self_nhdsGT_zero
    p lambda hp hlambda hlow hpsum
  have hhighLim := tendsto_reflectedBiHeatCountableHighSum_div_self_nhdsGT_zero
    q mu hq hmu hhigh
  have hlim := hlowLim.neg.add hhighLim
  have heq :
      (fun t : ℝ =>
        -(∑' i, p i * Real.sinh (lambda i * t) / t) +
          ∑' j, q j * Real.sinh (mu j * t) / t) =ᶠ[𝓝[>] 0]
      (fun t : ℝ =>
        reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t / t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [reflectedBiHeatCountableSeparatedSignReporter]
    have hlowDiv :
        (∑' i, p i * Real.sinh (lambda i * t)) / t =
          ∑' i, p i * Real.sinh (lambda i * t) / t := by
      rw [div_eq_mul_inv, ← tsum_mul_right]
      apply tsum_congr
      intro i
      ring
    have hhighDiv :
        (∑' j, q j * Real.sinh (mu j * t)) / t =
          ∑' j, q j * Real.sinh (mu j * t) / t := by
      rw [div_eq_mul_inv, ← tsum_mul_right]
      apply tsum_congr
      intro j
      ring
    rw [add_div, neg_div, hlowDiv, hhighDiv]
  have hlim' := hlim.congr' heq
  rw [reflectedBiHeatCountableSeparatedSignWallDerivative]
  simpa only [sub_eq_add_neg, add_comm] using hlim'

theorem reflectedBiHeatCountableSeparatedSignReporter_pos
    (p lambda q mu : ℕ → ℝ) (i0 : ℕ) {kappa t : ℝ}
    (hkappa : 0 < kappa) (ht : 0 < t)
    (hp : ∀ i, 0 ≤ p i) (hp0 : 0 < p i0)
    (hlambda : ∀ i, 0 < lambda i) (hlow : ∀ i, lambda i < kappa)
    (hpsum : Summable p)
    (hq : ∀ j, 0 ≤ q j) (hhighRate : ∀ j, kappa ≤ mu j)
    (hhigh : ∀ T : ℝ, 0 < T →
      Summable (fun j => q j * Real.sinh (mu j * T)))
    (hderiv : 0 ≤
      reflectedBiHeatCountableSeparatedSignWallDerivative p lambda q mu) :
    0 < reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t := by
  have hmu : ∀ j, 0 < mu j := fun j => hkappa.trans_le (hhighRate j)
  let G : ℝ := Real.sinh (kappa * t) / (kappa * t)
  have hkt : 0 < kappa * t := mul_pos hkappa ht
  have hG : 0 < G := div_pos (Real.sinh_pos_iff.mpr hkt) hkt
  have hlowTerm : ∀ i : ℕ,
      p i * Real.sinh (lambda i * t) ≤
        (p i * lambda i) * t * G := by
    intro i
    have hlit : 0 < lambda i * t := mul_pos (hlambda i) ht
    have hmono := GaloisForLFunctions.RHTower.sinh_div_self_strictMonoOn
      (show lambda i * t ∈ Ioi 0 from hlit)
      (show kappa * t ∈ Ioi 0 from hkt)
      (mul_lt_mul_of_pos_right (hlow i) ht)
    have heq : p i * Real.sinh (lambda i * t) =
        (p i * lambda i) * t *
          (Real.sinh (lambda i * t) / (lambda i * t)) := by
      field_simp [(hlambda i).ne', ht.ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_left hmono.le
      (mul_nonneg (mul_nonneg (hp i) (hlambda i).le) ht.le)
  have hlowTerm0 :
      p i0 * Real.sinh (lambda i0 * t) <
        (p i0 * lambda i0) * t * G := by
    have hlit : 0 < lambda i0 * t := mul_pos (hlambda i0) ht
    have hmono := GaloisForLFunctions.RHTower.sinh_div_self_strictMonoOn
      (show lambda i0 * t ∈ Ioi 0 from hlit)
      (show kappa * t ∈ Ioi 0 from hkt)
      (mul_lt_mul_of_pos_right (hlow i0) ht)
    have heq : p i0 * Real.sinh (lambda i0 * t) =
        (p i0 * lambda i0) * t *
          (Real.sinh (lambda i0 * t) / (lambda i0 * t)) := by
      field_simp [(hlambda i0).ne', ht.ne']
    rw [heq]
    exact mul_lt_mul_of_pos_left hmono
      (mul_pos (mul_pos hp0 (hlambda i0)) ht)
  have hhighTerm : ∀ j : ℕ,
      (q j * mu j) * t * G ≤ q j * Real.sinh (mu j * t) := by
    intro j
    have hmut : 0 < mu j * t := mul_pos (hmu j) ht
    have hmono : G ≤ Real.sinh (mu j * t) / (mu j * t) := by
      rcases eq_or_lt_of_le (hhighRate j) with heq | hlt
      · simp [G, heq]
      · exact (GaloisForLFunctions.RHTower.sinh_div_self_strictMonoOn
          (show kappa * t ∈ Ioi 0 from hkt)
          (show mu j * t ∈ Ioi 0 from hmut)
          (mul_lt_mul_of_pos_right hlt ht)).le
    have heq : q j * Real.sinh (mu j * t) =
        (q j * mu j) * t *
          (Real.sinh (mu j * t) / (mu j * t)) := by
      field_simp [(hmu j).ne', ht.ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_left hmono
      (mul_nonneg (mul_nonneg (hq j) (hmu j).le) ht.le)
  have hlowSummable := summable_reflectedBiHeatCountableLowTerm
    p lambda ht hp hlambda hlow hpsum
  have hlowMoment := summable_reflectedBiHeatCountableLowMoment
    p lambda hp hlambda hlow hpsum
  have hhighMoment := summable_reflectedBiHeatCountableHighMoment
    q mu hq hmu hhigh
  have hlowScaled : Summable (fun i => (p i * lambda i) * t * G) :=
    (hlowMoment.mul_right t).mul_right G
  have hhighScaled : Summable (fun j => (q j * mu j) * t * G) :=
    (hhighMoment.mul_right t).mul_right G
  have hhighSummable := hhigh t ht
  have hlowSum :
      (∑' i, p i * Real.sinh (lambda i * t)) <
        ∑' i, (p i * lambda i) * t * G :=
    hlowSummable.tsum_lt_tsum (i := i0) hlowTerm hlowTerm0 hlowScaled
  have hhighSum :
      (∑' j, (q j * mu j) * t * G) ≤
        ∑' j, q j * Real.sinh (mu j * t) :=
    hhighScaled.tsum_le_tsum hhighTerm hhighSummable
  have hcommon :
      (∑' i, (p i * lambda i) * t * G) ≤
        ∑' j, (q j * mu j) * t * G := by
    have hsum : (∑' i, p i * lambda i) ≤ ∑' j, q j * mu j := by
      simpa [reflectedBiHeatCountableSeparatedSignWallDerivative] using hderiv
    have hmul := mul_le_mul_of_nonneg_right hsum (mul_nonneg ht.le hG.le)
    simpa only [show ∀ a : ℝ, a * t * G = a * (t * G) by intro a; ring,
      tsum_mul_right] using hmul
  rw [reflectedBiHeatCountableSeparatedSignReporter]
  linarith

theorem reflectedBiHeatCountableSeparatedSignWallOriented_iff
    (p lambda q mu : ℕ → ℝ) (i0 : ℕ) {kappa : ℝ}
    (hkappa : 0 < kappa)
    (hp : ∀ i, 0 ≤ p i) (hp0 : 0 < p i0)
    (hlambda : ∀ i, 0 < lambda i) (hlow : ∀ i, lambda i < kappa)
    (hpsum : Summable p)
    (hq : ∀ j, 0 ≤ q j) (hhighRate : ∀ j, kappa ≤ mu j)
    (hhigh : ∀ T : ℝ, 0 < T →
      Summable (fun j => q j * Real.sinh (mu j * T))) :
    0 ≤ reflectedBiHeatCountableSeparatedSignWallDerivative p lambda q mu ↔
      ∀ t : ℝ, 0 < t →
        0 < reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t := by
  have hmu : ∀ j, 0 < mu j := fun j => hkappa.trans_le (hhighRate j)
  constructor
  · intro hderiv t ht
    exact reflectedBiHeatCountableSeparatedSignReporter_pos
      p lambda q mu i0 hkappa ht hp hp0 hlambda hlow hpsum hq hhighRate hhigh hderiv
  · intro horiented
    by_contra hnot
    have hderiv :
        reflectedBiHeatCountableSeparatedSignWallDerivative p lambda q mu < 0 :=
      lt_of_not_ge hnot
    have hlim :=
      tendsto_reflectedBiHeatCountableSeparatedSignReporter_div_self_nhdsGT_zero
        p lambda q mu hp hlambda hlow hpsum hq hmu hhigh
    have hevNeg : ∀ᶠ t in 𝓝[>] 0,
        reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t / t < 0 :=
      (tendsto_order.mp hlim).2 0 hderiv
    have hevPos : ∀ᶠ t in 𝓝[>] 0, t ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
    rcases (hevPos.and hevNeg).exists with ⟨t, ht, hneg⟩
    have hvalue : reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t < 0 := by
      have := (div_lt_iff₀ (show 0 < t from ht)).mp hneg
      simpa using this
    exact (not_lt_of_ge (horiented t ht).le) hvalue

theorem reflectedBiHeatCountableSeparatedSignReporter_neg
    (p lambda q mu : ℕ → ℝ) (t : ℝ) :
    reflectedBiHeatCountableSeparatedSignReporter p lambda q mu (-t) =
      -reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t := by
  simp only [reflectedBiHeatCountableSeparatedSignReporter]
  simp_rw [show ∀ r : ℝ, r * -t = -(r * t) by intro r; ring,
    Real.sinh_neg, mul_neg]
  rw [tsum_neg, tsum_neg]
  ring

theorem tendsto_reflectedBiHeatCountableLowRateSum_div_sinh_atTop
    (p lambda : ℕ → ℝ) {kappa : ℝ}
    (hkappa : 0 < kappa)
    (hp : ∀ i, 0 ≤ p i) (hlambda : ∀ i, 0 < lambda i)
    (hlow : ∀ i, lambda i < kappa) (hpsum : Summable p) :
    Tendsto
      (fun t : ℝ =>
        (∑' i, p i * Real.sinh (lambda i * t)) /
          Real.sinh (kappa * t))
      atTop (𝓝 0) := by
  have hpoint : ∀ i : ℕ,
      Tendsto
        (fun t : ℝ =>
          p i * Real.sinh (lambda i * t) / Real.sinh (kappa * t))
        atTop (𝓝 0) := by
    intro i
    have htop := tendsto_sinh_rate_ratio_atTop (hlambda i) (hlow i)
    have hinv : Tendsto
        (fun t : ℝ => 1 /
          (Real.sinh (kappa * t) / Real.sinh (lambda i * t)))
        atTop (𝓝 0) := htop.const_div_atTop 1
    have hratio : Tendsto
        (fun t : ℝ => Real.sinh (lambda i * t) / Real.sinh (kappa * t))
        atTop (𝓝 0) := by
      apply hinv.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hsl : Real.sinh (lambda i * t) ≠ 0 :=
        (Real.sinh_pos_iff.mpr (mul_pos (hlambda i) ht)).ne'
      have hsk : Real.sinh (kappa * t) ≠ 0 :=
        (Real.sinh_pos_iff.mpr (mul_pos hkappa ht)).ne'
      field_simp
    have hmul := (tendsto_const_nhds.mul hratio :
      Tendsto
        (fun t : ℝ => p i *
          (Real.sinh (lambda i * t) / Real.sinh (kappa * t)))
        atTop (𝓝 (p i * 0)))
    simpa [mul_div_assoc] using hmul
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ i : ℕ,
      ‖p i * Real.sinh (lambda i * t) / Real.sinh (kappa * t)‖ ≤ p i := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht i
    have hnum : 0 ≤ p i * Real.sinh (lambda i * t) :=
      mul_nonneg (hp i)
        (Real.sinh_pos_iff.mpr (mul_pos (hlambda i) ht)).le
    have hden : 0 < Real.sinh (kappa * t) :=
      Real.sinh_pos_iff.mpr (mul_pos hkappa ht)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum hden.le),
      div_le_iff₀ hden]
    calc
      p i * Real.sinh (lambda i * t) ≤
          p i * Real.sinh (kappa * t) :=
        mul_le_mul_of_nonneg_left
          (Real.sinh_le_sinh.mpr
            (mul_le_mul_of_nonneg_right (hlow i).le ht.le)) (hp i)
      _ = p i * Real.sinh (kappa * t) := rfl
  have hlim := tendsto_tsum_of_dominated_convergence
    hpsum hpoint hbound
  have heq :
      (fun t : ℝ =>
        ∑' i, p i * Real.sinh (lambda i * t) / Real.sinh (kappa * t)) =
      (fun t : ℝ =>
        (∑' i, p i * Real.sinh (lambda i * t)) /
          Real.sinh (kappa * t)) := by
    funext t
    rw [div_eq_mul_inv, ← tsum_mul_right]
    apply tsum_congr
    intro i
    ring
  simpa [heq] using hlim

theorem continuousOn_reflectedBiHeatCountableSeparatedSignReporter_Icc
    (p lambda q mu : ℕ → ℝ) {kappa b : ℝ}
    (hkappa : 0 < kappa) (hb : 0 < b)
    (hp : ∀ i, 0 ≤ p i) (hlambda : ∀ i, 0 < lambda i)
    (hlow : ∀ i, lambda i < kappa) (hpsum : Summable p)
    (hq : ∀ j, 0 ≤ q j) (hmu : ∀ j, 0 < mu j)
    (hhigh : ∀ T : ℝ, 0 < T →
      Summable (fun j => q j * Real.sinh (mu j * T))) :
    ContinuousOn
      (reflectedBiHeatCountableSeparatedSignReporter p lambda q mu)
      (Icc 0 b) := by
  have hlowCont : ContinuousOn
      (fun t : ℝ => ∑' i, p i * Real.sinh (lambda i * t))
      (Icc 0 b) := by
    apply continuousOn_tsum
    · intro i
      fun_prop
    · exact hpsum.mul_right (Real.sinh (kappa * b))
    · intro i t ht
      have hterm : 0 ≤ p i * Real.sinh (lambda i * t) :=
        mul_nonneg (hp i)
          (Real.sinh_nonneg_iff.mpr (mul_nonneg (hlambda i).le ht.1))
      rw [Real.norm_eq_abs, abs_of_nonneg hterm]
      apply mul_le_mul_of_nonneg_left _ (hp i)
      rw [Real.sinh_le_sinh]
      calc
        lambda i * t ≤ kappa * t :=
          mul_le_mul_of_nonneg_right (hlow i).le ht.1
        _ ≤ kappa * b := mul_le_mul_of_nonneg_left ht.2 hkappa.le
  have hhighCont : ContinuousOn
      (fun t : ℝ => ∑' j, q j * Real.sinh (mu j * t))
      (Icc 0 b) := by
    apply continuousOn_tsum
    · intro j
      fun_prop
    · exact hhigh b hb
    · intro j t ht
      have hterm : 0 ≤ q j * Real.sinh (mu j * t) :=
        mul_nonneg (hq j)
          (Real.sinh_nonneg_iff.mpr (mul_nonneg (hmu j).le ht.1))
      rw [Real.norm_eq_abs, abs_of_nonneg hterm]
      apply mul_le_mul_of_nonneg_left _ (hq j)
      rw [Real.sinh_le_sinh]
      exact mul_le_mul_of_nonneg_left ht.2 (hmu j).le
  change ContinuousOn
    (fun t : ℝ => -(∑' i, p i * Real.sinh (lambda i * t)) +
      ∑' j, q j * Real.sinh (mu j * t)) (Icc 0 b)
  exact hlowCont.neg.add hhighCont

theorem exists_pos_reflectedBiHeatCountableSeparatedSignReporter_eq_zero_of_derivative_neg
    (p lambda q mu : ℕ → ℝ) (j0 : ℕ) {kappa : ℝ}
    (hkappa : 0 < kappa)
    (hp : ∀ i, 0 ≤ p i)
    (hlambda : ∀ i, 0 < lambda i) (hlow : ∀ i, lambda i < kappa)
    (hpsum : Summable p)
    (hq : ∀ j, 0 ≤ q j) (hq0 : 0 < q j0)
    (hhighRate : ∀ j, kappa ≤ mu j)
    (hhigh : ∀ T : ℝ, 0 < T →
      Summable (fun j => q j * Real.sinh (mu j * T)))
    (hderiv :
      reflectedBiHeatCountableSeparatedSignWallDerivative p lambda q mu < 0) :
    ∃ t : ℝ, 0 < t ∧
      reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t = 0 := by
  have hmu : ∀ j, 0 < mu j := fun j => hkappa.trans_le (hhighRate j)
  have hzeroLim :=
    tendsto_reflectedBiHeatCountableSeparatedSignReporter_div_self_nhdsGT_zero
      p lambda q mu hp hlambda hlow hpsum hq hmu hhigh
  have hevNeg : ∀ᶠ t in 𝓝[>] 0,
      reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t / t < 0 :=
    (tendsto_order.mp hzeroLim).2 0 hderiv
  obtain ⟨t0, ht0, hneg0⟩ : ∃ t0 : ℝ, 0 < t0 ∧
      reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t0 < 0 := by
    have hevPos : ∀ᶠ t in 𝓝[>] 0, t ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
    rcases (hevPos.and hevNeg).exists with ⟨t, ht, hnorm⟩
    have hvalue : reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t < 0 := by
      have := (div_lt_iff₀ (show 0 < t from ht)).mp hnorm
      simpa using this
    exact ⟨t, ht, hvalue⟩
  have hratioLim := tendsto_reflectedBiHeatCountableLowRateSum_div_sinh_atTop
    p lambda hkappa hp hlambda hlow hpsum
  have hevRatio : ∀ᶠ t in atTop,
      (∑' i, p i * Real.sinh (lambda i * t)) / Real.sinh (kappa * t) < q j0 :=
    (tendsto_order.mp hratioLim).2 (q j0) hq0
  obtain ⟨t1, ht01, hratio⟩ : ∃ t1 : ℝ, t0 ≤ t1 ∧
      (∑' i, p i * Real.sinh (lambda i * t1)) /
        Real.sinh (kappa * t1) < q j0 := by
    exact ((eventually_ge_atTop t0).and hevRatio).exists
  have ht1 : 0 < t1 := ht0.trans_le ht01
  have hsk : 0 < Real.sinh (kappa * t1) :=
    Real.sinh_pos_iff.mpr (mul_pos hkappa ht1)
  have hlowLt : (∑' i, p i * Real.sinh (lambda i * t1)) <
      q j0 * Real.sinh (kappa * t1) :=
    (div_lt_iff₀ hsk).mp hratio
  have hsepAtom : q j0 * Real.sinh (kappa * t1) ≤
      q j0 * Real.sinh (mu j0 * t1) := by
    exact mul_le_mul_of_nonneg_left
      (Real.sinh_le_sinh.mpr
        (mul_le_mul_of_nonneg_right (hhighRate j0) ht1.le)) (hq j0)
  have hhighSummable := hhigh t1 ht1
  have hhighAtom : q j0 * Real.sinh (mu j0 * t1) ≤
      ∑' j, q j * Real.sinh (mu j * t1) := by
    exact hhighSummable.le_tsum j0 (fun j _ =>
      mul_nonneg (hq j)
        (Real.sinh_pos_iff.mpr (mul_pos (hmu j) ht1)).le)
  have hpos1 : 0 <
      reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t1 := by
    rw [reflectedBiHeatCountableSeparatedSignReporter]
    linarith
  have hcont0 := continuousOn_reflectedBiHeatCountableSeparatedSignReporter_Icc
    p lambda q mu hkappa ht1 hp hlambda hlow hpsum hq hmu hhigh
  have hcont : ContinuousOn
      (reflectedBiHeatCountableSeparatedSignReporter p lambda q mu)
      (Icc t0 t1) :=
    hcont0.mono (fun t ht => ⟨ht0.le.trans ht.1, ht.2⟩)
  have hmem : (0 : ℝ) ∈ Icc
      (reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t0)
      (reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t1) :=
    ⟨hneg0.le, hpos1.le⟩
  rcases intermediate_value_Icc ht01 hcont hmem with ⟨t, ht, hzero⟩
  exact ⟨t, ht0.trans_le ht.1, hzero⟩

theorem reflectedBiHeatCountableSeparatedSignWallSelective_iff
    (p lambda q mu : ℕ → ℝ) (i0 j0 : ℕ) {kappa : ℝ}
    (hkappa : 0 < kappa)
    (hp : ∀ i, 0 ≤ p i) (hp0 : 0 < p i0)
    (hlambda : ∀ i, 0 < lambda i) (hlow : ∀ i, lambda i < kappa)
    (hpsum : Summable p)
    (hq : ∀ j, 0 ≤ q j) (hq0 : 0 < q j0)
    (hhighRate : ∀ j, kappa ≤ mu j)
    (hhigh : ∀ T : ℝ, 0 < T →
      Summable (fun j => q j * Real.sinh (mu j * T))) :
    0 ≤ reflectedBiHeatCountableSeparatedSignWallDerivative p lambda q mu ↔
      ∀ t : ℝ,
        reflectedBiHeatCountableSeparatedSignReporter p lambda q mu t = 0 ↔ t = 0 := by
  constructor
  · intro hderiv t
    constructor
    · intro hzero
      by_contra ht
      rcases lt_or_gt_of_ne ht with htneg | htpos
      · have hpos := reflectedBiHeatCountableSeparatedSignReporter_pos
          p lambda q mu i0 hkappa (neg_pos.mpr htneg) hp hp0 hlambda hlow
          hpsum hq hhighRate hhigh hderiv
        have hnegzero :
            reflectedBiHeatCountableSeparatedSignReporter p lambda q mu (-t) = 0 := by
          rw [reflectedBiHeatCountableSeparatedSignReporter_neg, hzero, neg_zero]
        exact hpos.ne' hnegzero
      · have hpos := reflectedBiHeatCountableSeparatedSignReporter_pos
          p lambda q mu i0 hkappa htpos hp hp0 hlambda hlow
          hpsum hq hhighRate hhigh hderiv
        exact hpos.ne' hzero
    · rintro rfl
      simp [reflectedBiHeatCountableSeparatedSignReporter]
  · intro hselect
    by_contra hnot
    have hderiv :
        reflectedBiHeatCountableSeparatedSignWallDerivative p lambda q mu < 0 :=
      lt_of_not_ge hnot
    rcases
        exists_pos_reflectedBiHeatCountableSeparatedSignReporter_eq_zero_of_derivative_neg
          p lambda q mu j0 hkappa hp hlambda hlow hpsum hq hq0 hhighRate hhigh hderiv with
      ⟨t, ht, hzero⟩
    exact ht.ne' ((hselect t).mp hzero)

def reflectedBiHeatCountableSeparatedSignApertureGap
    (p lambda q mu : ℕ → ℝ)
    (x : ℝ) (rho : XiDivisorSupport) : ℝ :=
  -(∑' i, p i * x ^ (lambda i / 2) *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ lambda i) ^ (2 : ℕ) -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ lambda i) ^ (2 : ℕ))) +
    ∑' j, q j * x ^ (mu j / 2) *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ mu j) ^ (2 : ℕ) -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ mu j) ^ (2 : ℕ))

theorem reflectedBiHeatCountableSeparatedSignApertureGap_eq_reporter
    (p lambda q mu : ℕ → ℝ)
    {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) :
    reflectedBiHeatCountableSeparatedSignApertureGap p lambda q mu x rho =
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ (2 : ℕ) *
        reflectedBiHeatCountableSeparatedSignReporter p lambda q mu
          (Real.log x * ((rho : ℂ).re - 1 / 2)) := by
  let C : ℝ := 2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ (2 : ℕ)
  let u : ℝ := Real.log x * ((rho : ℂ).re - 1 / 2)
  have hlow :
      (∑' i, p i * x ^ (lambda i / 2) *
        (reflectedBiHeatLeftLeadingJetNorm rho (x ^ lambda i) ^ (2 : ℕ) -
          reflectedBiHeatRightLeadingJetNorm rho (x ^ lambda i) ^ (2 : ℕ))) =
      ∑' i, C * (p i * Real.sinh (lambda i * u)) := by
    apply tsum_congr
    intro i
    have hi := reflectedBiHeatWeightedRealPowerApertureGap_eq_sinh
      (lambda i) hx rho
    dsimp only [C, u]
    calc
      p i * x ^ (lambda i / 2) *
          (reflectedBiHeatLeftLeadingJetNorm rho (x ^ lambda i) ^ (2 : ℕ) -
            reflectedBiHeatRightLeadingJetNorm rho (x ^ lambda i) ^ (2 : ℕ)) =
        p i * (x ^ (lambda i / 2) *
          (reflectedBiHeatLeftLeadingJetNorm rho (x ^ lambda i) ^ (2 : ℕ) -
            reflectedBiHeatRightLeadingJetNorm rho (x ^ lambda i) ^ (2 : ℕ))) := by ring
      _ = p i * (2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ (2 : ℕ) *
          Real.sinh (lambda i *
            (Real.log x * ((rho : ℂ).re - 1 / 2)))) := by rw [hi]
      _ = _ := by ring
  have hhighEq :
      (∑' j, q j * x ^ (mu j / 2) *
        (reflectedBiHeatLeftLeadingJetNorm rho (x ^ mu j) ^ (2 : ℕ) -
          reflectedBiHeatRightLeadingJetNorm rho (x ^ mu j) ^ (2 : ℕ))) =
      ∑' j, C * (q j * Real.sinh (mu j * u)) := by
    apply tsum_congr
    intro j
    have hj := reflectedBiHeatWeightedRealPowerApertureGap_eq_sinh
      (mu j) hx rho
    dsimp only [C, u]
    calc
      q j * x ^ (mu j / 2) *
          (reflectedBiHeatLeftLeadingJetNorm rho (x ^ mu j) ^ (2 : ℕ) -
            reflectedBiHeatRightLeadingJetNorm rho (x ^ mu j) ^ (2 : ℕ)) =
        q j * (x ^ (mu j / 2) *
          (reflectedBiHeatLeftLeadingJetNorm rho (x ^ mu j) ^ (2 : ℕ) -
            reflectedBiHeatRightLeadingJetNorm rho (x ^ mu j) ^ (2 : ℕ))) := by ring
      _ = q j * (2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ (2 : ℕ) *
          Real.sinh (mu j *
            (Real.log x * ((rho : ℂ).re - 1 / 2)))) := by rw [hj]
      _ = _ := by ring
  rw [reflectedBiHeatCountableSeparatedSignApertureGap,
    reflectedBiHeatCountableSeparatedSignReporter, hlow, hhighEq]
  change -(∑' i, C * (p i * Real.sinh (lambda i * u))) +
      ∑' j, C * (q j * Real.sinh (mu j * u)) =
    C * (-(∑' i, p i * Real.sinh (lambda i * u)) +
      ∑' j, q j * Real.sinh (mu j * u))
  rw [tsum_mul_left, tsum_mul_left]
  ring

theorem reflectedBiHeatCountableSeparatedSignApertureGap_eq_zero_iff
    (p lambda q mu : ℕ → ℝ) (i0 j0 : ℕ) {kappa : ℝ}
    (hkappa : 0 < kappa)
    (hp : ∀ i, 0 ≤ p i) (hp0 : 0 < p i0)
    (hlambda : ∀ i, 0 < lambda i) (hlow : ∀ i, lambda i < kappa)
    (hpsum : Summable p)
    (hq : ∀ j, 0 ≤ q j) (hq0 : 0 < q j0)
    (hhighRate : ∀ j, kappa ≤ mu j)
    (hhigh : ∀ T : ℝ, 0 < T →
      Summable (fun j => q j * Real.sinh (mu j * T)))
    (hderiv : 0 ≤
      reflectedBiHeatCountableSeparatedSignWallDerivative p lambda q mu)
    {x : ℝ} (hx : 1 < x) (rho : XiDivisorSupport) :
    reflectedBiHeatCountableSeparatedSignApertureGap p lambda q mu x rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflectedBiHeatCountableSeparatedSignApertureGap_eq_reporter
    p lambda q mu (lt_trans zero_lt_one hx) rho]
  have hcoef :
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ (2 : ℕ) ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)))
  have hselect :=
    (reflectedBiHeatCountableSeparatedSignWallSelective_iff
      p lambda q mu i0 j0 hkappa hp hp0 hlambda hlow hpsum hq hq0
        hhighRate hhigh).mp hderiv
  constructor
  · intro hzero
    have hreport : reflectedBiHeatCountableSeparatedSignReporter p lambda q mu
        (Real.log x * ((rho : ℂ).re - 1 / 2)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hcoef
    have hu := (hselect
      (Real.log x * ((rho : ℂ).re - 1 / 2))).mp hreport
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hsub : (rho : ℂ).re - 1 / 2 = 0 :=
      (mul_eq_zero.mp hu).resolve_left hlog.ne'
    exact sub_eq_zero.mp hsub
  · intro hre
    rw [hre, sub_self, mul_zero]
    simp [reflectedBiHeatCountableSeparatedSignReporter]

theorem riemannHypothesis_iff_reflectedBiHeatCountableSeparatedSignApertureGap_eq_zero
    (p lambda q mu : ℕ → ℝ) (i0 j0 : ℕ) {kappa : ℝ}
    (hkappa : 0 < kappa)
    (hp : ∀ i, 0 ≤ p i) (hp0 : 0 < p i0)
    (hlambda : ∀ i, 0 < lambda i) (hlow : ∀ i, lambda i < kappa)
    (hpsum : Summable p)
    (hq : ∀ j, 0 ≤ q j) (hq0 : 0 < q j0)
    (hhighRate : ∀ j, kappa ≤ mu j)
    (hhigh : ∀ T : ℝ, 0 < T →
      Summable (fun j => q j * Real.sinh (mu j * T)))
    (hderiv : 0 ≤
      reflectedBiHeatCountableSeparatedSignWallDerivative p lambda q mu)
    {x : ℝ} (hx : 1 < x) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatCountableSeparatedSignApertureGap p lambda q mu x rho = 0 := by
  constructor
  · intro hRH rho
    exact (reflectedBiHeatCountableSeparatedSignApertureGap_eq_zero_iff
      p lambda q mu i0 j0 hkappa hp hp0 hlambda hlow hpsum hq hq0
        hhighRate hhigh hderiv hx rho).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (reflectedBiHeatCountableSeparatedSignApertureGap_eq_zero_iff
        p lambda q mu i0 j0 hkappa hp hp0 hlambda hlow hpsum hq hq0
          hhighRate hhigh hderiv hx rho).mp (h rho)

end

end RHTower

