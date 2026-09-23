import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPoleUnitPrimeCellDyadicParityProvenance
import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveFisherChiralitySelection

/-!
# Parity-fibre chirality no-go for Route P

P-G52 realizes the squarefree Route-P prime cell as parity reporter of full geometric valuation.
The corpus's horizontal producer socket asks for a source reversal whose Boolean observer has
balanced directed information loss.  This module computes the hidden term of the canonical parity
reporter.

The geometric exponential-family KL chirality splits exactly into Bernoulli parity chirality plus
geometric residual chirality at doubled natural parameter.  Residual term has same strict
orientation and vanishes only at equal endpoint rates.  Therefore canonical valuation parity is
not the missing fibre-balanced observer off the critical wall; it amplifies rather than cancels
directed chirality.
-/

open Real Set

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Log partition of geometric/Bose valuation law in negative natural parameter. -/
def sourceHorizontalBoseLogPartition (x : ℝ) : ℝ :=
  -Real.log (1 - Real.exp x)

/-- Mean geometric valuation. -/
def sourceHorizontalBoseMean (x : ℝ) : ℝ :=
  Real.exp x / (1 - Real.exp x)

/-- Fisher variance of geometric valuation. -/
def sourceHorizontalBoseVariance (x : ℝ) : ℝ :=
  Real.exp x / (1 - Real.exp x) ^ (2 : ℕ)

/-- Directed KL chirality of two geometric laws with natural parameters `c+s` and `c-s`. -/
def sourceHorizontalCenteredGeometricKLChirality (c s : ℝ) : ℝ :=
  2 * s * (sourceHorizontalBoseMean (c + s) + sourceHorizontalBoseMean (c - s)) -
    2 * (sourceHorizontalBoseLogPartition (c + s) -
      sourceHorizontalBoseLogPartition (c - s))

theorem sourceHorizontalHasDerivAt_boseLogPartition {x : ℝ} (hx : x < 0) :
    HasDerivAt sourceHorizontalBoseLogPartition (sourceHorizontalBoseMean x) x := by
  have hden : 1 - Real.exp x ≠ 0 := by
    have := Real.exp_lt_one_iff.mpr hx
    linarith
  have h := ((hasDerivAt_const x 1).sub (Real.hasDerivAt_exp x)).log hden
  change HasDerivAt (fun y => -Real.log (1 - Real.exp y))
    (Real.exp x / (1 - Real.exp x)) x
  refine (h.neg.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)).congr_deriv ?_
  change -((0 - Real.exp x) / (1 - Real.exp x)) =
    Real.exp x / (1 - Real.exp x)
  ring

theorem sourceHorizontalHasDerivAt_boseMean {x : ℝ} (hx : x < 0) :
    HasDerivAt sourceHorizontalBoseMean (sourceHorizontalBoseVariance x) x := by
  have hden : 1 - Real.exp x ≠ 0 := by
    have := Real.exp_lt_one_iff.mpr hx
    linarith
  have h := (Real.hasDerivAt_exp x).div
    ((hasDerivAt_const x 1).sub (Real.hasDerivAt_exp x)) hden
  change HasDerivAt (fun y => Real.exp y / (1 - Real.exp y))
    (Real.exp x / (1 - Real.exp x) ^ (2 : ℕ)) x
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)).congr_deriv ?_
  change (Real.exp x * (1 - Real.exp x) - Real.exp x * (0 - Real.exp x)) /
      (1 - Real.exp x) ^ (2 : ℕ) =
    Real.exp x / (1 - Real.exp x) ^ (2 : ℕ)
  ring

theorem sourceHorizontalHasDerivAt_boseVariance {x : ℝ} (hx : x < 0) :
    HasDerivAt sourceHorizontalBoseVariance
      (Real.exp x * (1 + Real.exp x) / (1 - Real.exp x) ^ (3 : ℕ)) x := by
  have hden : 1 - Real.exp x ≠ 0 := by
    have := Real.exp_lt_one_iff.mpr hx
    linarith
  have hbase := (hasDerivAt_const x 1).sub (Real.hasDerivAt_exp x)
  have hsq := hbase.pow 2
  have h := (Real.hasDerivAt_exp x).div hsq (pow_ne_zero 2 hden)
  change HasDerivAt (fun y => Real.exp y / (1 - Real.exp y) ^ (2 : ℕ)) _ x
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)).congr_deriv ?_
  simp only [Pi.pow_apply, Pi.sub_apply, Nat.cast_ofNat]
  norm_num
  field_simp [hden]
  ring

theorem sourceHorizontalBoseVariance_strictMonoOn_neg :
    StrictMonoOn sourceHorizontalBoseVariance (Iio 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Iio 0)
    (fun x hx => (sourceHorizontalHasDerivAt_boseVariance hx).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Iio] at hx
  rw [(sourceHorizontalHasDerivAt_boseVariance hx).deriv]
  have he : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx
  exact div_pos (mul_pos (Real.exp_pos x) (by positivity)) (pow_pos (by linarith) 3)

theorem sourceHorizontalCenteredGeometricKLChirality_zero (c : ℝ) :
    sourceHorizontalCenteredGeometricKLChirality c 0 = 0 := by
  simp [sourceHorizontalCenteredGeometricKLChirality]

theorem sourceHorizontalCenteredGeometricKLChirality_odd (c s : ℝ) :
    sourceHorizontalCenteredGeometricKLChirality c (-s) =
      -sourceHorizontalCenteredGeometricKLChirality c s := by
  unfold sourceHorizontalCenteredGeometricKLChirality
  ring

theorem sourceHorizontalHasDerivAt_centeredGeometricKLChirality
    {c s : ℝ} (hplus : c + s < 0) (hminus : c - s < 0) :
    HasDerivAt (sourceHorizontalCenteredGeometricKLChirality c)
      (2 * s * (sourceHorizontalBoseVariance (c + s) -
        sourceHorizontalBoseVariance (c - s))) s := by
  have hp := (sourceHorizontalHasDerivAt_boseMean hplus).comp s
    ((hasDerivAt_const s c).add (hasDerivAt_id s))
  have hm := (sourceHorizontalHasDerivAt_boseMean hminus).comp s
    ((hasDerivAt_const s c).sub (hasDerivAt_id s))
  have hlp := (sourceHorizontalHasDerivAt_boseLogPartition hplus).comp s
    ((hasDerivAt_const s c).add (hasDerivAt_id s))
  have hlm := (sourceHorizontalHasDerivAt_boseLogPartition hminus).comp s
    ((hasDerivAt_const s c).sub (hasDerivAt_id s))
  change HasDerivAt
    (fun y => 2 * y * (sourceHorizontalBoseMean (c + y) +
      sourceHorizontalBoseMean (c - y)) -
      2 * (sourceHorizontalBoseLogPartition (c + y) -
        sourceHorizontalBoseLogPartition (c - y))) _ s
  convert (((hasDerivAt_id s).const_mul 2).mul (hp.add hm)).sub
    ((hlp.sub hlm).const_mul 2) using 1
  all_goals first
    | rfl
    | (simp only [Function.comp_apply, Pi.add_apply, id_eq]; ring)

theorem sourceHorizontalCenteredGeometricKLChirality_strictMonoOn_nonneg
    (c : ℝ) (hc : c < 0) :
    StrictMonoOn (sourceHorizontalCenteredGeometricKLChirality c) (Ico 0 (-c)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 (-c))
    (fun s hs => by
      rcases hs with ⟨hs0, hsc⟩
      have hplus : c + s < 0 := by linarith
      have hminus : c - s < 0 := by linarith
      exact (sourceHorizontalHasDerivAt_centeredGeometricKLChirality hplus hminus).continuousAt.continuousWithinAt)
  intro s hs
  rw [interior_Ico] at hs
  rcases hs with ⟨hs0, hsc⟩
  have hplus : c + s < 0 := by linarith
  have hminus : c - s < 0 := by linarith
  rw [(sourceHorizontalHasDerivAt_centeredGeometricKLChirality hplus hminus).deriv]
  have hv := sourceHorizontalBoseVariance_strictMonoOn_neg hminus hplus (by linarith)
  exact mul_pos (mul_pos (by norm_num) hs0) (sub_pos.mpr hv)

/-- Geometric KL chirality vanishes only when endpoint rates coincide. -/
theorem sourceHorizontalCenteredGeometricKLChirality_eq_zero_iff
    {c s : ℝ} (hc : c < 0) (hs : |s| < -c) :
    sourceHorizontalCenteredGeometricKLChirality c s = 0 ↔ s = 0 := by
  constructor
  · intro hzero
    rcases lt_trichotomy s 0 with hneg | hzero' | hpos
    · have hmem : -s ∈ Ico 0 (-c) := by
        constructor
        · linarith
        · rw [abs_of_neg hneg] at hs
          linarith
      have hlt := sourceHorizontalCenteredGeometricKLChirality_strictMonoOn_nonneg c hc
        (by constructor <;> linarith : (0 : ℝ) ∈ Ico 0 (-c)) hmem (by linarith)
      rw [sourceHorizontalCenteredGeometricKLChirality_zero,
        sourceHorizontalCenteredGeometricKLChirality_odd, hzero] at hlt
      linarith
    · exact hzero'
    · have hmem : s ∈ Ico 0 (-c) := by
        constructor
        · linarith
        · rw [abs_of_pos hpos] at hs
          linarith
      have hlt := sourceHorizontalCenteredGeometricKLChirality_strictMonoOn_nonneg c hc
        (by constructor <;> linarith : (0 : ℝ) ∈ Ico 0 (-c)) hmem hpos
      rw [sourceHorizontalCenteredGeometricKLChirality_zero, hzero] at hlt
      linarith
  · rintro rfl
    exact sourceHorizontalCenteredGeometricKLChirality_zero c

/-- Geometric log partition splits into parity/Fermi partition and doubled residual. -/
theorem sourceHorizontalBoseLogPartition_dyadic_split {x : ℝ} (hx : x < 0) :
    sourceHorizontalBoseLogPartition x =
      RHTower.sourceHorizontalSoftplus x + sourceHorizontalBoseLogPartition (2 * x) := by
  have he : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx
  have hminus : 1 - Real.exp x ≠ 0 := by linarith
  have hplus : 1 + Real.exp x ≠ 0 := by positivity
  rw [sourceHorizontalBoseLogPartition, RHTower.sourceHorizontalSoftplus,
    sourceHorizontalBoseLogPartition]
  rw [show 2 * x = x + x by ring, Real.exp_add]
  rw [show 1 - Real.exp x * Real.exp x =
      (1 - Real.exp x) * (1 + Real.exp x) by ring,
    Real.log_mul hminus hplus]
  ring

/-- Geometric mean splits into parity mean and twice doubled residual mean. -/
theorem sourceHorizontalBoseMean_dyadic_split {x : ℝ} (hx : x < 0) :
    sourceHorizontalBoseMean x =
      Real.sigmoid x + 2 * sourceHorizontalBoseMean (2 * x) := by
  have he : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx
  have hminus : 1 - Real.exp x ≠ 0 := by linarith
  have hplus : 1 + Real.exp x ≠ 0 := by positivity
  rw [sourceHorizontalBoseMean, RHTower.sourceHorizontalSigmoid_eq_exp_div,
    sourceHorizontalBoseMean]
  rw [show 2 * x = x + x by ring, Real.exp_add]
  field_simp [hminus, hplus,
    show 1 - Real.exp x ^ (2 : ℕ) ≠ 0 by nlinarith [Real.exp_pos x]]
  ring

/-- **Exact information-chain split.**  Total geometric chirality is visible Bernoulli parity
chirality plus hidden residual chirality at doubled natural parameter. -/
theorem sourceHorizontalCenteredGeometricKLChirality_dyadic_split
    {c s : ℝ} (hplus : c + s < 0) (hminus : c - s < 0) :
    sourceHorizontalCenteredGeometricKLChirality c s =
      RHTower.sourceHorizontalCenteredBernoulliKLChirality c s +
        sourceHorizontalCenteredGeometricKLChirality (2 * c) (2 * s) := by
  rw [sourceHorizontalCenteredGeometricKLChirality,
    RHTower.sourceHorizontalCenteredBernoulliKLChirality,
    sourceHorizontalCenteredGeometricKLChirality,
    sourceHorizontalBoseMean_dyadic_split hplus,
    sourceHorizontalBoseMean_dyadic_split hminus,
    sourceHorizontalBoseLogPartition_dyadic_split hplus,
    sourceHorizontalBoseLogPartition_dyadic_split hminus]
  ring

/-- Canonical parity fibre is balanced exactly at saturation. -/
theorem sourceHorizontalParityFibreKLChirality_eq_zero_iff
    {c s : ℝ} (hc : c < 0) (hs : |s| < -c) :
    sourceHorizontalCenteredGeometricKLChirality (2 * c) (2 * s) = 0 ↔ s = 0 := by
  rw [sourceHorizontalCenteredGeometricKLChirality_eq_zero_iff (by linarith)
    (by rw [abs_mul]; norm_num; linarith)]
  norm_num

theorem sourceHorizontalParityFibreKLChirality_pos
    {c s : ℝ} (hc : c < 0) (hs : 0 < s) (hsc : s < -c) :
    0 < sourceHorizontalCenteredGeometricKLChirality (2 * c) (2 * s) := by
  have hc2 : 2 * c < 0 := mul_neg_of_pos_of_neg two_pos hc
  have hmono := sourceHorizontalCenteredGeometricKLChirality_strictMonoOn_nonneg
    (2 * c) hc2
    (by constructor <;> linarith : (0 : ℝ) ∈ Ico 0 (-(2 * c)))
    (by constructor <;> linarith : 2 * s ∈ Ico 0 (-(2 * c))) (by linarith)
  rwa [sourceHorizontalCenteredGeometricKLChirality_zero] at hmono

/-- Off-center, hidden residual has same orientation: total geometric chirality strictly exceeds
visible parity chirality on the positive branch. -/
theorem sourceHorizontalGeometricKLChirality_gt_parity
    {c s : ℝ} (hc : c < 0) (hs : 0 < s) (hsc : s < -c) :
    RHTower.sourceHorizontalCenteredBernoulliKLChirality c s <
      sourceHorizontalCenteredGeometricKLChirality c s := by
  rw [sourceHorizontalCenteredGeometricKLChirality_dyadic_split
    (by linarith) (by linarith)]
  exact lt_add_of_pos_right _
    (sourceHorizontalParityFibreKLChirality_pos hc hs hsc)

end

end RHTower.HedenmalmThetaSource
