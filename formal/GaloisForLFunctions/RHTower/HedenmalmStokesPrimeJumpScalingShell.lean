import GaloisForLFunctions.RHTower.HedenmalmStokesPrimeJumpProjector
import GaloisForLFunctions.RHTower.HedenmalmThetaPhysicalEndpointPrimeHardyGreenRenormalizationNoGo

/-!
# Source-only moving-scale prime--Stokes shells

Conjecture `HCF-SX2` was checked against the fixed-positive-scalarizer and bounded/weak-source
locks, in particular `XiWardCubicPositiveShiftDampedDiagonalSeparatorNoGo`, and against the
source identity in `HedenmalmStokesPrimeJumpProjector`.  Its surviving RH-chain edge is signed
cross-scale transport before scalarization.

The prime--Stokes aperture is defined entirely by the pole--Gamma--von-Mangoldt source.  At a
moving point `t = c*a`, it converges to one uniformly in every strict inner collar `|c| <= r < 1`
and to zero beyond the collar.  A dyadic difference therefore cancels the critical line and
selects the moving annulus `a/2 < t < a`.  The quantitative estimate is linear in total packet
multiplicity, which is the uniformity needed for a later height-cell summation.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Exact moving-collar decomposition into the unit wall jump plus regular source anomalies. -/
theorem gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_eq
    {a c : ℝ} (ha : 0 < a) (hc : |c| < 1) :
    gammaSewnMobiusApertureStokesPrimeJumpProjector a (c * a) =
      1 + (((1 + c) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 + c) * a) +
        ((1 - c) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 - c) * a)) / 8 := by
  have hc' := abs_lt.mp hc
  have hpc : 1 + c ≠ 0 := by linarith
  have hmc : 1 - c ≠ 0 := by linarith
  have hp : 0 < (1 + c) * a := mul_pos (by linarith) ha
  have hm : 0 < (1 - c) * a := mul_pos (by linarith) ha
  rw [gammaSewnMobiusApertureStokesPrimeJumpProjector]
  rw [show c * a + a = (1 + c) * a by ring,
    show c * a - a = -((1 - c) * a) by ring,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_neg]
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq,
    abs_of_pos hp, abs_of_pos hm,
    thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_four_div_add_regularAnomaly _ hp,
    thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_four_div_add_regularAnomaly _ hm]
  field_simp [hpc, hmc, ha.ne']
  ring

/-- The source-only projector converges uniformly along any moving strict inner collar. -/
theorem tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_collar
    (a c : ℕ → ℝ) {r : ℝ} (ha : ∀ n, 0 < a n)
    (ha0 : Tendsto a atTop (nhds 0))
    (_hr0 : 0 ≤ r) (hr1 : r < 1) (hc : ∀ n, |c n| ≤ r) :
    Tendsto
      (fun n => gammaSewnMobiusApertureStokesPrimeJumpProjector
        (a n) (c n * a n))
      atTop (nhds 1) := by
  let dplus : ℕ → ℝ := fun n => (1 + c n) * a n
  let dminus : ℕ → ℝ := fun n => (1 - c n) * a n
  have hcp (n : ℕ) : 0 < 1 + c n := by
    have h := (abs_le.mp (hc n)).1
    linarith
  have hcm (n : ℕ) : 0 < 1 - c n := by
    have h := (abs_le.mp (hc n)).2
    linarith
  have hdp (n : ℕ) : 0 < dplus n := mul_pos (hcp n) (ha n)
  have hdm (n : ℕ) : 0 < dminus n := mul_pos (hcm n) (ha n)
  have hupper : Tendsto (fun n => (1 + r) * a n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul ha0)
  have hdp0 : Tendsto dplus atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n => (hdp n).le)
      (Filter.Eventually.of_forall fun n => ?_) hupper
    exact mul_le_mul_of_nonneg_right (by
      have h := (abs_le.mp (hc n)).2
      linarith) (ha n).le
  have hdm0 : Tendsto dminus atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n => (hdm n).le)
      (Filter.Eventually.of_forall fun n => ?_) hupper
    exact mul_le_mul_of_nonneg_right (by
      have h := (abs_le.mp (hc n)).1
      linarith) (ha n).le
  have hdpWithin : Tendsto dplus atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hdp0, Filter.Eventually.of_forall hdp⟩
  have hdmWithin : Tendsto dminus atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hdm0, Filter.Eventually.of_forall hdm⟩
  have hAp :=
    tendsto_thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly.comp hdpWithin
  have hAm :=
    tendsto_thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly.comp hdmWithin
  have hprodP := hdp0.mul hAp
  have hprodM := hdm0.mul hAm
  have herr := (hprodP.add hprodM).div_const (8 : ℝ)
  have htotal := (tendsto_const_nhds (x := (1 : ℝ))).add herr
  convert htotal using 1
  · funext n
    rw [gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_eq
      (ha n) (lt_of_le_of_lt (hc n) hr1)]
    rfl
  · ring

/-- Once the regular source anomaly is bounded by `M`, a common aperture loses at most
`a*M/4`, uniformly throughout `|t| <= a/2`. -/
theorem abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_sub_one_le
    {a c M : ℝ} (ha : 0 < a) (hc : |c| < 1) (_hM : 0 ≤ M)
    (hplus :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 + c) * a)| ≤ M)
    (hminus :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 - c) * a)| ≤ M) :
    |gammaSewnMobiusApertureStokesPrimeJumpProjector a (c * a) - 1| ≤
      a * M / 4 := by
  have hc' := abs_lt.mp hc
  have hdp : 0 ≤ (1 + c) * a := (mul_pos (by linarith) ha).le
  have hdm : 0 ≤ (1 - c) * a := (mul_pos (by linarith) ha).le
  rw [gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_eq ha hc]
  rw [add_sub_cancel_left, abs_div]
  have htri := abs_add_le
    (((1 + c) * a) *
      thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 + c) * a))
    (((1 - c) * a) *
      thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 - c) * a))
  have htermPlus :
      |((1 + c) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 + c) * a)| ≤
        ((1 + c) * a) * M := by
    rw [abs_mul, abs_of_nonneg hdp]
    exact mul_le_mul_of_nonneg_left hplus hdp
  have htermMinus :
      |((1 - c) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 - c) * a)| ≤
        ((1 - c) * a) * M := by
    rw [abs_mul, abs_of_nonneg hdm]
    exact mul_le_mul_of_nonneg_left hminus hdm
  have hnum :
      |((1 + c) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 + c) * a) +
        ((1 - c) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 - c) * a)| ≤
        2 * a * M := by
    calc
      _ ≤ |((1 + c) * a) *
            thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 + c) * a)| +
          |((1 - c) * a) *
            thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 - c) * a)| := htri
      _ ≤ ((1 + c) * a) * M + ((1 - c) * a) * M :=
        add_le_add htermPlus htermMinus
      _ = 2 * a * M := by ring
  norm_num at hnum ⊢
  linarith

/-- Packet error is linear in total multiplicity, hence compatible with growing finite packets. -/
theorem abs_finiteGammaSewnMobiusApertureStokesPrimeJumpProjection_scaled_sub_mass_le
    {ι : Type*} (S : Finset ι) (mass c : ι → ℝ) {a M : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M)
    (hmass : ∀ i ∈ S, 0 ≤ mass i)
    (hc : ∀ i ∈ S, |c i| ≤ 1 / 2)
    (hplus : ∀ i ∈ S,
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 + c i) * a)| ≤ M)
    (hminus : ∀ i ∈ S,
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 - c i) * a)| ≤ M) :
    |finiteGammaSewnMobiusApertureStokesPrimeJumpProjection S
          (fun i => c i * a) mass a - ∑ i ∈ S, mass i| ≤
      (∑ i ∈ S, mass i) * (a * M / 4) := by
  rw [finiteGammaSewnMobiusApertureStokesPrimeJumpProjection,
    ← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ S,
        (mass i * gammaSewnMobiusApertureStokesPrimeJumpProjector a (c i * a) -
          mass i)| ≤
        ∑ i ∈ S,
          |mass i * gammaSewnMobiusApertureStokesPrimeJumpProjector a (c i * a) -
            mass i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, mass i * (a * M / 4) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [show mass i *
          gammaSewnMobiusApertureStokesPrimeJumpProjector a (c i * a) - mass i =
        mass i *
          (gammaSewnMobiusApertureStokesPrimeJumpProjector a (c i * a) - 1) by ring,
        abs_mul, abs_of_nonneg (hmass i hi)]
      exact mul_le_mul_of_nonneg_left
        (abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_sub_one_le
          ha (lt_of_le_of_lt (hc i hi) (by norm_num)) hM
          (hplus i hi) (hminus i hi))
        (hmass i hi)
    _ = (∑ i ∈ S, mass i) * (a * M / 4) := by
      rw [Finset.sum_mul]

/-- Beyond the moving collar, both source currents approach the same wall value, so the normalized
difference vanishes. -/
theorem tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_outside_right
    (a : ℕ → ℝ) {c : ℝ} (ha : ∀ n, 0 < a n)
    (ha0 : Tendsto a atTop (nhds 0)) (hc : 1 < c) :
    Tendsto
      (fun n => gammaSewnMobiusApertureStokesPrimeJumpProjector
        (a n) (c * a n))
      atTop (nhds 0) := by
  let dplus : ℕ → ℝ := fun n => (c + 1) * a n
  let dminus : ℕ → ℝ := fun n => (c - 1) * a n
  have hdp0 : Tendsto dplus atTop (nhds 0) := by
    simpa [dplus] using (tendsto_const_nhds.mul ha0 :
      Tendsto (fun n => (c + 1) * a n) atTop (nhds ((c + 1) * 0)))
  have hdm0 : Tendsto dminus atTop (nhds 0) := by
    simpa [dminus] using (tendsto_const_nhds.mul ha0 :
      Tendsto (fun n => (c - 1) * a n) atTop (nhds ((c - 1) * 0)))
  have hdp (n : ℕ) : 0 < dplus n := mul_pos (by linarith) (ha n)
  have hdm (n : ℕ) : 0 < dminus n := mul_pos (by linarith) (ha n)
  have hdpWithin : Tendsto dplus atTop (𝓝[>] (0 : ℝ)) := by
    exact tendsto_nhdsWithin_iff.mpr
      ⟨hdp0, Filter.Eventually.of_forall hdp⟩
  have hdmWithin : Tendsto dminus atTop (𝓝[>] (0 : ℝ)) := by
    exact tendsto_nhdsWithin_iff.mpr
      ⟨hdm0, Filter.Eventually.of_forall hdm⟩
  have hplus :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.comp
      hdpWithin
  have hminus :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.comp
      hdmWithin
  have h := (hplus.sub hminus).div_const (8 : ℝ)
  convert h using 1
  · funext n
    simp only [Function.comp_apply, dplus, dminus,
      gammaSewnMobiusApertureStokesPrimeJumpProjector]
    ring_nf
  · norm_num

/-- Exactly on the moving aperture boundary, half of the quantized source jump remains. -/
theorem gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary_eq
    {a : ℝ} (ha : 0 < a) :
    gammaSewnMobiusApertureStokesPrimeJumpProjector a a =
      1 / 2 + a * thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly (2 * a) / 4 := by
  have h2a : 0 < 2 * a := by positivity
  rw [gammaSewnMobiusApertureStokesPrimeJumpProjector]
  rw [show a + a = 2 * a by ring, sub_self,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_zero,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq,
    abs_of_pos h2a,
    thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_four_div_add_regularAnomaly _ h2a]
  field_simp [ha.ne']
  ring

/-- Along a shrinking moving boundary, the source projector converges to exactly one half. -/
theorem tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (ha0 : Tendsto a atTop (nhds 0)) :
    Tendsto
      (fun n => gammaSewnMobiusApertureStokesPrimeJumpProjector (a n) (a n))
      atTop (nhds (1 / 2 : ℝ)) := by
  let d : ℕ → ℝ := fun n => 2 * a n
  have hd0 : Tendsto d atTop (nhds 0) := by
    simpa [d] using (tendsto_const_nhds.mul ha0 :
      Tendsto (fun n => (2 : ℝ) * a n) atTop (nhds ((2 : ℝ) * 0)))
  have hd (n : ℕ) : 0 < d n := mul_pos (by norm_num) (ha n)
  have hdWithin : Tendsto d atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hd0, Filter.Eventually.of_forall hd⟩
  have hA :=
    tendsto_thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly.comp hdWithin
  have hprod := ha0.mul hA
  have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).add (hprod.div_const 4)
  convert h using 1
  · funext n
    rw [gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary_eq (ha n)]
    rfl
  · ring

/-- Strictly outside the aperture, universal pole terms cancel and only regular source anomalies
remain. -/
theorem gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_outside_eq
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    gammaSewnMobiusApertureStokesPrimeJumpProjector a (c * a) =
      (((c + 1) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c + 1) * a) -
        ((c - 1) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c - 1) * a)) / 8 := by
  have hcp : c + 1 ≠ 0 := by linarith
  have hcm : c - 1 ≠ 0 := by linarith
  have hp : 0 < (c + 1) * a := mul_pos (by linarith) ha
  have hm : 0 < (c - 1) * a := mul_pos (by linarith) ha
  rw [gammaSewnMobiusApertureStokesPrimeJumpProjector]
  rw [show c * a + a = (c + 1) * a by ring,
    show c * a - a = (c - 1) * a by ring]
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq,
    abs_of_pos hp, abs_of_pos hm,
    thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_four_div_add_regularAnomaly _ hp,
    thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_four_div_add_regularAnomaly _ hm]
  field_simp [hcp, hcm, ha.ne']
  ring

/-- Quantitative outside-aperture estimate: after pole cancellation, cost is `c*a*M/4`. -/
theorem abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_outside_le
    {a c M : ℝ} (ha : 0 < a) (hc : 1 < c) (_hM : 0 ≤ M)
    (hplus :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c + 1) * a)| ≤ M)
    (hminus :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c - 1) * a)| ≤ M) :
    |gammaSewnMobiusApertureStokesPrimeJumpProjector a (c * a)| ≤
      c * a * M / 4 := by
  have hcp : 0 ≤ (c + 1) * a := (mul_pos (by linarith) ha).le
  have hcm : 0 ≤ (c - 1) * a := (mul_pos (by linarith) ha).le
  rw [gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_outside_eq ha hc,
    abs_div]
  have htri :
      |((c + 1) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c + 1) * a) -
        ((c - 1) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c - 1) * a)| ≤
        |((c + 1) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c + 1) * a)| +
        |((c - 1) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c - 1) * a)| := by
    rw [sub_eq_add_neg]
    simpa only [abs_neg] using abs_add_le
      (((c + 1) * a) *
        thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c + 1) * a))
      (-(((c - 1) * a) *
        thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c - 1) * a)))
  have htermPlus :
      |((c + 1) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c + 1) * a)| ≤
        ((c + 1) * a) * M := by
    rw [abs_mul, abs_of_nonneg hcp]
    exact mul_le_mul_of_nonneg_left hplus hcp
  have htermMinus :
      |((c - 1) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c - 1) * a)| ≤
        ((c - 1) * a) * M := by
    rw [abs_mul, abs_of_nonneg hcm]
    exact mul_le_mul_of_nonneg_left hminus hcm
  have hnum :
      |((c + 1) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c + 1) * a) -
        ((c - 1) * a) *
          thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c - 1) * a)| ≤
        2 * c * a * M := by
    calc
      _ ≤ |((c + 1) * a) *
            thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c + 1) * a)| +
          |((c - 1) * a) *
            thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((c - 1) * a)| := htri
      _ ≤ ((c + 1) * a) * M + ((c - 1) * a) * M :=
        add_le_add htermPlus htermMinus
      _ = 2 * c * a * M := by ring
  norm_num at hnum ⊢
  linarith

/-- Source-defined dyadic prime--Stokes shell. -/
def gammaSewnMobiusApertureStokesPrimeDyadicShell (a t : ℝ) : ℝ :=
  gammaSewnMobiusApertureStokesPrimeJumpProjector a t -
    gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) t

/-- A dyadic prime--Stokes shell asymptotically selects `a/2 < t < a`. -/
theorem tendsto_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_annulus
    (a : ℕ → ℝ) {c : ℝ} (ha : ∀ n, 0 < a n)
    (ha0 : Tendsto a atTop (nhds 0))
    (hcLower : 1 / 2 < c) (hcUpper : c < 1) :
    Tendsto
      (fun n => gammaSewnMobiusApertureStokesPrimeDyadicShell
        (a n) (c * a n))
      atTop (nhds 1) := by
  have hcAbs : |c| ≤ c := by
    rw [abs_of_pos (by linarith : 0 < c)]
  have houter :=
    tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_collar
      a (fun _ => c) ha ha0 (by linarith : 0 ≤ c) hcUpper (fun _ => hcAbs)
  let b : ℕ → ℝ := fun n => a n / 2
  have hb : ∀ n, 0 < b n := fun n => div_pos (ha n) (by norm_num)
  have hb0 : Tendsto b atTop (nhds 0) := by
    simpa [b] using ha0.div_const (2 : ℝ)
  have hinner :=
    tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_outside_right
      b hb hb0 (show 1 < 2 * c by linarith)
  have hinner' : Tendsto
      (fun n => gammaSewnMobiusApertureStokesPrimeJumpProjector
        (a n / 2) (c * a n)) atTop (nhds 0) := by
    convert hinner using 1
    funext n
    change gammaSewnMobiusApertureStokesPrimeJumpProjector (a n / 2) (c * a n) =
      gammaSewnMobiusApertureStokesPrimeJumpProjector (a n / 2)
        (2 * c * (a n / 2))
    congr 1
    ring
  simpa [gammaSewnMobiusApertureStokesPrimeDyadicShell] using
    houter.sub hinner'

/-- At the outer dyadic-band boundary `t=a`, shell charge converges to `1/2`; no scale-boundary
blind spot remains. -/
theorem tendsto_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_upperBoundary
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (ha0 : Tendsto a atTop (nhds 0)) :
    Tendsto
      (fun n => gammaSewnMobiusApertureStokesPrimeDyadicShell (a n) (a n))
      atTop (nhds (1 / 2 : ℝ)) := by
  have houter :=
    tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary a ha ha0
  let b : ℕ → ℝ := fun n => a n / 2
  have hb : ∀ n, 0 < b n := fun n => div_pos (ha n) (by norm_num)
  have hb0 : Tendsto b atTop (nhds 0) := by
    simpa [b] using ha0.div_const (2 : ℝ)
  have hinner :=
    tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_outside_right
      b hb hb0 (show (1 : ℝ) < 2 by norm_num)
  have hinner' : Tendsto
      (fun n => gammaSewnMobiusApertureStokesPrimeJumpProjector
        (a n / 2) (a n)) atTop (nhds 0) := by
    convert hinner using 1
    funext n
    change gammaSewnMobiusApertureStokesPrimeJumpProjector (a n / 2) (a n) =
      gammaSewnMobiusApertureStokesPrimeJumpProjector (a n / 2)
        (2 * (a n / 2))
    congr 1
    ring
  simpa [gammaSewnMobiusApertureStokesPrimeDyadicShell] using
    houter.sub hinner'

/-- At the inner dyadic-band boundary `t=a/2`, shell charge also converges to `1/2`. -/
theorem tendsto_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_lowerBoundary
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (ha0 : Tendsto a atTop (nhds 0)) :
    Tendsto
      (fun n => gammaSewnMobiusApertureStokesPrimeDyadicShell (a n) (a n / 2))
      atTop (nhds (1 / 2 : ℝ)) := by
  have houter :=
    tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_collar
      a (fun _ => (1 / 2 : ℝ)) (r := 1 / 2) ha ha0 (by norm_num) (by norm_num)
        (fun _ => by norm_num)
  let b : ℕ → ℝ := fun n => a n / 2
  have hb : ∀ n, 0 < b n := fun n => div_pos (ha n) (by norm_num)
  have hb0 : Tendsto b atTop (nhds 0) := by
    simpa [b] using ha0.div_const (2 : ℝ)
  have hinner :=
    tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary b hb hb0
  have h := houter.sub hinner
  convert h using 1
  · funext n
    simp only [gammaSewnMobiusApertureStokesPrimeDyadicShell, b]
    congr 2
    ring
  · norm_num

/-- Every fixed coordinate in the closed dyadic band carries eventually more than `21/100` of
squared source-shell charge.  Boundary coordinates retain `1/4`; interior coordinates tend to
unit charge. -/
theorem eventually_twentyOneHundred_lt_sq_gammaSewnMobiusApertureStokesPrimeDyadicShell
    (a : ℕ → ℝ) {c : ℝ} (ha : ∀ n, 0 < a n)
    (ha0 : Tendsto a atTop (nhds 0))
    (hcLower : 1 / 2 ≤ c) (hcUpper : c ≤ 1) :
    ∀ᶠ n in atTop,
      (21 / 100 : ℝ) <
        gammaSewnMobiusApertureStokesPrimeDyadicShell (a n) (c * a n) ^ 2 := by
  have charge_of_half {f : ℕ → ℝ}
      (hf : Tendsto f atTop (nhds (1 / 2 : ℝ))) :
      ∀ᶠ n in atTop, (21 / 100 : ℝ) < f n ^ 2 := by
    have hsq : Tendsto (fun n => f n ^ 2) atTop (nhds ((1 / 2 : ℝ) ^ 2)) := by
      simpa only [pow_two] using hf.mul hf
    exact hsq.eventually (Ioi_mem_nhds (by norm_num))
  by_cases hcLowerEq : c = 1 / 2
  · subst c
    apply charge_of_half
    have h :=
      tendsto_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_lowerBoundary
        a ha ha0
    convert h using 1
    funext n
    congr 1
    ring
  by_cases hcUpperEq : c = 1
  · subst c
    apply charge_of_half
    simpa using
      tendsto_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_upperBoundary
        a ha ha0
  · have h :=
      tendsto_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_annulus
        a ha ha0
        (lt_of_le_of_ne hcLower (Ne.symm hcLowerEq))
        (lt_of_le_of_ne hcUpper hcUpperEq)
    have hsq : Tendsto
        (fun n =>
          gammaSewnMobiusApertureStokesPrimeDyadicShell (a n) (c * a n) ^ 2)
        atTop (nhds (1 : ℝ)) := by
      simpa only [pow_two, one_mul] using h.mul h
    exact hsq.eventually (Ioi_mem_nhds (by norm_num))

/-- Dyadic prime--Stokes shells cancel the critical line in the shrinking-aperture limit. -/
theorem tendsto_gammaSewnMobiusApertureStokesPrimeDyadicShell_zero
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (ha0 : Tendsto a atTop (nhds 0)) :
    Tendsto
      (fun n => gammaSewnMobiusApertureStokesPrimeDyadicShell (a n) 0)
      atTop (nhds 0) := by
  have houter :=
    tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_collar
      a (fun _ => 0) (r := 0) ha ha0 (by norm_num) (by norm_num)
        (fun _ => by norm_num)
  let b : ℕ → ℝ := fun n => a n / 2
  have hb : ∀ n, 0 < b n := fun n => div_pos (ha n) (by norm_num)
  have hb0 : Tendsto b atTop (nhds 0) := by
    simpa [b] using ha0.div_const (2 : ℝ)
  have hinner :=
    tendsto_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_collar
      b (fun _ => 0) (r := 0) hb hb0 (by norm_num) (by norm_num)
        (fun _ => by norm_num)
  simpa [gammaSewnMobiusApertureStokesPrimeDyadicShell, b] using
    houter.sub hinner

/-! ## Uniform source control for growing packets -/

/-- The regular pole--Gamma--von-Mangoldt anomaly has one common absolute bound on a positive
punctured interval at the wall. -/
theorem exists_pos_regularAnomaly_abs_le_near_zero :
    ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧
      ∀ d : ℝ, 0 < d → d < δ →
        |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ M := by
  let L : ℝ := 8 * (RHTower.Sieve.zetaLogDerivReg 1 -
    xiPrimeLogHigherValuation 1).re
  have hdist : ∀ᶠ d in 𝓝[>] (0 : ℝ),
      dist (thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d) L < 1 :=
    (Metric.tendsto_nhds.mp
      tendsto_thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly) 1 (by norm_num)
  have hbound : ∀ᶠ d in 𝓝[>] (0 : ℝ),
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ |L| + 1 := by
    filter_upwards [hdist] with d hd
    rw [Real.dist_eq] at hd
    calc
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| =
          |(thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d - L) + L| := by ring_nf
      _ ≤ |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d - L| + |L| :=
        abs_add_le _ _
      _ ≤ |L| + 1 := by linarith
  rcases Metric.mem_nhdsWithin_iff.mp hbound with ⟨δ, hδ, hsub⟩
  refine ⟨δ, |L| + 1, hδ, by positivity, ?_⟩
  intro d hd hdδ
  apply hsub
  constructor
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hd]
    exact hdδ
  · exact hd

/-- Consequently one pair `(δ,M)` controls every finite multiplicity packet, with no bound on its
cardinality or total mass.  Only the aperture must satisfy `a < 2δ/3`. -/
theorem abs_finiteGammaSewnMobiusApertureStokesPrimeJumpProjection_scaled_sub_mass_le_of_small
    {ι : Type*} (S : Finset ι) (mass c : ι → ℝ) {δ M a : ℝ}
    (_hδ : 0 < δ) (hM : 0 ≤ M) (ha : 0 < a) (haδ : a < 2 * δ / 3)
    (hbound : ∀ d : ℝ, 0 < d → d < δ →
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ M)
    (hmass : ∀ i ∈ S, 0 ≤ mass i)
    (hc : ∀ i ∈ S, |c i| ≤ 1 / 2) :
    |finiteGammaSewnMobiusApertureStokesPrimeJumpProjection S
          (fun i => c i * a) mass a - ∑ i ∈ S, mass i| ≤
      (∑ i ∈ S, mass i) * (a * M / 4) := by
  apply abs_finiteGammaSewnMobiusApertureStokesPrimeJumpProjection_scaled_sub_mass_le
    S mass c ha hM hmass hc
  · intro i hi
    have hc' := abs_le.mp (hc i hi)
    have hpos : 0 < (1 + c i) * a := mul_pos (by linarith) ha
    apply hbound _ hpos
    have hfac : 1 + c i ≤ 3 / 2 := by linarith
    have hmul : (1 + c i) * a ≤ (3 / 2) * a :=
      mul_le_mul_of_nonneg_right hfac ha.le
    have hscale : (3 / 2) * a < δ := by
      nlinarith
    exact lt_of_le_of_lt hmul hscale
  · intro i hi
    have hc' := abs_le.mp (hc i hi)
    have hpos : 0 < (1 - c i) * a := mul_pos (by linarith) ha
    apply hbound _ hpos
    have hfac : 1 - c i ≤ 3 / 2 := by linarith
    have hmul : (1 - c i) * a ≤ (3 / 2) * a :=
      mul_le_mul_of_nonneg_right hfac ha.le
    have hscale : (3 / 2) * a < δ := by
      nlinarith
    exact lt_of_le_of_lt hmul hscale

end

end RHTower
