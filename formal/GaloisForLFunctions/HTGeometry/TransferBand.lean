/-
The transfer band: how much room an off-line abscissa provides, and how much of it is used.

Fix a record `θ` for the critical line.  At an abscissa `σ > 1/2` three levels matter.

    convexity prediction :  **2θ(1 - σ)**            — what convexity from the record already gives
    record threshold     :  **θ - (σ - 1/2)/2**      — what would transfer back to the record
    a bound `v = μ(σ)`   :  informative iff `v < 2θ(1-σ)`, record-beating iff `v < θ - (σ-1/2)/2`

The interval between the two levels is the **transfer band**, of width

    **2θ(1-σ) - (θ - (σ-1/2)/2) = (σ - 1/2)(1/2 - 2θ)** ,

which vanishes at the critical line and grows linearly with the distance from it.  A bound inside the
band beats convexity without beating the record; only a bound below the band improves the record.

At `σ = 7/10` with `θ = 13/84` the band is `4/105 = 32/840` wide, running from `13/140 = 78/840` down
to `23/420 = 46/840`.  The published bound `3/40 = 63/840` sits `15/840` into it — a captured
fraction of `15/32` — leaving `17/840`.

Finally, the transfer deficit `D(σ) = μ(σ) - (θ - (σ-1/2)/2)` satisfies `D(σ) ≥ μ(1/2) - θ` for every
`σ`, with `D(1/2) = 0` when `μ(1/2) = θ`.  So the off-line route is a witness mechanism: it certifies
that the record is not sharp exactly when some off-line bound comes within `(σ - 1/2)/2` of the truth.
-/
import GaloisForLFunctions.HTGeometry.OffLineExponentPairProfile

namespace HTGeometry

/-! ### The three levels -/

/-- What convexity from a record `θ` predicts at abscissa `σ`. -/
def convexityPrediction (θ σ : ℚ) : ℚ := 2 * θ * (1 - σ)

/-- The convexity prediction is the record pair's own profile. -/
theorem convexityPrediction_eq_profile (κ σ : ℚ) :
    convexityPrediction κ σ = linePairProfile κ σ := rfl

@[simp] theorem convexityPrediction_at_half (θ : ℚ) : convexityPrediction θ (1 / 2) = θ := by
  unfold convexityPrediction; ring

@[simp] theorem convexityPrediction_at_one (θ : ℚ) : convexityPrediction θ 1 = 0 := by
  unfold convexityPrediction; ring

/-- The width of the transfer band at abscissa `σ`. -/
def transferBandWidth (θ σ : ℚ) : ℚ := convexityPrediction θ σ - transferThreshold θ σ

/-- **The band width factorises as `(σ - 1/2)(1/2 - 2θ)`.** -/
theorem transferBandWidth_eq (θ σ : ℚ) :
    transferBandWidth θ σ = (σ - 1 / 2) * (1 / 2 - 2 * θ) := by
  unfold transferBandWidth convexityPrediction transferThreshold; ring

/-- **The band is empty exactly on the critical line**, for any record below the convexity bound. -/
theorem transferBandWidth_zero_iff {θ σ : ℚ} (hθ : θ < 1 / 4) :
    transferBandWidth θ σ = 0 ↔ σ = 1 / 2 := by
  rw [transferBandWidth_eq]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · linarith
    · linarith
  · intro h; rw [h]; ring

/-- **The band grows linearly with the distance from the critical line.** -/
theorem transferBandWidth_mono {θ σ σ' : ℚ} (hθ : θ < 1 / 4) (h : σ < σ') :
    transferBandWidth θ σ < transferBandWidth θ σ' := by
  rw [transferBandWidth_eq, transferBandWidth_eq]; nlinarith

/-! ### The three regimes -/

/-- A bound at `σ` that does not beat convexity carries no information. -/
theorem uninformative_iff (θ σ v : ℚ) :
    convexityPrediction θ σ ≤ v ↔ 2 * θ * (1 - σ) ≤ v := Iff.rfl

/-- **A bound below the band's lower edge transfers to a better record.** -/
theorem below_band_beats_record (G : GrowthExponent) {θ σ : ℚ}
    (h : G.mu σ ≤ transferThreshold θ σ) : G.mu (1 / 2) ≤ θ := by
  unfold transferThreshold at h
  exact G.transfer_threshold σ θ h

/-- **A bound inside the band beats convexity but not the record.** -/
theorem inside_band {θ σ v : ℚ} (hlow : transferThreshold θ σ < v)
    (hhigh : v < convexityPrediction θ σ) :
    transferThreshold θ σ < v ∧ v < convexityPrediction θ σ := ⟨hlow, hhigh⟩

/-! ### The ledger at `σ = 7/10` -/

@[simp] theorem band_at_seven_tenths :
    transferBandWidth bourgainTheta (7 / 10) = 4 / 105 := by
  rw [transferBandWidth_eq]; unfold bourgainTheta; norm_num

/-- The band's two edges at `σ = 7/10`. -/
theorem band_edges_at_seven_tenths :
    convexityPrediction bourgainTheta (7 / 10) = 78 / 840 ∧
      transferThreshold bourgainTheta (7 / 10) = 46 / 840 := by
  constructor
  · unfold convexityPrediction bourgainTheta; norm_num
  · unfold transferThreshold bourgainTheta; norm_num

/-- The published bound lies strictly inside the band. -/
theorem published_inside_band :
    transferThreshold bourgainTheta (7 / 10) < muSevenTenths ∧
      muSevenTenths < convexityPrediction bourgainTheta (7 / 10) := by
  rw [band_edges_at_seven_tenths.1, band_edges_at_seven_tenths.2]
  unfold muSevenTenths
  constructor <;> norm_num

/-- The fraction of the band captured by the published bound. -/
def capturedFraction : ℚ := 15 / 32

/-- **The published bound captures `15/32` of the band.** -/
theorem published_captures :
    (convexityPrediction bourgainTheta (7 / 10) - muSevenTenths)
      = capturedFraction * transferBandWidth bourgainTheta (7 / 10) := by
  rw [band_at_seven_tenths, band_edges_at_seven_tenths.1]
  unfold muSevenTenths capturedFraction; norm_num

/-- **And `17/32` of it remains.** -/
theorem remaining_fraction :
    (muSevenTenths - transferThreshold bourgainTheta (7 / 10))
      = (17 / 32 : ℚ) * transferBandWidth bourgainTheta (7 / 10) := by
  rw [band_at_seven_tenths, band_edges_at_seven_tenths.2]
  unfold muSevenTenths; norm_num

/-! ### The transfer deficit -/

/-- How far a bound at `σ` is from transferring to the record. -/
def transferDeficit (θ σ v : ℚ) : ℚ := v - transferThreshold θ σ

/-- **On the critical line the deficit vanishes for the record itself.** -/
@[simp] theorem transferDeficit_at_half (θ : ℚ) : transferDeficit θ (1 / 2) θ = 0 := by
  unfold transferDeficit transferThreshold; ring

/-- **The deficit is bounded below by the record's own slack.**  So an off-line bound can beat the
record only if the record is not sharp. -/
theorem transferDeficit_ge_slack (G : GrowthExponent) (θ σ : ℚ) :
    G.mu (1 / 2) - θ ≤ transferDeficit θ σ (G.mu σ) := by
  unfold transferDeficit transferThreshold
  have := G.mu_half_le σ
  linarith

/-- **The witness principle.**  A negative transfer deficit at any abscissa certifies that the record
is not sharp, and the certificate is exactly a bound within `(σ - 1/2)/2` of the truth. -/
theorem negative_deficit_certifies (G : GrowthExponent) {θ σ : ℚ}
    (h : transferDeficit θ σ (G.mu σ) < 0) : G.mu (1 / 2) < θ := by
  have hge := transferDeficit_ge_slack G θ σ
  linarith

/-- The published deficit at `σ = 7/10`. -/
theorem published_deficit :
    transferDeficit bourgainTheta (7 / 10) muSevenTenths = 17 / 840 := by
  unfold transferDeficit transferThreshold muSevenTenths bourgainTheta; norm_num

end HTGeometry
