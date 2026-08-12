import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPoleUnitPrimeCellWallFreezing

/-!
# Boundary-layer conjugacy of the Route-P prime-cell cascade

P-G45 finds one transient peak in every interior thermal prime cell, while P-G46 finds a frozen
wall residue.  This module proves that these are not separate regimes.  In the scaling coordinate
`k = (r - 1) log T`, every interior cell is exactly a wall cell whose base odds flow by the
positive semigroup `q ↦ q exp(-k)`.

Thus finite boundary-layer transport never annihilates a positive prime cell.  Cold vacuum occurs
only when the running coordinate escapes to infinity; finite running coordinate retains a
strictly positive frozen residue.  On a literal source prime, this semigroup is exactly the slower
aperture exponent.
-/

open Filter Set Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Eccentricity at fixed boundary-layer coordinate `k = (r - 1) log T`. -/
def thermalBernoulliBoundaryLayerEccentricity (k T : ℝ) : ℝ :=
  1 + k / Real.log T

/-- Positive semigroup transporting base odds through the thermal boundary layer. -/
def thermalBernoulliRunningOdds (q k : ℝ) : ℝ :=
  q * Real.exp (-k)

theorem thermalBernoulliRunningOdds_zero (q : ℝ) :
    thermalBernoulliRunningOdds q 0 = q := by
  rw [thermalBernoulliRunningOdds]
  norm_num

theorem thermalBernoulliRunningOdds_add (q k₁ k₂ : ℝ) :
    thermalBernoulliRunningOdds q (k₁ + k₂) =
      thermalBernoulliRunningOdds (thermalBernoulliRunningOdds q k₁) k₂ := by
  rw [thermalBernoulliRunningOdds, thermalBernoulliRunningOdds,
    thermalBernoulliRunningOdds, neg_add, Real.exp_add]
  ring

theorem thermalBernoulliRunningOdds_pos {q k : ℝ} (hq : 0 < q) :
    0 < thermalBernoulliRunningOdds q k := by
  exact mul_pos hq (Real.exp_pos _)

/-- Boundary-layer eccentricity remains strictly inside the two-sided aperture for positive
running coordinate. -/
theorem one_lt_thermalBernoulliBoundaryLayerEccentricity
    {k T : ℝ} (hk : 0 < k) (hT : 1 < T) :
    1 < thermalBernoulliBoundaryLayerEccentricity k T := by
  rw [thermalBernoulliBoundaryLayerEccentricity]
  exact lt_add_of_pos_right _ (div_pos hk (Real.log_pos hT))

/-- Exact mass renormalization in the moving boundary layer. -/
theorem thermalBernoulliBoundaryLayerMass_eq
    {q k T : ℝ} (hT : 1 < T) :
    thermalBernoulliMidpointMass q
        (thermalBernoulliBoundaryLayerEccentricity k T) T =
      thermalBernoulliRunningOdds q k / T := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hlog0 : Real.log T ≠ 0 := (Real.log_pos hT).ne'
  rw [thermalBernoulliMidpointMass, thermalBernoulliBoundaryLayerEccentricity,
    thermalBernoulliRunningOdds, Real.rpow_def_of_pos hT0]
  have hexponent : Real.log T * (-(1 + k / Real.log T)) = -k - Real.log T := by
    field_simp [hlog0]
    ring
  rw [hexponent, Real.exp_sub, Real.exp_log hT0]
  ring

/-- **Boundary-layer conjugacy.** Every moving interior cell is exactly a singular-wall cell with
running odds `q exp(-k)`. -/
theorem thermalBernoulliBoundaryLayerDefectOdds_eq_wall
    {q k T : ℝ} (hT : 1 < T) :
    thermalBernoulliMidpointDefectOdds q
        (thermalBernoulliBoundaryLayerEccentricity k T) T =
      thermalBernoulliMidpointDefectOdds (thermalBernoulliRunningOdds q k) 1 T := by
  rw [thermalBernoulliMidpointDefectOdds, bernoulliMidpointDefectOdds,
    thermalBernoulliBoundaryLayerMass_eq hT,
    thermalBernoulliMidpointDefectOdds_one (lt_trans zero_lt_one hT).ne']
  field_simp [(lt_trans zero_lt_one hT).ne']

/-- Finite boundary-layer coordinate freezes at the transported positive odds instead of reaching
the cold vacuum. -/
theorem tendsto_thermalBernoulliBoundaryLayerDefectOdds_atTop (q k : ℝ) :
    Tendsto
      (fun T => thermalBernoulliMidpointDefectOdds q
        (thermalBernoulliBoundaryLayerEccentricity k T) T)
      atTop (nhds (thermalBernoulliRunningOdds q k)) := by
  have heq : (fun T => thermalBernoulliMidpointDefectOdds q
      (thermalBernoulliBoundaryLayerEccentricity k T) T) =ᶠ[atTop]
      thermalBernoulliMidpointDefectOdds (thermalBernoulliRunningOdds q k) 1 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact thermalBernoulliBoundaryLayerDefectOdds_eq_wall hT
  exact (tendsto_thermalBernoulliMidpointDefectOdds_one_atTop
    (thermalBernoulliRunningOdds q k)).congr' heq.symm

/-- On a power thermal path, boundary-layer eccentricity is exactly the ratio of total to
oriented aperture. -/
theorem thermalBernoulliBoundaryLayerEccentricity_rpow
    {p x delta epsilon : ℝ} (hp : 1 < p) (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon) :
    thermalBernoulliBoundaryLayerEccentricity
        (x * epsilon * Real.log p) (p ^ (delta * epsilon)) =
      (x + delta) / delta := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hlogp : 0 < Real.log p := Real.log_pos hp
  rw [thermalBernoulliBoundaryLayerEccentricity, Real.log_rpow hp0]
  field_simp [hdelta.ne', hepsilon.ne', hlogp.ne']
  ring

/-- Literal prime odds under boundary transport become the slower aperture power. -/
theorem prime_boundaryLayer_effectiveOdds
    {p x epsilon : ℝ} (hp : 0 < p) :
    thermalBernoulliRunningOdds (p ^ (-1 : ℝ))
        (x * epsilon * Real.log p) =
      p ^ (-(1 + x * epsilon)) := by
  rw [thermalBernoulliRunningOdds, Real.rpow_def_of_pos hp,
    Real.rpow_def_of_pos hp, ← Real.exp_add]
  congr 1
  ring

/-- Exact source-cell renormalization law: an interior literal prime cell equals a wall cell whose
odds are set by the slower aperture. -/
theorem thermalBernoulliPrimeCell_eq_runningWall
    {p x delta epsilon : ℝ} (hp : 1 < p) (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon) :
    thermalBernoulliMidpointDefectOdds (p ^ (-1 : ℝ))
        ((x + delta) / delta) (p ^ (delta * epsilon)) =
      thermalBernoulliMidpointDefectOdds (p ^ (-(1 + x * epsilon))) 1
        (p ^ (delta * epsilon)) := by
  have hT : 1 < p ^ (delta * epsilon) :=
    Real.one_lt_rpow hp (mul_pos hdelta hepsilon)
  rw [← thermalBernoulliBoundaryLayerEccentricity_rpow hp hdelta hepsilon]
  rw [thermalBernoulliBoundaryLayerDefectOdds_eq_wall hT]
  rw [prime_boundaryLayer_effectiveOdds (lt_trans zero_lt_one hp)]

end

end RHTower.HedenmalmThetaSource
