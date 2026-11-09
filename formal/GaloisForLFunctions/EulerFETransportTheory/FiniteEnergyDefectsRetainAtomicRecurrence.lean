import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyTentErrorsVanish
import GaloisForLFunctions.ExactEventTheory.TentRecurrenceOfIntegrableDefects

/-!
# Atomic recurrence survives every finite-energy defect

The actual tent identity, decay of translated errors, and the discrete mass floor
force the same nonlinear recurrence law as in the integrable-defect class.
Small tents in the unit gap then have exactly zero boundary pairing.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.HamburgerStability
open GaloisForLFunctions.ExactEventTheory

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- The physical atomic tent decomposes into its recurrent part and canonical boundary error. -/
theorem beurling_finiteEnergy_tent_identity (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h y : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hy : h < y) :
    tentAtomMass B.intNorm h y = tentRecurrentPart B.intNorm β h y +
      finiteEnergyTentError (hg.toLp g) h (y / h) := by
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp
    (integrable_rpow_beurlingSystemIntegerMeasure B hBsum)
  have hn : 1 < y / h := (lt_div_iff₀ hh).mpr (by simpa only [one_mul] using hy)
  have hid := tent_boundary_identity_of_finite_energy_defect hsupp hmom hgm hgb hg hθ hh hh1 hn
  have he (u : ℝ) : 2 * Real.pi * (h * u) * (y / h) = 2 * Real.pi * u * y := by
    field_simp
  simp only [integral_beurlingSystemIntegerMeasure_eq_tsum, he] at hid
  rw [tentRecurrentPart_eq B.intNorm_pos (summable_beurling_inv_sq B hBsum) hh]
  dsimp only [tentAtomMass]
  linarith only [hid]

theorem tendsto_physicalFiniteEnergyTentError (g : DefectL2) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun y : ℝ => finiteEnergyTentError g h (y / h)) atTop (𝓝 0) := by
  have ht : Tendsto (fun y : ℝ => y / h) atTop atTop := by
    refine tendsto_atTop.mpr fun b => eventually_atTop.mpr ⟨b * h, fun y hy => ?_⟩
    exact (le_div_iff₀ hh).mpr hy
  exact (tendsto_finiteEnergyTentError_atTop g hh).comp ht

/-- The FE and the atom floor impose a nonlinear relation between two recurrent widths.
Finite energy itself supplies both decay conditions; none is assumed separately. -/
theorem beurling_finiteEnergy_tentRecurrentPart_half_eq_zero
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h y : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hy : tentRecurrentPart B.intNorm β h y < 1 / 4) :
    tentRecurrentPart B.intNorm β (h / 2) y = 0 := by
  have hsum := summable_beurling_inv_sq B hBsum
  have hh2 : 0 < h / 2 := half_pos hh
  apply recurrent_threshold_of_decaying_errors
    (continuous_tentRecurrentPart B.intNorm_pos hsum hh β)
    (isBohrAlmostPeriodic_tentRecurrentPart B.intNorm_pos hsum hh β)
    (continuous_tentRecurrentPart B.intNorm_pos hsum hh2 β)
    (isBohrAlmostPeriodic_tentRecurrentPart B.intNorm_pos hsum hh2 β)
    (tendsto_physicalFiniteEnergyTentError (hg.toLp g) hh)
    (tendsto_physicalFiniteEnergyTentError (hg.toLp g) hh2) ?_ hy
  refine eventually_atTop.mpr ⟨h + 1, fun x hx => ?_⟩
  rw [← beurling_finiteEnergy_tent_identity B hBsum hgm hgb hg hθ hh hh1
      (by linarith only [hx]),
    ← beurling_finiteEnergy_tent_identity B hBsum hgm hgb hg hθ hh2
      (by linarith only [hh1, hh]) (by linarith only [hx, hh])]
  exact tentAtomMass_half_eq_zero_of_lt B.intNorm_pos hsum hh

/-- Every point of the positive unit gap has arbitrarily small tents whose canonical
boundary pairing is exactly zero. This conclusion requires no pointwise trace. -/
theorem beurling_finiteEnergyTentError_eventually_zero_on_unit_gap
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), finiteEnergyTentError (hg.toLp g) (h / 2) (y / (h / 2)) = 0 := by
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      |finiteEnergyTentError (hg.toLp g) h (y / h)| < 1 / 4 := by
    simpa only [Real.norm_eq_abs] using
      (tendsto_zero_iff_norm_tendsto_zero.mp
        (tendsto_finiteEnergyTentError_smallWidth (hg.toLp g) (fun h => y / h))).eventually
          (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hw : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 (min y (min (1 - y) 1)) :=
    Ioo_mem_nhdsGT (lt_min hy0 (lt_min (sub_pos.mpr hy1) zero_lt_one))
  filter_upwards [hw, hsmall] with h hh he
  have hhy : h < y := (lt_min_iff.mp hh.2).1
  have hh1 : h ≤ 1 := (lt_min_iff.mp (lt_min_iff.mp hh.2).2).2.le
  have hgap : y + h ≤ 1 := by
    have hhgap := (lt_min_iff.mp (lt_min_iff.mp hh.2).2).1
    linarith only [hhgap]
  have hid := beurling_finiteEnergy_tent_identity B hBsum hgm hgb hg hθ hh.1 hh1 hhy
  rw [tentAtomMass_eq_zero_in_unit_gap B.one_le_intNorm hh.1 hgap] at hid
  have hP : tentRecurrentPart B.intNorm β h y < 1 / 4 := by
    have hb := (abs_lt.mp he).1
    linarith only [hid, hb]
  have hQ := beurling_finiteEnergy_tentRecurrentPart_half_eq_zero B hBsum hgm hgb hg hθ
    hh.1 hh1 hP
  have hh2 : 0 < h / 2 := half_pos hh.1
  have hid2 := beurling_finiteEnergy_tent_identity B hBsum hgm hgb hg hθ (y := y) hh2
    (by linarith only [hh1, hh.1]) (by linarith only [hhy, hh.1])
  rw [tentAtomMass_eq_zero_in_unit_gap B.one_le_intNorm hh2 (by linarith only [hgap, hh.1]),
    hQ, zero_add] at hid2
  exact hid2.symm

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_finiteEnergy_tent_identity
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_finiteEnergy_tentRecurrentPart_half_eq_zero
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_finiteEnergyTentError_eventually_zero_on_unit_gap
