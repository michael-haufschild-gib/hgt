import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorWeightedZeroPacket

/-!
# Full Route T contour zero packet is negligible

The uniform density theorem controls real parts at least `7/10`.  This module closes the remaining
low strip of the common detector rectangle using the global `O(X log X)` Xi multiplicity bound.
The physical schedule `H=N^(701/1000)` leaves the exact residual power `X^(-1/299)` below the
density threshold.  Consequently both low and high pieces vanish, so the whole finite zero packet
crossed by the Route-T contour has normalized weight `o(1)`.
-/

open Complex Filter Metric Set ArithmeticFunction Finset Topology

namespace RHTower.Sieve

noncomputable section

/-- Common detector packet below the density threshold. -/
def inghamRouteTLowZeroPacket (X : ℕ) : Finset ℂ :=
  (inghamRouteTCommonZeroPacket X).filter (fun w => w.re < 7 / 10)

/-- Physical explicit-formula weight of the low detector packet. -/
def inghamRouteTLowZeroWeightedMass (X : ℕ) : ℝ :=
  ∑ w ∈ inghamRouteTLowZeroPacket X,
    (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
      inghamRouteTZeroMultiplicity w

/-- Physical weight of every zero in the common detector rectangle. -/
def inghamRouteTCommonZeroWeightedMass (X : ℕ) : ℝ :=
  ∑ w ∈ inghamRouteTCommonZeroPacket X,
    (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
      inghamRouteTZeroMultiplicity w

theorem inghamRouteTCommonZeroWeightedMass_eq_low_add_high (X : ℕ) :
    inghamRouteTCommonZeroWeightedMass X =
      inghamRouteTLowZeroWeightedMass X + inghamRouteTHighZeroWeightedMass X := by
  let f : ℂ → ℝ := fun w =>
    (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
      inghamRouteTZeroMultiplicity w
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := inghamRouteTCommonZeroPacket X) (p := fun w : ℂ => w.re < 7 / 10) f
  unfold inghamRouteTCommonZeroWeightedMass inghamRouteTLowZeroWeightedMass
    inghamRouteTLowZeroPacket inghamRouteTHighZeroWeightedMass inghamRouteTHighZeroPacket
  simpa only [f, not_lt] using hsplit.symm

/-- Every low-packet zero has at most the endpoint weight `X^(-300/299)`. -/
theorem inghamRouteTLowZeroWeightedMass_le_endpoint_mul_multiplicity
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTLowZeroWeightedMass X ≤
      (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * ((7 / 10 : ℝ) - 1)) *
        ∑ w ∈ inghamRouteTCommonZeroPacket X, inghamRouteTZeroMultiplicity w := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  let endpoint : ℝ :=
    (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * ((7 / 10 : ℝ) - 1))
  have hterm : ∀ w ∈ inghamRouteTLowZeroPacket X,
      (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
          inghamRouteTZeroMultiplicity w ≤
        endpoint * inghamRouteTZeroMultiplicity w := by
    intro w hw
    have hwlt : w.re < 7 / 10 := (Finset.mem_filter.mp hw).2
    have hexp : inghamRouteTPhysicalScaleExponent * (w.re - 1) ≤
        inghamRouteTPhysicalScaleExponent * ((7 / 10 : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) inghamRouteTPhysicalScaleExponent_pos.le
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hXR hexp)
      (inghamRouteTZeroMultiplicity_nonneg w)
  have hsum : inghamRouteTLowZeroWeightedMass X ≤
      ∑ w ∈ inghamRouteTLowZeroPacket X,
        endpoint * inghamRouteTZeroMultiplicity w := by
    unfold inghamRouteTLowZeroWeightedMass
    exact Finset.sum_le_sum fun w hw => hterm w hw
  have hsub : inghamRouteTLowZeroPacket X ⊆ inghamRouteTCommonZeroPacket X :=
    Finset.filter_subset _ _
  have hsumSub : (∑ w ∈ inghamRouteTLowZeroPacket X,
      inghamRouteTZeroMultiplicity w) ≤
      ∑ w ∈ inghamRouteTCommonZeroPacket X, inghamRouteTZeroMultiplicity w :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun w _ _ => inghamRouteTZeroMultiplicity_nonneg w)
  calc
    inghamRouteTLowZeroWeightedMass X ≤
        ∑ w ∈ inghamRouteTLowZeroPacket X,
          endpoint * inghamRouteTZeroMultiplicity w := hsum
    _ = endpoint * ∑ w ∈ inghamRouteTLowZeroPacket X,
          inghamRouteTZeroMultiplicity w := by rw [Finset.mul_sum]
    _ ≤ endpoint * ∑ w ∈ inghamRouteTCommonZeroPacket X,
          inghamRouteTZeroMultiplicity w :=
      mul_le_mul_of_nonneg_left hsumSub (Real.rpow_nonneg (zero_le_one.trans hXR) _)
    _ = _ := by rfl

/-- Global Xi counting gives the low detector packet a fixed-power majorant. -/
theorem exists_eventually_inghamRouteTLowZeroWeightedMass_le_global :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop,
        inghamRouteTLowZeroWeightedMass X ≤
          C * ((X : ℝ) + 2) * Real.log ((X : ℝ) + 3) *
            (X : ℝ) ^ (-(300 / 299 : ℝ)) := by
  obtain ⟨C, hC, hglobal⟩ :=
    exists_zetaResidueUnitClosedRectangleMultiplicity_le_global
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with X hX
  have hX1 : 1 ≤ X := by omega
  have hXR3 : (3 : ℝ) ≤ X := by exact_mod_cast hX
  have hc0 : 0 < inghamUniformGabrielCenter (7 / 10 : ℝ) := by
    unfold inghamUniformGabrielCenter
    norm_num
  have hc1 : inghamUniformGabrielCenter (7 / 10 : ℝ) ≤ 1 := by
    unfold inghamUniformGabrielCenter
    norm_num
  have hT : (1 : ℝ) ≤ (X : ℝ) - 2 := by linarith
  have hcount := hglobal hc0 hc1 hT
  have hcount' :
      (∑ w ∈ inghamRouteTCommonZeroPacket X, inghamRouteTZeroMultiplicity w) ≤
        C * ((X : ℝ) + 2) * Real.log ((X : ℝ) + 3) := by
    unfold inghamRouteTCommonZeroPacket inghamRouteTZeroMultiplicity
    convert hcount using 1 <;> norm_num <;> ring
  have hlow := inghamRouteTLowZeroWeightedMass_le_endpoint_mul_multiplicity hX1
  have hendpoint :
      (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * ((7 / 10 : ℝ) - 1)) =
        (X : ℝ) ^ (-(300 / 299 : ℝ)) := by
    congr 1
    unfold inghamRouteTPhysicalScaleExponent
    norm_num
  rw [hendpoint] at hlow
  have hweight0 : 0 ≤ (X : ℝ) ^ (-(300 / 299 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  calc
    inghamRouteTLowZeroWeightedMass X ≤
        (X : ℝ) ^ (-(300 / 299 : ℝ)) *
          ∑ w ∈ inghamRouteTCommonZeroPacket X,
            inghamRouteTZeroMultiplicity w := hlow
    _ ≤ (X : ℝ) ^ (-(300 / 299 : ℝ)) *
        (C * ((X : ℝ) + 2) * Real.log ((X : ℝ) + 3)) :=
      mul_le_mul_of_nonneg_left hcount' hweight0
    _ = C * ((X : ℝ) + 2) * Real.log ((X : ℝ) + 3) *
        (X : ℝ) ^ (-(300 / 299 : ℝ)) := by ring

theorem tendsto_nat_log_mul_rpow_neg_one_div_299_zero :
    Tendsto (fun X : ℕ =>
      Real.log (X : ℝ) * (X : ℝ) ^ (-(1 / 299 : ℝ))) atTop (𝓝 0) := by
  have hrealDiv : Tendsto (fun x : ℝ =>
      Real.log x / x ^ (1 / 299 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 299)).tendsto_div_nhds_zero
  have hreal : Tendsto (fun x : ℝ =>
      Real.log x * x ^ (-(1 / 299 : ℝ))) atTop (𝓝 0) := by
    apply hrealDiv.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx]
    rfl
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- The complete low detector packet is negligible; the `0.001` physical slack leaves the exact
fixed power `X^(-1/299)` after paying the global `O(X log X)` zero count. -/
theorem tendsto_inghamRouteTLowZeroWeightedMass_zero :
    Tendsto inghamRouteTLowZeroWeightedMass atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eventually_inghamRouteTLowZeroWeightedMass_le_global
  have hcore := tendsto_nat_log_mul_rpow_neg_one_div_299_zero
  have hupper : Tendsto (fun X : ℕ =>
      (4 * C) * (Real.log (X : ℝ) *
        (X : ℝ) ^ (-(1 / 299 : ℝ)))) atTop (𝓝 0) := by
    simpa using hcore.const_mul (4 * C)
  have hcompare : ∀ᶠ X : ℕ in atTop,
      inghamRouteTLowZeroWeightedMass X ≤
        (4 * C) * (Real.log (X : ℝ) *
          (X : ℝ) ^ (-(1 / 299 : ℝ))) := by
    filter_upwards [hbound, eventually_ge_atTop (3 : ℕ)] with X hboundX hX
    have hXR : (3 : ℝ) ≤ X := by exact_mod_cast hX
    have hXpos : (0 : ℝ) < X := by linarith
    have hXone : (1 : ℝ) ≤ X := by linarith
    have hlog0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hXone
    have hadd : (X : ℝ) + 2 ≤ 2 * X := by linarith
    have hquad : (X : ℝ) + 3 ≤ (X : ℝ) ^ (2 : ℕ) := by nlinarith
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (X : ℝ) + 3) hquad
    have hlogpow : Real.log ((X : ℝ) ^ (2 : ℕ)) = 2 * Real.log (X : ℝ) := by
      rw [Real.log_pow]
      norm_num
    rw [hlogpow] at hlog
    have hfac : ((X : ℝ) + 2) * Real.log ((X : ℝ) + 3) ≤
        4 * (X : ℝ) * Real.log (X : ℝ) := by
      calc
        ((X : ℝ) + 2) * Real.log ((X : ℝ) + 3) ≤
            (2 * (X : ℝ)) * (2 * Real.log (X : ℝ)) :=
          mul_le_mul hadd hlog (Real.log_nonneg (by linarith : (1 : ℝ) ≤ (X : ℝ) + 3))
            (by positivity)
        _ = 4 * (X : ℝ) * Real.log (X : ℝ) := by ring
    have hweight0 : 0 ≤ (X : ℝ) ^ (-(300 / 299 : ℝ)) :=
      Real.rpow_nonneg hXpos.le _
    have hfacC : C * (((X : ℝ) + 2) * Real.log ((X : ℝ) + 3)) ≤
        C * (4 * (X : ℝ) * Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_left hfac hC.le
    have hpowCollapse :
        (X : ℝ) * (X : ℝ) ^ (-(300 / 299 : ℝ)) =
          (X : ℝ) ^ (-(1 / 299 : ℝ)) := by
      calc
        (X : ℝ) * (X : ℝ) ^ (-(300 / 299 : ℝ)) =
            (X : ℝ) ^ (1 : ℝ) * (X : ℝ) ^ (-(300 / 299 : ℝ)) := by
          rw [Real.rpow_one]
        _ = (X : ℝ) ^ ((1 : ℝ) + -(300 / 299 : ℝ)) :=
          (Real.rpow_add hXpos _ _).symm
        _ = (X : ℝ) ^ (-(1 / 299 : ℝ)) := by
          congr 1
          norm_num
    calc
      inghamRouteTLowZeroWeightedMass X ≤
          C * ((X : ℝ) + 2) * Real.log ((X : ℝ) + 3) *
            (X : ℝ) ^ (-(300 / 299 : ℝ)) := hboundX
      _ = C * (((X : ℝ) + 2) * Real.log ((X : ℝ) + 3)) *
            (X : ℝ) ^ (-(300 / 299 : ℝ)) := by ring
      _ ≤ C * (4 * (X : ℝ) * Real.log (X : ℝ)) *
            (X : ℝ) ^ (-(300 / 299 : ℝ)) :=
        mul_le_mul_of_nonneg_right hfacC hweight0
      _ = (4 * C) * (Real.log (X : ℝ) *
          (X : ℝ) ^ (-(1 / 299 : ℝ))) := by
        rw [← hpowCollapse]
        ring
  refine squeeze_zero' ?_ hcompare hupper
  filter_upwards with X
  unfold inghamRouteTLowZeroWeightedMass
  apply Finset.sum_nonneg
  intro w hw
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (inghamRouteTZeroMultiplicity_nonneg w)

/-- **Every zero in the common Route-T detector rectangle has negligible normalized physical
weight at interval exponent `701/1000`.** -/
theorem tendsto_inghamRouteTCommonZeroWeightedMass_zero :
    Tendsto inghamRouteTCommonZeroWeightedMass atTop (𝓝 0) := by
  have hsum := tendsto_inghamRouteTLowZeroWeightedMass_zero.add
    tendsto_inghamRouteTHighZeroWeightedMass_zero
  have heq : (fun X => inghamRouteTLowZeroWeightedMass X +
      inghamRouteTHighZeroWeightedMass X) =ᶠ[atTop]
      inghamRouteTCommonZeroWeightedMass := by
    filter_upwards with X
    exact (inghamRouteTCommonZeroWeightedMass_eq_low_add_high X).symm
  simpa only [zero_add] using hsum.congr' heq

end

end RHTower.Sieve
