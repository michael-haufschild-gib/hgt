import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceWork
import GaloisForLFunctions.RHTower.XiShiftedArcsineVacuumRenormalizedSourceLaw
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Source-clock quadratic concentration at shifted-Xi strict frontiers

The positive strict-frontier terminal source channel is not only a residue: its derivative is the
intrinsic source clock.  A contact of order `d` makes that clock speed of order `d - 1`, while the
fully arcsine-centered Christoffel source wall has order `-d`.  Their product with the wall square
therefore has the universal nonintegrable power `u^(-d-1)`.

This supplies Route U's source-clock quadratic lower shadow.  It does not provide the missing
source-pure finite cofinal ceiling: a successful U/Q energy must dominate this local source-clock
energy before taking any cofinal limit.
-/

open Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- A literal source charge with contact order `d` and a wall with order `-d` carry infinite
quadratic energy.  Unlike the clock form below, this density is the terminal source charge
itself, so no differentiation or externally imposed time coordinate is involved. -/
theorem not_integrableOn_Ioo_sourceCharge_mul_sq_of_tendsto_div_pow_pos
    {charge wall : ℝ → ℝ} {d : ℕ} (hd : 0 < d) {C R : ℝ}
    (hC : 0 < C) (hR : 0 < R)
    (hcharge : Tendsto (fun u : ℝ => charge u / u ^ d) (𝓝[>] (0 : ℝ)) (𝓝 C))
    (hwall : Tendsto (fun u : ℝ => u ^ d * wall u) (𝓝[>] (0 : ℝ)) (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ¬ IntegrableOn (fun u : ℝ => charge u * wall u ^ 2) (Ioo 0 ε) := by
  have hchargeNear : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), C / 2 < charge u / u ^ d :=
    hcharge.eventually (eventually_gt_nhds (by linarith : C / 2 < C))
  have hwallNear : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), R / 2 < u ^ d * wall u :=
    hwall.eventually (eventually_gt_nhds (by linarith : R / 2 < R))
  obtain ⟨δC, hδC, hδCsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hchargeNear
  obtain ⟨δR, hδR, hδRsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hwallNear
  let t : ℝ := min ε (min δC (min δR 1))
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min hε (lt_min hδC (lt_min hδR zero_lt_one))
  have htε : t ≤ ε := min_le_left _ _
  have htδC : t ≤ δC := le_trans (min_le_right _ _) (min_le_left _ _)
  have htδR : t ≤ δR := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _))
  intro hint
  have hintT : IntegrableOn (fun u : ℝ => charge u * wall u ^ 2) (Ioo 0 t) :=
    hint.mono_set (Ioo_subset_Ioo le_rfl htε)
  have hmajor : IntegrableOn
      (fun u : ℝ => (C * R ^ 2 / 8) * (u ^ d)⁻¹) (Ioo 0 t) := by
    refine hintT.mono'
      ((measurable_const.mul ((measurable_id.pow_const d).inv)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have huC : u ∈ Ioo (0 : ℝ) δC := ⟨hu.1, lt_of_lt_of_le hu.2 htδC⟩
    have huR : u ∈ Ioo (0 : ℝ) δR := ⟨hu.1, lt_of_lt_of_le hu.2 htδR⟩
    have hc : C / 2 < charge u / u ^ d := hδCsub huC
    have hw : R / 2 < u ^ d * wall u := hδRsub huR
    have hpow : 0 < u ^ d := pow_pos hu.1 _
    have hchargePos : 0 < charge u := by
      rcases div_pos_iff.mp (lt_trans (by linarith : 0 < C / 2) hc) with hpos | hneg
      · exact hpos.1
      · exact False.elim (not_lt_of_ge hpow.le hneg.2)
    have hwallPos : 0 < wall u := by
      rcases mul_pos_iff.mp (lt_trans (by linarith : 0 < R / 2) hw) with hpos | hneg
      · exact hpos.2
      · exact False.elim (not_lt_of_ge hpow.le hneg.1)
    have hwallSq : R ^ 2 / 4 < (u ^ d * wall u) ^ 2 := by
      nlinarith [sq_nonneg (u ^ d * wall u - R / 2)]
    have hratioPos : 0 < charge u / u ^ d := div_pos hchargePos hpow
    have hCR : 0 < R ^ 2 / 4 := by positivity
    have hproduct : C * R ^ 2 / 8 <
        (charge u / u ^ d) * (u ^ d * wall u) ^ 2 := by
      calc
        C * R ^ 2 / 8 = (C / 2) * (R ^ 2 / 4) := by ring
        _ < (charge u / u ^ d) * (R ^ 2 / 4) :=
          mul_lt_mul_of_pos_right hc hCR
        _ < (charge u / u ^ d) * (u ^ d * wall u) ^ 2 :=
          mul_lt_mul_of_pos_left hwallSq hratioPos
    rw [Real.norm_eq_abs,
      abs_of_pos (mul_pos (by positivity) (inv_pos.mpr hpow))]
    apply le_of_lt
    calc
      C * R ^ 2 / 8 * (u ^ d)⁻¹ = (C * R ^ 2 / 8) / u ^ d := by
        exact (div_eq_mul_inv _ _).symm
      _ < ((charge u / u ^ d) * (u ^ d * wall u) ^ 2) / u ^ d :=
        (div_lt_div_iff_of_pos_right hpow).mpr hproduct
      _ = charge u * wall u ^ 2 := by
        field_simp [hpow.ne']
  have hscale : IntegrableOn (fun u : ℝ => (u ^ d)⁻¹) (Ioo 0 t) := by
    have h := hmajor.const_mul (8 / (C * R ^ 2))
    have hCR0 : C * R ^ 2 ≠ 0 := ne_of_gt (mul_pos hC (sq_pos_of_pos hR))
    have hfun : (fun u : ℝ => 8 / (C * R ^ 2) *
        (C * R ^ 2 / 8 * (u ^ d)⁻¹)) =
        (fun u : ℝ => (u ^ d)⁻¹) := by
      funext u
      field_simp [hCR0]
    rw [hfun] at h
    exact h
  have hrpow : IntegrableOn (fun u : ℝ => u ^ (-(d : ℕ) : ℝ)) (Ioo 0 t) := by
    refine hscale.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.rpow_neg (le_of_lt hu.1), Real.rpow_natCast]
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff ht] at hrpow
  norm_num at hrpow
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- A source clock with order `d - 1` and a wall with order `d` carry infinite quadratic
energy.  The density is intrinsic: it is the source-clock speed, not an imposed mass weight. -/
theorem not_integrableOn_Ioo_sourceClock_mul_sq_of_tendsto_div_pow_pos
    {clock wall : ℝ → ℝ} {d : ℕ} (hd : 0 < d) {C R : ℝ}
    (hC : 0 < C) (hR : 0 < R)
    (hclock : Tendsto (fun u : ℝ => clock u / u ^ (d - 1)) (𝓝[>] (0 : ℝ)) (𝓝 C))
    (hwall : Tendsto (fun u : ℝ => u ^ d * wall u) (𝓝[>] (0 : ℝ)) (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ¬ IntegrableOn (fun u : ℝ => clock u * wall u ^ 2) (Ioo 0 ε) := by
  have hclockNear : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), C / 2 < clock u / u ^ (d - 1) :=
    hclock.eventually (eventually_gt_nhds (by linarith : C / 2 < C))
  have hwallNear : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), R / 2 < u ^ d * wall u :=
    hwall.eventually (eventually_gt_nhds (by linarith : R / 2 < R))
  obtain ⟨δC, hδC, hδCsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hclockNear
  obtain ⟨δR, hδR, hδRsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hwallNear
  let t : ℝ := min ε (min δC (min δR 1))
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min hε (lt_min hδC (lt_min hδR zero_lt_one))
  have htε : t ≤ ε := min_le_left _ _
  have htδC : t ≤ δC := le_trans (min_le_right _ _) (min_le_left _ _)
  have htδR : t ≤ δR := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _))
  intro hint
  have hintT : IntegrableOn (fun u : ℝ => clock u * wall u ^ 2) (Ioo 0 t) :=
    hint.mono_set (Ioo_subset_Ioo le_rfl htε)
  have hmajor : IntegrableOn
      (fun u : ℝ => (C * R ^ 2 / 8) * (u ^ (d + 1))⁻¹) (Ioo 0 t) := by
    refine hintT.mono'
      ((measurable_const.mul ((measurable_id.pow_const (d + 1)).inv)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have huC : u ∈ Ioo (0 : ℝ) δC := ⟨hu.1, lt_of_lt_of_le hu.2 htδC⟩
    have huR : u ∈ Ioo (0 : ℝ) δR := ⟨hu.1, lt_of_lt_of_le hu.2 htδR⟩
    have hc : C / 2 < clock u / u ^ (d - 1) := hδCsub huC
    have hw : R / 2 < u ^ d * wall u := hδRsub huR
    have hpowClock : 0 < u ^ (d - 1) := pow_pos hu.1 _
    have hpowWall : 0 < u ^ d := pow_pos hu.1 _
    have hclockPos : 0 < clock u := by
      rcases div_pos_iff.mp (lt_trans (by linarith : 0 < C / 2) hc) with hpos | hneg
      · exact hpos.1
      · exact False.elim (not_lt_of_ge hpowClock.le hneg.2)
    have hwallPos : 0 < wall u := by
      rcases mul_pos_iff.mp (lt_trans (by linarith : 0 < R / 2) hw) with hpos | hneg
      · exact hpos.2
      · exact False.elim (not_lt_of_ge hpowWall.le hneg.1)
    have hwallSq : R ^ 2 / 4 < (u ^ d * wall u) ^ 2 := by
      nlinarith [sq_nonneg (u ^ d * wall u - R / 2)]
    have hratioPos : 0 < clock u / u ^ (d - 1) := div_pos hclockPos hpowClock
    have hCR : 0 < R ^ 2 / 4 := by positivity
    have hproduct : C * R ^ 2 / 8 <
        (clock u / u ^ (d - 1)) * (u ^ d * wall u) ^ 2 := by
      calc
        C * R ^ 2 / 8 = (C / 2) * (R ^ 2 / 4) := by ring
        _ < (clock u / u ^ (d - 1)) * (R ^ 2 / 4) :=
          mul_lt_mul_of_pos_right hc hCR
        _ < (clock u / u ^ (d - 1)) * (u ^ d * wall u) ^ 2 :=
          mul_lt_mul_of_pos_left hwallSq hratioPos
    have hpowd1 : 0 < u ^ (d + 1) := pow_pos hu.1 _
    rw [Real.norm_eq_abs,
      abs_of_pos (mul_pos (by positivity) (inv_pos.mpr hpowd1))]
    apply le_of_lt
    calc
      C * R ^ 2 / 8 * (u ^ (d + 1))⁻¹ = (C * R ^ 2 / 8) / u ^ (d + 1) := by
        exact (div_eq_mul_inv _ _).symm
      _ < ((clock u / u ^ (d - 1)) * (u ^ d * wall u) ^ 2) / u ^ (d + 1) :=
        (div_lt_div_iff_of_pos_right hpowd1).mpr hproduct
      _ = clock u * wall u ^ 2 := by
        have hpowId : u ^ (d - 1) * u ^ (d + 1) = (u ^ d) ^ 2 := by
          calc
            u ^ (d - 1) * u ^ (d + 1) = u ^ ((d - 1) + (d + 1)) := (pow_add _ _ _).symm
            _ = u ^ (d + d) := by congr 1; omega
            _ = u ^ d * u ^ d := pow_add _ _ _
            _ = (u ^ d) ^ 2 := (pow_two _).symm
        field_simp [hpowClock.ne', hpowWall.ne', hpowd1.ne', hpowId]
        exact hpowId.symm
  have hscale : IntegrableOn (fun u : ℝ => (u ^ (d + 1))⁻¹) (Ioo 0 t) := by
    have h := hmajor.const_mul (8 / (C * R ^ 2))
    have hCR0 : C * R ^ 2 ≠ 0 := ne_of_gt (mul_pos hC (sq_pos_of_pos hR))
    have hfun : (fun u : ℝ => 8 / (C * R ^ 2) *
        (C * R ^ 2 / 8 * (u ^ (d + 1))⁻¹)) =
        (fun u : ℝ => (u ^ (d + 1))⁻¹) := by
      funext u
      field_simp [hCR0]
    rw [hfun] at h
    exact h
  have hrpow : IntegrableOn (fun u : ℝ => u ^ (-(d + 1 : ℕ) : ℝ)) (Ioo 0 t) := by
    refine hscale.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.rpow_neg (le_of_lt hu.1), Real.rpow_natCast]
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff ht] at hrpow
  norm_num [Nat.cast_add] at hrpow
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- **Source-clock Route-U quadratic concentration.**  At every occupied physical strict
frontier, literal terminal-source speed weighted by the square of the fully arcsine-centered
Christoffel source wall has infinite local energy.  The contact clock is generated by the literal
source terminal channel, so arbitrary finite contact order does not weaken this lower shadow. -/
theorem not_integrableOn_Ioo_terminalSourceClock_mul_sq_arcsineCenteredChristoffelWall
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d))
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n))
    {ε : ℝ} (hε : 0 < ε) :
    ¬ IntegrableOn (fun u : ℝ =>
      deriv (fun v =>
        XiShiftedCanonicalAdmission.xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceChargeAtMass
          v (n + 1))
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) *
      (xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall
          (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 1)) ^ 2)
      (Ioo 0 ε) := by
  apply not_integrableOn_Ioo_sourceClock_mul_sq_of_tendsto_div_pow_pos hd
    (XiShiftedCanonicalAdmission.xiShiftedStrictFrontierAdaptiveMixedTerminalSourceWorkResidue_pos
      hne hstrict hd hsigned)
    (xiShiftedStrictFrontierAllContactSourceWallResidue_pos hne hstrict hsigned)
  · exact XiShiftedCanonicalAdmission.tendsto_adaptiveMixedTerminalSourceWork_div_pow_pred_at_strictFrontierContact
      hne hstrict hphysical hd hzero hsource
  · exact tendsto_xiShiftedStrictFrontierAllContactScaledArcsineCenteredSourceWall
      hne hstrict hd hzero hsigned
  · exact hε

/-- **Literal-source Route-U quadratic concentration.**  At every occupied physical strict
frontier, the terminal charge itself, multiplied by the square of the fully arcsine-centered
Christoffel source wall, has infinite local energy.  This is a direct source-side lower shadow:
the source charge and wall already contain the exact cancelling contact orders. -/
theorem not_integrableOn_Ioo_terminalSourceCharge_mul_sq_arcsineCenteredChristoffelWall
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d))
    {ε : ℝ} (hε : 0 < ε) :
    ¬ IntegrableOn (fun u : ℝ =>
      XiShiftedCanonicalAdmission.xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceChargeAtMass
          (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 1) *
      (xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall
          (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 1)) ^ 2)
      (Ioo 0 ε) := by
  apply not_integrableOn_Ioo_sourceCharge_mul_sq_of_tendsto_div_pow_pos hd
    (XiShiftedCanonicalAdmission.xiShiftedStrictFrontierAdaptiveMixedTerminalSourceChargeResidue_pos
      hne hstrict hsigned)
    (xiShiftedStrictFrontierAllContactSourceWallResidue_pos hne hstrict hsigned)
  · simpa only [XiShiftedCanonicalAdmission.xiShiftedCanonicalAdmissionAdaptiveMixedTerminalSourceChargeAtMass] using
      XiShiftedCanonicalAdmission.tendsto_adaptiveMixedTerminalSourceCharge_div_pow_at_strictFrontierContact
        hne hstrict hphysical hd hzero
  · exact tendsto_xiShiftedStrictFrontierAllContactScaledArcsineCenteredSourceWall
      hne hstrict hd hzero hsigned
  · exact hε

end

end RHTower
