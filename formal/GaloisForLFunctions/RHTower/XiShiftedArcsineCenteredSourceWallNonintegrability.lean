import GaloisForLFunctions.RHTower.XiShiftedArcsineVacuumRenormalizedSourceLaw
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Strict-frontier nonintegrability of the arithmetic source wall

An exact positive contact residue of order `d ≥ 1` is not merely a pointwise blow-up certificate.
It forces the underlying source wall outside local `L¹` on every right neighborhood.  Full
arcsine-vacuum subtraction cannot remove this obstruction: bounded counterterms disappear under
positive contact scaling, so the centered arithmetic deviation has the same nonintegrable germ.

This is the source-first wall law needed by the mass-shifted spectral-face route.  Under false RH,
such nonintegrable centered arithmetic germs occur cofinally.  Consequently any independent global
admission theorem placing every fixed-degree centered wall in local `L¹` at its terminal boundary
would close the route immediately.
-/

open Filter Matrix Polynomial MeasureTheory Set Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- A positive finite order-`d` residue, with `d ≥ 1`, forces failure of local `L¹` on every
right neighborhood.  This formulation needs no regularity assumption on the unscaled function. -/
theorem not_integrableOn_Ioo_of_tendsto_natPow_mul_pos
    {f : ℝ → ℝ} {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (hlim : Tendsto (fun u : ℝ => u ^ d * f u) (𝓝[>] (0 : ℝ)) (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ¬ IntegrableOn f (Ioo 0 ε) := by
  have hnear : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), R / 2 < u ^ d * f u :=
    hlim.eventually (eventually_gt_nhds (by linarith : R / 2 < R))
  obtain ⟨δ, hδ, hδsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  let t : ℝ := min ε (min δ 1)
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min hε (lt_min hδ zero_lt_one)
  have htε : t ≤ ε := min_le_left _ _
  have htδ : t ≤ δ := le_trans (min_le_right _ _) (min_le_left _ _)
  have ht1 : t ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  intro hf
  have hft : IntegrableOn f (Ioo 0 t) :=
    hf.mono_set (Ioo_subset_Ioo le_rfl htε)
  have hc : IntegrableOn (fun u : ℝ => (R / 2) * u⁻¹) (Ioo 0 t) := by
    refine hft.mono' ((measurable_const.mul measurable_id.inv).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have huδ : u ∈ Ioo (0 : ℝ) δ := ⟨hu.1, lt_of_lt_of_le hu.2 htδ⟩
    have hcontact : R / 2 < u ^ d * f u := hδsub huδ
    have hpowpos : 0 < u ^ d := pow_pos hu.1 d
    have hfpos : 0 < f u := by
      by_contra hfnot
      have hfle : f u ≤ 0 := le_of_not_gt hfnot
      have hprodle : u ^ d * f u ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpowpos.le hfle
      linarith
    have hpw : u ^ d ≤ u :=
      pow_le_of_le_one hu.1.le (hu.2.le.trans ht1) (Nat.ne_of_gt hd)
    have hscaled : (R / 2) * u⁻¹ ≤ f u := by
      rw [← div_eq_mul_inv, div_le_iff₀ hu.1]
      exact le_trans hcontact.le (by
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hpw hfpos.le)
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (half_pos hR) (inv_pos.mpr hu.1))]
    exact hscaled
  have hinv : IntegrableOn (fun u : ℝ => u⁻¹) (Ioo 0 t) := by
    have hscaled := hc.const_mul (2 / R)
    have heq : (fun u : ℝ => 2 / R * (R / 2 * u⁻¹)) = (fun u : ℝ => u⁻¹) := by
      funext u
      field_simp
    rw [heq] at hscaled
    exact hscaled
  have hrpow : IntegrableOn (fun u : ℝ => u ^ (-1 : ℝ)) (Ioo 0 t) := by
    refine hinv.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.rpow_neg_one]
  exact (not_lt_of_ge le_rfl)
    ((intervalIntegral.integrableOn_Ioo_rpow_iff ht).mp hrpow)

/-- Actual adaptive mixed/completed arithmetic source quotient before reflection aggregation. -/
noncomputable def xiShiftedStrictFrontierAllContactArithmeticSourceWall
    (n : ℕ) (u : ℝ) : ℝ :=
  let v := xiShiftedHigherBlockTerminalFrontier (n + 1) + u
  xiShiftedAdaptiveMixedCompletedArithmeticSource (Real.sqrt v)
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence (Real.sqrt v)) (n + 1)) /
    (32 * xiShiftedCanonicalAdmissionNorm v (n + 2))

/-- Exact positive all-contact residue forces literal adaptive mixed/completed arithmetic source
quotient outside `L¹` on every right neighborhood of a physical strict frontier. -/
theorem not_integrableOn_Ioo_xiShiftedStrictFrontierAllContactArithmeticSourceWall
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
    ¬ IntegrableOn
        (xiShiftedStrictFrontierAllContactArithmeticSourceWall n)
        (Ioo 0 ε) := by
  have hlim := tendsto_xiShiftedStrictFrontierAllContactScaledArithmeticSourceWall
    hne hstrict hphysical hd hzero hsigned
  have hlim' : Tendsto
      (fun u : ℝ => u ^ d *
        xiShiftedStrictFrontierAllContactArithmeticSourceWall n u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierAllContactSourceWallResidue n d)) := by
    change Tendsto
      (fun u : ℝ => u ^ d *
        xiShiftedStrictFrontierAllContactArithmeticSourceWall n u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierAllContactSourceWallResidue n d)) at hlim
    exact hlim
  exact not_integrableOn_Ioo_of_tendsto_natPow_mul_pos hd
    (xiShiftedStrictFrontierAllContactSourceWallResidue_pos hne hstrict hsigned)
    hlim' hε

/-- Full arcsine-vacuum centering does not cure strict-frontier source nonintegrability. -/
theorem not_integrableOn_Ioo_xiShiftedStrictFrontierArcsineCenteredSourceWall
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d))
    {ε : ℝ} (hε : 0 < ε) :
    ¬ IntegrableOn
        (fun u : ℝ =>
          xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall
            (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 1))
        (Ioo 0 ε) := by
  have hlim := tendsto_xiShiftedStrictFrontierAllContactScaledArcsineCenteredSourceWall
    hne hstrict hd hzero hsigned
  exact not_integrableOn_Ioo_of_tendsto_natPow_mul_pos hd
    (xiShiftedStrictFrontierAllContactSourceWallResidue_pos hne hstrict hsigned)
    (by
      change Tendsto
        (fun u : ℝ => u ^ d *
          xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall
            (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 1))
        (𝓝[>] (0 : ℝ))
        (𝓝 (xiShiftedStrictFrontierAllContactSourceWallResidue n d)) at hlim
      exact hlim)
    hε

/-- **Cofinal centered-source singular phase.** False RH creates arbitrarily late strict frontiers
whose admission-sensitive, arcsine-centered arithmetic source wall is nonintegrable on every
right neighborhood. -/
theorem exists_cofinal_arcsineCenteredSourceWall_nonintegrable_of_not_riemannHypothesis
    (hnot : ¬RiemannHypothesis) (A : ℝ) :
    ∃ n d : ℕ,
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      0 < d ∧
      (∀ k < 2 * (n + 2) + d,
        xiShiftedStrictFrontierPadeDefect n k = 0) ∧
      0 < (-1 : ℝ) ^ d *
        xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d) ∧
      ∀ ε : ℝ, 0 < ε →
        ¬ IntegrableOn
            (fun u : ℝ =>
              xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall
                (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 1))
            (Ioo 0 ε) := by
  obtain ⟨n, hne, hA, hstrict, _hphysical, hlaw⟩ :=
    xiShiftedCofinalAllContactSourceWallResiduePhase_of_not_riemannHypothesis hnot A
  obtain ⟨d, hd, hzero, hsigned, _hresidue, _hlimit, _hsource⟩ := hlaw
  refine ⟨n, d, hA, hd, hzero, hsigned, fun ε hε => ?_⟩
  exact not_integrableOn_Ioo_xiShiftedStrictFrontierArcsineCenteredSourceWall
    hne hstrict hd hzero hsigned hε

end

end RHTower
