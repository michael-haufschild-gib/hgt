import GaloisForLFunctions.RHTower.XiCTaylorAnisotropicSublinearGate
import GaloisForLFunctions.HTGeometry.LogarithmicResidueQuantization

/-!
# Exact anisotropic divisor charge and fixed-gauge screening

The anisotropic mesh does not merely amplify a hypothetical Xi zero at some unspecified positive
linear rate.  After retaining the horizontal mesh displacement, its scalar logarithmic current
converges to the exact local divisor order.  Superaccurate finite Xi Taylor sections inherit the
same charge.

A fixed centered meromorphic gauge subtracts exactly its integer local order.  In particular, an
analytic unit cannot screen any Xi divisor charge; exact screening requires a gauge with the same
local divisor multiplicity.
-/

open Complex Metric Filter Topology

namespace RHTower

noncomputable section

/-- Horizontal displacement of the right-approximating anisotropic mesh. -/
def xiTaylorAnisotropicHorizontalStep (sigma : ℂ) (n : ℕ) : ℝ :=
  (xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma).re

/-- The horizontal anisotropic step tends to zero. -/
theorem tendsto_xiTaylorAnisotropicHorizontalStep (sigma : ℂ) :
    Tendsto (xiTaylorAnisotropicHorizontalStep sigma) atTop (nhds 0) := by
  have hmesh : Tendsto
      (fun n : ℕ => xiTaylorAnisotropicRightApprox sigma (n + 1)) atTop
      (nhds sigma) :=
    (tendsto_xiTaylorAnisotropicRightApprox_succ sigma).mono_right
      nhdsWithin_le_nhds
  have hsub : Tendsto
      (fun n : ℕ => xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma)
      atTop (nhds 0) := by
    simpa using hmesh.sub_const sigma
  change Tendsto
    (fun n : ℕ =>
      (xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma).re)
    atTop (nhds 0)
  simpa [Function.comp_def] using
    Complex.continuous_re.continuousAt.tendsto.comp hsub

/-- **Anisotropic residue scalarization.** If a complex logarithmic response has normalized
residue `q` along the rational mesh, then its horizontal real current recovers the same real
residue exactly.  The `1/n²` vertical error is too small to contribute at the `1/n` pole scale. -/
theorem anisotropicHorizontalResidue_tendsto
    (sigma : ℂ) (L : ℕ → ℂ) (q : ℝ)
    (hresidue : Tendsto
      (fun n : ℕ =>
        (xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma) * L n)
      atTop (nhds (q : ℂ))) :
    Tendsto
      (fun n : ℕ => xiTaylorAnisotropicHorizontalStep sigma n * (L n).re)
      atTop (nhds q) := by
  let delta : ℕ → ℂ := fun n =>
    xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma
  let A : ℕ → ℂ := fun n => delta n * L n
  let C : ℝ := ‖(q : ℂ)‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hAnorm : Tendsto (fun n => ‖A n‖) atTop (nhds ‖(q : ℂ)‖) := by
    simpa [A, delta, Function.comp_def] using hresidue.norm
  have hAbound : ∀ᶠ n : ℕ in atTop, ‖A n‖ ≤ C := by
    have hev : ∀ᶠ n : ℕ in atTop, ‖A n‖ < C :=
      hAnorm.eventually (eventually_lt_nhds (by dsimp [C]; linarith))
    exact hev.mono fun _ hn => hn.le
  have herrorNorm : Tendsto
      (fun n : ℕ => |(delta n).im * (L n).im|) atTop (nhds 0) := by
    have hupper : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1)))
        atTop (nhds 0) := by
      simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) ?_ hupper
    filter_upwards [hAbound] with n hnA
    let N : ℕ := n + 1
    have hN : 0 < N := by dsimp [N]; omega
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hdeltaRe := xiTaylorAnisotropicRightApprox_re_sub_bounds sigma hN
    have hdeltaIm := abs_xiTaylorAnisotropicRightApprox_im_sub_lt sigma hN
    have hdelta0 : delta n ≠ 0 := by
      apply ne_of_apply_ne Complex.re
      have hsmall : (0 : ℝ) < 1 / (N : ℝ) := by positivity
      have hpos : 0 < (delta n).re := lt_of_lt_of_le hsmall
        (by simpa only [delta, N] using hdeltaRe.1)
      exact ne_of_gt hpos
    have hinv : ‖(delta n)⁻¹‖ ≤ (N : ℝ) := by
      apply norm_inv_le_nat_of_inv_nat_le_re hN
      simpa only [delta, N] using hdeltaRe.1
    have hL : L n = (delta n)⁻¹ * A n := by
      dsimp only [A]
      field_simp
    have hLnorm : ‖L n‖ ≤ (N : ℝ) * C := by
      rw [hL, norm_mul]
      exact mul_le_mul hinv hnA (norm_nonneg _) (by positivity)
    have hprod : |(delta n).im * (L n).im| ≤ C * (1 / (N : ℝ)) := by
      calc
        |(delta n).im * (L n).im| = |(delta n).im| * |(L n).im| :=
          abs_mul _ _
        _ ≤ |(delta n).im| * ‖L n‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg _)
        _ ≤ (1 / (N : ℝ) ^ (2 : ℕ)) * ((N : ℝ) * C) :=
          mul_le_mul hdeltaIm.le hLnorm (norm_nonneg _) (by positivity)
        _ = C * (1 / (N : ℝ)) := by field_simp
    simpa only [N, Nat.cast_add, Nat.cast_one] using hprod
  have herror : Tendsto
      (fun n : ℕ => (delta n).im * (L n).im) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using herrorNorm
  have hreal : Tendsto (fun n => (A n).re) atTop (nhds q) := by
    have hcomplex : Tendsto A atTop (nhds (q : ℂ)) := by
      simpa [A, delta] using hresidue
    change Tendsto (Complex.re ∘ A) atTop (nhds q)
    simpa using
      Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  have htarget := hreal.add herror
  convert htarget using 1
  · funext n
    dsimp only [A, delta, xiTaylorAnisotropicHorizontalStep]
    rw [mul_re]
    ring
  · ring

/-- Centered-coordinate version of anisotropic residue scalarization.  Multiplication by `-i`
rotates the horizontal Xi displacement into the oriented imaginary logarithmic current. -/
theorem centeredAnisotropicHorizontalResidue_tendsto
    (sigma : ℂ) (L : ℕ → ℂ) (q : ℝ)
    (hresidue : Tendsto
      (fun n : ℕ =>
        (xiCTaylorAnisotropicCenteredPoint sigma n -
            xiCTaylorCenteredPoint sigma) * L n)
      atTop (nhds (q : ℂ))) :
    Tendsto
      (fun n : ℕ => xiTaylorAnisotropicHorizontalStep sigma n * (L n).im)
      atTop (nhds q) := by
  have hcoord (n : ℕ) :
      xiCTaylorAnisotropicCenteredPoint sigma n - xiCTaylorCenteredPoint sigma =
        (xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma) * (-I) := by
    simp only [xiCTaylorAnisotropicCenteredPoint, xiCTaylorCenteredPoint]
    ring
  have hrot : Tendsto
      (fun n : ℕ =>
        (xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma) *
          ((-I) * L n))
      atTop (nhds (q : ℂ)) := by
    convert hresidue using 1
    funext n
    rw [hcoord]
    ring
  have h := anisotropicHorizontalResidue_tendsto sigma (fun n => (-I) * L n) q hrot
  have hpoint (n : ℕ) : ((-I) * L n).re = (L n).im := by
    rw [mul_re]
    simp
  simpa only [hpoint] using h

/-- Exact horizontal scalar charge of the Xi logarithmic derivative on the anisotropic mesh. -/
theorem xi_logDeriv_anisotropicHorizontalCharge_tendsto (sigma : ℂ) :
    Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          (logDeriv xi
            (xiTaylorAnisotropicRightApprox sigma (n + 1))).re)
      atTop (nhds ((analyticOrderAt xi sigma).toNat : ℝ)) := by
  exact anisotropicHorizontalResidue_tendsto sigma
    (fun n => logDeriv xi (xiTaylorAnisotropicRightApprox sigma (n + 1)))
    ((analyticOrderAt xi sigma).toNat : ℝ)
    (by simpa using xi_normalizedLogDeriv_anisotropicMesh_tendsto sigma)

/-- Every superaccurate finite Xi Taylor schedule recovers the exact horizontal divisor charge,
not merely a fixed positive fraction of it. -/
theorem xiCTaylor_logDeriv_anisotropicHorizontalCharge_tendsto
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N) (sigma : ℂ) :
    Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          (logDeriv
            (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n)).im)
      atTop (nhds ((analyticOrderAt xi sigma).toNat : ℝ)) := by
  have hbase := xi_logDeriv_anisotropicHorizontalCharge_tendsto sigma
  have htrackNorm := tendsto_norm_xiCTaylor_logDeriv_sub_XiC_at_anisotropic hN sigma
  have htrack : Tendsto
      (fun n : ℕ =>
        logDeriv
            (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n) -
          logDeriv XiC (xiCTaylorAnisotropicCenteredPoint sigma n))
      atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr htrackNorm
  have htrackIm : Tendsto
      (fun n : ℕ =>
        (logDeriv
            (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n) -
          logDeriv XiC (xiCTaylorAnisotropicCenteredPoint sigma n)).im)
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Complex.continuous_im.continuousAt.tendsto.comp htrack
  have hstep := tendsto_xiTaylorAnisotropicHorizontalStep sigma
  have herror := hstep.mul htrackIm
  have hbaseCentered : Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          (logDeriv XiC (xiCTaylorAnisotropicCenteredPoint sigma n)).im)
      atTop (nhds ((analyticOrderAt xi sigma).toNat : ℝ)) := by
    convert hbase using 1
    funext n
    have hcoord :
        1 / 2 + xiCTaylorAnisotropicCenteredPoint sigma n * I =
          xiTaylorAnisotropicRightApprox sigma (n + 1) := by
      simp only [xiCTaylorAnisotropicCenteredPoint,
        half_add_xiCTaylorCenteredPoint_mul_I]
    rw [RHTower.logDeriv_XiC_eq_mul_I_logDeriv_xi, hcoord]
    simp
  have hsum := hbaseCentered.add herror
  convert hsum using 1
  · funext n
    rw [sub_im]
    ring
  · ring

/-- The centered anisotropic points approach the target through its punctured neighborhood. -/
theorem tendsto_xiCTaylorAnisotropicCenteredPoint_punctured (sigma : ℂ) :
    Tendsto (xiCTaylorAnisotropicCenteredPoint sigma) atTop
      (nhdsWithin (xiCTaylorCenteredPoint sigma)
        ({xiCTaylorCenteredPoint sigma}ᶜ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_xiCTaylorAnisotropicCenteredPoint sigma, ?_⟩
  exact Eventually.of_forall fun n => by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcenter
    have hs := congrArg (fun z : ℂ => 1 / 2 + z * I) hcenter
    simp only [xiCTaylorAnisotropicCenteredPoint,
      half_add_xiCTaylorCenteredPoint_mul_I] at hs
    have hre := (xiTaylorAnisotropicRightApprox_re_sub_bounds sigma
      (show 0 < n + 1 by omega)).1
    rw [hs, sub_self, zero_re] at hre
    exact (not_le_of_gt (by positivity :
      (0 : ℝ) < 1 / (((n + 1 : ℕ) : ℝ)))) hre

/-- A fixed centered meromorphic gauge contributes exactly its integer local order to the
anisotropic horizontal current. -/
theorem meromorphicGauge_logDeriv_anisotropicHorizontalCharge_tendsto
    (G : ℂ → ℂ) (sigma : ℂ) (ell : ℤ)
    (hG : MeromorphicAt G (xiCTaylorCenteredPoint sigma))
    (horder : meromorphicOrderAt G (xiCTaylorCenteredPoint sigma) = ell) :
    Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          (logDeriv G (xiCTaylorAnisotropicCenteredPoint sigma n)).im)
      atTop (nhds (ell : ℝ)) := by
  have hresidue :=
    (GaloisForLFunctions.HTGeometry.logDeriv_residue_of_meromorphicOrder hG horder).comp
      (tendsto_xiCTaylorAnisotropicCenteredPoint_punctured sigma)
  exact centeredAnisotropicHorizontalResidue_tendsto sigma
    (fun n => logDeriv G (xiCTaylorAnisotropicCenteredPoint sigma n))
    (ell : ℝ) (by simpa [Function.comp_def] using hresidue)

/-- **Fixed meromorphic gauge-screening law.** A gauge of local order `ell` subtracts exactly
`ell` from the finite Xi Taylor divisor charge. -/
theorem xiCTaylor_meromorphicGaugeTransferCharge_tendsto
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    (G : ℂ → ℂ) (sigma : ℂ) (ell : ℤ)
    (hG : MeromorphicAt G (xiCTaylorCenteredPoint sigma))
    (horder : meromorphicOrderAt G (xiCTaylorCenteredPoint sigma) = ell) :
    Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          ((logDeriv
              (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
              (xiCTaylorAnisotropicCenteredPoint sigma n)).im -
            (logDeriv G (xiCTaylorAnisotropicCenteredPoint sigma n)).im))
      atTop
      (nhds (((analyticOrderAt xi sigma).toNat : ℝ) - (ell : ℝ))) := by
  have hTaylor := xiCTaylor_logDeriv_anisotropicHorizontalCharge_tendsto hN sigma
  have hGauge := meromorphicGauge_logDeriv_anisotropicHorizontalCharge_tendsto
    G sigma ell hG horder
  convert hTaylor.sub hGauge using 1
  funext n
  ring

/-- Exact local screening means that the mesh-rescaled transferred current tends to zero. -/
def XiCTaylorMeromorphicGaugeChargeScreenedAt
    (N : ℕ → ℕ) (G : ℂ → ℂ) (sigma : ℂ) : Prop :=
  Tendsto
    (fun n : ℕ =>
      xiTaylorAnisotropicHorizontalStep sigma n *
        ((logDeriv
            (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n)).im -
          (logDeriv G (xiCTaylorAnisotropicCenteredPoint sigma n)).im))
    atTop (nhds 0)

/-- **Sharp fixed-gauge screening classification.** A fixed meromorphic germ screens the finite
Xi Taylor charge exactly if and only if its integer local order equals the Xi multiplicity. -/
theorem xiCTaylor_meromorphicGaugeChargeScreenedAt_iff_order_eq
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    (G : ℂ → ℂ) (sigma : ℂ) (ell : ℤ)
    (hG : MeromorphicAt G (xiCTaylorCenteredPoint sigma))
    (horder : meromorphicOrderAt G (xiCTaylorCenteredPoint sigma) = ell) :
    XiCTaylorMeromorphicGaugeChargeScreenedAt N G sigma ↔
      ell = ((analyticOrderAt xi sigma).toNat : ℤ) := by
  have hlimit := xiCTaylor_meromorphicGaugeTransferCharge_tendsto
    hN G sigma ell hG horder
  constructor
  · intro hscreen
    have heq :
        (((analyticOrderAt xi sigma).toNat : ℝ) - (ell : ℝ)) = 0 :=
      tendsto_nhds_unique hlimit hscreen
    exact_mod_cast (show (ell : ℝ) = ((analyticOrderAt xi sigma).toNat : ℝ) by
      linarith)
  · intro heq
    simpa only [XiCTaylorMeromorphicGaugeChargeScreenedAt, heq, Int.cast_natCast,
      sub_self] using hlimit

/-- Analytic units preserve the full finite Xi Taylor divisor charge. -/
theorem xiCTaylor_analyticUnitGaugeTransferCharge_tendsto
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    (G : ℂ → ℂ) (sigma : ℂ)
    (hG : AnalyticAt ℂ G (xiCTaylorCenteredPoint sigma))
    (hG0 : G (xiCTaylorCenteredPoint sigma) ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          ((logDeriv
              (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
              (xiCTaylorAnisotropicCenteredPoint sigma n)).im -
            (logDeriv G (xiCTaylorAnisotropicCenteredPoint sigma n)).im))
      atTop (nhds ((analyticOrderAt xi sigma).toNat : ℝ)) := by
  have horder : meromorphicOrderAt G (xiCTaylorCenteredPoint sigma) = (0 : ℤ) := by
    rw [hG.meromorphicOrderAt_eq, hG.analyticOrderAt_eq_zero.mpr hG0]
    rfl
  simpa using xiCTaylor_meromorphicGaugeTransferCharge_tendsto hN G sigma 0
    hG.meromorphicAt horder

end

end RHTower
