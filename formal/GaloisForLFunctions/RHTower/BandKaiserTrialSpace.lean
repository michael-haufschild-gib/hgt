import GaloisForLFunctions.RHTower.BandKaiserComplexTrial
import GaloisForLFunctions.RHTower.ConstrainedProlateTrueLeakage
import GaloisForLFunctions.RHTower.ConstrainedProlateSpectralIdentification
import GaloisForLFunctions.RHTower.ProlateSignedLeakageOrdering

/-!
# Conditioned Kaiser trial spaces for the true prolate operator

The physical Kaiser packet synthesis is eventually injective at every fixed depth.  Its range is
therefore an explicit finite-dimensional complex trial space of the required dimension.  Combining
that dimension statement with the uniform packet defect estimate and the true Courant--Fischer
interface gives an unconditional exponential upper bound for every fixed true prolate leakage.
-/

open MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

/-- Range of the physical conditioned Kaiser synthesis at fixed packet depth. -/
def kaiserPhysicalTrialSpace (m : ℕ) (a : ℝ) (ha : 0 < a) :
    Submodule ℂ evenSubspace :=
  LinearMap.range (kaiserPhysicalGridSynthesis (m := m) a ha)

/-- Injective synthesis gives the packet range its exact coordinate dimension. -/
theorem finrank_kaiserPhysicalTrialSpace {m : ℕ} {a : ℝ} (ha : 0 < a)
    (hinj : Function.Injective (kaiserPhysicalGridSynthesis (m := m) a ha)) :
    Module.finrank ℂ (kaiserPhysicalTrialSpace m a ha) = m := by
  have hfin := (LinearEquiv.ofInjective
    (kaiserPhysicalGridSynthesis (m := m) a ha) hinj).finrank_eq
  rw [Module.finrank_fin_fun] at hfin
  exact hfin.symm

/-- At every fixed positive packet depth, all three explicit conditioning inequalities required by
the Kaiser energy estimate hold eventually in physical aperture. -/
theorem eventually_kaiserPhysicalGridSynthesis_injective {m : ℕ} (hm : 0 < m) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      Function.Injective (kaiserPhysicalGridSynthesis (m := m) a ha) := by
  have hc : ∀ᶠ a : ℝ in atTop, 1 ≤ 2 * Real.pi * a ^ 2 :=
    tendsto_two_pi_mul_sq_atTop.eventually_ge_atTop 1
  have hsqrt : Tendsto (fun a : ℝ => Real.sqrt (2 * Real.pi * a ^ 2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_two_pi_mul_sq_atTop
  have hscale : ∀ᶠ a : ℝ in atTop,
      8 * (m : ℝ) ^ 2 ≤ Real.sqrt (2 * Real.pi * a ^ 2) :=
    hsqrt.eventually_ge_atTop (8 * (m : ℝ) ^ 2)
  have hsqrtDiv : Tendsto
      (fun a : ℝ => Real.sqrt (2 * Real.pi * a ^ 2) / 2) atTop atTop :=
    hsqrt.atTop_div_const (by norm_num)
  have hnegSqrt : Tendsto
      (fun a : ℝ => -(Real.sqrt (2 * Real.pi * a ^ 2) / 2)) atTop atBot := by
    simpa only [Function.comp_def] using Filter.tendsto_neg_atTop_atBot.comp hsqrtDiv
  have hexpSqrt : Tendsto
      (fun a : ℝ => Real.exp (-(Real.sqrt (2 * Real.pi * a ^ 2) / 2)))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hnegSqrt
  have hsmallTendsto : Tendsto
      (fun a : ℝ => 32 * (m : ℝ) *
        Real.exp (-(Real.sqrt (2 * Real.pi * a ^ 2) / 2))) atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hexpSqrt : Tendsto
      (fun a : ℝ => (32 * (m : ℝ)) *
        Real.exp (-(Real.sqrt (2 * Real.pi * a ^ 2) / 2))) atTop
      (nhds ((32 * (m : ℝ)) * 0))) using 1 <;> norm_num
  have hsmall : ∀ᶠ a : ℝ in atTop,
      32 * (m : ℝ) * Real.exp (-(Real.sqrt (2 * Real.pi * a ^ 2) / 2)) ≤ 1 :=
    ((tendsto_order.1 hsmallTendsto).2 1 (by norm_num)).mono fun _ h => h.le
  filter_upwards [hc, hscale, hsmall] with a hca hscalea hsmalla
  intro ha
  exact kaiserPhysicalGridSynthesis_injective hm ha hca hscalea hsmalla

/-- Exact dimension of the physical packet range, eventually at every fixed positive depth. -/
theorem eventually_finrank_kaiserPhysicalTrialSpace {m : ℕ} (hm : 0 < m) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      Module.finrank ℂ (kaiserPhysicalTrialSpace m a ha) = m := by
  filter_upwards [eventually_kaiserPhysicalGridSynthesis_injective hm] with a hinj
  intro ha
  exact finrank_kaiserPhysicalTrialSpace ha (hinj ha)

/-- Every fixed true even-prolate leakage has the full Kaiser exponential clock, up to an arbitrary
positive loss in the normalized exponent. -/
theorem eventually_evenProlateLeakageValue_le_kaiser {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop,
      evenProlateLeakageValue a n ≤
        Real.exp (-((2 - ε) * (2 * Real.pi * a ^ 2))) := by
  let m : ℕ := n + 1
  have hm : 0 < m := by simp [m]
  have hinj := eventually_kaiserPhysicalGridSynthesis_injective hm
  have hdefect := eventually_exp_mul_timeBand_defect_kaiserPhysicalGridComplex_le hm hε
  filter_upwards [hinj, hdefect, eventually_gt_atTop (0 : ℝ)] with a hinja hdefecta ha
  let V : Submodule ℂ evenSubspace := kaiserPhysicalTrialSpace m a ha
  have hdim : n < Module.finrank ℂ V := by
    rw [finrank_kaiserPhysicalTrialSpace ha (hinja ha)]
    simp [m]
  apply evenProlateLeakageValue_le_of_form_trial a n V hdim
  intro f hf
  rcases hf with ⟨z, rfl⟩
  rw [kaiserPhysicalGridSynthesis_apply]
  let q : ℝ := Real.exp ((2 - ε) * (2 * Real.pi * a ^ 2))
  let δ : ℝ := Real.exp (-((2 - ε) * (2 * Real.pi * a ^ 2)))
  have hq : 0 < q := Real.exp_pos _
  have hqδ : q * δ = 1 := by
    rw [← Real.exp_add]
    simp [q, δ]
  have hpacket := hdefecta ha z
  change (1 - δ) * ‖kaiserPhysicalGridComplex a ha z‖ ^ 2 ≤
    ‖evenTimeBandFourier a (kaiserPhysicalGridComplex a ha z)‖ ^ 2
  have hmul : q * ((1 - δ) * ‖kaiserPhysicalGridComplex a ha z‖ ^ 2) ≤
      q * ‖evenTimeBandFourier a (kaiserPhysicalGridComplex a ha z)‖ ^ 2 := by
    calc
    q * ((1 - δ) * ‖kaiserPhysicalGridComplex a ha z‖ ^ 2) =
        q * ‖kaiserPhysicalGridComplex a ha z‖ ^ 2 -
          (q * δ) * ‖kaiserPhysicalGridComplex a ha z‖ ^ 2 := by ring
    _ = q * ‖kaiserPhysicalGridComplex a ha z‖ ^ 2 -
          ‖kaiserPhysicalGridComplex a ha z‖ ^ 2 := by rw [hqδ, one_mul]
    _ ≤ q * ‖evenTimeBandFourier a
          (kaiserPhysicalGridComplex a ha z)‖ ^ 2 := by
      change q *
          (‖kaiserPhysicalGridComplex a ha z‖ ^ 2 -
            ‖evenTimeBandFourier a (kaiserPhysicalGridComplex a ha z)‖ ^ 2) ≤
        ‖kaiserPhysicalGridComplex a ha z‖ ^ 2 at hpacket
      linarith
  nlinarith

/-- Closed fixed-index corollary: true even-prolate leakage is eventually at most
`exp (-2 pi a²)`, with no assumptions or supplied data. -/
theorem eventually_evenProlateLeakageValue_le_exp_neg_two_pi_sq (n : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      evenProlateLeakageValue a n ≤ Real.exp (-(2 * Real.pi * a ^ 2)) := by
  filter_upwards [eventually_evenProlateLeakageValue_le_kaiser (n := n)
    (ε := 1) zero_lt_one] with a ha
  convert ha using 1 <;> ring

/-- The same closed exponential bound for the actual signed greedy prolate leakage. -/
theorem eventually_evenProlateSignedLeakage_le_exp_neg_two_pi_sq (n : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      evenProlateSignedLeakage a n ≤ Real.exp (-(2 * Real.pi * a ^ 2)) := by
  filter_upwards [eventually_evenProlateLeakageValue_le_exp_neg_two_pi_sq n,
    eventually_gt_atTop (0 : ℝ)] with a hle ha
  rw [evenProlateSignedLeakage,
    ← evenProlateLeakageValue_eq_signedValue_leakage a ha n]
  exact hle

end RHTower

end
