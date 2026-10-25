import GaloisForLFunctions.ArithmeticOrientationTheory.TheOffLineZerosObstructTheMoebiusReceiver
import Mathlib.Analysis.Analytic.Order
import GaloisForLFunctions.RHTower.DeckChargeInvariant
import GaloisForLFunctions.RHTower.ZetaOffLineWeightedDensity

/-!
# Paid kernels cover visible translated zero orders

The cleared analytic identity compares local vanishing orders. Paid Wiener
kernels supply all zero order left after translated zeta cancellation; their
corresponding interior jets vanish.
-/

section

noncomputable section
set_option autoImplicit false
open Filter Topology Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory
open TransHorizonIncidenceMechanics WienerAlgebraAt BezoutValuationIncidence

/-- Every paid kernel supplies the vanishing order left after cancellation of shifted zeta zeros. -/
theorem zeta_order_le_translated_order_add_kernel_order_of_repairs
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k : ℕ → ℝ} (hk : CriticalWiener k)
    (hB : ReceiverBounded (RHTower.dirichletConv k (pmPowerDampedRealWeight ε)))
    {ρ : ℂ} (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1) :
    analyticOrderAt riemannZeta ρ ≤
      analyticOrderAt riemannZeta (ρ - ε) +
        analyticOrderAt (LSeries (cplx k)) (ρ - ε) := by
  obtain ⟨Φ, hΦ, hclear⟩ := exists_cleared_continuation_of_repairs hε hε2 hk hB
  let s : ℂ := ρ - ε
  let m : ℂ := ((∑' d : ℕ, RHTower.dirichletConv k (pmPowerDampedRealWeight ε) d / d : ℝ) : ℂ)
  have hs : 1 / 2 < s.re := by dsimp [s]; linarith only [hρ]
  have hs1 : s.re < 1 := by dsimp [s]; linarith only [hρ1, hε]
  have hρne : ρ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [one_re] at this
    linarith
  have hsne : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [one_re] at this
    linarith
  have hζ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hsne
  have hK : AnalyticAt ℂ (LSeries (cplx k)) s := analyticOnNhd_lSeries_kernel hk s hs
  have hZ : AnalyticAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (z + ε)) s :=
    (RHTower.analyticAt_zetaResidueUnit (s + ε)).comp
      (f := fun z : ℂ => z + (ε : ℂ)) (analyticAt_id.add analyticAt_const)
  have hD : AnalyticAt ℂ (fun z : ℂ => z + ε - 1) s := by fun_prop
  have hF : AnalyticAt ℂ (fun z : ℂ => Φ z + m * riemannZeta z) s :=
    (hΦ s hs).add (analyticAt_const.mul hζ)
  have hU : {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} ∈ 𝓝 s :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨hs, hs1⟩
  have heq :
      (fun z : ℂ => RHTower.zetaResidueUnit (z + ε) * (Φ z + m * riemannZeta z))
        =ᶠ[𝓝 s] fun z : ℂ => (z + ε - 1) * (riemannZeta z * LSeries (cplx k) z) := by
    filter_upwards [hU] with z hz
    have h := hclear z hz.1 hz.2
    change RHTower.zetaResidueUnit (z + ε) * Φ z =
      (z + ε - 1) * riemannZeta z * LSeries (cplx k) z -
        m * riemannZeta z * RHTower.zetaResidueUnit (z + ε) at h
    calc
      _ = RHTower.zetaResidueUnit (z + ε) * Φ z +
          m * riemannZeta z * RHTower.zetaResidueUnit (z + ε) := by ring
      _ = _ := by rw [h]; ring
  have hord := analyticOrderAt_congr heq
  change analyticOrderAt ((fun z : ℂ => RHTower.zetaResidueUnit (z + ε)) *
    (fun z : ℂ => Φ z + m * riemannZeta z)) s =
      analyticOrderAt ((fun z : ℂ => z + ε - 1) *
        (riemannZeta * LSeries (cplx k))) s at hord
  rw [analyticOrderAt_mul hZ hF, analyticOrderAt_mul hD (hζ.mul hK),
    analyticOrderAt_mul hζ hK] at hord
  have hDzero : analyticOrderAt (fun z : ℂ => z + ε - 1) s = 0 := by
    apply hD.analyticOrderAt_eq_zero.mpr
    simpa only [s, sub_add_cancel, sub_ne_zero] using hρne
  have hZorder : analyticOrderAt (fun z : ℂ => RHTower.zetaResidueUnit (z + ε)) s =
      analyticOrderAt riemannZeta ρ := by
    rw [RHTower.analyticOrderAt_comp_add]
    dsimp only [s]
    rw [sub_add_cancel, RHTower.analyticOrderAt_zetaResidueUnit_eq_zeta hρne]
  rw [hDzero, zero_add, hZorder] at hord
  calc
    analyticOrderAt riemannZeta ρ ≤ analyticOrderAt riemannZeta ρ +
        analyticOrderAt (fun z : ℂ => Φ z + m * riemannZeta z) s := le_self_add
    _ = _ := hord

/-- Strictly greater denominator multiplicity forces every repairing kernel to vanish. -/
theorem lSeries_kernel_eq_zero_of_strict_order_loss
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k : ℕ → ℝ} (hk : CriticalWiener k)
    (hB : ReceiverBounded (RHTower.dirichletConv k (pmPowerDampedRealWeight ε)))
    {ρ : ℂ} (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1)
    (hloss : analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ) :
    LSeries (cplx k) (ρ - ε) = 0 := by
  by_contra hne
  have hs : 1 / 2 < (ρ - (ε : ℂ)).re := by
    simp only [sub_re, ofReal_re]
    linarith
  have hK := analyticOnNhd_lSeries_kernel hk (ρ - ε) hs
  have horder := zeta_order_le_translated_order_add_kernel_order_of_repairs hε hε2 hk hB hρ hρ1
  rw [hK.analyticOrderAt_eq_zero.mpr hne, add_zero] at horder
  exact hloss.not_ge horder


/-- The exact cancellation bound also holds for complex kernels in the actual paid ideal. -/
theorem zeta_order_le_translated_order_add_paid_kernel_order
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (k : WienerAlgebraAt (1 / 2))
    (hk : k ∈ paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε))
    {ρ : ℂ} (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1) :
    analyticOrderAt riemannZeta ρ ≤
      analyticOrderAt riemannZeta (ρ - ε) + analyticOrderAt (LSeries (⇑k.toFn)) (ρ - ε) := by
  rw [mem_paidIdeal] at hk
  have hs : 1 / 2 < (ρ - (ε : ℂ)).re := by simp only [sub_re, ofReal_re]; linarith
  have hr := zeta_order_le_translated_order_add_kernel_order_of_repairs hε hε2
    (criticalWiener_rePart k) hk.1 hρ hρ1
  have hi := zeta_order_le_translated_order_add_kernel_order_of_repairs hε hε2
    (criticalWiener_imPart k) hk.2 hρ hρ1
  have hia := analyticOnNhd_lSeries_kernel (criticalWiener_imPart k) (ρ - ε) hs
  have hI : AnalyticAt ℂ (fun _ : ℂ => I) (ρ - ε) := analyticAt_const
  have hIorder : analyticOrderAt ((fun _ : ℂ => I) * LSeries (cplx (imPart k)))
      (ρ - ε) = analyticOrderAt (LSeries (cplx (imPart k))) (ρ - ε) := by
    rw [analyticOrderAt_mul hI hia, hI.analyticOrderAt_eq_zero.mpr I_ne_zero, zero_add]
  have heq : LSeries (⇑k.toFn) =ᶠ[𝓝 (ρ - (ε : ℂ))]
      LSeries (cplx (rePart k)) + (fun _ : ℂ => I) * LSeries (cplx (imPart k)) := by
    have hU := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hU] with z hz
    exact lSeries_toFn_eq k hz.le
  have hmin := le_analyticOrderAt_add (f := LSeries (cplx (rePart k)))
    (g := (fun _ : ℂ => I) * LSeries (cplx (imPart k))) (z₀ := ρ - (ε : ℂ))
  rw [hIorder, ← analyticOrderAt_congr heq] at hmin
  rcases le_total (analyticOrderAt (LSeries (cplx (rePart k))) (ρ - (ε : ℂ)))
    (analyticOrderAt (LSeries (cplx (imPart k))) (ρ - (ε : ℂ))) with h | h
  · rw [min_eq_left h] at hmin
    exact hr.trans (add_le_add le_rfl hmin)
  · rw [min_eq_right h] at hmin
    exact hi.trans (add_le_add le_rfl hmin)

/-- The visible pole order subtracts numerator zeros from the shifted denominator order. -/
def visibleTranslatedZetaOrder (ε : ℝ) (ρ : ℂ) : ℕ∞ :=
  analyticOrderAt riemannZeta ρ - analyticOrderAt riemannZeta (ρ - ε)

/-- Every complex repairing kernel vanishes to at least the visible translated pole order. -/
theorem visibleTranslatedZetaOrder_le_paid_kernel_order
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (k : WienerAlgebraAt (1 / 2))
    (hk : k ∈ paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε))
    {ρ : ℂ} (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1) :
    visibleTranslatedZetaOrder ε ρ ≤ analyticOrderAt (LSeries (⇑k.toFn)) (ρ - ε) := by
  apply tsub_le_iff_right.mpr
  simpa only [add_comm] using
    zeta_order_le_translated_order_add_paid_kernel_order hε hε2 k hk hρ hρ1

/-- The visible pole multiplicity imposes all corresponding kernel jet conditions. -/
theorem paid_kernel_jets_vanish_below_visible_order
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (k : WienerAlgebraAt (1 / 2))
    (hk : k ∈ paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε))
    {ρ : ℂ} (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1)
    {N : ℕ} (hN : (N : ℕ∞) ≤ visibleTranslatedZetaOrder ε ρ) :
    ∀ i < N, iteratedDeriv i (LSeries (⇑k.toFn)) (ρ - ε) = 0 := by
  have hs : 1 / 2 < (ρ - (ε : ℂ)).re := by simp only [sub_re, ofReal_re]; linarith
  have hr := analyticOnNhd_lSeries_kernel (criticalWiener_rePart k) (ρ - ε) hs
  have hi := analyticOnNhd_lSeries_kernel (criticalWiener_imPart k) (ρ - ε) hs
  have heq : LSeries (⇑k.toFn) =ᶠ[𝓝 (ρ - (ε : ℂ))]
      (fun z => LSeries (cplx (rePart k)) z + I * LSeries (cplx (imPart k)) z) := by
    have hU := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hU] with z hz
    exact lSeries_toFn_eq k hz.le
  have hK : AnalyticAt ℂ (LSeries (⇑k.toFn)) (ρ - ε) :=
    (hr.add (analyticAt_const.mul hi)).congr heq.symm
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hK).mp
    (hN.trans (visibleTranslatedZetaOrder_le_paid_kernel_order hε hε2 k hk hρ hρ1))

/-- Partial cancellation still gives a Bohr obstruction whenever the shifted pole order stays positive. -/
theorem mem_obstructionHull_moebius_of_strict_order_loss
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {ρ : ℂ}
    (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1)
    (hloss : analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ) :
    halfPlanePoint (1 / 2) (ρ - ε) (by simp; linarith) ∈
      obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) := by
  intro k hk
  rw [mem_paidIdeal] at hk
  have hs : (1 / 2 : ℝ) ≤ (ρ - ε).re := by simp; linarith
  rw [bohrEval_halfPlanePoint, lSeries_toFn_eq k hs]
  rw [lSeries_kernel_eq_zero_of_strict_order_loss hε hε2 (criticalWiener_rePart k)
      hk.1 hρ hρ1 hloss,
    lSeries_kernel_eq_zero_of_strict_order_loss hε hε2 (criticalWiener_imPart k)
      hk.2 hρ hρ1 hloss, mul_zero, add_zero]

/-- Any uncancelled translated zero order rules out payment of the actual Möbius receiver. -/
theorem not_receiverBounded_moebius_of_strict_order_loss
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {ρ : ℂ}
    (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1)
    (hloss : analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ) :
    ¬ ReceiverBounded (pmPowerDampedRealWeight ε) :=
  (obstructionHull_nonempty_iff _ _).1
    ⟨_, mem_obstructionHull_moebius_of_strict_order_loss hε hε2 hρ hρ1 hloss⟩

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.zeta_order_le_translated_order_add_kernel_order_of_repairs
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.lSeries_kernel_eq_zero_of_strict_order_loss

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.mem_obstructionHull_moebius_of_strict_order_loss

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.zeta_order_le_translated_order_add_paid_kernel_order

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.paid_kernel_jets_vanish_below_visible_order
end
end
