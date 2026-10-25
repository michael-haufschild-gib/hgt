import GaloisForLFunctions.ArithmeticOrientationTheory.TheOffLineZerosObstructTheMoebiusReceiver
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PaidMellinPairingsHaveNoCriticalBoundaryPole
import GaloisForLFunctions.HTGeometry.VanishingOrderControlsBoundaryCancellation
import GaloisForLFunctions.RHTower.PrimeShiftResidueClosability
import GaloisForLFunctions.RHTower.WeilConeBoundaryDilationInequality
import GaloisForLFunctions.RHTower.DeckChargeInvariant

/-!
# Critical boundary poles obstruct paid kernels

The actual Möbius Mellin identity extends the paid-kernel obstruction to
translated zeta zeros on the critical boundary. Any positive uncancelled
order forces boundary vanishing and prevents payment of the source.
-/

section

noncomputable section
set_option autoImplicit false
open Filter Topology Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory
open TransHorizonIncidenceMechanics WienerAlgebraAt BezoutValuationIncidence

/-- Positive uncancelled pole order on the critical boundary forces every paid kernel to vanish. -/
theorem lSeries_kernel_eq_zero_of_critical_boundary_order_loss
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k : ℕ → ℝ} (hk : CriticalWiener k)
    (hpaid : ReceiverBounded (RHTower.dirichletConv k (pmPowerDampedRealWeight ε)))
    {ρ : ℂ} (hρ : ρ.re = 1 / 2 + ε)
    (hloss : analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ) :
    LSeries (cplx k) (ρ - ε) = 0 := by
  let s₀ : ℂ := ρ - ε
  let c := RHTower.dirichletConv k (pmPowerDampedRealWeight ε)
  let f := weightCenteredPrefix c (∑' d : ℕ, c d / d)
  let m : ℂ := ((∑' d : ℕ, c d / d : ℝ) : ℂ)
  let Φ (s : ℂ) := complexMellinPairing f s + m * riemannZeta s
  have hs₀ : s₀.re = 1 / 2 := by simp only [s₀, sub_re, ofReal_re, hρ]; ring
  have hρ1 : ρ.re < 1 := by rw [hρ]; linarith only [hε2]
  have hρne : ρ ≠ 1 := by intro h; rw [h, one_re] at hρ1; exact lt_irrefl _ hρ1
  have hsne : s₀ ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    rw [hs₀, one_re] at hh
    norm_num at hh
  have hA : AnalyticAt ℂ (fun s : ℂ => riemannZeta (s + ε)) s₀ := by
    have h : AnalyticAt ℂ riemannZeta (s₀ + ε) := by
      simpa only [s₀, sub_add_cancel] using analyticOn_riemannZeta ρ hρne
    exact h.comp (f := fun z : ℂ => z + (ε : ℂ)) (analyticAt_id.add analyticAt_const)
  have hB : AnalyticAt ℂ riemannZeta s₀ := analyticOn_riemannZeta s₀ hsne
  have horder : analyticOrderAt (fun s : ℂ => riemannZeta (s + ε)) s₀ =
      analyticOrderAt riemannZeta ρ := by
    rw [RHTower.analyticOrderAt_comp_add]
    dsimp only [s₀]
    rw [sub_add_cancel]
  have hAfin : analyticOrderAt (fun s : ℂ => riemannZeta (s + ε)) s₀ ≠ ⊤ := by
    rw [horder]
    exact RHTower.analyticOrderAt_riemannZeta_ne_top hρne
  have hcurve : Tendsto (fun u : ℝ => s₀ + (u : ℂ)) (𝓝[>] 0) (𝓝 s₀) := by
    have hc : Continuous (fun u : ℝ => s₀ + (u : ℂ)) := by fun_prop
    have hc0 : ContinuousAt (fun u : ℝ => s₀ + (u : ℂ)) 0 := hc.continuousAt
    have ht := hc0.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    simpa only [ofReal_zero, add_zero] using ht
  have hu : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    change Tendsto Complex.ofReal (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) : ℂ))
    exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨E, hE⟩ := hpaid
  have hΦ : Tendsto (fun u : ℝ => (u : ℂ) * Φ (s₀ + u)) (𝓝[>] 0) (𝓝 0) := by
    have hmain := mul_complexMellinPairing_tendsto_zero_at_boundary
      (weightCenteredPrefix_zero _ _) (fun T => hE T) hs₀
    have hcorr := hu.mul ((tendsto_const_nhds (x := m)).mul
      (hB.continuousAt.tendsto.comp hcurve))
    rw [zero_mul] at hcorr
    simpa only [Φ, f, c, mul_add, zero_add, Function.comp_apply] using hmain.add hcorr
  have hK : Tendsto (fun u : ℝ => LSeries (cplx k) (s₀ + u))
      (𝓝[>] 0) (𝓝 (LSeries (cplx k) s₀)) := by
    have hsum : LSeriesSummable (cplx k) (1 / 2) := by
      have h := (lSeriesSummable_cplx_iff (by norm_num : (0 : ℝ) < 1 / 2)).mpr hk
      convert h using 1; norm_num
    have hcont := RHTower.WeilBoundaryDilation.continuousOn_LSeries_half hsum
    apply (hcont s₀ (by simpa only [Set.mem_setOf_eq, hs₀] using le_rfl)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hcurve, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu0
    rw [add_re, ofReal_re, hs₀]
    linarith only [show 0 < u from hu0]
  apply HTGeometry.eq_zero_of_boundary_order_loss hA hB hAfin
    (by rw [horder]; exact hloss) hΦ hK
  have hsmall : ∀ᶠ u : ℝ in 𝓝[>] 0, u < 1 - ρ.re :=
    (eventually_lt_nhds (sub_pos.mpr hρ1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with u hu0 hu1
  have hu0 : 0 < u := hu0
  have hs : 1 / 2 < (s₀ + (u : ℂ)).re := by rw [add_re, ofReal_re, hs₀]; linarith only [hu0]
  have hs1 : (s₀ + (u : ℂ)).re < 1 := by
    rw [add_re, ofReal_re, hs₀]
    linarith only [hu1, hρ, hε]
  have hne : s₀ + (u : ℂ) + ε ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, ofReal_re, one_re, hs₀] at hre
    linarith only [hre, hu1, hρ]
  have hclear := complexMellinPairing_cleared_identity_of_repairs hε hε2 hk ⟨E, hE⟩
    (s₀ + u) hs hs1
  rw [RHTower.zetaResidueUnit, Function.update_of_ne hne] at hclear
  change ((s₀ + u + ε - 1) * riemannZeta (s₀ + u + ε)) * complexMellinPairing f (s₀ + u) =
    (s₀ + u + ε - 1) * riemannZeta (s₀ + u) * LSeries (cplx k) (s₀ + u) -
      m * riemannZeta (s₀ + u) * ((s₀ + u + ε - 1) * riemannZeta (s₀ + u + ε)) at hclear
  apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
  change (s₀ + u + ε - 1) *
    (riemannZeta (s₀ + u + ε) * (complexMellinPairing f (s₀ + u) + m * riemannZeta (s₀ + u))) =
      (s₀ + u + ε - 1) * (riemannZeta (s₀ + u) * LSeries (cplx k) (s₀ + u))
  linear_combination hclear

/-- Boundary points with visible translated pole order belong to the actual paid-ideal hull. -/
theorem mem_obstructionHull_moebius_of_critical_boundary_order_loss
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2 + ε)
    (hloss : analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ) :
    halfPlanePoint (1 / 2) (ρ - ε) (by simp only [sub_re, ofReal_re, hρ]; linarith) ∈
      obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) := by
  intro k hk
  rw [mem_paidIdeal] at hk
  have hs : (1 / 2 : ℝ) ≤ (ρ - ε).re := by simp only [sub_re, ofReal_re, hρ]; linarith
  rw [bohrEval_halfPlanePoint, lSeries_toFn_eq k hs]
  rw [lSeries_kernel_eq_zero_of_critical_boundary_order_loss hε hε2
      (criticalWiener_rePart k) hk.1 hρ hloss,
    lSeries_kernel_eq_zero_of_critical_boundary_order_loss hε hε2
      (criticalWiener_imPart k) hk.2 hρ hloss, mul_zero, add_zero]

/-- A positive translated boundary pole order rules out payment of the actual Möbius receiver. -/
theorem not_receiverBounded_moebius_of_critical_boundary_order_loss
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2 + ε)
    (hloss : analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ) :
    ¬ ReceiverBounded (pmPowerDampedRealWeight ε) :=
  (obstructionHull_nonempty_iff _ _).1
    ⟨_, mem_obstructionHull_moebius_of_critical_boundary_order_loss hε hε2 hρ hloss⟩

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.lSeries_kernel_eq_zero_of_critical_boundary_order_loss
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.mem_obstructionHull_moebius_of_critical_boundary_order_loss
end
end
