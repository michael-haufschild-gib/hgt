import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryLowPacketCorrectionHasItsPolarCapacity
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalThresholdOfAWindow

/-!
# The low-packet payment at every ratio is the Riemann hypothesis

Along the critical curve `c⁸/log N → R`, the best low-packet correction of a window block lowers its
energy by exactly the polar capacity `S(h)²/D(R)` (`tendsto_optimized_terminal_window_energy`). The
**polar payment** at ratio `R` on the window `[−A, 0]` is the inequality

`S(h)²/D(R) ≤ a_φ Q(H) + (7J(1)/R) M₈(H)`,  `H = e^{y/2} h`, for every window test `h`

(`PolarPaymentAt`). It is the limit form of the low-packet Schur payment against a window.

* **Necessity** (`polarPaymentAt_of_eventually_nonneg`): if the complete matrix is eventually
  positive semidefinite along one critical sequence of ratio `R`, the payment holds at `R` on every
  window.
* **The payment bounds the ratio** (`le_windowThreshold_of_polarPaymentAt`): payment at `R` on
  `[−A, 0]` gives `R ≤ R₁(A)`, the critical threshold of the window. So positivity at one ratio forces
  `R ≤ inf_A R₁(A)` (`le_windowThreshold_of_eventually_nonneg`).
* **At every ratio it is RH** (`riemannHypothesis_of_polarPayment_on_growing_windows`,
  `riemannHypothesis_of_polarPayment_on_top_windows`): payment at every ratio `R` on windows of
  length `A(R) → ∞`, in particular on the top logarithmic windows `(1/8) log(R + 1) + C₀`, implies RH.
  Positivity of the complete matrix at every ratio implies RH
  (`riemannHypothesis_of_eventually_nonneg_at_every_ratio`).
* **The certified band** (`exists_polarPaymentAt_on_every_window`): below `(2K)⁸` the payment holds on
  every window.

So the low-packet payment against the top window is not a finite task at every ratio: past the
certified band it carries the sign of Weil's form on windows of length `(1/8) log R + O(1)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations ArithmeticDegenerationTheory
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics CohomologyOfWindowsOfSpecZ
  WindowTowerOfSpecZ

/-- **Polar payment at ratio `R` on the window `[−A, 0]`**: every window test pays the polar capacity
of the low packet out of its critical pencil. -/
def PolarPaymentAt (R A : ℝ) : Prop :=
  ∀ h : ℝ → ℝ, ContDiff ℝ 2 h → (∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) →
    generalTerminalPolarSource A h ^ 2 / criticalPoleWindowCost R ≤ windowPencil R (halfWeight h)

/-- **Necessity.** Eventual positive semidefiniteness along a critical sequence of ratio `R` forces
the polar payment at `R` on every window. -/
theorem polarPaymentAt_of_eventually_nonneg {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hpsd : ∀ᶠ N : ℕ in atTop, ∀ z : EuclideanSpace ℝ (PrimeHorizonIndex N),
      0 ≤ ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) z, z⟫)
    {A : ℝ} (hA : 0 ≤ A) : PolarPaymentAt R A := by
  intro h hh hsupp
  have ht := tendsto_optimized_terminal_window_energy hh hA hsupp hc hR hcrit
  have hlim := ge_of_tendsto ht (by
    filter_upwards [hpsd] with N hN
    exact div_nonneg (hN _) (zero_le_one.trans (hc N)))
  unfold windowPencil splineAtom exponentialMass
  linarith only [hlim]

/-- **The payment bounds the ratio by the window threshold.** -/
theorem le_windowThreshold_of_polarPaymentAt {R A : ℝ} (hR : 0 < R) (hpay : PolarPaymentAt R A) :
    (R : EReal) ≤ windowThreshold A := by
  refine le_iInf fun H => le_iInf fun hH => le_iInf fun hQ => EReal.coe_le_coe_iff.mpr ?_
  have he : ContDiff ℝ 2 (fun y : ℝ => Real.exp (-(y / 2))) := by fun_prop
  have hh : ContDiff ℝ 2 (fun y => Real.exp (-(y / 2)) * H y) := he.mul hH.contDiff
  have hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → Real.exp (-(y / 2)) * H y = 0 := fun y hy => by
    rw [hH.vanish y hy, mul_zero]
  have hp := hpay _ hh hsupp
  rw [halfWeight_inv] at hp
  have hD := criticalPoleWindowCost_pos hR
  have hpen : 0 ≤ windowPencil R H := (div_nonneg (sq_nonneg _) hD.le).trans hp
  have hq : 0 < -weilQuad H := neg_pos.mpr hQ
  have hκ := splineAtom_pos
  rw [testCriticalMultiple, le_div_iff₀ (mul_pos hκ hq)]
  unfold windowPencil at hpen
  have h1 : splineAtom * -weilQuad H ≤ 7 * tiltedJordanOne / R * exponentialMass 8 H := by
    linarith only [hpen]
  have h2 := mul_le_mul_of_nonneg_left h1 hR.le
  have h3 : R * (7 * tiltedJordanOne / R * exponentialMass 8 H) =
      7 * tiltedJordanOne * exponentialMass 8 H := by
    field_simp
  linarith only [h2, h3]

/-- **Positivity at one ratio bounds it by every window threshold.** -/
theorem le_windowThreshold_of_eventually_nonneg {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ}
    (hR : 0 < R) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hpsd : ∀ᶠ N : ℕ in atTop, ∀ z : EuclideanSpace ℝ (PrimeHorizonIndex N),
      0 ≤ ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) z, z⟫)
    {A : ℝ} (hA : 0 ≤ A) : (R : EReal) ≤ windowThreshold A :=
  le_windowThreshold_of_polarPaymentAt hR (polarPaymentAt_of_eventually_nonneg hc hR hcrit hpsd hA)

/-- **Payment at every ratio on growing windows is RH.** -/
theorem riemannHypothesis_of_polarPayment_on_growing_windows {A : ℝ → ℝ}
    (hA : Tendsto A atTop atTop) (hpay : ∀ R : ℝ, 0 < R → PolarPaymentAt R (A R)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_windowThreshold_eq_top]
  intro B _
  refine (EReal.eq_top_iff_forall_lt _).mpr fun r => ?_
  obtain ⟨R, hRB, hRr⟩ := ((hA.eventually_ge_atTop B).and
    (eventually_ge_atTop (max (r + 1) 1))).exists
  have hR : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hRr)
  have hthr := (le_windowThreshold_of_polarPaymentAt hR (hpay R hR)).trans
    (windowThreshold_antitone hRB)
  have hrR : (r : EReal) < (R : EReal) :=
    EReal.coe_lt_coe_iff.mpr (by linarith only [(le_max_left _ _).trans hRr])
  exact hrR.trans_le hthr

/-- **Payment at every ratio on the top logarithmic windows is RH.** -/
theorem riemannHypothesis_of_polarPayment_on_top_windows (C₀ : ℝ)
    (hpay : ∀ R : ℝ, 0 < R → PolarPaymentAt R ((1 / 8 : ℝ) * Real.log (R + 1) + C₀)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_polarPayment_on_growing_windows ?_ hpay
  refine tendsto_atTop_add_const_right _ C₀ (Tendsto.const_mul_atTop (by norm_num) ?_)
  exact Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)

/-- **Positivity of the complete matrix at every ratio is RH.** -/
theorem riemannHypothesis_of_eventually_nonneg_at_every_ratio
    (hpos : ∀ R : ℝ, 0 < R → ∃ c : ℕ → ℝ, (∀ N, 1 ≤ c N) ∧
      Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R) ∧
      ∀ᶠ N : ℕ in atTop, ∀ z : EuclideanSpace ℝ (PrimeHorizonIndex N),
        0 ≤ ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) z, z⟫) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_polarPayment_on_growing_windows (A := fun R => R) tendsto_id ?_
  intro R hR
  obtain ⟨c, hc, hcrit, hpsd⟩ := hpos R hR
  exact polarPaymentAt_of_eventually_nonneg hc hR hcrit hpsd hR.le

/-- **The certified band.** Below `(2K)⁸` the polar payment holds on every window. -/
theorem exists_polarPaymentAt_on_every_window :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R ≤ R₀ → ∀ A : ℝ, 0 ≤ A → PolarPaymentAt R A := by
  obtain ⟨K, hK, -, hband⟩ := exists_critical_band_all_windows_ge_polar_capacity
  refine ⟨(2 * K) ^ 8, by positivity, fun R hR hRK A hA h hh hsupp => ?_⟩
  have := hband R hR hRK hh hA hsupp
  unfold windowPencil splineAtom exponentialMass
  exact this

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
