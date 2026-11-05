import GaloisForLFunctions.FrustratedArithmeticDirichletForms.TheArithmeticHardyInterval
import GaloisForLFunctions.FrustratedArithmeticDirichletForms.FrustrationCannotBeSwitchedAway
import GaloisForLFunctions.FrustratedArithmeticDirichletForms.TheWindowEnergyHasNoTrace
import GaloisForLFunctions.FrustratedArithmeticDirichletForms.WeilsFormCannotReadPointValues
import GaloisForLFunctions.FrustratedArithmeticDirichletForms.TheEntryIsLogarithmicallySoft
import GaloisForLFunctions.FrustratedArithmeticDirichletForms.TheCentreReflectsTheTrivialZeros
import GaloisForLFunctions.FrustratedArithmeticDirichletForms.SignedThetaGaugesReverseTheEvenDeficit
import GaloisForLFunctions.FrustratedArithmeticDirichletForms.EachEntryConfinesItsWeight
import GaloisForLFunctions.FrustratedArithmeticDirichletForms.SoftEntryInEveryStageFibre
import GaloisForLFunctions.SignedWindowCriticality.BelowLogFour.RetainedVarianceAndHalfWindowBandBelowLogFour
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WindowGrowthIsATranslationContraction
import GaloisForLFunctions.RHTower.DeBruijnNewmanCollisionCriterion
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.SymmetricHalfCollisionLaw
import GaloisForLFunctions.GrowingWindowsOfSpecZ.RHIsDecidedOnTwoSites

/-!
# The questions of the field

The eight questions of review §2.7, each answered by one theorem in exact form. Q1, Q2, Q5, Q6 and the
stage part of Q7 rest on this programme's modules; Q3, Q4, Q7 and Q8 collect the corpus's exact forms
(SWC, SRT, CSTW, RHTower, ZCG) into the statement the question asks for. Every statement is
unconditional; where the answer is an equivalence with RH it is stated as one.

* **Q1** (`question_one`): the arithmetic part is an optimal Hardy term iff RH; scaling optimality,
  criticality, the prime-free line and the bounded interval after the first entry are unconditional.
* **Q2** (`question_two`): the even sector is balanced exactly up to `log ρ` and frustrated in every
  sign gauge past it, whatever the prime weights; the odd light cone is positive, and every acting
  prime power adds an anti-diagonal that is frustrated in every sign gauge.
* **Q3** (`question_three`, `question_three_survivor`): on every window and for every shift `a > 0`,
  the retained-variance certificates in the theta gauge `Φ` (even sector) and the shifted ground state
  `ω_a` (odd sector) are exact, their remainders nonnegative on every window iff RH; and the even outside
  deficit is an artifact of nonnegative gauges.
* **Q4** (`question_four`): on a reflection pair the collective law is the band
  `|𝓗_m(f) − Σ_nw_n(f⋆f)(2m − log n)| ≤ W(f)`, equivalent to positivity of the pair; uniformly in the
  stage (all centred pairs of every length) it is RH.
* **Q5** (`question_five`): the window energy is regional plus edge killing, the plateau is pure
  edge, point evaluation is unbounded in the energy norm, Weil's form cannot read point values, and
  the centre pays the trivial zeros.
* **Q6** (`question_six`): each entry confines its weight; the stage step in the newest weight is a
  compact interval; the entry is at most logarithmically soft.
* **Q7** (`question_seven`): positivity propagates from length `ℓ` to `ℓ + ε` iff the translation by
  `ε` is a contraction; RH iff every growth step is.
* **Q8** (`question_eight`): reality at near-coincidences is the absence of heat collisions, RH iff
  every heat zero is simple for `t > 0`, and size alone cannot repel: Lindelöf-bounded pair models
  collide below every positive time scale.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower _root_.Zeta23
open GaloisForLFunctions.RHTower (screwSignThreshold)
open GaloisForLFunctions.SignedWindowCriticality
open GaloisForLFunctions.SignedWindowCriticality.BelowLogFour
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis (weilQuad SupportedIn)
open GaloisForLFunctions.SquareRootThreshold (ZetaWindowPositive)
open GaloisForLFunctions.ArithmeticCriticalityTheory (translateSpan translateCoshCoefficient)

/-- **Q1.** -/
theorem question_one :
    (ArithmeticPartIsOptimalHardyTerm ↔ RiemannHypothesis) ∧
      (∀ t : ℝ, (∀ c, t ∈ hardyInterval c) → t = 1) ∧
      (∀ c : ℝ, 2 * c < Real.log 2 → hardyInterval c = univ) ∧
      (∀ c : ℝ, Real.log 2 < 2 * c → ∃ L U : ℝ, hardyInterval c ⊆ Icc L U) ∧
      (∀ c, Convex ℝ (hardyInterval c) ∧ IsClosed (hardyInterval c)) :=
  ⟨isOptimalHardyTerm_iff_RH, fun _ => eq_one_of_forall_mem_hardyInterval,
    fun _ => hardyInterval_eq_univ, fun _ => hardyInterval_bounded,
    fun c => ⟨convex_hardyInterval c, isClosed_hardyInterval c⟩⟩

/-- **Q2.** -/
theorem question_two :
    (∀ c : ℝ, 0 ≤ c → ((∀ u ∈ Icc (-c) 0, ∀ v ∈ Icc (-c) 0, u ≠ v → 0 ≤ evenSectorKernel u v) ↔
      c ≤ screwSignThreshold)) ∧
    (∀ c : ℝ, screwSignThreshold < c → ∀ σ : ℝ → ℝ, IsSignGauge σ →
      ∃ u ∈ Icc (-c) 0, ∃ v ∈ Icc (-c) 0, u ≠ v ∧ σ u * σ v * evenSectorKernel u v < 0) ∧
    (∀ c u v : ℝ, u ∈ Ioo (-c) 0 → v ∈ Ioo (-c) 0 → u ≠ v → 0 < oddSectorKernel u v) ∧
    (∀ c w ℓ : ℝ, 0 < ℓ → ℓ / 2 < c → 0 < w → ∀ σ : ℝ → ℝ, IsSignGauge σ →
      ∃ u ∈ Ioo (-c) 0, ∃ v ∈ Ioo (-c) 0, u ≠ v ∧
        (σ u * σ v * oddSectorKernel u v < 0 ∨ (u + v = -ℓ ∧ σ u * σ v * (-w) < 0))) :=
  ⟨fun _ hc => evenSectorKernel_nonneg_iff hc, fun _ hc _ hσ => even_frustrated_in_every_sign_gauge hc hσ,
    fun _ _ _ hu hv huv => oddSectorKernel_pos_on_halfWindow hu hv huv,
    fun _ _ _ hℓ hc hw _ hσ => odd_frustrated_at_every_entry hℓ hc hw hσ⟩

/-- **Q3.** On every window `[−c, c]` and for every shift `a > 0` the window is nonnegative iff the
retained-variance certificates hold in `Φ` (even sector) and in `ω_a` (odd sector); hence RH iff
they hold on every window. -/
theorem question_three {a : ℝ} (ha : 0 < a) :
    (∀ c : ℝ, 0 < c → (ZetaWindowPositive c ↔
      (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
        2 * SignedWindowCriticality.chargeVariance (fun x => riemannKernelReal x * Real.cosh (x / 2))
            (Ioo (-c) c) u +
          2 * (1 / 2 - ∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2)) *
            (∫ x, u x ^ 2 * (riemannKernelReal x * Real.cosh (x / 2))) ≤
          ArithmeticCriticalityTheory.signedJumpEnergy riemannKernelReal u) ∧
      (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
        0 ≤ 2 * ArithmeticCriticalityTheory.sameSideEnergy (ArithmeticCriticalityTheory.shiftedGroundState a) u -
            ArithmeticCriticalityTheory.reflectedDifferenceEnergy
              (ArithmeticCriticalityTheory.shiftedGroundState a) u +
          8 * ((∫ x in Ioo (0 : ℝ) c, ArithmeticCriticalityTheory.shiftDifference a x * Real.sinh (x / 2)) *
              (∫ x in Ioi (0 : ℝ), u x ^ 2 * ArithmeticCriticalityTheory.shiftDifference a x *
                Real.sinh (x / 2)) -
            (∫ x in Ioi (0 : ℝ), u x * ArithmeticCriticalityTheory.shiftDifference a x *
              Real.sinh (x / 2)) ^ 2) +
          8 * SignedWindowCriticality.outsideCharge a c *
            ∫ x in Ioi (0 : ℝ), u x ^ 2 * ArithmeticCriticalityTheory.shiftDifference a x *
              Real.sinh (x / 2)))) ∧
    (RiemannHypothesis ↔ ∀ c : ℝ, 0 < c → ZetaWindowPositive c) :=
  ⟨fun c hc => (zetaWindowPositive_iff_even_and_odd_sectors c).trans
      (and_congr (even_nonneg_iff_retainedVariance_groundState hc.le)
        (odd_nonneg_iff_retainedVariance_shiftedGroundState ha hc)),
    SquareRootThreshold.riemannHypothesis_iff_forall_zetaWindowPositive⟩

/-- **Q3, positive survivor.** The outside cosh deficit of nonnegative even theta gauges is not
forced: on every window a signed three-translate gauge is positive and has negative outside cosh
charge. -/
theorem question_three_survivor {c : ℝ} (hc : 0 < c) :
    ∃ b : ℝ, (∀ x, |x| ≤ c → 0 < riemannKernelReal x *
        translateSpan Finset.univ lobeWeights (lobeShifts b) x) ∧
      translateCoshCoefficient Finset.univ lobeWeights (lobeShifts b) / 2 -
        coshCharge (translateSpan Finset.univ lobeWeights (lobeShifts b)) (Ioo (-c) c) < 0 := by
  obtain ⟨hpos, -, hneg⟩ := exists_signedThetaGauge hc (le_max_left (2 * c) 4) (le_max_right _ _)
  exact ⟨max (2 * c) 4, fun x hx => lt_of_lt_of_le (by have := riemannKernelReal_pos x; linarith)
    (hpos x hx), hneg⟩

/-- On a reflection pair the collective law is Weil's pairing of the test with its mirror. -/
theorem coupling_eq_weilPair {f : ℝ → ℝ} {m : ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hm : ∀ u, m < u → f u = 0) :
    collarHankel m f - ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n) =
      ArithmeticCastelnuovoSeveri.weilPair f (collarReflect m f) := by
  set g := collarReflect m f
  have hfr : f ∈ ArithmeticCastelnuovoSeveri.realTests := ⟨hf, hfc⟩
  have hgr : g ∈ ArithmeticCastelnuovoSeveri.realTests :=
    ⟨contDiff_collarReflect hf, hasCompactSupport_collarReflect hfc⟩
  have hfgr : f + g ∈ ArithmeticCastelnuovoSeveri.realTests :=
    ArithmeticCastelnuovoSeveri.realTests.add_mem hfr hgr
  have hsum := weilQuad_add_collarReflect hf hfc hm
  have hQ : ∀ h : ℝ → ℝ, weilQuad h = ArithmeticCastelnuovoSeveri.weilPair h h := fun _ => rfl
  have hpol : weilQuad (fun u => f u + g u) =
      weilQuad f + 2 * ArithmeticCastelnuovoSeveri.weilPair f g + weilQuad g := by
    rw [show (fun u => f u + g u) = f + g from rfl, hQ, hQ f, hQ g,
      ArithmeticCastelnuovoSeveri.weilPair_add_left hfr hgr hfgr,
      ArithmeticCastelnuovoSeveri.weilPair_comm f, ArithmeticCastelnuovoSeveri.weilPair_comm g,
      ArithmeticCastelnuovoSeveri.weilPair_add_left hfr hgr hfr,
      ArithmeticCastelnuovoSeveri.weilPair_add_left hfr hgr hgr,
      ArithmeticCastelnuovoSeveri.weilPair_comm g f]
    ring
  have hg : weilQuad g = weilQuad f := weilQuad_collarReflect f m
  linarith

/-- **Uniformly in the stage the collective law of an even bump is its orbit correlation**:
`𝒞_m(φ) = c_φ(2m)`, the Weil pairing of `φ` with its translate by `2m`. -/
theorem coupling_eq_weilOrbitCorr_of_even {φ : ℝ → ℝ} {m : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hm : ∀ u, m < u → φ u = 0) (heven : ∀ x, φ (-x) = φ x) :
    collarHankel m φ - ∑' n : ℕ, vonMangoldtAtom n * selfConv φ (2 * m - Real.log n) =
      GrowingWindowsOfSpecZ.weilOrbitCorr φ (2 * m) := by
  rw [coupling_eq_weilPair hφ hφc hm, GrowingWindowsOfSpecZ.weilOrbitCorr,
    ArithmeticCastelnuovoSeveri.weilPair_comm]
  congr 1
  funext v
  simp only [ArithmeticCastelnuovoSeveri.scaleShift, collarReflect]
  rw [← heven (2 * m - v)]
  congr 1
  ring

/-- Under RH the collective law is strict on every nonzero even bump at every stage beyond its
support (GWZ: RH is strict orbit Cauchy–Schwarz). -/
theorem abs_coupling_lt_of_RH (hRH : RiemannHypothesis) {φ : ℝ → ℝ} {m : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφ0 : φ ≠ 0) (hm0 : 0 < m) (hm : ∀ u, m < u → φ u = 0)
    (heven : ∀ x, φ (-x) = φ x) :
    |collarHankel m φ - ∑' n : ℕ, vonMangoldtAtom n * selfConv φ (2 * m - Real.log n)| <
      weilQuad φ := by
  rw [coupling_eq_weilOrbitCorr_of_even hφ hφc hm heven]
  exact GrowingWindowsOfSpecZ.abs_weilOrbitCorr_lt hRH ⟨hφ, hφc⟩ hφ0 (by positivity)

/-- **Q4.** On every reflection pair the collective law (the pole square of the collar Hankel form
against the sliver reflections of all acting prime powers) is the band, equivalent to positivity of
the pair; uniformly in the stage — on the centred pairs of every half-window — it is RH. -/
theorem question_four :
    (∀ (f : ℝ → ℝ) (m : ℝ), ContDiff ℝ 2 f → HasCompactSupport f → (∀ u, m < u → f u = 0) →
      (|collarHankel m f - ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n)| ≤
          weilQuad f ↔
        0 ≤ weilQuad (fun u => f u + collarReflect m f u) ∧
          0 ≤ weilQuad (fun u => f u + -collarReflect m f u))) ∧
    (RiemannHypothesis ↔ ∀ c : ℝ, 0 < c → ∀ f : ℝ → ℝ, ContDiff ℝ 2 f →
      (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) → |centreCoupling f| ≤ weilQuad f) := by
  refine ⟨fun f m hf hfc hm => abs_coupling_le_weilQuad_iff hf hfc hm, ?_⟩
  rw [SquareRootThreshold.riemannHypothesis_iff_forall_zetaWindowPositive]
  exact forall_congr' fun c => forall_congr' fun hc => zetaWindowPositive_iff_abs_centreCoupling_le hc

/-- **Q5.** -/
theorem question_five :
    (∀ (f : ℝ → ℝ) (a b : ℝ), ContDiff ℝ 2 f → HasCompactSupport f → (∀ u, u ∉ Icc a b → f u = 0) →
      levyEnergy f = regionalEnergy f a b + edgeKilling f a b ∧ edgeKilling f a b ≤ levyEnergy f) ∧
    (∀ a b : ℝ, a ≤ b → edgeKilling ((Icc a b).indicator fun _ => (1 : ℝ)) a b =
      levyEnergy ((Icc a b).indicator fun _ => (1 : ℝ))) ∧
    (∀ (x₀ ε : ℝ), 0 < ε → ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ g x₀ = 1 ∧
      (∀ u, ε < |u - x₀| → g u = 0) ∧ (∫ u, g u ^ 2) ≤ ε ∧ (∫ u, |g u|) ≤ ε ∧ levyEnergy g ≤ ε) ∧
    (∀ (f : ℝ → ℝ) (R x₀ ε : ℝ), ContDiff ℝ 2 f → HasCompactSupport f → SupportedIn R f →
      |x₀| < R → 0 < ε → ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ g x₀ = 1 ∧
        SupportedIn R g ∧ |weilQuad (fun u => f u + g u) - weilQuad f| ≤ ε) ∧
    (∀ (c : ℝ) (f : ℝ → ℝ) (α : ℝ), Continuous f → (∀ u, u ∉ Icc (-c) 0 → f u = 0) →
      mirrorMoment f α ^ 2 + neumannEnergy c f α = mirrorKilling c f α ∧
        dirichletEnergy c f α = mirrorKilling c f α + mirrorMoment f α ^ 2) :=
  ⟨fun _ _ _ hf hfs hab => ⟨levyEnergy_eq_regional_add_edge hf hfs hab,
      edgeKilling_le_levyEnergy hf hfs hab⟩,
    fun _ _ hab => edgeKilling_indicator hab, fun x₀ _ hε => exists_spike x₀ hε,
    fun _ _ _ _ hf hfc hfR hx₀ hε => exists_spike_weilQuad_close hf hfc hfR hx₀ hε,
    fun _ _ α hfc hf => ⟨sq_moment_add_neumann_eq hfc hf α, dirichlet_eq_add_sq_moment hfc hf α⟩⟩

/-- **Q6.** Each entry confines its weight, the stage step is a compact interval, and the entry is
at most logarithmically soft. -/
theorem question_six {n₀ : ℕ} (hn₀ : 2 ≤ n₀) :
    (∀ c : ℝ, Real.log n₀ < 2 * c →
      (∃ L U : ℝ, ∀ lam ∈ calibration c, lam n₀ ∈ Icc L U) ∧
        ∀ lam : ℕ → ℝ, Convex ℝ {t : ℝ | withWeight lam n₀ t ∈ calibration c} ∧
          IsClosed {t : ℝ | withWeight lam n₀ t ∈ calibration c} ∧
            ∃ L U : ℝ, {t : ℝ | withWeight lam n₀ t ∈ calibration c} ⊆ Icc L U) ∧
    ∃ δ₀ A B : ℝ, 0 < δ₀ ∧ ∀ c : ℝ, Real.log n₀ < 2 * c → 2 * c - Real.log n₀ ≤ δ₀ →
      ∀ lam ∈ calibration c,
        |lam n₀| ≤ Real.sqrt n₀ * (A * Real.log (1 / (2 * c - Real.log n₀)) + B) :=
  ⟨fun _ hc => ⟨calibration_coord_bounded hn₀ hc, fun lam => stageFibre_interval lam hn₀ hc⟩,
    abs_calibration_coord_le_log hn₀⟩

/-- **Q6, beyond the sliver.** The stage fibre of an entering weight is logarithmically soft from both
sides: with a Lévy margin `η` it contains the interval of radius `√n₀ η (e^{−1/2}/2) log(1/δ)` about
the current weight and lies in one of radius `√n₀(A log(1/δ) + B)`. Summed over all acting powers,
size pays a perturbation `μ` of the weights up to the edge-law constant `E_c(μ)`; this certificate
dies once `E_c ≥ 1`, which for `ζ` happens on every window with `2c ≥ log 2 + 8`. Beyond the sliver
the primes are paid collectively and by sign. -/
theorem question_six_beyond_the_sliver {n₀ : ℕ} (hn₀ : 2 ≤ n₀) :
    (∃ δ₀ A B : ℝ, 0 < δ₀ ∧ ∀ c : ℝ, Real.log n₀ < 2 * c → 2 * c - Real.log n₀ ≤ δ₀ →
      ∀ (η : ℝ) (lam : ℕ → ℝ), 0 ≤ η →
      (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c →
        η * levyEnergy f ≤
          (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re) →
      Icc (lam n₀ - Real.sqrt n₀ * η *
            (Real.exp (-1 / 2) / 2 * Real.log (1 / (2 * c - Real.log n₀))))
          (lam n₀ + Real.sqrt n₀ * η *
            (Real.exp (-1 / 2) / 2 * Real.log (1 / (2 * c - Real.log n₀)))) ⊆
        {t | withWeight lam n₀ t ∈ calibration c} ∧
      {t | withWeight lam n₀ t ∈ calibration c} ⊆
        Icc (-(Real.sqrt n₀ * (A * Real.log (1 / (2 * c - Real.log n₀)) + B)))
          (Real.sqrt n₀ * (A * Real.log (1 / (2 * c - Real.log n₀)) + B))) ∧
    (∀ (c : ℝ) (lam mu : ℕ → ℝ),
      (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c →
        edgeLawConstant c mu * levyEnergy f ≤
          (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re) →
      lam + mu ∈ calibration c) ∧
    ∀ c : ℝ, Real.log 2 + 8 ≤ 2 * c →
      ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c ∧
        (weilFullFunctional (fun _ => 0)
            (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re <
          edgeLawConstant c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) * levyEnergy f :=
  ⟨stageFibre_two_sided hn₀, fun _ _ _ h => add_mem_calibration_of_edgeLaw h,
    fun _ hc => edgeLaw_fails_for_vonMangoldt hc⟩

/-- **Q7.** -/
theorem question_seven :
    (∀ ℓ ε : ℝ, 0 < ε → ε < ℓ →
      ((∀ H, CohomologyOfWindowsOfSpecZ.IsWindowTest (ℓ + ε) H → 0 ≤ weilQuad H) ↔
        (∀ v, CohomologyOfWindowsOfSpecZ.IsWindowTest ℓ v → 0 ≤ weilQuad v) ∧
          ∀ u v, CohomologyOfWindowsOfSpecZ.IsWindowTest ℓ u →
            CohomologyOfWindowsOfSpecZ.IsWindowTest ℓ v →
            ArithmeticCastelnuovoSeveri.weilPair (fun x => u (x + ε)) v ^ 2 ≤
              weilQuad u * weilQuad v)) ∧
    (RiemannHypothesis ↔ ∀ ℓ ε : ℝ, 0 < ε → ε < ℓ → ∀ u v,
      CohomologyOfWindowsOfSpecZ.IsWindowTest ℓ u →
        CohomologyOfWindowsOfSpecZ.IsWindowTest ℓ v →
        ArithmeticCastelnuovoSeveri.weilPair (fun x => u (x + ε)) v ^ 2 ≤ weilQuad u * weilQuad v) :=
  ⟨fun _ _ hε hεℓ => CanonicalSystemOfTheWindowTower.window_nonneg_iff_contraction hε hεℓ,
    CanonicalSystemOfTheWindowTower.riemannHypothesis_iff_translation_contraction⟩

/-- **Q8.** -/
theorem question_eight :
    (RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → ∀ z : ℂ, DeBruijn.riemannHeat t z = 0 →
        deriv (DeBruijn.riemannHeat t) z ≠ 0) ∧
    ∀ L τ : ℝ, 0 < L → 0 < τ → ∃ δ t_star : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < t_star ∧ t_star < τ ∧
      DeBruijn.pairModelHeat L δ t_star 0 = 0 ∧
        deriv (DeBruijn.pairModelHeat L δ t_star) 0 = 0 := by
  refine ⟨DeBruijn.riemannHypothesis_iff_forall_zeros_simple, fun L τ hL hτ => ?_⟩
  obtain ⟨δ, t, hδ, hδ2, ht, htτ, -, -, h0, h1, -⟩ :=
    ZeroConfigurationGeometry.exists_pairModelHeat_real_collision_below_scale hL hτ
  exact ⟨δ, t, hδ, hδ2, ht, htτ, h0, h1⟩

end GaloisForLFunctions.FrustratedArithmeticDirichletForms
