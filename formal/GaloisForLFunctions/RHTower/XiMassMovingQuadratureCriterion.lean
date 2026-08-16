import GaloisForLFunctions.RHTower.XiMassSubcausticCriterion
import GaloisForLFunctions.RHTower.XiMassLogSubcausticWindow

/-!
# The moving quadrature-defect criterion

Whenever a moving height stays below the caustic and its prime-discrepancy annulus up to the
caustic is eventually bounded, the quadrature defect at its integer cutoff differs from the
caustic defect by a globally bounded amount.  Hence the Riemann hypothesis is equivalent to
uniform boundedness of the defect at that moving cutoff.

Applied to `κ_B u − L_c u^{1/10} − q log u` with `m_B q ≤ 1/2` this gives the smallest exact RH
criterion the three-scale budget produces: exponential action pays the `u^{1/10}` layer, the
prime-number-theorem remainder pays its coefficient, and the transport prefactor `u^{-1/2}` pays
one further logarithmic layer.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The quadrature-defect line bound at a moving integer cutoff. -/
def XiMassMovingQuadratureDefectLineBound (a sigma : ℝ) (Hgt : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp (Hgt u)⌋₊‖ ≤ C

/-- **The caustic and moving defects differ by a bounded amount.** -/
theorem exists_norm_prefixDefect_moving_sub_le {a sigma Cw : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) {Hgt : ℝ → ℝ}
    (hHle : ∀ u : ℝ, 0 ≤ u → Hgt u ≤ xiMassSpacelikeSharpSlope a * u)
    (hev : ∀ᶠ u : ℝ in atTop, 0 ≤ Hgt u ∧
      ‖(∑ p ∈ primeLogWindow (Hgt u) (xiMassSpacelikeSharpSlope a * u),
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
        - ∫ h in (Hgt u)..(xiMassSpacelikeSharpSlope a * u),
            xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤ Cw) :
    ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
        - xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp (Hgt u)⌋₊‖ ≤ C := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkap : 0 < xiMassSpacelikeSharpSlope a := sharpSlope_pos ha
  have hMnn := xiMassVerticalBound_nonneg sigma
  obtain ⟨u₁, hu₁⟩ := (hev.and (eventually_ge_atTop (0 : ℝ))).exists_forall_of_atTop
  have hu₁0 : (0 : ℝ) ≤ u₁ := (hu₁ u₁ le_rfl).2
  refine ⟨max (Cw + 2 * (Real.exp (1 / 2) * xiMassVerticalBound sigma))
    (2 * xiMassPrefixDefectBound sigma ⌊Real.exp (xiMassSpacelikeSharpSlope a * u₁)⌋₊),
    fun u hu => ?_⟩
  rcases le_or_gt u₁ u with hcase | hcase
  · obtain ⟨⟨hH0, hD⟩, _⟩ := hu₁ u hcase
    have hT0 : (0 : ℝ) ≤ xiMassSpacelikeSharpSlope a * u := by positivity
    have hdec := prefixDefect_sub_eq_window (a := a) (sigma := sigma) (u := u)
      (H := Hgt u) (T := xiMassSpacelikeSharpSlope a * u) ha0 hsigma (hHle u hu)
    have he1 := norm_integral_growing_edge_le (a := a) (sigma := sigma) (u := u)
      (H := Hgt u) ha0 hsigma hH0
    have he2 := norm_integral_growing_edge_le (a := a) (sigma := sigma) (u := u)
      (H := xiMassSpacelikeSharpSlope a * u) ha0 hsigma hT0
    rw [hdec]
    refine le_trans ?_ (le_max_left _ _)
    have hpair := norm_sub_le
      (((∑ p ∈ primeLogWindow (Hgt u) (xiMassSpacelikeSharpSlope a * u),
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
        - ∫ h in (Hgt u)..(xiMassSpacelikeSharpSlope a * u),
            xiMassCriticalGrowingFourierProfile a sigma u h)
        + (∫ h in (Hgt u)..Real.log ((⌊Real.exp (Hgt u)⌋₊ : ℝ) + 1),
            xiMassCriticalGrowingFourierProfile a sigma u h))
      (∫ h in (xiMassSpacelikeSharpSlope a * u)..Real.log
          ((⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊ : ℝ) + 1),
          xiMassCriticalGrowingFourierProfile a sigma u h)
    have hadd := norm_add_le
      ((∑ p ∈ primeLogWindow (Hgt u) (xiMassSpacelikeSharpSlope a * u),
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
        - ∫ h in (Hgt u)..(xiMassSpacelikeSharpSlope a * u),
            xiMassCriticalGrowingFourierProfile a sigma u h)
      (∫ h in (Hgt u)..Real.log ((⌊Real.exp (Hgt u)⌋₊ : ℝ) + 1),
          xiMassCriticalGrowingFourierProfile a sigma u h)
    linarith [hpair, hadd, hD, he1, he2]
  · have hmono1 : ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
        ≤ ⌊Real.exp (xiMassSpacelikeSharpSlope a * u₁)⌋₊ :=
      Nat.floor_mono (Real.exp_le_exp.2 (by nlinarith [hcase.le, hkap]))
    have hmono2 : ⌊Real.exp (Hgt u)⌋₊
        ≤ ⌊Real.exp (xiMassSpacelikeSharpSlope a * u₁)⌋₊ :=
      Nat.floor_mono (Real.exp_le_exp.2 (by nlinarith [hHle u hu, hcase.le, hkap]))
    have hb1 := norm_xiMassPrefixQuadratureDefect_le (a := a) (sigma := sigma) ha0 hsigma u
      ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
    have hb2 := norm_xiMassPrefixQuadratureDefect_le (a := a) (sigma := sigma) ha0 hsigma u
      ⌊Real.exp (Hgt u)⌋₊
    have hm1 := xiMassPrefixDefectBound_mono (sigma := sigma) hmono1
    have hm2 := xiMassPrefixDefectBound_mono (sigma := sigma) hmono2
    refine le_trans (norm_sub_le _ _) ?_
    refine le_trans ?_ (le_max_right _ _)
    linarith

/-- **The moving quadrature-defect RH criterion.** -/
theorem riemannHypothesis_iff_movingQuadratureDefectLineBound {a c sigma Cw : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) {Hgt : ℝ → ℝ}
    (hHle : ∀ u : ℝ, 0 ≤ u → Hgt u ≤ xiMassSpacelikeSharpSlope a * u)
    (hev : ∀ᶠ u : ℝ in atTop, 0 ≤ Hgt u ∧
      ‖(∑ p ∈ primeLogWindow (Hgt u) (xiMassSpacelikeSharpSlope a * u),
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
        - ∫ h in (Hgt u)..(xiMassSpacelikeSharpSlope a * u),
            xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤ Cw) :
    RiemannHypothesis ↔ XiMassMovingQuadratureDefectLineBound a sigma Hgt := by
  have ha : 1 / 2 < a := lt_trans hhalf hca
  have hkone : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  obtain ⟨C₀, hC₀⟩ := exists_norm_prefixDefect_moving_sub_le ha hsigma hHle hev
  have hcaustic := riemannHypothesis_iff_xiMassCriticalBesselQuadratureDefectLineBound
    (a := a) (c := c) (sigma := sigma) (kappa := xiMassSpacelikeSharpSlope a)
    hhalf hca hsigma hkone le_rfl
  rw [hcaustic, XiMassCriticalBesselQuadratureDefectLineBound,
    XiMassMovingQuadratureDefectLineBound]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + C₀, fun u hu => ?_⟩
    have hB := hC u hu
    rw [xiMassCriticalPrimeQuadratureDefect_eq_prefix hkone u] at hB
    have hdiff := hC₀ u hu
    have hsplit : xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp (Hgt u)⌋₊
        = xiMassPrefixQuadratureDefect a sigma u
            ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
          - (xiMassPrefixQuadratureDefect a sigma u
              ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
            - xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp (Hgt u)⌋₊) := by ring
    rw [hsplit]
    exact (norm_sub_le _ _).trans (add_le_add hB hdiff)
  · rintro ⟨C, hC⟩
    refine ⟨C + C₀, fun u hu => ?_⟩
    have hS := hC u hu
    have hdiff := hC₀ u hu
    rw [xiMassCriticalPrimeQuadratureDefect_eq_prefix hkone u]
    have hsplit : xiMassPrefixQuadratureDefect a sigma u
        ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
        = xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp (Hgt u)⌋₊
          + (xiMassPrefixQuadratureDefect a sigma u
              ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
            - xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp (Hgt u)⌋₊) := by ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hS hdiff)

/-! ## The logarithmically corrected criterion -/

/-- **(21.10) The logarithmically corrected subcaustic RH criterion.**  There is a positive
coefficient chamber inside which, for every logarithmic coefficient with `m_B q ≤ 1/2`, RH is
equivalent to uniform boundedness of the quadrature defect at the cutoff
`⌊e^{κ_B u − L u^{1/10} − q log u}⌋`. -/
theorem exists_riemannHypothesis_iff_logSubcausticQuadratureDefectLineBound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    ∃ Lc : ℝ, 0 < Lc ∧ ∀ L q : ℝ, 0 < L → L ≤ Lc → 0 ≤ q →
      (2 * a ^ 2 - 1 / 2) * q ≤ 1 / 2 →
      (RiemannHypothesis ↔ XiMassMovingQuadratureDefectLineBound a sigma
        (xiMassLogSubcausticHeight a L q)) := by
  have ha : 1 / 2 < a := lt_trans hhalf hca
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkap : 0 < xiMassSpacelikeSharpSlope a := sharpSlope_pos ha
  obtain ⟨Lc, hLc0, hLc⟩ := exists_eventually_norm_logSubcausticWindowDefect_le ha hsigma
  refine ⟨Lc, hLc0, fun L q hL hLle hq hqcap => ?_⟩
  obtain ⟨Cw, hCw⟩ := hLc L q hL hLle hq hqcap
  have hHle : ∀ u : ℝ, 0 ≤ u →
      xiMassLogSubcausticHeight a L q u ≤ xiMassSpacelikeSharpSlope a * u :=
    fun u hu => xiMassLogSubcausticHeight_le hL.le hq hu
  exact riemannHypothesis_iff_movingQuadratureDefectLineBound hhalf hca hsigma hHle hCw

end

end RHTower
