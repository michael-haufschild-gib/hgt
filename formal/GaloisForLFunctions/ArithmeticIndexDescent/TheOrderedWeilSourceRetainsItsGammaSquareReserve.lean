import GaloisForLFunctions.ArithmeticIndexDescent.TheGammaBoundaryReserveIsAnExactSquare
import GaloisForLFunctions.ArithmeticIndexDescent.TheOrderedWeilSourceIsACenteredChebyshevDefect

/-!
# A Gamma square reserve inside the ordered arithmetic source

Translation, reflection and restriction realize the literal ordered collar in
the existing Gamma boundary operator. Applying its exact square identity after
the polar cancellation retains a nonnegative reserve in the original Weil cross
term, alongside its centered Chebyshev discrepancy and localized boundary mass.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal InnerProduct ComplexConjugate
open RHTower RHTower.WeilSpectral Zeta23

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri

private theorem zeroExtension_eq_of_halfLine_support (v : SoninL2)
    (hv : ∀ᵐ x : ℝ, x ≤ 0 → v x = 0) :
    suzukiPositiveZeroExtension (soninHalfLine v) = v := by
  apply Lp.ext
  have hh := (ae_restrict_iff' measurableSet_Ioi).mp (coeFn_soninHalfLine v)
  filter_upwards [suzukiPositiveZeroExtension_ae (soninHalfLine v), hh, hv]
    with x he hh hv
  rw [he]
  change (Ioi (0 : ℝ)).indicator (fun t => soninHalfLine v t) x = v x
  by_cases hx : 0 < x
  · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    exact hh hx
  · rw [Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
    exact (hv (le_of_not_gt hx)).symm

private theorem reflection_zeroExtension_eq_of_negative_support (u : SoninL2)
    (hu : ∀ᵐ x : ℝ, 0 ≤ x → u x = 0) :
    l2Reflection (suzukiPositiveZeroExtension (soninHalfLine (l2Reflection u))) = u := by
  have hr : ∀ᵐ x : ℝ, x ≤ 0 → l2Reflection u x = 0 := by
    have hs :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae.eventually hu
    filter_upwards [l2Reflection_ae u, hs] with x hx hs
    intro hneg
    rw [hx]
    exact hs (by linarith only [hneg])
  rw [zeroExtension_eq_of_halfLine_support (l2Reflection u) hr, l2Reflection_involutive]

/-- The original compact test with the selected boundary translated to zero. -/
def shiftedRealTestL2 (b : ℝ) (f : realTests) : SoninL2 :=
  realProfileL2 (fun u => f.1 (u + b))
    (f.2.1.continuous.comp (continuous_add_const b))
    (f.2.2.comp_homeomorph (Homeomorph.addRight b))

/-- The reflected left profile in the actual positive-half-line carrier. -/
def leftBoundaryTestL2 (b : ℝ) (f : realTests) : SuzukiPositiveL2 :=
  soninHalfLine (l2Reflection (shiftedRealTestL2 b f))

/-- The right profile in the same positive-half-line carrier. -/
def rightBoundaryTestL2 (b : ℝ) (g : realTests) : SuzukiPositiveL2 :=
  soninHalfLine (shiftedRealTestL2 b g)

private theorem shiftedRealTestL2_ae (b : ℝ) (f : realTests) :
    (shiftedRealTestL2 b f : ℝ → ℂ) =ᵐ[volume] fun u => (f.1 (u + b) : ℂ) :=
  realProfileL2_ae _ _ _

private theorem shiftedRealTestL2_nonneg_zero (f : realTests) {b : ℝ}
    (hleft : ∀ u, b ≤ u → f.1 u = 0) :
    ∀ᵐ u : ℝ, 0 ≤ u → shiftedRealTestL2 b f u = 0 := by
  filter_upwards [shiftedRealTestL2_ae b f] with u hu
  intro hpos
  rw [hu, hleft (u + b) (by linarith only [hpos]), Complex.ofReal_zero]

private theorem shiftedRealTestL2_nonpos_zero (g : realTests) {b : ℝ}
    (hright : ∀ u, u ≤ b → g.1 u = 0) :
    ∀ᵐ u : ℝ, u ≤ 0 → shiftedRealTestL2 b g u = 0 := by
  filter_upwards [shiftedRealTestL2_ae b g] with u hu
  intro hneg
  rw [hu, hright (u + b) (by linarith only [hneg]), Complex.ofReal_zero]

private theorem norm_shiftedRealTestL2_sq (b : ℝ) (f : realTests) :
    ‖shiftedRealTestL2 b f‖ ^ 2 = sectionMass f.1 := by
  rw [shiftedRealTestL2, norm_realProfileL2_sq]
  exact integral_add_right_eq_self (fun u => f.1 u ^ 2) b

/-- Restriction and reflection preserve the entire mass of an ordered left test. -/
theorem norm_leftBoundaryTestL2_sq (f : realTests) {b : ℝ}
    (hleft : ∀ u, b ≤ u → f.1 u = 0) :
    ‖leftBoundaryTestL2 b f‖ ^ 2 = sectionMass f.1 := by
  have he := reflection_zeroExtension_eq_of_negative_support (shiftedRealTestL2 b f)
    (shiftedRealTestL2_nonneg_zero f hleft)
  have hn : ‖leftBoundaryTestL2 b f‖ = ‖shiftedRealTestL2 b f‖ := by
    calc
      _ = ‖suzukiPositiveZeroExtension (leftBoundaryTestL2 b f)‖ :=
        (norm_suzukiPositiveZeroExtension _).symm
      _ = ‖l2Reflection (suzukiPositiveZeroExtension (leftBoundaryTestL2 b f))‖ :=
        (l2ReflectionIsometry.norm_map _).symm
      _ = _ := congrArg norm he
  rw [hn, norm_shiftedRealTestL2_sq]

/-- Restriction preserves the entire mass of an ordered right test. -/
theorem norm_rightBoundaryTestL2_sq (g : realTests) {b : ℝ}
    (hright : ∀ u, u ≤ b → g.1 u = 0) :
    ‖rightBoundaryTestL2 b g‖ ^ 2 = sectionMass g.1 := by
  have he := zeroExtension_eq_of_halfLine_support (shiftedRealTestL2 b g)
    (shiftedRealTestL2_nonpos_zero g hright)
  have hn : ‖rightBoundaryTestL2 b g‖ = ‖shiftedRealTestL2 b g‖ := by
    rw [← norm_suzukiPositiveZeroExtension]
    exact congrArg norm he
  rw [hn, norm_shiftedRealTestL2_sq]

private theorem inner_translate_shiftedRealTest (b h : ℝ) (f g : realTests) :
    inner ℂ (logTranslationCLM h (shiftedRealTestL2 b g)) (shiftedRealTestL2 b f) =
      ((∫ u : ℝ, f.1 (u + b) * g.1 (u + h + b) : ℝ) : ℂ) := by
  rw [L2.inner_def, ← integral_complex_ofReal]
  have ht := (shiftedRealTestL2_ae b g).comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have htranslate : (logTranslationCLM h (shiftedRealTestL2 b g) : ℝ → ℂ) =ᵐ[volume]
      fun u => shiftedRealTestL2 b g (u + h) :=
    Lp.coeFn_compMeasurePreserving (shiftedRealTestL2 b g)
      (MellinL2.realTranslation_measurePreserving h)
  apply integral_congr_ae
  filter_upwards [htranslate, shiftedRealTestL2_ae b f, ht] with u hu hf hg
  rw [hu, hf]
  change shiftedRealTestL2 b g (u + h) = (g.1 (u + h + b) : ℂ) at hg
  rw [hg, RCLike.inner_apply, Complex.conj_ofReal]
  exact (Complex.ofReal_mul _ _).symm

/-- The literal ordered collar is the real pairing of its actual boundary profiles. -/
theorem sourceGammaCollar_eq_boundary_pair (f g : realTests) {b : ℝ}
    (hleft : ∀ u, b ≤ u → f.1 u = 0) (hright : ∀ u, u ≤ b → g.1 u = 0) :
    (∫ h in Ioi (0 : ℝ), archLevyDensity h * sourceCollarCorrelation f.1 g.1 h) =
      (inner ℂ (rightBoundaryTestL2 b g)
        (ccmGammaBoundaryCLM (leftBoundaryTestL2 b f))).re := by
  have hu := reflection_zeroExtension_eq_of_negative_support (shiftedRealTestL2 b f)
    (shiftedRealTestL2_nonneg_zero f hleft)
  have hv := zeroExtension_eq_of_halfLine_support (shiftedRealTestL2 b g)
    (shiftedRealTestL2_nonpos_zero g hright)
  have hp := integral_ccmGamma_oppositeHalfLines (leftBoundaryTestL2 b f) (rightBoundaryTestL2 b g)
  rw [show l2Reflection (suzukiPositiveZeroExtension (leftBoundaryTestL2 b f)) =
      shiftedRealTestL2 b f from hu,
    show suzukiPositiveZeroExtension (rightBoundaryTestL2 b g) = shiftedRealTestL2 b g from hv] at hp
  have hc : (∫ h in Ioi (0 : ℝ), (ccmGammaTranslationDensity h : ℂ) *
      inner ℂ (logTranslationCLM h (shiftedRealTestL2 b g)) (shiftedRealTestL2 b f)) =
      ((∫ h in Ioi (0 : ℝ), archLevyDensity h * sourceCollarCorrelation f.1 g.1 h : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro h hh
    dsimp only
    rw [inner_translate_shiftedRealTest]
    have hl : ∀ u, 0 ≤ u → f.1 (u + b) = 0 :=
      fun u hu => hleft (u + b) (by linarith only [hu])
    have hr : ∀ u, u ≤ 0 → g.1 (u + b) = 0 :=
      fun u hu => hright (u + b) (by linarith only [hu])
    rw [← sourceCollarCorrelation_ordered hl hr hh.le,
      sourceCollarCorrelation_translate, ← Complex.ofReal_mul]
    congr 2
    simp only [ccmGammaTranslationDensity, archLevyDensity, neg_div, neg_mul]
  have hre := congrArg Complex.re (hc.symm.trans hp)
  simpa only [Complex.ofReal_re] using hre

/-- The left test tilted by its exponential distance from the cut. -/
def leftBoundaryTiltTest (b : ℝ) (f : realTests) : realTests :=
  ⟨fun u => Real.exp (2 * (u - b)) * f.1 u,
    ((contDiff_const.mul (contDiff_id.sub contDiff_const)).exp).mul f.2.1,
    f.2.2.mul_left⟩

/-- The right test with the corresponding decaying distance weight. -/
def rightBoundaryTiltTest (b : ℝ) (g : realTests) : realTests :=
  ⟨fun u => Real.exp (-2 * (u - b)) * g.1 u,
    ((contDiff_const.mul (contDiff_id.sub contDiff_const)).exp).mul g.2.1,
    g.2.2.mul_left⟩

private theorem leftBoundaryTiltTest_zero (f : realTests) {b : ℝ}
    (hleft : ∀ u, b ≤ u → f.1 u = 0) :
    ∀ u, b ≤ u → (leftBoundaryTiltTest b f).1 u = 0 := by
  intro u hu
  change Real.exp (2 * (u - b)) * f.1 u = 0
  rw [hleft u hu, mul_zero]

private theorem rightBoundaryTiltTest_zero (g : realTests) {b : ℝ}
    (hright : ∀ u, u ≤ b → g.1 u = 0) :
    ∀ u, u ≤ b → (rightBoundaryTiltTest b g).1 u = 0 := by
  intro u hu
  change Real.exp (-2 * (u - b)) * g.1 u = 0
  rw [hright u hu, mul_zero]

private theorem tilted_collar_eq (f g : realTests) {b h : ℝ}
    (hleft : ∀ u, b ≤ u → f.1 u = 0) (hright : ∀ u, u ≤ b → g.1 u = 0)
    (hh : 0 ≤ h) :
    sourceCollarCorrelation (leftBoundaryTiltTest b f).1 (rightBoundaryTiltTest b g).1 h =
      Real.exp (-2 * h) * sourceCollarCorrelation f.1 g.1 h := by
  rw [sourceCollarCorrelation_ordered (leftBoundaryTiltTest_zero f hleft)
      (rightBoundaryTiltTest_zero g hright) hh,
    sourceCollarCorrelation_ordered hleft hright hh, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  change (Real.exp (2 * (u - b)) * f.1 u) *
    (Real.exp (-2 * (u + h - b)) * g.1 (u + h)) = _
  have he : Real.exp (2 * (u - b)) * Real.exp (-2 * (u + h - b)) = Real.exp (-2 * h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (2 * (u - b)) * Real.exp (-2 * (u + h - b))) *
        (f.1 u * g.1 (u + h)) := by ring
    _ = _ := by rw [he]

private theorem orderedGammaTail_eq_tilted_boundary_pair (f g : realTests) {b : ℝ}
    (hleft : ∀ u, b ≤ u → f.1 u = 0) (hright : ∀ u, u ≤ b → g.1 u = 0) :
    orderedGammaTail f.1 g.1 =
      (inner ℂ (rightBoundaryTestL2 b (rightBoundaryTiltTest b g))
        (ccmGammaBoundaryCLM (leftBoundaryTestL2 b (leftBoundaryTiltTest b f)))).re := by
  calc
    _ = ∫ h in Ioi (0 : ℝ), archLevyDensity h *
        sourceCollarCorrelation (leftBoundaryTiltTest b f).1 (rightBoundaryTiltTest b g).1 h := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro h hh
      dsimp only
      rw [tilted_collar_eq f g hleft hright hh.le]
      ring
    _ = _ := sourceGammaCollar_eq_boundary_pair _ _
      (leftBoundaryTiltTest_zero f hleft) (rightBoundaryTiltTest_zero g hright)

/-- The square reserve evaluated on the actual tilted source profiles. -/
def orderedGammaSquareReserve (b : ℝ) (f g : realTests) : ℝ :=
  ∫ p, gammaBoundaryPairReserveDensity
    (leftBoundaryTestL2 b (leftBoundaryTiltTest b f))
    (rightBoundaryTestL2 b (rightBoundaryTiltTest b g)) p
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))

theorem orderedGammaSquareReserve_nonneg (b : ℝ) (f g : realTests) :
    0 ≤ orderedGammaSquareReserve b f g := by
  apply integral_nonneg_of_ae
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  exact gammaBoundaryPairReserveDensity_nonneg _ _ hp.1 hp.2

/-- Exact localized Gamma payment retains its nonnegative square reserve. -/
theorem orderedGammaTail_eq_mass_sub_reserve (f g : realTests) {b : ℝ}
    (hleft : ∀ u, b ≤ u → f.1 u = 0) (hright : ∀ u, u ≤ b → g.1 u = 0) :
    orderedGammaTail f.1 g.1 =
      (Real.pi / 4) * (leftBoundaryMass b f.1 + rightBoundaryMass b g.1) -
        orderedGammaSquareReserve b f g := by
  have h := integral_gammaBoundaryPairReserveDensity
    (leftBoundaryTestL2 b (leftBoundaryTiltTest b f))
    (rightBoundaryTestL2 b (rightBoundaryTiltTest b g))
  rw [norm_leftBoundaryTestL2_sq _ (leftBoundaryTiltTest_zero f hleft),
    norm_rightBoundaryTestL2_sq _ (rightBoundaryTiltTest_zero g hright),
    ← orderedGammaTail_eq_tilted_boundary_pair f g hleft hright] at h
  change orderedGammaSquareReserve b f g =
    (Real.pi / 4) * (leftBoundaryMass b f.1 + rightBoundaryMass b g.1) -
      orderedGammaTail f.1 g.1 at h
  linarith only [h]

/-- The original ordered Weil block retains both signed arithmetic cancellation and Gamma slack. -/
theorem realWeilForm_ordered_eq_chebyshev_add_gammaReserve (f g : realTests) {b : ℝ}
    (hleft : ∀ u, b ≤ u → f.1 u = 0) (hright : ∀ u, u ≤ b → g.1 u = 0) (c : ℝ) :
    realWeilForm f g =
      -(∫ h in Ioi (0 : ℝ), (ArithmeticIncidencePositivity.chebyshevError h - c) *
        deriv (orderedSourceLagWeight f.1 g.1) h) -
      (Real.pi / 4) * (leftBoundaryMass b f.1 + rightBoundaryMass b g.1) +
        orderedGammaSquareReserve b f g := by
  rw [realWeilForm_ordered_eq_centered_chebyshev f g hleft hright c,
    orderedGammaTail_eq_mass_sub_reserve f g hleft hright]
  ring

/-- A signed lower payment on the actual source, with the discrepancy left intact. -/
theorem realWeilForm_ordered_ge_centered_source (f g : realTests) {b : ℝ}
    (hleft : ∀ u, b ≤ u → f.1 u = 0) (hright : ∀ u, u ≤ b → g.1 u = 0) (c : ℝ) :
    -(∫ h in Ioi (0 : ℝ), (ArithmeticIncidencePositivity.chebyshevError h - c) *
      deriv (orderedSourceLagWeight f.1 g.1) h) -
      (Real.pi / 4) * (leftBoundaryMass b f.1 + rightBoundaryMass b g.1) ≤ realWeilForm f g := by
  rw [realWeilForm_ordered_eq_chebyshev_add_gammaReserve f g hleft hright c]
  exact le_add_of_nonneg_right (orderedGammaSquareReserve_nonneg b f g)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.sourceGammaCollar_eq_boundary_pair
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.orderedGammaTail_eq_mass_sub_reserve
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.realWeilForm_ordered_eq_chebyshev_add_gammaReserve
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.realWeilForm_ordered_ge_centered_source
