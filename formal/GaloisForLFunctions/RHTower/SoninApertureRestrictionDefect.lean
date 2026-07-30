import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import GaloisForLFunctions.RHTower.SoninCalkinNormBound
import GaloisForLFunctions.RHTower.SoninEulerEssentialNorm
import GaloisForLFunctions.RHTower.SoninEulerTripleShellOverlap
import GaloisForLFunctions.RHTower.SoninPrincipalRelativeIdeal
import GaloisForLFunctions.RHTower.SoninPrincipalShellCyclicTrace

/-!
# Exact and noncompact Sonin aperture-restriction defect

The Sonin carriers are nested contravariantly in the aperture.  Compressing a quadratic dilation
corner from a smaller aperture to a larger aperture is not invariant: its defect is the Gram square
of the transition through the lost Sonin layer.  When the dilation crosses that layer, the
transition has compact distance at least one.  Thus this aperture defect is a new principal
boundary layer; it cannot be absorbed into the trace-class relative ideal.  In the strict crossing
chamber, however, its exact class modulo that ideal is an existing scale-one principal shell.  The
fixed-aperture principal-relative algebra is therefore closed under the positive restriction defect.
-/

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Set Filter Topology
open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-! ## Nested Sonin carriers and projections -/

/-- Enlarging the symmetric aperture shrinks the common physical/Fourier Sonin carrier. -/
theorem centralSoninCarrier_antitone {a b : ℝ} (hab : a ≤ b) :
    centralSoninCarrier b ≤ centralSoninCarrier a := by
  intro f hf
  constructor
  · change f ∈
      (physicalForbidden (centralInterval a)
        (measurableSet_centralInterval a))ᗮ
    apply (Submodule.starProjection_apply_eq_zero_iff
      (K := physicalForbidden (centralInterval a)
        (measurableSet_centralInterval a))).mp
    rw [← indicatorCutoff_eq_physicalForbidden_starProjection]
    have hfb : indicatorCutoff (centralInterval b)
        (measurableSet_centralInterval b) f = 0 := by
      rw [indicatorCutoff_eq_physicalForbidden_starProjection]
      exact (Submodule.starProjection_apply_eq_zero_iff
        (K := physicalForbidden (centralInterval b)
          (measurableSet_centralInterval b))).mpr hf.1
    have hnest := indicatorCutoff_central_mul_of_le a b hab
    calc
      indicatorCutoff (centralInterval a)
          (measurableSet_centralInterval a) f =
          (indicatorCutoff (centralInterval a)
              (measurableSet_centralInterval a) *
            indicatorCutoff (centralInterval b)
              (measurableSet_centralInterval b)) f := by rw [hnest]
      _ = 0 := by rw [mul_apply_eq_comp, hfb, map_zero]
  · change f ∈
      (fourierForbidden (centralInterval a)
        (measurableSet_centralInterval a))ᗮ
    apply (Submodule.starProjection_apply_eq_zero_iff
      (K := fourierForbidden (centralInterval a)
        (measurableSet_centralInterval a))).mp
    rw [← fourierCutoff_eq_fourierForbidden_starProjection]
    have hfb : fourierCutoff (centralInterval b)
        (measurableSet_centralInterval b) f = 0 := by
      rw [fourierCutoff_eq_fourierForbidden_starProjection]
      exact (Submodule.starProjection_apply_eq_zero_iff
        (K := fourierForbidden (centralInterval b)
          (measurableSet_centralInterval b))).mpr hf.2
    have hnest := fourierCutoff_central_mul_of_le a b hab
    calc
      fourierCutoff (centralInterval a)
          (measurableSet_centralInterval a) f =
          (fourierCutoff (centralInterval a)
              (measurableSet_centralInterval a) *
            fourierCutoff (centralInterval b)
              (measurableSet_centralInterval b)) f := by rw [hnest]
      _ = 0 := by rw [mul_apply_eq_comp, hfb, map_zero]

/-- The nested-carrier law restricted to the actual even Sonin Hilbert space. -/
theorem evenCentralSoninCarrier_antitone {a b : ℝ} (hab : a ≤ b) :
    evenCentralSoninCarrier b ≤ evenCentralSoninCarrier a := by
  intro f hf
  change (f : SoninL2) ∈ centralSoninCarrier a
  exact centralSoninCarrier_antitone hab hf

/-- Orthogonal projections onto nested even Sonin carriers absorb in both orders. -/
theorem evenCentralSoninProjection_mul_of_le {a b : ℝ} (hab : a ≤ b) :
    evenCentralSoninProjection b * evenCentralSoninProjection a =
        evenCentralSoninProjection b ∧
      evenCentralSoninProjection a * evenCentralSoninProjection b =
        evenCentralSoninProjection b := by
  have hcarrier : evenCentralSoninCarrier b ≤ evenCentralSoninCarrier a :=
    evenCentralSoninCarrier_antitone hab
  constructor
  · rw [evenCentralSoninProjection_eq_starProjection,
      evenCentralSoninProjection_eq_starProjection]
    exact Submodule.starProjection_comp_starProjection_of_le hcarrier
  · apply ContinuousLinearMap.ext
    intro f
    rw [mul_apply_eq_comp,
      evenCentralSoninProjection_eq_starProjection,
      evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier a).starProjection_eq_self_iff.mpr
      (hcarrier ((evenCentralSoninCarrier b).starProjection_apply_mem f))

/-! ## Exact positive restriction defect -/

/-- Orthogonal layer lost when the aperture grows from `a` to `b`. -/
def evenSoninApertureLayer (a b : ℝ) :
    evenSubspace →L[ℂ] evenSubspace :=
  evenCentralSoninProjection a - evenCentralSoninProjection b

/-- The lost layer is self-adjoint. -/
theorem adjoint_evenSoninApertureLayer (a b : ℝ) :
    (evenSoninApertureLayer a b)† = evenSoninApertureLayer a b := by
  rw [evenSoninApertureLayer, ContinuousLinearMap.adjoint.map_sub,
    adjoint_evenCentralSoninProjection, adjoint_evenCentralSoninProjection]

/-- Under nesting, the lost aperture layer is an orthogonal projection. -/
theorem evenSoninApertureLayer_mul_self {a b : ℝ} (hab : a ≤ b) :
    evenSoninApertureLayer a b * evenSoninApertureLayer a b =
      evenSoninApertureLayer a b := by
  let Qa := evenCentralSoninProjection a
  let Qb := evenCentralSoninProjection b
  have hQa : Qa * Qa = Qa := by
    dsimp only [Qa]
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier a).isIdempotentElem_starProjection
  have hQb : Qb * Qb = Qb := by
    dsimp only [Qb]
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier b).isIdempotentElem_starProjection
  have hnest : Qb * Qa = Qb ∧ Qa * Qb = Qb := by
    simpa only [Qa, Qb] using evenCentralSoninProjection_mul_of_le hab
  change (Qa - Qb) * (Qa - Qb) = Qa - Qb
  rw [sub_mul, mul_sub, mul_sub, hQa, hnest.2, hnest.1, hQb,
    sub_self, sub_zero]

/-- Dilation transition through the Sonin layer removed between two apertures. -/
def evenSoninApertureLostTransition
    (a b r : ℝ) (hr : 1 < r) : evenSubspace →L[ℂ] evenSubspace :=
  evenSoninApertureLayer a b * evenDilationSum r hr *
    evenCentralSoninProjection b

/-- **Exact aperture restriction law.**  The difference between the larger-aperture Gram corner
and the compression of the smaller-aperture corner factors through the lost Sonin layer. -/
theorem evenCentralSoninQuadraticCorner_restrictionDefect
    {a b p q : ℝ} (hab : a ≤ b) (hp : 1 < p) (hq : 1 < q) :
    evenCentralSoninQuadraticCorner b p q hp hq -
        evenCentralSoninProjection b *
          evenCentralSoninQuadraticCorner a p q hp hq *
            evenCentralSoninProjection b =
      evenCentralSoninProjection b * evenDilationSum p hp *
        evenSoninApertureLayer a b * evenDilationSum q hq *
          evenCentralSoninProjection b := by
  let Qa := evenCentralSoninProjection a
  let Qb := evenCentralSoninProjection b
  let Dp := evenDilationSum p hp
  let Dq := evenDilationSum q hq
  have hQb : Qb * Qb = Qb := by
    dsimp only [Qb]
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier b).isIdempotentElem_starProjection
  have hnest : Qb * Qa = Qb ∧ Qa * Qb = Qb := by
    simpa only [Qa, Qb] using evenCentralSoninProjection_mul_of_le hab
  rw [evenCentralSoninQuadraticCorner_eq_mul,
    evenCentralSoninQuadraticCorner_eq_mul]
  have hcompress :
      Qb * (Qa * Dp * (1 - Qa) * Dq * Qa) * Qb =
        Qb * Dp * (1 - Qa) * Dq * Qb := by
    calc
      Qb * (Qa * Dp * (1 - Qa) * Dq * Qa) * Qb =
          (Qb * Qa) * Dp * (1 - Qa) * Dq * (Qa * Qb) := by
            noncomm_ring
      _ = Qb * Dp * (1 - Qa) * Dq * Qb := by
        rw [hnest.1, hnest.2]
  change Qb * Dp * (1 - Qb) * Dq * Qb -
      Qb * (Qa * Dp * (1 - Qa) * Dq * Qa) * Qb =
    Qb * Dp * (Qa - Qb) * Dq * Qb
  rw [hcompress]
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, map_sub]
  abel

/-- **Positive diagonal restriction defect.**  At one scale the aperture defect is exactly the
Gram square of the transition through the lost layer. -/
theorem evenCentralSoninQuadraticCorner_restrictionDefect_eq_adjoint_mul
    {a b r : ℝ} (hab : a ≤ b) (hr : 1 < r) :
    evenCentralSoninQuadraticCorner b r r hr hr -
        evenCentralSoninProjection b *
          evenCentralSoninQuadraticCorner a r r hr hr *
            evenCentralSoninProjection b =
      (evenSoninApertureLostTransition a b r hr)† *
        evenSoninApertureLostTransition a b r hr := by
  rw [evenCentralSoninQuadraticCorner_restrictionDefect hab hr hr]
  let L := evenSoninApertureLayer a b
  let D := evenDilationSum r hr
  let Qb := evenCentralSoninProjection b
  have hL : L * L = L := by
    simpa only [L] using evenSoninApertureLayer_mul_self hab
  have hAdj : (L * D * Qb)† = Qb * D * L := by
    change ContinuousLinearMap.adjoint ((L ∘L D) ∘L Qb) = Qb * D * L
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      adjoint_evenCentralSoninProjection, adjoint_evenDilationSum,
      adjoint_evenSoninApertureLayer]
    rfl
  change Qb * D * L * D * Qb = (L * D * Qb)† * (L * D * Qb)
  rw [hAdj]
  calc
    Qb * D * L * D * Qb = Qb * D * (L * L) * D * Qb := by rw [hL]
    _ = (Qb * D * L) * (L * D * Qb) := by noncomm_ring

/-! ## Principal Calkin normal form of the lost aperture layer -/

/-- Compressing a two-polarization shell by the formal Sonin complement at an intermediate
aperture removes exactly the inner part of the shell, modulo finite time-band operators. -/
theorem evenFormalSoninComplement_compress_twoPolarizationShell_compactEq
    {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    let E := 1 - evenIndicatorCutoff b - evenFourierCutoff b
    E * evenTwoPolarizationShell a c * E =ₖ
      evenTwoPolarizationShell b c := by
  let Aa := evenIndicatorCutoff a
  let Ab := evenIndicatorCutoff b
  let Ac := evenIndicatorCutoff c
  let Ra := evenFourierCutoff a
  let Rb := evenFourierCutoff b
  let Rc := evenFourierCutoff c
  let Xp := Ac - Aa
  let Xf := Rc - Ra
  let E := 1 - Ab - Rb
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  have hRbXp : IsCompactOperator (Rb * Xp) := by
    dsimp only [Xp]
    rw [mul_sub]
    exact (isCompactOperator_evenFourierIndicatorBlock b c hb).sub
      (isCompactOperator_evenFourierIndicatorBlock b a hb)
  have hXpRb : IsCompactOperator (Xp * Rb) := by
    dsimp only [Xp]
    rw [sub_mul]
    exact (isCompactOperator_evenIndicatorFourierBlock c b hc).sub
      (isCompactOperator_evenIndicatorFourierBlock a b ha)
  have hAbXf : IsCompactOperator (Ab * Xf) := by
    dsimp only [Xf]
    rw [mul_sub]
    exact (isCompactOperator_evenIndicatorFourierBlock b c hb).sub
      (isCompactOperator_evenIndicatorFourierBlock b a hb)
  have hXfAb : IsCompactOperator (Xf * Ab) := by
    dsimp only [Xf]
    rw [sub_mul]
    exact (isCompactOperator_evenFourierIndicatorBlock c b hc).sub
      (isCompactOperator_evenFourierIndicatorBlock a b ha)
  have hAbAc : Ab * Ac = Ab := by
    simpa only [Ab, Ac] using evenIndicatorCutoff_mul_of_le b c hbc
  have hAcAb : Ac * Ab = Ab := by
    simpa only [Ab, Ac] using evenIndicatorCutoff_mul_of_le_rev b c hbc
  have hAbAa : Ab * Aa = Aa := by
    simpa only [Aa, Ab] using evenIndicatorCutoff_mul_of_le_rev a b hab
  have hAaAb : Aa * Ab = Aa := by
    simpa only [Aa, Ab] using evenIndicatorCutoff_mul_of_le a b hab
  have hAbAb : Ab * Ab = Ab := by
    simpa only [Ab] using evenIndicatorCutoff_mul_of_le b b le_rfl
  have hphysExact : (1 - Ab) * Xp * (1 - Ab) = Ac - Ab := by
    have hleft : (1 - Ab) * Xp = Ac - Ab := by
      dsimp only [Xp]
      rw [sub_mul, one_mul, mul_sub, hAbAc, hAbAa]
      abel
    rw [hleft, mul_sub, mul_one, sub_mul, hAcAb, hAbAb]
    abel
  have hphys : E * Xp * E =ₖ Ac - Ab := by
    exact (CompactOperatorEq.sub_sandwich (1 - Ab) Rb Xp hRbXp hXpRb).trans
      (CompactOperatorEq.of_eq hphysExact)
  have hRbRc : Rb * Rc = Rb := by
    simpa only [Rb, Rc] using evenFourierCutoff_mul_of_le b c hbc
  have hRcRb : Rc * Rb = Rb := by
    simpa only [Rb, Rc] using evenFourierCutoff_mul_of_le_rev b c hbc
  have hRbRa : Rb * Ra = Ra := by
    simpa only [Ra, Rb] using evenFourierCutoff_mul_of_le_rev a b hab
  have hRaRb : Ra * Rb = Ra := by
    simpa only [Ra, Rb] using evenFourierCutoff_mul_of_le a b hab
  have hRbRb : Rb * Rb = Rb := by
    simpa only [Rb] using evenFourierCutoff_mul_of_le b b le_rfl
  have hfourExact : (1 - Rb) * Xf * (1 - Rb) = Rc - Rb := by
    have hleft : (1 - Rb) * Xf = Rc - Rb := by
      dsimp only [Xf]
      rw [sub_mul, one_mul, mul_sub, hRbRc, hRbRa]
      abel
    rw [hleft, mul_sub, mul_one, sub_mul, hRcRb, hRbRb]
    abel
  have hfour : E * Xf * E =ₖ Rc - Rb := by
    rw [show E = 1 - Rb - Ab by dsimp only [E]; abel]
    exact (CompactOperatorEq.sub_sandwich (1 - Rb) Ab Xf hAbXf hXfAb).trans
      (CompactOperatorEq.of_eq hfourExact)
  have hsum := CompactOperatorEq.add hphys hfour
  dsimp only [evenTwoPolarizationShell, E, Xp, Xf, Aa, Ab, Ac, Ra, Rb, Rc]
  simpa only [mul_add, add_mul, mul_assoc] using hsum

/-- Exact-relative strengthening of the compressed-shell law: every discarded mixed block lies in
the concrete Schatten-1 Sonin ideal, not merely in the compact ideal. -/
theorem evenFormalSoninComplement_compress_twoPolarizationShell_principalRelativeEq
    {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    let E := 1 - evenIndicatorCutoff b - evenFourierCutoff b
    E * evenTwoPolarizationShell a c * E =ᵣ
      evenTwoPolarizationShell b c := by
  let Aa := evenIndicatorCutoff a
  let Ab := evenIndicatorCutoff b
  let Ac := evenIndicatorCutoff c
  let Ra := evenFourierCutoff a
  let Rb := evenFourierCutoff b
  let Rc := evenFourierCutoff c
  let Xp := Ac - Aa
  let Xf := Rc - Ra
  let E := 1 - Ab - Rb
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  have hRbXp : IsSoninPrincipalRelativeIdeal (Rb * Xp) := by
    dsimp only [Rb, Xp, Ac, Aa]
    rw [mul_sub]
    exact (IsSoninPrincipalRelativeIdeal.fourierIndicator b c hb).sub
      (IsSoninPrincipalRelativeIdeal.fourierIndicator b a hb)
  have hXpRb : IsSoninPrincipalRelativeIdeal (Xp * Rb) := by
    dsimp only [Xp, Rb, Ac, Aa]
    rw [sub_mul]
    exact (IsSoninPrincipalRelativeIdeal.indicatorFourier c b hc).sub
      (IsSoninPrincipalRelativeIdeal.indicatorFourier a b ha)
  have hAbXf : IsSoninPrincipalRelativeIdeal (Ab * Xf) := by
    dsimp only [Ab, Xf, Rc, Ra]
    rw [mul_sub]
    exact (IsSoninPrincipalRelativeIdeal.indicatorFourier b c hb).sub
      (IsSoninPrincipalRelativeIdeal.indicatorFourier b a hb)
  have hXfAb : IsSoninPrincipalRelativeIdeal (Xf * Ab) := by
    dsimp only [Xf, Ab, Rc, Ra]
    rw [sub_mul]
    exact (IsSoninPrincipalRelativeIdeal.fourierIndicator c b hc).sub
      (IsSoninPrincipalRelativeIdeal.fourierIndicator a b ha)
  have hAbAc : Ab * Ac = Ab := by
    simpa only [Ab, Ac] using evenIndicatorCutoff_mul_of_le b c hbc
  have hAcAb : Ac * Ab = Ab := by
    simpa only [Ab, Ac] using evenIndicatorCutoff_mul_of_le_rev b c hbc
  have hAbAa : Ab * Aa = Aa := by
    simpa only [Aa, Ab] using evenIndicatorCutoff_mul_of_le_rev a b hab
  have hAaAb : Aa * Ab = Aa := by
    simpa only [Aa, Ab] using evenIndicatorCutoff_mul_of_le a b hab
  have hAbAb : Ab * Ab = Ab := by
    simpa only [Ab] using evenIndicatorCutoff_mul_of_le b b le_rfl
  have hphysExact : (1 - Ab) * Xp * (1 - Ab) = Ac - Ab := by
    have hleft : (1 - Ab) * Xp = Ac - Ab := by
      dsimp only [Xp]
      rw [sub_mul, one_mul, mul_sub, hAbAc, hAbAa]
      abel
    rw [hleft, mul_sub, mul_one, sub_mul, hAcAb, hAbAb]
    abel
  have hphys : E * Xp * E =ᵣ Ac - Ab :=
    (SoninPrincipalRelativeEq.sub_sandwich (1 - Ab) Rb Xp hRbXp hXpRb).trans
      (SoninPrincipalRelativeEq.of_eq hphysExact)
  have hRbRc : Rb * Rc = Rb := by
    simpa only [Rb, Rc] using evenFourierCutoff_mul_of_le b c hbc
  have hRcRb : Rc * Rb = Rb := by
    simpa only [Rb, Rc] using evenFourierCutoff_mul_of_le_rev b c hbc
  have hRbRa : Rb * Ra = Ra := by
    simpa only [Ra, Rb] using evenFourierCutoff_mul_of_le_rev a b hab
  have hRaRb : Ra * Rb = Ra := by
    simpa only [Ra, Rb] using evenFourierCutoff_mul_of_le a b hab
  have hRbRb : Rb * Rb = Rb := by
    simpa only [Rb] using evenFourierCutoff_mul_of_le b b le_rfl
  have hfourExact : (1 - Rb) * Xf * (1 - Rb) = Rc - Rb := by
    have hleft : (1 - Rb) * Xf = Rc - Rb := by
      dsimp only [Xf]
      rw [sub_mul, one_mul, mul_sub, hRbRc, hRbRa]
      abel
    rw [hleft, mul_sub, mul_one, sub_mul, hRcRb, hRbRb]
    abel
  have hfour : E * Xf * E =ᵣ Rc - Rb := by
    rw [show E = 1 - Rb - Ab by dsimp only [E]; abel]
    exact (SoninPrincipalRelativeEq.sub_sandwich (1 - Rb) Ab Xf hAbXf hXfAb).trans
      (SoninPrincipalRelativeEq.of_eq hfourExact)
  have hsum := SoninPrincipalRelativeEq.add hphys hfour
  dsimp only [evenTwoPolarizationShell, E, Xp, Xf, Aa, Ab, Ac, Ra, Rb, Rc]
  simpa only [mul_add, add_mul, mul_assoc] using hsum

/-- The normalized canonical window product already closes modulo the concrete principal-relative
ideal.  This upgrades the corpus's compact normal-state multiplication to its exact retained
Schatten-1 congruence. -/
theorem evenSoninWindowTranslation_mul_principalRelativeEq_normalized
    (a C₁ F₁ x C₂ F₂ y : ℝ)
    (ha : 0 < a) (haF₁ : a ≤ F₁) (haF₂ : a ≤ F₂)
    (hF₁C₁ : F₁ ≤ C₁) (hF₂C₂ : F₂ ≤ C₂)
    (hx : 0 < x) (hy : 0 < y) :
    evenSoninWindowTranslation a C₁ F₁ x hx *
        evenSoninWindowTranslation a C₂ F₂ y hy =ᵣ
      evenSoninWindowTranslation a
        (soninWindowComposeCeiling C₁ x C₂)
        (soninWindowComposeNormalizedFloor a C₁ F₁ x C₂ F₂ y)
        (x * y) (mul_pos hx hy) := by
  have hraw := evenSoninWindowTranslation_mul_principalRelativeEq
    a C₁ F₁ x C₂ F₂ y ha haF₁ haF₂ hF₁C₁ hF₂C₂ hx hy
  have hfloorle : soninWindowComposeFloor C₁ F₁ x C₂ F₂ ≤
      soninWindowComposeCeiling C₁ x C₂ := min_le_right _ _
  have hnorm := evenSoninWindowTranslation_normalize a
    (soninWindowComposeCeiling C₁ x C₂)
    (soninWindowComposeFloor C₁ F₁ x C₂ F₂) (x * y)
    hfloorle (mul_pos hx hy)
  exact hraw.trans (SoninPrincipalRelativeEq.of_eq (by
    simpa [soninWindowComposeNormalizedFloor] using hnorm))

/-- Canonical zero/live state composition realizes multiplication modulo the exact concrete
principal-relative ideal, not merely modulo arbitrary compact operators. -/
theorem soninWindowState_operator_mul_principalRelativeEq
    {a : ℝ} (ha : 0 < a) (s t : SoninWindowState a) :
    s.operator * t.operator =ᵣ (composeSoninWindowStates s t).operator := by
  cases s with
  | zero =>
      exact SoninPrincipalRelativeEq.of_eq (by simp [composeSoninWindowStates])
  | live d =>
      cases t with
      | zero =>
          exact SoninPrincipalRelativeEq.of_eq (by simp [composeSoninWindowStates])
      | live e =>
          have hprod := evenSoninWindowTranslation_mul_principalRelativeEq_normalized
            a d.ceiling d.floor d.scale e.ceiling e.floor e.scale
            ha d.base_le_floor e.base_le_floor d.floor_lt_ceiling.le
            e.floor_lt_ceiling.le d.scale_pos e.scale_pos
          by_cases h : soninLiveComposeFloor d e < soninLiveComposeCeiling d e
          · let D : SoninLiveWindow a :=
              { ceiling := soninLiveComposeCeiling d e
                floor := soninLiveComposeFloor d e
                scale := soninLiveComposeScale d e
                scale_pos := soninLiveComposeScale_pos d e
                base_le_floor := base_le_soninLiveComposeFloor_of_lt d e h
                floor_lt_ceiling := h
                domain_le := domain_le_soninLiveComposeFloor_of_lt d e h }
            have hstate : composeSoninWindowStates
                (SoninWindowState.live d) (SoninWindowState.live e) =
                SoninWindowState.live D := by
              simp [composeSoninWindowStates, composeSoninLiveWindows, h, D]
            rw [hstate]
            simpa [D, soninLiveComposeCeiling, soninLiveComposeFloor,
              soninLiveComposeScale] using hprod
          · have hfloorle : soninLiveComposeFloor d e ≤ soninLiveComposeCeiling d e :=
              min_le_right _ _
            have heq : soninLiveComposeFloor d e = soninLiveComposeCeiling d e :=
              le_antisymm hfloorle (le_of_not_gt h)
            have hzero : evenSoninWindowTranslation a
                (soninLiveComposeCeiling d e) (soninLiveComposeFloor d e)
                (soninLiveComposeScale d e) (soninLiveComposeScale_pos d e) = 0 := by
              rw [heq]
              simp [evenSoninWindowTranslation, evenPhysicalWindowTranslation,
                evenFourierWindowTranslation]
            have hprod' : (SoninWindowState.live d).operator *
                (SoninWindowState.live e).operator =ᵣ 0 := by
              refine hprod.trans (SoninPrincipalRelativeEq.of_eq ?_)
              simpa [soninLiveComposeCeiling, soninLiveComposeFloor,
                soninLiveComposeScale] using hzero
            simpa [composeSoninWindowStates, composeSoninLiveWindows, h] using hprod'

/-- **Exact Calkin normal form of the strict aperture defect.**  Once the dilation crosses the
lost aperture layer, the positive restriction defect is the two-polarization shell from `r*a` to
`r*b`, modulo compact operators. -/
theorem evenCentralSoninQuadraticCorner_restrictionDefect_compactEq_shell
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    evenCentralSoninQuadraticCorner b r r hr hr -
        evenCentralSoninProjection b *
          evenCentralSoninQuadraticCorner a r r hr hr *
            evenCentralSoninProjection b =ₖ
      evenTwoPolarizationShell (r * a) (r * b) := by
  let Qb := evenCentralSoninProjection b
  let E := 1 - evenIndicatorCutoff b - evenFourierCutoff b
  let Ga := evenCentralSoninQuadraticCorner a r r hr hr
  let Gb := evenCentralSoninQuadraticCorner b r r hr hr
  let Sa := evenTwoPolarizationShell a (r * a)
  let Sb := evenTwoPolarizationShell b (r * b)
  let Smid := evenTwoPolarizationShell b (r * a)
  let Slost := evenTwoPolarizationShell (r * a) (r * b)
  have hb : 0 < b := ha.trans hab
  have hra : 0 < r * a := mul_pos (zero_lt_one.trans hr) ha
  have hrb : 0 < r * b := mul_pos (zero_lt_one.trans hr) hb
  have hGa : Ga =ₖ Sa := by
    simpa only [Ga, Sa, evenCentralSoninQuadraticCorner] using!
      evenCentralSoninDilationCorner_adjoint_mul_compactEq_shell a r ha hr
  have hGb : Gb =ₖ Sb := by
    simpa only [Gb, Sb, evenCentralSoninQuadraticCorner] using!
      evenCentralSoninDilationCorner_adjoint_mul_compactEq_shell b r hb hr
  have hQb : Qb =ₖ E := by
    simpa only [Qb, E] using evenCentralSoninProjection_compactEq_complement b hb
  have hcompressed : Qb * Ga * Qb =ₖ Smid := by
    have hmul := CompactOperatorEq.mul (CompactOperatorEq.mul hQb hGa) hQb
    exact hmul.trans
      (by
        simpa only [E, Sa, Smid] using
          evenFormalSoninComplement_compress_twoPolarizationShell_compactEq
            ha hab.le hbr.le)
  have hsub := CompactOperatorEq.sub hGb hcompressed
  have hshellSub : Sb - Smid = Slost := by
    dsimp only [Sb, Smid, Slost, evenTwoPolarizationShell]
    abel
  exact hsub.trans (CompactOperatorEq.of_eq hshellSub)

/-- **Principal-relative aperture closure.**  The strict positive restriction defect is not an
extra generator: modulo the concrete Schatten-1 Sonin ideal it is the canonical scale-one live
shell from `r*a` to `r*b` already present in the aperture-`b` principal algebra. -/
theorem evenCentralSoninQuadraticCorner_restrictionDefect_principalRelativeEq_shell
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    evenCentralSoninQuadraticCorner b r r hr hr -
        evenCentralSoninProjection b *
          evenCentralSoninQuadraticCorner a r r hr hr *
            evenCentralSoninProjection b =ᵣ
      evenTwoPolarizationShell (r * a) (r * b) := by
  let Qb := evenCentralSoninProjection b
  let E := 1 - evenIndicatorCutoff b - evenFourierCutoff b
  let Ga := evenCentralSoninQuadraticCorner a r r hr hr
  let Gb := evenCentralSoninQuadraticCorner b r r hr hr
  let Sa := evenTwoPolarizationShell a (r * a)
  let Sb := evenTwoPolarizationShell b (r * b)
  let Smid := evenTwoPolarizationShell b (r * a)
  let Slost := evenTwoPolarizationShell (r * a) (r * b)
  have hb : 0 < b := ha.trans hab
  have hGa : Ga =ᵣ Sa := by
    have h := evenCentralSoninQuadraticCorner_principalRelativeEq_shellTranslation
      a r r ha hr hr
    rw [evenSoninMixedShellTranslation_self a r ha hr] at h
    simpa only [Ga, Sa] using h
  have hGb : Gb =ᵣ Sb := by
    have h := evenCentralSoninQuadraticCorner_principalRelativeEq_shellTranslation
      b r r hb hr hr
    rw [evenSoninMixedShellTranslation_self b r hb hr] at h
    simpa only [Gb, Sb] using h
  have hQb : Qb =ᵣ E := by
    unfold SoninPrincipalRelativeEq
    simpa only [Qb, E, evenSoninProjectionCorrection] using
      (IsSoninPrincipalRelativeIdeal.projectionCorrection b hb)
  have hcompressed : Qb * Ga * Qb =ᵣ Smid := by
    have hmul := (hQb.mul hGa).mul hQb
    exact hmul.trans
      (by
        simpa only [E, Sa, Smid] using
          evenFormalSoninComplement_compress_twoPolarizationShell_principalRelativeEq
            ha hab.le hbr.le)
  have hsub : Gb - Qb * Ga * Qb =ᵣ Sb - Smid := by
    unfold SoninPrincipalRelativeEq at hGb hcompressed ⊢
    apply (hGb.sub hcompressed).of_eq
    abel
  have hshellSub : Sb - Smid = Slost := by
    dsimp only [Sb, Smid, Slost, evenTwoPolarizationShell]
    abel
  exact hsub.trans (SoninPrincipalRelativeEq.of_eq hshellSub)

/-- The diagonal restriction defect, packaged as an operator-valued aperture increment. -/
def evenSoninApertureRestrictionDefect
    (a b r : ℝ) (hr : 1 < r) : evenSubspace →L[ℂ] evenSubspace :=
  evenCentralSoninQuadraticCorner b r r hr hr -
    evenCentralSoninProjection b *
      evenCentralSoninQuadraticCorner a r r hr hr *
        evenCentralSoninProjection b

/-- **Exact compressed aperture cocycle.**  For nested apertures the direct restriction defect is
the last-step defect plus the earlier defect compressed to the final carrier.  No crossing or
compact quotient is used. -/
theorem evenSoninApertureRestrictionDefect_compressed_cocycle
    {a b c r : ℝ} (hbc : b ≤ c) (hr : 1 < r) :
    evenSoninApertureRestrictionDefect a c r hr =
      evenSoninApertureRestrictionDefect b c r hr +
        evenCentralSoninProjection c *
          evenSoninApertureRestrictionDefect a b r hr *
            evenCentralSoninProjection c := by
  rcases evenCentralSoninProjection_mul_of_le hbc with ⟨hcb, hbc'⟩
  have hcollapse : evenCentralSoninProjection c *
      (evenCentralSoninProjection b *
        (evenCentralSoninQuadraticCorner a r r hr hr * evenCentralSoninProjection c)) =
      evenCentralSoninProjection c *
        evenCentralSoninQuadraticCorner a r r hr hr * evenCentralSoninProjection c := by
    calc
      _ = (evenCentralSoninProjection c * evenCentralSoninProjection b) *
          (evenCentralSoninQuadraticCorner a r r hr hr *
            evenCentralSoninProjection c) :=
        (mul_assoc _ _ _).symm
      _ = evenCentralSoninProjection c *
          (evenCentralSoninQuadraticCorner a r r hr hr *
            evenCentralSoninProjection c) := by rw [hcb]
      _ = _ := (mul_assoc _ _ _).symm
  unfold evenSoninApertureRestrictionDefect
  rw [mul_sub, sub_mul]
  noncomm_ring [hcb, hbc']
  rw [hcollapse]
  simp only [mul_assoc]

/-- **Aperture anomaly cocycle.**  In one strict crossing chamber, restriction from `a` to `c`
equals the sum of the successive `a`-to-`b` and `b`-to-`c` defects modulo the exact Schatten-1
Sonin ideal.  Thus aperture loss is an additive positive principal-shell cocycle. -/
theorem evenSoninApertureRestrictionDefect_principalRelative_cocycle
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    evenSoninApertureRestrictionDefect a c r hr =ᵣ
      evenSoninApertureRestrictionDefect a b r hr +
        evenSoninApertureRestrictionDefect b c r hr := by
  have hb : 0 < b := ha.trans hab
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hbra : b < r * a := hbc.trans hcr
  have hcrb : c < r * b := hcr.trans (mul_lt_mul_of_pos_left hab hr0)
  have hac := evenCentralSoninQuadraticCorner_restrictionDefect_principalRelativeEq_shell
    ha (hab.trans hbc) hr hcr
  have hab' := evenCentralSoninQuadraticCorner_restrictionDefect_principalRelativeEq_shell
    ha hab hr hbra
  have hbc' := evenCentralSoninQuadraticCorner_restrictionDefect_principalRelativeEq_shell
    hb hbc hr hcrb
  have hshell : evenTwoPolarizationShell (r * a) (r * c) =
      evenTwoPolarizationShell (r * a) (r * b) +
        evenTwoPolarizationShell (r * b) (r * c) := by
    dsimp only [evenTwoPolarizationShell]
    abel
  exact hac.trans (SoninPrincipalRelativeEq.of_eq hshell) |>.trans
    (hab'.add hbc').symm

/-- Trace-class curvature left after replacing the exact compressed aperture cocycle by ordinary
addition.  The principal quotient is flat, so this is the complete scalar counterterm channel. -/
def evenSoninApertureRestrictionCurvature
    (a b c r : ℝ) (hr : 1 < r) : evenSubspace →L[ℂ] evenSubspace :=
  evenSoninApertureRestrictionDefect a c r hr -
    evenSoninApertureRestrictionDefect a b r hr -
      evenSoninApertureRestrictionDefect b c r hr

/-- In a strict crossing chamber the whole aperture curvature lies in the concrete Sonin
principal-relative ideal. -/
theorem evenSoninApertureRestrictionCurvature_mem_principalRelativeIdeal
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    IsSoninPrincipalRelativeIdeal
      (evenSoninApertureRestrictionCurvature a b c r hr) := by
  have h := evenSoninApertureRestrictionDefect_principalRelative_cocycle
    ha hab hbc hr hcr
  unfold SoninPrincipalRelativeEq at h
  apply h.of_eq
  unfold evenSoninApertureRestrictionCurvature
  abel

/-- Consequently the aperture curvature has an ordinary trace: no noncompact ambiguity remains
after the logarithmic principal cocycle is removed. -/
theorem evenSoninApertureRestrictionCurvature_memSchattenClass_one
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    MemSchattenClass 1 (evenSoninApertureRestrictionCurvature a b c r hr) :=
  (evenSoninApertureRestrictionCurvature_mem_principalRelativeIdeal
    ha hab hbc hr hcr).memSchattenClass_one

/-- Canonical live normal-state window carried by a strict lost-aperture defect. -/
def soninApertureLostLayerWindow
    (a b r : ℝ) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) : SoninLiveWindow b where
  ceiling := r * b
  floor := r * a
  scale := 1
  scale_pos := zero_lt_one
  base_le_floor := hbr.le
  floor_lt_ceiling := mul_lt_mul_of_pos_left hab (zero_lt_one.trans hr)
  domain_le := by simpa using hbr.le

/-- The normal-state operator of the lost-aperture window is exactly its two-polarization shell. -/
theorem soninApertureLostLayerWindow_operator
    (a b r : ℝ) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    (soninApertureLostLayerWindow a b r hab hr hbr).operator =
      evenTwoPolarizationShell (r * a) (r * b) := by
  have hfloor : b ≤ r * a := hbr.le
  have hceil : r * a ≤ r * b :=
    (mul_le_mul_of_nonneg_left hab.le (zero_lt_one.trans hr).le)
  dsimp only [soninApertureLostLayerWindow, SoninLiveWindow.operator,
    SoninWindowState.operator, evenSoninWindowTranslation,
    evenPhysicalWindowTranslation, evenFourierWindowTranslation,
    evenTwoPolarizationShell]
  rw [evenDilationCLM_one]
  simp only [inv_one, evenDilationCLM_one, mul_one]
  have hp := evenIndicatorCutoff_shellComplementProduct
    (r * b) (r * a) b (hfloor.trans hceil)
  have hf := evenFourierCutoff_shellComplementProduct
    (r * b) (r * a) b (hfloor.trans hceil)
  rw [hp, hf, max_eq_left hfloor]

/-- **Aperture-capacity law.**  The principal cyclic mass of the strict lost layer is exactly the
logarithmic aperture ratio, independent of the dilation scale once crossing occurs. -/
theorem soninLiveWindowCyclicLogWeight_apertureLostLayer
    (a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    soninLiveWindowCyclicLogWeight
        (soninApertureLostLayerWindow a b r hab hr hbr) =
      Real.log b - Real.log a := by
  have hb : 0 < b := ha.trans hab
  rw [soninLiveWindowCyclicLogWeight]
  simp only [soninApertureLostLayerWindow, if_pos]
  rw [Real.log_mul (zero_lt_one.trans hr).ne' hb.ne',
    Real.log_mul (zero_lt_one.trans hr).ne' ha.ne']
  ring

/-! ## The lost layer is a principal, noncompact channel -/

/-- In the crossing regime `0 < a < d < b < r*a`, the lost-layer transition maps an orthonormal
inverse-dilated exterior shell asymptotically onto the normalized shell between `a` and `d`. -/
theorem evenSoninApertureLostTransition_pairedShell_tendsto
    {a d b r : ℝ} (ha : 0 < a) (had : a < d) (hdb : d < b)
    (hr : 1 < r) (hbr : b < r * a) :
    Tendsto (fun n =>
      ‖evenSoninApertureLostTransition a b r hr
          (inverseDilatedEvenShellEven a d r had hr n) -
        evenShellVectorEven a d had n‖) atTop (𝓝 0) := by
  let Qa := evenCentralSoninProjection a
  let Qb := evenCentralSoninProjection b
  let D := evenDilationSum r hr
  let B := (1 - Qb) * D * Qb
  let T := evenSoninApertureLostTransition a b r hr
  let f : ℕ → evenSubspace := inverseDilatedEvenShellEven a d r had hr
  let v : ℕ → evenSubspace := evenShellVectorEven a d had
  have hb : 0 < b := ha.trans (had.trans hdb)
  have hQb : Qb * Qb = Qb := by
    dsimp only [Qb]
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier b).isIdempotentElem_starProjection
  have hnest := evenCentralSoninProjection_mul_of_le (had.le.trans hdb.le)
  have hQaQb : Qa * Qb = Qb := by
    simpa only [Qa, Qb] using hnest.2
  have hTB : T = Qa * B := by
    have hQaQb_apply (x : evenSubspace) : Qa (Qb x) = Qb x := by
      exact DFunLike.congr_fun hQaQb x
    apply ContinuousLinearMap.ext
    intro x
    change (Qa - Qb) (D (Qb x)) = Qa ((1 - Qb) (D (Qb x)))
    simp only [sub_apply, one_apply_eq_self, map_sub, hQaQb_apply]
  have hB : Tendsto (fun n => ‖B (f n) - v n‖) atTop (𝓝 0) := by
    have h := evenCentralSoninDilationCorner_pairedShell_tendsto
      b a d r hb ha had hdb hr hbr
    have hQb_apply (x : evenSubspace) : Qb (Qb x) = Qb x := by
      exact DFunLike.congr_fun hQb x
    have hcorner_apply (x : evenSubspace) :
        evenCentralSoninDilationCorner b r hr (Qb x) = B x := by
      rw [evenCentralSoninDilationCorner_eq_mul]
      change (1 - Qb) (D (Qb (Qb x))) = (1 - Qb) (D (Qb x))
      rw [hQb_apply]
    have heq : (fun n => ‖B (f n) - v n‖) =
        (fun n => ‖evenCentralSoninDilationCorner b r hr (Qb (f n)) - v n‖) := by
      funext n
      rw [hcorner_apply]
    rw [heq]
    exact h
  have hQa : Tendsto (fun n => ‖Qa (v n) - v n‖) atTop (𝓝 0) := by
    change Tendsto (fun n =>
      ‖centralSoninProjection a (evenShellVector a d had n) -
        evenShellVector a d had n‖) atTop (𝓝 0)
    exact centralSoninProjection_evenShellVector_tendsto_general a d ha had
  have hQa_contract (x : evenSubspace) : ‖Qa x‖ ≤ ‖x‖ := by
    dsimp only [Qa]
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier a).norm_starProjection_apply_le x
  have hsum : Tendsto (fun n => ‖B (f n) - v n‖ + ‖Qa (v n) - v n‖)
      atTop (𝓝 0) := by
    simpa using hB.add hQa
  apply squeeze_zero (fun n => norm_nonneg _) ?_ hsum
  intro n
  have hdecomp : T (f n) - v n =
      Qa (B (f n) - v n) + (Qa (v n) - v n) := by
    rw [hTB, mul_apply_eq_comp, map_sub]
    abel
  rw [hdecomp]
  exact (norm_add_le _ _).trans
    (add_le_add (hQa_contract (B (f n) - v n)) le_rfl)

/-- **Sharp compact-distance obstruction.**  Every lost-layer transition crossing a strict
aperture annulus stays at distance at least one from every compact operator. -/
theorem one_le_norm_evenSoninApertureLostTransition_sub_compact
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) (K : evenSubspace →L[ℂ] evenSubspace)
    (hK : IsCompactOperator K) :
    1 ≤ ‖evenSoninApertureLostTransition a b r hr - K‖ := by
  let d := (a + b) / 2
  have had : a < d := by dsimp only [d]; linarith
  have hdb : d < b := by dsimp only [d]; linarith
  let f : ℕ → evenSubspace := inverseDilatedEvenShellEven a d r had hr
  let v : ℕ → evenSubspace := evenShellVectorEven a d had
  have hf : Orthonormal ℂ f := by
    simpa only [f] using inverseDilatedEvenShellEven_orthonormal a d r ha had hr
  have hv : ∀ n, ‖v n‖ = 1 := by
    intro n
    simpa only [v] using (evenShellVectorEven_orthonormal a d ha had).norm_eq_one n
  have hT : Tendsto (fun n =>
      ‖evenSoninApertureLostTransition a b r hr (f n) - v n‖)
      atTop (𝓝 0) := by
    simpa only [f, v] using
      evenSoninApertureLostTransition_pairedShell_tendsto ha had hdb hr hbr
  exact one_le_norm_sub_compact_of_approx
    (evenSoninApertureLostTransition a b r hr) f v
    (fun n => (hf.norm_eq_one n).le) (Orthonormal.weakly_tendsto_zero hf)
    hv hT K hK

/-- The lost Sonin aperture transition is never compact in the strict crossing regime. -/
theorem evenSoninApertureLostTransition_not_isCompactOperator
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    ¬ IsCompactOperator (evenSoninApertureLostTransition a b r hr) := by
  intro hcompact
  have h := one_le_norm_evenSoninApertureLostTransition_sub_compact
    ha hab hr hbr (evenSoninApertureLostTransition a b r hr) hcompact
  rw [sub_self] at h
  have hzero : ‖(0 : evenSubspace →L[ℂ] evenSubspace)‖ = (0 : ℝ) :=
    ContinuousLinearMap.opNorm_zero
  rw [hzero] at h
  norm_num at h

/-- **Noncompact positive restriction defect.**  The exact lost-layer Gram square cannot belong
to the compact, Schatten, or trace-class relative channel. -/
theorem evenCentralSoninQuadraticCorner_restrictionDefect_not_isCompactOperator
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    ¬ IsCompactOperator
      (evenCentralSoninQuadraticCorner b r r hr hr -
        evenCentralSoninProjection b *
          evenCentralSoninQuadraticCorner a r r hr hr *
            evenCentralSoninProjection b) := by
  intro hdefect
  let X := evenSoninApertureLostTransition a b r hr
  have hfactor :=
    evenCentralSoninQuadraticCorner_restrictionDefect_eq_adjoint_mul hab.le hr
  have hXX : IsCompactOperator ((X†) * X) := by
    rw [← hfactor]
    exact hdefect
  have hXXzero : CompactOperatorEq ((X†) * X)
      (0 : evenSubspace →L[ℂ] evenSubspace) := by
    unfold CompactOperatorEq
    simpa only [sub_zero] using hXX
  exact evenSoninApertureLostTransition_not_isCompactOperator ha hab hr hbr
    (isCompactOperator_of_adjoint_mul_compactEq_zero X hXXzero)

end RHTower
