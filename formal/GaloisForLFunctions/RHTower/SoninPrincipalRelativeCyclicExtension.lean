import GaloisForLFunctions.RHTower.SoninApertureRestrictionDefect
import GaloisForLFunctions.RHTower.SoninPrincipalRelativeTraceSplitting

/-!
# Cyclic extension of the principal Sonin trace across the relative ideal

The canonical logarithmic trace lives on the faithful zero/live normal-state semigroup, and the
ordinary operator trace lives on the exact Sonin principal-relative ideal.  This module glues the
two into a single functional on the concrete operator system

`T = s.operator + K`,  `s` a canonical window state, `K` in the relative ideal,

and proves that the glued functional is a trace for the genuine operator product.

Two facts make the gluing unconditional.  Faithfulness of the zero/live normal form forces the
decomposition to be unique, because the relative ideal consists of compact operators.  Exactness of
the two polarization multiplication laws makes the residual of a state composition literally the sum
of the two cross-polarization products, and each cross product factors as a physical band times a
Fourier band, hence is Schatten-1.  Since a Schatten-1 operator is Hilbert--Schmidt, the residual
trace is symmetric in its two arguments, which is exactly the missing cyclicity input: the ordinary
trace already commutes past the ideal, and the logarithmic weight already commutes past the state
product.
-/

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

namespace RHTower

open ContinuousLinearMap

section SchattenHilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A Schatten-1 operator is Hilbert--Schmidt: its canonical trace-class factorization exhibits it
as a bounded operator composed with a Hilbert--Schmidt operator. -/
theorem MemSchattenClass.one_isHilbertSchmidt {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) : T.IsHilbertSchmidt := by
  obtain ⟨S, U, _, hU, hfac⟩ := hT.one_isTraceClass
  rw [hfac]
  exact hU.comp_left S

end SchattenHilbertSchmidt

section Bands

/-- The physical band of a physical window translation is a left unit for it. -/
theorem evenIndicatorBand_mul_physicalWindowTranslation
    (a C F x : ℝ) (hFC : F ≤ C) (hx : 0 < x) :
    (evenIndicatorCutoff C - evenIndicatorCutoff F) *
        evenPhysicalWindowTranslation a C F x hx =
      evenPhysicalWindowTranslation a C F x hx := by
  unfold evenPhysicalWindowTranslation
  rw [← mul_assoc, ← mul_assoc, evenIndicatorShell_mul_self F C hFC]

/-- The Fourier band of a Fourier window translation is a left unit for it. -/
theorem evenFourierBand_mul_fourierWindowTranslation
    (a C F x : ℝ) (hFC : F ≤ C) (hx : 0 < x) :
    (evenFourierCutoff C - evenFourierCutoff F) *
        evenFourierWindowTranslation a C F x hx =
      evenFourierWindowTranslation a C F x hx := by
  unfold evenFourierWindowTranslation
  rw [← mul_assoc, ← mul_assoc, evenFourierShell_mul_self F C hFC]

end Bands

section HalfCrossBlocks

/-- A physical window followed by a bare Fourier band already lies in the concrete relative
ideal: the dilation moves the Fourier band to the left of the physical band, producing a finite
time--band block. -/
theorem physicalWindow_mul_evenFourierDiff_mem_principalRelativeIdeal
    (a b c d e x : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) :
    IsSoninPrincipalRelativeIdeal
      (((evenIndicatorCutoff b - evenIndicatorCutoff c) * evenDilationCLM x hx *
          (1 - evenIndicatorCutoff a) *
        (evenFourierCutoff d - evenFourierCutoff e) :
          evenSubspace →L[Complex] evenSubspace)) := by
  let A := evenIndicatorCutoff a
  let AB := evenIndicatorCutoff b - evenIndicatorCutoff c
  let RD := evenFourierCutoff (x * d) - evenFourierCutoff (x * e)
  let Ax := evenIndicatorCutoff (x⁻¹ * a)
  let Ux := evenDilationCLM x hx
  have hmoveA : Ux * (1 - A) = (1 - Ax) * Ux := by
    have h := evenDilationCLM_mul_evenIndicatorCutoff a x hx
    change Ux * A = Ax * Ux at h
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  have hmoveR : Ux * (evenFourierCutoff d - evenFourierCutoff e) = RD * Ux := by
    have hd' := evenDilationCLM_mul_evenFourierCutoff d x hx
    have he' := evenDilationCLM_mul_evenFourierCutoff e x hx
    change Ux * evenFourierCutoff d = evenFourierCutoff (x * d) * Ux at hd'
    change Ux * evenFourierCutoff e = evenFourierCutoff (x * e) * Ux at he'
    rw [mul_sub, hd', he', ← sub_mul]
  have hdirect : IsSoninPrincipalRelativeIdeal (AB * RD) :=
    evenIndicatorDiff_mul_evenFourierDiff_mem_principalRelativeIdeal
      b c (x * d) (x * e) hb hc
  have hAx : IsSoninPrincipalRelativeIdeal (Ax * RD) := by
    have h₁ := IsSoninPrincipalRelativeIdeal.indicatorFourier
      (x⁻¹ * a) (x * d) (mul_pos (inv_pos.mpr hx) ha)
    have h₂ := IsSoninPrincipalRelativeIdeal.indicatorFourier
      (x⁻¹ * a) (x * e) (mul_pos (inv_pos.mpr hx) ha)
    apply (h₁.sub h₂).of_eq
    dsimp only [Ax, RD]
    rw [mul_sub]
  have hbracket : IsSoninPrincipalRelativeIdeal
      ((AB * (1 - Ax) * RD : evenSubspace →L[Complex] evenSubspace)) := by
    have h := hdirect.sub (hAx.leftMul AB)
    apply h.of_eq
    calc
      AB * RD - AB * (Ax * RD) = AB * RD - (AB * Ax) * RD := by
        rw [mul_assoc]
      _ = (AB - AB * Ax) * RD := (sub_mul AB (AB * Ax) RD).symm
      _ = (AB * 1 - AB * Ax) * RD := by rw [mul_one]
      _ = AB * (1 - Ax) * RD := by
        congr 1
        exact (mul_sub AB 1 Ax).symm
  have heq :
      AB * Ux * (1 - A) * (evenFourierCutoff d - evenFourierCutoff e) =
        (AB * (1 - Ax) * RD) * Ux := by
    calc
      AB * Ux * (1 - A) * (evenFourierCutoff d - evenFourierCutoff e) =
          AB * (Ux * (1 - A)) * (evenFourierCutoff d - evenFourierCutoff e) := by
            simp only [mul_assoc]
      _ = AB * ((1 - Ax) * Ux) * (evenFourierCutoff d - evenFourierCutoff e) := by
            rw [hmoveA]
      _ = AB * (1 - Ax) * (Ux * (evenFourierCutoff d - evenFourierCutoff e)) := by
            simp only [mul_assoc]
      _ = AB * (1 - Ax) * (RD * Ux) := by rw [hmoveR]
      _ = (AB * (1 - Ax) * RD) * Ux := by simp only [mul_assoc]
  change IsSoninPrincipalRelativeIdeal
    ((AB * Ux * (1 - A) * (evenFourierCutoff d - evenFourierCutoff e) :
      evenSubspace →L[Complex] evenSubspace))
  rw [heq]
  exact hbracket.rightMul Ux

/-- A Fourier window followed by a bare physical band already lies in the concrete relative
ideal. -/
theorem fourierWindow_mul_evenIndicatorDiff_mem_principalRelativeIdeal
    (a b c d e x : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) :
    IsSoninPrincipalRelativeIdeal
      (((evenFourierCutoff b - evenFourierCutoff c) * evenDilationCLM x hx *
          (1 - evenFourierCutoff a) *
        (evenIndicatorCutoff d - evenIndicatorCutoff e) :
          evenSubspace →L[Complex] evenSubspace)) := by
  let R := evenFourierCutoff a
  let RB := evenFourierCutoff b - evenFourierCutoff c
  let AD := evenIndicatorCutoff (x⁻¹ * d) - evenIndicatorCutoff (x⁻¹ * e)
  let Rx := evenFourierCutoff (x * a)
  let Ux := evenDilationCLM x hx
  have hmoveR : Ux * (1 - R) = (1 - Rx) * Ux := by
    have h := evenDilationCLM_mul_evenFourierCutoff a x hx
    change Ux * R = Rx * Ux at h
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  have hmoveA : Ux * (evenIndicatorCutoff d - evenIndicatorCutoff e) = AD * Ux := by
    have hd' := evenDilationCLM_mul_evenIndicatorCutoff d x hx
    have he' := evenDilationCLM_mul_evenIndicatorCutoff e x hx
    change Ux * evenIndicatorCutoff d = evenIndicatorCutoff (x⁻¹ * d) * Ux at hd'
    change Ux * evenIndicatorCutoff e = evenIndicatorCutoff (x⁻¹ * e) * Ux at he'
    rw [mul_sub, hd', he', ← sub_mul]
  have hdirect : IsSoninPrincipalRelativeIdeal (RB * AD) :=
    evenFourierDiff_mul_evenIndicatorDiff_mem_principalRelativeIdeal
      b c (x⁻¹ * d) (x⁻¹ * e) hb hc
  have hRx : IsSoninPrincipalRelativeIdeal (Rx * AD) := by
    have h₁ := IsSoninPrincipalRelativeIdeal.fourierIndicator
      (x * a) (x⁻¹ * d) (mul_pos hx ha)
    have h₂ := IsSoninPrincipalRelativeIdeal.fourierIndicator
      (x * a) (x⁻¹ * e) (mul_pos hx ha)
    apply (h₁.sub h₂).of_eq
    dsimp only [Rx, AD]
    rw [mul_sub]
  have hbracket : IsSoninPrincipalRelativeIdeal
      ((RB * (1 - Rx) * AD : evenSubspace →L[Complex] evenSubspace)) := by
    have h := hdirect.sub (hRx.leftMul RB)
    apply h.of_eq
    calc
      RB * AD - RB * (Rx * AD) = RB * AD - (RB * Rx) * AD := by
        rw [mul_assoc]
      _ = (RB - RB * Rx) * AD := (sub_mul RB (RB * Rx) AD).symm
      _ = (RB * 1 - RB * Rx) * AD := by rw [mul_one]
      _ = RB * (1 - Rx) * AD := by
        congr 1
        exact (mul_sub RB 1 Rx).symm
  have heq :
      RB * Ux * (1 - R) * (evenIndicatorCutoff d - evenIndicatorCutoff e) =
        (RB * (1 - Rx) * AD) * Ux := by
    calc
      RB * Ux * (1 - R) * (evenIndicatorCutoff d - evenIndicatorCutoff e) =
          RB * (Ux * (1 - R)) * (evenIndicatorCutoff d - evenIndicatorCutoff e) := by
            simp only [mul_assoc]
      _ = RB * ((1 - Rx) * Ux) * (evenIndicatorCutoff d - evenIndicatorCutoff e) := by
            rw [hmoveR]
      _ = RB * (1 - Rx) * (Ux * (evenIndicatorCutoff d - evenIndicatorCutoff e)) := by
            simp only [mul_assoc]
      _ = RB * (1 - Rx) * (AD * Ux) := by rw [hmoveA]
      _ = (RB * (1 - Rx) * AD) * Ux := by simp only [mul_assoc]
  change IsSoninPrincipalRelativeIdeal
    ((RB * Ux * (1 - R) * (evenIndicatorCutoff d - evenIndicatorCutoff e) :
      evenSubspace →L[Complex] evenSubspace))
  rw [heq]
  exact hbracket.rightMul Ux

end HalfCrossBlocks

section CrossTrace

/-- **Cross-polarization trace symmetry.**  Neither factor is compact, yet both orders of a
physical window against a Fourier window are Schatten-1 and carry the same ordinary trace.  Cutting
each window down to its own band produces a Hilbert--Schmidt pair whose two products recover the two
orders. -/
theorem opTrace_physicalWindow_mul_fourierWindow_comm
    (a C₁ F₁ x C₂ F₂ y : ℝ) (ha : 0 < a)
    (haF₁ : a ≤ F₁) (haF₂ : a ≤ F₂)
    (hF₁C₁ : F₁ ≤ C₁) (hF₂C₂ : F₂ ≤ C₂)
    (hx : 0 < x) (hy : 0 < y) :
    opTrace (evenPhysicalWindowTranslation a C₁ F₁ x hx *
        evenFourierWindowTranslation a C₂ F₂ y hy) =
      opTrace (evenFourierWindowTranslation a C₂ F₂ y hy *
        evenPhysicalWindowTranslation a C₁ F₁ x hx) := by
  have hF₁pos : 0 < F₁ := lt_of_lt_of_le ha haF₁
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le hF₁pos hF₁C₁
  have hF₂pos : 0 < F₂ := lt_of_lt_of_le ha haF₂
  have hC₂pos : 0 < C₂ := lt_of_lt_of_le hF₂pos hF₂C₂
  set G : evenSubspace →L[Complex] evenSubspace :=
    evenIndicatorCutoff C₁ - evenIndicatorCutoff F₁ with hG
  set H : evenSubspace →L[Complex] evenSubspace :=
    evenFourierCutoff C₂ - evenFourierCutoff F₂ with hH
  set P : evenSubspace →L[Complex] evenSubspace :=
    evenPhysicalWindowTranslation a C₁ F₁ x hx with hP
  set Q : evenSubspace →L[Complex] evenSubspace :=
    evenFourierWindowTranslation a C₂ F₂ y hy with hQ
  have hGP : G * P = P := by
    rw [hG, hP]
    exact evenIndicatorBand_mul_physicalWindowTranslation a C₁ F₁ x hF₁C₁ hx
  have hHQ : H * Q = Q := by
    rw [hH, hQ]
    exact evenFourierBand_mul_fourierWindowTranslation a C₂ F₂ y hF₂C₂ hy
  have hPH : IsSoninPrincipalRelativeIdeal (P * H) := by
    rw [hP, hH]
    simpa only [evenPhysicalWindowTranslation] using
      physicalWindow_mul_evenFourierDiff_mem_principalRelativeIdeal
        a C₁ F₁ C₂ F₂ x ha hC₁pos hF₁pos hx
  have hQG : IsSoninPrincipalRelativeIdeal (Q * G) := by
    rw [hQ, hG]
    simpa only [evenFourierWindowTranslation] using
      fourierWindow_mul_evenIndicatorDiff_mem_principalRelativeIdeal
        a C₂ F₂ C₁ F₁ y⁻¹ ha hC₂pos hF₂pos (inv_pos.mpr hy)
  have hPQ : IsSoninPrincipalRelativeIdeal (P * Q) := by
    rw [hP, hQ]
    simpa only [evenPhysicalWindowTranslation, evenFourierWindowTranslation] using
      physicalWindow_mul_fourierWindow_mem_principalRelativeIdeal
        a C₁ F₁ C₂ F₂ x y⁻¹ ha hC₁pos hF₁pos hx (inv_pos.mpr hy)
  have hQP : IsSoninPrincipalRelativeIdeal (Q * P) := by
    rw [hQ, hP]
    simpa only [evenPhysicalWindowTranslation, evenFourierWindowTranslation] using
      fourierWindow_mul_physicalWindow_mem_principalRelativeIdeal
        a C₂ F₂ C₁ F₁ y⁻¹ x ha hC₂pos hF₂pos (inv_pos.mpr hy) hx
  have hprod₁ : (P * H) * (Q * G) = (P * Q) * G := by
    calc
      (P * H) * (Q * G) = P * ((H * Q) * G) := by
        simp only [mul_assoc]
      _ = P * (Q * G) := by rw [hHQ]
      _ = (P * Q) * G := by rw [mul_assoc]
  have hprod₂ : (Q * G) * (P * H) = (Q * P) * H := by
    calc
      (Q * G) * (P * H) = Q * ((G * P) * H) := by
        simp only [mul_assoc]
      _ = Q * (P * H) := by rw [hGP]
      _ = (Q * P) * H := by rw [mul_assoc]
  have htrace₁ : opTrace ((P * Q) * G) = opTrace (P * Q) := by
    have hcyc := hPQ.memSchattenClass_one.one_opTrace_comp_comm G
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def] at hcyc
    rw [← hcyc]
    congr 1
    calc
      G * (P * Q) = (G * P) * Q := by rw [mul_assoc]
      _ = P * Q := by rw [hGP]
  have htrace₂ : opTrace ((Q * P) * H) = opTrace (Q * P) := by
    have hcyc := hQP.memSchattenClass_one.one_opTrace_comp_comm H
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def] at hcyc
    rw [← hcyc]
    congr 1
    calc
      H * (Q * P) = (H * Q) * P := by rw [mul_assoc]
      _ = Q * P := by rw [hHQ]
  have hcross : opTrace ((P * H) * (Q * G)) = opTrace ((Q * G) * (P * H)) := by
    have hHS₁ := hPH.memSchattenClass_one.one_isHilbertSchmidt
    have hHS₂ := hQG.memSchattenClass_one.one_isHilbertSchmidt
    simpa only [ContinuousLinearMap.mul_def] using
      ContinuousLinearMap.opTrace_comp_comm hHS₁ hHS₂
  rw [← htrace₁, ← htrace₂, ← hprod₁, ← hprod₂]
  exact hcross

end CrossTrace

section StateResidual

/-- The exact residual by which the canonical state composition fails to be the operator
product. -/
def soninWindowStateResidual {a : ℝ} (s t : SoninWindowState a) :
    evenSubspace →L[Complex] evenSubspace :=
  s.operator * t.operator - (composeSoninWindowStates s t).operator

/-- Composed live states are always represented by the normalized composed window, including the
degenerate case where the composed window is empty. -/
theorem composeSoninWindowStates_operator_live {a : ℝ} (d e : SoninLiveWindow a) :
    (composeSoninWindowStates (SoninWindowState.live d)
        (SoninWindowState.live e)).operator =
      evenSoninWindowTranslation a (soninLiveComposeCeiling d e)
        (soninLiveComposeFloor d e) (soninLiveComposeScale d e)
        (soninLiveComposeScale_pos d e) := by
  by_cases h : soninLiveComposeFloor d e < soninLiveComposeCeiling d e
  · simp [composeSoninWindowStates, composeSoninLiveWindows, h,
      SoninWindowState.operator]
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
    rw [hzero]
    simp [composeSoninWindowStates, composeSoninLiveWindows, h,
      SoninWindowState.operator]

/-- **Exact cross-polarization residual.**  The whole failure of the canonical state product to be
the operator product is the sum of the two cross-polarization products; the same-polarization
products are exact. -/
theorem soninWindowStateResidual_live_eq_cross {a : ℝ} (d e : SoninLiveWindow a) :
    soninWindowStateResidual (SoninWindowState.live d) (SoninWindowState.live e) =
      evenPhysicalWindowTranslation a d.ceiling d.floor d.scale d.scale_pos *
          evenFourierWindowTranslation a e.ceiling e.floor e.scale e.scale_pos +
        evenFourierWindowTranslation a d.ceiling d.floor d.scale d.scale_pos *
          evenPhysicalWindowTranslation a e.ceiling e.floor e.scale e.scale_pos := by
  have hPP := evenPhysicalWindowTranslation_mul a d.ceiling d.floor d.scale
    e.ceiling e.floor e.scale e.base_le_floor d.floor_lt_ceiling.le
    e.floor_lt_ceiling.le d.scale_pos e.scale_pos
  have hFF := evenFourierWindowTranslation_mul a d.ceiling d.floor d.scale
    e.ceiling e.floor e.scale e.base_le_floor d.floor_lt_ceiling.le
    e.floor_lt_ceiling.le d.scale_pos e.scale_pos
  have hfloorle : soninWindowComposeFloor d.ceiling d.floor d.scale
      e.ceiling e.floor ≤ soninWindowComposeCeiling d.ceiling d.scale e.ceiling :=
    min_le_right _ _
  have hnorm := evenSoninWindowTranslation_normalize a
    (soninWindowComposeCeiling d.ceiling d.scale e.ceiling)
    (soninWindowComposeFloor d.ceiling d.floor d.scale e.ceiling e.floor)
    (d.scale * e.scale) hfloorle (mul_pos d.scale_pos e.scale_pos)
  have hcompose := composeSoninWindowStates_operator_live d e
  rw [soninWindowStateResidual, hcompose]
  have hstate : (SoninWindowState.live d).operator *
      (SoninWindowState.live e).operator =
        evenSoninWindowTranslation a
          (soninWindowComposeCeiling d.ceiling d.scale e.ceiling)
          (soninWindowComposeFloor d.ceiling d.floor d.scale e.ceiling e.floor)
          (d.scale * e.scale) (mul_pos d.scale_pos e.scale_pos) +
        (evenPhysicalWindowTranslation a d.ceiling d.floor d.scale d.scale_pos *
            evenFourierWindowTranslation a e.ceiling e.floor e.scale e.scale_pos +
          evenFourierWindowTranslation a d.ceiling d.floor d.scale d.scale_pos *
            evenPhysicalWindowTranslation a e.ceiling e.floor e.scale e.scale_pos) := by
    simp only [SoninWindowState.operator_live, evenSoninWindowTranslation,
      add_mul, mul_add]
    rw [hPP, hFF]
    abel
  rw [hstate]
  have hsame : evenSoninWindowTranslation a (soninLiveComposeCeiling d e)
      (soninLiveComposeFloor d e) (soninLiveComposeScale d e)
      (soninLiveComposeScale_pos d e) =
        evenSoninWindowTranslation a
          (soninWindowComposeCeiling d.ceiling d.scale e.ceiling)
          (soninWindowComposeFloor d.ceiling d.floor d.scale e.ceiling e.floor)
          (d.scale * e.scale) (mul_pos d.scale_pos e.scale_pos) := by
    rw [hnorm]
    rfl
  rw [hsame]
  abel

/-- The residual of any state composition lies in the exact relative ideal.  This is the corpus's
relative-ideal composition law read as a statement about the residual operator. -/
theorem soninWindowStateResidual_mem {a : ℝ} (ha : 0 < a) (s t : SoninWindowState a) :
    IsSoninPrincipalRelativeIdeal (soninWindowStateResidual s t) :=
  soninWindowState_operator_mul_principalRelativeEq ha s t

/-- **Residual trace symmetry.**  The exact composition residual carries the same ordinary trace in
both orders, even though its two summands are individually order dependent. -/
theorem opTrace_soninWindowStateResidual_comm
    {a : ℝ} (ha : 0 < a) (s t : SoninWindowState a) :
    opTrace (soninWindowStateResidual s t) =
      opTrace (soninWindowStateResidual t s) := by
  cases s with
  | zero =>
      cases t with
      | zero => rfl
      | live e =>
          have hleft : soninWindowStateResidual
              (SoninWindowState.zero : SoninWindowState a)
              (SoninWindowState.live e) = 0 := by
            simp [soninWindowStateResidual, composeSoninWindowStates,
              SoninWindowState.operator]
          have hright : soninWindowStateResidual (SoninWindowState.live e)
              (SoninWindowState.zero : SoninWindowState a) = 0 := by
            simp [soninWindowStateResidual, composeSoninWindowStates,
              SoninWindowState.operator]
          rw [hleft, hright]
  | live d =>
      cases t with
      | zero =>
          have hleft : soninWindowStateResidual (SoninWindowState.live d)
              (SoninWindowState.zero : SoninWindowState a) = 0 := by
            simp [soninWindowStateResidual, composeSoninWindowStates,
              SoninWindowState.operator]
          have hright : soninWindowStateResidual
              (SoninWindowState.zero : SoninWindowState a)
              (SoninWindowState.live d) = 0 := by
            simp [soninWindowStateResidual, composeSoninWindowStates,
              SoninWindowState.operator]
          rw [hleft, hright]
      | live e =>
          have hdF : 0 < d.floor := lt_of_lt_of_le ha d.base_le_floor
          have hdC : 0 < d.ceiling := hdF.trans d.floor_lt_ceiling
          have heF : 0 < e.floor := lt_of_lt_of_le ha e.base_le_floor
          have heC : 0 < e.ceiling := heF.trans e.floor_lt_ceiling
          have hPdFe : IsSoninPrincipalRelativeIdeal
              (evenPhysicalWindowTranslation a d.ceiling d.floor d.scale d.scale_pos *
                evenFourierWindowTranslation a e.ceiling e.floor e.scale e.scale_pos) := by
            simpa only [evenPhysicalWindowTranslation, evenFourierWindowTranslation] using
              physicalWindow_mul_fourierWindow_mem_principalRelativeIdeal
                a d.ceiling d.floor e.ceiling e.floor d.scale e.scale⁻¹ ha hdC hdF
                d.scale_pos (inv_pos.mpr e.scale_pos)
          have hFdPe : IsSoninPrincipalRelativeIdeal
              (evenFourierWindowTranslation a d.ceiling d.floor d.scale d.scale_pos *
                evenPhysicalWindowTranslation a e.ceiling e.floor e.scale e.scale_pos) := by
            simpa only [evenPhysicalWindowTranslation, evenFourierWindowTranslation] using
              fourierWindow_mul_physicalWindow_mem_principalRelativeIdeal
                a d.ceiling d.floor e.ceiling e.floor d.scale⁻¹ e.scale ha hdC hdF
                (inv_pos.mpr d.scale_pos) e.scale_pos
          have hPeFd : IsSoninPrincipalRelativeIdeal
              (evenPhysicalWindowTranslation a e.ceiling e.floor e.scale e.scale_pos *
                evenFourierWindowTranslation a d.ceiling d.floor d.scale d.scale_pos) := by
            simpa only [evenPhysicalWindowTranslation, evenFourierWindowTranslation] using
              physicalWindow_mul_fourierWindow_mem_principalRelativeIdeal
                a e.ceiling e.floor d.ceiling d.floor e.scale d.scale⁻¹ ha heC heF
                e.scale_pos (inv_pos.mpr d.scale_pos)
          have hFePd : IsSoninPrincipalRelativeIdeal
              (evenFourierWindowTranslation a e.ceiling e.floor e.scale e.scale_pos *
                evenPhysicalWindowTranslation a d.ceiling d.floor d.scale d.scale_pos) := by
            simpa only [evenPhysicalWindowTranslation, evenFourierWindowTranslation] using
              fourierWindow_mul_physicalWindow_mem_principalRelativeIdeal
                a e.ceiling e.floor d.ceiling d.floor e.scale⁻¹ d.scale ha heC heF
                (inv_pos.mpr e.scale_pos) d.scale_pos
          rw [soninWindowStateResidual_live_eq_cross d e,
            soninWindowStateResidual_live_eq_cross e d,
            opTrace_add_of_memSchattenClass_one
              hPdFe.memSchattenClass_one hFdPe.memSchattenClass_one,
            opTrace_add_of_memSchattenClass_one
              hPeFd.memSchattenClass_one hFePd.memSchattenClass_one]
          have h₁ := opTrace_physicalWindow_mul_fourierWindow_comm
            a d.ceiling d.floor d.scale e.ceiling e.floor e.scale ha
            d.base_le_floor e.base_le_floor d.floor_lt_ceiling.le
            e.floor_lt_ceiling.le d.scale_pos e.scale_pos
          have h₂ := opTrace_physicalWindow_mul_fourierWindow_comm
            a e.ceiling e.floor e.scale d.ceiling d.floor d.scale ha
            e.base_le_floor d.base_le_floor e.floor_lt_ceiling.le
            d.floor_lt_ceiling.le e.scale_pos d.scale_pos
          rw [h₁, ← h₂]
          ring

end StateResidual

section ExtendedTrace

/-- An operator presented as one canonical Sonin principal shell plus one exact relative
correction. -/
structure SoninPrincipalRelativeOperator (a : ℝ) where
  /-- Canonical zero/live normal state carrying the noncompact principal part. -/
  state : SoninWindowState a
  /-- Exact Schatten-1 correction. -/
  relative : evenSubspace →L[Complex] evenSubspace
  /-- The correction belongs to the concrete Sonin principal-relative ideal. -/
  relative_mem : IsSoninPrincipalRelativeIdeal relative

namespace SoninPrincipalRelativeOperator

variable {a : ℝ}

/-- The bounded operator represented by a principal-relative presentation. -/
def toOperator (X : SoninPrincipalRelativeOperator a) :
    evenSubspace →L[Complex] evenSubspace :=
  X.state.operator + X.relative

/-- The canonical trace extending the logarithmic principal weight by the ordinary operator
trace. -/
def extendedTrace (X : SoninPrincipalRelativeOperator a) : ℂ :=
  (soninWindowStateCyclicLogTrace X.state : ℂ) + opTrace X.relative

@[ext]
theorem ext {X Y : SoninPrincipalRelativeOperator a}
    (hstate : X.state = Y.state) (hrelative : X.relative = Y.relative) : X = Y := by
  cases X
  cases Y
  simp_all

/-- **Directness of the principal-relative presentation.**  Faithfulness of the zero/live normal
form determines both components from the represented operator. -/
theorem toOperator_injective (ha : 0 < a) :
    Function.Injective
      (toOperator : SoninPrincipalRelativeOperator a →
        evenSubspace →L[Complex] evenSubspace) := by
  intro X Y hXY
  have hdiff : X.state.operator - Y.state.operator = Y.relative - X.relative := by
    unfold toOperator at hXY
    calc
      X.state.operator - Y.state.operator =
          (X.state.operator + X.relative) - (Y.state.operator + X.relative) := by abel
      _ = (Y.state.operator + Y.relative) - (Y.state.operator + X.relative) := by
          rw [hXY]
      _ = Y.relative - X.relative := by abel
  have hcompact : X.state.operator =ₖ Y.state.operator := by
    rw [CompactOperatorEq, hdiff]
    exact (Y.relative_mem.sub X.relative_mem).isCompactOperator
  have hstate : X.state = Y.state :=
    (SoninWindowState.operator_compactEq_iff ha X.state Y.state).mp hcompact
  have hrelative : X.relative = Y.relative := by
    have hsame : X.state.operator + X.relative = X.state.operator + Y.relative := by
      unfold toOperator at hXY
      rw [hXY, hstate]
    exact add_left_cancel hsame
  exact ext hstate hrelative

/-- The extended trace depends only on the represented operator. -/
theorem extendedTrace_eq_of_toOperator_eq (ha : 0 < a)
    {X Y : SoninPrincipalRelativeOperator a} (hXY : toOperator X = toOperator Y) :
    extendedTrace X = extendedTrace Y := by
  rw [toOperator_injective ha hXY]

/-- Purely principal presentation of a canonical normal state. -/
def ofState (s : SoninWindowState a) : SoninPrincipalRelativeOperator a where
  state := s
  relative := 0
  relative_mem := IsSoninPrincipalRelativeIdeal.zero

@[simp] theorem toOperator_ofState (s : SoninWindowState a) :
    toOperator (ofState (a := a) s) = s.operator := by
  simp [toOperator, ofState]

/-- On principal shells the extension is the canonical logarithmic trace. -/
@[simp] theorem extendedTrace_ofState (s : SoninWindowState a) :
    extendedTrace (ofState (a := a) s) = (soninWindowStateCyclicLogTrace s : ℂ) := by
  simp [extendedTrace, ofState]

/-- Purely relative presentation of an exact correction. -/
def ofRelative {K : evenSubspace →L[Complex] evenSubspace}
    (hK : IsSoninPrincipalRelativeIdeal K) : SoninPrincipalRelativeOperator a where
  state := SoninWindowState.zero
  relative := K
  relative_mem := hK

@[simp] theorem toOperator_ofRelative
    {K : evenSubspace →L[Complex] evenSubspace}
    (hK : IsSoninPrincipalRelativeIdeal K) :
    toOperator (ofRelative (a := a) hK) = K := by
  simp [toOperator, ofRelative, SoninWindowState.operator]

/-- On the exact relative ideal the extension is the ordinary operator trace. -/
@[simp] theorem extendedTrace_ofRelative
    {K : evenSubspace →L[Complex] evenSubspace}
    (hK : IsSoninPrincipalRelativeIdeal K) :
    extendedTrace (ofRelative (a := a) hK) = opTrace K := by
  simp [extendedTrace, ofRelative, soninWindowStateCyclicLogTrace]

/-- Exact product of two principal-relative presentations. -/
def compose (ha : 0 < a) (X Y : SoninPrincipalRelativeOperator a) :
    SoninPrincipalRelativeOperator a where
  state := composeSoninWindowStates X.state Y.state
  relative := soninWindowStateResidual X.state Y.state +
    X.state.operator * Y.relative + X.relative * Y.state.operator +
    X.relative * Y.relative
  relative_mem :=
    (((soninWindowStateResidual_mem ha X.state Y.state).add
      (Y.relative_mem.leftMul X.state.operator)).add
        (X.relative_mem.rightMul Y.state.operator)).add
          (Y.relative_mem.leftMul X.relative)

/-- The presented product is the genuine operator product. -/
theorem toOperator_compose (ha : 0 < a) (X Y : SoninPrincipalRelativeOperator a) :
    toOperator (compose ha X Y) = toOperator X * toOperator Y := by
  unfold toOperator compose soninWindowStateResidual
  simp only [add_mul, mul_add]
  abel

/-- **Cyclic extension of the principal Sonin trace.**  The logarithmic normal-state weight and the
ordinary trace on the exact relative ideal glue to a single functional which is cyclic for the
genuine operator product. -/
theorem extendedTrace_compose_comm (ha : 0 < a)
    (X Y : SoninPrincipalRelativeOperator a) :
    extendedTrace (compose ha X Y) = extendedTrace (compose ha Y X) := by
  have hres := soninWindowStateResidual_mem ha X.state Y.state
  have hres' := soninWindowStateResidual_mem ha Y.state X.state
  have hXY₁ := Y.relative_mem.leftMul X.state.operator
  have hXY₂ := X.relative_mem.rightMul Y.state.operator
  have hXY₃ := Y.relative_mem.leftMul X.relative
  have hYX₁ := X.relative_mem.leftMul Y.state.operator
  have hYX₂ := Y.relative_mem.rightMul X.state.operator
  have hYX₃ := X.relative_mem.leftMul Y.relative
  have hstate : soninWindowStateCyclicLogTrace
      (composeSoninWindowStates X.state Y.state) =
        soninWindowStateCyclicLogTrace
          (composeSoninWindowStates Y.state X.state) :=
    soninWindowStateCyclicLogTrace_compose_comm ha X.state Y.state
  have hresidual : opTrace (soninWindowStateResidual X.state Y.state) =
      opTrace (soninWindowStateResidual Y.state X.state) :=
    opTrace_soninWindowStateResidual_comm ha X.state Y.state
  have hcross₁ : opTrace (X.state.operator * Y.relative) =
      opTrace (Y.relative * X.state.operator) := by
    simpa only [ContinuousLinearMap.mul_def] using
      Y.relative_mem.memSchattenClass_one.one_opTrace_comp_comm X.state.operator
  have hcross₂ : opTrace (X.relative * Y.state.operator) =
      opTrace (Y.state.operator * X.relative) := by
    simpa only [ContinuousLinearMap.mul_def] using
      (X.relative_mem.memSchattenClass_one.one_opTrace_comp_comm
        Y.state.operator).symm
  have hcross₃ : opTrace (X.relative * Y.relative) =
      opTrace (Y.relative * X.relative) := by
    simpa only [ContinuousLinearMap.mul_def] using
      (X.relative_mem.memSchattenClass_one.one_opTrace_comp_comm Y.relative).symm
  unfold extendedTrace compose
  simp only
  rw [opTrace_add_of_memSchattenClass_one
        ((hres.add hXY₁).add hXY₂).memSchattenClass_one hXY₃.memSchattenClass_one,
    opTrace_add_of_memSchattenClass_one
      (hres.add hXY₁).memSchattenClass_one hXY₂.memSchattenClass_one,
    opTrace_add_of_memSchattenClass_one
      hres.memSchattenClass_one hXY₁.memSchattenClass_one,
    opTrace_add_of_memSchattenClass_one
        ((hres'.add hYX₁).add hYX₂).memSchattenClass_one hYX₃.memSchattenClass_one,
    opTrace_add_of_memSchattenClass_one
      (hres'.add hYX₁).memSchattenClass_one hYX₂.memSchattenClass_one,
    opTrace_add_of_memSchattenClass_one
      hres'.memSchattenClass_one hYX₁.memSchattenClass_one,
    hstate, hresidual, hcross₁, hcross₂, hcross₃]
  ring

/-- Three-factor cyclicity of the extended trace. -/
theorem extendedTrace_compose_rotate (ha : 0 < a)
    (X Y Z : SoninPrincipalRelativeOperator a) :
    extendedTrace (compose ha (compose ha X Y) Z) =
      extendedTrace (compose ha Z (compose ha X Y)) :=
  extendedTrace_compose_comm ha (compose ha X Y) Z

end SoninPrincipalRelativeOperator

end ExtendedTrace

end RHTower

namespace RHTower

open ContinuousLinearMap

section GramCorner

/-- The actual CCM Gram corner has its canonical live window as principal part, with the difference
retained inside the exact relative ideal rather than as an unspecified compact error. -/
theorem SoninGramFactor.operator_principalRelativeEq_liveWindow
    (a : ℝ) (ha : 0 < a) (g : SoninGramFactor) :
    g.operator a =ᵣ (g.liveWindow a ha).operator := by
  have hcorner := evenCentralSoninQuadraticCorner_principalRelativeEq_shellTranslation
    a g.source g.target ha g.source_gt_one g.target_gt_one
  have hraw := evenSoninMixedShellTranslation_eq_window
    a g.source g.target g.source_gt_one g.target_gt_one
  have hsa : a < g.source * a := by
    nlinarith [mul_pos (sub_pos.mpr g.source_gt_one) ha]
  have hfloor : soninWindowNormalizedFloor a (g.source * a) a
      (g.source⁻¹ * g.target) = max a ((g.source * g.target⁻¹) * a) := by
    have hscale : (g.source⁻¹ * g.target)⁻¹ * a =
        (g.source * g.target⁻¹) * a := by field_simp
    rw [soninWindowNormalizedFloor, hscale]
    have hmaxlt : max a ((g.source * g.target⁻¹) * a) < g.source * a := by
      apply max_lt
      · exact hsa
      · have htinv : g.target⁻¹ < 1 := inv_lt_one_of_one_lt₀ g.target_gt_one
        nlinarith [mul_pos (zero_lt_one.trans g.source_gt_one) ha]
    rw [min_eq_left hmaxlt.le]
  have hnorm := evenSoninWindowTranslation_normalize a (g.source * a) a
    (g.source⁻¹ * g.target) hsa.le
    (mul_pos (inv_pos.mpr (zero_lt_one.trans g.source_gt_one))
      (zero_lt_one.trans g.target_gt_one))
  rw [hfloor] at hnorm
  refine hcorner.trans (SoninPrincipalRelativeEq.of_eq ?_)
  rw [hraw, hnorm]
  rfl

namespace SoninPrincipalRelativeOperator

/-- Canonical principal-relative presentation of one genuine CCM Gram corner. -/
def ofGramFactor (a : ℝ) (ha : 0 < a) (g : SoninGramFactor) :
    SoninPrincipalRelativeOperator a where
  state := SoninWindowState.live (g.liveWindow a ha)
  relative := g.operator a - (g.liveWindow a ha).operator
  relative_mem := g.operator_principalRelativeEq_liveWindow a ha

@[simp] theorem toOperator_ofGramFactor (a : ℝ) (ha : 0 < a) (g : SoninGramFactor) :
    toOperator (ofGramFactor a ha g) = g.operator a := by
  simp only [toOperator, ofGramFactor, SoninLiveWindow.operator]
  abel

/-- **Exact single-corner anomaly formula.**  The extended trace of a genuine Gram corner is its
logarithmic principal weight plus the ordinary trace of the exact relative residual. -/
theorem extendedTrace_ofGramFactor (a : ℝ) (ha : 0 < a) (g : SoninGramFactor) :
    extendedTrace (ofGramFactor a ha g) =
      ((if g.source = g.target then Real.log g.source else 0 : ℝ) : ℂ) +
        opTrace (g.operator a - (g.liveWindow a ha).operator) := by
  have hstate : soninWindowStateCyclicLogTrace
      (SoninWindowState.live (g.liveWindow a ha)) =
        soninGramFactorPrincipalCyclicTrace a ha g := rfl
  unfold extendedTrace ofGramFactor
  simp only
  rw [hstate, soninGramFactorPrincipalCyclicTrace_eq_ite]

/-- On the diagonal the extended trace reads the exact orbital length, independently of the
aperture, plus one ordinary trace-class residual. -/
theorem extendedTrace_ofGramFactor_diagonal (a r : ℝ) (ha : 0 < a) (hr : 1 < r) :
    extendedTrace (ofGramFactor a ha (soninDiagonalGramFactor r hr)) =
      (Real.log r : ℂ) +
        opTrace ((soninDiagonalGramFactor r hr).operator a -
          ((soninDiagonalGramFactor r hr).liveWindow a ha).operator) := by
  rw [extendedTrace_ofGramFactor]
  simp [soninDiagonalGramFactor]

end SoninPrincipalRelativeOperator

end GramCorner

section BilinearExtension

/-- Bilinear extended-trace pairing on the finite-support algebraic core of the principal-relative
system. -/
def soninPrincipalRelativePairTrace {a : ℝ} (ha : 0 < a)
    (A B : SoninPrincipalRelativeOperator a →₀ ℂ) : ℂ :=
  ∑ X ∈ A.support, ∑ Y ∈ B.support,
    A X * B Y *
      SoninPrincipalRelativeOperator.extendedTrace
        (SoninPrincipalRelativeOperator.compose ha X Y)

/-- **Cyclic finite-support extension.**  The bilinear extended-trace pairing is symmetric on the
whole finite-support core, principal and relative parts together. -/
theorem soninPrincipalRelativePairTrace_comm {a : ℝ} (ha : 0 < a)
    (A B : SoninPrincipalRelativeOperator a →₀ ℂ) :
    soninPrincipalRelativePairTrace ha A B =
      soninPrincipalRelativePairTrace ha B A := by
  rw [soninPrincipalRelativePairTrace, soninPrincipalRelativePairTrace,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  apply Finset.sum_congr rfl
  intro X _
  rw [SoninPrincipalRelativeOperator.extendedTrace_compose_comm ha X Y]
  ring

end BilinearExtension

end RHTower
