import GaloisForLFunctions.RHTower.FieldOneFiniteStageThetaSoninIsomorphism
import GaloisForLFunctions.RHTower.HardyTitchmarshSemilocalSquare

/-!
# Hardy--Titchmarsh reading of the literal `θ_S`

Under the archimedean dual Hardy--Titchmarsh unitary `υ_∞`, the finite Euler operator
`E_S = ∏_{p∈S} (1 - p^{-1/2} U_p^*)` becomes multiplication by the finite Euler symbol
`σ_S(s) = ∏_{p∈S} (1 - p^{-1/2-is})`.  Hence the literal theta transport, read through the
unitary `Υ_S = υ_∞ ∘ w_∞⁻¹ ∘ w_S` of `L²(X_S)^{K_S}` onto the weighted Hardy--Titchmarsh line, is
`c · σ_S · υ_∞`: adjoining the places of `S` acts on representatives only through the Euler
symbol.  This is the finite-`S` form of the one-prime square of
`HardyTitchmarshSemilocalSquare`, and it describes both Sonin spaces of Theorem 4.6 on one line.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory IsDedekindDomain

/-- Intertwining is inherited by ordered products. -/
theorem fieldOne_list_prod_comp_intertwine {α E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (U : E →L[ℂ] F) (l : List α)
    (T : α → E →L[ℂ] E) (A : α → F →L[ℂ] F) (h : ∀ a ∈ l, A a ∘L U = U ∘L T a) :
    (l.map A).prod ∘L U = U ∘L (l.map T).prod := by
  induction l with
  | nil =>
    ext x
    rfl
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    ext x
    have hx := DFunLike.congr_fun hl x
    have hax := DFunLike.congr_fun ha ((l.map T).prod x)
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.comp_apply,
      mul_apply_eq_comp] at hx hax ⊢
    rw [hx, hax]

/-- Spectral Euler factors `∏_{p∈S} M_{1-p^{-1/2-is}}` on the weighted Hardy--Titchmarsh line,
in the order used by `fieldOneFiniteStageThetaEulerOperator`. -/
def fieldOneFiniteStageSpectralEulerOperator (S : Finset (HeightOneSpectrum ℤ)) :
    RHTower.ArchimedeanWeightedL2 →L[ℂ] RHTower.ArchimedeanWeightedL2 :=
  (S.attach.toList.map fun v =>
    RHTower.archimedeanPrimeLocalFactor (fieldOneFinitePlacePrime v.1 : ℝ)).prod

/-- `υ_∞` carries `E_S` to the spectral Euler operator. -/
theorem archimedeanDualHardyTitchmarshUnitary_thetaEulerOperator
    (S : Finset (HeightOneSpectrum ℤ)) (f : RHTower.evenSubspace) :
    RHTower.archimedeanDualHardyTitchmarshUnitary (fieldOneFiniteStageThetaEulerOperator S f) =
      fieldOneFiniteStageSpectralEulerOperator S
        (RHTower.archimedeanDualHardyTitchmarshUnitary f) := by
  have h := fieldOne_list_prod_comp_intertwine
    (RHTower.archimedeanDualHardyTitchmarshUnitary :
      RHTower.evenSubspace →L[ℂ] RHTower.ArchimedeanWeightedL2)
    S.attach.toList (fieldOneFiniteStageThetaEulerTerm S)
    (fun v => RHTower.archimedeanPrimeLocalFactor (fieldOneFinitePlacePrime v.1 : ℝ))
    (fun v _ => RHTower.archimedeanPrimeLocalFactor_comp_dualUnitary _
      (fieldOneFinitePlacePrime_real_gt_one v.1))
  exact (DFunLike.congr_fun h f).symm

/-- The local symbol `1 - p^{-1/2-is}` of the spectral factor `archimedeanPrimeLocalFactor p`. -/
def fieldOneSpectralPrimeSymbol (p s : ℝ) : ℂ :=
  1 - ((Real.sqrt p : ℂ)⁻¹) * (RHTower.MellinL2.mellinCharacter p s)⁻¹

/-- The finite Euler symbol `σ_S(s) = ∏_{p∈S} (1 - p^{-1/2-is})`. -/
def fieldOneFiniteStageEulerSymbol (S : Finset (HeightOneSpectrum ℤ)) (s : ℝ) : ℂ :=
  (S.attach.toList.map fun v =>
    fieldOneSpectralPrimeSymbol (fieldOneFinitePlacePrime v.1 : ℝ) s).prod

theorem fieldOne_list_prod_archimedeanPrimeLocalFactor_ae {α : Type*} (l : List α)
    (p : α → ℝ) (g : RHTower.ArchimedeanWeightedL2) :
    (l.map fun a => RHTower.archimedeanPrimeLocalFactor (p a)).prod g =ᵐ[
        RHTower.archimedeanWeightedMeasure]
      fun s => (l.map fun a => fieldOneSpectralPrimeSymbol (p a) s).prod * g s := by
  induction l with
  | nil =>
    filter_upwards with s
    simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    filter_upwards [RHTower.archimedeanPrimeLocalFactor_ae (p a)
        ((l.map fun a => RHTower.archimedeanPrimeLocalFactor (p a)).prod g), ih] with s h1 h2
    rw [h1, h2, fieldOneSpectralPrimeSymbol]
    ring

/-- The spectral Euler operator is multiplication by the finite Euler symbol. -/
theorem fieldOneFiniteStageSpectralEulerOperator_ae (S : Finset (HeightOneSpectrum ℤ))
    (g : RHTower.ArchimedeanWeightedL2) :
    fieldOneFiniteStageSpectralEulerOperator S g =ᵐ[RHTower.archimedeanWeightedMeasure]
      fun s => fieldOneFiniteStageEulerSymbol S s * g s :=
  fieldOne_list_prod_archimedeanPrimeLocalFactor_ae S.attach.toList
    (fun v => (fieldOneFinitePlacePrime v.1 : ℝ)) g

/-- Hardy--Titchmarsh realization `Υ_S = υ_∞ ∘ w_∞⁻¹ ∘ w_S` of `L²(X_S)^{K_S}`. -/
def fieldOneFiniteStageClassHardyTitchmarshUnitary (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageClassModuleOneInvariantSubmodule S ≃ₗᵢ[ℂ]
      RHTower.ArchimedeanWeightedL2 :=
  (fieldOneFiniteStageSourceUnitary S).trans
    (fieldOneEvenToPositiveUnitsHaarUnitary.symm.trans
      RHTower.archimedeanDualHardyTitchmarshUnitary)

/-- **Hardy--Titchmarsh compatibility of `θ_S`.**  `Υ_S (θ_S f) = c · σ_S · υ_∞ f`. -/
theorem fieldOneFiniteStageClassHardyTitchmarshUnitary_literalTheta
    (S : Finset (HeightOneSpectrum ℤ)) (f : RHTower.evenSubspace) :
    fieldOneFiniteStageClassHardyTitchmarshUnitary S
        (fieldOneFiniteStageLiteralThetaTransportEquiv S f) =
      fieldOneThetaSourceNormalization •
        fieldOneFiniteStageSpectralEulerOperator S
          (RHTower.archimedeanDualHardyTitchmarshUnitary f) := by
  change RHTower.archimedeanDualHardyTitchmarshUnitary
      (fieldOneEvenToPositiveUnitsHaarUnitary.symm
        (fieldOneFiniteStageSourceUnitary S (fieldOneFiniteStageLiteralThetaTransportEquiv S f))) = _
  rw [fieldOneFiniteStageSourceUnitary_literalThetaTransport, map_smul, map_smul,
    LinearIsometryEquiv.symm_apply_apply, archimedeanDualHardyTitchmarshUnitary_thetaEulerOperator]

theorem fieldOneFiniteStageClassHardyTitchmarshUnitary_literalTheta_ae
    (S : Finset (HeightOneSpectrum ℤ)) (f : RHTower.evenSubspace) :
    fieldOneFiniteStageClassHardyTitchmarshUnitary S
        (fieldOneFiniteStageLiteralThetaTransportEquiv S f) =ᵐ[
        RHTower.archimedeanWeightedMeasure]
      fun s => fieldOneThetaSourceNormalization * fieldOneFiniteStageEulerSymbol S s *
        RHTower.archimedeanDualHardyTitchmarshUnitary f s := by
  rw [fieldOneFiniteStageClassHardyTitchmarshUnitary_literalTheta]
  filter_upwards [Lp.coeFn_smul fieldOneThetaSourceNormalization
      (fieldOneFiniteStageSpectralEulerOperator S (RHTower.archimedeanDualHardyTitchmarshUnitary f)),
    fieldOneFiniteStageSpectralEulerOperator_ae S
      (RHTower.archimedeanDualHardyTitchmarshUnitary f)] with s h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, mul_assoc]

/-- On the Sonin level: the Hardy--Titchmarsh image of `Sonin_λ(X_S)` is `c · σ_S` times the
Hardy--Titchmarsh image of `Sonin_λ(ℝ)`. -/
theorem fieldOneFiniteStageClassHardyTitchmarshUnitary_soninThetaEquiv
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) (f : RHTower.evenCentralSoninCarrier lam) :
    fieldOneFiniteStageClassHardyTitchmarshUnitary S (fieldOneFiniteStageSoninThetaEquiv S lam f) =
      fieldOneThetaSourceNormalization •
        fieldOneFiniteStageSpectralEulerOperator S
          (RHTower.archimedeanDualHardyTitchmarshUnitary f.1) :=
  fieldOneFiniteStageClassHardyTitchmarshUnitary_literalTheta S f.1

end

end GaloisForLFunctions.RHTower
