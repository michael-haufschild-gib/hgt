import GaloisForLFunctions.HTGeometry.HerglotzDiscreteSupportSeries
import GaloisForLFunctions.HTGeometry.HerglotzFullTranslationRegularizedFreeness

/-!
# Discrete-support full-translation Herglotz freeness

This module transports arbitrary-measure residual freeness through the exact isometric
identification `ℓ∞ ≃ L∞` for positive weighted Dirac measures and through the real constant
relating the regularized transform to its literal normally convergent meromorphic series.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory Set Topology Filter
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped ENNReal

noncomputable section

theorem exists_denseResidual_boundedSequence_regularizedHerglotz_fullTranslationFree
    {ε atoms : ℕ → ℝ} (hinj : Function.Injective atoms)
    (hε : ∀ n, 0 < ε n) (hH7 : DiscreteHerglotzH7 ε atoms) :
    ∃ Ufree : Set BoundedRealSequence,
      Dense Ufree ∧ Ufree ∈ residual BoundedRealSequence ∧
      ∀ u ∈ Ufree, ∀ (m : ℕ) (shift : InjectiveShiftConfiguration (Fin m)),
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z => ∫ t, regularizedHerglotzKernel t (z + shift.1 i) *
            (Real.exp (countableWeightedDiracLinftyEquiv hinj hε u t) : ℂ)
              ∂(HTGeometry.countableWeightedDirac ε atoms))
          (commonUpperTranslationDomain shift) := by
  let μ := HTGeometry.countableWeightedDirac ε atoms
  let e := countableWeightedDiracLinftyEquiv hinj hε
  let universalPhase : Set (Lp ℝ ⊤ μ) := {u | ∀
    (p : FiniteDifferentialPattern ℕ)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    herglotzExpandedPatternRelationHolds
      (row := CarrierPatternRow p) μ nevanlinnaWeight p.coefficientDegree p.orders
        (carrierPatternExponent p) u shift coeff →
      ∀ col, coeff col = 0}
  have hbase :=
    herglotz_fullTranslationRegularizedFreeness_denseResidual μ
      (infinite_support_countableWeightedDirac hinj hε)
      (integrable_nevanlinnaWeight_countableWeightedDirac_of_H7
        (fun n => (hε n).le) hH7)
  refine ⟨e.toHomeomorph ⁻¹' universalPhase, ?_, ?_, ?_⟩
  · simpa only [universalPhase, μ] using
      hbase.1.preimage e.toHomeomorph.isOpenMap
  · apply Filter.mem_map.mp
    simpa only [universalPhase, μ] using
      (tendsto_residual_of_isOpenMap
        e.toHomeomorph.continuous e.toHomeomorph.isOpenMap) hbase.2.1
  · intro u hu m shift
    change e.toHomeomorph u ∈ universalPhase at hu
    have heu : e.toHomeomorph u = e u := rfl
    rw [heu] at hu
    have hu' : e u ∈ {v | ∀
        (p : FiniteDifferentialPattern ℕ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
        herglotzExpandedPatternRelationHolds
          (row := CarrierPatternRow p) μ nevanlinnaWeight p.coefficientDegree p.orders
            (carrierPatternExponent p) v shift coeff →
          ∀ col, coeff col = 0} := by
      simpa only [universalPhase] using hu
    simpa only [μ, e] using hbase.2.2 (e u) hu' m shift

/-- **Discrete-support meromorphic corollary.** Under exact `(H7)` and escape of distinct poles,
one dense residual subset of literal `ℓ∞(ℝ)` makes every finite family of distinct complex
translates of the normally convergent series `(1)` differentially algebraically independent. -/
theorem exists_denseResidual_discreteHerglotzCauchy_fullTranslationFree
    {ε atoms : ℕ → ℝ} (hinj : Function.Injective atoms)
    (hε : ∀ n, 0 < ε n) (hH7 : DiscreteHerglotzH7 ε atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop) :
    ∃ Ufree : Set BoundedRealSequence,
      Dense Ufree ∧ Ufree ∈ residual BoundedRealSequence ∧
      ∀ u ∈ Ufree, ∀ (m : ℕ) (shift : InjectiveShiftConfiguration (Fin m)),
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z => discreteHerglotzCauchySeries ε atoms u (z + shift.1 i))
          (commonUpperTranslationDomain shift) := by
  obtain ⟨Ufree, hUdense, hUresidual, hUfree⟩ :=
    exists_denseResidual_boundedSequence_regularizedHerglotz_fullTranslationFree
      hinj hε hH7
  refine ⟨Ufree, hUdense, hUresidual, ?_⟩
  intro u hu m shift
  let C : ℂ := (discreteHerglotzRegularizationConstant ε atoms u : ℂ)
  let g : Fin m → ℂ → ℂ :=
    fun i z => discreteHerglotzCauchySeries ε atoms u (z + shift.1 i) - C
  have hopen := isOpen_commonUpperTranslationDomain shift
  have hseriesDiff :=
    differentiableOn_discreteHerglotzCauchySeries_off_poles hε hH7 hescape u
  have hpoleOpen := isOpen_compl_discreteHerglotzPoleSet hescape
  have hgSmooth : ∀ z ∈ commonUpperTranslationDomain shift, ∀ i,
      ContDiffAt ℂ (⊤ : ℕ∞) (g i) z := by
    intro z hz i
    have hw : z + shift.1 i ∈ (discreteHerglotzPoleSet atoms)ᶜ := by
      rw [Set.mem_compl_iff]
      rintro ⟨n, hn⟩
      have hpos := hz i
      rw [← hn] at hpos
      simp at hpos
    have hsmoothAt : ContDiffAt ℂ (⊤ : ℕ∞)
        (discreteHerglotzCauchySeries ε atoms u) (z + shift.1 i) :=
      ((hseriesDiff.analyticOnNhd hpoleOpen) (z + shift.1 i) hw).contDiffAt
    have hshift : ContDiffAt ℂ (⊤ : ℕ∞) (fun w : ℂ => w + shift.1 i) z :=
      contDiffAt_id.add contDiffAt_const
    exact (hsmoothAt.comp z hshift).sub contDiffAt_const
  intro hseries
  apply hUfree u hu m shift
  have hgDA : FamilyDifferentiallyAlgebraicOn g
      (commonUpperTranslationDomain shift) := by
    apply familyDifferentiallyAlgebraicOn_of_add_polynomial g
      (fun _ => Polynomial.C C) hgSmooth
    apply familyDifferentiallyAlgebraicOn_congr_of_isOpen hopen _ hseries
    intro i z hz
    simp [g, C]
  apply familyDifferentiallyAlgebraicOn_congr_of_isOpen hopen _ hgDA
  intro i z hz
  exact (integral_regularizedHerglotz_countableWeightedDirac_eq_series_sub_const
    hinj hε hH7 hescape u (ne_of_gt (hz i))).symm


end

end GaloisForLFunctions.HTGeometry
