import GaloisForLFunctions.RHTower.BurnolTheoremThreeOne
import GaloisForLFunctions.RHTower.SoninStripEvaluator
import GaloisForLFunctions.HTGeometry.MinimalCompleteSystem
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Burnol's literal aperture jet-vector system

The existing Burnol completeness theorem is stated through divisibility of the continued Mellin
transform.  This file realizes every zero jet as its actual Riesz vector in the extended even Sonin
space and transfers the divisibility threshold to dense span of that concrete vector family.

For positive aperture `a`, the resulting system is complete exactly when `1 ≤ a`.
-/

open Complex Set Filter MeasureTheory Topology
open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- A nontrivial zeta zero together with one jet index strictly below its multiplicity. -/
structure BurnolZetaJetIndex where
  point : ℂ
  zero : riemannZeta point = 0
  re_pos : 0 < point.re
  re_lt_one : point.re < 1
  jet : ℕ
  jet_lt : (jet : ℕ∞) < analyticOrderAt riemannZeta point

/-- The bounded continued-Mellin jet functional attached to a zeta zero and jet index. -/
def burnolZetaJetFunctional (a : ℝ) (ha : 0 < a) (i : BurnolZetaJetIndex) :
    soninEvenExtended a →L[ℂ] ℂ :=
  Classical.choose (exists_soninEvaluatorJet ha i.jet i.re_pos i.re_lt_one)

/-- The chosen functional evaluates the prescribed continued-Mellin jet. -/
theorem burnolZetaJetFunctional_apply (a : ℝ) (ha : 0 < a)
    (i : BurnolZetaJetIndex) (f : soninEvenExtended a) :
    burnolZetaJetFunctional a ha i f =
      iteratedDeriv i.jet (soninEval a ((f : SoninL2))) i.point :=
  Classical.choose_spec (exists_soninEvaluatorJet ha i.jet i.re_pos i.re_lt_one) f

/-- Riesz vector representing a continued-Mellin zero jet on the extended even Sonin space. -/
def burnolZetaJetVector (a : ℝ) (ha : 0 < a) (i : BurnolZetaJetIndex) :
    soninEvenExtended a :=
  (InnerProductSpace.toDual ℂ (soninEvenExtended a)).symm
    (burnolZetaJetFunctional a ha i)

/-- Inner product with the Riesz vector is the corresponding continued-Mellin jet. -/
theorem inner_burnolZetaJetVector (a : ℝ) (ha : 0 < a)
    (i : BurnolZetaJetIndex) (f : soninEvenExtended a) :
    ⟪burnolZetaJetVector a ha i, f⟫_ℂ =
      iteratedDeriv i.jet (soninEval a ((f : SoninL2))) i.point := by
  rw [burnolZetaJetVector, InnerProductSpace.toDual_symm_apply]
  exact burnolZetaJetFunctional_apply a ha i f

private theorem iteratedDeriv_soninEval_eq_zero_of_zeta_order_le
    {a : ℝ} (ha : 0 < a) (f : soninEvenExtended a) {rho : ℂ}
    (hre0 : 0 < rho.re) (hre1 : rho.re < 1)
    (horder : meromorphicOrderAt riemannZeta rho ≤
      meromorphicOrderAt (soninEval a ((f : SoninL2))) rho)
    {k : ℕ} (hk : (k : ℕ∞) < analyticOrderAt riemannZeta rho) :
    iteratedDeriv k (soninEval a ((f : SoninL2))) rho = 0 := by
  have hrho1 : rho ≠ 1 := by
    intro h
    rw [h] at hre1
    norm_num at hre1
  have hzeta : AnalyticAt ℂ riemannZeta rho := analyticAt_riemannZeta hrho1
  have heval : AnalyticAt ℂ (soninEval a ((f : SoninL2))) rho :=
    soninEval_analyticAt ha f.property.1 f.property.2 hre0 hre1
  rw [hzeta.meromorphicOrderAt_eq, heval.meromorphicOrderAt_eq] at horder
  induction heq : analyticOrderAt (soninEval a ((f : SoninL2))) rho with
  | top =>
      have hlocal : (soninEval a ((f : SoninL2))) =ᶠ[𝓝 rho] 0 :=
        analyticOrderAt_eq_top.mp heq
      simpa using hlocal.iteratedDeriv_eq k
  | coe n =>
      have hle : analyticOrderAt riemannZeta rho ≤ (n : ℕ∞) := by
        rw [heq] at horder
        induction hz : analyticOrderAt riemannZeta rho with
        | top => simp [hz] at horder
        | coe m =>
            rw [hz] at horder
            simp only [ENat.map_coe] at horder
            have hmnZ : (m : ℤ) ≤ (n : ℤ) := by
              exact_mod_cast horder
            exact ENat.coe_le_coe.mpr (by exact_mod_cast hmnZ)
      have hkn : k < n := by
        exact_mod_cast lt_of_lt_of_le hk hle
      exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero heval).mp
        (by rw [heq]) k hkn

private theorem zeta_order_le_soninEval_of_all_jet_inner_zero
    {a : ℝ} (ha : 0 < a) (f : soninEvenExtended a)
    (horth : ∀ i : BurnolZetaJetIndex, ⟪burnolZetaJetVector a ha i, f⟫_ℂ = 0) :
    AnnihilatesEvaluators a ((f : soninEvenExtended a) : SoninL2)
      (soninFourierBandConst a ((f : soninEvenExtended a) : SoninL2))
      (soninBandConst a ((f : soninEvenExtended a) : SoninL2)) := by
  intro rho hzero hre0 hre1
  have hfin : analyticOrderAt riemannZeta rho ≠ ⊤ :=
    analyticOrderAt_riemannZeta_ne_top_of_strip hre0 hre1
  let m : ℕ := (analyticOrderAt riemannZeta rho).toNat
  have hm : (m : ℕ∞) = analyticOrderAt riemannZeta rho := ENat.coe_toNat hfin
  have heval : AnalyticAt ℂ (soninEval a ((f : soninEvenExtended a) : SoninL2)) rho :=
    soninEval_analyticAt ha f.property.1 f.property.2 hre0 hre1
  have hjets : ∀ k < m,
      iteratedDeriv k (soninEval a ((f : soninEvenExtended a) : SoninL2)) rho = 0 := by
    intro k hk
    let i : BurnolZetaJetIndex :=
      { point := rho
        zero := hzero
        re_pos := hre0
        re_lt_one := hre1
        jet := k
        jet_lt := by rw [← hm]; exact_mod_cast hk }
    have hi := horth i
    rw [inner_burnolZetaJetVector] at hi
    exact hi
  have hle : (m : ℕ∞) ≤
      analyticOrderAt (soninEval a ((f : soninEvenExtended a) : SoninL2)) rho := by
    by_cases htop : analyticOrderAt (soninEval a ((f : soninEvenExtended a) : SoninL2)) rho = ⊤
    · simp [htop]
    · exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero heval).2 hjets
  have hrho1 : rho ≠ 1 := by
    intro h
    rw [h] at hre1
    norm_num at hre1
  have hzeta : AnalyticAt ℂ riemannZeta rho := analyticAt_riemannZeta hrho1
  change meromorphicOrderAt riemannZeta rho ≤
    meromorphicOrderAt (soninEval a ((f : soninEvenExtended a) : SoninL2)) rho
  rw [hzeta.meromorphicOrderAt_eq]
  rw [← hm]
  exact le_meromorphicOrderAt_of_le_analyticOrderAt heval hle

/-- Burnol's literal Riesz jet-vector system has dense span for aperture at least one. -/
theorem isCompleteSystem_burnolZetaJetVector_of_one_le
    {a : ℝ} (ha : 0 < a) (ha1 : 1 ≤ a) :
    IsCompleteSystem ℂ (burnolZetaJetVector a ha) := by
  rw [isCompleteSystem_iff_forall_inner_eq_zero]
  intro f horth
  apply Subtype.ext
  apply burnol_evaluators_complete_of_one_le ha1
  · have hc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
        ((fourierUnitary ((f : soninEvenExtended a) : SoninL2) : SoninL2) : ℝ → ℂ) x =
          soninFourierBandConst a ((f : soninEvenExtended a) : SoninL2) := by
      obtain ⟨c, hc⟩ := ae_fourier_eq_of_mem_extended f.property.1
      have hcc : soninFourierBandConst a ((f : soninEvenExtended a) : SoninL2) = c := by
        rw [soninFourierBandConst]
        exact soninBandConst_eq ha hc
      rw [hcc]
      exact hc
    exact ⟨f.property.2, f.property.1, hc, ae_eq_soninBandConst ha f.property.1⟩
  · exact zeta_order_le_soninEval_of_all_jet_inner_zero ha f horth

/-- Burnol's literal Riesz jet-vector system does not have dense span below aperture one. -/
theorem not_isCompleteSystem_burnolZetaJetVector_of_lt_one
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ¬ IsCompleteSystem ℂ (burnolZetaJetVector a ha) := by
  obtain ⟨v, c, d, hdat, hann, hv⟩ := burnol_evaluators_not_complete_of_lt_one ha ha1
  let f : soninEvenExtended a := ⟨v, ⟨hdat.2.1, hdat.1⟩⟩
  intro hcomplete
  have hcriterion := (isCompleteSystem_iff_forall_inner_eq_zero
    (burnolZetaJetVector a ha)).mp hcomplete
  have hfzero : f = 0 := hcriterion f (fun i => by
    rw [inner_burnolZetaJetVector]
    apply iteratedDeriv_soninEval_eq_zero_of_zeta_order_le ha f i.re_pos i.re_lt_one
    · have hcc : soninFourierBandConst a v = c := by
        rw [soninFourierBandConst]
        exact soninBandConst_eq ha hdat.2.2.1
      have hdd : soninBandConst a v = d := soninBandConst_eq ha hdat.2.2.2
      change meromorphicOrderAt riemannZeta i.point ≤
        meromorphicOrderAt
          (extendedMellinContinuation a (soninFourierBandConst a v)
            (soninBandConst a v) v) i.point
      rw [hcc, hdd]
      exact hann i.point i.zero i.re_pos i.re_lt_one
    · exact i.jet_lt)
  apply hv
  simpa [f] using
    congrArg (fun x : soninEvenExtended a => ((x : soninEvenExtended a) : SoninL2)) hfzero

/-- Exact aperture threshold for dense span of Burnol's literal Riesz zero-jet vectors. -/
theorem isCompleteSystem_burnolZetaJetVector_iff_one_le
    {a : ℝ} (ha : 0 < a) :
    IsCompleteSystem ℂ (burnolZetaJetVector a ha) ↔ 1 ≤ a := by
  constructor
  · intro h
    by_contra hnot
    exact not_isCompleteSystem_burnolZetaJetVector_of_lt_one ha (lt_of_not_ge hnot) h
  · exact isCompleteSystem_burnolZetaJetVector_of_one_le ha

end

end RHTower
