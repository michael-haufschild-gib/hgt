import GaloisForLFunctions.RHTower.DeningerMeyerBoundaryEulerSource
import GaloisForLFunctions.RHTower.DeningerMeyerGeneralizedZeroJetDescent
import GaloisForLFunctions.HTGeometry.GammaShiftConfluentAnnihilator

/-!
# Full finite jet transgression from literal Poisson boundaries

The actual negative Euler orbit of a cap source realizes every finite jet
packet at distinct nonzero points where its boundary Mellin transform is
nonzero. The proof retains every derivative: multiplication by the analytic
unit preserves vanishing order, and finite Hermite interpolation is bijective.
-/

open Complex Filter Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

/-- Full finite jets of the Mellin transform of an actual Poisson boundary. -/
def deningerMeyerBoundaryJetPacketLM {K : ℕ} (x : Fin K → ℂ) (m : ℕ) :
    DeningerMeyerCap →ₗ[ℂ] (Fin K × Fin m → ℂ) :=
  LinearMap.pi fun i =>
    (deningerMeyerStrongLogMellinJetLM i.2.val (x i.1)).comp deningerMeyerStrongLogSumLM

theorem deningerMeyerBoundaryJetPacketLM_apply {K : ℕ}
    (x : Fin K → ℂ) (m : ℕ) (f : DeningerMeyerCap) (i : Fin K × Fin m) :
    deningerMeyerBoundaryJetPacketLM x m f i =
      iteratedDeriv i.2.val (deningerMeyerBoundaryMellin f) (x i.1) :=
  deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv _ _ _

/-- Finite negative Euler coefficients mapped to the full boundary jet packet. -/
def deningerMeyerBoundaryEulerJetLM {K : ℕ}
    (f : DeningerMeyerCap) (x : Fin K → ℂ) (m : ℕ) :
    (Fin (K * m) → ℂ) →ₗ[ℂ] (Fin K × Fin m → ℂ) :=
  (deningerMeyerBoundaryJetPacketLM x m).comp
    (deningerMeyerBoundaryPolynomialSource f (K * m))

theorem deningerMeyerBoundaryEulerJetLM_injective {K : ℕ}
    (f : DeningerMeyerCap) (x : Fin K → ℂ) (m : ℕ)
    (hx : Function.Injective x) (hx0 : ∀ i, x i ≠ 0)
    (hf : ∀ i, deningerMeyerBoundaryMellin f (x i) ≠ 0) :
    Function.Injective (deningerMeyerBoundaryEulerJetLM f x m) := by
  classical
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro c hc
  apply windowJetMap_injective hx hx0 m 0
  rw [map_zero]
  funext i
  rw [windowJetMap_apply]
  let P := windowLin 0 (K * m) c
  have hP : AnalyticAt ℂ (fun z => P.eval z) (x i.1) :=
    AnalyticOnNhd.eval_polynomial P (x i.1) (Set.mem_univ _)
  have hB : AnalyticAt ℂ (deningerMeyerBoundaryMellin f) (x i.1) :=
    analyticOnNhd_deningerMeyerStrongLogMellin
      (deningerMeyerStrongLogSumLM f).property _ (Set.mem_univ _)
  have heq : deningerMeyerBoundaryMellin (deningerMeyerBoundaryPolynomialSource f (K*m) c) =
      fun z => P.eval z * deningerMeyerBoundaryMellin f z :=
    funext (deningerMeyerBoundaryPolynomialSource_mellin f (K*m) c)
  have hflat : ∀ k < m,
      iteratedDeriv k (fun z => P.eval z * deningerMeyerBoundaryMellin f z) (x i.1) = 0 := by
    intro k hk
    have h := congrFun hc (i.1, ⟨k, hk⟩)
    change deningerMeyerBoundaryJetPacketLM x m
      (deningerMeyerBoundaryPolynomialSource f (K*m) c) (i.1, ⟨k, hk⟩) = 0 at h
    rw [deningerMeyerBoundaryJetPacketLM_apply, heq] at h
    exact h
  have hord := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (n := m) (hP.mul hB)).mpr hflat
  rw [analyticOrderAt_mul hP hB,
    analyticOrderAt_eq_zero.mpr (Or.inr (hf i.1)), add_zero] at hord
  have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hP).mp hord i.2.val i.2.isLt
  rw [iteratedDeriv_complexPolynomial_eval] at hz
  exact hz

/-- The actual finite Euler source orbit maps bijectively to all requested jets. -/
theorem deningerMeyerBoundaryEulerJetLM_bijective {K : ℕ}
    (f : DeningerMeyerCap) (x : Fin K → ℂ) (m : ℕ)
    (hx : Function.Injective x) (hx0 : ∀ i, x i ≠ 0)
    (hf : ∀ i, deningerMeyerBoundaryMellin f (x i) ≠ 0) :
    Function.Bijective (deningerMeyerBoundaryEulerJetLM f x m) := by
  have hinj := deningerMeyerBoundaryEulerJetLM_injective f x m hx hx0 hf
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj

/-- Every jet vector has a preimage in the literal cap, without a lifting premise. -/
theorem deningerMeyerBoundaryJetPacketLM_surjective {K : ℕ}
    (f : DeningerMeyerCap) (x : Fin K → ℂ) (m : ℕ)
    (hx : Function.Injective x) (hx0 : ∀ i, x i ≠ 0)
    (hf : ∀ i, deningerMeyerBoundaryMellin f (x i) ≠ 0) :
    Function.Surjective (deningerMeyerBoundaryJetPacketLM x m) := by
  intro y
  obtain ⟨c, hc⟩ := (deningerMeyerBoundaryEulerJetLM_bijective f x m hx hx0 hf).2 y
  exact ⟨deningerMeyerBoundaryPolynomialSource f (K*m) c, hc⟩

end
end RHTower
