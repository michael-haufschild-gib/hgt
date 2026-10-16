import GaloisForLFunctions.RHTower.DeningerMeyerSourceShiftTopology
import GaloisForLFunctions.RHTower.DeningerMeyerInvisibleSourceDivisibility
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Elimination of all finite-order modes from the invisible Meyer sector

Cyclic boundary approximation, a single leading Xi jet, and strict source
division show that an invisible eigenclass is an actual Poisson boundary.
Every finite word is therefore bijective on the literal invisible sector.
No vanishing of that whole sector is asserted or assumed.
-/

open Complex Polynomial Set Topology

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

private theorem boundaryPolynomial_topJet (rho : ℂ) (d : ℕ)
    (hz : ∀ i < d, iteratedDeriv i xi rho = 0) (p : ℂ[X]) :
    deningerMeyerStrongLogMellinJetLM d rho (deningerMeyerXiBoundaryPolynomial p) =
      p.eval rho * iteratedDeriv d xi rho := by
  rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
  have he : deningerMeyerStrongLogMellin (deningerMeyerXiBoundaryPolynomial p) =
      (fun s => p.eval s) * xi := by
    funext s
    exact deningerMeyerXiBoundaryPolynomial_mellin p s
  have hp : ContDiffAt ℂ d (fun s : ℂ => p.eval s) rho := by
    simpa [Polynomial.aeval_def] using!
      (p.contDiff_aeval (d : WithTop ℕ∞)).contDiffAt
  rw [he, iteratedDeriv_mul hp
    (xi_analyticOnNhd_univ rho (Set.mem_univ _)).contDiffAt,
    Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    rw [hz (d - i) (by have := Finset.mem_range.mp hi; omega)]
    simp
  · simp

private theorem sourceShift_topJet_zero (rho : ℂ) (d : ℕ)
    (g : DeningerMeyerStrongLogTarget)
    (hz : ∀ i < d, iteratedDeriv i (deningerMeyerStrongLogMellin g) rho = 0) :
    deningerMeyerStrongLogMellinJetLM d rho (deningerMeyerStrongLogShift rho g) = 0 := by
  rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
  have he : deningerMeyerStrongLogMellin (deningerMeyerStrongLogShift rho g) =
      (fun s : ℂ => s - rho) * deningerMeyerStrongLogMellin g := by
    funext s
    exact deningerMeyerStrongLogShift_mellin rho g s
  rw [he, iteratedDeriv_mul (by fun_prop)
    (analyticOnNhd_deningerMeyerStrongLogMellin g.property rho (Set.mem_univ _)).contDiffAt]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    simp
  · rw [hz (d - i) (by have := Finset.mem_range.mp hi; omega)]
    simp

private theorem boundary_division (rho : ℂ) (d : ℕ)
    (hz : ∀ i < d, iteratedDeriv i xi rho = 0)
    (hn : iteratedDeriv d xi rho ≠ 0)
    (g : DeningerMeyerStrongLogTarget)
    (hg : deningerMeyerStrongLogShift rho g ∈ LinearMap.range deningerMeyerStrongLogSumLM)
    (hj : deningerMeyerStrongLogMellinJetLM d rho (deningerMeyerStrongLogShift rho g) = 0) :
    g ∈ LinearMap.range deningerMeyerStrongLogSumLM := by
  let N := LinearMap.range deningerMeyerStrongLogSumLM
  let T := deningerMeyerStrongLogShift rho
  let Z := N.map T
  let H := LinearMap.range deningerMeyerXiBoundaryPolynomial
  let J : DeningerMeyerStrongLogTarget →L[ℂ] ℂ :=
    (iteratedDeriv d xi rho)⁻¹ • deningerMeyerStrongLogMellinJetCLM d rho
  let R : DeningerMeyerStrongLogTarget →L[ℂ] DeningerMeyerStrongLogTarget :=
    ContinuousLinearMap.id ℂ _ - J.smulRight (deningerMeyerXiBoundaryPolynomial 1)
  have hZ : IsClosed (Z : Set DeningerMeyerStrongLogTarget) :=
    (deningerMeyerStrongLogShift_isClosedMap rho) _ deningerMeyerStrongLogSum_range_isClosed
  have hJ (p : ℂ[X]) : J (deningerMeyerXiBoundaryPolynomial p) = p.eval rho := by
    change (iteratedDeriv d xi rho)⁻¹ *
      deningerMeyerStrongLogMellinJetCLM d rho (deningerMeyerXiBoundaryPolynomial p) = _
    rw [deningerMeyerStrongLogMellinJetCLM_apply, boundaryPolynomial_topJet rho d hz]
    field_simp [hn]
  have hC (a : ℂ) : deningerMeyerXiBoundaryPolynomial (C a) =
      a • deningerMeyerXiBoundaryPolynomial 1 := by
    rw [show C a = a • (1 : ℂ[X]) by simp [Polynomial.smul_eq_C_mul], map_smul]
  have hR : H ≤ Z.comap R.toLinearMap := by
    rintro v ⟨p, rfl⟩
    change R (deningerMeyerXiBoundaryPolynomial p) ∈ Z
    have hfactor : (p - C (p.eval rho)).IsRoot rho := by simp
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hfactor
    refine ⟨deningerMeyerXiBoundaryPolynomial q, ⟨deningerMeyerXiCapPolynomial q, rfl⟩, ?_⟩
    change T (deningerMeyerXiBoundaryPolynomial q) =
      deningerMeyerXiBoundaryPolynomial p - J (deningerMeyerXiBoundaryPolynomial p) •
        deningerMeyerXiBoundaryPolynomial 1
    rw [hJ, ← hC, ← map_sub, hq, sub_mul, map_sub,
      deningerMeyerXiBoundaryPolynomial_X_mul, ← Polynomial.smul_eq_C_mul, map_smul]
    rfl
  have hcl := H.topologicalClosure_minimal hR (hZ.preimage R.continuous)
  rw [deningerMeyerXiBoundaryPolynomial_closure] at hcl
  have hmem := hcl hg
  have hfix : R (T g) = T g := by
    change T g - ((iteratedDeriv d xi rho)⁻¹ *
      deningerMeyerStrongLogMellinJetCLM d rho (T g)) •
        deningerMeyerXiBoundaryPolynomial 1 = T g
    rw [deningerMeyerStrongLogMellinJetCLM_apply, hj]
    simp
  change R (T g) ∈ Z at hmem
  rw [hfix] at hmem
  obtain ⟨h, hh, he⟩ := hmem
  exact (deningerMeyerStrongLogShift_injective rho he) ▸ hh

/-- A literal invisible eigenclass must already be an actual Poisson boundary. -/
theorem deningerMeyerInvisible_shift_eq_zero (rho : ℂ)
    (u : DeningerMeyerInvisible)
    (hu : deningerMeyerCohomologyShift rho u = 0) : (u : DeningerMeyerStrongLogCohomology) = 0 := by
  obtain ⟨g, hg⟩ := (LinearMap.range deningerMeyerStrongLogSumLM).mkQ_surjective u.val
  change Submodule.Quotient.mk g = u.val at hg
  have hmk : deningerMeyerCohomologyShift rho (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (deningerMeyerStrongLogShift rho g) := by
    simp [deningerMeyerCohomologyShift, deningerMeyerStrongLogShift]
  have hb : deningerMeyerStrongLogShift rho g ∈ LinearMap.range deningerMeyerStrongLogSumLM := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    rw [← hmk, hg]
    exact hu
  have hgin : g ∈ LinearMap.range deningerMeyerStrongLogSumLM := by
    by_cases hr : xi rho = 0
    · let tau : XiDivisorSupport := ⟨rho, mem_xi_divisor_support_of_eq_zero hr⟩
      have ho := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
        (xi_analyticOnNhd_univ rho (Set.mem_univ _))).mp (xi_analyticOrderAt_support tau)
      apply boundary_division rho (xiSupportMultiplicity tau) ho.1 ho.2 g hb
      apply sourceShift_topJet_zero
      intro i hi
      have h := (mem_deningerMeyerInvisible_iff u.val).mp u.property tau ⟨i, hi⟩
      rw [← hg, deningerMeyerXiSupportJetEvaluationLM_mk,
        deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv] at h
      exact h
    · apply boundary_division rho 0 (by intro i hi; omega) (by simpa using hr) g hb
      exact sourceShift_topJet_zero rho 0 g (by intro i hi; omega)
  rw [← hg]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hgin

/-- Every complex shift acts bijectively on the actual invisible sector. -/
theorem deningerMeyerInvisibleGenerator_shift_bijective (rho : ℂ) :
    Function.Bijective (deningerMeyerInvisibleGenerator -
      rho • (LinearMap.id : Module.End ℂ DeningerMeyerInvisible)) := by
  refine ⟨?_, deningerMeyerInvisibleGenerator_shift_surjective rho⟩
  intro u v huv
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply deningerMeyerInvisible_shift_eq_zero rho (u - v)
  have hzero := sub_eq_zero.mpr huv
  rw [← map_sub] at hzero
  exact congrArg Subtype.val hzero

/-- No nonzero invisible class can satisfy any finite generator word. -/
theorem deningerMeyerInvisibleGeneratorWord_bijective (L : List ℂ) :
    Function.Bijective (deningerMeyerGeneratorWord deningerMeyerInvisibleGenerator L) := by
  induction L with
  | nil => exact Function.bijective_id
  | cons rho L ih => exact (deningerMeyerInvisibleGenerator_shift_bijective rho).comp ih

end
end RHTower
