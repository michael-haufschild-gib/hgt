import GaloisForLFunctions.RHTower.DeningerArithmeticCompactDualLocalization
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Canonical jet Hilbert rigging of Deninger arithmetic cohomology

The compact-open arithmetic middle cohomology is the full product of its multiplicity-bounded
local Xi jets, while its continuous compact-support dual consists exactly of finite-support jet
functionals.  The canonical Hilbert space between these two boundaries is therefore the
square-summable jet carrier

`⊕ J_rho^vee ⊂ ell^2(rho,k) ⊂ ∏ J_rho`.

This file constructs that middle carrier from the source jet equivalence.  It proves an exact
linear equivalence between compact-support cohomology and the finite jet sum and a continuous
injective map from the Hilbert carrier into compact-open ordinary cohomology.

No Frobenius symmetry, Hodge positivity, zero-location statement, or simplicity hypothesis is
used.
-/

open Complex Function Set Topology

namespace RHTower

noncomputable section

/-- One multiplicity-bounded local Xi-jet coordinate. -/
abbrev DeningerArithmeticJetCoordinate :=
  Σ rho : XiDivisorSupport, DeningerArithmeticJetIndex rho

/-- Algebraic finite-support boundary of the source jet product. -/
abbrev DeningerArithmeticJetTest :=
  DeningerArithmeticJetCoordinate →₀ ℂ

/-- Canonical Hilbert middle carrier of square-summable source jets. -/
abbrev DeningerArithmeticJetHilbert :=
  lp (fun _ : DeningerArithmeticJetCoordinate => ℂ) 2

/-- A finite jet family acts on compact-open cohomology by the corresponding finite sum. -/
def deningerArithmeticJetTestToCompact :
    DeningerArithmeticJetTest →ₗ[ℂ]
      DeningerArithmeticTopologicalH1Compact :=
  Finsupp.lsum ℂ fun idx =>
    LinearMap.toSpanSingleton ℂ
      DeningerArithmeticTopologicalH1Compact
      (deningerCompactOpenH1Jet idx.1 idx.2)

@[simp]
theorem deningerArithmeticJetTestToCompact_single
    (idx : DeningerArithmeticJetCoordinate) (c : ℂ) :
    deningerArithmeticJetTestToCompact
        (Finsupp.single idx c) =
      c • deningerCompactOpenH1Jet idx.1 idx.2 := by
  simp [deningerArithmeticJetTestToCompact]

theorem deningerArithmeticJetTestToCompact_apply
    (a : DeningerArithmeticJetTest)
    (x : DeningerArithmeticCompactOpenH1) :
    deningerArithmeticJetTestToCompact a x =
      a.sum fun idx c =>
        c * deningerCompactOpenH1Jet idx.1 idx.2 x := by
  classical
  rw [deningerArithmeticJetTestToCompact,
    Finsupp.lsum_apply]
  rw [Finsupp.sum_apply]
  simp only [LinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- One product basis vector, written using the flattened jet-coordinate index. -/
def deningerArithmeticJetCoordinateBasis
    (idx : DeningerArithmeticJetCoordinate) :
    DeningerArithmeticJetProduct :=
  deningerArithmeticJetBasisVector idx.1 idx.2

/-- A local jet evaluates the corresponding product basis vector by the Kronecker law. -/
theorem deningerCompactOpenH1Jet_jetCoordinateBasis
    (i j : DeningerArithmeticJetCoordinate) :
    deningerCompactOpenH1Jet i.1 i.2
        (deningerCompactOpenJetProductToH1
          (deningerArithmeticJetCoordinateBasis j)) =
      if i = j then 1 else 0 := by
  rw [← deningerCompactOpenH1AllJets_apply,
    deningerCompactOpenH1AllJets_jetProductToH1]
  by_cases hij : i = j
  · subst j
    simp [deningerArithmeticJetCoordinateBasis,
      deningerArithmeticJetBasisVector, piBasisVector]
  · have hrho :
        i.1 = j.1 → HEq i.2 j.2 → False := by
      intro hrho hk
      apply hij
      exact Sigma.ext hrho hk
    rcases i with ⟨rho, k⟩
    rcases j with ⟨tau, l⟩
    by_cases hrt : rho = tau
    · subst tau
      have hkl : k ≠ l := by
        intro h
        apply hij
        exact Sigma.ext rfl (by simpa [h])
      simp [deningerArithmeticJetCoordinateBasis,
        deningerArithmeticJetBasisVector, piBasisVector,
        hij, hkl]
    · simp [deningerArithmeticJetCoordinateBasis,
        deningerArithmeticJetBasisVector, piBasisVector,
        hij, hrt]

/-- Evaluation of a finite jet functional on a product basis vector recovers its coefficient. -/
@[simp]
theorem deningerArithmeticJetTestToCompact_basis
    (a : DeningerArithmeticJetTest)
    (idx : DeningerArithmeticJetCoordinate) :
    deningerArithmeticJetTestToCompact a
        (deningerCompactOpenJetProductToH1
          (deningerArithmeticJetCoordinateBasis idx)) =
      a idx := by
  classical
  rw [deningerArithmeticJetTestToCompact_apply]
  simp_rw [deningerCompactOpenH1Jet_jetCoordinateBasis]
  have hsum :=
    Finsupp.sum_ite_eq' a idx
      (fun (_ : DeningerArithmeticJetCoordinate) (c : ℂ) => c)
  simp only [mul_ite, mul_one, mul_zero] at *
  by_cases hidx : idx ∈ a.support
  · simpa [hidx] using hsum
  · have ha : a idx = 0 :=
      by simpa [Finsupp.mem_support_iff] using hidx
    simpa [hidx, ha] using hsum

/-- Distinct finite jet families define distinct continuous compact-support classes. -/
theorem deningerArithmeticJetTestToCompact_injective :
    Function.Injective deningerArithmeticJetTestToCompact := by
  intro a b hab
  ext idx
  have h :=
    congrArg
      (fun ell : DeningerArithmeticTopologicalH1Compact =>
        ell
          (deningerCompactOpenJetProductToH1
            (deningerArithmeticJetCoordinateBasis idx)))
      hab
  simpa using h

/-- Every continuous compact-support class is represented by one finite jet family. -/
theorem deningerArithmeticJetTestToCompact_surjective :
    Function.Surjective deningerArithmeticJetTestToCompact := by
  classical
  intro ell
  obtain ⟨S, T, hEll⟩ :=
    deningerArithmeticTopologicalH1Compact_finiteJetSupport ell
  let a : DeningerArithmeticJetTest :=
    ∑ rho : ↥S,
      ∑ k ∈ T rho.1,
        Finsupp.single
          (⟨rho.1, k⟩ : DeningerArithmeticJetCoordinate)
          (ell
            (deningerCompactOpenJetProductToH1
              (deningerArithmeticJetBasisVector rho.1 k)))
  refine ⟨a, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  rw [hEll x]
  simp only [a, map_sum, deningerArithmeticJetTestToCompact_single,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  ring_nf

/--
Exact source identification of continuous compact-support cohomology with the algebraic direct
sum of local Xi-jet duals.
-/
noncomputable def deningerArithmeticJetTestCompactEquiv :
    DeningerArithmeticJetTest ≃ₗ[ℂ]
      DeningerArithmeticTopologicalH1Compact :=
  LinearEquiv.ofBijective deningerArithmeticJetTestToCompact
    ⟨deningerArithmeticJetTestToCompact_injective,
      deningerArithmeticJetTestToCompact_surjective⟩

/-- Continuous inclusion of square-summable jets into the full product jet carrier. -/
def deningerArithmeticJetHilbertToProduct :
    DeningerArithmeticJetHilbert →L[ℂ]
      DeningerArithmeticJetProduct where
  toFun a rho k := a ⟨rho, k⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    apply continuous_pi
    intro rho
    apply continuous_pi
    intro k
    exact
      (lp.evalCLM ℂ
        (fun _ : DeningerArithmeticJetCoordinate => ℂ)
        2 (⟨rho, k⟩ : DeningerArithmeticJetCoordinate)).continuous

@[simp]
theorem deningerArithmeticJetHilbertToProduct_apply
    (a : DeningerArithmeticJetHilbert)
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    deningerArithmeticJetHilbertToProduct a rho k =
      a ⟨rho, k⟩ :=
  rfl

/-- Square-summable source jets determine compact-open arithmetic cohomology classes. -/
def deningerArithmeticJetHilbertToH1 :
    DeningerArithmeticJetHilbert →L[ℂ]
      DeningerArithmeticCompactOpenH1 :=
  deningerCompactOpenJetProductToH1.comp
    deningerArithmeticJetHilbertToProduct

/-- The Hilbert-to-distribution map is injective. -/
theorem deningerArithmeticJetHilbertToH1_injective :
    Function.Injective deningerArithmeticJetHilbertToH1 := by
  intro a b hab
  apply Subtype.ext
  funext idx
  have h :=
    congrArg deningerCompactOpenH1AllJets hab
  have hidx :=
    congrFun (congrFun h idx.1) idx.2
  simpa [deningerArithmeticJetHilbertToH1] using hidx

end

end RHTower
