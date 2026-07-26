import GaloisForLFunctions.RHTower.DeningerArithmeticGlobalDivision
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Topological Deninger arithmetic cohomology

This file replaces the provisional algebraic-dual compact-support space by the strong continuous
dual of the compact-open source quotient

`H¹ = O(ℂ) / XiC · O(ℂ)`.

The weight-one coordinate acts continuously on the source, preserves Xi coboundaries, and
therefore descends to a continuous Frobenius generator on `H¹`.  Its compact-support partner is
the continuous-dual action `ell ↦ ell - ell ∘ Theta`, so the Poincare pairing satisfies the exact
weight-one derivation law.

The removable Xi divided chains descend directly to this topological quotient and give a genuine
Frobenius eigenvector for every Xi divisor point.  Consequently a continuous conjugate-linear
positive comparison from this full distribution space to its strong dual would prove RH.  This
direct comparison is deliberately retained as an overstrong diagnostic implication.  Deninger's
actual Hilbert completion lies between the strong dual and this quotient and is formalized in
`DeningerArithmeticGelfandTriple`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The weight-one coordinate as a compact-open entire source. -/
def deningerCompactOpenThetaCoordinate :
    DeningerCompactOpenEntire :=
  deningerCompactOpenEntireEquiv.symm
    deningerEntireThetaCoordinate

@[simp]
theorem deningerCompactOpenThetaCoordinate_apply
    (z : ℂ) :
    deningerCompactOpenThetaCoordinate z =
      1 / 2 + Complex.I * z :=
  deningerEntireThetaCoordinate_apply z

/-- Continuous multiplication by the weight-one coordinate on source one-cochains. -/
def deningerCompactOpenThetaMul :
    DeningerCompactOpenEntire →L[ℂ]
      DeningerCompactOpenEntire where
  toFun F :=
    ⟨deningerCompactOpenThetaCoordinate.1 * F.1,
      deningerCompactOpenThetaCoordinate.2.mul F.2⟩
  map_add' F G := by
    ext z
    simp
    ring
  map_smul' c F := by
    ext z
    simp
    ring
  cont := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val

@[simp]
theorem deningerCompactOpenThetaMul_apply
    (F : DeningerCompactOpenEntire) (z : ℂ) :
    deningerCompactOpenThetaMul F z =
      (1 / 2 + Complex.I * z) * F z :=
  congrArg (· * F z)
    (deningerCompactOpenThetaCoordinate_apply z)

/-- Weight-one coordinate multiplication preserves compact-open Xi coboundaries. -/
theorem deningerCompactOpenThetaMul_mem_XiRange
    {F : DeningerCompactOpenEntire}
    (hF : F ∈ deningerCompactOpenXiRange) :
    deningerCompactOpenThetaMul F ∈
      deningerCompactOpenXiRange := by
  obtain ⟨G, rfl⟩ := hF
  refine ⟨deningerCompactOpenThetaMul G, ?_⟩
  ext z
  change
    XiC z * (deningerCompactOpenThetaCoordinate z * G z) =
      deningerCompactOpenThetaCoordinate z * (XiC z * G z)
  ring

/-- Continuous Frobenius generator on compact-open middle cohomology. -/
def deningerCompactOpenTheta :
    DeningerArithmeticCompactOpenH1 →L[ℂ]
      DeningerArithmeticCompactOpenH1 :=
  DeningerCompactOpenQuotient.mapL
    deningerCompactOpenXiRange
    deningerCompactOpenThetaMul
    deningerCompactOpenThetaMul_mem_XiRange

@[simp]
theorem deningerCompactOpenTheta_class
    (F : DeningerCompactOpenEntire) :
    deningerCompactOpenTheta
        (deningerArithmeticCompactOpenH1Class F) =
      deningerArithmeticCompactOpenH1Class
        (deningerCompactOpenThetaMul F) :=
  rfl

/--
Compact-support middle cohomology is the strong continuous dual of compact-open ordinary
cohomology.
-/
abbrev DeningerArithmeticTopologicalH1Compact :=
  StrongDual ℂ DeningerArithmeticCompactOpenH1

/-- Canonical ordinary/compact-support Poincare pairing. -/
def deningerTopologicalPoincarePairing
    (x : DeningerArithmeticCompactOpenH1)
    (ell : DeningerArithmeticTopologicalH1Compact) : ℂ :=
  ell x

/-- Compact-support Frobenius forced by weight one on the Poincare trace line. -/
def deningerCompactOpenThetaCompact :
    Module.End ℂ DeningerArithmeticTopologicalH1Compact where
  toFun ell :=
    ell - ell.comp deningerCompactOpenTheta
  map_add' ell eta := by
    ext x
    simp
    ring
  map_smul' c ell := by
    ext x
    simp
    ring

@[simp]
theorem deningerCompactOpenThetaCompact_apply
    (ell : DeningerArithmeticTopologicalH1Compact)
    (x : DeningerArithmeticCompactOpenH1) :
    deningerCompactOpenThetaCompact ell x =
      ell x - ell (deningerCompactOpenTheta x) :=
  rfl

/-- Exact weight-one derivation law for topological Poincare duality. -/
theorem deningerCompactOpenTheta_poincare
    (x : DeningerArithmeticCompactOpenH1)
    (ell : DeningerArithmeticTopologicalH1Compact) :
    deningerTopologicalPoincarePairing
          (deningerCompactOpenTheta x) ell +
        deningerTopologicalPoincarePairing x
          (deningerCompactOpenThetaCompact ell) =
      deningerTopologicalPoincarePairing x ell := by
  change
    ell (deningerCompactOpenTheta x) +
        (ell x - ell (deningerCompactOpenTheta x)) =
      ell x
  ring

/-- A removable Xi divided chain as a compact-open entire source. -/
def deningerCompactOpenDividedChain
    (alpha : ℂ) (k : ℕ) :
    DeningerCompactOpenEntire :=
  deningerCompactOpenEntireEquiv.symm
    (deningerEntireDividedChain alpha k)

@[simp]
theorem deningerCompactOpenDividedChain_apply
    (alpha : ℂ) (k : ℕ) (z : ℂ) :
    deningerCompactOpenDividedChain alpha k z =
      xiThetaDividedChain alpha k z :=
  rfl

/-- Cohomology class of a compact-open removable Xi divided chain. -/
def deningerCompactOpenDividedChainClass
    (alpha : ℂ) (k : ℕ) :
    DeningerArithmeticCompactOpenH1 :=
  deningerArithmeticCompactOpenH1Class
    (deningerCompactOpenDividedChain alpha k)

@[simp]
theorem deningerCompactOpenDividedChainClass_zero
    (alpha : ℂ) :
    deningerCompactOpenDividedChainClass alpha 0 = 0 := by
  apply
    (DeningerCompactOpenQuotient.mk_eq_zero_iff_mem
      deningerCompactOpenXiRange
      (deningerCompactOpenDividedChain alpha 0)).mpr
  let oneSource : DeningerCompactOpenEntire :=
    ⟨⟨fun _ : ℂ => 1, continuous_const⟩,
      differentiable_const 1⟩
  refine ⟨oneSource, ?_⟩
  ext z
  change XiC z * 1 = xiThetaDividedChain alpha 0 z
  simp only [mul_one, xiThetaDividedChain_zero]

/-- Exact compact-open source Jordan recurrence for the Frobenius coordinate. -/
theorem deningerCompactOpenThetaMul_dividedChain
    (rho : XiDivisorSupport) {k : ℕ}
    (hk : k < xiSupportMultiplicity rho) :
    deningerCompactOpenThetaMul
        (deningerCompactOpenDividedChain
          (xiSpectralPointSupport rho) (k + 1)) =
      (1 / 2 + Complex.I * xiSpectralPointSupport rho) •
          deningerCompactOpenDividedChain
            (xiSpectralPointSupport rho) (k + 1) +
        Complex.I •
          deningerCompactOpenDividedChain
            (xiSpectralPointSupport rho) k := by
  apply deningerCompactOpenEntireEquiv.injective
  simpa [deningerCompactOpenThetaMul,
    deningerCompactOpenThetaCoordinate,
    deningerCompactOpenDividedChain] using
      deningerEntireThetaCoordinate_mul_dividedChain rho hk

/-- Multiplicity-exact Jordan recurrence in compact-open middle cohomology. -/
theorem deningerCompactOpenTheta_dividedChainClass
    (rho : XiDivisorSupport) {k : ℕ}
    (hk : k < xiSupportMultiplicity rho) :
    deningerCompactOpenTheta
        (deningerCompactOpenDividedChainClass
          (xiSpectralPointSupport rho) (k + 1)) =
      (1 / 2 + Complex.I * xiSpectralPointSupport rho) •
          deningerCompactOpenDividedChainClass
            (xiSpectralPointSupport rho) (k + 1) +
        Complex.I •
          deningerCompactOpenDividedChainClass
            (xiSpectralPointSupport rho) k := by
  rw [deningerCompactOpenDividedChainClass,
    deningerCompactOpenTheta_class]
  have h :=
    congrArg deningerArithmeticCompactOpenH1Class
      (deningerCompactOpenThetaMul_dividedChain rho hk)
  simpa only [map_add, map_smul] using h

/-- Terminal multiplicity-depth divided chain is nonzero in compact-open cohomology. -/
theorem deningerCompactOpenDividedChainClass_multiplicity_ne_zero
    (rho : XiDivisorSupport) :
    deningerCompactOpenDividedChainClass
      (xiSpectralPointSupport rho)
      (xiSupportMultiplicity rho) ≠ 0 := by
  intro hzero
  have hmem :
      deningerCompactOpenDividedChain
          (xiSpectralPointSupport rho)
          (xiSupportMultiplicity rho) ∈
        deningerCompactOpenXiRange := by
    exact
      (DeningerCompactOpenQuotient.mk_eq_zero_iff_mem
        deningerCompactOpenXiRange
        (deningerCompactOpenDividedChain
          (xiSpectralPointSupport rho)
          (xiSupportMultiplicity rho))).mp hzero
  obtain ⟨G, hG⟩ := hmem
  have heval :=
    congrArg
      (fun F : DeningerCompactOpenEntire =>
        F (xiSpectralPointSupport rho)) hG
  have hXi :
      XiC (xiSpectralPointSupport rho) = 0 := by
    simpa only [xiThetaDividedChain_zero] using
      xiThetaDividedChain_vanish_before_multiplicity rho
        (xiSupportMultiplicity_pos rho)
  have hterminal :=
    xiThetaDividedChain_nonzero_at_multiplicity rho
  apply hterminal
  simpa [deningerCompactOpenXiMul_apply,
    deningerCompactOpenDividedChain_apply, hXi] using heval.symm

/-- Every Xi divisor point supplies a genuine eigenvector in source topological cohomology. -/
theorem exists_deningerCompactOpenTheta_eigenvector
    (rho : XiDivisorSupport) :
    ∃ x : DeningerArithmeticCompactOpenH1,
      x ≠ 0 ∧
        deningerCompactOpenTheta x =
          (1 / 2 + Complex.I * xiSpectralPointSupport rho) • x := by
  classical
  have hex :
      ∃ j : ℕ,
        deningerCompactOpenDividedChainClass
          (xiSpectralPointSupport rho) j ≠ 0 :=
    ⟨xiSupportMultiplicity rho,
      deningerCompactOpenDividedChainClass_multiplicity_ne_zero rho⟩
  have hfind0 : Nat.find hex ≠ 0 := by
    intro hzero
    have hnonzero := Nat.find_spec hex
    rw [hzero, deningerCompactOpenDividedChainClass_zero] at hnonzero
    exact hnonzero rfl
  obtain ⟨k, hfind⟩ :=
    Nat.exists_eq_succ_of_ne_zero hfind0
  have hclass :
      deningerCompactOpenDividedChainClass
        (xiSpectralPointSupport rho) (k + 1) ≠ 0 := by
    have hnonzero := Nat.find_spec hex
    rw [hfind] at hnonzero
    simpa only [Nat.succ_eq_add_one] using hnonzero
  have hkmult : k < xiSupportMultiplicity rho := by
    have hle :
        Nat.find hex ≤ xiSupportMultiplicity rho :=
      Nat.find_min' hex
        (deningerCompactOpenDividedChainClass_multiplicity_ne_zero rho)
    omega
  have hkzero :
      deningerCompactOpenDividedChainClass
        (xiSpectralPointSupport rho) k = 0 := by
    by_contra hk
    have hle : Nat.find hex ≤ k :=
      Nat.find_min' hex hk
    omega
  refine
    ⟨deningerCompactOpenDividedChainClass
        (xiSpectralPointSupport rho) (k + 1),
      hclass, ?_⟩
  rw [deningerCompactOpenTheta_dividedChainClass rho hkmult,
    hkzero]
  simp

/--
Direct strong-dual Hodge comparison.

The target is the strong continuous dual, and `star` itself is continuous for that strong-dual
topology.  This is stronger than Deninger's intended intermediate Hilbert completion; it is kept
as a diagnostic implication, not declared as the final arithmetic Hodge object.
-/
structure DeningerArithmeticTopologicalHodgeStar where
  star :
    DeningerArithmeticCompactOpenH1 →L⋆[ℂ]
      DeningerArithmeticTopologicalH1Compact
  bijective : Function.Bijective star
  theta_star :
    ∀ x,
      deningerCompactOpenThetaCompact (star x) =
        star (deningerCompactOpenTheta x)
  positive :
    ∀ {x : DeningerArithmeticCompactOpenH1}, x ≠ 0 →
      0 < (star x x).re

namespace DeningerArithmeticTopologicalHodgeStar

/-- Topological Hodge compatibility forces every source Frobenius eigenvalue to weight one. -/
theorem eigenvalue_re_eq_half
    (Hodge : DeningerArithmeticTopologicalHodgeStar)
    {rho : ℂ} {x : DeningerArithmeticCompactOpenH1}
    (hx0 : x ≠ 0)
    (hx : deningerCompactOpenTheta x = rho • x) :
    rho.re = 1 / 2 := by
  have hcup :=
    deningerCompactOpenTheta_poincare x (Hodge.star x)
  rw [hx, Hodge.theta_star, hx] at hcup
  have hstar :
      Hodge.star (rho • x) =
        (starRingEnd ℂ) rho • Hodge.star x :=
    map_smulₛₗ Hodge.star rho x
  rw [hstar] at hcup
  change
    Hodge.star x (rho • x) +
        ((starRingEnd ℂ) rho • Hodge.star x) x =
      Hodge.star x x at hcup
  simp only [map_smul, ContinuousLinearMap.smul_apply] at hcup
  have hmetric0 : Hodge.star x x ≠ 0 := by
    intro hzero
    have hpos := Hodge.positive hx0
    rw [hzero, zero_re] at hpos
    linarith
  have hweight :
      rho + (starRingEnd ℂ) rho = 1 := by
    apply mul_right_cancel₀ hmetric0
    linear_combination hcup
  have hre := congrArg Complex.re hweight
  simp only [add_re, conj_re, one_re] at hre
  linarith

/-- A positive continuous source Hodge star proves the Riemann hypothesis. -/
theorem riemannHypothesis
    (Hodge : DeningerArithmeticTopologicalHodgeStar) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  obtain ⟨x, hx0, hx⟩ :=
    exists_deningerCompactOpenTheta_eigenvector q.1
  have hre :=
    Hodge.eigenvalue_re_eq_half hx0 hx
  have him :
      (xiSpectralPointSupport q.1).im = 0 := by
    norm_num [Complex.mul_re] at hre
    linarith
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · rw [xiSpectralPoint_eq_support]
    simpa using him

end DeningerArithmeticTopologicalHodgeStar

end

end RHTower
