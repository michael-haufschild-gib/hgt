import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HodgeIndexFromEffectivity
import GaloisForLFunctions.RHTower.OddWeilGramLimit
import GaloisForLFunctions.RHTower.WeilDecayClassRHCriterion
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# The scaling surface of `ℤ` as a polar surface

The cycles of the scaling surface are the classes `aH + bV + f` of the pole plane and a real `C²`
compactly supported test `f` (`ScalingCycle`). The pairing is (`scalingPair`)

    H² = V² = 0,  H·V = 1,  f·H = B(f) = ∫ f e^{−u/2},  f·V = A(f) = ∫ f e^{u/2},
    f·g = B(f)A(g) + A(f)B(g) − Re W(f, g),

the last line being the local side of the explicit formula (prime comb minus archimedean collar,
the pole cancelled). This is a polar surface (`scalingSurface`), and its Castelnuovo–Severi defect
is Weil's form: `δ(aH + bV + f) = Re W(f, f)` (`scalingSurface_defect_self`). Every theorem about
abstract polar surfaces therefore applies to `ζ` verbatim:

* **the arithmetic Hodge index theorem is RH** (`scalingSurface_hodgeIndex_iff`), in all four forms
  of `hodgeIndex_tfae`;
* **Weil's discriminant step**: under RH, `(Re W(f, g))² ≤ W(f, f) W(g, g)`
  (`weilPair_sq_le_of_riemannHypothesis`);
* **RH is the existence of an effectivity** with the Riemann–Roch and ample axioms
  (`riemannHypothesis_iff_exists_effectivity`);
* **positivity is not effectivity**: the cone of the positive pole quadrant and nonnegative tests
  fails the Riemann–Roch axiom, unconditionally (`posTestCone_not_riemannRoch`).
-/

open Complex MeasureTheory
open scoped ComplexConjugate
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The real `C²` compactly supported tests. -/
def realTests : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ 2 f ∧ HasCompactSupport f}
  add_mem' ha hb := ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, by
    convert hf.2.smul_left (f := fun _ : ℝ => c) using 1
    funext x; simp⟩

/-- The complexification of a real test. -/
def cx (f : ℝ → ℝ) : ℝ → ℂ := fun u => (f u : ℂ)

theorem cx_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (cx f) :=
  Complex.ofRealCLM.contDiff.comp hf

theorem cx_hasCompactSupport {f : ℝ → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (cx f) :=
  hf.comp_left Complex.ofReal_zero

theorem cx_add (f g : ℝ → ℝ) : cx (f + g) = cx f + cx g := by
  funext u; simp [cx]

theorem cx_smul (c : ℝ) (f : ℝ → ℝ) : cx (c • f) = (c : ℂ) • cx f := by
  funext u; simp [cx]

theorem weilTest_add_left {f₁ f₂ g : ℝ → ℂ} (h₁ : Continuous f₁) (h₁c : HasCompactSupport f₁)
    (h₂ : Continuous f₂) (h₂c : HasCompactSupport f₂) (hg : Continuous g) :
    EF.weilTest (f₁ + f₂) g = EF.weilTest f₁ g + EF.weilTest f₂ g := by
  funext x
  simp only [Pi.add_apply, RHTower.WeilSpectral.weilTest_apply, add_mul]
  exact integral_add (RHTower.WeilSpectral.integrable_mul_conj_shift h₁ h₁c hg x)
    (RHTower.WeilSpectral.integrable_mul_conj_shift h₂ h₂c hg x)

theorem weilTest_smul_left (c : ℂ) (f g : ℝ → ℂ) :
    EF.weilTest (c • f) g = c • EF.weilTest f g := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, RHTower.WeilSpectral.weilTest_apply, mul_assoc]
  exact integral_const_mul c _

/-- Weil's pairing of two real tests, `Re W(f, g)`. -/
def weilPair (f g : ℝ → ℝ) : ℝ :=
  (RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (EF.weilTest (cx f) (cx g))).re

theorem weilPair_comm (f g : ℝ → ℝ) : weilPair f g = weilPair g f := by
  rw [weilPair, weilPair, ← RHTower.OddResolvent.tilde_weilTest_mixed,
    RHTower.WeilSpectral.weilFullFunctional_tilde, Complex.conj_re]

theorem weilPair_add_left {f₁ f₂ g : ℝ → ℝ} (h₁ : f₁ ∈ realTests) (h₂ : f₂ ∈ realTests)
    (hg : g ∈ realTests) : weilPair (f₁ + f₂) g = weilPair f₁ g + weilPair f₂ g := by
  rw [weilPair, cx_add, weilTest_add_left (cx_contDiff h₁.1).continuous (cx_hasCompactSupport h₁.2)
    (cx_contDiff h₂.1).continuous (cx_hasCompactSupport h₂.2) (cx_contDiff hg.1).continuous,
    RHTower.WeilSpectral.weilFullFunctional_add _
      (RHTower.OddResolvent.admissible_weilTest_mixed (cx_contDiff h₁.1) (cx_hasCompactSupport h₁.2)
        (cx_contDiff hg.1) (cx_hasCompactSupport hg.2))
      (RHTower.OddResolvent.admissible_weilTest_mixed (cx_contDiff h₂.1) (cx_hasCompactSupport h₂.2)
        (cx_contDiff hg.1) (cx_hasCompactSupport hg.2)), Complex.add_re, weilPair, weilPair]

theorem weilPair_smul_left (c : ℝ) (f g : ℝ → ℝ) : weilPair (c • f) g = c * weilPair f g := by
  rw [weilPair, cx_smul, weilTest_smul_left, RHTower.WeilSpectral.weilFullFunctional_smul,
    Complex.re_ofReal_mul, weilPair]

/-- The pole coordinate `B(f) = h_f(i/2) = ∫ f e^{−u/2}`. -/
def poleB (f : ℝ → ℝ) : ℝ := ∫ u, f u * Real.exp (-u / 2)

/-- The pole coordinate `A(f) = h_f(−i/2) = ∫ f e^{u/2}`. -/
def poleA (f : ℝ → ℝ) : ℝ := ∫ u, f u * Real.exp (u / 2)

theorem integrable_mul_exp {f : ℝ → ℝ} (hf : f ∈ realTests) (c : ℝ) :
    Integrable fun u => f u * Real.exp (c * u) :=
  (hf.1.continuous.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
    hf.2.mul_right

theorem poleB_add {f g : ℝ → ℝ} (hf : f ∈ realTests) (hg : g ∈ realTests) :
    poleB (f + g) = poleB f + poleB g := by
  have e : ∀ h : ℝ → ℝ, (fun u => h u * Real.exp (-(1 / 2) * u)) = fun u => h u * Real.exp (-u / 2) :=
    fun h => by funext u; congr 2; ring
  have i1 := integrable_mul_exp hf (-(1 / 2))
  have i2 := integrable_mul_exp hg (-(1 / 2))
  rw [e] at i1 i2
  simp only [poleB, Pi.add_apply, add_mul]
  exact integral_add i1 i2

theorem poleA_add {f g : ℝ → ℝ} (hf : f ∈ realTests) (hg : g ∈ realTests) :
    poleA (f + g) = poleA f + poleA g := by
  have e : ∀ h : ℝ → ℝ, (fun u => h u * Real.exp ((1 / 2) * u)) = fun u => h u * Real.exp (u / 2) :=
    fun h => by funext u; congr 2; ring
  have i1 := integrable_mul_exp hf (1 / 2)
  have i2 := integrable_mul_exp hg (1 / 2)
  rw [e] at i1 i2
  simp only [poleA, Pi.add_apply, add_mul]
  exact integral_add i1 i2

theorem poleB_smul (c : ℝ) (f : ℝ → ℝ) : poleB (c • f) = c * poleB f := by
  simp only [poleB, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem poleA_smul (c : ℝ) (f : ℝ → ℝ) : poleA (c • f) = c * poleA f := by
  simp only [poleA, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

/-- The local intersection of two real tests: polar part minus Weil's pairing. -/
def localPair (f g : ℝ → ℝ) : ℝ := poleB f * poleA g + poleA f * poleB g - weilPair f g

/-- The cycles `aH + bV + f` of the scaling surface. -/
abbrev ScalingCycle := ℝ × ℝ × realTests

/-- The intersection pairing of the scaling surface. -/
def scalingPairFun (x y : ScalingCycle) : ℝ :=
  x.1 * y.2.1 + x.2.1 * y.1 + x.1 * poleB y.2.2 + x.2.1 * poleA y.2.2 + y.1 * poleB x.2.2
    + y.2.1 * poleA x.2.2 + localPair x.2.2 y.2.2

theorem localPair_add_left {f₁ f₂ g : ℝ → ℝ} (h₁ : f₁ ∈ realTests) (h₂ : f₂ ∈ realTests)
    (hg : g ∈ realTests) : localPair (f₁ + f₂) g = localPair f₁ g + localPair f₂ g := by
  simp only [localPair, poleB_add h₁ h₂, poleA_add h₁ h₂, weilPair_add_left h₁ h₂ hg]; ring

theorem localPair_smul_left (c : ℝ) (f g : ℝ → ℝ) :
    localPair (c • f) g = c * localPair f g := by
  simp only [localPair, poleB_smul, poleA_smul, weilPair_smul_left]; ring

theorem localPair_comm (f g : ℝ → ℝ) : localPair f g = localPair g f := by
  simp only [localPair, weilPair_comm f g]; ring

/-- The intersection pairing as a bilinear map. -/
def scalingPair : ScalingCycle →ₗ[ℝ] ScalingCycle →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ scalingPairFun
    (fun x x' y => by
      simp only [scalingPairFun, Prod.fst_add, Prod.snd_add, Submodule.coe_add,
        poleB_add x.2.2.2 x'.2.2.2, poleA_add x.2.2.2 x'.2.2.2,
        localPair_add_left x.2.2.2 x'.2.2.2 y.2.2.2]; ring)
    (fun c x y => by
      simp only [scalingPairFun, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_eq_mul,
        poleB_smul, poleA_smul, localPair_smul_left]; ring)
    (fun x y y' => by
      simp only [scalingPairFun, Prod.fst_add, Prod.snd_add, Submodule.coe_add,
        poleB_add y.2.2.2 y'.2.2.2, poleA_add y.2.2.2 y'.2.2.2]
      rw [localPair_comm x.2.2, localPair_add_left y.2.2.2 y'.2.2.2 x.2.2.2,
        localPair_comm y.2.2, localPair_comm y'.2.2]; ring)
    (fun c x y => by
      simp only [scalingPairFun, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_eq_mul,
        poleB_smul, poleA_smul]
      rw [localPair_comm x.2.2, localPair_smul_left, localPair_comm]; ring)

theorem scalingPair_apply (x y : ScalingCycle) : scalingPair x y = scalingPairFun x y := rfl

theorem poleB_zero : poleB 0 = 0 := by simp [poleB]
theorem poleA_zero : poleA 0 = 0 := by simp [poleA]
theorem localPair_zero_left (g : ℝ → ℝ) : localPair 0 g = 0 := by
  have := localPair_smul_left 0 0 g
  simpa using this

/-- **The scaling surface of `ℤ`** as a polar surface, with the pole plane as `⟨H, V⟩`. -/
def scalingSurface : PolarSurface ScalingCycle where
  pair := scalingPair
  pair_comm x y := by
    simp only [scalingPair_apply, scalingPairFun, localPair_comm x.2.2]; ring
  H := (1, 0, 0)
  V := (0, 1, 0)
  pair_H_H := by simp [scalingPair_apply, scalingPairFun, poleB_zero, poleA_zero, localPair_zero_left]
  pair_V_V := by simp [scalingPair_apply, scalingPairFun, poleB_zero, poleA_zero, localPair_zero_left]
  pair_H_V := by simp [scalingPair_apply, scalingPairFun, poleB_zero, poleA_zero, localPair_zero_left]

theorem localPair_zero_right (f : ℝ → ℝ) : localPair f 0 = 0 := by
  rw [localPair_comm, localPair_zero_left]

/-- **The defect of the scaling surface is Weil's form.** -/
theorem scalingSurface_defect_self (x : ScalingCycle) :
    scalingSurface.defect x x = weilPair x.2.2 x.2.2 := by
  rw [PolarSurface.defect_self]
  change 2 * scalingPairFun x (1, 0, 0) * scalingPairFun x (0, 1, 0) - scalingPairFun x x = _
  simp only [scalingPairFun, localPair, Submodule.coe_zero, poleB_zero, poleA_zero,
    weilPair_comm _ (0 : ℝ → ℝ)]
  have h0 : weilPair 0 x.2.2 = 0 := by
    have := weilPair_smul_left 0 0 x.2.2
    simpa using this
  rw [h0]
  ring

/-- **The arithmetic Hodge index theorem is the Riemann hypothesis.** -/
theorem scalingSurface_hodgeIndex_iff : scalingSurface.HodgeIndex ↔ RiemannHypothesis := by
  rw [scalingSurface.hodgeIndex_iff_castelnuovoSeveri, scalingSurface.castelnuovoSeveri_iff_defect_nonneg,
    RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive]
  constructor
  · intro h g hg hgc
    have := h (0, 0, ⟨g, hg, hgc⟩)
    rwa [scalingSurface_defect_self] at this
  · intro h x
    rw [scalingSurface_defect_self]
    exact h _ x.2.2.2.1 x.2.2.2.2

/-- **Weil's discriminant step over `ℚ`**: under RH Weil's pairing obeys Cauchy–Schwarz. -/
theorem weilPair_sq_le_of_riemannHypothesis (hRH : RiemannHypothesis) {f g : ℝ → ℝ}
    (hf : f ∈ realTests) (hg : g ∈ realTests) :
    weilPair f g ^ 2 ≤ weilPair f f * weilPair g g := by
  have h := scalingSurface.defect_sq_le_of_hodgeIndex (scalingSurface_hodgeIndex_iff.mpr hRH)
    (0, 0, ⟨f, hf⟩) (0, 0, ⟨g, hg⟩)
  rw [scalingSurface_defect_self, scalingSurface_defect_self] at h
  have hd : scalingSurface.defect (0, 0, ⟨f, hf⟩) (0, 0, ⟨g, hg⟩) = weilPair f g := by
    rw [PolarSurface.defect, PolarSurface.polar]
    change scalingPairFun (0, 0, ⟨f, hf⟩) (1, 0, 0) * scalingPairFun (0, 0, ⟨g, hg⟩) (0, 1, 0)
      + scalingPairFun (0, 0, ⟨f, hf⟩) (0, 1, 0) * scalingPairFun (0, 0, ⟨g, hg⟩) (1, 0, 0)
      - scalingPairFun (0, 0, ⟨f, hf⟩) (0, 0, ⟨g, hg⟩) = _
    simp only [scalingPairFun, localPair, Submodule.coe_zero, poleB_zero, poleA_zero]
    have h0 : ∀ k : ℝ → ℝ, weilPair k 0 = 0 := fun k => by
      rw [weilPair_comm]; have := weilPair_smul_left 0 0 k; simpa using this
    simp only [h0]
    ring
  rwa [hd] at h

/-- **RH is the existence of an effectivity** of the scaling surface with the Riemann–Roch and
ample axioms. -/
theorem riemannHypothesis_iff_exists_effectivity :
    RiemannHypothesis ↔ ∃ E : Set ScalingCycle,
      scalingSurface.RiemannRochAxiom E ∧ scalingSurface.AmpleAxiom E :=
  scalingSurface_hodgeIndex_iff.symm.trans scalingSurface.exists_effectivity_iff_hodgeIndex

/-- The cone of the positive pole quadrant and nonnegative tests. -/
def posTestCone : Set ScalingCycle := {x | 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ ∀ u, 0 ≤ (x.2.2 : ℝ → ℝ) u}

/-- A sign-changing real test: a bump minus its translate. -/
def signChangingTest : ℝ → ℝ :=
  fun u => (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)) u -
    (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)) (u - 5)

theorem signChangingTest_mem : signChangingTest ∈ realTests := by
  set φ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  refine ⟨φ.contDiff.sub (φ.contDiff.comp
    (contDiff_id.sub contDiff_const)), φ.hasCompactSupport.sub ?_⟩
  exact φ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight 5)

theorem signChangingTest_zero : signChangingTest 0 = 1 := by
  simp only [signChangingTest]
  rw [ContDiffBump.one_of_mem_closedBall _ (by simp), ContDiffBump.zero_of_le_dist _ (by
    simp; norm_num)]
  norm_num

theorem signChangingTest_five : signChangingTest 5 = -1 := by
  simp only [signChangingTest]
  rw [ContDiffBump.zero_of_le_dist _ (by simp; norm_num), sub_self,
    ContDiffBump.one_of_mem_closedBall _ (by simp)]
  norm_num

/-- **Positivity is not effectivity.** The cone of the positive pole quadrant and nonnegative tests
fails the Riemann–Roch axiom of the scaling surface. -/
theorem posTestCone_not_riemannRoch : ¬ scalingSurface.RiemannRochAxiom posTestCone := by
  refine scalingSurface.not_riemannRoch_of_perturbation (0, 0, ⟨_, signChangingTest_mem⟩)
    fun ε hε => ⟨fun h => ?_, fun h => ?_⟩
  · have := h.2.2 5
    simp only [PolarSurface.ample, scalingSurface, Prod.snd_add, Prod.smul_snd, Submodule.coe_add,
      Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero,
      Pi.zero_apply, signChangingTest_five] at this
    linarith
  · have := h.2.2 0
    simp only [PolarSurface.ample, scalingSurface, Prod.snd_neg, Prod.snd_add, Prod.smul_snd,
      Submodule.coe_neg, Submodule.coe_add, Submodule.coe_smul, Pi.neg_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply, signChangingTest_zero] at this
    linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
