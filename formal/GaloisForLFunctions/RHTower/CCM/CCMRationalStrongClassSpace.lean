import GaloisForLFunctions.RHTower.CCM.CCMRationalClassSpaceSection
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerDilationFlow
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Exact strong Schwartz target on the rational idele class space

The canonical section `C_ℚ = Ẑˣ × ℝ₊ˣ` identifies its positive-real factor with logarithmic
radius.  Strong Bruhat--Schwartz functions are therefore locally constant in `Ẑˣ` and lie in
Meyer's all-derivative, all-exponential-weight target in log radius.  This file builds that exact
space, its faithful scalar realization, its Real structure, and its right `C_ℚ` action.

No ordinary-Schwartz replacement, finite differentiability cutoff, asymptotic hypothesis, or
numerical computation occurs.
-/

open Complex Filter Function Set Topology
open scoped ContDiff

noncomputable section

namespace RHTower

private theorem iteratedDeriv_complexConj :
    ∀ (n : ℕ) {g : ℝ → ℂ}, ContDiff ℝ (⊤ : ℕ∞) g →
      iteratedDeriv n (fun x => star (g x)) =
        fun x => star (iteratedDeriv n g x) := by
  intro n
  induction n with
  | zero =>
      intro g _
      simp
  | succ n ihn =>
      intro g hg
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ihn hg]
      funext x
      have hdiff : DifferentiableAt ℝ (iteratedDeriv n g) x := by
        have h := hg.differentiable_iteratedDeriv n
          (compareOfLessAndEq_eq_lt.mp rfl)
        exact h.differentiableAt
      exact ((Complex.conjCLE.hasFDerivAt).comp_hasDerivAt
        x hdiff.hasDerivAt).deriv

/-- Meyer's all-weight logarithmic target is closed under complex conjugation. -/
theorem DeningerMeyerStrongLogDecay.conj
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g) :
    DeningerMeyerStrongLogDecay (fun t => star (g t)) where
  smooth := Complex.conjCLE.contDiff.comp hg.smooth
  decayTop := by
    intro n a
    rw [iteratedDeriv_complexConj n hg.smooth]
    rw [Asymptotics.isBigO_iff]
    rcases Asymptotics.isBigO_iff.mp (hg.decayTop n a) with ⟨c, hc⟩
    exact ⟨c, hc.mono fun t ht => by simpa using ht⟩
  decayBot := by
    intro n b
    rw [iteratedDeriv_complexConj n hg.smooth]
    rw [Asymptotics.isBigO_iff]
    rcases Asymptotics.isBigO_iff.mp (hg.decayBot n b) with ⟨c, hc⟩
    exact ⟨c, hc.mono fun t ht => by simpa using ht⟩

/-- Complex conjugation on the exact radial strong target. -/
def deningerMeyerStrongLogConj
    (g : DeningerMeyerStrongLogTarget) :
    DeningerMeyerStrongLogTarget :=
  ⟨fun t => star (((g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t),
    g.property.conj⟩

@[simp]
theorem deningerMeyerStrongLogConj_apply
    (g : DeningerMeyerStrongLogTarget) (t : ℝ) :
    ((deningerMeyerStrongLogConj g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t =
      star (((g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t) :=
  rfl

@[simp]
theorem deningerMeyerStrongLogConj_add
    (g h : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogConj (g + h) =
      deningerMeyerStrongLogConj g + deningerMeyerStrongLogConj h := by
  apply Subtype.ext
  funext t
  change star ((((g + h : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t)) =
    star (((g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t) +
      star (((h : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t)
  simp

@[simp]
theorem deningerMeyerStrongLogConj_smul
    (z : ℂ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogConj (z • g) =
      star z • deningerMeyerStrongLogConj g := by
  apply Subtype.ext
  funext t
  change star ((((z • g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t)) =
    star z * star (((g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t)
  simp

@[simp]
theorem deningerMeyerStrongLogConj_sq
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogConj (deningerMeyerStrongLogConj g) = g := by
  apply Subtype.ext
  funext t
  change star (star (((g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t)) =
    ((g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t
  simp

end RHTower

namespace GaloisForLFunctions
namespace RHTower

/-- Positive real unit with logarithmic coordinate `t`. -/
def ccmRationalPositiveLogUnit (t : ℝ) : Units NNReal :=
  (Nonneg.unitsHomeomorphPos ℝ).symm ⟨Real.exp t, Real.exp_pos t⟩

@[simp]
theorem ccmRationalPositiveLogUnit_coe (t : ℝ) :
    (((ccmRationalPositiveLogUnit t).val : NNReal) : ℝ) = Real.exp t :=
  rfl

theorem ccmRationalPositiveLogUnit_continuous :
    Continuous ccmRationalPositiveLogUnit :=
  (Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp
    (Real.continuous_exp.subtype_mk fun t => Real.exp_pos t)

@[simp]
theorem ccmRationalPositiveLogUnit_zero :
    ccmRationalPositiveLogUnit 0 = 1 := by
  apply Units.ext
  apply NNReal.eq
  simp

@[simp]
theorem ccmRationalPositiveLogUnit_add (s t : ℝ) :
    ccmRationalPositiveLogUnit (s + t) =
      ccmRationalPositiveLogUnit s * ccmRationalPositiveLogUnit t := by
  apply Units.ext
  apply NNReal.eq
  exact Real.exp_add s t

/-- Logarithmic coordinate of the positive-real factor. -/
def ccmRationalPositiveUnitLog (r : Units NNReal) : ℝ :=
  Real.log (((r.val : NNReal) : ℝ))

theorem ccmRationalPositiveUnit_coe_pos (r : Units NNReal) :
    0 < (((r.val : NNReal) : ℝ)) := by
  exact_mod_cast (pos_iff_ne_zero.mpr r.ne_zero : 0 < r.val)

@[simp]
theorem ccmRationalPositiveUnitLog_logUnit (t : ℝ) :
    ccmRationalPositiveUnitLog (ccmRationalPositiveLogUnit t) = t := by
  exact Real.log_exp t

@[simp]
theorem ccmRationalPositiveUnitLog_one :
    ccmRationalPositiveUnitLog 1 = 0 := by
  rw [← ccmRationalPositiveLogUnit_zero,
    ccmRationalPositiveUnitLog_logUnit]

@[simp]
theorem ccmRationalPositiveLogUnit_unitLog (r : Units NNReal) :
    ccmRationalPositiveLogUnit (ccmRationalPositiveUnitLog r) = r := by
  apply Units.ext
  apply NNReal.eq
  exact Real.exp_log (ccmRationalPositiveUnit_coe_pos r)

@[simp]
theorem ccmRationalPositiveUnitLog_mul (r s : Units NNReal) :
    ccmRationalPositiveUnitLog (r * s) =
      ccmRationalPositiveUnitLog r + ccmRationalPositiveUnitLog s := by
  unfold ccmRationalPositiveUnitLog
  rw [show ((((r * s).val : NNReal) : ℝ)) =
      (((r.val : NNReal) : ℝ)) * (((s.val : NNReal) : ℝ)) by rfl]
  exact Real.log_mul
    (ne_of_gt (ccmRationalPositiveUnit_coe_pos r))
    (ne_of_gt (ccmRationalPositiveUnit_coe_pos s))

/-- Exact strong Schwartz target on `C_ℚ = Ẑˣ × ℝ₊ˣ`: locally constant in the
profinite direction and all-derivative/all-exponential-weight Schwartz in log radius. -/
abbrev CCMRationalStrongClassSpace :=
  LocallyConstant CCMRationalProfiniteUnit
    _root_.RHTower.DeningerMeyerStrongLogTarget

/-- Scalar realization of an exact strong class-space function. -/
def ccmRationalStrongClassSpaceEval
    (f : CCMRationalStrongClassSpace)
    (b : CCMRationalClassSpaceSection) : ℂ :=
  (((f b.1 : _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ)
    (ccmRationalPositiveUnitLog b.2))

/-- Linear scalar realization on the literal class-space section. -/
def ccmRationalStrongClassSpaceEvalLinear :
    CCMRationalStrongClassSpace →ₗ[ℂ]
      (CCMRationalClassSpaceSection → ℂ) where
  toFun := ccmRationalStrongClassSpaceEval
  map_add' f g := by
    funext b
    change ((((f + g) b.1 : _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ)
      (ccmRationalPositiveUnitLog b.2)) =
      (((f b.1 : _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ)
        (ccmRationalPositiveUnitLog b.2)) +
      (((g b.1 : _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ)
        (ccmRationalPositiveUnitLog b.2))
    rfl
  map_smul' z f := by
    funext b
    change ((((z • f) b.1 : _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ)
      (ccmRationalPositiveUnitLog b.2)) = z *
      (((f b.1 : _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ)
        (ccmRationalPositiveUnitLog b.2))
    rfl

@[simp]
theorem ccmRationalStrongClassSpaceEvalLinear_apply
    (f : CCMRationalStrongClassSpace)
    (b : CCMRationalClassSpaceSection) :
    ccmRationalStrongClassSpaceEvalLinear f b =
      (((f b.1 : _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ)
        (ccmRationalPositiveUnitLog b.2)) :=
  rfl

@[simp]
theorem ccmRationalStrongClassSpaceEval_logUnit
    (f : CCMRationalStrongClassSpace)
    (u : CCMRationalProfiniteUnit) (t : ℝ) :
    ccmRationalStrongClassSpaceEval f
        (u, ccmRationalPositiveLogUnit t) =
      (((f u : _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ) t) := by
  simp [ccmRationalStrongClassSpaceEval]

theorem ccmRationalStrongClassSpaceEvalLinear_injective :
    Function.Injective ccmRationalStrongClassSpaceEvalLinear := by
  intro f g h
  apply LocallyConstant.ext
  intro u
  apply Subtype.ext
  funext t
  have ht := congrFun h (u, ccmRationalPositiveLogUnit t)
  simpa using ht

/-- Exact scalar strong-Schwartz functions on the rational class space. -/
def CCMRationalStrongClassSpaceScalarTarget :
    Submodule ℂ (CCMRationalClassSpaceSection → ℂ) :=
  LinearMap.range ccmRationalStrongClassSpaceEvalLinear

theorem mem_ccmRationalStrongClassSpaceScalarTarget_iff
    (s : CCMRationalClassSpaceSection → ℂ) :
    s ∈ CCMRationalStrongClassSpaceScalarTarget ↔
      ∃ f : CCMRationalStrongClassSpace,
        ccmRationalStrongClassSpaceEval f = s :=
  Iff.rfl

/-- Pointwise Real structure on the exact strong class-space target. -/
def ccmRationalStrongClassSpaceReal
    (f : CCMRationalStrongClassSpace) :
    CCMRationalStrongClassSpace :=
  LocallyConstant.map _root_.RHTower.deningerMeyerStrongLogConj f

@[simp]
theorem ccmRationalStrongClassSpaceReal_apply
    (f : CCMRationalStrongClassSpace)
    (u : CCMRationalProfiniteUnit) (t : ℝ) :
    ((((ccmRationalStrongClassSpaceReal f) u :
        _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ) t) =
      star ((((f u : _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ) t)) :=
  rfl

@[simp]
theorem ccmRationalStrongClassSpaceReal_add
    (f g : CCMRationalStrongClassSpace) :
    ccmRationalStrongClassSpaceReal (f + g) =
      ccmRationalStrongClassSpaceReal f +
        ccmRationalStrongClassSpaceReal g := by
  apply LocallyConstant.ext
  intro u
  exact _root_.RHTower.deningerMeyerStrongLogConj_add (f u) (g u)

@[simp]
theorem ccmRationalStrongClassSpaceReal_smul
    (z : ℂ) (f : CCMRationalStrongClassSpace) :
    ccmRationalStrongClassSpaceReal (z • f) =
      star z • ccmRationalStrongClassSpaceReal f := by
  apply LocallyConstant.ext
  intro u
  exact _root_.RHTower.deningerMeyerStrongLogConj_smul z (f u)

@[simp]
theorem ccmRationalStrongClassSpaceReal_sq
    (f : CCMRationalStrongClassSpace) :
    ccmRationalStrongClassSpaceReal
      (ccmRationalStrongClassSpaceReal f) = f := by
  apply LocallyConstant.ext
  intro u
  exact _root_.RHTower.deningerMeyerStrongLogConj_sq (f u)

@[simp]
theorem ccmRationalStrongClassSpaceEval_real
    (f : CCMRationalStrongClassSpace)
    (b : CCMRationalClassSpaceSection) :
    ccmRationalStrongClassSpaceEval
        (ccmRationalStrongClassSpaceReal f) b =
      star (ccmRationalStrongClassSpaceEval f b) :=
  rfl

/-- Right multiplication on the profinite-unit factor. -/
def ccmRationalProfiniteRightMul
    (v : CCMRationalProfiniteUnit) :
    C(CCMRationalProfiniteUnit, CCMRationalProfiniteUnit) where
  toFun u := u * v
  continuous_toFun := continuous_id.mul continuous_const

/-- Right regular action of `C_ℚ` on its exact strong-Schwartz target. -/
def ccmRationalStrongClassSpaceRightAction
    (c : CCMRationalClassSpaceSection)
    (f : CCMRationalStrongClassSpace) :
    CCMRationalStrongClassSpace :=
  LocallyConstant.map
    (fun g => _root_.RHTower.deningerMeyerStrongLogFlow
      (-ccmRationalPositiveUnitLog c.2) g)
    (LocallyConstant.comap (ccmRationalProfiniteRightMul c.1) f)

@[simp]
theorem ccmRationalStrongClassSpaceRightAction_apply
    (c : CCMRationalClassSpaceSection)
    (f : CCMRationalStrongClassSpace)
    (u : CCMRationalProfiniteUnit) (t : ℝ) :
    ((((ccmRationalStrongClassSpaceRightAction c f) u :
        _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ) t) =
      (((f (u * c.1) : _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ)
        (t + ccmRationalPositiveUnitLog c.2)) := by
  change ((((_root_.RHTower.deningerMeyerStrongLogFlow
      (-ccmRationalPositiveUnitLog c.2) (f (u * c.1)) :
        _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ) t)) = _
  rw [_root_.RHTower.deningerMeyerStrongLogFlow_apply]
  simp only [sub_neg_eq_add]

/-- The right regular action is complex-linear. -/
def ccmRationalStrongClassSpaceRightActionLinear
    (c : CCMRationalClassSpaceSection) :
    CCMRationalStrongClassSpace →ₗ[ℂ]
      CCMRationalStrongClassSpace where
  toFun := ccmRationalStrongClassSpaceRightAction c
  map_add' f g := by
    apply LocallyConstant.ext
    intro u
    apply Subtype.ext
    funext t
    change ((((ccmRationalStrongClassSpaceRightAction c (f + g)) u :
        _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ) t) = _
    rw [ccmRationalStrongClassSpaceRightAction_apply]
    change _ =
      ((((ccmRationalStrongClassSpaceRightAction c f) u :
          _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ) t) +
      ((((ccmRationalStrongClassSpaceRightAction c g) u :
          _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ) t)
    rw [ccmRationalStrongClassSpaceRightAction_apply,
      ccmRationalStrongClassSpaceRightAction_apply]
    rfl
  map_smul' z f := by
    apply LocallyConstant.ext
    intro u
    apply Subtype.ext
    funext t
    change ((((ccmRationalStrongClassSpaceRightAction c (z • f)) u :
        _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ) t) = _
    rw [ccmRationalStrongClassSpaceRightAction_apply]
    change _ = z *
      ((((ccmRationalStrongClassSpaceRightAction c f) u :
          _root_.RHTower.DeningerMeyerStrongLogTarget) : ℝ → ℂ) t)
    rw [ccmRationalStrongClassSpaceRightAction_apply]
    rfl

@[simp]
theorem ccmRationalStrongClassSpaceEval_rightAction
    (c : CCMRationalClassSpaceSection)
    (f : CCMRationalStrongClassSpace)
    (b : CCMRationalClassSpaceSection) :
    ccmRationalStrongClassSpaceEval
        (ccmRationalStrongClassSpaceRightAction c f) b =
      ccmRationalStrongClassSpaceEval f (b * c) := by
  simp [ccmRationalStrongClassSpaceEval,
    ccmRationalStrongClassSpaceRightAction_apply]

@[simp]
theorem ccmRationalStrongClassSpaceRightAction_one
    (f : CCMRationalStrongClassSpace) :
    ccmRationalStrongClassSpaceRightAction 1 f = f := by
  apply ccmRationalStrongClassSpaceEvalLinear_injective
  funext b
  simp

theorem ccmRationalStrongClassSpaceRightAction_mul
    (c d : CCMRationalClassSpaceSection)
    (f : CCMRationalStrongClassSpace) :
    ccmRationalStrongClassSpaceRightAction c
        (ccmRationalStrongClassSpaceRightAction d f) =
      ccmRationalStrongClassSpaceRightAction (c * d) f := by
  apply ccmRationalStrongClassSpaceEvalLinear_injective
  funext b
  simp [mul_assoc, add_assoc]

theorem ccmRationalStrongClassSpaceRightAction_real
    (c : CCMRationalClassSpaceSection)
    (f : CCMRationalStrongClassSpace) :
    ccmRationalStrongClassSpaceRightAction c
        (ccmRationalStrongClassSpaceReal f) =
      ccmRationalStrongClassSpaceReal
        (ccmRationalStrongClassSpaceRightAction c f) := by
  apply ccmRationalStrongClassSpaceEvalLinear_injective
  funext b
  simp

theorem CCMRationalStrongClassSpaceScalarTarget.rightTranslate_mem
    {s : CCMRationalClassSpaceSection → ℂ}
    (hs : s ∈ CCMRationalStrongClassSpaceScalarTarget)
    (c : CCMRationalClassSpaceSection) :
    (fun b => s (b * c)) ∈ CCMRationalStrongClassSpaceScalarTarget := by
  rcases hs with ⟨f, rfl⟩
  exact ⟨ccmRationalStrongClassSpaceRightAction c f, by
    funext b
    simp⟩

theorem CCMRationalStrongClassSpaceScalarTarget.real_mem
    {s : CCMRationalClassSpaceSection → ℂ}
    (hs : s ∈ CCMRationalStrongClassSpaceScalarTarget) :
    (fun b => star (s b)) ∈ CCMRationalStrongClassSpaceScalarTarget := by
  rcases hs with ⟨f, rfl⟩
  exact ⟨ccmRationalStrongClassSpaceReal f, by
    funext b
    simp⟩

end RHTower
end GaloisForLFunctions
