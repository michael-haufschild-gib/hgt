import GaloisForLFunctions.RHTower.EulerSquarefreeWickCompletedJetBundleLanding
import GaloisForLFunctions.RHTower.DirichletLZerosInfinite
import GaloisForLFunctions.RHTower.CompletedFluxGradedReality
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.HTGeometry.ShiftedEulerTangentFiltration

/-!
# Completed EWQ jet orientation rigidity

The completed EWQ jet bundle removes auxiliary-zero selection, but a completed landing also needs
an orientation law.  The primitive mod-12 interaction supplies its own law: Schwarz conjugation
and the self-dual functional equation grade its full Taylor jet by root number and derivative
parity.

This module proves the converse without an aperiodicity premise.  If the graded law held away from
the critical line, its full jet would create a second holomorphic reflection center.  Comparing
that center with the functional equation gives a nonzero real period.  Such a period is impossible:
an actual completed Dirichlet zero, translated repeatedly, would leave the unconditional strip
`0 < re(s) < 1`.  Thus the full EWQ jet orientation locus is exactly the critical line.
-/

open Complex Filter Set Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The primitive EWQ completion has the Schwarz real structure inherited from its real
quadratic coefficients. -/
theorem eulerWickPrimitiveCompletedInteraction_conj (s : ℂ) :
    eulerWickQuadraticPrimitiveCompletedInteraction ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (eulerWickQuadraticPrimitiveCompletedInteraction s) := by
  rw [eulerWickQuadraticPrimitiveCompletedInteraction,
    _root_.RHTower.dirichletXi, _root_.RHTower.dirichletXi]
  rw [map_mul, _root_.RHTower.conj_completedLFunction quadraticCharacterTwelve_ne_one]
  rw [quadraticCharacterTwelve_inv]
  congr 1
  have hpow := _root_.RHTower.natCast_cpow_conj 12 (s / 2)
  rw [map_div₀, map_ofNat] at hpow
  exact hpow

/-- The self-dual EWQ root number is a literal sign. -/
theorem quadraticCharacterTwelve_rootNumber_eq_one_or_neg_one :
    quadraticCharacterTwelve.rootNumber = 1 ∨
      quadraticCharacterTwelve.rootNumber = -1 := by
  apply mul_self_eq_one_iff.mp
  have hfirst := eulerWickQuadraticPrimitiveCompletedInteraction_one_sub (2 : ℂ)
  have hsecond := eulerWickQuadraticPrimitiveCompletedInteraction_one_sub (-1 : ℂ)
  norm_num at hfirst hsecond
  rw [hfirst] at hsecond
  apply mul_right_cancel₀ eulerWickQuadraticPrimitiveCompletedInteraction_two_ne_zero
  calc
    (quadraticCharacterTwelve.rootNumber * quadraticCharacterTwelve.rootNumber) *
        eulerWickQuadraticPrimitiveCompletedInteraction 2 =
      quadraticCharacterTwelve.rootNumber *
        (quadraticCharacterTwelve.rootNumber *
          eulerWickQuadraticPrimitiveCompletedInteraction 2) := by ring
    _ = eulerWickQuadraticPrimitiveCompletedInteraction 2 := hsecond.symm
    _ = 1 * eulerWickQuadraticPrimitiveCompletedInteraction 2 := by ring

theorem quadraticCharacterTwelve_rootNumber_conj :
    (starRingEnd ℂ) quadraticCharacterTwelve.rootNumber =
      quadraticCharacterTwelve.rootNumber := by
  rcases quadraticCharacterTwelve_rootNumber_eq_one_or_neg_one with h | h
  · simp [h]
  · simp [h]

/-- Iterated EWQ jets satisfy Schwarz reflection. -/
theorem eulerWickPrimitiveCompletedInteraction_iteratedDeriv_conj
    (s : ℂ) (n : ℕ) :
    iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction
        ((starRingEnd ℂ) s) =
      (starRingEnd ℂ)
        (iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s) := by
  have hfun :
      (starRingEnd ℂ) ∘ eulerWickQuadraticPrimitiveCompletedInteraction ∘
          (starRingEnd ℂ) =
        eulerWickQuadraticPrimitiveCompletedInteraction := by
    funext z
    simp only [Function.comp_apply]
    rw [eulerWickPrimitiveCompletedInteraction_conj]
    simp
  have hd := _root_.RHTower.iteratedDeriv_conj_conj
    eulerWickQuadraticPrimitiveCompletedInteraction n
  rw [hfun] at hd
  simpa [Function.comp_apply] using congrFun hd ((starRingEnd ℂ) s)

/-- The self-dual functional equation grades the completed EWQ jet by derivative parity. -/
theorem eulerWickPrimitiveCompletedInteraction_iteratedDeriv_one_sub
    (s : ℂ) (n : ℕ) :
    iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction (1 - s) =
      quadraticCharacterTwelve.rootNumber * (-1 : ℂ) ^ n *
        iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s := by
  have hfun : (fun z : ℂ =>
      eulerWickQuadraticPrimitiveCompletedInteraction (1 - z)) =
      fun z => quadraticCharacterTwelve.rootNumber *
        eulerWickQuadraticPrimitiveCompletedInteraction z := by
    funext z
    exact eulerWickQuadraticPrimitiveCompletedInteraction_one_sub z
  have hder := congrFun (congrArg (iteratedDeriv n) hfun) s
  have hanalytic : ∀ z : ℂ,
      AnalyticAt ℂ eulerWickQuadraticPrimitiveCompletedInteraction z := by
    intro z
    exact eulerWickQuadraticPrimitiveCompletedInteraction_differentiable.differentiableOn
      |>.analyticOnNhd isOpen_univ z (Set.mem_univ z)
  rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_sub n
      hanalytic 1 s,
    congrFun (GaloisForLFunctions.iteratedDeriv_const_mul_field
      quadraticCharacterTwelve.rootNumber
      eulerWickQuadraticPrimitiveCompletedInteraction n) s] at hder
  have hsign : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← pow_add]
    simp
  calc
    iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction (1 - s) =
        1 * iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction (1 - s) := by ring
    _ = (((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n)) *
        iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction (1 - s) := by rw [hsign]
    _ = (-1 : ℂ) ^ n *
        (((-1 : ℂ) ^ n) *
          iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction (1 - s)) := by ring
    _ = (-1 : ℂ) ^ n *
        (quadraticCharacterTwelve.rootNumber *
          iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s) := by rw [hder]
    _ = quadraticCharacterTwelve.rootNumber * (-1 : ℂ) ^ n *
        iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s := by ring

/-- A positive real period would translate an actual completed Dirichlet zero out of its
unconditional open-strip confinement. -/
theorem eulerWickPrimitiveCompletedInteraction_not_pos_real_period
    {τ : ℝ} (hτ : 0 < τ)
    (hperiod : ∀ s : ℂ,
      eulerWickQuadraticPrimitiveCompletedInteraction (s + (τ : ℂ)) =
        eulerWickQuadraticPrimitiveCompletedInteraction s) : False := by
  obtain ⟨rho, hrho⟩ :=
    _root_.RHTower.exists_completedLFunction_eq_zero quadraticCharacterTwelve_ne_one
  have hrhoJ : eulerWickQuadraticPrimitiveCompletedInteraction rho = 0 := by
    simp [eulerWickQuadraticPrimitiveCompletedInteraction, _root_.RHTower.dirichletXi,
      hrho]
  have hper : Function.Periodic eulerWickQuadraticPrimitiveCompletedInteraction (τ : ℂ) :=
    hperiod
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt ((1 - rho.re) / τ)
  have hnτ : 1 - rho.re < (n : ℝ) * τ := (div_lt_iff₀ hτ).mp hn
  have htranslated :
      eulerWickQuadraticPrimitiveCompletedInteraction
        (rho + (n : ℂ) * (τ : ℂ)) = 0 := by
    rw [(hper.nat_mul n) rho, hrhoJ]
  have hcompleted :
      DirichletCharacter.completedLFunction quadraticCharacterTwelve
        (rho + (n : ℂ) * (τ : ℂ)) = 0 := by
    rw [eulerWickQuadraticPrimitiveCompletedInteraction,
      _root_.RHTower.dirichletXi] at htranslated
    exact (mul_eq_zero.mp htranslated).resolve_left
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
  have hstrip := _root_.RHTower.completedLFunction_zero_mem_openUnitStrip
    quadraticCharacterTwelve_ne_one quadraticCharacterTwelve_isPrimitive hcompleted
  have hre : (rho + (n : ℂ) * (τ : ℂ)).re = rho.re + (n : ℝ) * τ := by
    simp
  rw [hre] at hstrip
  linarith

/-- The primitive EWQ completion has no nonzero real period. -/
theorem eulerWickPrimitiveCompletedInteraction_not_real_period
    {τ : ℝ} (hτ : τ ≠ 0) :
    ¬ ∀ s : ℂ,
      eulerWickQuadraticPrimitiveCompletedInteraction (s + (τ : ℂ)) =
        eulerWickQuadraticPrimitiveCompletedInteraction s := by
  intro hperiod
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · apply eulerWickPrimitiveCompletedInteraction_not_pos_real_period
      (τ := -τ) (by linarith)
    have hper : Function.Periodic eulerWickQuadraticPrimitiveCompletedInteraction (τ : ℂ) :=
      hperiod
    have hperNeg := hper.neg
    intro s
    simpa only [Complex.ofReal_neg] using hperNeg s
  · exact eulerWickPrimitiveCompletedInteraction_not_pos_real_period hpos hperiod

/-- Root-number graded Schwarz reality of the full completed EWQ jet. -/
def EulerWickPrimitiveCompletedJetGradedRealAt (s : ℂ) : Prop :=
  ∀ n : ℕ,
    (starRingEnd ℂ)
        (iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s) =
      quadraticCharacterTwelve.rootNumber * (-1 : ℂ) ^ n *
        iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s

/-- On the critical line, Schwarz reflection and the EWQ functional equation coincide on every
jet coordinate. -/
theorem eulerWickPrimitiveCompletedJetGradedRealAt_of_re_eq_half
    {s : ℂ} (hs : s.re = 1 / 2) :
    EulerWickPrimitiveCompletedJetGradedRealAt s := by
  intro n
  have hcenter : (1 : ℂ) - s = (starRingEnd ℂ) s := by
    apply Complex.ext
    · simp
      linarith
    · simp
  have hFE := eulerWickPrimitiveCompletedInteraction_iteratedDeriv_one_sub s n
  rw [hcenter,
    eulerWickPrimitiveCompletedInteraction_iteratedDeriv_conj] at hFE
  exact hFE

/-- All-order EWQ jet reality creates a second holomorphic reflection.  A second center would
produce a forbidden real period, so its fixed line must be the critical line. -/
theorem re_eq_half_of_eulerWickPrimitiveCompletedJetGradedRealAt
    {s : ℂ} (hs : EulerWickPrimitiveCompletedJetGradedRealAt s) :
    s.re = 1 / 2 := by
  let beta : ℝ := s.re
  let eps : ℂ := quadraticCharacterTwelve.rootNumber
  let reflected : ℂ → ℂ := fun z =>
    eulerWickQuadraticPrimitiveCompletedInteraction (2 * (beta : ℂ) - z)
  let target : ℂ → ℂ := fun z =>
    eps * eulerWickQuadraticPrimitiveCompletedInteraction z
  let defect : ℂ → ℂ := fun z => reflected z - target z
  have hJanalytic : ∀ z : ℂ,
      AnalyticAt ℂ eulerWickQuadraticPrimitiveCompletedInteraction z := by
    intro z
    exact eulerWickQuadraticPrimitiveCompletedInteraction_differentiable.differentiableOn
      |>.analyticOnNhd isOpen_univ z (Set.mem_univ z)
  have hcenter : 2 * (beta : ℂ) - (starRingEnd ℂ) s = s := by
    apply Complex.ext
    · simp [beta]
      ring
    · simp
  have hrootSq : eps * eps = 1 := by
    exact mul_self_eq_one_iff.mpr
      quadraticCharacterTwelve_rootNumber_eq_one_or_neg_one
  have hreflectedAnalytic : ∀ z : ℂ, AnalyticAt ℂ reflected z := by
    intro z
    dsimp [reflected]
    fun_prop
  have htargetAnalytic : ∀ z : ℂ, AnalyticAt ℂ target z := by
    intro z
    dsimp [target, eps]
    fun_prop
  have hflat : ∀ n : ℕ, iteratedDeriv n defect ((starRingEnd ℂ) s) = 0 := by
    intro n
    rw [show iteratedDeriv n defect ((starRingEnd ℂ) s) =
        iteratedDeriv n reflected ((starRingEnd ℂ) s) -
          iteratedDeriv n target ((starRingEnd ℂ) s) by
      exact GaloisForLFunctions.HTGeometry.iteratedDeriv_fun_sub n
        hreflectedAnalytic htargetAnalytic ((starRingEnd ℂ) s)]
    rw [show iteratedDeriv n reflected ((starRingEnd ℂ) s) =
        (-1 : ℂ) ^ n *
          iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction
            (2 * (beta : ℂ) - (starRingEnd ℂ) s) by
      exact GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_sub n
        hJanalytic (2 * (beta : ℂ)) ((starRingEnd ℂ) s)]
    rw [show iteratedDeriv n target ((starRingEnd ℂ) s) =
        eps * iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction
          ((starRingEnd ℂ) s) by
      exact congrFun (GaloisForLFunctions.iteratedDeriv_const_mul_field
        eps eulerWickQuadraticPrimitiveCompletedInteraction n) ((starRingEnd ℂ) s)]
    rw [hcenter,
      eulerWickPrimitiveCompletedInteraction_iteratedDeriv_conj,
      hs n]
    dsimp [eps] at hrootSq ⊢
    calc
      (-1 : ℂ) ^ n *
            iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s -
          quadraticCharacterTwelve.rootNumber *
            (quadraticCharacterTwelve.rootNumber * (-1 : ℂ) ^ n *
              iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s) =
        (1 - quadraticCharacterTwelve.rootNumber *
          quadraticCharacterTwelve.rootNumber) * (-1 : ℂ) ^ n *
            iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s := by ring
      _ = 0 := by rw [hrootSq]; ring
  have hdefectDifferentiable : Differentiable ℂ defect := by
    dsimp [defect, reflected, target, eps]
    exact (eulerWickQuadraticPrimitiveCompletedInteraction_differentiable.comp
      ((differentiable_const _).sub differentiable_id)).sub
        ((differentiable_const _).mul
          eulerWickQuadraticPrimitiveCompletedInteraction_differentiable)
  have hdefectAnalytic : AnalyticOnNhd ℂ defect Set.univ :=
    hdefectDifferentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hgerm : defect =ᶠ[nhds ((starRingEnd ℂ) s)] 0 :=
    _root_.HTGeometry.eventuallyEq_zero_of_iteratedDeriv_eq_zero
      (hdefectAnalytic _ (Set.mem_univ _)) hflat
  have hglobal : Set.EqOn defect 0 Set.univ :=
    hdefectAnalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ _) hgerm
  have hreflection : ∀ z : ℂ,
      eulerWickQuadraticPrimitiveCompletedInteraction (2 * (beta : ℂ) - z) =
        eps * eulerWickQuadraticPrimitiveCompletedInteraction z := by
    intro z
    have hz := hglobal (Set.mem_univ z)
    simpa [defect, reflected, target, sub_eq_zero] using hz
  let tau : ℝ := 2 * beta - 1
  have hperiod : ∀ u : ℂ,
      eulerWickQuadraticPrimitiveCompletedInteraction (u + (tau : ℂ)) =
        eulerWickQuadraticPrimitiveCompletedInteraction u := by
    intro u
    calc
      eulerWickQuadraticPrimitiveCompletedInteraction (u + (tau : ℂ)) =
          eulerWickQuadraticPrimitiveCompletedInteraction
            (2 * (beta : ℂ) - (1 - u)) := by
              congr 1
              dsimp [tau]
              push_cast
              ring
      _ = eps * eulerWickQuadraticPrimitiveCompletedInteraction (1 - u) :=
        hreflection (1 - u)
      _ = eps * (quadraticCharacterTwelve.rootNumber *
          eulerWickQuadraticPrimitiveCompletedInteraction u) := by
        rw [eulerWickQuadraticPrimitiveCompletedInteraction_one_sub]
      _ = eulerWickQuadraticPrimitiveCompletedInteraction u := by
        dsimp [eps] at hrootSq ⊢
        rw [← mul_assoc, hrootSq, one_mul]
  have htau : tau = 0 := by
    by_contra hne
    exact eulerWickPrimitiveCompletedInteraction_not_real_period hne hperiod
  dsimp [tau, beta] at htau
  linarith

/-- **Exact EWQ completed-jet orientation law.**  The all-order root-number graded real locus is
precisely the critical line. -/
theorem eulerWickPrimitiveCompletedJetGradedRealAt_iff_re_eq_half (s : ℂ) :
    EulerWickPrimitiveCompletedJetGradedRealAt s ↔ s.re = 1 / 2 := by
  exact ⟨re_eq_half_of_eulerWickPrimitiveCompletedJetGradedRealAt,
    eulerWickPrimitiveCompletedJetGradedRealAt_of_re_eq_half⟩

/-- The nonzero square-zero completed jet landing plus its intrinsic EWQ orientation is exactly
the critical-line Xi divisor. -/
theorem eulerWickCompletedJetExtension_orientedSquareZero_iff (s : ℂ) :
    ((∃ n : ℕ, eulerWickCompletedJetExtension s n ≠ 0 ∧
        eulerWickCompletedJetExtension s n * eulerWickCompletedJetExtension s n = 0) ∧
      EulerWickPrimitiveCompletedJetGradedRealAt s) ↔
        _root_.RHTower.xi s = 0 ∧ s.re = 1 / 2 := by
  exact and_congr (eulerWickCompletedJetExtension_nonzero_squareZero_iff s)
    (eulerWickPrimitiveCompletedJetGradedRealAt_iff_re_eq_half s)

/-- Every Xi zero satisfies the intrinsic completed-EWQ orientation law. -/
def EveryXiZeroHasEulerWickCompletedJetOrientation : Prop :=
  ∀ s : ℂ, _root_.RHTower.xi s = 0 →
    EulerWickPrimitiveCompletedJetGradedRealAt s

/-- Global EWQ completed-jet orientation is exactly RH.  The statement uses the source-formed
primitive mod-12 carrier and its pre-divisor countable jet, with no auxiliary nonvanishing choice. -/
theorem everyXiZeroHasEulerWickCompletedJetOrientation_iff_riemannHypothesis :
    EveryXiZeroHasEulerWickCompletedJetOrientation ↔ RiemannHypothesis := by
  constructor
  · intro hall
    rw [_root_.RHTower.riemannHypothesis_iff_xi_zero_re_eq_half]
    intro s hs
    exact (eulerWickPrimitiveCompletedJetGradedRealAt_iff_re_eq_half s).mp (hall s hs)
  · intro hRH s hs
    apply (eulerWickPrimitiveCompletedJetGradedRealAt_iff_re_eq_half s).mpr
    exact (_root_.RHTower.riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH) s hs

end

end GaloisForLFunctions.RHTower
