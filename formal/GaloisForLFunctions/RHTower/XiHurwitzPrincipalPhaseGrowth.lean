import GaloisForLFunctions.RHTower.CCMRectangularTransverseGrowth
import GaloisForLFunctions.RHTower.XiHurwitzConstraintOrientation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Principal Hurwitz phase as the sharp transverse Xi growth exponent

The open critical strip removes the integer ambiguity in the principal argument of the negative
Hurwitz monodromy character.  Its normalized absolute phase at a right-half Xi zero is exactly the
horizontal displacement from the critical line.  Taking the supremum therefore identifies a
pure HGT value invariant with the sharp power exponent of the fixed-width logarithmic rectangular
Weil sequence.
-/

open Complex Set
open GaloisForLFunctions

namespace RHTower

noncomputable section

open HurwitzOrbit

/-- **Exact open-strip phase law.**  The principal branch of the negative Hurwitz monodromy
character recovers horizontal displacement from the critical line without any trigonometric
aliasing. -/
theorem monoScalar_neg_arg_openCriticalStrip {s : ℂ}
    (hs : 0 < s.re ∧ s.re < 1) :
    (-monoScalar s).arg = -2 * Real.pi * (s.re - 1 / 2) := by
  let θ : ℝ := -2 * Real.pi * (s.re - 1 / 2)
  have hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi := by
    dsimp only [θ]
    constructor <;> nlinarith [Real.pi_pos]
  have hdecomp :
      -monoScalar s =
        ((Real.exp (2 * Real.pi * s.im) : ℝ) : ℂ) *
          Complex.exp ((θ : ℂ) * I) := by
    rw [monoScalar]
    calc
      -Complex.exp (-(2 * (Real.pi : ℂ) * I * s)) =
          Complex.exp ((Real.pi : ℂ) * I) *
            Complex.exp (-(2 * (Real.pi : ℂ) * I * s)) := by
              rw [Complex.exp_pi_mul_I]
              simp
      _ = Complex.exp
          (((Real.pi : ℂ) * I) + -(2 * (Real.pi : ℂ) * I * s)) := by
            rw [Complex.exp_add]
      _ = Complex.exp
          (((2 * Real.pi * s.im : ℝ) : ℂ) + (θ : ℂ) * I) := by
            congr 1
            apply Complex.ext
            · simp [θ]
            · simp [θ]
              ring
      _ = Complex.exp (((2 * Real.pi * s.im : ℝ) : ℂ)) *
          Complex.exp ((θ : ℂ) * I) := by
            rw [Complex.exp_add]
      _ = ((Real.exp (2 * Real.pi * s.im) : ℝ) : ℂ) *
          Complex.exp ((θ : ℂ) * I) := by
            rw [Complex.ofReal_exp]
  have hθmod : θ ∈ Set.Ioc (-Real.pi)
      (-Real.pi + 2 * Real.pi) := by
    have hu : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [hu]
    exact hθ
  have hmod : toIocMod Real.two_pi_pos (-Real.pi) θ = θ :=
    (toIocMod_eq_self Real.two_pi_pos).2 hθmod
  rw [hdecomp, Complex.arg_real_mul _ (Real.exp_pos _),
    Complex.arg_exp_mul_I, hmod]

/-- Normalized absolute principal phase of the negative Hurwitz character on one right-half Xi
zero copy. -/
def xiHurwitzRightPrincipalPhase (q : XiRightZeroCopy) : ℝ :=
  |(-xiHurwitzMonodromyCharacter q.1.1).arg| / (2 * Real.pi)

/-- The normalized HGT phase is pointwise exactly the positive transverse Xi displacement. -/
theorem xiHurwitzRightPrincipalPhase_eq_transverse (q : XiRightZeroCopy) :
    xiHurwitzRightPrincipalPhase q = (xiRightCenteredZero q).re := by
  have harg := monoScalar_neg_arg_openCriticalStrip
    (s := (q.1.1 : ℂ)) (xi_divisor_support_re_mem_open_unit q.1.1)
  rw [xiHurwitzRightPrincipalPhase]
  change |(-HurwitzOrbit.monoScalar (q.1.1 : ℂ)).arg| /
      (2 * Real.pi) = _
  rw [harg, xiRightCenteredZero_eq_support_sub_half]
  have hhalf : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by norm_num
  rw [Complex.sub_re, hhalf]
  change |-2 * Real.pi * ((q.1.1 : ℂ).re - 1 / 2)| /
      (2 * Real.pi) = (q.1.1 : ℂ).re - 1 / 2
  have hdelta : 0 < (q.1.1 : ℂ).re - 1 / 2 := by
    have hpos := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half] at hpos
    norm_num at hpos
    linarith
  have hneg : -2 * Real.pi * ((q.1.1 : ℂ).re - 1 / 2) < 0 := by
    nlinarith [Real.pi_pos]
  rw [abs_of_neg hneg]
  field_simp [Real.pi_ne_zero]

/-- Value-side set of all positive principal Hurwitz phases carried by right-half Xi zeros. -/
def xiHurwitzRightPrincipalPhaseSet : Set ℝ :=
  Set.range xiHurwitzRightPrincipalPhase

/-- Supremal normalized principal Hurwitz phase. -/
noncomputable def xiHurwitzRightPrincipalPhaseSup : ℝ :=
  sSup xiHurwitzRightPrincipalPhaseSet

theorem xiHurwitzRightPrincipalPhaseSet_eq_transverseSet :
    xiHurwitzRightPrincipalPhaseSet = xiRightTransverseSet := by
  unfold xiHurwitzRightPrincipalPhaseSet xiRightTransverseSet
  congr 1
  funext q
  exact xiHurwitzRightPrincipalPhase_eq_transverse q

/-- **Phase--divisor supremum identity.**  The supremal HGT character phase is exactly the
rightmost horizontal displacement of the Xi divisor. -/
theorem xiHurwitzRightPrincipalPhaseSup_eq_transverseSup :
    xiHurwitzRightPrincipalPhaseSup = xiRightTransverseSup := by
  rw [xiHurwitzRightPrincipalPhaseSup, xiRightTransverseSup,
    xiHurwitzRightPrincipalPhaseSet_eq_transverseSet]

/-- RH is precisely the zero-phase boundary of the supremal principal Hurwitz character. -/
theorem riemannHypothesis_iff_xiHurwitzRightPrincipalPhaseSup_eq_zero :
    RiemannHypothesis ↔ xiHurwitzRightPrincipalPhaseSup = 0 := by
  constructor
  · intro hRH
    have hempty : IsEmpty XiRightZeroCopy := by
      refine ⟨fun q => ?_⟩
      have hs : ((q.1.1 : ℂ)).re = 1 / 2 :=
        xi_divisor_support_re_eq_half_of_rh hRH q.1.1
      have hpos := xiRightCenteredZero_re_pos q
      rw [xiRightCenteredZero_eq_support_sub_half] at hpos
      norm_num at hpos
      linarith
    rw [xiHurwitzRightPrincipalPhaseSup,
      xiHurwitzRightPrincipalPhaseSet]
    have hrange : Set.range xiHurwitzRightPrincipalPhase = ∅ := by
      exact Set.range_eq_empty_iff.mpr hempty
    rw [hrange, Real.sSup_empty]
  · intro hzero
    by_contra hRH
    have hne := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    rw [xiHurwitzRightPrincipalPhaseSup_eq_transverseSup] at hzero
    linarith [xiRightTransverseSup_pos hne]

/-- **Principal-phase sharp-growth law.**  For every fixed positive width, whenever the positive
transverse divisor is nonempty, the supremal principal phase of the Xi-indexed Hurwitz monodromy
characters is exactly the sharp power exponent of the logarithmically sampled rectangular Weil
sequence.  The first clause is the matching upper power law; the second excludes every smaller
power cofinally. -/
theorem xiHurwitzPrincipalPhaseSup_is_sharp_rectangular_power_exponent
    {L : ℝ} (hL : 0 < L) (hne : Nonempty XiRightZeroCopy) :
    (∀ n : ℕ, 1 ≤ n → L ≤ Real.log n / 2 →
      ‖xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖ ≤
        (2 * xiRectangularRightCoefficientNormSum L +
          rectangularTwoEdgeRemainderBound L *
            ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) *
          (n : ℝ) ^ xiHurwitzRightPrincipalPhaseSup) ∧
    (∀ α : ℝ, 0 ≤ α → α < xiHurwitzRightPrincipalPhaseSup →
      ∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
        N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
        C * (n : ℝ) ^ α <
          ‖xiWeilPolarization
            (xiRectangularTwoEdgeTransform L (Real.log n / 2))
            (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖) := by
  rw [xiHurwitzRightPrincipalPhaseSup_eq_transverseSup]
  exact xiRightTransverseSup_is_sharp_rectangular_power_exponent hL hne

end

end RHTower
