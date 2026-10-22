import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheEscapeIsAnInteriorBump
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SignedDampingWorkOfTheMobiusEnergy

/-!
# One sign change of the signed work closes the problem

Both ends of the damping range are paid, so what has to be excluded is an interior bump.  A bump
needs the energy to rise and then fall, hence the signed work — half the energy's damping
derivative — must change sign from positive to negative somewhere inside.  Forbidding *that* order
of sign change is therefore enough:

if for every horizon the signed work, once nonnegative at some damping, stays nonnegative up to
half damping, then the energy is antitone before the crossing and monotone after it, no interior
bump exists, and the Riemann hypothesis follows
(`riemannHypothesis_of_signedWork_single_sign_change`).

This is a hypothesis of a different kind from the bounds the layer has used so far: no constant, no
norm and no uniformity in the horizon beyond the shape itself.  Monotonicity of the work in the
damping — equivalently convexity of the critical energy — is the special case
(`riemannHypothesis_of_monotoneOn_signedWork`), and so is nonnegativity of the work everywhere,
which the autocorrelation sign criterion already gives.
-/

open Set Filter Finset Topology RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. Sign of the work controls the shape of the energy -/

private theorem antitoneOn_of_hasDerivAt_nonpos {a b : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Icc a b, f' x ≤ 0) :
    AntitoneOn f (Icc a b) := by
  have hmono : MonotoneOn (fun z => -f z) (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (f' := fun z => -f' z)
      (fun z hz => ((hf z hz).continuousAt.neg).continuousWithinAt) ?_ ?_
    · intro z hz
      rw [interior_Icc] at hz
      exact ((hf z (Ioo_subset_Icc_self hz)).neg).hasDerivWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      linarith [hf' z (Ioo_subset_Icc_self hz)]
  intro x hx y hy hxy
  have := hmono hx hy hxy
  linarith

/-- Nonpositive work on a compact damping interval away from zero: the energy falls. -/
theorem antitoneOn_dampedMobiusEnergy_of_signedWork_nonpos {a b : ℝ} (ha : 0 < a) (T : ℕ)
    (hW : ∀ ε ∈ Icc a b, signedDampingWork ε T ≤ 0) :
    AntitoneOn (fun ε => dampedMobiusEnergy ε T) (Icc a b) :=
  antitoneOn_of_hasDerivAt_nonpos (f' := fun ε => 2 * signedDampingWork ε T)
    (fun x hx => hasDerivAt_dampedMobiusEnergy (lt_of_lt_of_le ha hx.1) T)
    fun x hx => by linarith [hW x hx]

/-- Nonnegative work on a compact damping interval away from zero: the energy rises. -/
theorem monotoneOn_dampedMobiusEnergy_of_signedWork_nonneg {a b : ℝ} (ha : 0 < a) (T : ℕ)
    (hW : ∀ ε ∈ Icc a b, 0 ≤ signedDampingWork ε T) :
    MonotoneOn (fun ε => dampedMobiusEnergy ε T) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (f' := fun ε => 2 * signedDampingWork ε T)
    (fun z hz => ((hasDerivAt_dampedMobiusEnergy (lt_of_lt_of_le ha hz.1) T).continuousAt
      ).continuousWithinAt) ?_ ?_
  · intro z hz
    rw [interior_Icc] at hz
    exact (hasDerivAt_dampedMobiusEnergy
      (lt_of_lt_of_le ha (Ioo_subset_Icc_self hz).1) T).hasDerivWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    linarith [hW z (Ioo_subset_Icc_self hz)]

/-! ## §2. The single-sign-change criterion -/

/-- **One sign change of the signed work gives the Riemann hypothesis.**  If at every horizon the
work, once nonnegative, stays nonnegative up to half damping, then no horizon's energy exceeds the
larger of its two paid end values. -/
theorem riemannHypothesis_of_signedWork_single_sign_change
    (h : ∀ (T : ℕ) (x : ℝ), 0 < x → x ≤ 1 / 2 → 0 ≤ signedDampingWork x T →
      ∀ y ∈ Icc x (1 / 2 : ℝ), 0 ≤ signedDampingWork y T) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_no_interior_bump fun T ε hε hε2 δ hδ hδε => ?_
  by_cases hsign : 0 ≤ signedDampingWork ε T
  · have hmono := monotoneOn_dampedMobiusEnergy_of_signedWork_nonneg hε T
      fun x hx => h T ε hε hε2 hsign x hx
    exact le_max_of_le_right
      (hmono (left_mem_Icc.mpr hε2) (right_mem_Icc.mpr hε2) hε2)
  · have hneg : ∀ x ∈ Icc δ ε, signedDampingWork x T ≤ 0 := by
      intro x hx
      by_contra hpos
      have hx0 : 0 < x := lt_of_lt_of_le hδ hx.1
      have hx2 : x ≤ 1 / 2 := le_trans hx.2 hε2
      exact hsign (h T x hx0 hx2 (le_of_not_ge hpos) ε ⟨hx.2, hε2⟩)
    have hanti := antitoneOn_dampedMobiusEnergy_of_signedWork_nonpos hδ T hneg
    exact le_max_of_le_left
      (hanti (left_mem_Icc.mpr hδε.le) (right_mem_Icc.mpr hδε.le) hδε.le)

/-- **Monotone work gives the Riemann hypothesis.**  Equivalently: convexity of the critical energy
in the damping, which is a condition on the pairing of the source with the second damping tangent
and not on any norm. -/
theorem riemannHypothesis_of_monotoneOn_signedWork
    (h : ∀ T : ℕ, MonotoneOn (fun ε => signedDampingWork ε T) (Ioc (0 : ℝ) (1 / 2))) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_signedWork_single_sign_change fun T x hx hx2 hsign y hy => ?_
  have hy0 : 0 < y := lt_of_lt_of_le hx hy.1
  exact le_trans hsign ((h T) (mem_Ioc.mpr ⟨hx, hx2⟩) (mem_Ioc.mpr ⟨hy0, hy.2⟩) hy.1)

/-- Nonnegative work everywhere is the degenerate case of one sign change. -/
theorem riemannHypothesis_of_nonneg_signedWork
    (h : ∀ (T : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 → 0 ≤ signedDampingWork ε T) :
    RiemannHypothesis :=
  riemannHypothesis_of_signedWork_single_sign_change fun T _ hx _ _ y hy =>
    h T y (lt_of_lt_of_le hx hy.1) hy.2

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
