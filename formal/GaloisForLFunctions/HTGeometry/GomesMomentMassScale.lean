import GaloisForLFunctions.HTGeometry.GomesFavardData
import GaloisForLFunctions.HTGeometry.GomesMomentFrameTransport
import GaloisForLFunctions.HTGeometry.ComplexSecondKind

/-!
# Positive mass as a character forgotten by monic frames

Application of invariant-menu limitations in https://arxiv.org/abs/2607.24901
and internal-frame geometry in https://arxiv.org/abs/2404.10461.
Positive rescaling changes every moment inner product and squared norm by its
mass character, while every monic polynomial, Jacobi coefficient, second-kind
polynomial, and complete recurrence frame remains unchanged. The algebraic
invariance even holds for arbitrary degenerate input sequences.
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- Positive rescaling of the full moment functional by its logarithmic mass. -/
def gomesMomentMassScale (r : ℝ) (s : ℕ → ℝ) (n : ℕ) : ℝ := Real.exp r*s n

/-- The entire moment bilinear form has exactly the mass character. -/
theorem gomesMomentMassScale_inner (r : ℝ) (s : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentInner (gomesMomentMassScale r s) p q = Real.exp r*momentInner s p q := by
  exact momentFunctional_smul_sequence s (Real.exp r) (p*q)

/-- Positive mass rescaling preserves and reflects strict moment positivity. -/
theorem gomesMomentMassScale_positive_iff (r : ℝ) (s : ℕ → ℝ) :
    PositiveMomentForm (gomesMomentMassScale r s) ↔ PositiveMomentForm s := by
  constructor
  · intro h
    refine ⟨fun p hp => ?_⟩
    have hh := h.pos_of_ne_zero p hp
    rw [gomesMomentMassScale_inner] at hh
    exact pos_of_mul_pos_right hh (Real.exp_pos r).le
  · intro h
    refine ⟨fun p hp => ?_⟩
    rw [gomesMomentMassScale_inner]
    exact mul_pos (Real.exp_pos r) (h.pos_of_ne_zero p hp)

/-- Gram--Schmidt's monic family forgets positive mass even for arbitrary, possibly degenerate sequences. -/
theorem gomesMomentMassScale_monicOrtho (r : ℝ) (s : ℕ → ℝ) (n : ℕ) :
    monicOrtho (gomesMomentMassScale r s) n = monicOrtho s n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [monicOrtho_eq,monicOrtho_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih k k.isLt,gomesMomentMassScale_inner,gomesMomentMassScale_inner,
        mul_div_mul_left _ _ (Real.exp_ne_zero r)]

/-- Squared polynomial norms retain the mass forgotten by the monic family. -/
theorem gomesMomentMassScale_normSq (r : ℝ) (s : ℕ → ℝ) (n : ℕ) :
    monicOrthoNormSq (gomesMomentMassScale r s) n = Real.exp r*monicOrthoNormSq s n := by
  simp only [monicOrthoNormSq,gomesMomentMassScale_monicOrtho,gomesMomentMassScale_inner]

/-- Every diagonal Jacobi coefficient is insensitive to positive mass. -/
theorem gomesMomentMassScale_alpha (r : ℝ) (s : ℕ → ℝ) (n : ℕ) :
    monicOrthoAlpha (gomesMomentMassScale r s) n = monicOrthoAlpha s n := by
  simp only [monicOrthoAlpha,gomesMomentMassScale_monicOrtho,gomesMomentMassScale_normSq,
    gomesMomentMassScale_inner]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero r)

/-- Every lower Jacobi coefficient, including the canonical zero endpoint, forgets mass. -/
theorem gomesMomentMassScale_beta (r : ℝ) (s : ℕ → ℝ) (n : ℕ) :
    monicOrthoBeta (gomesMomentMassScale r s) n = monicOrthoBeta s n := by
  cases n with
  | zero => rfl
  | succ n =>
      simp only [monicOrthoBeta,gomesMomentMassScale_normSq]
      exact mul_div_mul_left _ _ (Real.exp_ne_zero r)

/-- The existing second-kind recurrence diagonal has the same mass invariance. -/
theorem gomesMomentMassScale_recurDiag (r : ℝ) (s : ℕ → ℝ) (n : ℕ) :
    recurDiag (gomesMomentMassScale r s) n = recurDiag s n := by
  simp only [recurDiag,gomesMomentMassScale_monicOrtho,gomesMomentMassScale_inner]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero r)

/-- The existing second-kind recurrence coupling has the same mass invariance. -/
theorem gomesMomentMassScale_recurOff (r : ℝ) (s : ℕ → ℝ) (n : ℕ) :
    recurOff (gomesMomentMassScale r s) n = recurOff s n := by
  simp only [recurOff,gomesMomentMassScale_monicOrtho,gomesMomentMassScale_inner]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero r)

/-- The full second-kind family also forgets the absolute moment mass. -/
theorem gomesMomentMassScale_secondKind (r : ℝ) (s : ℕ → ℝ) (n : ℕ) :
    secondKind (gomesMomentMassScale r s) n = secondKind s n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp
      | succ n =>
        rw [secondKind_succ_succ,secondKind_succ_succ,ih (n+1) (by omega),ih n (by omega),
          gomesMomentMassScale_recurDiag,gomesMomentMassScale_recurOff]

/-- The entire existing real two-solution frame loses the positive mass parameter. -/
theorem gomesMomentMassScale_frame (r : ℝ) (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    gomesMomentFrame (gomesMomentMassScale r s) n x = gomesMomentFrame s n x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesMomentFrame,gomesMomentMassScale_monicOrtho,gomesMomentMassScale_secondKind]

/-- Complex evaluation does not restore mass information to the first-kind channel. -/
theorem gomesMomentMassScale_monicOrthoC (r : ℝ) (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    monicOrthoC (gomesMomentMassScale r s) n z = monicOrthoC s n z := by
  simp [monicOrthoC,gomesMomentMassScale_monicOrtho]

/-- Complex evaluation does not restore mass information to the second-kind channel. -/
theorem gomesMomentMassScale_secondKindC (r : ℝ) (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    secondKindC (gomesMomentMassScale r s) n z = secondKindC s n z := by
  simp [secondKindC,gomesMomentMassScale_secondKind]

end GaloisForLFunctions.HTGeometry
