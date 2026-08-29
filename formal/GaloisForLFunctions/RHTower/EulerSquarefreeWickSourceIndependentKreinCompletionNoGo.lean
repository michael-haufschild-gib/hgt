import GaloisForLFunctions.RHTower.PrimeTranslationKoszulOffLine
import GaloisForLFunctions.RHTower.XiCriticalLineIntegrality

/-!
# Source-independent Krein completion no-go for EWQ-V

The remaining EWQ-V matrix chamber allows unequal diagonal masses, auxiliary dimensions, and an
indefinite metric.  This file classifies that chamber without assuming positivity.  Fix any real
diagonal Hilbert/Krein metric on an arbitrary finite coefficient space.  A coefficient-faithful
completion places the literal Meyer--EWQ forward and inverse characters in two paired entries and
is self-adjoint for that metric.

One weighted-adjoint entry forces the reverse metric magnitude to be the forward metric magnitude
times the character modular weight.  Critical-line reflection reciprocates that weight.  Hence the
same source-independent nondegenerate metric cannot complete both points of an off-line reflection
orbit.  Completion on every Xi fibre therefore implies RH.

No positivity, purity, rank, equal-diagonal condition, or restriction on auxiliary entries is
used.  The positive survivor is exact: a single-fibre completion must tune its metric by
`‖chi‖²`, the source modular counterweight already identified by the corpus.  Thus a
divisor-dependent metric gives a receiver, while a fixed independent vacuum cannot be the missing
producer.
-/

open Complex Matrix
open scoped ComplexOrder MatrixOrder

namespace RHTower

noncomputable section

/-- The literal centered prime character used by the Meyer--EWQ coefficient pair.  The corpus
identifies this multiplier coefficient-for-coefficient with its Meyer/Gamma source reporter. -/
def ewqKreinXiPrimeCharacter (rho : XiDivisorSupport) (p : Nat.Primes) : ℂ :=
  deltaS p rho

theorem ewqKreinXiPrimeCharacter_ne_zero
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    ewqKreinXiPrimeCharacter rho p ≠ 0 := by
  intro hzero
  have hnorm := norm_deltaS p.2.pos (rho : ℂ)
  rw [← ewqKreinXiPrimeCharacter, hzero, norm_zero] at hnorm
  have hpos : 0 < (p : ℝ) ^ (1 / 2 - (rho : ℂ).re) :=
    Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  linarith

/-- Critical-line reflection reciprocates the norm of the actual Meyer--EWQ prime character. -/
theorem norm_ewqKreinXiPrimeCharacter_lineReflection
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    ‖ewqKreinXiPrimeCharacter (xiZeroLineConjEquiv rho) p‖ =
      ‖ewqKreinXiPrimeCharacter rho p‖⁻¹ := by
  rw [ewqKreinXiPrimeCharacter, ewqKreinXiPrimeCharacter,
    norm_deltaS p.2.pos, norm_deltaS p.2.pos]
  rw [← Real.rpow_neg (by positivity)]
  congr 1
  simp [xiZeroLineConjEquiv_apply]
  ring

/-- A coefficient-faithful completion in an arbitrary finite auxiliary space.  All entries except
the two literal source orientations are unrestricted.  The landing law is self-adjointness for a
fixed real diagonal metric, allowing positive, negative, and mixed signs. -/
def EWQSourceIndependentDiagonalKreinCompletionAt
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) (w : ι → ℝ) (rho : XiDivisorSupport) (p : Nat.Primes) : Prop :=
  ∃ M : Matrix ι ι ℂ,
    M i j = ewqKreinXiPrimeCharacter rho p ∧
    M j i = (ewqKreinXiPrimeCharacter rho p)⁻¹ ∧
    Mᴴ * Matrix.diagonal (fun k => (w k : ℂ)) =
      Matrix.diagonal (fun k => (w k : ℂ)) * M

/-- The weighted-adjoint equation at the coefficient-faithful channel pair.  Auxiliary entries
drop out because the metric is diagonal in the source coefficient basis. -/
theorem ewqSourceIndependentDiagonalKreinCompletion_weightedStar
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) (w : ι → ℝ) (rho : XiDivisorSupport) (p : Nat.Primes)
    (h : EWQSourceIndependentDiagonalKreinCompletionAt i j w rho p) :
    (w j : ℂ) * (star (ewqKreinXiPrimeCharacter rho p))⁻¹ =
      (w i : ℂ) * ewqKreinXiPrimeCharacter rho p := by
  rcases h with ⟨M, hij, hji, hstar⟩
  have hentry := congrFun (congrFun hstar i) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at hentry
  simp only [Matrix.diagonal] at hentry
  simp [hij, hji, mul_comm] at hentry
  exact hentry

/-- Abstract reflected-pair rigidity behind the EWQ-V no-go. -/
private theorem norm_eq_one_of_weighted_reflection_pair
    (x y : ℂ) (a b : ℝ) (hx : x ≠ 0) (ha : a ≠ 0)
    (hy : ‖y‖ = ‖x‖⁻¹)
    (hforward : (b : ℂ) * (star x)⁻¹ = (a : ℂ) * x)
    (hreflected : (b : ℂ) * (star y)⁻¹ = (a : ℂ) * y) :
    ‖x‖ = 1 := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hforwardNorm :
      ‖b‖ * ‖x‖⁻¹ = ‖a‖ * ‖x‖ := by
    simpa only [norm_mul, norm_inv, norm_star, Complex.norm_real] using
      congrArg norm hforward
  have hreflectedNorm :
      ‖b‖ * ‖y‖⁻¹ = ‖a‖ * ‖y‖ := by
    simpa only [norm_mul, norm_inv, norm_star, Complex.norm_real] using
      congrArg norm hreflected
  rw [hy] at hreflectedNorm
  rw [inv_inv] at hreflectedNorm
  have hforwardCleared : ‖b‖ = ‖a‖ * ‖x‖ ^ 2 := by
    calc
      ‖b‖ = (‖b‖ * ‖x‖⁻¹) * ‖x‖ := by field_simp
      _ = (‖a‖ * ‖x‖) * ‖x‖ := by rw [hforwardNorm]
      _ = ‖a‖ * ‖x‖ ^ 2 := by ring
  have hreflectedCleared : ‖b‖ * ‖x‖ ^ 2 = ‖a‖ := by
    calc
      ‖b‖ * ‖x‖ ^ 2 = (‖b‖ * ‖x‖) * ‖x‖ := by ring
      _ = (‖a‖ * ‖x‖⁻¹) * ‖x‖ := by rw [hreflectedNorm]
      _ = ‖a‖ := by field_simp
  rw [hforwardCleared] at hreflectedCleared
  have hfactor : ‖a‖ * (‖x‖ ^ 2 * ‖x‖ ^ 2 - 1) = 0 := by
    nlinarith
  have hfourth : ‖x‖ ^ 2 * ‖x‖ ^ 2 = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hapos.ne')
  have hsquare : ‖x‖ ^ 2 = 1 := by
    nlinarith [sq_nonneg (‖x‖ ^ 2)]
  nlinarith [norm_nonneg x]

/-- Exact positive survivor.  A single-fibre weighted completion uniquely fixes the magnitude
ratio of the two metric weights to the character's modular counterweight. -/
theorem ewqKrein_reverseWeightNorm_eq_forwardWeightNorm_mul_characterNormSq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) (w : ι → ℝ) (rho : XiDivisorSupport) (p : Nat.Primes)
    (h : EWQSourceIndependentDiagonalKreinCompletionAt i j w rho p) :
    ‖w j‖ = ‖w i‖ * ‖ewqKreinXiPrimeCharacter rho p‖ ^ 2 := by
  have hx : ewqKreinXiPrimeCharacter rho p ≠ 0 :=
    ewqKreinXiPrimeCharacter_ne_zero rho p
  have hxpos : 0 < ‖ewqKreinXiPrimeCharacter rho p‖ :=
    norm_pos_iff.mpr hx
  have hnorm := congrArg norm
    (ewqSourceIndependentDiagonalKreinCompletion_weightedStar i j w rho p h)
  simp only [norm_mul, norm_inv, norm_star, Complex.norm_real] at hnorm
  calc
    ‖w j‖ =
        (‖w j‖ * ‖ewqKreinXiPrimeCharacter rho p‖⁻¹) *
          ‖ewqKreinXiPrimeCharacter rho p‖ := by field_simp
    _ =
        (‖w i‖ * ‖ewqKreinXiPrimeCharacter rho p‖) *
          ‖ewqKreinXiPrimeCharacter rho p‖ := by rw [hnorm]
    _ = ‖w i‖ * ‖ewqKreinXiPrimeCharacter rho p‖ ^ 2 := by ring

/-- Two coefficient-faithful completions using the same nondegenerate metric at both points of an
Xi reflection orbit force unit character modulus. -/
theorem norm_ewqKreinXiPrimeCharacter_eq_one_of_reflectionPair_kreinCompletions
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) (w : ι → ℝ) (rho : XiDivisorSupport) (p : Nat.Primes)
    (hwi : w i ≠ 0)
    (hrho : EWQSourceIndependentDiagonalKreinCompletionAt i j w rho p)
    (hreflect : EWQSourceIndependentDiagonalKreinCompletionAt
      i j w (xiZeroLineConjEquiv rho) p) :
    ‖ewqKreinXiPrimeCharacter rho p‖ = 1 := by
  exact norm_eq_one_of_weighted_reflection_pair
    (ewqKreinXiPrimeCharacter rho p)
    (ewqKreinXiPrimeCharacter (xiZeroLineConjEquiv rho) p)
    (w i) (w j)
    (ewqKreinXiPrimeCharacter_ne_zero rho p) hwi
    (norm_ewqKreinXiPrimeCharacter_lineReflection rho p)
    (ewqSourceIndependentDiagonalKreinCompletion_weightedStar i j w rho p hrho)
    (ewqSourceIndependentDiagonalKreinCompletion_weightedStar
      i j w (xiZeroLineConjEquiv rho) p hreflect)

/-- One fixed diagonal-metric completion over every actual Xi divisor. -/
def EveryXiEWQSourceIndependentDiagonalKreinCompletion
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) (w : ι → ℝ) (p : Nat.Primes) : Prop :=
  ∀ rho : XiDivisorSupport,
    EWQSourceIndependentDiagonalKreinCompletionAt i j w rho p

/-- **EWQ-V route capstone.**  A source-independent nondegenerate diagonal Hilbert/Krein
completion in any finite auxiliary dimension already implies RH. -/
theorem riemannHypothesis_of_everyXiEWQSourceIndependentDiagonalKreinCompletion
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) (w : ι → ℝ) (p : Nat.Primes) (hwi : w i ≠ 0)
    (hcompletion : EveryXiEWQSourceIndependentDiagonalKreinCompletion i j w p) :
    RiemannHypothesis := by
  apply (riemannHypothesis_iff_xiZeroLineConj_fixed).2
  intro rho
  have hline : (rho : ℂ).re = 1 / 2 := by
    apply (norm_deltaS_eq_one_iff p.2.two_le (rho : ℂ)).1
    change ‖ewqKreinXiPrimeCharacter rho p‖ = 1
    exact
      norm_ewqKreinXiPrimeCharacter_eq_one_of_reflectionPair_kreinCompletions
        i j w rho p hwi (hcompletion rho)
          (hcompletion (xiZeroLineConjEquiv rho))
  apply Subtype.ext
  rw [xiZeroLineConjEquiv_apply]
  apply Complex.ext
  · simp
    linarith
  · simp

/-- Off the critical line, no fixed nondegenerate diagonal metric can complete both members of the
reflection orbit, even with indefinite signs and arbitrary auxiliary entries. -/
theorem not_reflectionPair_ewqSourceIndependentDiagonalKreinCompletions_of_re_ne_half
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) (w : ι → ℝ) (rho : XiDivisorSupport) (p : Nat.Primes)
    (hwi : w i ≠ 0) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    ¬(EWQSourceIndependentDiagonalKreinCompletionAt i j w rho p ∧
      EWQSourceIndependentDiagonalKreinCompletionAt
        i j w (xiZeroLineConjEquiv rho) p) := by
  rintro ⟨hrho, hreflect⟩
  apply hoff
  apply (norm_deltaS_eq_one_iff p.2.two_le (rho : ℂ)).1
  change ‖ewqKreinXiPrimeCharacter rho p‖ = 1
  exact
    norm_ewqKreinXiPrimeCharacter_eq_one_of_reflectionPair_kreinCompletions
      i j w rho p hwi hrho hreflect

end

end RHTower
