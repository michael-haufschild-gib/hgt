import GaloisForLFunctions.RHTower.PrimeDyadicWeyl
import GaloisForLFunctions.RHTower.PrimeQuadraticGelfondSchneiderPhase

/-!
# Algebraic small-translation prime--Weyl determinant obstruction

The moving-fiber prime--Weyl parallelogram does not have trivial holonomy in general.  Triviality
is unnecessary.  Translate by the arbitrarily small rational-imaginary step `I / q`.  On a
rank-`d` moving fiber the exact Weyl multiplier has determinant

`p ^ (-(d / q) * I)`.

For `q ≠ 0` this principal power is transcendental whenever `d ≠ 0`, by Gelfond--Schneider.
Therefore even a nonflat moving determinant line cannot have this holonomy and simultaneously
descend algebraically.  Algebraicity, rather than flatness, is the sharp positive successor to the
old parallelogram no-go.

This file proves the exact global multiplier, its arbitrary smallness, the transcendence collision,
and the conditional RH endpoint.  It does not construct the source-defined moving Xi cluster or
its algebraic determinant-line descent.
-/

namespace RHTower

noncomputable section

/-- Rational-imaginary translation step.  Increasing `q` makes the step arbitrarily small. -/
def primeAlgebraicClockStep (q : ℕ) : ℂ :=
  ((1 : ℂ) / (q : ℂ)) * Complex.I

/-- Rank-`d` determinant phase of the prime--Weyl multiplier at step `I / q`. -/
def primeAlgebraicWeylDeterminantPhase (p : Nat.Primes) (d q : ℕ) : ℂ :=
  (p : ℂ) ^ (-((d : ℂ) / (q : ℂ)) * Complex.I)

private theorem isAlgebraic_natComplex (n : ℕ) : IsAlgebraic ℚ (n : ℂ) := by
  have h : IsAlgebraic ℚ (algebraMap ℚ ℂ (n : ℚ)) :=
    (isIntegral_algebraMap : IsIntegral ℚ (algebraMap ℚ ℂ (n : ℚ))).isAlgebraic
  simpa using h

/-- The norm of the rational-imaginary clock step is exactly `1/q`. -/
theorem norm_primeAlgebraicClockStep (q : ℕ) :
    ‖primeAlgebraicClockStep q‖ = 1 / (q : ℝ) := by
  simp [primeAlgebraicClockStep]

/-- Rational-imaginary clock steps fit inside every positive isolating radius. -/
theorem exists_primeAlgebraicClockStep_norm_lt {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ q : ℕ, 0 < q ∧ ‖primeAlgebraicClockStep q‖ < epsilon := by
  obtain ⟨q, hq⟩ := exists_nat_gt (1 / epsilon)
  have hqrealpos : 0 < (q : ℝ) := (one_div_pos.mpr hepsilon).trans hq
  have hqpos : 0 < q := by exact_mod_cast hqrealpos
  refine ⟨q, hqpos, ?_⟩
  rw [norm_primeAlgebraicClockStep]
  exact (one_div_lt hqrealpos hepsilon).2 hq

/-- The generic prime translation law at the rational-imaginary step. -/
theorem primeAlgebraicTranslationWeylRelation
    (p : Nat.Primes) (q : ℕ) (s : ℂ) (f : ℂ → ℂ) :
    spectralTranslate (primeAlgebraicClockStep q) (primeEulerExpMultiply p f) s =
      Complex.exp (-((Real.log p : ℝ) : ℂ) * primeAlgebraicClockStep q) *
        primeEulerExpMultiply p
          (spectralTranslate (primeAlgebraicClockStep q) f) s := by
  exact spectralTranslate_primeEulerExpMultiply p (primeAlgebraicClockStep q) s f

/-- The `d`-th power of the scalar Weyl multiplier is exactly the principal rank-`d`
Gelfond--Schneider phase. -/
theorem primeAlgebraicWeylMultiplier_pow_eq_phase
    (p : Nat.Primes) (d q : ℕ) :
    Complex.exp
        (-((Real.log p : ℝ) : ℂ) * primeAlgebraicClockStep q) ^ d =
      primeAlgebraicWeylDeterminantPhase p d q := by
  rw [← Complex.exp_nat_mul]
  rw [primeAlgebraicWeylDeterminantPhase,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast p.2.ne_zero)]
  rw [← Complex.natCast_log]
  unfold primeAlgebraicClockStep
  congr 1
  field_simp

/-- **Positive parallelogram obstruction.**  Every positive-rank determinant phase at a nonzero
rational-imaginary step is transcendental. -/
theorem primeAlgebraicWeylDeterminantPhase_transcendental
    (p : Nat.Primes) {d q : ℕ} (hd : d ≠ 0) (hq : q ≠ 0) :
    Transcendental ℚ (primeAlgebraicWeylDeterminantPhase p d q) := by
  unfold primeAlgebraicWeylDeterminantPhase
  apply GaloisForLFunctions.RHTower.GelfondSchneiderProof.Setup.transcendental_cpow_of_isAlgebraic_of_irrational
      (p : ℂ) (-((d : ℂ) / (q : ℂ)) * Complex.I)
  · exact isAlgebraic_natComplex p
  · exact (((isAlgebraic_natComplex d).mul
      (isAlgebraic_natComplex q).inv).neg).mul
        GaloisForLFunctions.RHTower.isAlgebraic_I
  · constructor
    · exact_mod_cast p.2.ne_zero
    · exact_mod_cast p.2.ne_one
  · intro i j hij
    have him := congrArg Complex.im hij
    simp [div_eq_mul_inv] at him
    rcases him with hd0 | hq0
    · exact hd hd0
    · exact hq hq0

/-- At every nonzero rational-imaginary step, algebraic determinant descent is possible exactly in
rank zero. -/
theorem primeAlgebraicWeylDeterminantPhase_isAlgebraic_iff
    (p : Nat.Primes) (d : ℕ) {q : ℕ} (hq : q ≠ 0) :
    IsAlgebraic ℚ (primeAlgebraicWeylDeterminantPhase p d q) ↔ d = 0 := by
  constructor
  · intro halgebraic
    by_contra hd
    exact primeAlgebraicWeylDeterminantPhase_transcendental p hd hq halgebraic
  · rintro rfl
    simpa [primeAlgebraicWeylDeterminantPhase] using isAlgebraic_natComplex 1

/-- Minimal interface for a source construction whose moving-fiber determinant holonomy is
algebraic and equals the exact rank-`d` prime--Weyl phase. -/
structure AlgebraicPrimeWeylDeterminantDescent
    (p : Nat.Primes) (d q : ℕ) where
  holonomy : ℂ
  holonomy_isAlgebraic : IsAlgebraic ℚ holonomy
  holonomy_eq_phase : holonomy = primeAlgebraicWeylDeterminantPhase p d q

/-- A source algebraic determinant descent at nonzero step exists exactly in rank zero. -/
theorem algebraicPrimeWeylDeterminantDescent_iff
    (p : Nat.Primes) (d : ℕ) {q : ℕ} (hq : q ≠ 0) :
    Nonempty (AlgebraicPrimeWeylDeterminantDescent p d q) ↔ d = 0 := by
  constructor
  · rintro ⟨h⟩
    apply (primeAlgebraicWeylDeterminantPhase_isAlgebraic_iff p d hq).mp
    rw [← h.holonomy_eq_phase]
    exact h.holonomy_isAlgebraic
  · rintro rfl
    refine ⟨⟨1, by simpa using isAlgebraic_natComplex 1, ?_⟩⟩
    simp [primeAlgebraicWeylDeterminantPhase]

/-- Algebraic moving-fiber determinant descent attached to the local Xi multiplicity. -/
abbrev XiAlgebraicPrimeWeylDeterminantDescent
    (p : Nat.Primes) (q : ℕ) (rho : ℂ) :=
  AlgebraicPrimeWeylDeterminantDescent p (analyticOrderAt xi rho).toNat q

/-- **Moving-fiber algebraic-parallelogram criterion for RH.**  A source theorem producing one
nonzero-step algebraic prime--Weyl determinant descent at every hypothetical right-half zero would
prove RH.  Conversely RH makes this consumer condition vacuous. -/
theorem riemannHypothesis_iff_xiAlgebraicPrimeWeylDeterminantDescents
    (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) :
    RiemannHypothesis ↔
      ∀ rho ∈ rightHalf, xi rho = 0 →
        Nonempty (XiAlgebraicPrimeWeylDeterminantDescent p q rho) := by
  constructor
  · intro hRH rho hrho hzero
    exact (rh_iff_xi_ne_zero_right.mp hRH rho hrho hzero).elim
  · intro hdescent
    apply rh_iff_xi_ne_zero_right.mpr
    intro rho hrho hzero
    have horder :=
      (algebraicPrimeWeylDeterminantDescent_iff
        p (analyticOrderAt xi rho).toNat hq).mp
          (hdescent rho hrho hzero)
    exact (xi_order_toNat_ne_zero hzero horder).elim

end

end RHTower
