import GaloisForLFunctions.RHTower.EulerPositiveFisherHilbertLift

/-!
# Direct full-Euler four-unit Fisher law

The normalized positive Euler state on `ℓ²(ℕ+)` is not merely analogous to
the squarefree-times-square source: under the unique factorization
`n = m² d`, its Gibbs probability is exactly the independent product of the
squarefree and square-residual probabilities.  Consequently its actual
centered Fisher tangent has the same critical four-unit energy as the affine
source.

Everything here is unconditional and source-side.
-/

open Complex Filter Set
open scoped BigOperators Topology

noncomputable section
namespace RHTower

/-- Exact factorization of the full Euler partition function into its
squarefree and square-residual partition functions. -/
theorem eulerPositiveTotal_eq_squarefree_mul_residual
    {sigma : ℝ} (hsigma : 1 < sigma) :
    eulerPositiveTotal sigma =
      squarefreeMobiusTotal sigma * eulerSquareResidualTotal sigma := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul,
    ofReal_eulerPositiveTotal_eq_riemannZeta hsigma,
    ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma,
    ofReal_eulerSquareResidualTotal_eq_riemannZeta hsigma]
  have htwo :
      (((2 * sigma : ℝ) : ℂ)) = 2 * (sigma : ℂ) := by
    norm_cast
  rw [htwo]
  have hz2 : riemannZeta (2 * (sigma : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      norm_num
      linarith)
  exact (div_mul_cancel₀ _ hz2).symm

/-- Exact factorization of one positive Euler Gibbs mass under
`n = m² d`. -/
theorem eulerPositiveMass_eq_squarefree_mul_residual
    (sigma : ℝ) (n : ℕ+) :
    eulerPositiveMass sigma n =
      squarefreeMobiusMass sigma
          ((dyadicSquarefreeSquareEquiv n).1.1 : ℕ) *
        eulerSquareResidualMass sigma
          ((dyadicSquarefreeSquareEquiv n).2 : ℕ) := by
  let d : ℕ := (dyadicSquarefreeSquareEquiv n).1.1
  let m : ℕ := (dyadicSquarefreeSquareEquiv n).2
  have hd : Squarefree d := (dyadicSquarefreeSquareEquiv n).1.2
  have hm0 : m ≠ 0 := (dyadicSquarefreeSquareEquiv n).2.property.ne'
  have hdm : m ^ 2 * d = (n : ℕ) :=
    dyadicSquarefreeSquareEquiv_mul n
  have hcast : ((m : ℝ) ^ 2 * (d : ℝ)) = ((n : ℕ) : ℝ) := by
    exact_mod_cast hdm
  rw [eulerPositiveMass, squarefreeMobiusMass, if_pos hd,
    eulerSquareResidualMass, if_neg hm0]
  change ((n : ℕ) : ℝ) ^ (-sigma) =
    (d : ℝ) ^ (-sigma) * (m : ℝ) ^ (-2 * sigma)
  rw [← hcast]
  rw [Real.mul_rpow (sq_nonneg (m : ℝ)) (Nat.cast_nonneg d)]
  rw [show -2 * sigma = 2 * (-sigma) by ring,
    Real.rpow_mul (Nat.cast_nonneg m) 2 (-sigma)]
  have hm :
      (m : ℝ) ^ (2 : ℝ) = (m : ℝ) ^ (2 : ℕ) :=
    Real.rpow_natCast _ _
  rw [hm]
  exact mul_comm _ _

/-- The normalized full Euler Gibbs law becomes the independent product law
under the global squarefree-times-square carrier. -/
theorem eulerPositiveProbability_eq_squarefree_mul_residual
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ+) :
    eulerPositiveProbability sigma n =
      squarefreeMobiusProbability sigma
          ((dyadicSquarefreeSquareEquiv n).1.1 : ℕ) *
        eulerSquareResidualProbability sigma
          ((dyadicSquarefreeSquareEquiv n).2 : ℕ) := by
  rw [eulerPositiveProbability,
    squarefreeMobiusProbability, eulerSquareResidualProbability,
    eulerPositiveMass_eq_squarefree_mul_residual,
    eulerPositiveTotal_eq_squarefree_mul_residual hsigma]
  field_simp [(squarefreeMobiusTotal_pos hsigma).ne',
    (eulerSquareResidualTotal_pos hsigma).ne']

/-- The nested positive-squarefree carrier is equivalent to the ordinary
subtype of squarefree natural numbers; squarefreeness itself excludes zero. -/
noncomputable def squarefreePNatEquivNatSquarefree :
    SquarefreePNat ≃ {n : ℕ // Squarefree n} where
  toFun d := ⟨d.1, d.2⟩
  invFun d :=
    ⟨⟨d.1, Nat.pos_of_ne_zero (fun hzero => by
        exact not_squarefree_zero (hzero ▸ d.2))⟩, d.2⟩
  left_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv d := by
    apply Subtype.ext
    rfl

/-- Restricting a squarefree Gibbs moment to the positive-squarefree carrier
does not change its value. -/
theorem tsum_squarefreePNat_probability_log_pow
    (k : ℕ) (sigma : ℝ) :
    (∑' d : SquarefreePNat,
        squarefreeMobiusProbability sigma (d.1 : ℕ) *
          Real.log (d.1 : ℕ) ^ k) =
      squarefreeMobiusLogMoment k sigma := by
  calc
    _ = ∑' d : {n : ℕ // Squarefree n},
        squarefreeMobiusProbability sigma d.1 *
          Real.log d.1 ^ k := by
      simpa [squarefreePNatEquivNatSquarefree] using
        (squarefreePNatEquivNatSquarefree.tsum_eq
        (fun d : {n : ℕ // Squarefree n} =>
          squarefreeMobiusProbability sigma d.1 *
            Real.log d.1 ^ k))
    _ = ∑' n : ℕ, {n : ℕ | Squarefree n}.indicator
        (fun n =>
          squarefreeMobiusProbability sigma n *
            Real.log n ^ k) n := by
      simpa only using
        (tsum_subtype {n : ℕ | Squarefree n}
          (fun n : ℕ =>
            squarefreeMobiusProbability sigma n *
              Real.log n ^ k))
    _ = squarefreeMobiusLogMoment k sigma := by
      unfold squarefreeMobiusLogMoment
      apply tsum_congr
      intro n
      by_cases hn : Squarefree n
      · rw [Set.indicator_of_mem hn]
      · rw [Set.indicator_of_notMem hn]
        simp [squarefreeMobiusProbability, squarefreeMobiusMass, hn]

/-- Restricting a residual square Gibbs moment to positive integers does not
change it, because its zero-coordinate mass is exactly zero. -/
theorem tsum_pnat_eulerSquareResidualProbability_log_pow
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' m : ℕ+,
        eulerSquareResidualProbability sigma (m : ℕ) *
          Real.log (m : ℕ) ^ k) =
      eulerSquareResidualLogMoment k sigma := by
  have hshift :=
    (summable_eulerSquareResidualLogMoment k hsigma)
      |>.sum_add_tsum_nat_add 1
  unfold eulerSquareResidualLogMoment
  calc
    (∑' m : ℕ+,
        eulerSquareResidualProbability sigma (m : ℕ) *
          Real.log (m : ℕ) ^ k) =
      ∑' n : ℕ,
        eulerSquareResidualProbability sigma (n + 1) *
          Real.log (n + 1) ^ k := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (tsum_pnat_eq_tsum_succ
            (f := fun n : ℕ =>
              eulerSquareResidualProbability sigma n *
                Real.log n ^ k))
    _ = ∑' n : ℕ,
        eulerSquareResidualProbability sigma n *
          Real.log n ^ k := by
      simpa [eulerSquareResidualProbability,
        eulerSquareResidualMass, Nat.cast_add, Nat.cast_one] using hshift

/-- Direct full-Euler moments reindex exactly to the independent affine
squarefree--square law. -/
theorem eulerPositiveLogMoment_eq_dyadicAffine
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    eulerPositiveLogMoment k sigma =
      ∑' q : SquarefreePNat × ℕ+,
        (squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
          eulerSquareResidualProbability sigma (q.2 : ℕ)) *
          (Real.log (q.1.1 : ℕ) +
            2 * Real.log (q.2 : ℕ)) ^ k := by
  unfold eulerPositiveLogMoment
  rw [← dyadicSquarefreeSquareEquiv.symm.tsum_eq]
  apply tsum_congr
  intro q
  rw [eulerPositiveProbability_eq_squarefree_mul_residual hsigma]
  have hlog :=
    dyadicSquarefreeSquareEquiv_log
      (dyadicSquarefreeSquareEquiv.symm q)
  simp only [Equiv.apply_symm_apply] at hlog
  rw [hlog]
  simp only [Equiv.apply_symm_apply]

private theorem summable_squarefreePNat_probability_log_pow
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun d : SquarefreePNat =>
      squarefreeMobiusProbability sigma (d.1 : ℕ) *
        Real.log (d.1 : ℕ) ^ k) := by
  have hsub :=
    (summable_squarefreeMobiusLogMoment k hsigma)
      |>.subtype (fun n : ℕ => Squarefree n)
  have htransport :=
    (squarefreePNatEquivNatSquarefree.summable_iff
      (f := fun d : {n : ℕ // Squarefree n} =>
        squarefreeMobiusProbability sigma d.1 *
          Real.log d.1 ^ k)).mpr hsub
  simpa [squarefreePNatEquivNatSquarefree,
    Function.comp_def] using htransport

private theorem summable_pnat_eulerSquareResidualProbability_log_pow
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun m : ℕ+ =>
      eulerSquareResidualProbability sigma (m : ℕ) *
        Real.log (m : ℕ) ^ k) := by
  simpa only [Function.comp_apply] using
    (summable_eulerSquareResidualLogMoment k hsigma)
      |>.subtype (fun n : ℕ => 0 < n)

private theorem squarefreePNat_probability_log_pow_nonneg
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma)
    (d : SquarefreePNat) :
    0 ≤ squarefreeMobiusProbability sigma (d.1 : ℕ) *
      Real.log (d.1 : ℕ) ^ k :=
  mul_nonneg
    (squarefreeMobiusProbability_nonneg hsigma _)
    (pow_nonneg (Real.log_natCast_nonneg _) _)

private theorem pnat_eulerSquareResidualProbability_log_pow_nonneg
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) (m : ℕ+) :
    0 ≤ eulerSquareResidualProbability sigma (m : ℕ) *
      Real.log (m : ℕ) ^ k :=
  mul_nonneg
    (eulerSquareResidualProbability_nonneg hsigma _)
    (pow_nonneg (Real.log_natCast_nonneg _) _)

theorem squarefreeMobiusLogMoment_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    squarefreeMobiusLogMoment 0 sigma = 1 := by
  unfold squarefreeMobiusLogMoment
  simpa using tsum_squarefreeMobiusProbability hsigma

theorem eulerSquareResidualLogMoment_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    eulerSquareResidualLogMoment 0 sigma = 1 := by
  unfold eulerSquareResidualLogMoment
  simpa using tsum_eulerSquareResidualProbability hsigma

end RHTower
