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

/-- First logarithmic moment of the direct positive-integer Euler law is
exactly the sum of the independent squarefree and doubled-square moments. -/
theorem eulerPositiveLogMoment_one_eq_affine
    {sigma : ℝ} (hsigma : 1 < sigma) :
    eulerPositiveLogMoment 1 sigma =
      squarefreeMobiusLogMoment 1 sigma +
        2 * eulerSquareResidualLogMoment 1 sigma := by
  rw [eulerPositiveLogMoment_eq_dyadicAffine 1 hsigma]
  simp only [pow_one]
  have ha0 :=
    summable_squarefreePNat_probability_log_pow 0 hsigma
  have ha1 :=
    summable_squarefreePNat_probability_log_pow 1 hsigma
  have hb0 :=
    summable_pnat_eulerSquareResidualProbability_log_pow 0 hsigma
  have hb1 :=
    summable_pnat_eulerSquareResidualProbability_log_pow 1 hsigma
  have h10 : Summable (fun q : SquarefreePNat × ℕ+ =>
      (squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
        Real.log (q.1.1 : ℕ)) *
      (eulerSquareResidualProbability sigma (q.2 : ℕ))) :=
    by
      simpa only [pow_one, pow_zero, mul_one] using
        ha1.mul_of_nonneg hb0
          (fun d => by
            simpa only [pow_one] using
              squarefreePNat_probability_log_pow_nonneg 1 hsigma d)
          (fun m => by
            simpa only [pow_zero, mul_one] using
              pnat_eulerSquareResidualProbability_log_pow_nonneg 0 hsigma m)
  have h01 : Summable (fun q : SquarefreePNat × ℕ+ =>
      squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
      (eulerSquareResidualProbability sigma (q.2 : ℕ) *
        Real.log (q.2 : ℕ))) :=
    by
      simpa only [pow_one, pow_zero, mul_one] using
        ha0.mul_of_nonneg hb1
          (fun d => by
            simpa only [pow_zero, mul_one] using
              squarefreePNat_probability_log_pow_nonneg 0 hsigma d)
          (fun m => by
            simpa only [pow_one] using
              pnat_eulerSquareResidualProbability_log_pow_nonneg 1 hsigma m)
  have h10raw : Summable (fun q : SquarefreePNat × ℕ+ =>
      (squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
        Real.log (q.1.1 : ℕ) ^ 1) *
      (eulerSquareResidualProbability sigma (q.2 : ℕ) *
        Real.log (q.2 : ℕ) ^ 0)) := by
    simpa only [pow_one, pow_zero, mul_one] using h10
  have h01raw : Summable (fun q : SquarefreePNat × ℕ+ =>
      (squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
        Real.log (q.1.1 : ℕ) ^ 0) *
      (eulerSquareResidualProbability sigma (q.2 : ℕ) *
        Real.log (q.2 : ℕ) ^ 1)) := by
    simpa only [pow_one, pow_zero, mul_one] using h01
  have hsum10 :
      (∑' d : SquarefreePNat,
          squarefreeMobiusProbability sigma (d.1 : ℕ) *
            Real.log (d.1 : ℕ)) *
        (∑' m : ℕ+,
          eulerSquareResidualProbability sigma (m : ℕ)) =
      ∑' q : SquarefreePNat × ℕ+,
        (squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
          Real.log (q.1.1 : ℕ)) *
            eulerSquareResidualProbability sigma (q.2 : ℕ) := by
    simpa only [pow_one, pow_zero, mul_one] using
      ha1.tsum_mul_tsum hb0 h10raw
  have hsum01 :
      (∑' d : SquarefreePNat,
          squarefreeMobiusProbability sigma (d.1 : ℕ)) *
        (∑' m : ℕ+,
          eulerSquareResidualProbability sigma (m : ℕ) *
            Real.log (m : ℕ)) =
      ∑' q : SquarefreePNat × ℕ+,
        squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
          (eulerSquareResidualProbability sigma (q.2 : ℕ) *
            Real.log (q.2 : ℕ)) := by
    simpa only [pow_one, pow_zero, mul_one] using
      ha0.tsum_mul_tsum hb1 h01raw
  rw [show (fun q : SquarefreePNat × ℕ+ =>
      (squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
        eulerSquareResidualProbability sigma (q.2 : ℕ)) *
      (Real.log (q.1.1 : ℕ) + 2 * Real.log (q.2 : ℕ))) =
    fun q =>
      (squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
        Real.log (q.1.1 : ℕ)) *
          eulerSquareResidualProbability sigma (q.2 : ℕ) +
      2 * (squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
        (eulerSquareResidualProbability sigma (q.2 : ℕ) *
          Real.log (q.2 : ℕ))) by
    funext q
    ring]
  rw [Summable.tsum_add h10 (h01.mul_left 2)]
  rw [tsum_mul_left]
  rw [← hsum10, ← hsum01]
  have hA0 :
      (∑' d : SquarefreePNat,
        squarefreeMobiusProbability sigma (d.1 : ℕ)) =
        squarefreeMobiusLogMoment 0 sigma := by
    simpa only [pow_zero, mul_one] using
      tsum_squarefreePNat_probability_log_pow 0 sigma
  have hA1 :
      (∑' d : SquarefreePNat,
        squarefreeMobiusProbability sigma (d.1 : ℕ) *
          Real.log (d.1 : ℕ)) =
        squarefreeMobiusLogMoment 1 sigma := by
    simpa only [pow_one] using
      tsum_squarefreePNat_probability_log_pow 1 sigma
  have hB0 :
      (∑' m : ℕ+,
        eulerSquareResidualProbability sigma (m : ℕ)) =
        eulerSquareResidualLogMoment 0 sigma := by
    simpa only [pow_zero, mul_one] using
      tsum_pnat_eulerSquareResidualProbability_log_pow 0 hsigma
  have hB1 :
      (∑' m : ℕ+,
        eulerSquareResidualProbability sigma (m : ℕ) *
          Real.log (m : ℕ)) =
        eulerSquareResidualLogMoment 1 sigma := by
    simpa only [pow_one] using
      tsum_pnat_eulerSquareResidualProbability_log_pow 1 hsigma
  rw [hA0, hA1, hB0, hB1,
    squarefreeMobiusLogMoment_zero hsigma,
    eulerSquareResidualLogMoment_zero hsigma]
  ring

private theorem summable_dyadic_probability_log_pow_product
    (j k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun q : SquarefreePNat × ℕ+ =>
      (squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
        Real.log (q.1.1 : ℕ) ^ j) *
      (eulerSquareResidualProbability sigma (q.2 : ℕ) *
        Real.log (q.2 : ℕ) ^ k)) := by
  exact
    (summable_squarefreePNat_probability_log_pow j hsigma).mul_of_nonneg
      (summable_pnat_eulerSquareResidualProbability_log_pow k hsigma)
      (squarefreePNat_probability_log_pow_nonneg j hsigma)
      (pnat_eulerSquareResidualProbability_log_pow_nonneg k hsigma)

/-- Every mixed logarithmic moment of the reindexed Euler law factors
exactly. -/
theorem tsum_dyadic_probability_log_pow_product
    (j k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' q : SquarefreePNat × ℕ+,
      (squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
        Real.log (q.1.1 : ℕ) ^ j) *
      (eulerSquareResidualProbability sigma (q.2 : ℕ) *
        Real.log (q.2 : ℕ) ^ k)) =
      squarefreeMobiusLogMoment j sigma *
        eulerSquareResidualLogMoment k sigma := by
  have ha :=
    summable_squarefreePNat_probability_log_pow j hsigma
  have hb :=
    summable_pnat_eulerSquareResidualProbability_log_pow k hsigma
  have hab :=
    summable_dyadic_probability_log_pow_product j k hsigma
  calc
    _ = (∑' d : SquarefreePNat,
          squarefreeMobiusProbability sigma (d.1 : ℕ) *
            Real.log (d.1 : ℕ) ^ j) *
        (∑' m : ℕ+,
          eulerSquareResidualProbability sigma (m : ℕ) *
            Real.log (m : ℕ) ^ k) :=
      (ha.tsum_mul_tsum hb hab).symm
    _ = _ := by
      rw [tsum_squarefreePNat_probability_log_pow,
        tsum_pnat_eulerSquareResidualProbability_log_pow k hsigma]

/-- Second logarithmic moment of the direct Euler law has the exact affine
independent-sum formula. -/
theorem eulerPositiveLogMoment_two_eq_affine
    {sigma : ℝ} (hsigma : 1 < sigma) :
    eulerPositiveLogMoment 2 sigma =
      squarefreeMobiusLogMoment 2 sigma +
        4 * squarefreeMobiusLogMoment 1 sigma *
          eulerSquareResidualLogMoment 1 sigma +
        4 * eulerSquareResidualLogMoment 2 sigma := by
  rw [eulerPositiveLogMoment_eq_dyadicAffine 2 hsigma]
  have h20 :=
    summable_dyadic_probability_log_pow_product 2 0 hsigma
  have h11 :=
    summable_dyadic_probability_log_pow_product 1 1 hsigma
  have h02 :=
    summable_dyadic_probability_log_pow_product 0 2 hsigma
  rw [show (fun q : SquarefreePNat × ℕ+ =>
      (squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
        eulerSquareResidualProbability sigma (q.2 : ℕ)) *
      (Real.log (q.1.1 : ℕ) + 2 * Real.log (q.2 : ℕ)) ^ 2) =
    fun q =>
      ((squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
          Real.log (q.1.1 : ℕ) ^ 2) *
        (eulerSquareResidualProbability sigma (q.2 : ℕ) *
          Real.log (q.2 : ℕ) ^ 0) +
      4 * ((squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
          Real.log (q.1.1 : ℕ) ^ 1) *
        (eulerSquareResidualProbability sigma (q.2 : ℕ) *
          Real.log (q.2 : ℕ) ^ 1))) +
      4 * ((squarefreeMobiusProbability sigma (q.1.1 : ℕ) *
          Real.log (q.1.1 : ℕ) ^ 0) *
        (eulerSquareResidualProbability sigma (q.2 : ℕ) *
          Real.log (q.2 : ℕ) ^ 2)) by
    funext q
    ring]
  rw [Summable.tsum_add (h20.add (h11.mul_left 4))
    (h02.mul_left 4)]
  rw [Summable.tsum_add h20 (h11.mul_left 4)]
  rw [tsum_mul_left, tsum_mul_left]
  rw [tsum_dyadic_probability_log_pow_product 2 0 hsigma,
    tsum_dyadic_probability_log_pow_product 1 1 hsigma,
    tsum_dyadic_probability_log_pow_product 0 2 hsigma,
    squarefreeMobiusLogMoment_zero hsigma,
    eulerSquareResidualLogMoment_zero hsigma]
  ring

end RHTower
