import GaloisForLFunctions.RHTower.GaussHodgeWeilGNSSocket

/-!
# The construction attempt, executed: the Krein signature decomposition of the Weil form

Attempting to build the square realization directly produces, unconditionally, exactly one
obstruction — and this module formalizes the attempt and the obstruction.

Split every divisor evaluation into its reflection pair sum and pair difference,
`F(α_q) ± F(ᾱ_q)`.  The natural candidate realization uses the pair sums; what it actually
realizes is the **Krein signature decomposition**: for every square-summable test,

`4·Re(xiWeilPolarization F F) = Σ‖pair sum‖² − Σ‖pair difference‖²` —

a difference of two convergent sums of squares, with no hypothesis.  The Weil form is a
Pontryagin-space form; its positive sector is the reflection-coherent part of the evaluation
map and its negative sector is the reflection-difference part.  At the prime exponential test
the difference-sector energy density is exactly the centered cosh defect — the Hodge mass
density — so the negative Krein sector *is* the loop's mass sector.  Finally, the square
realization exists exactly when the difference sector is annihilated on every square-summable
test (with an elementary indicator witness for the converse), which is RH.  This closes the
Krein alternative of the card's attempt 2 into theorems: definitizability of the Weil form,
annihilation of its negative sector, vanishing of the Hodge mass, the square realization, and
RH are one statement.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The reflection pair split of the evaluation map -/

/-- The reflection pair sum of a test's divisor evaluations. -/
def xiWeilPairSum (F : ℂ → ℂ) (q : XiZeroCopy) : ℂ :=
  F (xiSpectralPoint q) + F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))

/-- The reflection pair difference of a test's divisor evaluations. -/
def xiWeilPairDif (F : ℂ → ℂ) (q : XiZeroCopy) : ℂ :=
  F (xiSpectralPoint q) - F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))

/-- **Pointwise signature law.**  Each Weil pair summand splits into a positive and a negative
square: four times its real part is the pair-sum square minus the pair-difference square. -/
theorem xiWeilPairTerm_re (F : ℂ → ℂ) (q : XiZeroCopy) :
    (xiWeilPairTerm F q).re =
      (‖xiWeilPairSum F q‖ ^ (2 : ℕ) - ‖xiWeilPairDif F q‖ ^ (2 : ℕ)) / 4 := by
  have hpt : xiSpectralPoint (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiSpectralPoint q) := xiSpectralPoint_lineConj q
  rw [xiWeilPairTerm, xiWeilSharp, xiWeilPairSum, xiWeilPairDif, hpt]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_add, Complex.normSq_sub]
  ring

/-! ## Summability of the two sectors -/

/-- Square-summability transports across the reflection pairing. -/
theorem xiWeil_squareSummable_lineConj {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    Summable (fun q : XiZeroCopy =>
      ‖F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖ ^ (2 : ℕ)) :=
  (xiZeroCopyLineConjEquiv.summable_iff
    (f := fun q : XiZeroCopy => ‖F (xiSpectralPoint q)‖ ^ (2 : ℕ))).mpr hF

/-- The pair-sum sector of a square-summable test has convergent energy. -/
theorem xiWeilPairSum_squareSummable {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    Summable (fun q : XiZeroCopy => ‖xiWeilPairSum F q‖ ^ (2 : ℕ)) := by
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_)
    ((hF.add (xiWeil_squareSummable_lineConj hF)).mul_left 2)
  rw [xiWeilPairSum]
  have htri := norm_add_le (F (xiSpectralPoint q))
    (F (xiSpectralPoint (xiZeroCopyLineConjEquiv q)))
  have hsq1 := pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith [hsq1, sq_nonneg (‖F (xiSpectralPoint q)‖ -
    ‖F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖)]

/-- The pair-difference sector of a square-summable test has convergent energy. -/
theorem xiWeilPairDif_squareSummable {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    Summable (fun q : XiZeroCopy => ‖xiWeilPairDif F q‖ ^ (2 : ℕ)) := by
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_)
    ((hF.add (xiWeil_squareSummable_lineConj hF)).mul_left 2)
  rw [xiWeilPairDif]
  have htri := norm_sub_le (F (xiSpectralPoint q))
    (F (xiSpectralPoint (xiZeroCopyLineConjEquiv q)))
  have hsq1 := pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith [hsq1, sq_nonneg (‖F (xiSpectralPoint q)‖ -
    ‖F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖)]

/-- The Weil pair summands of a square-summable test are absolutely summable. -/
theorem xiWeilPairTerm_summable {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    Summable (fun q : XiZeroCopy => xiWeilPairTerm F q) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun q => norm_nonneg _)
    (fun q => ?_) ((hF.add (xiWeil_squareSummable_lineConj hF)).div_const 2))
  have hpt : xiSpectralPoint (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiSpectralPoint q) := xiSpectralPoint_lineConj q
  rw [xiWeilPairTerm, xiWeilSharp, norm_mul, RCLike.norm_conj]
  rw [← hpt]
  nlinarith [norm_nonneg (F (xiSpectralPoint q)),
    norm_nonneg (F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))),
    sq_nonneg (‖F (xiSpectralPoint q)‖ -
      ‖F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖)]

/-! ## The Krein signature decomposition -/

/-- **The Krein signature decomposition of the Weil form.**  For every square-summable test,
four times the diagonal Weil value is the pair-sum energy minus the pair-difference energy: a
difference of two convergent sums of squares, unconditionally.  This is what the direct
square-realization construction actually produces — the form is Pontryagin, and its negative
sector is the reflection-difference sector. -/
theorem xiWeilPolarization_re_eq_krein {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    (xiWeilPolarization F F).re =
      ((∑' q : XiZeroCopy, ‖xiWeilPairSum F q‖ ^ (2 : ℕ)) -
        (∑' q : XiZeroCopy, ‖xiWeilPairDif F q‖ ^ (2 : ℕ))) / 4 := by
  rw [xiWeilPolarization_eq_tsum_pairTerm, Complex.re_tsum (xiWeilPairTerm_summable hF)]
  calc (∑' q : XiZeroCopy, (xiWeilPairTerm F q).re) =
      ∑' q : XiZeroCopy,
        (‖xiWeilPairSum F q‖ ^ (2 : ℕ) - ‖xiWeilPairDif F q‖ ^ (2 : ℕ)) / 4 :=
        tsum_congr fun q => xiWeilPairTerm_re F q
    _ = (∑' q : XiZeroCopy, (‖xiWeilPairSum F q‖ ^ (2 : ℕ) - ‖xiWeilPairDif F q‖ ^ (2 : ℕ))) / 4 := by
        rw [tsum_div_const]
    _ = ((∑' q : XiZeroCopy, ‖xiWeilPairSum F q‖ ^ (2 : ℕ)) -
        (∑' q : XiZeroCopy, ‖xiWeilPairDif F q‖ ^ (2 : ℕ))) / 4 := by
        rw [(xiWeilPairSum_squareSummable hF).tsum_sub (xiWeilPairDif_squareSummable hF)]

/-- At the prime exponential test the negative-sector energy density is exactly the centered
cosh defect: the negative Krein sector of the Weil form is the Hodge mass sector. -/
theorem norm_sq_pairDif_primeTest {p : ℝ} (hp : 1 < p) (q : XiZeroCopy) :
    ‖xiWeilPairDif (xiWeilPrimeTest p) q‖ ^ (2 : ℕ) =
      (p : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) + (p : ℝ) ^ (1 - 2 * ((q.1 : ℂ)).re) - 2 :=
  norm_sq_primeTest_sub_lineConj hp q

/-! ## Annihilating the negative sector is the square realization, is RH -/

/-- **RH ⟺ the negative Krein sector is annihilated** on every square-summable test.  The
converse uses an elementary indicator witness at an off-line spectral point. -/
theorem riemannHypothesis_iff_forall_pairDifEnergy_eq_zero :
    RiemannHypothesis ↔
      ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
        (∑' q : XiZeroCopy, ‖xiWeilPairDif F q‖ ^ (2 : ℕ)) = 0 := by
  constructor
  · intro hRH F _
    have hzero : ∀ q : XiZeroCopy, xiWeilPairDif F q = 0 := by
      intro q
      obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
      rw [xiWeilPairDif, xiSpectralPoint_lineConj, ht,
        show (starRingEnd ℂ) ((t : ℝ) : ℂ) = ((t : ℝ) : ℂ) from Complex.conj_ofReal t,
        sub_self]
    calc (∑' q : XiZeroCopy, ‖xiWeilPairDif F q‖ ^ (2 : ℕ)) =
        ∑' _q : XiZeroCopy, (0 : ℝ) :=
          tsum_congr fun q => by rw [hzero q, norm_zero]; norm_num
      _ = 0 := tsum_zero
  · intro hodd
    by_contra hnRH
    rw [riemannHypothesis_iff_xi_zero_re_eq_half] at hnRH
    obtain ⟨rho, hrho⟩ := not_forall.mp hnRH
    obtain ⟨hzero, hre⟩ := Classical.not_imp.mp hrho
    have hXiC : XiC (((rho : ℂ) - 1 / 2) * (-Complex.I)) = 0 := by
      rw [XiC]
      have harg : 1 / 2 + ((rho : ℂ) - 1 / 2) * -Complex.I * Complex.I = rho := by
        have hI : (-Complex.I) * Complex.I = 1 := by
          rw [neg_mul, Complex.I_mul_I]
          ring
        linear_combination ((rho : ℂ) - 1 / 2) * hI
      rw [harg]
      exact hzero
    obtain ⟨q0, hq0⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hXiC
    set alpha : ℂ := ((rho : ℂ) - 1 / 2) * (-Complex.I) with halpha
    have himalpha : alpha.im ≠ 0 := by
      have him : alpha.im = -(rho.re - 1 / 2) := by
        rw [halpha]
        simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]
      rw [him]
      intro hcontra
      apply hre
      linarith [neg_eq_zero.mp hcontra]
    have hconjne : (starRingEnd ℂ) alpha ≠ alpha := by
      intro hcontra
      apply himalpha
      have := congrArg Complex.im hcontra
      simp only [Complex.conj_im] at this
      linarith
    set F : ℂ → ℂ := fun z => if z = alpha then 1 else 0 with hFdef
    have hFsupp : ∀ q : XiZeroCopy, F (xiSpectralPoint q) ≠ 0 →
        xiSpectralPoint q = alpha := by
      intro q hq
      by_contra hne
      apply hq
      rw [hFdef]
      simp [hne]
    have hFsq : XiWeilSquareSummable F := by
      unfold XiWeilSquareSummable
      apply summable_of_hasFiniteSupport
      apply (finite_xiSpectralPoint_fiber alpha).subset
      intro q hq
      simp only [Function.mem_support] at hq
      have : F (xiSpectralPoint q) ≠ 0 := by
        intro hzero'
        apply hq
        rw [hzero', norm_zero]
        norm_num
      exact hFsupp q this
    have hdif0 : xiWeilPairDif F q0 = 1 := by
      rw [xiWeilPairDif, xiSpectralPoint_lineConj, hq0]
      show (if alpha = alpha then (1 : ℂ) else 0) -
        (if (starRingEnd ℂ) alpha = alpha then (1 : ℂ) else 0) = 1
      rw [if_pos rfl, if_neg hconjne, sub_zero]
    have hdifsum : Summable (fun q : XiZeroCopy => ‖xiWeilPairDif F q‖ ^ (2 : ℕ)) :=
      xiWeilPairDif_squareSummable hFsq
    have hle : ‖xiWeilPairDif F q0‖ ^ (2 : ℕ) ≤
        ∑' q : XiZeroCopy, ‖xiWeilPairDif F q‖ ^ (2 : ℕ) :=
      hdifsum.le_tsum q0 fun q _ => sq_nonneg _
    rw [hdif0] at hle
    rw [hodd F hFsq] at hle
    norm_num at hle

/-- **The construction verdict.**  The square realization of the Weil form exists exactly when
its negative Krein sector is annihilated: building the realization *is* killing the
pair-difference sector, whose energy density at the prime test is the Hodge mass. -/
theorem xiWeilSquareRealization_iff_forall_pairDifEnergy_eq_zero :
    XiWeilSquareRealization ↔
      ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
        (∑' q : XiZeroCopy, ‖xiWeilPairDif F q‖ ^ (2 : ℕ)) = 0 :=
  riemannHypothesis_iff_xiWeilSquareRealization.symm.trans
    riemannHypothesis_iff_forall_pairDifEnergy_eq_zero

end

end RHTower
