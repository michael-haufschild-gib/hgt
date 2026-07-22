import GaloisForLFunctions.RHTower.XiReciprocalSquareFixedCauchySourceReconstruction

/-!
# A single reciprocal-Krylov Cauchy source generates the continued Xi source core

Fix one regular continued-Cauchy vector and iterate the compact reciprocal Xi operator. Complex
finite-shell separator polynomials recover every complete divisor-multiplicity fiber in norm.
Consequently the closed polynomial Krylov orbit of this one vector is exactly the full continued
Cauchy Hilbert source core, and contains every multiplicity-safe square-summable Xi Weil
evaluation.

Complex coefficients are essential: real separator polynomials force conjugate target values,
whereas fixed adjoint response at off-axis pole does not obey that constraint. Proof uses only
finite outer spectral shells plus dominated convergence; it assumes neither RH nor simplicity.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section


def xiReciprocalCauchyKrylovPolynomialVector (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  ∑ n ∈ p.support,
    p.coeff n • ((xiReciprocalOperator ^ n) (xiWeilContinuedCauchyLp z))

theorem xiReciprocalOperator_pow_apply
    (f : lp (fun _ : XiZeroCopy => ℂ) 2) (n : ℕ) (q : XiZeroCopy) :
    (xiReciprocalOperator ^ n) f q = (xiSpectralPoint q)⁻¹ ^ n * f q := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, ih,
        xiReciprocalOperator_apply]
      ring

theorem xiReciprocalCauchyKrylovPolynomialVector_apply
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) (q : XiZeroCopy) :
    xiReciprocalCauchyKrylovPolynomialVector z p q =
      p.eval (xiSpectralPoint q)⁻¹ * (xiWeilContinuedCauchyLp z) q := by
  rw [xiReciprocalCauchyKrylovPolynomialVector]
  simp only [lp.coeFn_sum, Finset.sum_apply]
  change (∑ n ∈ p.support,
    p.coeff n * ((xiReciprocalOperator ^ n)
      (xiWeilContinuedCauchyLp z)) q) = _
  simp_rw [xiReciprocalOperator_pow_apply]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  simp only [mul_assoc]

def xiReciprocalSpectralSupport (rho : XiDivisorSupport) : ℂ :=
  (xiSpectralPointSupport rho)⁻¹

theorem xiReciprocalSpectralSupport_ne_zero (rho : XiDivisorSupport) :
    xiReciprocalSpectralSupport rho ≠ 0 := by
  exact inv_ne_zero (by
    simpa only [xiSpectralPoint_eq_support] using
      xiSpectralPoint_ne_zero (xiFirstZeroCopy rho))

theorem xiReciprocalSpectralSupport_injective :
    Function.Injective xiReciprocalSpectralSupport := by
  intro rho tau h
  apply xiSpectralPointSupport_injective
  exact inv_injective h

theorem xiReciprocalSpectralSupport_sq (rho : XiDivisorSupport) :
    xiReciprocalSpectralSupport rho ^ 2 = xiCentralReciprocalSquare (rho : ℂ) := by
  have h := xiZeroCopyReciprocalSquare_eq (xiFirstZeroCopy rho)
  simpa only [xiZeroCopyReciprocalSquare, xiSpectralPoint_eq_support,
    xiFirstZeroCopy_fst, xiReciprocalSpectralSupport] using h

theorem xiReciprocalSpectralSupport_finite_norm_ge {r : ℝ} (hr : 0 < r) :
    {rho : XiDivisorSupport | r ≤ ‖xiReciprocalSpectralSupport rho‖}.Finite := by
  apply (xi_central_reciprocal_square_finite_norm_ge (sq_pos_of_pos hr)).subset
  intro rho hrho
  change r ≤ ‖xiReciprocalSpectralSupport rho‖ at hrho
  change r ^ 2 ≤ ‖xiCentralReciprocalSquare (rho : ℂ)‖
  rw [← xiReciprocalSpectralSupport_sq, norm_pow]
  nlinarith [norm_nonneg (xiReciprocalSpectralSupport rho)]

def xiComplexFiniteSpectralSeparator (F : Finset ℂ) (alpha : ℂ) : Polynomial ℂ :=
  ∏ beta ∈ F.erase alpha, (Polynomial.X - Polynomial.C beta)

theorem xi_eval_complexFiniteSpectralSeparator (F : Finset ℂ) (alpha z : ℂ) :
    (xiComplexFiniteSpectralSeparator F alpha).eval z =
      ∏ beta ∈ F.erase alpha, (z - beta) := by
  classical
  have hmap (S : Finset ℂ) :
      Polynomial.eval z
          (∏ beta ∈ S, (Polynomial.X - Polynomial.C beta)) =
        ∏ beta ∈ S, (z - beta) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert beta S hbeta ih => simp [hbeta, ih]
  exact hmap (F.erase alpha)

theorem xi_eval_complexFiniteSpectralSeparator_ne_zero
    {F : Finset ℂ} {alpha : ℂ} :
    (xiComplexFiniteSpectralSeparator F alpha).eval alpha ≠ 0 := by
  rw [xi_eval_complexFiniteSpectralSeparator]
  apply Finset.prod_ne_zero_iff.mpr
  intro beta hbeta
  exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hbeta).symm

def xiComplexRadialSeparatorPolynomial
    (F : Finset ℂ) (alpha c : ℂ) (n : ℕ) : Polynomial ℂ :=
  Polynomial.C (c / (xiComplexFiniteSpectralSeparator F alpha).eval alpha) *
    xiComplexFiniteSpectralSeparator F alpha *
    (Polynomial.C alpha⁻¹ * Polynomial.X) ^ n

theorem xi_eval_complexRadialSeparatorPolynomial_target
    (F : Finset ℂ) {alpha c : ℂ} (halpha : alpha ≠ 0) (n : ℕ) :
    (xiComplexRadialSeparatorPolynomial F alpha c n).eval alpha = c := by
  simp only [xiComplexRadialSeparatorPolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hsep := xi_eval_complexFiniteSpectralSeparator_ne_zero
    (F := F) (alpha := alpha)
  field_simp [hsep, halpha]
  simp

theorem xi_eval_complexRadialSeparatorPolynomial_outer_zero
    {F : Finset ℂ} {alpha beta c : ℂ}
    (hbeta : beta ∈ F) (hbetaAlpha : beta ≠ alpha) (n : ℕ) :
    (xiComplexRadialSeparatorPolynomial F alpha c n).eval beta = 0 := by
  simp only [xiComplexRadialSeparatorPolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hsep : (xiComplexFiniteSpectralSeparator F alpha).eval beta = 0 := by
    rw [xi_eval_complexFiniteSpectralSeparator]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hbetaAlpha, hbeta⟩)
    simp
  rw [hsep]
  ring

theorem xi_tendsto_eval_complexRadialSeparatorPolynomial_zero
    (F : Finset ℂ) {alpha beta c : ℂ} (halpha : alpha ≠ 0)
    (hinner : ‖beta‖ < ‖alpha‖) :
    Tendsto (fun n => (xiComplexRadialSeparatorPolynomial F alpha c n).eval beta)
      atTop (nhds 0) := by
  have hratio : ‖alpha⁻¹ * beta‖ < 1 := by
    rw [norm_mul, norm_inv]
    have hpos : 0 < ‖alpha‖ := norm_pos_iff.mpr halpha
    rw [inv_mul_lt_one₀ hpos]
    exact hinner
  have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hratio
  have hmul := hpow.const_mul
    ((c / (xiComplexFiniteSpectralSeparator F alpha).eval alpha) *
      (xiComplexFiniteSpectralSeparator F alpha).eval beta)
  have hmul0 : Tendsto (fun n =>
      ((c / (xiComplexFiniteSpectralSeparator F alpha).eval alpha) *
        (xiComplexFiniteSpectralSeparator F alpha).eval beta) *
          (alpha⁻¹ * beta) ^ n) atTop (nhds 0) := by
    simpa using hmul
  apply hmul0.congr'
  exact Eventually.of_forall fun n => by
    simp only [xiComplexRadialSeparatorPolynomial, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

def xiComplexRadialSeparatorBound (F : Finset ℂ) (alpha c : ℂ) : ℝ :=
  ‖c / (xiComplexFiniteSpectralSeparator F alpha).eval alpha‖ *
    ∏ beta ∈ F.erase alpha, (‖alpha‖ + ‖beta‖)

theorem xi_norm_eval_complexFiniteSpectralSeparator_le
    (F : Finset ℂ) (alpha z : ℂ) (hz : ‖z‖ ≤ ‖alpha‖) :
    ‖(xiComplexFiniteSpectralSeparator F alpha).eval z‖ ≤
      ∏ beta ∈ F.erase alpha, (‖alpha‖ + ‖beta‖) := by
  rw [xi_eval_complexFiniteSpectralSeparator]
  calc
    ‖∏ beta ∈ F.erase alpha, (z - beta)‖ ≤
        ∏ beta ∈ F.erase alpha, ‖z - beta‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ beta ∈ F.erase alpha, (‖alpha‖ + ‖beta‖) := by
      apply Finset.prod_le_prod
      · intro beta hbeta
        positivity
      · intro beta hbeta
        exact (norm_sub_le z beta).trans (add_le_add hz le_rfl)

theorem xi_norm_eval_complexRadialSeparatorPolynomial_le
    (F : Finset ℂ) {alpha z c : ℂ} (halpha : alpha ≠ 0)
    (hz : ‖z‖ ≤ ‖alpha‖) (n : ℕ) :
    ‖(xiComplexRadialSeparatorPolynomial F alpha c n).eval z‖ ≤
      xiComplexRadialSeparatorBound F alpha c := by
  have hpos : 0 < ‖alpha‖ := norm_pos_iff.mpr halpha
  have hradial : (‖alpha⁻¹‖ * ‖z‖) ^ n ≤ 1 := by
    have hbase : ‖alpha⁻¹‖ * ‖z‖ ≤ 1 := by
      rw [norm_inv, inv_mul_le_one₀ hpos]
      exact hz
    exact pow_le_one₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbase
  simp only [xiComplexRadialSeparatorPolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, norm_mul,
    norm_pow]
  change ‖c / (xiComplexFiniteSpectralSeparator F alpha).eval alpha‖ *
      ‖(xiComplexFiniteSpectralSeparator F alpha).eval z‖ *
        (‖alpha⁻¹‖ * ‖z‖) ^ n ≤ _
  have hsep := xi_norm_eval_complexFiniteSpectralSeparator_le F alpha z hz
  calc
    ‖c / Polynomial.eval alpha (xiComplexFiniteSpectralSeparator F alpha)‖ *
          ‖Polynomial.eval z (xiComplexFiniteSpectralSeparator F alpha)‖ *
            (‖alpha⁻¹‖ * ‖z‖) ^ n
        ≤ ‖c / Polynomial.eval alpha (xiComplexFiniteSpectralSeparator F alpha)‖ *
            (∏ beta ∈ F.erase alpha, (‖alpha‖ + ‖beta‖)) * 1 := by
          gcongr
    _ = xiComplexRadialSeparatorBound F alpha c := by
      simp only [xiComplexRadialSeparatorBound, mul_one]

def xiReciprocalCauchyKrylovAlgebraicSubspace (z : XiContinuedCauchyPoint) :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  Submodule.span ℂ (Set.range fun n : ℕ =>
    (xiReciprocalOperator ^ n) (xiWeilContinuedCauchyLp z))

def xiReciprocalCauchyKrylovHilbertSubspace (z : XiContinuedCauchyPoint) :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  (xiReciprocalCauchyKrylovAlgebraicSubspace z).topologicalClosure

theorem xiReciprocalCauchyKrylovPolynomialVector_mem_algebraicSubspace
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) :
    xiReciprocalCauchyKrylovPolynomialVector z p ∈ xiReciprocalCauchyKrylovAlgebraicSubspace z := by
  rw [xiReciprocalCauchyKrylovPolynomialVector]
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨n, rfl⟩

theorem xiReciprocalCauchyKrylovPolynomialVector_zero
    (z : XiContinuedCauchyPoint) :
    xiReciprocalCauchyKrylovPolynomialVector z 0 = 0 := by
  apply Subtype.ext
  funext q
  change xiReciprocalCauchyKrylovPolynomialVector z 0 q = (0 : ℂ)
  rw [xiReciprocalCauchyKrylovPolynomialVector_apply]
  simp

theorem xiReciprocalCauchyKrylovPolynomialVector_add
    (z : XiContinuedCauchyPoint) (p q : Polynomial ℂ) :
    xiReciprocalCauchyKrylovPolynomialVector z (p + q) =
      xiReciprocalCauchyKrylovPolynomialVector z p +
        xiReciprocalCauchyKrylovPolynomialVector z q := by
  apply Subtype.ext
  funext r
  rw [xiReciprocalCauchyKrylovPolynomialVector_apply]
  change _ = xiReciprocalCauchyKrylovPolynomialVector z p r +
    xiReciprocalCauchyKrylovPolynomialVector z q r
  rw [
    xiReciprocalCauchyKrylovPolynomialVector_apply,
    xiReciprocalCauchyKrylovPolynomialVector_apply]
  simp only [Polynomial.eval_add]
  ring

theorem xiReciprocalCauchyKrylovPolynomialVector_C_mul
    (z : XiContinuedCauchyPoint) (c : ℂ) (p : Polynomial ℂ) :
    xiReciprocalCauchyKrylovPolynomialVector z (Polynomial.C c * p) =
      c • xiReciprocalCauchyKrylovPolynomialVector z p := by
  apply Subtype.ext
  funext r
  rw [xiReciprocalCauchyKrylovPolynomialVector_apply]
  change _ = c * xiReciprocalCauchyKrylovPolynomialVector z p r
  rw [
    xiReciprocalCauchyKrylovPolynomialVector_apply]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem xiReciprocalCauchyKrylovPolynomialVector_X_pow
    (z : XiContinuedCauchyPoint) (n : ℕ) :
    xiReciprocalCauchyKrylovPolynomialVector z (Polynomial.X ^ n) =
      (xiReciprocalOperator ^ n) (xiWeilContinuedCauchyLp z) := by
  apply Subtype.ext
  funext q
  rw [xiReciprocalCauchyKrylovPolynomialVector_apply,
    xiReciprocalOperator_pow_apply]
  simp

/-- Every finite algebraic reciprocal-Krylov packet is represented by one complex polynomial. -/
theorem exists_polynomial_eq_of_mem_xiReciprocalCauchyKrylovAlgebraicSubspace
    (z : XiContinuedCauchyPoint)
    (v : lp (fun _ : XiZeroCopy => ℂ) 2)
    (hv : v ∈ xiReciprocalCauchyKrylovAlgebraicSubspace z) :
    ∃ p : Polynomial ℂ,
      xiReciprocalCauchyKrylovPolynomialVector z p = v := by
  rw [xiReciprocalCauchyKrylovAlgebraicSubspace] at hv
  refine Submodule.span_induction (p := fun v _ => ∃ p : Polynomial ℂ,
      xiReciprocalCauchyKrylovPolynomialVector z p = v) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨n, rfl⟩
    exact ⟨Polynomial.X ^ n,
      xiReciprocalCauchyKrylovPolynomialVector_X_pow z n⟩
  · exact ⟨0, xiReciprocalCauchyKrylovPolynomialVector_zero z⟩
  · rintro x y _hx _hy ⟨p, hp⟩ ⟨q, hq⟩
    refine ⟨p + q, ?_⟩
    rw [xiReciprocalCauchyKrylovPolynomialVector_add, hp, hq]
  · rintro c x _hx ⟨p, hp⟩
    refine ⟨Polynomial.C c * p, ?_⟩
    rw [xiReciprocalCauchyKrylovPolynomialVector_C_mul, hp]

theorem xiWeilContinuedCauchyLp_coordinate_ne_zero
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) :
    xiWeilContinuedCauchyLp z q ≠ 0 := by
  simp only [xiWeilContinuedCauchyLp, xiWeilCauchyLp_apply,
    xiWeilCauchyTest]
  exact inv_ne_zero (xiSpectralPoint_sub_continuedCauchyPoint_ne z q)

theorem xi_tendsto_reciprocalCauchyKrylovPolynomialVector_fiber
    (z : XiContinuedCauchyPoint) (rho : XiDivisorSupport) (d : ℂ) :
    ∃ p : ℕ → Polynomial ℂ,
      Tendsto (fun n => xiReciprocalCauchyKrylovPolynomialVector z (p n)) atTop
        (nhds (d • xiWeilFiberIndicatorLp (xiSpectralPointSupport rho))) := by
  let qRho : XiZeroCopy := xiFirstZeroCopy rho
  let alpha : ℂ := xiReciprocalSpectralSupport rho
  have halpha : alpha ≠ 0 := xiReciprocalSpectralSupport_ne_zero rho
  have hrad : 0 < ‖alpha‖ := norm_pos_iff.mpr halpha
  let S : Finset XiDivisorSupport :=
    (xiReciprocalSpectralSupport_finite_norm_ge hrad).toFinset
  have hrhoS : rho ∈ S := by
    simp only [S, Set.Finite.mem_toFinset]
    change ‖alpha‖ ≤ ‖xiReciprocalSpectralSupport rho‖
    change ‖alpha‖ ≤ ‖alpha‖
    exact le_rfl
  let F : Finset ℂ := S.image xiReciprocalSpectralSupport
  have halphaF : alpha ∈ F := by
    exact Finset.mem_image.mpr ⟨rho, hrhoS, rfl⟩
  let kRho : ℂ := xiWeilContinuedCauchyLp z qRho
  have hkRho : kRho ≠ 0 := xiWeilContinuedCauchyLp_coordinate_ne_zero z qRho
  let c : ℂ := d / kRho
  have hck : c * kRho = d := by
    exact div_mul_cancel₀ d hkRho
  let p : ℕ → Polynomial ℂ := fun n =>
    xiComplexRadialSeparatorPolynomial F alpha c n
  let V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2 := fun n =>
    xiReciprocalCauchyKrylovPolynomialVector z (p n)
  let I : lp (fun _ : XiZeroCopy => ℂ) 2 :=
    d • xiWeilFiberIndicatorLp (xiSpectralPointSupport rho)
  let M : ℝ := ‖c‖ + xiComplexRadialSeparatorBound F alpha c
  have hM : 0 ≤ M := by
    dsimp only [M, xiComplexRadialSeparatorBound]
    positivity
  have hevalBound (n : ℕ) (q : XiZeroCopy) :
      ‖(p n).eval (xiSpectralPoint q)⁻¹‖ ≤ M := by
    let beta : ℂ := xiReciprocalSpectralSupport q.1
    have hbeta : beta = (xiSpectralPoint q)⁻¹ := by
      simp only [beta, xiReciprocalSpectralSupport, xiSpectralPoint_eq_support]
    rw [← hbeta]
    by_cases hqrho : q.1 = rho
    · have hbetaAlpha : beta = alpha := by
        simp only [beta, alpha, hqrho]
      rw [hbetaAlpha]
      change ‖(xiComplexRadialSeparatorPolynomial F alpha c n).eval alpha‖ ≤ M
      rw [xi_eval_complexRadialSeparatorPolynomial_target F halpha n]
      exact le_add_of_nonneg_right (by
        dsimp only [xiComplexRadialSeparatorBound]
        positivity)
    · by_cases houter : ‖alpha‖ ≤ ‖beta‖
      · have hqS : q.1 ∈ S := by
          simp only [S, Set.Finite.mem_toFinset]
          exact houter
        have hbetaF : beta ∈ F := Finset.mem_image.mpr ⟨q.1, hqS, rfl⟩
        have hbetaAlpha : beta ≠ alpha := by
          intro h
          apply hqrho
          exact xiReciprocalSpectralSupport_injective h
        change ‖(xiComplexRadialSeparatorPolynomial F alpha c n).eval beta‖ ≤ M
        rw [xi_eval_complexRadialSeparatorPolynomial_outer_zero hbetaF hbetaAlpha n,
          norm_zero]
        exact hM
      · have hinner : ‖beta‖ ≤ ‖alpha‖ := le_of_lt (lt_of_not_ge houter)
        have hb := xi_norm_eval_complexRadialSeparatorPolynomial_le F
          (alpha := alpha) (z := beta) (c := c) halpha hinner n
        change ‖(xiComplexRadialSeparatorPolynomial F alpha c n).eval beta‖ ≤ M
        exact hb.trans (le_add_of_nonneg_left (norm_nonneg c))
  let term : ℕ → XiZeroCopy → ℝ := fun n q => ‖V n q - I q‖ ^ 2
  have hpoint (q : XiZeroCopy) :
      Tendsto (fun n => term n q) atTop (nhds 0) := by
    let beta : ℂ := xiReciprocalSpectralSupport q.1
    have hbeta : beta = (xiSpectralPoint q)⁻¹ := by
      simp only [beta, xiReciprocalSpectralSupport, xiSpectralPoint_eq_support]
    have hVapply (n : ℕ) :
        V n q = (p n).eval beta * xiWeilContinuedCauchyLp z q := by
      change xiReciprocalCauchyKrylovPolynomialVector z (p n) q = _
      rw [xiReciprocalCauchyKrylovPolynomialVector_apply, hbeta]
    by_cases hqrho : q.1 = rho
    · have hbetaAlpha : beta = alpha := by
        simp only [beta, alpha, hqrho]
      have hk : xiWeilContinuedCauchyLp z q = kRho := by
        simp only [kRho, qRho, xiWeilContinuedCauchyLp,
          xiWeilCauchyLp_apply, xiWeilCauchyTest,
          xiSpectralPoint_eq_support, hqrho, xiFirstZeroCopy_fst]
      have hIapply : I q = d := by
        simp [I, xiWeilFiberIndicatorLp_apply, xiSpectralPoint_eq_support,
          hqrho]
      have hzero : (fun n => term n q) = fun _ => 0 := by
        funext n
        simp only [term, hVapply n, hbetaAlpha, p]
        rw [xi_eval_complexRadialSeparatorPolynomial_target F halpha n,
          hk, hck, hIapply, sub_self, norm_zero, zero_pow (by norm_num)]
      rw [hzero]
      exact tendsto_const_nhds
    · have hIapply : I q = 0 := by
        have hspec : xiSpectralPoint q ≠ xiSpectralPointSupport rho := by
          rw [xiSpectralPoint_eq_support]
          intro h
          exact hqrho (xiSpectralPointSupport_injective h)
        simp [I, xiWeilFiberIndicatorLp_apply, hspec]
      by_cases houter : ‖alpha‖ ≤ ‖beta‖
      · have hqS : q.1 ∈ S := by
          simp only [S, Set.Finite.mem_toFinset]
          exact houter
        have hbetaF : beta ∈ F := Finset.mem_image.mpr ⟨q.1, hqS, rfl⟩
        have hbetaAlpha : beta ≠ alpha := by
          intro h
          apply hqrho
          exact xiReciprocalSpectralSupport_injective h
        have hzero : (fun n => term n q) = fun _ => 0 := by
          funext n
          simp only [term, hVapply n, p]
          rw [xi_eval_complexRadialSeparatorPolynomial_outer_zero hbetaF hbetaAlpha n,
            zero_mul, hIapply, sub_zero, norm_zero, zero_pow (by norm_num)]
        rw [hzero]
        exact tendsto_const_nhds
      · have hinner : ‖beta‖ < ‖alpha‖ := lt_of_not_ge houter
        have hp := xi_tendsto_eval_complexRadialSeparatorPolynomial_zero F
          (alpha := alpha) (beta := beta) (c := c) halpha hinner
        have hprod := hp.mul_const (xiWeilContinuedCauchyLp z q)
        have hsub : Tendsto
            (fun n => V n q - I q) atTop (nhds 0) := by
          simpa only [hVapply, hIapply, sub_zero, p, zero_mul] using hprod
        simpa [term] using hsub.norm.pow 2
  let bound : XiZeroCopy → ℝ := fun q =>
    2 * M ^ 2 * ‖xiWeilContinuedCauchyLp z q‖ ^ 2 + 2 * ‖I q‖ ^ 2
  have hboundSum : Summable bound := by
    have hk := HilbertSchmidt.summable_coe_sq (xiWeilContinuedCauchyLp z)
    have hI := HilbertSchmidt.summable_coe_sq I
    exact (hk.mul_left (2 * M ^ 2)).add (hI.mul_left 2)
  have hdom (n : ℕ) (q : XiZeroCopy) : term n q ≤ bound q := by
    have hVnorm : ‖V n q‖ ≤ M * ‖xiWeilContinuedCauchyLp z q‖ := by
      change ‖xiReciprocalCauchyKrylovPolynomialVector z (p n) q‖ ≤ _
      rw [xiReciprocalCauchyKrylovPolynomialVector_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right (hevalBound n q) (norm_nonneg _)
    have hsub : ‖V n q - I q‖ ≤ ‖V n q‖ + ‖I q‖ := norm_sub_le _ _
    have hVnonneg : 0 ≤ ‖V n q‖ := norm_nonneg _
    have hInonneg : 0 ≤ ‖I q‖ := norm_nonneg _
    have hMkNonneg : 0 ≤ M * ‖xiWeilContinuedCauchyLp z q‖ :=
      mul_nonneg hM (norm_nonneg _)
    have hVsq : ‖V n q‖ ^ 2 ≤
        M ^ 2 * ‖xiWeilContinuedCauchyLp z q‖ ^ 2 := by
      nlinarith
    have hsumSq : (‖V n q‖ + ‖I q‖) ^ 2 ≤
        2 * ‖V n q‖ ^ 2 + 2 * ‖I q‖ ^ 2 := by
      nlinarith [sq_nonneg (‖V n q‖ - ‖I q‖)]
    have hsubSq : ‖V n q - I q‖ ^ 2 ≤
        (‖V n q‖ + ‖I q‖) ^ 2 := by
      nlinarith [norm_nonneg (V n q - I q)]
    dsimp only [term, bound]
    nlinarith
  have htsum : Tendsto (fun n => ∑' q, term n q) atTop (nhds 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hboundSum hpoint
      (Eventually.of_forall fun n q => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hdom n q)
  have hnormsq (n : ℕ) : ‖V n - I‖ ^ 2 = ∑' q, term n q := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    apply tsum_congr
    intro q
    rfl
  have hsqzero : Tendsto (fun n => ‖V n - I‖ ^ 2) atTop (nhds 0) := by
    exact htsum.congr' (Eventually.of_forall fun n => (hnormsq n).symm)
  have hnormzero : Tendsto (fun n => ‖V n - I‖) atTop (nhds 0) := by
    have hsqrt := hsqzero.sqrt
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt
  refine ⟨p, ?_⟩
  change Tendsto V atTop (nhds I)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hnormzero

theorem xiWeilEvaluationFiberVector_mem_reciprocalCauchyKrylovHilbertSubspace
    (z : XiContinuedCauchyPoint) (Ftest : ℂ → ℂ)
    (rho : XiDivisorSupport) :
    xiWeilEvaluationFiberVector Ftest rho ∈
      xiReciprocalCauchyKrylovHilbertSubspace z := by
  obtain ⟨p, hp⟩ := xi_tendsto_reciprocalCauchyKrylovPolynomialVector_fiber z rho
    (Ftest (xiSpectralPointSupport rho))
  apply (Submodule.isClosed_topologicalClosure
    (xiReciprocalCauchyKrylovAlgebraicSubspace z)).mem_of_tendsto hp
  exact Eventually.of_forall fun n =>
    (xiReciprocalCauchyKrylovAlgebraicSubspace z).le_topologicalClosure
      (xiReciprocalCauchyKrylovPolynomialVector_mem_algebraicSubspace z (p n))

theorem xiWeilEvaluationLp_mem_reciprocalCauchyKrylovHilbertSubspace
    (z : XiContinuedCauchyPoint) (Ftest : ℂ → ℂ)
    (hF : XiWeilSquareSummable Ftest) :
    xiWeilEvaluationLp Ftest hF ∈
      xiReciprocalCauchyKrylovHilbertSubspace z := by
  have hmem : (∑' rho : XiDivisorSupport,
      xiWeilEvaluationFiberVector Ftest rho) ∈
      xiReciprocalCauchyKrylovHilbertSubspace z :=
    tsum_mem
      (Submodule.isClosed_topologicalClosure
        (xiReciprocalCauchyKrylovAlgebraicSubspace z))
      (xiWeilEvaluationFiberVector_mem_reciprocalCauchyKrylovHilbertSubspace z Ftest)
  rw [(hasSum_xiWeilEvaluationFiberVector Ftest hF).tsum_eq] at hmem
  exact hmem

/-- Every multiplicity-safe evaluation is a norm limit of actual polynomial vectors from one
fixed reciprocal-Krylov orbit. -/
theorem exists_reciprocalCauchyKrylovPolynomials_tendsto_evaluation
    (z : XiContinuedCauchyPoint) (Ftest : ℂ → ℂ)
    (hF : XiWeilSquareSummable Ftest) :
    ∃ p : ℕ → Polynomial ℂ,
      Tendsto (fun n => xiReciprocalCauchyKrylovPolynomialVector z (p n))
        atTop (nhds (xiWeilEvaluationLp Ftest hF)) := by
  have hclosure : xiWeilEvaluationLp Ftest hF ∈
      closure (↑(xiReciprocalCauchyKrylovAlgebraicSubspace z) :
        Set (lp (fun _ : XiZeroCopy => ℂ) 2)) := by
    exact xiWeilEvaluationLp_mem_reciprocalCauchyKrylovHilbertSubspace z Ftest hF
  have happ : ∀ n : ℕ, ∃ v,
      v ∈ xiReciprocalCauchyKrylovAlgebraicSubspace z ∧
      dist (xiWeilEvaluationLp Ftest hF) v < 1 / ((n : ℝ) + 1) := by
    intro n
    exact Metric.mem_closure_iff.mp hclosure _ (by positivity)
  choose V hVmem hVdist using happ
  have hpoly : ∀ n, ∃ p : Polynomial ℂ,
      xiReciprocalCauchyKrylovPolynomialVector z p = V n := fun n =>
    exists_polynomial_eq_of_mem_xiReciprocalCauchyKrylovAlgebraicSubspace
      z (V n) (hVmem n)
  choose p hp using hpoly
  refine ⟨p, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn => ?_⟩
  rw [hp n, dist_comm]
  have hden : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hn 1
  exact (hVdist n).trans
    ((one_div_le_one_div_of_le (by positivity) hden).trans_lt hN)

/-- Holomorphic test represented by a polynomial in the reciprocal coordinate times one fixed
Cauchy atom. -/
def xiReciprocalCauchyKrylovPolynomialTest
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) (a : ℂ) : ℂ :=
  p.eval a⁻¹ * (a - (z : ℂ))⁻¹

theorem xiReciprocalCauchyKrylovPolynomialTest_squareSummable
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) :
    XiWeilSquareSummable (xiReciprocalCauchyKrylovPolynomialTest z p) := by
  have hsum := HilbertSchmidt.summable_coe_sq
    (xiReciprocalCauchyKrylovPolynomialVector z p)
  apply hsum.congr
  intro q
  rw [xiReciprocalCauchyKrylovPolynomialVector_apply]
  rfl

theorem xiReciprocalCauchyKrylovPolynomialTest_evaluation
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) :
    xiWeilEvaluationLp (xiReciprocalCauchyKrylovPolynomialTest z p)
        (xiReciprocalCauchyKrylovPolynomialTest_squareSummable z p) =
      xiReciprocalCauchyKrylovPolynomialVector z p := by
  apply Subtype.ext
  funext q
  rw [xiWeilEvaluationLp_apply,
    xiReciprocalCauchyKrylovPolynomialVector_apply]
  rfl

def xiReciprocalCauchyKrylovSourcePlusTest
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) (a : ℂ) : ℂ :=
  xiWeilCauchyTest (z : ℂ) a +
    I * xiReciprocalCauchyKrylovPolynomialTest z p a

def xiReciprocalCauchyKrylovSourceMinusTest
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) (a : ℂ) : ℂ :=
  xiWeilCauchyTest (z : ℂ) a -
    I * xiReciprocalCauchyKrylovPolynomialTest z p a

theorem xiReciprocalCauchyKrylovSourcePlusTest_squareSummable
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) :
    XiWeilSquareSummable (xiReciprocalCauchyKrylovSourcePlusTest z p) := by
  have hsum := HilbertSchmidt.summable_coe_sq
    (xiWeilContinuedCauchyLp z +
      I • xiReciprocalCauchyKrylovPolynomialVector z p)
  apply hsum.congr
  intro q
  symm
  change ‖xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) +
    I * xiReciprocalCauchyKrylovPolynomialTest z p (xiSpectralPoint q)‖ ^ 2 = _
  change _ = ‖xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) +
    I * xiReciprocalCauchyKrylovPolynomialVector z p q‖ ^ 2
  rw [xiReciprocalCauchyKrylovPolynomialVector_apply]
  rfl

theorem xiReciprocalCauchyKrylovSourceMinusTest_squareSummable
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) :
    XiWeilSquareSummable (xiReciprocalCauchyKrylovSourceMinusTest z p) := by
  have hsum := HilbertSchmidt.summable_coe_sq
    (xiWeilContinuedCauchyLp z -
      I • xiReciprocalCauchyKrylovPolynomialVector z p)
  apply hsum.congr
  intro q
  symm
  change ‖xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) -
    I * xiReciprocalCauchyKrylovPolynomialTest z p (xiSpectralPoint q)‖ ^ 2 = _
  change _ = ‖xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) -
    I * xiReciprocalCauchyKrylovPolynomialVector z p q‖ ^ 2
  rw [xiReciprocalCauchyKrylovPolynomialVector_apply]
  rfl

theorem xiReciprocalCauchyKrylovSourcePlusTest_evaluation
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) :
    xiWeilEvaluationLp (xiReciprocalCauchyKrylovSourcePlusTest z p)
        (xiReciprocalCauchyKrylovSourcePlusTest_squareSummable z p) =
      xiWeilContinuedCauchyLp z +
        I • xiReciprocalCauchyKrylovPolynomialVector z p := by
  apply Subtype.ext
  funext q
  change xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) +
      I * xiReciprocalCauchyKrylovPolynomialTest z p (xiSpectralPoint q) =
    xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) +
      I * xiReciprocalCauchyKrylovPolynomialVector z p q
  rw [xiReciprocalCauchyKrylovPolynomialVector_apply]
  rfl

theorem xiReciprocalCauchyKrylovSourceMinusTest_evaluation
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) :
    xiWeilEvaluationLp (xiReciprocalCauchyKrylovSourceMinusTest z p)
        (xiReciprocalCauchyKrylovSourceMinusTest_squareSummable z p) =
      xiWeilContinuedCauchyLp z -
        I • xiReciprocalCauchyKrylovPolynomialVector z p := by
  apply Subtype.ext
  funext q
  change xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) -
      I * xiReciprocalCauchyKrylovPolynomialTest z p (xiSpectralPoint q) =
    xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) -
      I * xiReciprocalCauchyKrylovPolynomialVector z p q
  rw [xiReciprocalCauchyKrylovPolynomialVector_apply]
  rfl

/-- Norm convergence of reciprocal-polynomial responses forces convergence of their fully
holomorphic source-polarization contrast to the reciprocal-square orientation defect. -/
theorem xiReciprocalCauchyKrylovSourceContrast_tendsto_orientationDefect_of_response_tendsto
    (z : XiContinuedCauchyPoint) (p : ℕ → Polynomial ℂ)
    (hp : Tendsto
      (fun n => xiReciprocalCauchyKrylovPolynomialVector z (p n)) atTop
      (nhds (xiWeilEvaluationLp
        (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
        (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z)))) :
    Tendsto (fun n =>
        ((xiWeilPolarization
              (xiReciprocalCauchyKrylovSourcePlusTest z (p n))
              (xiReciprocalCauchyKrylovSourcePlusTest z (p n))).re -
          (xiWeilPolarization
              (xiReciprocalCauchyKrylovSourceMinusTest z (p n))
              (xiReciprocalCauchyKrylovSourceMinusTest z (p n))).re) / 4)
      atTop (nhds (xiReciprocalSquareContinuedCauchyOrientationDefect z)) := by
  let k := xiWeilContinuedCauchyLp z
  let r := xiWeilEvaluationLp
    (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
    (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z)
  let V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2 := fun n =>
    xiReciprocalCauchyKrylovPolynomialVector z (p n)
  have hplusVec : Tendsto (fun n => k + I • V n) atTop
      (nhds (k + I • r)) := by
    exact tendsto_const_nhds.add (hp.const_smul I)
  have hminusVec : Tendsto (fun n => k - I • V n) atTop
      (nhds (k - I • r)) := by
    exact tendsto_const_nhds.sub (hp.const_smul I)
  have hQplus :=
    continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hplusVec
  have hQminus :=
    continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hminusVec
  have hplusEnergy : Tendsto (fun n =>
      (xiWeilPolarization
        (xiReciprocalCauchyKrylovSourcePlusTest z (p n))
        (xiReciprocalCauchyKrylovSourcePlusTest z (p n))).re) atTop
      (nhds (xiWeilPolarization
        (xiReciprocalSquareCauchySourcePlusTest (z : ℂ))
        (xiReciprocalSquareCauchySourcePlusTest (z : ℂ))).re) := by
    convert hQplus using 1
    · funext n
      rw [← xiWeilHilbertQuadratic_evaluation_eq_polarization_re
          (xiReciprocalCauchyKrylovSourcePlusTest z (p n))
          (xiReciprocalCauchyKrylovSourcePlusTest_squareSummable z (p n)),
        xiReciprocalCauchyKrylovSourcePlusTest_evaluation]
      rfl
    · rw [← xiWeilHilbertQuadratic_evaluation_eq_polarization_re
          (xiReciprocalSquareCauchySourcePlusTest (z : ℂ))
          (xiReciprocalSquareCauchySourcePlusTest_squareSummable z),
        xiReciprocalSquareCauchySourcePlusTest_evaluation]
  have hminusEnergy : Tendsto (fun n =>
      (xiWeilPolarization
        (xiReciprocalCauchyKrylovSourceMinusTest z (p n))
        (xiReciprocalCauchyKrylovSourceMinusTest z (p n))).re) atTop
      (nhds (xiWeilPolarization
        (xiReciprocalSquareCauchySourceMinusTest (z : ℂ))
        (xiReciprocalSquareCauchySourceMinusTest (z : ℂ))).re) := by
    convert hQminus using 1
    · funext n
      rw [← xiWeilHilbertQuadratic_evaluation_eq_polarization_re
          (xiReciprocalCauchyKrylovSourceMinusTest z (p n))
          (xiReciprocalCauchyKrylovSourceMinusTest_squareSummable z (p n)),
        xiReciprocalCauchyKrylovSourceMinusTest_evaluation]
      rfl
    · rw [← xiWeilHilbertQuadratic_evaluation_eq_polarization_re
          (xiReciprocalSquareCauchySourceMinusTest (z : ℂ))
          (xiReciprocalSquareCauchySourceMinusTest_squareSummable z),
        xiReciprocalSquareCauchySourceMinusTest_evaluation]
  have hcontrast := (hplusEnergy.sub hminusEnergy).const_mul (1 / 4 : ℝ)
  convert hcontrast using 1
  · funext n
    ring
  · congr 1
    linarith [
      xiReciprocalSquareCauchySourceContrast_eq_four_mul_orientationDefect z]

/-- The fixed adjoint response is unconditionally recovered from one fixed Cauchy vector by
complex reciprocal polynomials, and the corresponding holomorphic source contrast converges to
the one-scalar RH defect. -/
theorem exists_fixedReciprocalCauchyKrylovSourceContrast_tendsto_orientationDefect :
    ∃ p : ℕ → Polynomial ℂ,
      Tendsto (fun n => xiReciprocalCauchyKrylovPolynomialVector
          xiReciprocalSquareFixedCauchyPole (p n)) atTop
        (nhds (xiWeilEvaluationLp
          (xiReciprocalSquareCauchyAdjointResponseTest
            (xiReciprocalSquareFixedCauchyPole : ℂ))
          (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
            xiReciprocalSquareFixedCauchyPole))) ∧
      Tendsto (fun n =>
          ((xiWeilPolarization
                (xiReciprocalCauchyKrylovSourcePlusTest
                  xiReciprocalSquareFixedCauchyPole (p n))
                (xiReciprocalCauchyKrylovSourcePlusTest
                  xiReciprocalSquareFixedCauchyPole (p n))).re -
            (xiWeilPolarization
                (xiReciprocalCauchyKrylovSourceMinusTest
                  xiReciprocalSquareFixedCauchyPole (p n))
                (xiReciprocalCauchyKrylovSourceMinusTest
                  xiReciprocalSquareFixedCauchyPole (p n))).re) / 4)
        atTop (nhds (xiReciprocalSquareContinuedCauchyOrientationDefect
          xiReciprocalSquareFixedCauchyPole)) := by
  obtain ⟨p, hp⟩ := exists_reciprocalCauchyKrylovPolynomials_tendsto_evaluation
    xiReciprocalSquareFixedCauchyPole
    (xiReciprocalSquareCauchyAdjointResponseTest
      (xiReciprocalSquareFixedCauchyPole : ℂ))
    (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
      xiReciprocalSquareFixedCauchyPole)
  exact ⟨p, hp,
    xiReciprocalCauchyKrylovSourceContrast_tendsto_orientationDefect_of_response_tendsto
      xiReciprocalSquareFixedCauchyPole p hp⟩

/-- Right-side RH interface constrained to holomorphic reciprocal-polynomial tests generated by
one predetermined Cauchy source. Response recovery is unconditional; only vanishing of resulting
source-polarization contrast remains. -/
def XiReciprocalSquareFixedCauchyKrylovSourceContrastSaturation : Prop :=
  ∃ p : ℕ → Polynomial ℂ,
    Tendsto (fun n => xiReciprocalCauchyKrylovPolynomialVector
        xiReciprocalSquareFixedCauchyPole (p n)) atTop
      (nhds (xiWeilEvaluationLp
        (xiReciprocalSquareCauchyAdjointResponseTest
          (xiReciprocalSquareFixedCauchyPole : ℂ))
        (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
          xiReciprocalSquareFixedCauchyPole))) ∧
    Tendsto (fun n =>
        ((xiWeilPolarization
              (xiReciprocalCauchyKrylovSourcePlusTest
                xiReciprocalSquareFixedCauchyPole (p n))
              (xiReciprocalCauchyKrylovSourcePlusTest
                xiReciprocalSquareFixedCauchyPole (p n))).re -
          (xiWeilPolarization
              (xiReciprocalCauchyKrylovSourceMinusTest
                xiReciprocalSquareFixedCauchyPole (p n))
              (xiReciprocalCauchyKrylovSourceMinusTest
                xiReciprocalSquareFixedCauchyPole (p n))).re) / 4)
      atTop (nhds 0)

/-- Vanishing reciprocal-Krylov source contrast at one fixed Cauchy pole is exactly RH. -/
theorem xiReciprocalSquareFixedCauchyKrylovSourceContrastSaturation_iff_riemannHypothesis :
    XiReciprocalSquareFixedCauchyKrylovSourceContrastSaturation ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨p, hp, hzero⟩
    have hdefect :=
      xiReciprocalCauchyKrylovSourceContrast_tendsto_orientationDefect_of_response_tendsto
        xiReciprocalSquareFixedCauchyPole p hp
    have hD : xiReciprocalSquareContinuedCauchyOrientationDefect
        xiReciprocalSquareFixedCauchyPole = 0 :=
      tendsto_nhds_unique hdefect hzero
    exact xiReciprocalSquareFixedCauchyOrientationDefectZero_iff_riemannHypothesis.mp hD
  · intro hRH
    obtain ⟨p, hp, hcontrast⟩ :=
      exists_fixedReciprocalCauchyKrylovSourceContrast_tendsto_orientationDefect
    have hD : xiReciprocalSquareContinuedCauchyOrientationDefect
        xiReciprocalSquareFixedCauchyPole = 0 :=
      xiReciprocalSquareFixedCauchyOrientationDefectZero_iff_riemannHypothesis.mpr hRH
    exact ⟨p, hp, by simpa [hD] using hcontrast⟩

def xiReciprocalCauchyKrylovTest
    (z : XiContinuedCauchyPoint) (n : ℕ) (a : ℂ) : ℂ :=
  a⁻¹ ^ n * (a - (z : ℂ))⁻¹

theorem xiReciprocalCauchyKrylovTest_squareSummable
    (z : XiContinuedCauchyPoint) (n : ℕ) :
    XiWeilSquareSummable (xiReciprocalCauchyKrylovTest z n) := by
  have hsum := HilbertSchmidt.summable_coe_sq
    ((xiReciprocalOperator ^ n) (xiWeilContinuedCauchyLp z))
  apply hsum.congr
  intro q
  rw [xiReciprocalOperator_pow_apply]
  rfl

theorem xiReciprocalCauchyKrylovTest_evaluation
    (z : XiContinuedCauchyPoint) (n : ℕ) :
    xiWeilEvaluationLp (xiReciprocalCauchyKrylovTest z n)
        (xiReciprocalCauchyKrylovTest_squareSummable z n) =
      (xiReciprocalOperator ^ n) (xiWeilContinuedCauchyLp z) := by
  apply Subtype.ext
  funext q
  rw [xiWeilEvaluationLp_apply, xiReciprocalOperator_pow_apply]
  rfl

theorem xiReciprocalCauchyKrylovHilbertSubspace_le_continuedCauchyHilbertSubspace
    (z : XiContinuedCauchyPoint) :
    xiReciprocalCauchyKrylovHilbertSubspace z ≤
      xiWeilContinuedCauchyHilbertSubspace := by
  apply Submodule.topologicalClosure_minimal
  · rw [xiReciprocalCauchyKrylovAlgebraicSubspace, Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    change (xiReciprocalOperator ^ n) (xiWeilContinuedCauchyLp z) ∈
      xiWeilContinuedCauchyHilbertSubspace
    rw [← xiReciprocalCauchyKrylovTest_evaluation z n]
    exact xiWeilEvaluationLp_mem_continuedCauchyHilbertSubspace
      (xiReciprocalCauchyKrylovTest z n)
      (xiReciprocalCauchyKrylovTest_squareSummable z n)
  · exact Submodule.isClosed_topologicalClosure
      xiWeilContinuedCauchyAlgebraicSubspace

theorem xiWeilContinuedCauchyHilbertSubspace_le_reciprocalCauchyKrylovHilbertSubspace
    (z : XiContinuedCauchyPoint) :
    xiWeilContinuedCauchyHilbertSubspace ≤
      xiReciprocalCauchyKrylovHilbertSubspace z := by
  apply Submodule.topologicalClosure_minimal
  · rw [xiWeilContinuedCauchyAlgebraicSubspace, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact xiWeilEvaluationLp_mem_reciprocalCauchyKrylovHilbertSubspace z
      (xiWeilCauchyTest (w : ℂ)) (XiWeilSquareSummable_cauchy (w : ℂ))
  · exact Submodule.isClosed_topologicalClosure
      (xiReciprocalCauchyKrylovAlgebraicSubspace z)

theorem xiReciprocalCauchyKrylovHilbertSubspace_eq_continuedCauchyHilbertSubspace
    (z : XiContinuedCauchyPoint) :
    xiReciprocalCauchyKrylovHilbertSubspace z =
      xiWeilContinuedCauchyHilbertSubspace := by
  apply le_antisymm
  · exact xiReciprocalCauchyKrylovHilbertSubspace_le_continuedCauchyHilbertSubspace z
  · exact xiWeilContinuedCauchyHilbertSubspace_le_reciprocalCauchyKrylovHilbertSubspace z

theorem xiReciprocalSquareFixedCauchyAdjointResponse_mem_krylovHilbertSubspace :
    xiWeilEvaluationLp
        (xiReciprocalSquareCauchyAdjointResponseTest
          (xiReciprocalSquareFixedCauchyPole : ℂ))
        (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
          xiReciprocalSquareFixedCauchyPole) ∈
      xiReciprocalCauchyKrylovHilbertSubspace
        xiReciprocalSquareFixedCauchyPole := by
  exact xiWeilEvaluationLp_mem_reciprocalCauchyKrylovHilbertSubspace
    xiReciprocalSquareFixedCauchyPole
    (xiReciprocalSquareCauchyAdjointResponseTest
      (xiReciprocalSquareFixedCauchyPole : ℂ))
    (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
      xiReciprocalSquareFixedCauchyPole)

end

end RHTower
