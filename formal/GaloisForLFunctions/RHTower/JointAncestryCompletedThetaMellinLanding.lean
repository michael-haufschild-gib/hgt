import GaloisForLFunctions.RHTower.JointAncestryRestrictionHistoryArithmeticSpecialization
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticTranslate
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds
import GaloisForLFunctions.RHTower.XiThetaLogTranslationSeam
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreCancellation
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment

/-!
# Joint ancestry: completed-theta landing and the full-density obstruction

This module tests the literal completed theta density against the closed singular Mellin operator,
rather than constructing another abstract carrier.

It proves four sharp facts:

* maximal multiplication by `exp` has no eigenvectors, excluding coefficientwise eigenlanding;
* every actual differentiated theta atom lies in the maximal domain, with exact reciprocal-index
  Mellin covariance and injective arithmetic coefficients;
* positive-half completion creates an explicit nonzero swept-boundary current;
* the unrenormalized full density is not in full-line `L²`, while the exact survivor
  `rho - rawTail = 4 Phi` lies in the maximal domain and has cosine current exactly `XiC`.

Thus the full-density route is killed before completion ambiguity can be hidden, and its strongest
completed-Xi survivor is retained as a closed, coefficient-faithful operator landing.
-/

open Complex Real MeasureTheory Set Polynomial
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

theorem jointAncestry_exp_ne_eigenvalue_of_ne_exception
    (z : ℂ) {x : ℝ} (hx : x ≠ Real.log z.re) :
    (Real.exp x : ℂ) ≠ z := by
  intro heq
  apply hx
  have hre := congrArg Complex.re heq
  have hzpos : 0 < z.re := by
    rw [← hre]
    exact Real.exp_pos x
  rw [← Real.exp_log hzpos] at hre
  exact Real.exp_injective hre

theorem jointAncestry_ae_eq_zero_of_exp_mul_eq
    (z : ℂ) {f : ℝ → ℂ}
    (h : ∀ᵐ x : ℝ ∂volume, (Real.exp x : ℂ) * f x = z * f x) :
    f =ᵐ[volume] 0 := by
  filter_upwards [h, (volume : Measure ℝ).ae_ne (Real.log z.re)] with x hx hne
  have hcoef : (Real.exp x : ℂ) - z ≠ 0 :=
    sub_ne_zero.mpr (jointAncestry_exp_ne_eigenvalue_of_ne_exception z hne)
  have hzero : ((Real.exp x : ℂ) - z) * f x = 0 := by
    rw [sub_mul, hx, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left hcoef

theorem jointAncestrySingularMellinOperator_has_no_eigenvector
    (z : ℂ) (f : jointAncestrySingularMellinOperator.domain)
    (h : jointAncestrySingularMellinOperator f =
      z • (f : Lp ℂ 2 (volume : Measure ℝ))) :
    (f : Lp ℂ 2 (volume : Measure ℝ)) = 0 := by
  have hmul := maximalRealL2Mul_apply_ae volume Real.exp f
  have h' : maximalRealL2Mul volume Real.exp f =
      z • (f : Lp ℂ 2 (volume : Measure ℝ)) := by
    simpa only [jointAncestrySingularMellinOperator] using h
  rw [h'] at hmul
  have hzero := jointAncestry_ae_eq_zero_of_exp_mul_eq z (by
    filter_upwards [hmul, Lp.coeFn_smul z
      (f : Lp ℂ 2 (volume : Measure ℝ))] with x hx hsmul
    calc
      (Real.exp x : ℂ) * (f : Lp ℂ 2 (volume : Measure ℝ)) x =
          (z • (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 volume) x := hx.symm
      _ = z * (f : Lp ℂ 2 (volume : Measure ℝ)) x := by
        rw [hsmul]
        rfl)
  apply Lp.ext
  filter_upwards [hzero, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx h0
  rw [hx, h0]

def JASCoefficientwiseMellinEigenlanding : Prop :=
  ∃ F : ℕ → jointAncestrySingularMellinOperator.domain,
    Function.Injective (fun n =>
      (F n : Lp ℂ 2 (volume : Measure ℝ))) ∧
    ∀ n, jointAncestrySingularMellinOperator (F n) =
      ((n + 1 : ℝ) : ℂ) •
        (F n : Lp ℂ 2 (volume : Measure ℝ))

theorem not_jointAncestryCoefficientwiseMellinEigenlanding :
    ¬ JASCoefficientwiseMellinEigenlanding := by
  rintro ⟨F, hF, heigen⟩
  have h0 := jointAncestrySingularMellinOperator_has_no_eigenvector
    (1 : ℂ) (F 0) (by simpa using heigen 0)
  have h1 := jointAncestrySingularMellinOperator_has_no_eigenvector
    (2 : ℂ) (F 1) (by
      convert heigen 1 using 1
      norm_num)
  exact Nat.zero_ne_one (hF (h0.trans h1.symm))

private def thetaPolynomialAtomPositiveConstant (P : ℝ[X]) (r : ℕ) : ℝ :=
  thetaCuspCoeffMass P *
    Real.exp (((r + 1 + P.natDegree + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi)) *
      Real.exp (-(Real.pi / 2))

private theorem abs_thetaCuspPolynomialAtom_one_le_coeffMass_exp_half_of_nonpos
    (P : ℝ[X]) {x : ℝ} (hx : x ≤ 0) :
    |thetaCuspPolynomialAtom P 1 x| ≤
      thetaCuspCoeffMass P * Real.exp (x / 2) := by
  have hexp0 : 0 ≤ Real.exp x := (Real.exp_pos x).le
  have hexp1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx
  have heval0 := abs_eval_le_coefficient_sum P hexp0
  have heval : |eval (Real.exp x) P| ≤ thetaCuspCoeffMass P := by
    refine heval0.trans ?_
    unfold thetaCuspCoeffMass
    refine Finset.sum_le_sum fun k hk => ?_
    simpa using
      (mul_le_mul_of_nonneg_left (pow_le_one₀ hexp0 hexp1) (abs_nonneg (P.coeff k)))
  have hgauss : Real.exp (-Real.pi * Real.exp x ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _)
  rw [thetaCuspPolynomialAtom]
  simp only [Nat.cast_one, one_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (x / 2) * |eval (Real.exp x) P| *
          Real.exp (-Real.pi * Real.exp x ^ 2) ≤
        Real.exp (x / 2) * thetaCuspCoeffMass P * 1 := by
          have hmass : 0 ≤ thetaCuspCoeffMass P := thetaCuspCoeffMass_nonneg P
          calc
            Real.exp (x / 2) * |eval (Real.exp x) P| *
                Real.exp (-Real.pi * Real.exp x ^ 2) ≤
              Real.exp (x / 2) * thetaCuspCoeffMass P *
                Real.exp (-Real.pi * Real.exp x ^ 2) := by gcongr
            _ ≤ Real.exp (x / 2) * thetaCuspCoeffMass P * 1 := by gcongr
    _ = thetaCuspCoeffMass P * Real.exp (x / 2) := by ring

private theorem thetaCuspPolynomialAtom_one_expWeight_memLp
    (P : ℝ[X]) (r : ℕ) :
    MemLp (fun x : ℝ => ((Real.exp ((r : ℝ) * x) *
      thetaCuspPolynomialAtom P 1 x : ℝ) : ℂ)) 2 volume := by
  let Cneg : ℝ := thetaCuspCoeffMass P
  let Cpos : ℝ := thetaPolynomialAtomPositiveConstant P r
  have hcont : Continuous (fun x : ℝ => ((Real.exp ((r : ℝ) * x) *
      thetaCuspPolynomialAtom P 1 x : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (continuous_iff_continuousAt.mpr fun x =>
          (hasDerivAt_thetaCuspPolynomialAtom P 1 x).continuousAt))
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  apply IntegrableOn.union
  · have hdom : IntegrableOn (fun x : ℝ => Cneg ^ 2 * Real.exp x) (Iic 0) :=
      (integrableOn_exp_Iic 0).const_mul (Cneg ^ 2)
    refine Integrable.mono' hdom (hcont.norm.pow 2).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Iic).2
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hrx : Real.exp ((r : ℝ) * x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg r) hx
    have hatom := abs_thetaCuspPolynomialAtom_one_le_coeffMass_exp_half_of_nonpos P hx
    change |‖((Real.exp ((r : ℝ) * x) *
      thetaCuspPolynomialAtom P 1 x : ℝ) : ℂ)‖ ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have hweighted : Real.exp ((r : ℝ) * x) *
        |thetaCuspPolynomialAtom P 1 x| ≤ Cneg * Real.exp (x / 2) := by
      dsimp [Cneg]
      calc
        Real.exp ((r : ℝ) * x) * |thetaCuspPolynomialAtom P 1 x| ≤
            1 * |thetaCuspPolynomialAtom P 1 x| := by gcongr
        _ ≤ thetaCuspCoeffMass P * Real.exp (x / 2) := by simpa using hatom
    have hnon : 0 ≤ Cneg * Real.exp (x / 2) := by
      exact mul_nonneg (thetaCuspCoeffMass_nonneg P) (Real.exp_pos _).le
    calc
      (Real.exp ((r : ℝ) * x) * |thetaCuspPolynomialAtom P 1 x|) ^ 2 ≤
          (Cneg * Real.exp (x / 2)) ^ 2 := pow_le_pow_left₀ (by positivity) hweighted 2
      _ = Cneg ^ 2 * Real.exp x := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 1
        ring_nf
  · have hdom : IntegrableOn (fun x : ℝ => Cpos ^ 2 * Real.exp (-2 * x)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).const_mul (Cpos ^ 2)
    refine Integrable.mono' hdom (hcont.norm.pow 2).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hraw := exp_nat_mul_abs_thetaCuspPolynomialAtom_le_of_pos
      P (r + 1) hx.le (by omega : 0 < (1 : ℕ))
    have hbound : Real.exp (((r + 1 : ℕ) : ℝ) * x) *
        |thetaCuspPolynomialAtom P 1 x| ≤ Cpos := by
      simpa [Cpos, thetaPolynomialAtomPositiveConstant] using hraw
    have hrewrite : Real.exp ((r : ℝ) * x) *
        |thetaCuspPolynomialAtom P 1 x| =
          Real.exp (-x) *
            (Real.exp (((r + 1 : ℕ) : ℝ) * x) *
              |thetaCuspPolynomialAtom P 1 x|) := by
      have hexp : Real.exp ((r : ℝ) * x) =
          Real.exp (-x) * Real.exp (((r + 1 : ℕ) : ℝ) * x) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      ring
    change |‖((Real.exp ((r : ℝ) * x) *
      thetaCuspPolynomialAtom P 1 x : ℝ) : ℂ)‖ ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), hrewrite]
    have hnonC : 0 ≤ Cpos := by
      dsimp [Cpos, thetaPolynomialAtomPositiveConstant]
      positivity [thetaCuspCoeffMass_nonneg P]
    calc
      (Real.exp (-x) *
          (Real.exp (((r + 1 : ℕ) : ℝ) * x) *
            |thetaCuspPolynomialAtom P 1 x|)) ^ 2 ≤
          (Real.exp (-x) * Cpos) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity)
            exact mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
      _ = Cpos ^ 2 * Real.exp (-2 * x) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        ring_nf

theorem thetaCuspTailSecondDensityAtom_one_memLp :
    MemLp (fun x : ℝ => (thetaCuspTailSecondDensityAtom 1 x : ℂ)) 2 volume := by
  have h := (thetaCuspPolynomialAtom_one_expWeight_memLp
    (thetaCuspTailDerivativePolynomial 2) 0).const_mul (4 : ℂ)
  refine (memLp_congr_ae ?_).mpr h
  filter_upwards with x
  simp only [thetaCuspTailSecondDensityAtom, Nat.cast_zero, zero_mul, Real.exp_zero,
    one_mul]
  push_cast
  ring

theorem exp_mul_thetaCuspTailSecondDensityAtom_one_memLp :
    MemLp (fun x : ℝ => (Real.exp x : ℂ) *
      thetaCuspTailSecondDensityAtom 1 x) 2 volume := by
  have h := (thetaCuspPolynomialAtom_one_expWeight_memLp
    (thetaCuspTailDerivativePolynomial 2) 1).const_mul (4 : ℂ)
  refine (memLp_congr_ae ?_).mpr h
  filter_upwards with x
  simp only [thetaCuspTailSecondDensityAtom, Nat.cast_one, one_mul]
  push_cast
  ring

/-- The actual first completed-theta second-density atom as a full-line `L²` vector. -/
def jointAncestryThetaDensitySeedL2 : Lp ℂ 2 (volume : Measure ℝ) :=
  thetaCuspTailSecondDensityAtom_one_memLp.toLp
    (fun x : ℝ => (thetaCuspTailSecondDensityAtom 1 x : ℂ))

theorem jointAncestryThetaDensitySeedL2_coeFn :
    (jointAncestryThetaDensitySeedL2 : ℝ → ℂ) =ᵐ[volume]
      fun x => (thetaCuspTailSecondDensityAtom 1 x : ℂ) :=
  MemLp.coeFn_toLp thetaCuspTailSecondDensityAtom_one_memLp

/-- The first completed-theta atom belongs to the maximal singular-Mellin domain. -/
def jointAncestryThetaDensitySeedDomain :
    jointAncestrySingularMellinOperator.domain :=
  ⟨jointAncestryThetaDensitySeedL2, by
    change MemLp (fun x : ℝ => (Real.exp x : ℂ) *
      (jointAncestryThetaDensitySeedL2 : ℝ → ℂ) x) 2 volume
    refine (memLp_congr_ae ?_).mpr
      exp_mul_thetaCuspTailSecondDensityAtom_one_memLp
    filter_upwards [jointAncestryThetaDensitySeedL2_coeFn] with x hx
    rw [hx]⟩

theorem jointAncestrySingularMellinOperator_thetaDensitySeed_apply_ae :
    (jointAncestrySingularMellinOperator jointAncestryThetaDensitySeedDomain : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.exp x : ℂ) * thetaCuspTailSecondDensityAtom 1 x := by
  have h := maximalRealL2Mul_apply_ae volume Real.exp
    jointAncestryThetaDensitySeedDomain
  change (jointAncestrySingularMellinOperator
      jointAncestryThetaDensitySeedDomain : ℝ → ℂ) =ᵐ[volume]
    fun x => (Real.exp x : ℂ) *
      (jointAncestryThetaDensitySeedDomain : Lp ℂ 2 volume) x at h
  have hdomain :
      ((jointAncestryThetaDensitySeedDomain :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
        fun x => (thetaCuspTailSecondDensityAtom 1 x : ℂ) := by
    exact jointAncestryThetaDensitySeedL2_coeFn
  filter_upwards [h, hdomain] with x hx hseed
  exact hx.trans (by rw [hseed])

private theorem jointAncestry_eq_at_of_ae_eq_of_continuousAt
    {E : Type*} [NormedAddCommGroup E] {f g : ℝ → E} {x : ℝ}
    (hae : f =ᵐ[(volume : Measure ℝ)] g)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    f x = g x := by
  by_contra hne
  have hnorm : ContinuousAt (fun y => ‖f y - g y‖) x := (hf.sub hg).norm
  have hxpos : 0 < ‖f x - g x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hev : {y | 0 < ‖f y - g y‖} ∈ nhds x :=
    hnorm.eventually (Ioi_mem_nhds hxpos)
  rcases mem_nhds_iff.mp hev with ⟨s, hs, hsopen, hxs⟩
  have hsub : s ⊆ {y | f y ≠ g y} := by
    intro y hy heq
    exact (norm_pos_iff.mp (hs hy)) (sub_eq_zero.mpr heq)
  have hnull : (volume : Measure ℝ) {y | f y ≠ g y} = 0 := hae
  have hsnull : (volume : Measure ℝ) s = 0 := measure_mono_null hsub hnull
  exact (hsopen.measure_ne_zero (volume : Measure ℝ) ⟨x, hxs⟩) hsnull

theorem jointAncestryThetaDensitySeedL2_ne_zero :
    jointAncestryThetaDensitySeedL2 ≠ 0 := by
  intro hzero
  have hae : (fun x : ℝ => (thetaCuspTailSecondDensityAtom 1 x : ℂ)) =ᵐ[volume]
      fun _ => 0 := by
    have hseed := jointAncestryThetaDensitySeedL2_coeFn
    rw [hzero] at hseed
    filter_upwards [hseed, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hz
    exact hx.symm.trans hz
  have hcont : Continuous (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom 1 x : ℂ)) := by
    unfold thetaCuspTailSecondDensityAtom
    exact Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 2) 1 x).continuousAt))
  have hat0 := jointAncestry_eq_at_of_ae_eq_of_continuousAt (x := (0 : ℝ)) hae
    hcont.continuousAt continuousAt_const
  have hpos := thetaCuspTailSecondDensityAtom_pos
    (by omega : 0 < (1 : ℕ)) (show (0 : ℝ) ≤ 0 by rfl)
  norm_cast at hat0
  linarith

/-- Unscaled logarithmic translate carrying the `n`th arithmetic theta atom. -/
def jointAncestryThetaDensityTranslateDomain (n : ℕ) :
    jointAncestrySingularMellinOperator.domain :=
  ⟨MellinL2.additiveTranslationUnitary (Real.log n)
      jointAncestryThetaDensitySeedL2,
    jointAncestrySingularMellinOperator_translation_mem (Real.log n)
      jointAncestryThetaDensitySeedDomain⟩

/-- Actual `n`th completed-theta atom in the singular-Mellin domain. -/
def jointAncestryThetaDensityAtomDomain (n : ℕ) :
    jointAncestrySingularMellinOperator.domain :=
  (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
    jointAncestryThetaDensityTranslateDomain n

theorem jointAncestryThetaDensityAtomDomain_coeFn
    {n : ℕ} (hn : 0 < n) :
    ((jointAncestryThetaDensityAtomDomain n :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun x => (thetaCuspTailSecondDensityAtom n x : ℂ) := by
  have hseed := jointAncestryThetaDensitySeedL2_coeFn.comp_tendsto
    (MellinL2.realTranslation_measurePreserving (Real.log n)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [Lp.coeFn_smul
      (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      (jointAncestryThetaDensityTranslateDomain n :
        Lp ℂ 2 (volume : Measure ℝ)),
    translation_coeFn (Real.log n) jointAncestryThetaDensitySeedL2,
    hseed] with x hsmul htrans hseedx
  change ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      (jointAncestryThetaDensityTranslateDomain n :
        Lp ℂ 2 (volume : Measure ℝ))) x = _
  rw [hsmul]
  change (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (MellinL2.additiveTranslationUnitary (Real.log n)
        jointAncestryThetaDensitySeedL2 : ℝ → ℂ) x = _
  rw [htrans]
  change (jointAncestryThetaDensitySeedL2 : ℝ → ℂ) (x + Real.log n) =
      (thetaCuspTailSecondDensityAtom 1 (x + Real.log n) : ℂ) at hseedx
  rw [hseedx]
  rw [thetaCuspTailSecondDensityAtom_eq_rpow_mul_translate hn]
  norm_cast

/-- Each actual theta atom obeys exact closed singular-Mellin covariance.  Its arithmetic
index acts by the reciprocal multiplier, while critical half-density normalization remains
outside the translated operator image. -/
theorem jointAncestrySingularMellinOperator_thetaDensityAtom
    {n : ℕ} (hn : 0 < n) :
    jointAncestrySingularMellinOperator
        (jointAncestryThetaDensityAtomDomain n) =
      (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        ((((n : ℝ)⁻¹ : ℝ) : ℂ) •
          MellinL2.additiveTranslationUnitary (Real.log n)
            (jointAncestrySingularMellinOperator
              jointAncestryThetaDensitySeedDomain)) := by
  have hcov := jointAncestrySingularMellinOperator_covariance
    (Real.log n) jointAncestryThetaDensitySeedDomain
      (jointAncestryThetaDensityTranslateDomain n) rfl
  change jointAncestrySingularMellinOperator
      ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        jointAncestryThetaDensityTranslateDomain n) = _
  rw [LinearPMap.map_smul, hcov]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.exp_neg, Real.exp_log hnR]

theorem jointAncestryThetaDensityTranslate_eq_positiveMellinLift
    {n : ℕ} (hn : 0 < n) :
    (jointAncestryThetaDensityTranslateDomain n :
      Lp ℂ 2 (volume : Measure ℝ)) =
        jointAncestryPositiveMellinLift ((n : ℝ)⁻¹)
          jointAncestryThetaDensitySeedL2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold jointAncestryThetaDensityTranslateDomain jointAncestryPositiveMellinLift
  simp only [Real.log_inv, neg_neg]

theorem norm_jointAncestryThetaDensityAtomDomain {n : ℕ} (hn : 0 < n) :
    ‖(jointAncestryThetaDensityAtomDomain n :
        Lp ℂ 2 (volume : Measure ℝ))‖ =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * ‖jointAncestryThetaDensitySeedL2‖ := by
  change ‖((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      MellinL2.additiveTranslationUnitary (Real.log n)
        jointAncestryThetaDensitySeedL2)‖ = _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  congr 1
  exact (MellinL2.additiveTranslationUnitary (Real.log n)).norm_map
    jointAncestryThetaDensitySeedL2

/-- Coefficient faithfulness: distinct positive integer theta coefficients land in distinct
maximal-domain vectors.  Unitary translation preserves norm, while critical normalization
records the arithmetic index exactly. -/
theorem jointAncestryThetaDensityAtomDomain_injective :
    Function.Injective (fun n : ℕ+ =>
      (jointAncestryThetaDensityAtomDomain n :
        Lp ℂ 2 (volume : Measure ℝ))) := by
  intro m n hmn
  have hnorm := congrArg norm hmn
  rw [norm_jointAncestryThetaDensityAtomDomain m.pos,
    norm_jointAncestryThetaDensityAtomDomain n.pos] at hnorm
  have hseed : 0 < ‖jointAncestryThetaDensitySeedL2‖ :=
    norm_pos_iff.mpr jointAncestryThetaDensitySeedL2_ne_zero
  have hrpow : (m : ℝ) ^ (-(1 / 2 : ℝ)) =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    nlinarith
  have hmR : (0 : ℝ) < m := by positivity
  have hnR : (0 : ℝ) < n := by positivity
  rw [Real.rpow_def_of_pos hmR, Real.rpow_def_of_pos hnR] at hrpow
  have hlogmul := Real.exp_injective hrpow
  have hlog : Real.log (m : ℝ) = Real.log (n : ℝ) := by linarith
  have hcast : (m : ℝ) = (n : ℝ) := by
    have := congrArg Real.exp hlog
    simpa [Real.exp_log hmR, Real.exp_log hnR] using this
  exact Subtype.ext (Nat.cast_injective hcast)

/-- Exact one-sided completion seam for actual second-density theta atoms.  The full-line
singular-Mellin translate survives, but positive truncation creates the swept boundary current. -/
theorem positiveThetaCuspTailSecondDensityAtom_translation_seam
    {n : ℕ} (hn : 1 < n) (u : ℝ) :
    positiveLogTruncation (thetaCuspTailSecondDensityAtom n) u +
        (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          forwardTranslationBoundary (Real.log n)
            (thetaCuspTailSecondDensityAtom 1) u =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        positiveLogTruncation (thetaCuspTailSecondDensityAtom 1)
          (u + Real.log n) := by
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  let c : ℝ := (n : ℝ) ^ (-(1 / 2 : ℝ))
  let a : ℝ := Real.log n
  have hatom : positiveLogTruncation (thetaCuspTailSecondDensityAtom n) u =
      c * positiveLogTruncation
        (fun v => thetaCuspTailSecondDensityAtom 1 (v + a)) u := by
    by_cases hu : 0 < u
    · simp [positiveLogTruncation, hu, c, a,
        thetaCuspTailSecondDensityAtom_eq_rpow_mul_translate hn0]
    · simp [positiveLogTruncation, hu]
  have hcomm := positiveLogTruncation_translate_add_boundary
    (thetaCuspTailSecondDensityAtom 1) ha u
  rw [hatom]
  change c * positiveLogTruncation
        (fun v => thetaCuspTailSecondDensityAtom 1 (v + a)) u +
      c * forwardTranslationBoundary a (thetaCuspTailSecondDensityAtom 1) u =
        c * positiveLogTruncation (thetaCuspTailSecondDensityAtom 1) (u + a)
  calc
    c * positiveLogTruncation
          (fun v => thetaCuspTailSecondDensityAtom 1 (v + a)) u +
        c * forwardTranslationBoundary a (thetaCuspTailSecondDensityAtom 1) u =
      c * (positiveLogTruncation
          (fun v => thetaCuspTailSecondDensityAtom 1 (v + a)) u +
        forwardTranslationBoundary a (thetaCuspTailSecondDensityAtom 1) u) := by ring
    _ = c * positiveLogTruncation (thetaCuspTailSecondDensityAtom 1) (u + a) := by
      rw [hcomm]

/-- The swept completion current is genuinely nonzero for every nontrivial arithmetic translate. -/
theorem forwardTranslationBoundary_thetaDensityAtom_one_pos
    {n : ℕ} (hn : 1 < n) :
    0 < forwardTranslationBoundary (Real.log n)
      (thetaCuspTailSecondDensityAtom 1) (-(Real.log n) / 2) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hmem : -(Real.log (n : ℝ)) / 2 ∈ Ioc (-Real.log n) 0 := by
    constructor <;> linarith
  rw [forwardTranslationBoundary, Set.indicator_of_mem hmem]
  apply thetaCuspTailSecondDensityAtom_pos (by omega : 0 < (1 : ℕ))
  linarith

/-- Therefore positive-half completion cannot identify the actual theta atom with its bare
full-line Mellin translate: the nonzero boundary current is mandatory. -/
theorem positiveThetaCuspTailSecondDensityAtom_ne_bare_translate
    {n : ℕ} (hn : 1 < n) :
    positiveLogTruncation (thetaCuspTailSecondDensityAtom n) (-(Real.log n) / 2) ≠
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        positiveLogTruncation (thetaCuspTailSecondDensityAtom 1)
          (-(Real.log n) / 2 + Real.log n) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hleft : positiveLogTruncation (thetaCuspTailSecondDensityAtom n)
      (-(Real.log n) / 2) = 0 := by
    simp [positiveLogTruncation, not_lt.mpr (by linarith : -(Real.log (n : ℝ)) / 2 ≤ 0)]
  have hrightSeed : 0 < thetaCuspTailSecondDensityAtom 1
      (-(Real.log n) / 2 + Real.log n) := by
    apply thetaCuspTailSecondDensityAtom_pos (by omega : 0 < (1 : ℕ))
    linarith
  have hshift : 0 < -(Real.log (n : ℝ)) / 2 + Real.log n := by linarith
  rw [hleft]
  have hc : 0 < (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  rw [positiveLogTruncation, Set.indicator_of_mem (show
    -(Real.log (n : ℝ)) / 2 + Real.log n ∈ Ioi 0 by exact hshift)]
  exact ne_of_lt (mul_pos hc hrightSeed)

/-- The canonical unrenormalized completed density is excluded from full-line `L²`: its exact
theta reflection law contains a half-exponential defect.  Hence atomwise maximal-domain landing
cannot be summed there without first removing the reflection mode. -/
theorem not_memLp_two_thetaCuspTailSecondDensity_fullLine :
    ¬ MemLp (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ)) 2 volume := by
  intro hL2
  have hreflected := hL2.comp_measurePreserving
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hreflected' : MemLp
      (fun x : ℝ => (thetaCuspTailSecondDensity (-x) : ℂ)) 2 volume := by
    simpa [Function.comp_def] using hreflected
  have hint : Integrable (fun x : ℝ =>
      ‖(thetaCuspTailSecondDensity (-x) : ℂ)‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hreflected'.aestronglyMeasurable).1 hreflected'
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 4) := by
    refine hint.integrableOn.mono' aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := lt_trans (by norm_num) hx
    have hdensityPos : 0 < thetaCuspTailSecondDensity x :=
      thetaCuspTailSecondDensity_pos hx0
    have hexpLower : 3 ≤ Real.exp (x / 2) := by
      have hbase := Real.add_one_le_exp (x / 2)
      have hx4 : (4 : ℝ) < x := hx
      exact (show (3 : ℝ) ≤ x / 2 + 1 by nlinarith).trans hbase
    have hexpUpper : Real.exp (-x / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have hreflection : 1 ≤ thetaCuspReflectionMode x := by
      rw [thetaCuspReflectionMode]
      linarith
    have hdensity : 1 ≤ thetaCuspTailSecondDensity (-x) := by
      rw [thetaCuspTailSecondDensity_neg]
      linarith
    rw [show ‖(1 : ℝ)‖ = 1 by norm_num]
    have hnorm : 1 ≤ ‖(thetaCuspTailSecondDensity (-x) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hdensity)]
      exact hdensity
    nlinarith
  simp [integrableOn_const_iff, Real.volume_Ioi] at hone

/-- Arbitrary exponential-decay constant for the even, reflection-renormalized theta source. -/
def thetaCuspFullSourceNatExpConstant (p : ℕ) : ℝ :=
  thetaCuspTailDerivativeNatExpConstant 2 p +
    (1 / 4 : ℝ) * thetaCuspTailDerivativeNatExpConstant 0 p

theorem thetaCuspFullSourceNatExpConstant_nonneg (p : ℕ) :
    0 ≤ thetaCuspFullSourceNatExpConstant p := by
  unfold thetaCuspFullSourceNatExpConstant
  have hnat (m q : ℕ) : 0 ≤ thetaCuspTailDerivativeNatExpConstant m q := by
    unfold thetaCuspTailDerivativeNatExpConstant
    dsimp only
    refine mul_nonneg (mul_nonneg (thetaCuspCoeffMass_nonneg _) (Real.exp_pos _).le) ?_
    exact tsum_nonneg fun n =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le
  exact add_nonneg (hnat 2 p)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (hnat 0 p))

/-- After exact reflection-mode subtraction, completed theta source has arbitrary exponential
decay on positive logarithmic ray. -/
theorem abs_thetaCuspFullSource_le_nat_exp_neg
    (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |thetaCuspFullSource x| ≤
      thetaCuspFullSourceNatExpConstant p * Real.exp (-(p : ℝ) * x) := by
  rw [thetaCuspFullSource_eq_tail_second_sub]
  calc
    |thetaCuspTailDerivative 2 x -
        (1 / 4 : ℝ) * thetaCuspTailDerivative 0 x| ≤
      |thetaCuspTailDerivative 2 x| +
        |(1 / 4 : ℝ) * thetaCuspTailDerivative 0 x| := abs_sub _ _
    _ = |thetaCuspTailDerivative 2 x| +
        (1 / 4 : ℝ) * |thetaCuspTailDerivative 0 x| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    _ ≤ thetaCuspTailDerivativeNatExpConstant 2 p * Real.exp (-(p : ℝ) * x) +
        (1 / 4 : ℝ) *
          (thetaCuspTailDerivativeNatExpConstant 0 p * Real.exp (-(p : ℝ) * x)) := by
      gcongr
      · exact abs_thetaCuspTailDerivative_le_nat_exp_neg 2 p hx
      · exact abs_thetaCuspTailDerivative_le_nat_exp_neg 0 p hx
    _ = thetaCuspFullSourceNatExpConstant p * Real.exp (-(p : ℝ) * x) := by
      unfold thetaCuspFullSourceNatExpConstant
      ring

private theorem thetaCuspFullSource_expWeight_memLp (r : ℕ) :
    MemLp (fun x : ℝ => ((Real.exp ((r : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ))
      2 volume := by
  let Cneg : ℝ := thetaCuspFullSourceNatExpConstant 1
  let Cpos : ℝ := thetaCuspFullSourceNatExpConstant (r + 1)
  have hsourceCont : Continuous thetaCuspFullSource := by
    rw [show thetaCuspFullSource = fun x =>
        thetaCuspTailDerivative 2 x - (1 / 4 : ℝ) * thetaCuspTailDerivative 0 x by
      funext x
      exact thetaCuspFullSource_eq_tail_second_sub x]
    exact (differentiable_thetaCuspTailDerivative 2).continuous.sub
      (continuous_const.mul (differentiable_thetaCuspTailDerivative 0).continuous)
  have hcont : Continuous (fun x : ℝ =>
      ((Real.exp ((r : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hsourceCont)
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  apply IntegrableOn.union
  · have hdom : IntegrableOn (fun x : ℝ => Cneg ^ 2 * Real.exp (2 * x)) (Iic 0) :=
      (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 2) 0).const_mul (Cneg ^ 2)
    refine Integrable.mono' hdom (hcont.norm.pow 2).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Iic).2
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hrx : Real.exp ((r : ℝ) * x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg r) hx
    have hx0 : x ≤ 0 := hx
    have hsource := abs_thetaCuspFullSource_le_nat_exp_neg 1
      (show 0 ≤ -x by linarith)
    rw [thetaCuspFullSource_neg] at hsource
    have hweighted : Real.exp ((r : ℝ) * x) * |thetaCuspFullSource x| ≤
        Cneg * Real.exp x := by
      dsimp [Cneg]
      calc
        Real.exp ((r : ℝ) * x) * |thetaCuspFullSource x| ≤
            1 * |thetaCuspFullSource x| := by gcongr
        _ ≤ thetaCuspFullSourceNatExpConstant 1 * Real.exp x := by
          simpa using hsource
    change |‖((Real.exp ((r : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ)‖ ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    calc
      (Real.exp ((r : ℝ) * x) * |thetaCuspFullSource x|) ^ 2 ≤
          (Cneg * Real.exp x) ^ 2 := pow_le_pow_left₀ (by positivity) hweighted 2
      _ = Cneg ^ 2 * Real.exp (2 * x) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num
  · have hdom : IntegrableOn (fun x : ℝ => Cpos ^ 2 * Real.exp (-2 * x)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).const_mul (Cpos ^ 2)
    refine Integrable.mono' hdom (hcont.norm.pow 2).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hsource := abs_thetaCuspFullSource_le_nat_exp_neg (r + 1) hx.le
    have hweighted : Real.exp ((r : ℝ) * x) * |thetaCuspFullSource x| ≤
        Cpos * Real.exp (-x) := by
      dsimp [Cpos]
      calc
        Real.exp ((r : ℝ) * x) * |thetaCuspFullSource x| ≤
            Real.exp ((r : ℝ) * x) *
              (thetaCuspFullSourceNatExpConstant (r + 1) *
                Real.exp (-((r + 1 : ℕ) : ℝ) * x)) := by gcongr
        _ = thetaCuspFullSourceNatExpConstant (r + 1) * Real.exp (-x) := by
          rw [show Real.exp ((r : ℝ) * x) *
              (thetaCuspFullSourceNatExpConstant (r + 1) *
                Real.exp (-((r + 1 : ℕ) : ℝ) * x)) =
            thetaCuspFullSourceNatExpConstant (r + 1) *
              (Real.exp ((r : ℝ) * x) *
                Real.exp (-((r + 1 : ℕ) : ℝ) * x)) by ring,
            ← Real.exp_add]
          congr 1
          push_cast
          ring_nf
    change |‖((Real.exp ((r : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ)‖ ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    calc
      (Real.exp ((r : ℝ) * x) * |thetaCuspFullSource x|) ^ 2 ≤
          (Cpos * Real.exp (-x)) ^ 2 := pow_le_pow_left₀ (by positivity) hweighted 2
      _ = Cpos ^ 2 * Real.exp (-2 * x) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        ring_nf

theorem thetaCuspFullSource_memLp_two :
    MemLp (fun x : ℝ => (thetaCuspFullSource x : ℂ)) 2 volume := by
  simpa using thetaCuspFullSource_expWeight_memLp 0

theorem exp_mul_thetaCuspFullSource_memLp_two :
    MemLp (fun x : ℝ => (Real.exp x : ℂ) * thetaCuspFullSource x) 2 volume := by
  simpa using thetaCuspFullSource_expWeight_memLp 1

/-- Strongest survivor after the full-density no-go: exact reflection renormalization
`rho - rawTail = 4 Phi` lands the completed even theta source in the maximal Mellin domain. -/
def jointAncestryCompletedThetaSourceL2 : Lp ℂ 2 (volume : Measure ℝ) :=
  thetaCuspFullSource_memLp_two.toLp (fun x : ℝ => (thetaCuspFullSource x : ℂ))

theorem jointAncestryCompletedThetaSourceL2_coeFn :
    (jointAncestryCompletedThetaSourceL2 : ℝ → ℂ) =ᵐ[volume]
      fun x => (thetaCuspFullSource x : ℂ) :=
  MemLp.coeFn_toLp thetaCuspFullSource_memLp_two

def jointAncestryCompletedThetaSourceDomain :
    jointAncestrySingularMellinOperator.domain :=
  ⟨jointAncestryCompletedThetaSourceL2, by
    change MemLp (fun x : ℝ => (Real.exp x : ℂ) *
      (jointAncestryCompletedThetaSourceL2 : ℝ → ℂ) x) 2 volume
    refine (memLp_congr_ae ?_).mpr exp_mul_thetaCuspFullSource_memLp_two
    filter_upwards [jointAncestryCompletedThetaSourceL2_coeFn] with x hx
    rw [hx]⟩

theorem jointAncestryCompletedThetaSource_eq_renormalizedDensity (x : ℝ) :
    4 * thetaCuspFullSource x =
      thetaCuspTailSecondDensity x - thetaCuspTailDerivative 0 x := by
  rw [thetaCuspTailSecondDensity_eq_tail_add_four_fullSource]
  ring

/-- Direct completed-Xi comparison for the surviving maximal-domain vector.  This is the literal
completed theta source, not an abstract carrier: its positive-half cosine current is `XiC`. -/
theorem XiC_ofReal_eq_jointAncestryCompletedThetaSourceL2_cosine (t : ℝ) :
    XiC (t : ℂ) =
      (2 : ℂ) * ∫ x : ℝ in Ioi 0,
        jointAncestryCompletedThetaSourceL2 x * (Real.cos (t * x) : ℂ) := by
  rw [XiC_ofReal_eq_two_mul_thetaCuspCosine]
  rw [Complex.ofReal_mul]
  norm_num only [Complex.ofReal_ofNat]
  congr 1
  calc
    (((∫ x : ℝ in Ioi 0,
        thetaCuspFullSource x * Real.cos (t * x) : ℝ)) : ℂ) =
      ∫ x : ℝ in Ioi 0,
        ((thetaCuspFullSource x * Real.cos (t * x) : ℝ) : ℂ) :=
          integral_ofReal.symm
    _ = ∫ x : ℝ in Ioi 0,
        jointAncestryCompletedThetaSourceL2 x * (Real.cos (t * x) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [jointAncestryCompletedThetaSourceL2_coeFn.restrict] with x hx
      rw [hx]
      rw [Complex.ofReal_mul]

end

end RHTower
