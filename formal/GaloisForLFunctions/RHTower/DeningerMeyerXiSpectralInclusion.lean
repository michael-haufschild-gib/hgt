import GaloisForLFunctions.RHTower.DeningerMeyerGeneralizedZeroJetDescent
import GaloisForLFunctions.RHTower.DeningerMeyerDilationFlow
import GaloisForLFunctions.RHTower.DeningerArithmeticGlobalDivision
import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Algebra.Polynomial.Roots

/-!
# Literal Meyer-to-Xi spectral inclusion

This file closes the one-way spectral inclusion from every actual Xi divisor
into the dual flow of the literal all-weight Meyer quotient.

The centered faithful Mellin transform maps the literal Poisson range into
the actual compact-open Xi-multiplication range.  Global analytic division
therefore gives a canonical comparison map and identifies its injectivity
with one precise inverse-Mellin spectral-synthesis theorem.

More importantly for divisor inclusion, smooth compactly supported profiles
separate every finite Mellin jet packet.  At an Xi support point, zeta and
completed Xi have the same analytic order, so all jets below the full
multiplicity descend through the genuine Poisson quotient.  They remain
linearly independent and obey the exact lower-triangular binomial flow law.
Thus every Xi divisor occurs with its full analytic multiplicity; the zeroth
jet is a nonzero eigenfunctional with character `c ↦ exp(c rho)`.

All results are unconditional.  No RH, simplicity, divisor-indexed carrier,
spectral realization premise, positivity premise, or numerical computation
is used.
-/

open Complex Filter Function Set Topology
open scoped Classical

namespace RHTower

noncomputable section

/-- Every smooth compactly supported log profile belongs to the all-weight target. -/
theorem deningerMeyerStrongLogDecay_of_hasCompactSupport
    {g : ℝ → ℂ}
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgCompact : HasCompactSupport g) :
    DeningerMeyerStrongLogDecay g where
  smooth := hg
  decayTop := by
    intro n a
    have hnCompact :
        HasCompactSupport (iteratedDeriv n g) := by
      induction n with
      | zero =>
          simpa only [iteratedDeriv_zero] using hgCompact
      | succ n ih =>
          rw [iteratedDeriv_succ]
          exact ih.deriv
    have hnZero := hnCompact
    rw [hasCompactSupport_iff_eventuallyEq,
      Filter.coclosedCompact_eq_cocompact] at hnZero
    exact
      (hnZero.filter_mono _root_.atTop_le_cocompact).trans_isBigO
        (Asymptotics.isBigO_zero _ _)
  decayBot := by
    intro n b
    have hnCompact :
        HasCompactSupport (iteratedDeriv n g) := by
      induction n with
      | zero =>
          simpa only [iteratedDeriv_zero] using hgCompact
      | succ n ih =>
          rw [iteratedDeriv_succ]
          exact ih.deriv
    have hnZero := hnCompact
    rw [hasCompactSupport_iff_eventuallyEq,
      Filter.coclosedCompact_eq_cocompact] at hnZero
    exact
      (hnZero.filter_mono _root_.atBot_le_cocompact).trans_isBigO
        (Asymptotics.isBigO_zero _ _)

/--
At every spectral point, the finite logarithmic Mellin jet packet is linearly
independent on the exact all-weight target.  Compactly supported smooth test
profiles reduce a putative relation to a polynomial-exponential distribution;
the distributional fundamental lemma then forces the polynomial to vanish.
-/
theorem deningerMeyerStrongLogMellinJetLM_linearIndependent
    (rho : ℂ) (m : ℕ) :
    LinearIndependent ℂ
      (fun k : Fin m =>
        deningerMeyerStrongLogMellinJetLM k rho) := by
  rw [Fintype.linearIndependent_iff]
  intro c hrelation i
  let p : Polynomial ℂ :=
    ∑ k : Fin m, Polynomial.monomial k (c k)
  let F : ℝ → ℂ := fun t =>
    Complex.exp (rho * (t : ℂ)) * p.eval (t : ℂ)
  have hFcont : Continuous F := by
    exact
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).mul
        ((Polynomial.continuous p).comp Complex.continuous_ofReal)
  have hFzeroAE : ∀ᵐ t ∂MeasureTheory.volume, F t = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      hFcont.locallyIntegrable
    intro phi hphi hphiCompact
    let phiC : ℝ → ℂ := Complex.ofRealCLM ∘ phi
    have hphiCSmooth :
        ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) phiC :=
      Complex.ofRealCLM.contDiff.comp hphi
    have hphiCCompact : HasCompactSupport phiC :=
      hphiCompact.comp_left rfl
    let g : DeningerMeyerStrongLogTarget :=
      ⟨phiC,
        deningerMeyerStrongLogDecay_of_hasCompactSupport
          hphiCSmooth hphiCCompact⟩
    have hEval :=
      congrArg
        (fun L :
            DeningerMeyerStrongLogTarget →ₗ[ℂ] ℂ =>
          L g) hrelation
    have hEval' :
        (∑ k : Fin m,
          c k *
            iteratedDeriv k
              (deningerMeyerStrongLogMellin g) rho) = 0 := by
      simpa only [
        LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, LinearMap.zero_apply,
        deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
        using hEval
    have hsum :
        (∑ k : Fin m,
          c k *
            ∫ t : ℝ,
              deningerMeyerStrongLogMellinJet
                k rho g t) = 0 := by
      calc
        _ = ∑ k : Fin m,
              c k *
                iteratedDeriv k
                  (deningerMeyerStrongLogMellin g) rho := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [
              iteratedDeriv_deningerMeyerStrongLogMellin_eq_integral_jet
                g.property]
        _ = 0 := hEval'
    calc
      (∫ t : ℝ, phi t • F t) =
          ∫ t : ℝ,
            ∑ k : Fin m,
              c k *
                deningerMeyerStrongLogMellinJet
                  k rho g t := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        simp only [F, p, phiC, g,
          deningerMeyerStrongLogMellinJet,
          Function.comp_apply, Complex.ofRealCLM_apply,
          Polynomial.eval_finsetSum,
          Polynomial.eval_monomial, Complex.real_smul]
        rw [← mul_assoc, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ = ∑ k : Fin m,
            ∫ t : ℝ,
              c k *
                deningerMeyerStrongLogMellinJet
                  k rho g t := by
        apply MeasureTheory.integral_finsetSum
        intro k _hk
        exact
          (integrable_deningerMeyerStrongLogMellinJet
            g.property k rho).const_mul (c k)
      _ = ∑ k : Fin m,
            c k *
              ∫ t : ℝ,
                deningerMeyerStrongLogMellinJet
                  k rho g t := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [MeasureTheory.integral_const_mul]
      _ = 0 := hsum
  have hFzero : F = 0 :=
    (Continuous.ae_eq_iff_eq MeasureTheory.volume
      hFcont continuous_zero).mp hFzeroAE
  have hpRoots :
      Set.range (fun t : ℝ => (t : ℂ)) ⊆
        {z : ℂ | p.IsRoot z} := by
    rintro _ ⟨t, rfl⟩
    change p.eval (t : ℂ) = 0
    have ht := congrFun hFzero t
    change
      Complex.exp (rho * (t : ℂ)) * p.eval (t : ℂ) = 0 at ht
    exact (mul_eq_zero.mp ht).resolve_left (Complex.exp_ne_zero _)
  have hpInfinite :
      Set.Infinite {z : ℂ | p.IsRoot z} :=
    (Set.infinite_range_of_injective Complex.ofReal_injective).mono hpRoots
  have hpZero : p = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot p hpInfinite
  have hcoeff :=
    congrArg (fun q : Polynomial ℂ => q.coeff i) hpZero
  have hpCoeff : p.coeff i = c i := by
    change
      (∑ k : Fin m,
        Polynomial.monomial k (c k)).coeff i = c i
    change
      (Polynomial.lcoeff ℂ i)
          (∑ k : Fin m,
            Polynomial.monomial k (c k)) = c i
    rw [map_sum]
    change
      (∑ k : Fin m,
        (Polynomial.monomial k (c k)).coeff i) = c i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      simp only [Polynomial.coeff_monomial]
      rw [if_neg]
      intro hval
      exact hji (Fin.ext hval)
    · simp
  rw [hpCoeff] at hcoeff
  simpa using hcoeff

/-- Centered Meyer Mellin transform is entire. -/
theorem differentiable_deningerMeyerCenteredMellin
    (g : DeningerMeyerStrongLogTarget) :
    Differentiable ℂ
      (fun z : ℂ =>
        deningerMeyerStrongLogMellin g
          (1 / 2 + Complex.I * z)) := by
  intro z
  have houter :
      DifferentiableAt ℂ
        (deningerMeyerStrongLogMellin (g : ℝ → ℂ))
        (1 / 2 + Complex.I * z) :=
    differentiable_deningerMeyerStrongLogMellin
      g.property _
  have hinner :
      DifferentiableAt ℂ
        (fun w : ℂ => 1 / 2 + Complex.I * w) z := by
    fun_prop
  exact
    DifferentiableAt.comp
      (f := fun w : ℂ => 1 / 2 + Complex.I * w)
      (g := deningerMeyerStrongLogMellin (g : ℝ → ℂ))
      z houter hinner

/-- Center the faithful Meyer Mellin transform at the functional-equation fixed point. -/
def deningerMeyerCenteredMellin
    (g : DeningerMeyerStrongLogTarget) :
    DeningerCompactOpenEntire :=
  ⟨⟨fun z =>
      deningerMeyerStrongLogMellin g
        (1 / 2 + Complex.I * z),
    (differentiable_deningerMeyerCenteredMellin g).continuous⟩,
  differentiable_deningerMeyerCenteredMellin g⟩

@[simp]
theorem deningerMeyerCenteredMellin_apply
    (g : DeningerMeyerStrongLogTarget) (z : ℂ) :
    deningerMeyerCenteredMellin g z =
      deningerMeyerStrongLogMellin g
        (1 / 2 + Complex.I * z) :=
  rfl

/-- Algebraic centered Mellin transform into the compact-open entire source. -/
def deningerMeyerCenteredMellinLM :
    DeningerMeyerStrongLogTarget →ₗ[ℂ]
      DeningerCompactOpenEntire where
  toFun := deningerMeyerCenteredMellin
  map_add' g h := by
    ext z
    simp only [DeningerCompactOpenEntire.coe_add]
    change
      deningerMeyerStrongLogMellin (g + h)
          (1 / 2 + Complex.I * z) =
        deningerMeyerStrongLogMellin g
            (1 / 2 + Complex.I * z) +
          deningerMeyerStrongLogMellin h
            (1 / 2 + Complex.I * z)
    exact
      (deningerMeyerStrongLogMellinLM
        (1 / 2 + Complex.I * z)).map_add g h
  map_smul' c g := by
    ext z
    simp only [DeningerCompactOpenEntire.coe_smul]
    change
      deningerMeyerStrongLogMellin (c • g)
          (1 / 2 + Complex.I * z) =
        c • deningerMeyerStrongLogMellin g
          (1 / 2 + Complex.I * z)
    exact
      (deningerMeyerStrongLogMellinLM
        (1 / 2 + Complex.I * z)).map_smul c g

theorem iteratedDeriv_deningerMeyerCenteredMellin
    (g : DeningerMeyerStrongLogTarget) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (deningerMeyerCenteredMellin g : ℂ → ℂ) z =
      Complex.I ^ k *
        iteratedDeriv k
          (deningerMeyerStrongLogMellin g)
          (1 / 2 + Complex.I * z) := by
  have hF :
      ContDiff ℂ ⊤ (deningerMeyerStrongLogMellin g) :=
    (differentiable_deningerMeyerStrongLogMellin
      g.property).contDiff
  have hshift :
      ContDiff ℂ (k : WithTop ℕ∞)
        (fun u : ℂ =>
          deningerMeyerStrongLogMellin g (1 / 2 + u)) :=
    (hF.comp (contDiff_const.add contDiff_id)).of_le
      (by simp)
  change
    iteratedDeriv k
        (fun w : ℂ =>
          deningerMeyerStrongLogMellin g
            (1 / 2 + Complex.I * w)) z =
      _
  change
    iteratedDeriv k
        (fun w : ℂ =>
          (fun u : ℂ =>
            deningerMeyerStrongLogMellin g (1 / 2 + u))
              (Complex.I * w)) z =
      _
  rw [congrFun
      (iteratedDeriv_comp_const_mul
        (n := k)
        (f := fun u : ℂ =>
          deningerMeyerStrongLogMellin g (1 / 2 + u))
        hshift Complex.I) z]
  rw [congrFun
      (iteratedDeriv_comp_const_add
        k (deningerMeyerStrongLogMellin g) (1 / 2)) (Complex.I * z)]

/-- Undo centered Xi spectral coordinates. -/
theorem deningerMeyer_uncenter_xiSpectralPointSupport
    (rho : XiDivisorSupport) :
    1 / 2 + Complex.I * xiSpectralPointSupport rho =
      (rho : ℂ) := by
  simp only [xiSpectralPointSupport]
  have hI : Complex.I * (-Complex.I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I]
    ring
  calc
    1 / 2 + Complex.I * (((rho : ℂ) - 1 / 2) * -Complex.I) =
        1 / 2 + ((rho : ℂ) - 1 / 2) *
          (Complex.I * -Complex.I) := by ring
    _ = (rho : ℂ) := by rw [hI]; ring

/--
Every zeta derivative below the actual Xi divisor multiplicity vanishes.
This transfers completed-Xi multiplicity to the literal zeta factor in the
open critical strip.
-/
theorem iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity
    (rho : XiDivisorSupport) {j : ℕ}
    (hj : j < xiSupportMultiplicity rho) :
    iteratedDeriv j riemannZeta (rho : ℂ) = 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hne1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have horder :
      analyticOrderAt xi (rho : ℂ) =
        analyticOrderAt riemannZeta (rho : ℂ) :=
    xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip
  have hzetaFinite :
      analyticOrderAt riemannZeta (rho : ℂ) ≠ ⊤ := by
    rw [← horder]
    exact xi_orderAt_ne_top (rho : ℂ)
  have hm :
      ((xiSupportMultiplicity rho : ℕ) : ℕ∞) =
        analyticOrderAt riemannZeta (rho : ℂ) := by
    rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat, horder]
    exact ENat.coe_toNat hzetaFinite
  have hjOrder :
      ((j + 1 : ℕ) : ℕ∞) ≤
        analyticOrderAt riemannZeta (rho : ℂ) := by
    rw [← hm]
    exact_mod_cast hj
  have hzero :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticOn_riemannZeta (rho : ℂ) hne1)).mp hjOrder
  exact hzero j (by omega)

/-- Every genuine Meyer Poisson boundary has zero full Xi jet product. -/
theorem deningerMeyerCenteredMellin_boundary_allJets_zero
    (f : DeningerMeyerCap) :
    deningerCompactOpenAllJets
        (deningerMeyerCenteredMellin
          (deningerMeyerStrongLogSumLM f)) = 0 := by
  funext rho k
  rw [deningerCompactOpenAllJets_apply,
    iteratedDeriv_deningerMeyerCenteredMellin,
    deningerMeyer_uncenter_xiSpectralPointSupport]
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hne1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [deningerMeyerStrongLogMellin_boundary_iteratedDeriv_zero
    f hstrip.1 hne1 k]
  · simp
  · intro j hj
    exact
      iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity
        rho (lt_of_le_of_lt hj k.isLt)

/-- Genuine Meyer Poisson boundaries become actual compact-open Xi coboundaries. -/
theorem deningerMeyerCenteredMellin_boundary_mem_XiRange
    (f : DeningerMeyerCap) :
    deningerMeyerCenteredMellin
        (deningerMeyerStrongLogSumLM f) ∈
      deningerCompactOpenXiRange := by
  rw [deningerCompactOpenXiRange_eq_allJets_ker]
  exact deningerMeyerCenteredMellin_boundary_allJets_zero f

/--
Canonical comparison from the literal Meyer Poisson quotient to compact-open
Xi cohomology.  Existence is unconditional: global Xi division converts every
genuine Poisson boundary into an Xi coboundary.
-/
def deningerMeyerCompactOpenXiComparison :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      DeningerArithmeticCompactOpenH1 :=
  (LinearMap.range deningerMeyerStrongLogSumLM).liftQ
    (deningerArithmeticCompactOpenH1Class.toLinearMap.comp
      deningerMeyerCenteredMellinLM)
    (by
      rintro _ ⟨f, rfl⟩
      rw [LinearMap.mem_ker]
      change
        deningerArithmeticCompactOpenH1Class
            (deningerMeyerCenteredMellin
              (deningerMeyerStrongLogSumLM f)) = 0
      rw [deningerArithmeticCompactOpenH1Class_apply,
        DeningerCompactOpenQuotient.mk_eq_zero_iff_mem]
      exact deningerMeyerCenteredMellin_boundary_mem_XiRange f)

@[simp]
theorem deningerMeyerCompactOpenXiComparison_mk
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerCompactOpenXiComparison
        (Submodule.Quotient.mk g) =
      deningerArithmeticCompactOpenH1Class
        (deningerMeyerCenteredMellin g) :=
  rfl

/--
Exact kernel test on a Meyer representative: comparison kills its class
precisely when every multiplicity-bounded Xi jet of its centered Mellin
transform vanishes.
-/
theorem deningerMeyerCompactOpenXiComparison_mk_eq_zero_iff
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerCompactOpenXiComparison
          (Submodule.Quotient.mk g) = 0 ↔
      deningerCompactOpenAllJets
          (deningerMeyerCenteredMellin g) = 0 := by
  rw [deningerMeyerCompactOpenXiComparison_mk,
    deningerArithmeticCompactOpenH1Class_apply,
    DeningerCompactOpenQuotient.mk_eq_zero_iff_mem,
    deningerCompactOpenXiRange_eq_allJets_ker]
  rfl

/--
The remaining injectivity problem, stated without proxy spaces: Xi-divisibility
of the centered Mellin transform must force membership in the literal Poisson
range.
-/
def DeningerMeyerXiSpectralSynthesis : Prop :=
  ∀ g : DeningerMeyerStrongLogTarget,
    deningerCompactOpenAllJets
        (deningerMeyerCenteredMellin g) = 0 →
      g ∈ LinearMap.range deningerMeyerStrongLogSumLM

/--
Exact frontier theorem: literal Meyer-to-Xi comparison is injective if and
only if source-native Xi spectral synthesis holds.
-/
theorem deningerMeyerCompactOpenXiComparison_injective_iff :
    Function.Injective deningerMeyerCompactOpenXiComparison ↔
      DeningerMeyerXiSpectralSynthesis := by
  constructor
  · intro hinj g hjets
    have hzero :
        deningerMeyerCompactOpenXiComparison
            (Submodule.Quotient.mk g) = 0 :=
      (deningerMeyerCompactOpenXiComparison_mk_eq_zero_iff g).2
        hjets
    have hclass :
        Submodule.Quotient.mk g =
          (0 : DeningerMeyerStrongLogCohomology) := by
      apply hinj
      simpa using hzero
    exact
      (Submodule.Quotient.mk_eq_zero
        (LinearMap.range deningerMeyerStrongLogSumLM)).mp hclass
  · intro hsynth
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm
    · intro u hu
      rcases
          (Submodule.Quotient.mk_surjective
            (LinearMap.range deningerMeyerStrongLogSumLM)) u with
        ⟨g, rfl⟩
      rw [LinearMap.mem_ker] at hu
      have hjets :=
        (deningerMeyerCompactOpenXiComparison_mk_eq_zero_iff g).1 hu
      exact
        ((Submodule.Quotient.mk_eq_zero
            (LinearMap.range deningerMeyerStrongLogSumLM)).mpr
          (hsynth g hjets)) ▸ Submodule.zero_mem _
    · exact bot_le

/-- An actual Xi divisor point cannot equal zeta's pole. -/
theorem xiDivisorSupport_ne_one (rho : XiDivisorSupport) :
    (rho : ℂ) ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  norm_num at hre
  linarith

/--
Canonical generalized Meyer eigenfunctional attached to one actual Xi
divisor jet.  Zeta multiplicity supplies the boundary-annihilation proof.
-/
def deningerMeyerXiSupportJetEvaluationLM
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  deningerMeyerZetaZeroJetEvaluationLM
    (rho : ℂ)
    (xi_divisor_support_re_mem_open_unit rho).1
    (xiDivisorSupport_ne_one rho)
    k
    (fun _j hj =>
      iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity
        rho (lt_of_le_of_lt hj k.isLt))

@[simp]
theorem deningerMeyerXiSupportJetEvaluationLM_mk
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho)
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerXiSupportJetEvaluationLM rho k
        (Submodule.Quotient.mk g) =
      deningerMeyerStrongLogMellinJetLM k (rho : ℂ) g :=
  rfl

/--
Every actual Xi divisor enters literal Meyer cohomology with its full analytic
multiplicity: all generalized jet functionals below the multiplicity are
linearly independent.
-/
theorem deningerMeyerXiSupportJetEvaluationLM_linearIndependent
    (rho : XiDivisorSupport) :
    LinearIndependent ℂ
      (deningerMeyerXiSupportJetEvaluationLM rho) := by
  rw [Fintype.linearIndependent_iff]
  intro c hrelation i
  have htarget :
      (∑ k : DeningerArithmeticJetIndex rho,
        c k •
          deningerMeyerStrongLogMellinJetLM k (rho : ℂ)) = 0 := by
    ext g
    have hEval :=
      congrArg
        (fun L :
            DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ =>
          L (Submodule.Quotient.mk g)) hrelation
    simpa only [
      LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply,
      deningerMeyerXiSupportJetEvaluationLM_mk] using hEval
  exact
    (Fintype.linearIndependent_iff.mp
      (deningerMeyerStrongLogMellinJetLM_linearIndependent
        (rho : ℂ) (xiSupportMultiplicity rho))
      c htarget i)

/--
Exact confluent flow law on logarithmic Mellin jets.  Translation is not
diagonal at a multiple zero: the full lower-jet triangular block is forced.
-/
theorem deningerMeyerStrongLogMellinJetLM_flow
    (c : ℝ) (g : DeningerMeyerStrongLogTarget)
    (k : ℕ) (rho : ℂ) :
    deningerMeyerStrongLogMellinJetLM k rho
        (deningerMeyerStrongLogFlow c g) =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) *
          (c : ℂ) ^ i *
          Complex.exp ((c : ℂ) * rho) *
          deningerMeyerStrongLogMellinJetLM (k - i) rho g := by
  rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
  have hfun :
      deningerMeyerStrongLogMellin
          (deningerMeyerStrongLogFlow c g) =
        fun s : ℂ =>
          Complex.exp ((c : ℂ) * s) *
            deningerMeyerStrongLogMellin g s := by
    funext s
    rw [deningerMeyerStrongLogMellin_flow]
    congr 2
    ring
  rw [hfun]
  have hexp :
      ContDiff ℂ (k : WithTop ℕ∞)
        (fun s : ℂ => Complex.exp ((c : ℂ) * s)) := by
    fun_prop
  have hmellin :
      ContDiff ℂ (k : WithTop ℕ∞)
        (deningerMeyerStrongLogMellin g) :=
    (differentiable_deningerMeyerStrongLogMellin
      g.property).contDiff.of_le le_top
  change
    iteratedDeriv k
        ((fun s : ℂ => Complex.exp ((c : ℂ) * s)) *
          deningerMeyerStrongLogMellin g) rho = _
  rw [iteratedDeriv_mul hexp.contDiffAt hmellin.contDiffAt]
  apply Finset.sum_congr rfl
  intro i hi
  rw [congrFun
      (iteratedDeriv_cexp_const_mul i (c : ℂ)) rho]
  rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
  ring

/--
Full generalized Xi-eigenpacket flow law on literal Meyer cohomology.  Each
order mixes only with lower orders, with the exact binomial translation
matrix and eigencharacter `exp(c rho)`.
-/
theorem deningerMeyerXiSupportJetEvaluationLM_flow
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho)
    (c : ℝ) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerXiSupportJetEvaluationLM rho k
        (deningerMeyerStrongLogCohomologyFlow c u) =
      ∑ i ∈ Finset.range (k.val + 1),
        (k.val.choose i : ℂ) *
          (c : ℂ) ^ i *
          Complex.exp ((c : ℂ) * (rho : ℂ)) *
          deningerMeyerXiSupportJetEvaluationLM rho
            (⟨k.val - i,
              lt_of_le_of_lt (Nat.sub_le k.val i) k.isLt⟩ :
                DeningerArithmeticJetIndex rho) u := by
  induction u using Submodule.Quotient.induction_on with
  | _ g =>
      simp only [
        deningerMeyerStrongLogCohomologyFlow_mk,
        deningerMeyerXiSupportJetEvaluationLM_mk]
      exact
        deningerMeyerStrongLogMellinJetLM_flow
          c g k.val (rho : ℂ)

/-- Zeroth Xi evaluation is a genuine nonzero flow eigenfunctional. -/
theorem deningerMeyerXiSupportEvaluationLM_ne_zero
    (rho : XiDivisorSupport) :
    deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho) ≠ 0 := by
  intro hzero
  have htarget :
      deningerMeyerStrongLogMellinJetLM 0 (rho : ℂ) = 0 := by
    ext g
    have h :=
      LinearMap.congr_fun hzero (Submodule.Quotient.mk g)
    simpa only [
      deningerMeyerXiSupportJetEvaluationLM_mk,
      LinearMap.zero_apply] using h
  exact
    ((deningerMeyerStrongLogMellinJetLM_linearIndependent
        (rho : ℂ) 1).ne_zero ⟨0, by omega⟩) htarget

/--
Exact one-way Xi-divisor inclusion into the literal Meyer dual flow:
every actual Xi divisor point supplies a nonzero eigenfunctional with
character `c ↦ exp(c rho)`.
-/
theorem deningerMeyer_every_xiDivisor_is_flowEigenvalue
    (rho : XiDivisorSupport) :
    ∃ E :
        DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ,
      E ≠ 0 ∧
      ∀ (c : ℝ) (u : DeningerMeyerStrongLogCohomology),
        E (deningerMeyerStrongLogCohomologyFlow c u) =
          Complex.exp ((c : ℂ) * (rho : ℂ)) * E u := by
  let k0 : DeningerArithmeticJetIndex rho :=
    ⟨0, xiSupportMultiplicity_pos rho⟩
  refine
    ⟨deningerMeyerXiSupportJetEvaluationLM rho k0,
      deningerMeyerXiSupportEvaluationLM_ne_zero rho, ?_⟩
  intro c u
  simpa [k0] using
    deningerMeyerXiSupportJetEvaluationLM_flow rho k0 c u

end

end RHTower
