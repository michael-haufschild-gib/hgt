import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowDivisorTomography
import GaloisForLFunctions.RHTower.OrbitwiseSourceDivisorSeam
import GaloisForLFunctions.RHTower.PrimePolarDirichletBackbone

/-!
# A minimal prime source for the complete nontrivial zeta divisor

The coefficient `(Λ(n) - 1) * sqrt(n)` has the initial Dirichlet series

`-ζ'/ζ(s - 1/2) - ζ(s - 1/2)`.

The two poles at `s = 3/2` cancel.  Its pole-filled continuation has a simple pole at every
translated nontrivial zeta zero, with residue the negative analytic multiplicity.  This is a
minimal baseline for divisor recovery; unlike the dyadic sharp source, it has no semilocal window
geometry.
-/

open Complex Filter Function Set Topology

namespace RHTower

noncomputable section

/-- The elementary complete-divisor source coefficient. -/
def simplePrimeDivisorSourceCoefficient (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n - 1) * Real.sqrt n

/-- Its pole-filled continuation.  The divided difference cancels the zeta pole at `s = 3/2`. -/
def simplePrimeDivisorContinuedSource (s : ℂ) : ℂ :=
  -logDeriv regularizedRiemannZeta (s - 1 / 2) -
    dslope regularizedRiemannZeta 1 (s - 1 / 2)

private theorem shiftedVonMangoldtCoeff_neg_half_eq_sqrt
    (n : ℕ) :
    shiftedVonMangoldtCoeff (-(1 / 2 : ℂ)) n =
      ((ArithmeticFunction.vonMangoldt n * Real.sqrt n : ℝ) : ℂ) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [shiftedVonMangoldtCoeff]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    rw [shiftedVonMangoldtCoeff, Complex.cpow_neg]
    have hsqrt : ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow]
      simpa using Complex.ofReal_cpow (Nat.cast_nonneg n) (1 / 2 : ℝ)
    rw [div_eq_mul_inv, inv_inv]
    push_cast
    rw [hsqrt]

private theorem complex_sqrt_eq_cpow_half (n : ℕ) :
    ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) ^ (1 / 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow]
  simpa using Complex.ofReal_cpow (Nat.cast_nonneg n) (1 / 2 : ℝ)

private theorem simplePrimeDivisorSourceCoefficient_cast
    (n : ℕ) :
    ((simplePrimeDivisorSourceCoefficient n : ℝ) : ℂ) =
      shiftedVonMangoldtCoeff (-(1 / 2 : ℂ)) n -
        (n : ℂ) ^ (1 / 2 : ℂ) := by
  rw [simplePrimeDivisorSourceCoefficient, shiftedVonMangoldtCoeff_neg_half_eq_sqrt]
  push_cast
  rw [complex_sqrt_eq_cpow_half]
  ring

private theorem LSeriesSummable_shiftedVonMangoldtCoeff_neg_half
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (shiftedVonMangoldtCoeff (-(1 / 2 : ℂ))) s := by
  have hvm : LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s - 1 / 2) := by
    apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    norm_num [Complex.sub_re]
    linarith
  change Summable (LSeries.term (shiftedVonMangoldtCoeff (-(1 / 2 : ℂ))) s)
  change Summable (LSeries.term
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s - 1 / 2)) at hvm
  apply hvm.congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [LSeries.term_zero]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0,
      shiftedVonMangoldtCoeff]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    rw [Complex.cpow_sub _ _ hnC, Complex.cpow_neg]
    field_simp

theorem simplePrimeDivisorSourceCoefficient_LSeriesSummable
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable
      (fun n => ((simplePrimeDivisorSourceCoefficient n : ℝ) : ℂ)) s := by
  have hvm := LSeriesSummable_shiftedVonMangoldtCoeff_neg_half hs
  have hpow : LSeriesSummable (fun n : ℕ => (n : ℂ) ^ (1 / 2 : ℂ)) s := by
    rw [lseriesSummable_cpow]
    apply LSeriesSummable_one_iff.mpr
    norm_num [Complex.sub_re]
    linarith
  have hsub := hvm.sub hpow
  change Summable (LSeries.term
    (fun n => ((simplePrimeDivisorSourceCoefficient n : ℝ) : ℂ)) s)
  change Summable (LSeries.term _ s) at hsub
  exact hsub.congr fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne',
        simplePrimeDivisorSourceCoefficient_cast]
      rfl

/-- Far right, the elementary source has the advertised logarithmic-derivative identity. -/
theorem LSeries_simplePrimeDivisorSourceCoefficient_eq_zetaLogDeriv
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries (fun n => ((simplePrimeDivisorSourceCoefficient n : ℝ) : ℂ)) s =
      -zetaLogDeriv (s - 1 / 2) - riemannZeta (s - 1 / 2) := by
  have hvm := LSeriesSummable_shiftedVonMangoldtCoeff_neg_half hs
  have hpow : LSeriesSummable (fun n : ℕ => (n : ℂ) ^ (1 / 2 : ℂ)) s := by
    rw [lseriesSummable_cpow]
    apply LSeriesSummable_one_iff.mpr
    norm_num [Complex.sub_re]
    linarith
  calc
    LSeries (fun n => ((simplePrimeDivisorSourceCoefficient n : ℝ) : ℂ)) s =
        LSeries (shiftedVonMangoldtCoeff (-(1 / 2 : ℂ)) -
          fun n : ℕ => (n : ℂ) ^ (1 / 2 : ℂ)) s := by
      apply LSeries_congr
      intro n hn
      simpa only [Pi.sub_apply] using simplePrimeDivisorSourceCoefficient_cast n
    _ = LSeries (shiftedVonMangoldtCoeff (-(1 / 2 : ℂ))) s -
        LSeries (fun n : ℕ => (n : ℂ) ^ (1 / 2 : ℂ)) s := LSeries_sub hvm hpow
    _ = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s - 1 / 2) -
        riemannZeta (s - 1 / 2) := by
      rw [LSeries_shiftedVonMangoldtCoeff, lseries_cpow_eq_zeta]
      · ring_nf
      · norm_num [Complex.sub_re]
        linarith
    _ = -zetaLogDeriv (s - 1 / 2) - riemannZeta (s - 1 / 2) := by
      have hshift : 1 < (s - 1 / 2).re := by
        norm_num [Complex.sub_re]
        linarith
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hshift,
        zetaLogDeriv]
      ring

private theorem differentiable_simplePrimeDivisorDslope :
    Differentiable ℂ (fun s : ℂ =>
      dslope regularizedRiemannZeta 1 (s - 1 / 2)) := by
  have hds : Differentiable ℂ (dslope regularizedRiemannZeta 1) := by
    rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
    exact differentiable_regularizedRiemannZeta.differentiableOn
  exact hds.comp (differentiable_id.sub_const (1 / 2))

/-- The continuation equals the ordinary source series on its initial half-plane. -/
theorem simplePrimeDivisorContinuedSource_eq_zetaLogDeriv
    {s : ℂ} (hs : 3 / 2 < s.re) :
    simplePrimeDivisorContinuedSource s =
      -zetaLogDeriv (s - 1 / 2) - riemannZeta (s - 1 / 2) := by
  let u : ℂ := s - 1 / 2
  have hu1 : u ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [u] at hre
    norm_num [Complex.sub_re] at hre
    linarith
  have hz : riemannZeta u ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      dsimp only [u]
      norm_num [Complex.sub_re]
      linarith)
  have hreg : regularizedRiemannZeta u = (u - 1) * riemannZeta u :=
    regularizedRiemannZeta_of_ne_one hu1
  have hds : dslope regularizedRiemannZeta 1 u =
      (regularizedRiemannZeta u - 1) / (u - 1) := by
    rw [dslope_of_ne _ hu1, slope_def_field, regularizedRiemannZeta_one]
  rw [simplePrimeDivisorContinuedSource, show s - 1 / 2 = u by rfl,
    logDeriv_regularizedRiemannZeta_eq hu1 hz, hds, hreg]
  have hden : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  field_simp [hden]
  ring

theorem LSeries_simplePrimeDivisorSourceCoefficient_eq_continuedSource
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries (fun n => ((simplePrimeDivisorSourceCoefficient n : ℝ) : ℂ)) s =
      simplePrimeDivisorContinuedSource s := by
  rw [LSeries_simplePrimeDivisorSourceCoefficient_eq_zetaLogDeriv hs,
    simplePrimeDivisorContinuedSource_eq_zetaLogDeriv hs]

/-- Away from a zero of the pole-filled zeta, the elementary source is analytic. -/
theorem analyticAt_simplePrimeDivisorContinuedSource_of_regularizedZeta_ne_zero
    {s : ℂ} (hz : regularizedRiemannZeta (s - 1 / 2) ≠ 0) :
    AnalyticAt ℂ simplePrimeDivisorContinuedSource s := by
  have hreg : AnalyticAt ℂ regularizedRiemannZeta (s - 1 / 2) :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) _ (Set.mem_univ _)
  have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2) s := by fun_prop
  have hlog : AnalyticAt ℂ
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) s := by
    rw [show (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) =
        fun z : ℂ => deriv regularizedRiemannZeta (z - 1 / 2) /
          regularizedRiemannZeta (z - 1 / 2) by
      funext z
      rw [logDeriv_apply]]
    exact (AnalyticAt.comp (f := fun z : ℂ => z - 1 / 2) (x := s)
      hreg.deriv hshift).div
        (AnalyticAt.comp (f := fun z : ℂ => z - 1 / 2) (x := s) hreg hshift) hz
  have hds : AnalyticAt ℂ
      (fun z : ℂ => dslope regularizedRiemannZeta 1 (z - 1 / 2)) s :=
    (differentiable_simplePrimeDivisorDslope.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  exact hlog.neg.sub hds

/-- The artificial pole at `s = 3/2` is removable. -/
theorem analyticAt_simplePrimeDivisorContinuedSource_three_halves :
    AnalyticAt ℂ simplePrimeDivisorContinuedSource (3 / 2) := by
  apply analyticAt_simplePrimeDivisorContinuedSource_of_regularizedZeta_ne_zero
  norm_num [regularizedRiemannZeta_one]

/-- Every translated right Xi zero is an exact simple pole of the elementary source. -/
theorem meromorphicOrderAt_simplePrimeDivisorContinuedSource_eq_neg_one
    (q : XiRightZeroCopy) :
    meromorphicOrderAt simplePrimeDivisorContinuedSource (xiRightShiftedPole q) =
      ((-1 : ℤ) : WithTop ℤ) := by
  let p : ℂ := xiRightShiftedPole q
  let rho : ℂ := (q.1.1 : ℂ)
  have hpρ : p - 1 / 2 = rho := by
    simpa only [p, rho] using xiRightShiftedPole_sub_half q
  have hregZero : regularizedRiemannZeta rho = 0 := by
    simpa only [p, hpρ] using regularizedRiemannZeta_shift_eq_zero_at_xiRightPole q
  let shift : ℂ → ℂ := fun z => z - 1 / 2
  have hshiftAnalytic : AnalyticAt ℂ shift p := by
    dsimp only [shift]
    fun_prop
  have hshiftDeriv : deriv shift p ≠ 0 := by
    dsimp only [shift]
    rw [deriv_sub_const, deriv_id'']
    norm_num
  have hshiftOrder : meromorphicOrderAt
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) p =
        ((-1 : ℤ) : WithTop ℤ) := by
    have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := logDeriv regularizedRiemannZeta) (g := shift) (x := p)
      hshiftAnalytic hshiftDeriv
    rw [show shift p = rho by simpa only [shift] using hpρ,
      meromorphicOrderAt_logDeriv_regularizedRiemannZeta_eq_neg_one hregZero] at hcomp
    simpa only [shift, Function.comp_apply] using! hcomp
  let singular : ℂ → ℂ := fun z =>
    (-1 : ℂ) * logDeriv regularizedRiemannZeta (z - 1 / 2)
  have hfac : AnalyticAt ℂ (fun _z : ℂ => (-1 : ℂ)) p := analyticAt_const
  have hfacOrder : meromorphicOrderAt (fun _z : ℂ => (-1 : ℂ)) p = 0 := by
    rw [hfac.meromorphicOrderAt_eq, hfac.analyticOrderAt_eq_zero.mpr]
    · simp
    · norm_num
  have hshiftMero : MeromorphicAt
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) p := by
    have hbase : MeromorphicAt (logDeriv regularizedRiemannZeta) (shift p) := by
      rw [show shift p = rho by simpa only [shift] using hpρ]
      exact meromorphicAt_logDeriv_regularizedRiemannZeta rho
    simpa only [shift, Function.comp_apply] using!
      MeromorphicAt.comp_analyticAt hbase hshiftAnalytic
  have hsingOrder : meromorphicOrderAt singular p =
      ((-1 : ℤ) : WithTop ℤ) := by
    dsimp only [singular]
    rw [fun_meromorphicOrderAt_mul hfac.meromorphicAt hshiftMero,
      hfacOrder, hshiftOrder]
    norm_num
  let correction : ℂ → ℂ := fun z =>
    -dslope regularizedRiemannZeta 1 (z - 1 / 2)
  have hcorr : AnalyticAt ℂ correction p := by
    dsimp only [correction]
    exact ((differentiable_simplePrimeDivisorDslope.differentiableOn.analyticOnNhd
      isOpen_univ) p (Set.mem_univ p)).neg
  have hlt : meromorphicOrderAt singular p <
      meromorphicOrderAt correction p := by
    rw [hsingOrder]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hcorr.meromorphicOrderAt_nonneg
  have hfun : simplePrimeDivisorContinuedSource = singular + correction := by
    funext z
    simp only [simplePrimeDivisorContinuedSource, singular, correction, Pi.add_apply]
    ring
  rw [hfun, meromorphicOrderAt_add_eq_left_of_lt hcorr.meromorphicAt hlt,
    hsingOrder]

/-- The pole residue is the negative analytic multiplicity of the underlying Xi zero. -/
theorem tendsto_simplePrimeDivisorContinuedSource_residue
    (q : XiRightZeroCopy) :
    Tendsto
      (fun s : ℂ => (s - xiRightShiftedPole q) *
        simplePrimeDivisorContinuedSource s)
      (𝓝[≠] (xiRightShiftedPole q))
      (𝓝 (-(xiRightMultiplicity q : ℂ))) := by
  let p : ℂ := xiRightShiftedPole q
  have hlog := (tendsto_shiftedRegularizedZeta_logDeriv_residue q).neg
  have hdsAnalytic : AnalyticAt ℂ
      (fun s : ℂ => dslope regularizedRiemannZeta 1 (s - 1 / 2)) p :=
    (differentiable_simplePrimeDivisorDslope.differentiableOn.analyticOnNhd
      isOpen_univ) p (Set.mem_univ p)
  have hremAt : ContinuousAt
      (fun s : ℂ => -(s - p) *
        dslope regularizedRiemannZeta 1 (s - 1 / 2)) p :=
    ((continuousAt_id.sub continuousAt_const).neg.mul hdsAnalytic.continuousAt)
  have hrem : Tendsto
      (fun s : ℂ => -(s - p) *
        dslope regularizedRiemannZeta 1 (s - 1 / 2))
      (𝓝[≠] p) (𝓝 0) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds hremAt.tendsto)
  have hsum := hlog.add hrem
  convert hsum using 1
  · funext s
    simp only [simplePrimeDivisorContinuedSource]
    dsimp only [p]
    ring
  · simp

/-- The elementary source is holomorphic on `Re s > 1` exactly under RH. -/
theorem riemannHypothesis_iff_simplePrimeDivisorContinuedSource_analyticOn_rightOne :
    RiemannHypothesis ↔
      AnalyticOnNhd ℂ simplePrimeDivisorContinuedSource {s : ℂ | 1 < s.re} := by
  constructor
  · intro hRH s hs
    change 1 < s.re at hs
    apply analyticAt_simplePrimeDivisorContinuedSource_of_regularizedZeta_ne_zero
    let t : ℂ := s - 1 / 2
    by_cases ht : t = 1
    · rw [show s - 1 / 2 = t by rfl, ht, regularizedRiemannZeta_one]
      norm_num
    · rw [show s - 1 / 2 = t by rfl, regularizedRiemannZeta_of_ne_one ht]
      apply mul_ne_zero (sub_ne_zero.mpr ht)
      intro hζ
      have htHalf : 1 / 2 < t.re := by
        dsimp only [t]
        norm_num [Complex.sub_re]
        linarith
      have htpos : 0 < t.re := by linarith
      have htRight : t ∈ rightHalf := by rw [mem_rightHalf]; exact htHalf
      exact (rh_iff_xi_ne_zero_right.mp hRH) t htRight
        ((xi_eq_zero_iff htpos ht).mpr hζ)
  · intro han
    by_contra hRH
    let q : XiRightZeroCopy :=
      Classical.choice (nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH)
    let p : ℂ := xiRightShiftedPole q
    have hp : 1 < p.re := by
      dsimp only [p]
      rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
      linarith [xiRightCenteredZero_re_pos q]
    have hnonneg := (han p hp).meromorphicOrderAt_nonneg
    have horder := meromorphicOrderAt_simplePrimeDivisorContinuedSource_eq_neg_one q
    dsimp only [p] at hnonneg
    rw [horder] at hnonneg
    have hnot : ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) := by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)
    exact hnot hnonneg

end

end RHTower
