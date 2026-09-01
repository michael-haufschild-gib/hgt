import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherPhysicalHilbertWall
import GaloisForLFunctions.RHTower.DirichletHilbertRiggingBarrier

/-!
# Exact diagonal-rigging wall for the physical MSC overlap

The physical squarefree-Möbius column at spectral point `rho` and the literal
base Möbius covector defining its MSC overlap have coefficientwise norm product

`squarefreeMobiusMass rho.re n / squarefreeMobiusTotal sigma`.

This density is independent of aperture `sigma` up to normalization.  Reciprocal
positive diagonal Hilbert weights can make both coefficient sequences normal
exactly when `1 < rho.re`; weighted Cauchy--Schwarz gives necessity, while the
geometric-mean weight `exp ((rho.re - sigma) log n)` gives sufficiency.

Every strict-right Xi zero has `rho.re < 1`, so no coefficient-faithful diagonal
Hilbert/Gelfand completion can retain even the physical MSC overlap denominator.
The positive survivor is the exact product invariant and its canonical balanced
weight.  Any surviving completion must be non-diagonal or genuinely distributional.
-/

open Complex Filter Set Topology
open scoped Topology

noncomputable section

namespace RHTower.HedenmalmThetaSource

theorem mscPhysicalZeroCoordinate_re_mul_sub
    (rho : ℂ) {sigma : ℝ} (hsigma : sigma ≠ 1) :
    (RHTower.mscPhysicalZeroCoordinate rho sigma).re * (sigma - 1) =
      rho.re - sigma := by
  have hre : (RHTower.mscPhysicalZeroCoordinate rho sigma).re =
      (rho.re - sigma) / (sigma - 1) := by
    rw [RHTower.mscPhysicalZeroCoordinate, Complex.div_re]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero, Complex.normSq_apply]
    field_simp [sub_ne_zero.mpr hsigma]
    ring
  rw [hre]
  exact div_mul_cancel₀ _ (sub_ne_zero.mpr hsigma)

theorem physicalDamping_mul_squarefreeMobiusMass
    (rho : ℂ) {sigma : ℝ} (hsigma : sigma ≠ 1) (n : ℕ) :
    Real.exp (-((RHTower.mscPhysicalZeroCoordinate rho sigma).re *
        (sigma - 1) * Real.log n)) *
        RHTower.squarefreeMobiusMass sigma n =
      RHTower.squarefreeMobiusMass rho.re n := by
  rw [RHTower.squarefreeMobiusMass, RHTower.squarefreeMobiusMass]
  split_ifs with hn
  · have hn0 : n ≠ 0 := by
      intro h
      subst n
      exact not_squarefree_zero hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    rw [Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hnpos]
    rw [mscPhysicalZeroCoordinate_re_mul_sub rho hsigma]
    rw [← Real.exp_add]
    congr 1
    ring
  · simp

theorem norm_mul_norm_mscPhysicalSource_eq
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    ‖RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
        (RHTower.mscPhysicalZeroCoordinate rho sigma) n‖ *
      ‖RHTower.infiniteMobiusSignedWeight sigma n‖ =
        RHTower.squarefreeMobiusMass rho.re n /
          RHTower.squarefreeMobiusTotal sigma := by
  have hbase := RHTower.norm_infiniteMobiusSignedWeight_sq hsigma n
  have hphys := RHTower.norm_infiniteMobiusCriticalComplexDampedSignedWeight_sq
    (RHTower.mscPhysicalZeroCoordinate rho sigma) hsigma n
  have hexp0 : 0 < Real.exp
      (-((RHTower.mscPhysicalZeroCoordinate rho sigma).re *
        (sigma - 1) * Real.log n)) := Real.exp_pos _
  have hbase0 : 0 ≤ ‖RHTower.infiniteMobiusSignedWeight sigma n‖ := norm_nonneg _
  have hphys0 : 0 ≤ ‖RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
        (RHTower.mscPhysicalZeroCoordinate rho sigma) n‖ := norm_nonneg _
  have hprob0 : 0 ≤ RHTower.squarefreeMobiusProbability sigma n :=
    RHTower.squarefreeMobiusProbability_nonneg hsigma n
  have hprod :
      ‖RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
          (RHTower.mscPhysicalZeroCoordinate rho sigma) n‖ *
        ‖RHTower.infiniteMobiusSignedWeight sigma n‖ =
      Real.exp (-((RHTower.mscPhysicalZeroCoordinate rho sigma).re *
        (sigma - 1) * Real.log n)) *
        RHTower.squarefreeMobiusProbability sigma n := by
    have hsquare :
        (‖RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
            (RHTower.mscPhysicalZeroCoordinate rho sigma) n‖ *
          ‖RHTower.infiniteMobiusSignedWeight sigma n‖) ^ 2 =
        (Real.exp (-((RHTower.mscPhysicalZeroCoordinate rho sigma).re *
            (sigma - 1) * Real.log n)) *
          RHTower.squarefreeMobiusProbability sigma n) ^ 2 := by
      rw [mul_pow, hphys, hbase, mul_pow]
      ring
    exact (sq_eq_sq₀
      (mul_nonneg hphys0 hbase0)
      (mul_nonneg hexp0.le hprob0)).mp hsquare
  rw [hprod, RHTower.squarefreeMobiusProbability, ← mul_div_assoc,
    physicalDamping_mul_squarefreeMobiusMass rho hsigma.ne']

private theorem two_mul_norm_product_le_weighted_sum
    {w a b : ℝ} (hw : 0 < w) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    2 * (a * b) ≤ w * a ^ 2 + w⁻¹ * b ^ 2 := by
  have hinv : w * w⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
  apply (mul_le_mul_iff_of_pos_right hw).1
  nlinarith [sq_nonneg (w * a - b)]

/-- Reciprocal diagonal Hilbert admission forces absolute summability of the
coefficientwise source--covector product. -/
theorem summable_norm_mul_norm_of_reciprocal_weighted_rigging
    (x y : ℕ → ℂ) (w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    (hx : Summable (fun n => w n * ‖x n‖ ^ 2))
    (hy : Summable (fun n => (w n)⁻¹ * ‖y n‖ ^ 2)) :
    Summable (fun n => ‖x n‖ * ‖y n‖) := by
  have hmajor : Summable (fun n =>
      w n * ‖x n‖ ^ 2 + (w n)⁻¹ * ‖y n‖ ^ 2) := hx.add hy
  have htwo : Summable (fun n => 2 * (‖x n‖ * ‖y n‖)) := by
    apply Summable.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      exact two_mul_norm_product_le_weighted_sum
        (hw n) (norm_nonneg _) (norm_nonneg _)
    · exact hmajor
  exact (summable_mul_left_iff (by norm_num : (2 : ℝ) ≠ 0)).mp htwo

/-- Positive reciprocal diagonal rigging for both the physical MSC column and
the base Möbius overlap covector. -/
def AdmitsMSCPhysicalOverlapDiagonalRigging (rho : ℂ) (sigma : ℝ) : Prop :=
  ∃ w : ℕ → ℝ,
    (∀ n, 0 < w n) ∧
    Summable (fun n => w n *
      ‖RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
        (RHTower.mscPhysicalZeroCoordinate rho sigma) n‖ ^ 2) ∧
    Summable (fun n => (w n)⁻¹ *
      ‖RHTower.infiniteMobiusSignedWeight sigma n‖ ^ 2)

/-- The geometric-mean diagonal weight balancing physical source and overlap covector. -/
def mscBalancedDiagonalWeight (rho : ℂ) (sigma : ℝ) (n : ℕ) : ℝ :=
  Real.exp ((rho.re - sigma) * Real.log n)

theorem mscBalancedDiagonalWeight_pos
    (rho : ℂ) (sigma : ℝ) (n : ℕ) :
    0 < mscBalancedDiagonalWeight rho sigma n :=
  Real.exp_pos _

private theorem mscPhysicalDampingExponent_eq
    (rho : ℂ) {sigma : ℝ} (hsigma : sigma ≠ 1) (n : ℕ) :
    -((RHTower.mscPhysicalZeroCoordinate rho sigma).re *
        (sigma - 1) * Real.log n) =
      (sigma - rho.re) * Real.log n := by
  rw [mscPhysicalZeroCoordinate_re_mul_sub rho hsigma]
  ring

theorem mscBalancedDiagonalWeight_mul_physical_norm_sq
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    mscBalancedDiagonalWeight rho sigma n *
        ‖RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
          (RHTower.mscPhysicalZeroCoordinate rho sigma) n‖ ^ 2 =
      RHTower.squarefreeMobiusMass rho.re n /
        RHTower.squarefreeMobiusTotal sigma := by
  rw [RHTower.norm_infiniteMobiusCriticalComplexDampedSignedWeight_sq
    (RHTower.mscPhysicalZeroCoordinate rho sigma) hsigma]
  rw [mscPhysicalDampingExponent_eq rho hsigma.ne']
  have hcancel :
      mscBalancedDiagonalWeight rho sigma n *
          Real.exp ((sigma - rho.re) * Real.log n) ^ 2 =
        Real.exp ((sigma - rho.re) * Real.log n) := by
    rw [mscBalancedDiagonalWeight, pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hcancel, RHTower.squarefreeMobiusProbability,
    ← mul_div_assoc]
  have htransfer := physicalDamping_mul_squarefreeMobiusMass rho hsigma.ne' n
  rw [mscPhysicalDampingExponent_eq rho hsigma.ne'] at htransfer
  rw [htransfer]

theorem mscBalancedDiagonalWeight_inv_mul_base_norm_sq
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    (mscBalancedDiagonalWeight rho sigma n)⁻¹ *
        ‖RHTower.infiniteMobiusSignedWeight sigma n‖ ^ 2 =
      RHTower.squarefreeMobiusMass rho.re n /
        RHTower.squarefreeMobiusTotal sigma := by
  rw [RHTower.norm_infiniteMobiusSignedWeight_sq hsigma,
    mscBalancedDiagonalWeight, ← Real.exp_neg,
    RHTower.squarefreeMobiusProbability, ← mul_div_assoc]
  rw [← physicalDamping_mul_squarefreeMobiusMass rho hsigma.ne']
  rw [mscPhysicalDampingExponent_eq rho hsigma.ne']
  congr 2
  ring

theorem admitsMSCPhysicalOverlapDiagonalRigging_of_one_lt_re
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 < rho.re) :
    AdmitsMSCPhysicalOverlapDiagonalRigging rho sigma := by
  refine ⟨mscBalancedDiagonalWeight rho sigma,
    mscBalancedDiagonalWeight_pos rho sigma, ?_, ?_⟩
  · rw [show (fun n => mscBalancedDiagonalWeight rho sigma n *
        ‖RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
          (RHTower.mscPhysicalZeroCoordinate rho sigma) n‖ ^ 2) =
      fun n => RHTower.squarefreeMobiusMass rho.re n /
        RHTower.squarefreeMobiusTotal sigma by
      funext n
      exact mscBalancedDiagonalWeight_mul_physical_norm_sq rho hsigma n]
    exact (RHTower.summable_squarefreeMobiusMass hrho).div_const _
  · rw [show (fun n => (mscBalancedDiagonalWeight rho sigma n)⁻¹ *
        ‖RHTower.infiniteMobiusSignedWeight sigma n‖ ^ 2) =
      fun n => RHTower.squarefreeMobiusMass rho.re n /
        RHTower.squarefreeMobiusTotal sigma by
      funext n
      exact mscBalancedDiagonalWeight_inv_mul_base_norm_sq rho hsigma n]
    exact (RHTower.summable_squarefreeMobiusMass hrho).div_const _

theorem one_lt_re_of_admitsMSCPhysicalOverlapDiagonalRigging
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma)
    (h : AdmitsMSCPhysicalOverlapDiagonalRigging rho sigma) :
    1 < rho.re := by
  rcases h with ⟨w, hw, hphysical, hbase⟩
  have hprod := summable_norm_mul_norm_of_reciprocal_weighted_rigging
    (fun n => RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
      (RHTower.mscPhysicalZeroCoordinate rho sigma) n)
    (RHTower.infiniteMobiusSignedWeight sigma) w hw hphysical hbase
  have hratio : Summable (fun n =>
      RHTower.squarefreeMobiusMass rho.re n /
        RHTower.squarefreeMobiusTotal sigma) :=
    hprod.congr (fun n => norm_mul_norm_mscPhysicalSource_eq rho hsigma n)
  have htotal : RHTower.squarefreeMobiusTotal sigma ≠ 0 :=
    (RHTower.squarefreeMobiusTotal_pos hsigma).ne'
  have hmass : Summable (RHTower.squarefreeMobiusMass rho.re) := by
    have hscaled := hratio.mul_left (RHTower.squarefreeMobiusTotal sigma)
    exact hscaled.congr (fun n => by field_simp [htotal])
  exact RHTower.summable_squarefreeMobiusMass_iff.mp hmass

/-- Exact diagonal-rigging classification: the physical source and its literal
MSC overlap covector coexist in reciprocal weighted Hilbert spaces exactly to
the right of the absolute-convergence wall. -/
theorem admitsMSCPhysicalOverlapDiagonalRigging_iff
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) :
    AdmitsMSCPhysicalOverlapDiagonalRigging rho sigma ↔ 1 < rho.re := by
  exact ⟨one_lt_re_of_admitsMSCPhysicalOverlapDiagonalRigging rho hsigma,
    admitsMSCPhysicalOverlapDiagonalRigging_of_one_lt_re rho hsigma⟩

theorem not_admitsMSCPhysicalOverlapDiagonalRigging_of_re_le_one
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : rho.re ≤ 1) :
    ¬ AdmitsMSCPhysicalOverlapDiagonalRigging rho sigma := by
  rw [admitsMSCPhysicalOverlapDiagonalRigging_iff rho hsigma]
  exact not_lt_of_ge hrho

/-- At an actual strict-right Xi zero, the existing residue-split physical MSC
germ coexists with no positive reciprocal diagonal Hilbert realization of its
literal overlap denominator. -/
theorem strictRightXiZero_mscPhysicalOverlapDiagonalRiggingNoGo
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1)
    (hzero : RHTower.xi rho = 0) :
    (∃ k : ℕ, analyticOrderAt RHTower.xi rho = (k + 1 : ℕ) ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho ∧
        (∀ sigma : ℝ, 1 < sigma →
          AnalyticAt ℂ (RHTower.mscPhysicalRegularGerm rho g sigma)
              (RHTower.mscPhysicalZeroCoordinate rho sigma) ∧
            (fun v =>
              GaloisForLFunctions.squarefreeFisherScore
                  (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v /
                GaloisForLFunctions.squarefreeBoundaryOverlap
                  (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v) =ᶠ[
              𝓝[≠] (RHTower.mscPhysicalZeroCoordinate rho sigma)]
                fun v => 2 * ((k + 1 : ℕ) : ℂ) /
                  (v - RHTower.mscPhysicalZeroCoordinate rho sigma) +
                    RHTower.mscPhysicalRegularGerm rho g sigma v) ∧
          Tendsto
            (fun sigma : ℝ =>
              Complex.normSq
                (RHTower.mscPhysicalRegularGerm rho g sigma
                  (RHTower.mscPhysicalZeroCoordinate rho sigma)))
            (nhdsWithin 1 (Ioi 1)) (nhds 4)) ∧
      ∀ sigma : ℝ, 1 < sigma →
        ¬ AdmitsMSCPhysicalOverlapDiagonalRigging rho sigma := by
  refine ⟨RHTower.exists_mscPhysicalRegularGerm_residueSplit_tendsto_four
    hhalf hone hzero, ?_⟩
  intro sigma hsigma
  exact not_admitsMSCPhysicalOverlapDiagonalRigging_of_re_le_one
    rho hsigma hone.le

end RHTower.HedenmalmThetaSource

