import GaloisForLFunctions.RHTower.RouteESourceFaithfulEulerTiltUnitShell
import GaloisForLFunctions.HTGeometry.LaplaceTransformConvolution

/-!
# Route E physical-shell parity--energy regression

Dependency-closed finite core of physical shell conditioning.  Gaussian energy conditioning
preserves both regression frequency and Schur complement; a centered logarithmic Gaussian shell
cannot be represented by a positive Laplace measure; signed shell fields obey exact polarization;
and the full complex Euler product difference is a weighted odd Boolean cube retaining every
unselected recurrence factor.  These identities isolate sign-sensitive shell cancellation from
the still-open prime-asymptotic saddle estimates.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace RHTower

noncomputable section

/-! ## Exact Gaussian covariance survivor -/

/-- Positive energy covariance block and Gaussian shell width. -/
structure RouteEGaussianCovarianceBlock where
  A : ℝ
  B : ℝ
  C : ℝ
  Delta : ℝ
  C_pos : 0 < C
  Delta_pos : 0 < Delta

namespace RouteEGaussianCovarianceBlock

def conditionedA (g : RouteEGaussianCovarianceBlock) : ℝ :=
  g.A - g.B ^ 2 / (g.C + g.Delta ^ 2)

def conditionedB (g : RouteEGaussianCovarianceBlock) : ℝ :=
  g.B - g.B * g.C / (g.C + g.Delta ^ 2)

def conditionedC (g : RouteEGaussianCovarianceBlock) : ℝ :=
  g.C - g.C ^ 2 / (g.C + g.Delta ^ 2)

theorem denominator_pos (g : RouteEGaussianCovarianceBlock) :
    0 < g.C + g.Delta ^ 2 := by
  nlinarith [g.C_pos, sq_pos_of_pos g.Delta_pos]

theorem conditionedC_pos (g : RouteEGaussianCovarianceBlock) :
    0 < g.conditionedC := by
  unfold conditionedC
  have hden := g.denominator_pos
  have hD2 : 0 < g.Delta ^ 2 := sq_pos_of_pos g.Delta_pos
  field_simp [hden.ne']
  nlinarith [g.C_pos]

/-- Gaussian energy conditioning preserves exact regression frequency `B/C`. -/
theorem conditioned_regressionRatio (g : RouteEGaussianCovarianceBlock) :
    g.conditionedB / g.conditionedC = g.B / g.C := by
  unfold conditionedB conditionedC
  have hden := g.denominator_pos
  have hC := g.C_pos
  have hD2 : g.Delta ^ 2 ≠ 0 := (sq_pos_of_pos g.Delta_pos).ne'
  field_simp [hden.ne', hC.ne', hD2]

/-- Gaussian energy conditioning preserves the parity--energy Schur complement exactly. -/
theorem conditioned_schurComplement (g : RouteEGaussianCovarianceBlock) :
    g.conditionedA - g.conditionedB ^ 2 / g.conditionedC =
      g.A - g.B ^ 2 / g.C := by
  unfold conditionedA conditionedB conditionedC
  have hden := g.denominator_pos
  have hC := g.C_pos
  have hCc := g.conditionedC_pos
  have hD2 : g.Delta ^ 2 ≠ 0 := (sq_pos_of_pos g.Delta_pos).ne'
  field_simp [hden.ne', hC.ne', hCc.ne', hD2]
  ring

end RouteEGaussianCovarianceBlock

/-! ## Positive-Laplace descent wall -/

/-- Centered Gaussian shell in logarithmic product. -/
def routeEGaussianLogShell (X Delta m : ℝ) : ℝ :=
  Real.exp (-((Real.log m - Real.log X) ^ 2) / (2 * Delta ^ 2))

structure RouteEPositiveGaussianShell where
  X : ℝ
  Delta : ℝ
  X_pos : 0 < X
  Delta_pos : 0 < Delta

namespace RouteEPositiveGaussianShell

theorem at_center (g : RouteEPositiveGaussianShell) :
    routeEGaussianLogShell g.X g.Delta g.X = 1 := by
  simp [routeEGaussianLogShell]

theorem half_lt_center (g : RouteEPositiveGaussianShell) :
    routeEGaussianLogShell g.X g.Delta (g.X / 2) <
      routeEGaussianLogShell g.X g.Delta g.X := by
  rw [g.at_center]
  unfold routeEGaussianLogShell
  rw [Real.exp_lt_one_iff]
  have hhalf : 0 < g.X / 2 := div_pos g.X_pos (by norm_num)
  have hne : Real.log (g.X / 2) - Real.log g.X ≠ 0 := by
    rw [sub_ne_zero]
    intro hlog
    have := congrArg Real.exp hlog
    rw [Real.exp_log hhalf, Real.exp_log g.X_pos] at this
    nlinarith [g.X_pos]
  have hsq : 0 < (Real.log (g.X / 2) - Real.log g.X) ^ 2 :=
    sq_pos_of_ne_zero hne
  have hden : 0 < 2 * g.Delta ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos g.Delta_pos)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hsq) hden

/-- No positive measure on nonnegative scales has the centered Gaussian log shell as its
Laplace transform on the whole positive axis. -/
theorem no_positiveLaplaceRepresentation (g : RouteEPositiveGaussianShell) :
    ¬∃ μ : Measure ℝ,
      (∀ᵐ x ∂μ, 0 ≤ x) ∧
      ∀ m : ℝ, 0 < m →
        GaloisForLFunctions.HTGeometry.laplace μ m =
          ENNReal.ofReal (routeEGaussianLogShell g.X g.Delta m) := by
  rintro ⟨μ, hμ, hrep⟩
  have hanti := GaloisForLFunctions.HTGeometry.laplace_antitone μ
    (show g.X / 2 ≤ g.X by nlinarith [g.X_pos]) hμ
  rw [hrep (g.X / 2) (div_pos g.X_pos (by norm_num)),
    hrep g.X g.X_pos] at hanti
  have hstrictReal := g.half_lt_center
  have hcenterPos : 0 < routeEGaussianLogShell g.X g.Delta g.X := by
    rw [g.at_center]
    norm_num
  have hstrictENN :
      ENNReal.ofReal (routeEGaussianLogShell g.X g.Delta (g.X / 2)) <
        ENNReal.ofReal (routeEGaussianLogShell g.X g.Delta g.X) :=
    (ENNReal.ofReal_lt_ofReal_iff hcenterPos).2 hstrictReal
  exact (not_lt_of_ge hanti) hstrictENN

end RouteEPositiveGaussianShell

/-! ## Exact signed shell polarization -/

def routeESignedShellField
    {ι : Type*} [Fintype ι] (alpha field : ι → ℂ) : ℂ :=
  ∑ i, alpha i * field i

def routeESignedShellPolarizedKernel
    (Zi Mi Zj Mj : ℂ) : ℂ :=
  Zi * starRingEnd ℂ Zj - Mi * starRingEnd ℂ Mj

/-- Exact finite analogue of the double-integral polarization identity. -/
theorem routeESignedShell_polarization
    {ι : Type*} [Fintype ι] (alpha Z M : ι → ℂ) :
    routeESignedShellField alpha Z * starRingEnd ℂ (routeESignedShellField alpha Z) -
        routeESignedShellField alpha M * starRingEnd ℂ (routeESignedShellField alpha M) =
      ∑ i, ∑ j,
        alpha i * starRingEnd ℂ (alpha j) *
          routeESignedShellPolarizedKernel (Z i) (M i) (Z j) (M j) := by
  unfold routeESignedShellField routeESignedShellPolarizedKernel
  simp_rw [map_sum, map_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Weighted odd Boolean cube: selected coordinates contribute `U`, while unselected
coordinates retain their full recurrence factor `B`. -/
def routeEWeightedOddSubsetSum
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (B U : ι → ℂ) : ℂ :=
  ∑ R ∈ P.powerset with Odd R.card,
    (∏ p ∈ R, U p) * ∏ p ∈ P \ R, B p

/-- Full weighted product difference with parity coefficient retained. -/
theorem routeEWeightedProductDifference_eq_paritySum
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (B U : ι → ℂ) :
    (∏ p ∈ P, (B p + U p)) - ∏ p ∈ P, (B p - U p) =
      ∑ R ∈ P.powerset,
        (1 - (-1 : ℂ) ^ R.card) *
          ((∏ p ∈ R, U p) * ∏ p ∈ P \ R, B p) := by
  classical
  have hplus :
      (∏ p ∈ P, (B p + U p)) =
        ∑ R ∈ P.powerset,
          (∏ p ∈ R, U p) * ∏ p ∈ P \ R, B p := by
    simpa [add_comm] using (Finset.prod_add U B P)
  have hminus :
      (∏ p ∈ P, (B p - U p)) =
        ∑ R ∈ P.powerset,
          ((-1 : ℂ) ^ R.card) *
            ((∏ p ∈ R, U p) * ∏ p ∈ P \ R, B p) := by
    calc
      (∏ p ∈ P, (B p - U p)) =
          ∑ R ∈ P.powerset,
            (∏ p ∈ R, -U p) * ∏ p ∈ P \ R, B p := by
              simpa [sub_eq_add_neg, add_comm] using
                (Finset.prod_add (fun p => -U p) B P)
      _ = ∑ R ∈ P.powerset,
            ((-1 : ℂ) ^ R.card) *
              ((∏ p ∈ R, U p) * ∏ p ∈ P \ R, B p) := by
            apply Finset.sum_congr rfl
            intro R hR
            rw [Finset.prod_neg]
            ring
  rw [hplus, hminus, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro R hR
  ring

/-- Exact weighted odd-cube completion. Even grades cancel; odd grades double without
discarding baseline recurrence factors. -/
theorem routeEWeightedProductDifference_eq_two_oddSubsetSum
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (B U : ι → ℂ) :
    (∏ p ∈ P, (B p + U p)) - ∏ p ∈ P, (B p - U p) =
      2 * routeEWeightedOddSubsetSum P B U := by
  classical
  rw [routeEWeightedProductDifference_eq_paritySum]
  unfold routeEWeightedOddSubsetSum
  rw [← Finset.sum_filter_add_sum_filter_not P.powerset (fun R => Odd R.card)
    (fun R => (1 - (-1 : ℂ) ^ R.card) *
      ((∏ p ∈ R, U p) * ∏ p ∈ P \ R, B p))]
  have hodd :
      (∑ R ∈ P.powerset with Odd R.card,
          (1 - (-1 : ℂ) ^ R.card) *
            ((∏ p ∈ R, U p) * ∏ p ∈ P \ R, B p)) =
        2 * ∑ R ∈ P.powerset with Odd R.card,
          ((∏ p ∈ R, U p) * ∏ p ∈ P \ R, B p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R hR
    have hRodd : Odd R.card := (Finset.mem_filter.mp hR).2
    rw [hRodd.neg_one_pow]
    ring
  have heven :
      (∑ R ∈ P.powerset with ¬Odd R.card,
          (1 - (-1 : ℂ) ^ R.card) *
            ((∏ p ∈ R, U p) * ∏ p ∈ P \ R, B p)) = 0 := by
    apply Finset.sum_eq_zero
    intro R hR
    have hRnot : ¬ Odd R.card := (Finset.mem_filter.mp hR).2
    have hReven : Even R.card := (Nat.even_or_odd R.card).resolve_right hRnot
    rw [hReven.neg_one_pow]
    ring
  rw [hodd, heven, add_zero]

/-- Common shell multipliers preserve the exact weighted odd-subset cube. -/
theorem routeECommonShellMultiplier_preservesWeightedOddCube
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (B U : ι → ℂ) (K : ℂ) :
    K * ((∏ p ∈ P, (B p + U p)) - ∏ p ∈ P, (B p - U p)) =
      K * (2 * routeEWeightedOddSubsetSum P B U) := by
  rw [routeEWeightedProductDifference_eq_two_oddSubsetSum]

end

end RHTower
