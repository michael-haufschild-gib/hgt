import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartz
import GaloisForLFunctions.RHTower.PrimeArchThetaAtomMoments
import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination
import GaloisForLFunctions.RHTower.PrimeArchThetaLiouvilleWard
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFourierLaplace
import GaloisForLFunctions.RHTower.XiEndpointCompletedValue
import GaloisForLFunctions.HTGeometry.ObservationFidelity
import GaloisForLFunctions.HTGeometry.ObservationMomentBudget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Ward--Laplace half-density observation budget

The theta-cusp atom is constrained by a static half-line Ward identity. Pairing that identity
with the exponential observation family `exp (z x)` produces a shifted Laplace relation with an
endpoint anomaly. At the half-density observations `z = ± 1/2`, the shift coefficient vanishes
and the observations close exactly:

`A_n(1/2) + A_n(-1/2) = (4 pi n^(2 : ℕ) - 1) exp (-pi n^(2 : ℕ))`.

Equivalently, this is the exact nonlocal clock-observation budget

`2 integral cosh (x/2) f_n(x) dx = (4 pi n^(2 : ℕ) - 1) exp (-pi n^(2 : ℕ))`.

The opposite half-density channels also have the exact orientation difference

`A_n(1/2) - A_n(-1/2) = exp (-pi n^(2 : ℕ))`.

Their geometric mean is the unweighted observation.  The general HTGeometry fidelity bound
therefore turns the symmetric and antisymmetric observations into the strict square budget

`a_{0,n}^(2 : ℕ) + exp (-pi n^(2 : ℕ))^(2 : ℕ) ≤ ((4 pi n^(2 : ℕ) - 1) exp (-pi n^(2 : ℕ)))^(2 : ℕ)`.

The final theorem applies the budget to the existing atom-moment corpus: positivity and
`1 <= cosh` give a closed upper bound for the zeroth raw atom moment; the fidelity deficit makes
that upper bound strict. Thus one moment previously treated as an independent box is controlled
by boundary observation identities.

This is the half-line boundary term familiar from quantum Ward/hypervirial relations, used here
as a static observability constraint; no temporal evolution and no numerical enclosure enter.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive Liouville half-density behind one theta-cusp source atom. -/
def thetaCuspWardGibbsAtom (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspPolynomialAtom (X ^ (2 : ℕ)) n x

theorem thetaCuspWardGibbsAtom_apply (n : ℕ) (x : ℝ) :
    thetaCuspWardGibbsAtom n x =
      Real.exp (x / 2) * ((n : ℝ) * Real.exp x) ^ (2 : ℕ) *
        Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ (2 : ℕ)) := by
  simp [thetaCuspWardGibbsAtom, thetaCuspPolynomialAtom]

theorem thetaCuspWardGibbsAtom_zero (n : ℕ) :
    thetaCuspWardGibbsAtom n 0 =
      (n : ℝ) ^ (2 : ℕ) * Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  rw [thetaCuspWardGibbsAtom_apply]
  simp

theorem hasDerivAt_thetaCuspWardGibbsAtom (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspWardGibbsAtom n)
      (thetaCuspPolynomialAtom (thetaCuspLogDerivativeStep (X ^ (2 : ℕ))) n x) x := by
  exact hasDerivAt_thetaCuspPolynomialAtom (X ^ (2 : ℕ)) n x

theorem deriv_thetaCuspWardGibbsAtom_eq_score (n : ℕ) (x : ℝ) :
    deriv (thetaCuspWardGibbsAtom n) x =
      ((5 / 2 : ℝ) - 2 * Real.pi * (n : ℝ) ^ (2 : ℕ) * Real.exp (2 * x)) *
        thetaCuspWardGibbsAtom n x := by
  rw [(hasDerivAt_thetaCuspWardGibbsAtom n x).deriv]
  simp [thetaCuspWardGibbsAtom, thetaCuspLogDerivativeStep,
    thetaCuspPolynomialAtom]
  rw [show Real.exp (2 * x) = Real.exp x ^ (2 : ℕ) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  ring

theorem thetaCuspSourceTerm_eq_wardGibbs (n : ℕ) (x : ℝ) :
    thetaCuspSourceTerm x n =
      -2 * Real.pi *
        (deriv (thetaCuspWardGibbsAtom n) x +
          (1 / 2 : ℝ) * thetaCuspWardGibbsAtom n x) := by
  rw [(hasDerivAt_thetaCuspWardGibbsAtom n x).deriv]
  simp [thetaCuspSourceTerm, thetaCuspSeed, thetaCuspWardGibbsAtom,
    thetaCuspPolynomialAtom, thetaCuspLogDerivativeStep]
  ring

/-- Exponential observation of the positive Gibbs half-density. -/
def thetaCuspWardGibbsExponentialTilt (z : ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, Real.exp (z * x) * thetaCuspWardGibbsAtom n x

/-- Exponential observation of one theta-cusp source atom. -/
def thetaCuspSourceExponentialTilt (z : ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, Real.exp (z * x) * thetaCuspSourceTerm x n

/-- Exponential observation of one polynomial-Gaussian theta atom. -/
def thetaCuspPolynomialAtomExponentialTilt (P : ℝ[X]) (z : ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, Real.exp (z * x) * thetaCuspPolynomialAtom P n x

theorem integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
    (P : ℝ[X]) {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (z * x) * thetaCuspPolynomialAtom P n x) (Ioi 0) := by
  let C : ℝ := thetaCuspGaussianConstant P *
    Real.exp (-(Real.pi / 2) * (n : ℝ) ^ (2 : ℕ))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity [thetaCuspGaussianConstant_nonneg P]
  have hbase : IntegrableOn (fun x : ℝ => Real.exp ((z - 1) * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hdom : IntegrableOn (fun x : ℝ => C * Real.exp ((z - 1) * x)) (Ioi 0) :=
    hbase.const_mul C
  apply Integrable.mono hdom
  · have hatom : Continuous (thetaCuspPolynomialAtom P n) :=
      continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspPolynomialAtom P n x).continuousAt
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      hatom).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have h := exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos P hx.le hn
    change Real.exp x * |thetaCuspPolynomialAtom P n x| ≤ C at h
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
    calc
      Real.exp (z * x) * |thetaCuspPolynomialAtom P n x| =
          Real.exp ((z - 1) * x) *
            (Real.exp x * |thetaCuspPolynomialAtom P n x|) := by
              have he : Real.exp (z * x) =
                  Real.exp ((z - 1) * x) * Real.exp x := by
                rw [← Real.exp_add]
                congr 1
                ring
              rw [he]
              ring
      _ ≤ Real.exp ((z - 1) * x) * C :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = C * Real.exp ((z - 1) * x) := by ring

theorem exp_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_lt_one
    (P : ℝ[X]) {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : z < 1) :
    Tendsto (fun x : ℝ =>
      Real.exp (z * x) * thetaCuspPolynomialAtom P n x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let C : ℝ := thetaCuspGaussianConstant P *
    Real.exp (-(Real.pi / 2) * (n : ℝ) ^ (2 : ℕ))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity [thetaCuspGaussianConstant_nonneg P]
  have hle : ∀ᶠ x : ℝ in atTop,
      ‖Real.exp (z * x) * thetaCuspPolynomialAtom P n x‖ ≤
        C * Real.exp ((z - 1) * x) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have h := exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos P hx hn
    change Real.exp x * |thetaCuspPolynomialAtom P n x| ≤ C at h
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (z * x) * |thetaCuspPolynomialAtom P n x| =
          Real.exp ((z - 1) * x) *
            (Real.exp x * |thetaCuspPolynomialAtom P n x|) := by
              have he : Real.exp (z * x) =
                  Real.exp ((z - 1) * x) * Real.exp x := by
                rw [← Real.exp_add]
                congr 1
                ring
              rw [he]
              ring
      _ ≤ Real.exp ((z - 1) * x) * C :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = C * Real.exp ((z - 1) * x) := by ring
  have hexp : Tendsto (fun x : ℝ => Real.exp ((z - 1) * x)) atTop (𝓝 0) := by
    rw [Real.tendsto_exp_comp_nhds_zero]
    exact (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).const_mul_atTop_of_neg
      (sub_neg.mpr hz)
  have hmajor : Tendsto (fun x : ℝ => C * Real.exp ((z - 1) * x))
      atTop (𝓝 0) := by simpa using hexp.const_mul C
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hle hmajor

theorem integral_exp_mul_deriv_thetaCuspWardGibbsAtom_eq
    {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : z < 1) :
    (∫ x : ℝ in Ioi 0,
        Real.exp (z * x) * deriv (thetaCuspWardGibbsAtom n) x) =
      -thetaCuspWardGibbsAtom n 0 -
        z * thetaCuspWardGibbsExponentialTilt z n := by
  let u : ℝ → ℝ := fun x => Real.exp (z * x)
  let u' : ℝ → ℝ := fun x => z * Real.exp (z * x)
  let b : ℝ → ℝ := thetaCuspWardGibbsAtom n
  let b' : ℝ → ℝ := fun x =>
    thetaCuspPolynomialAtom (thetaCuspLogDerivativeStep (X ^ (2 : ℕ))) n x
  have huderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (u' x) x := by
    intro x _hx
    dsimp [u, u']
    simpa only [Function.comp_apply, id_eq, one_mul, mul_one, mul_comm] using!
      (Real.hasDerivAt_exp (z * x)).comp x
        ((hasDerivAt_id x).const_mul z)
  have hbderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt b (b' x) x := by
    intro x _hx
    exact hasDerivAt_thetaCuspWardGibbsAtom n x
  have hub'int : IntegrableOn (u * b') (Ioi 0) := by
    simpa only [u, b', Pi.mul_apply] using!
      integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
        (thetaCuspLogDerivativeStep (X ^ (2 : ℕ))) hn hz
  have hbase : IntegrableOn (fun x : ℝ =>
      Real.exp (z * x) * thetaCuspWardGibbsAtom n x) (Ioi 0) := by
    simpa only [thetaCuspWardGibbsAtom] using
      integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one (X ^ (2 : ℕ)) hn hz
  have hu'bint : IntegrableOn (u' * b) (Ioi 0) := by
    have h := hbase.const_mul z
    apply h.congr
    filter_upwards [] with x
    dsimp [u', b]
    ring
  have hbcont : Continuous b :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspWardGibbsAtom n x).continuousAt
  have hucont : Continuous u := by
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := b 0) (b' := (0 : ℝ))
    (u := u) (u' := u') (v := b) (v' := b')
    huderiv hbderiv hub'int hu'bint
    (by
      have h := ((hucont.mul hbcont).tendsto 0).mono_left
        (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      simpa only [u, Pi.mul_apply, mul_zero, Real.exp_zero, one_mul] using! h)
    (by
      exact Filter.Tendsto.congr'
        (f₁ := fun x : ℝ =>
          Real.exp (z * x) * thetaCuspPolynomialAtom (X ^ (2 : ℕ)) n x)
        (f₂ := u * b)
        (Eventually.of_forall fun x => by rfl)
        (exp_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_lt_one
          (X ^ (2 : ℕ)) hn hz))
  have hibp' :
      (∫ x : ℝ in Ioi 0, u x * b' x) =
        -b 0 - z * (∫ x : ℝ in Ioi 0, u x * b x) := by
    have hi : (∫ x : ℝ in Ioi 0, u' x * b x) =
        z * ∫ x : ℝ in Ioi 0, u x * b x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [u, u', b]
      ring
    rw [hi] at hibp
    simpa using hibp
  rw [show (fun x : ℝ =>
      Real.exp (z * x) * deriv (thetaCuspWardGibbsAtom n) x) =
      fun x => u x * b' x by
        funext x
        rw [(hasDerivAt_thetaCuspWardGibbsAtom n x).deriv]]
  simpa only [u, b, thetaCuspWardGibbsExponentialTilt] using hibp'

theorem thetaCuspSourceExponentialTilt_eq_wardBoundary
    {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : z < 1) :
    thetaCuspSourceExponentialTilt z n =
      2 * Real.pi *
        (thetaCuspWardGibbsAtom n 0 +
          (z - 1 / 2 : ℝ) * thetaCuspWardGibbsExponentialTilt z n) := by
  have hderiv : IntegrableOn (fun x : ℝ =>
      Real.exp (z * x) * deriv (thetaCuspWardGibbsAtom n) x) (Ioi 0) := by
    simpa only [(hasDerivAt_thetaCuspWardGibbsAtom n _).deriv] using
      integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
        (thetaCuspLogDerivativeStep (X ^ (2 : ℕ))) hn hz
  have hgibbs : IntegrableOn (fun x : ℝ =>
      Real.exp (z * x) * thetaCuspWardGibbsAtom n x) (Ioi 0) := by
    simpa only [thetaCuspWardGibbsAtom] using
      integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one (X ^ (2 : ℕ)) hn hz
  rw [thetaCuspSourceExponentialTilt]
  simp_rw [thetaCuspSourceTerm_eq_wardGibbs]
  rw [show (fun x : ℝ =>
      Real.exp (z * x) *
        (-2 * Real.pi *
          (deriv (thetaCuspWardGibbsAtom n) x +
            (1 / 2 : ℝ) * thetaCuspWardGibbsAtom n x))) =
      fun x => -2 * Real.pi *
        ((Real.exp (z * x) * deriv (thetaCuspWardGibbsAtom n) x) +
          (1 / 2 : ℝ) *
            (Real.exp (z * x) * thetaCuspWardGibbsAtom n x)) by
          funext x
          ring]
  rw [integral_const_mul, integral_add hderiv (hgibbs.const_mul (1 / 2 : ℝ)),
    integral_const_mul, integral_exp_mul_deriv_thetaCuspWardGibbsAtom_eq hn hz]
  rw [thetaCuspWardGibbsExponentialTilt]
  ring

theorem thetaCuspWardGibbsExponentialTilt_shift
    {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : z < -1) :
    2 * Real.pi * (n : ℝ) ^ (2 : ℕ) *
        thetaCuspWardGibbsExponentialTilt (z + 2) n =
      thetaCuspWardGibbsAtom n 0 +
        (z + 5 / 2 : ℝ) * thetaCuspWardGibbsExponentialTilt z n := by
  have hz' : z < 1 := by linarith
  have hz2 : z + 2 < 1 := by linarith
  have hshift : IntegrableOn (fun x : ℝ =>
      Real.exp ((z + 2) * x) * thetaCuspWardGibbsAtom n x) (Ioi 0) := by
    simpa only [thetaCuspWardGibbsAtom] using
      integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one (X ^ (2 : ℕ)) hn hz2
  have hgibbs : IntegrableOn (fun x : ℝ =>
      Real.exp (z * x) * thetaCuspWardGibbsAtom n x) (Ioi 0) := by
    simpa only [thetaCuspWardGibbsAtom] using
      integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one (X ^ (2 : ℕ)) hn hz'
  have hderiv : IntegrableOn (fun x : ℝ =>
      Real.exp (z * x) * deriv (thetaCuspWardGibbsAtom n) x) (Ioi 0) := by
    simpa only [(hasDerivAt_thetaCuspWardGibbsAtom n _).deriv] using
      integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
        (thetaCuspLogDerivativeStep (X ^ (2 : ℕ))) hn hz'
  have hpoint (x : ℝ) :
      2 * Real.pi * (n : ℝ) ^ (2 : ℕ) *
          (Real.exp ((z + 2) * x) * thetaCuspWardGibbsAtom n x) =
        (5 / 2 : ℝ) *
            (Real.exp (z * x) * thetaCuspWardGibbsAtom n x) -
          Real.exp (z * x) * deriv (thetaCuspWardGibbsAtom n) x := by
    rw [deriv_thetaCuspWardGibbsAtom_eq_score]
    have he : Real.exp ((z + 2) * x) =
        Real.exp (z * x) * Real.exp (2 * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  calc
    2 * Real.pi * (n : ℝ) ^ (2 : ℕ) *
        thetaCuspWardGibbsExponentialTilt (z + 2) n =
        ∫ x : ℝ in Ioi 0,
          2 * Real.pi * (n : ℝ) ^ (2 : ℕ) *
            (Real.exp ((z + 2) * x) * thetaCuspWardGibbsAtom n x) := by
          rw [thetaCuspWardGibbsExponentialTilt, integral_const_mul]
    _ = ∫ x : ℝ in Ioi 0,
        ((5 / 2 : ℝ) *
            (Real.exp (z * x) * thetaCuspWardGibbsAtom n x) -
          Real.exp (z * x) * deriv (thetaCuspWardGibbsAtom n) x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hpoint x
    _ = (5 / 2 : ℝ) * thetaCuspWardGibbsExponentialTilt z n -
        (∫ x : ℝ in Ioi 0,
          Real.exp (z * x) * deriv (thetaCuspWardGibbsAtom n) x) := by
          rw [integral_sub (hgibbs.const_mul (5 / 2 : ℝ)) hderiv,
            integral_const_mul, thetaCuspWardGibbsExponentialTilt]
    _ = thetaCuspWardGibbsAtom n 0 +
        (z + 5 / 2 : ℝ) * thetaCuspWardGibbsExponentialTilt z n := by
          rw [integral_exp_mul_deriv_thetaCuspWardGibbsAtom_eq hn hz']
          ring

theorem thetaCuspWardGibbsExponentialTilt_neg_half
    {n : ℕ} (hn : 0 < n) :
    thetaCuspWardGibbsExponentialTilt (-1 / 2) n =
      Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) / (2 * Real.pi) := by
  have h := thetaCuspWardGibbsExponentialTilt_shift
    (n := n) hn (z := (-5 / 2 : ℝ)) (by norm_num)
  norm_num at h
  rw [thetaCuspWardGibbsAtom_zero] at h
  have h' : 2 * Real.pi * (n : ℝ) ^ (2 : ℕ) *
      thetaCuspWardGibbsExponentialTilt (-1 / 2) n =
        (n : ℝ) ^ (2 : ℕ) * Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
    convert h using 1
    norm_num
  have hn0 : (n : ℝ) ^ (2 : ℕ) ≠ 0 := by positivity
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  apply (eq_div_iff hpi).2
  apply (mul_left_cancel₀ hn0)
  calc
    (n : ℝ) ^ (2 : ℕ) *
        (thetaCuspWardGibbsExponentialTilt (-1 / 2) n * (2 * Real.pi)) =
        2 * Real.pi * (n : ℝ) ^ (2 : ℕ) *
          thetaCuspWardGibbsExponentialTilt (-1 / 2) n := by ring
    _ = (n : ℝ) ^ (2 : ℕ) * Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := h'
    _ = (n : ℝ) ^ (2 : ℕ) * Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := rfl

theorem thetaCuspSourceExponentialTilt_half
    {n : ℕ} (hn : 0 < n) :
    thetaCuspSourceExponentialTilt (1 / 2) n =
      2 * Real.pi * (n : ℝ) ^ (2 : ℕ) *
        Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  rw [thetaCuspSourceExponentialTilt_eq_wardBoundary hn (by norm_num),
    thetaCuspWardGibbsAtom_zero]
  norm_num
  ring

theorem thetaCuspSourceExponentialTilt_neg_half
    {n : ℕ} (hn : 0 < n) :
    thetaCuspSourceExponentialTilt (-1 / 2) n =
      (2 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 1) *
        Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  rw [thetaCuspSourceExponentialTilt_eq_wardBoundary hn (by norm_num),
    thetaCuspWardGibbsAtom_zero,
    thetaCuspWardGibbsExponentialTilt_neg_half hn]
  field_simp [Real.pi_ne_zero]
  ring

theorem thetaCuspSourceExponentialTilt_half_budget
    {n : ℕ} (hn : 0 < n) :
    thetaCuspSourceExponentialTilt (1 / 2) n +
        thetaCuspSourceExponentialTilt (-1 / 2) n =
      (4 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 1) *
        Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  rw [thetaCuspSourceExponentialTilt_half hn,
    thetaCuspSourceExponentialTilt_neg_half hn]
  ring

theorem integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (z * x) * thetaCuspSourceTerm x n) (Ioi 0) := by
  have h := integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
    thetaCuspSeedPolynomial hn hz
  apply h.congr
  filter_upwards [] with x
  rw [show thetaCuspSourceTerm x n =
      thetaCuspPolynomialAtom thetaCuspSeedPolynomial n x by
    exact congrFun (thetaCuspSourceTerm_eq_polynomialAtom n) x]

/-- The antisymmetric half-density observation is the exact orientation atom. -/
theorem thetaCuspSourceExponentialTilt_half_sub_neg_half
    {n : ℕ} (hn : 0 < n) :
    thetaCuspSourceExponentialTilt (1 / 2) n -
        thetaCuspSourceExponentialTilt (-1 / 2) n =
      Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  rw [thetaCuspSourceExponentialTilt_half hn,
    thetaCuspSourceExponentialTilt_neg_half hn]
  ring

/-- The odd half-density clock observation has an exact value. -/
theorem two_mul_integral_sinh_half_mul_thetaCuspSourceTerm_eq_orientation
    {n : ℕ} (hn : 0 < n) :
    2 * (∫ x : ℝ in Ioi 0,
        Real.sinh (x / 2) * thetaCuspSourceTerm x n) =
      Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  have hplus := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    hn (z := (1 / 2 : ℝ)) (by norm_num)
  have hminus := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    hn (z := (-1 / 2 : ℝ)) (by norm_num)
  calc
    2 * (∫ x : ℝ in Ioi 0,
        Real.sinh (x / 2) * thetaCuspSourceTerm x n) =
        ∫ x : ℝ in Ioi 0,
          2 * (Real.sinh (x / 2) * thetaCuspSourceTerm x n) := by
            rw [integral_const_mul]
    _ = ∫ x : ℝ in Ioi 0,
        (Real.exp ((1 / 2 : ℝ) * x) * thetaCuspSourceTerm x n -
          Real.exp ((-1 / 2 : ℝ) * x) * thetaCuspSourceTerm x n) := by
            apply integral_congr_ae
            filter_upwards [] with x
            rw [Real.sinh_eq]
            have hpos : x / 2 = (1 / 2 : ℝ) * x := by ring
            have hneg : -(x / 2) = (-1 / 2 : ℝ) * x := by ring
            rw [hneg, hpos]
            ring
    _ = thetaCuspSourceExponentialTilt (1 / 2) n -
        thetaCuspSourceExponentialTilt (-1 / 2) n := by
          rw [integral_sub hplus hminus]
          rfl
    _ = Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) :=
      thetaCuspSourceExponentialTilt_half_sub_neg_half hn

theorem integrableOn_first_mul_thetaCuspSourceTerm (n : ℕ) :
    IntegrableOn (fun x : ℝ => x * thetaCuspSourceTerm x n) (Ioi 0) := by
  have hzero : IntegrableOn (fun x : ℝ => thetaCuspSourceTerm x n) (Ioi 0) := by
    simpa using integrableOn_pow_mul_thetaCuspSourceTerm 0 n
  have htwo := integrableOn_pow_mul_thetaCuspSourceTerm 1 n
  have hmajor : IntegrableOn (fun x : ℝ =>
      (1 + x ^ (2 : ℕ)) * thetaCuspSourceTerm x n) (Ioi 0) := by
    have h := hzero.add htwo
    apply h.congr
    filter_upwards [] with x
    simp only [Pi.add_apply]
    ring
  apply Integrable.mono hmajor
  · have hsource : Continuous (fun x : ℝ => thetaCuspSourceTerm x n) := by
      rw [thetaCuspSourceTerm_eq_polynomialAtom]
      exact continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspPolynomialAtom thetaCuspSeedPolynomial n x).continuousAt
    exact (continuous_id.mul hsource).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hs : 0 ≤ thetaCuspSourceTerm x n :=
      thetaCuspSourceTerm_nonneg_of_pos hx n
    have hxbound : x ≤ 1 + x ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.le hs),
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by positivity) hs)]
    exact mul_le_mul_of_nonneg_right hxbound hs

theorem integrableOn_third_mul_thetaCuspSourceTerm (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (3 : ℕ) * thetaCuspSourceTerm x n) (Ioi 0) := by
  have htwo := integrableOn_pow_mul_thetaCuspSourceTerm 1 n
  have hfour := integrableOn_pow_mul_thetaCuspSourceTerm 2 n
  have hmajor : IntegrableOn (fun x : ℝ =>
      (x ^ (2 : ℕ) + x ^ (4 : ℕ)) * thetaCuspSourceTerm x n) (Ioi 0) := by
    have h := htwo.add hfour
    apply h.congr
    filter_upwards [] with x
    simp only [Pi.add_apply]
    ring
  apply Integrable.mono hmajor
  · have hsource : Continuous (fun x : ℝ => thetaCuspSourceTerm x n) := by
      rw [thetaCuspSourceTerm_eq_polynomialAtom]
      exact continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspPolynomialAtom thetaCuspSeedPolynomial n x).continuousAt
    exact ((continuous_id.pow 3).mul hsource).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hs : 0 ≤ thetaCuspSourceTerm x n :=
      thetaCuspSourceTerm_nonneg_of_pos hx n
    have hpoly : 0 ≤ x ^ (2 : ℕ) * (x - 1) ^ (2 : ℕ) := mul_nonneg (sq_nonneg x) (sq_nonneg _)
    have hxbound : x ^ (3 : ℕ) ≤ x ^ (2 : ℕ) + x ^ (4 : ℕ) := by nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx.le 3) hs),
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (add_nonneg (sq_nonneg x) (pow_nonneg hx.le 4)) hs)]
    exact mul_le_mul_of_nonneg_right hxbound hs

theorem integrableOn_sinh_half_mul_thetaCuspSourceTerm
    {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ =>
      Real.sinh (x / 2) * thetaCuspSourceTerm x n) (Ioi 0) := by
  have hplus := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    hn (z := (1 / 2 : ℝ)) (by norm_num)
  have hminus := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    hn (z := (-1 / 2 : ℝ)) (by norm_num)
  have hhalf := (hplus.sub hminus).const_mul (1 / 2 : ℝ)
  apply hhalf.congr
  filter_upwards [] with x
  rw [Real.sinh_eq]
  have hpos : x / 2 = (1 / 2 : ℝ) * x := by ring
  have hneg : -(x / 2) = (-1 / 2 : ℝ) * x := by ring
  rw [hneg, hpos]
  simp only [Pi.sub_apply]
  ring

/-- The exact antisymmetric half-density value controls the first and third odd source moments. -/
theorem thetaCuspSourceOddMomentPair_le_orientation
    {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ in Ioi 0, x * thetaCuspSourceTerm x n) +
        (∫ x : ℝ in Ioi 0, x ^ (3 : ℕ) * thetaCuspSourceTerm x n) / 24 ≤
      Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  have hfirst := integrableOn_first_mul_thetaCuspSourceTerm n
  have hthird := integrableOn_third_mul_thetaCuspSourceTerm n
  have hsinh := integrableOn_sinh_half_mul_thetaCuspSourceTerm hn
  have hleft : IntegrableOn (fun x : ℝ =>
      (x + x ^ (3 : ℕ) / 24) * thetaCuspSourceTerm x n) (Ioi 0) := by
    have h := hfirst.add (hthird.const_mul (1 / 24 : ℝ))
    apply h.congr
    filter_upwards [] with x
    simp only [Pi.add_apply]
    ring
  have hright : IntegrableOn (fun x : ℝ =>
      2 * (Real.sinh (x / 2) * thetaCuspSourceTerm x n)) (Ioi 0) :=
    hsinh.const_mul 2
  have hmono :
      (∫ x : ℝ in Ioi 0,
          (x + x ^ (3 : ℕ) / 24) * thetaCuspSourceTerm x n) ≤
        ∫ x : ℝ in Ioi 0,
          2 * (Real.sinh (x / 2) * thetaCuspSourceTerm x n) := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hs : 0 ≤ thetaCuspSourceTerm x n :=
      thetaCuspSourceTerm_nonneg_of_pos hx n
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (HTGeometry.self_add_cube_div_twenty_four_le_two_sinh_half hx.le) hs
  calc
    (∫ x : ℝ in Ioi 0, x * thetaCuspSourceTerm x n) +
        (∫ x : ℝ in Ioi 0, x ^ (3 : ℕ) * thetaCuspSourceTerm x n) / 24 =
        ∫ x : ℝ in Ioi 0,
          (x + x ^ (3 : ℕ) / 24) * thetaCuspSourceTerm x n := by
            rw [show (fun x : ℝ =>
                (x + x ^ (3 : ℕ) / 24) * thetaCuspSourceTerm x n) =
              fun x => x * thetaCuspSourceTerm x n +
                (1 / 24 : ℝ) * (x ^ (3 : ℕ) * thetaCuspSourceTerm x n) by
                  funext x
                  ring,
              integral_add hfirst (hthird.const_mul (1 / 24 : ℝ)),
              integral_const_mul]
            ring
    _ ≤ ∫ x : ℝ in Ioi 0,
        2 * (Real.sinh (x / 2) * thetaCuspSourceTerm x n) := hmono
    _ = 2 * (∫ x : ℝ in Ioi 0,
        Real.sinh (x / 2) * thetaCuspSourceTerm x n) := by
          rw [integral_const_mul]
    _ = Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) :=
      two_mul_integral_sinh_half_mul_thetaCuspSourceTerm_eq_orientation hn

/-- Cauchy--Schwarz makes the second source moment log-convex between the two odd moments. -/
theorem thetaCuspSourceSecondMoment_sq_le_first_mul_third
    (n : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ (2 : ℕ) * thetaCuspSourceTerm x n) ^ (2 : ℕ) ≤
      (∫ x : ℝ in Ioi 0, x * thetaCuspSourceTerm x n) *
        ∫ x : ℝ in Ioi 0, x ^ (3 : ℕ) * thetaCuspSourceTerm x n := by
  have hsource : Continuous (fun x : ℝ => thetaCuspSourceTerm x n) := by
    rw [thetaCuspSourceTerm_eq_polynomialAtom]
    exact continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspPolynomialAtom thetaCuspSeedPolynomial n x).continuousAt
  have hX : AEStronglyMeasurable (fun x : ℝ => x)
      (volume.restrict (Ioi 0)) := continuous_id.aestronglyMeasurable
  have hsourceMeas : AEStronglyMeasurable (fun x : ℝ => thetaCuspSourceTerm x n)
      (volume.restrict (Ioi 0)) := hsource.aestronglyMeasurable
  have hXnonneg : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Ioi 0), 0 ≤ x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hx.le
  have hsourcenonneg : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Ioi 0),
      0 ≤ thetaCuspSourceTerm x n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact thetaCuspSourceTerm_nonneg_of_pos hx n
  simpa using HTGeometry.sq_second_observation_le_first_mul_third
    hX hsourceMeas hXnonneg hsourcenonneg
      (integrableOn_first_mul_thetaCuspSourceTerm n)
      (integrableOn_third_mul_thetaCuspSourceTerm n)

/-- The odd half-density orientation closes a square budget for the second source moment. -/
theorem thetaCuspSourceSecondMoment_sq_le_six_orientation_sq
    {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ in Ioi 0, x ^ (2 : ℕ) * thetaCuspSourceTerm x n) ^ (2 : ℕ) ≤
      6 * Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have hmfirst : 0 ≤ ∫ x : ℝ in Ioi 0,
      x * thetaCuspSourceTerm x n := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg hx.le (thetaCuspSourceTerm_nonneg_of_pos hx n)
  have hmthird : 0 ≤ ∫ x : ℝ in Ioi 0,
      x ^ (3 : ℕ) * thetaCuspSourceTerm x n := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le 3) (thetaCuspSourceTerm_nonneg_of_pos hx n)
  exact HTGeometry.sq_second_observation_le_six_budget_sq
    hmfirst hmthird (thetaCuspSourceSecondMoment_sq_le_first_mul_third n)
      (thetaCuspSourceOddMomentPair_le_orientation hn)

/-- The first nonconstant raw atom moment is bounded solely by the antisymmetric observation. -/
theorem thetaCuspAtomRawEvenMoment_one_sq_le_twenty_four_orientation_sq
    {n : ℕ} (hn : 0 < n) :
    thetaCuspAtomRawEvenMoment 1 n ^ (2 : ℕ) ≤
      24 * Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have h := thetaCuspSourceSecondMoment_sq_le_six_orientation_sq hn
  rw [thetaCuspAtomRawEvenMoment]
  simp only [Nat.mul_one]
  nlinarith

theorem thetaCuspAtomRawEvenMoment_one_le_five_mul_orientation
    {n : ℕ} (hn : 0 < n) :
    thetaCuspAtomRawEvenMoment 1 n ≤
      5 * Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  let a := thetaCuspAtomRawEvenMoment 1 n
  let d := Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ))
  have hsq : a ^ (2 : ℕ) ≤ 24 * d ^ (2 : ℕ) := by
    simpa only [a, d] using
      thetaCuspAtomRawEvenMoment_one_sq_le_twenty_four_orientation_sq hn
  have ha : 0 ≤ a := by
    exact thetaCuspAtomRawEvenMoment_nonneg 1 n
  have hd : 0 < d := Real.exp_pos _
  show a ≤ 5 * d
  by_contra hnot
  have hleft : 0 < a - 5 * d := sub_pos.mpr (lt_of_not_ge hnot)
  have hright : 0 < a + 5 * d := by positivity
  have hprod : 0 < (a - 5 * d) * (a + 5 * d) := mul_pos hleft hright
  have hd2 : 0 < d ^ (2 : ℕ) := sq_pos_of_pos hd
  nlinarith

theorem two_pi_mul_thetaCuspFirstAtomWardMoment_one_sq_le_orientation_sq :
    (2 * Real.pi * thetaCuspFirstAtomWardMoment 1) ^ (2 : ℕ) ≤
      24 * Real.exp (-Real.pi) ^ (2 : ℕ) := by
  rw [← thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 1]
  simpa using thetaCuspAtomRawEvenMoment_one_sq_le_twenty_four_orientation_sq
    (n := 1) (by norm_num)

theorem two_pi_mul_thetaCuspFirstAtomWardMoment_one_le_five_exp_neg_pi :
    2 * Real.pi * thetaCuspFirstAtomWardMoment 1 ≤
      5 * Real.exp (-Real.pi) := by
  rw [← thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 1]
  simpa using thetaCuspAtomRawEvenMoment_one_le_five_mul_orientation
    (n := 1) (by norm_num)

/-- Any proof of the live relaxed fourth-moment first-atom hypothesis must satisfy this explicit
half-density cap.  This is a useful feasibility constraint, not a proof of that hypothesis. -/
theorem relaxedFourthMoment_firstAtom_hypothesis_implies_halfDensity_cap
    (hfirst :
      16 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1) *
          ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) ≤
        45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ)) :
    16 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1) *
          ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) ≤
      1080 * Real.exp (-Real.pi) ^ (2 : ℕ) := by
  calc
    _ ≤ 45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ) := hfirst
    _ ≤ 45 * (24 * Real.exp (-Real.pi) ^ (2 : ℕ)) := by
      gcongr
      simpa using thetaCuspAtomRawEvenMoment_one_sq_le_twenty_four_orientation_sq
        (n := 1) (by norm_num)
    _ = 1080 * Real.exp (-Real.pi) ^ (2 : ℕ) := by ring

/-- The zeroth raw atom moment is twice the unweighted source observation. -/
theorem thetaCuspAtomRawEvenMoment_zero_eq_two_mul_tilt_zero (n : ℕ) :
    thetaCuspAtomRawEvenMoment 0 n =
      2 * thetaCuspSourceExponentialTilt 0 n := by
  rw [thetaCuspAtomRawEvenMoment, thetaCuspSourceExponentialTilt]
  simp

/-- Hellinger/Cauchy fidelity for the two opposite half-density observation channels. -/
theorem thetaCuspSourceExponentialTilt_zero_sq_le_half_mul_neg_half
    {n : ℕ} (hn : 0 < n) :
    thetaCuspSourceExponentialTilt 0 n ^ (2 : ℕ) ≤
      thetaCuspSourceExponentialTilt (1 / 2) n *
        thetaCuspSourceExponentialTilt (-1 / 2) n := by
  have hsource : Continuous (fun x : ℝ => thetaCuspSourceTerm x n) := by
    rw [thetaCuspSourceTerm_eq_polynomialAtom]
    exact continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspPolynomialAtom thetaCuspSeedPolynomial n x).continuousAt
  have hφ : AEStronglyMeasurable (fun x : ℝ => (1 / 2 : ℝ) * x)
      (volume.restrict (Ioi 0)) :=
    (continuous_const.mul continuous_id).aestronglyMeasurable
  have hρ : AEStronglyMeasurable (fun x : ℝ => thetaCuspSourceTerm x n)
      (volume.restrict (Ioi 0)) :=
    hsource.aestronglyMeasurable
  have hρnonneg : ∀ᵐ x ∂volume.restrict (Ioi 0),
      0 ≤ thetaCuspSourceTerm x n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact thetaCuspSourceTerm_nonneg_of_pos hx n
  have hplus := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    hn (z := (1 / 2 : ℝ)) (by norm_num)
  have hminus := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    hn (z := (-1 / 2 : ℝ)) (by norm_num)
  have hminus' : Integrable (fun x : ℝ =>
      Real.exp (-((1 / 2 : ℝ) * x)) * thetaCuspSourceTerm x n)
      (volume.restrict (Ioi 0)) := by
    apply hminus.congr
    filter_upwards [] with x
    congr 2
    ring
  have h := HTGeometry.sq_integral_le_exponential_tilt_product
    hφ hρ hρnonneg hplus hminus'
  have hneg : (∫ x : ℝ in Ioi 0,
      Real.exp (-((1 / 2 : ℝ) * x)) * thetaCuspSourceTerm x n) =
      thetaCuspSourceExponentialTilt (-1 / 2) n := by
    rw [thetaCuspSourceExponentialTilt]
    apply integral_congr_ae
    filter_upwards [] with x
    congr 2
    ring
  rw [hneg] at h
  simpa only [thetaCuspSourceExponentialTilt, zero_mul, Real.exp_zero, one_mul,
    neg_mul] using h

/-- The antisymmetric observation is the exact fidelity deficit in the symmetric square budget. -/
theorem thetaCuspAtomRawEvenMoment_zero_sq_add_orientation_sq_le_budget_sq
    {n : ℕ} (hn : 0 < n) :
    thetaCuspAtomRawEvenMoment 0 n ^ (2 : ℕ) +
        Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
      ((4 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 1) *
        Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ))) ^ (2 : ℕ) := by
  have hcs :=
    thetaCuspSourceExponentialTilt_zero_sq_le_half_mul_neg_half hn
  rw [thetaCuspAtomRawEvenMoment_zero_eq_two_mul_tilt_zero,
    ← thetaCuspSourceExponentialTilt_half_budget hn,
    ← thetaCuspSourceExponentialTilt_half_sub_neg_half hn]
  nlinarith

/-- Fidelity makes the half-density upper budget for the zeroth atom moment strict. -/
theorem thetaCuspAtomRawEvenMoment_zero_lt_halfDensityBudget
    {n : ℕ} (hn : 0 < n) :
    thetaCuspAtomRawEvenMoment 0 n <
      (4 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 1) *
        Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  have hsq :=
    thetaCuspAtomRawEvenMoment_zero_sq_add_orientation_sq_le_budget_sq hn
  have hm : 0 ≤ thetaCuspAtomRawEvenMoment 0 n :=
    thetaCuspAtomRawEvenMoment_nonneg 0 n
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnsq : (1 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by nlinarith
  have hcoef : 0 < 4 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 1 := by
    nlinarith [Real.pi_gt_three]
  have hbudget : 0 < (4 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 1) *
      Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) :=
    mul_pos hcoef (Real.exp_pos _)
  have horient : 0 < Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := Real.exp_pos _
  nlinarith

theorem thetaCuspFirstAtomRawEvenMoment_zero_lt_halfDensityBudget :
    thetaCuspAtomRawEvenMoment 0 1 <
      (4 * Real.pi - 1) * Real.exp (-Real.pi) := by
  simpa using thetaCuspAtomRawEvenMoment_zero_lt_halfDensityBudget
    (n := 1) (by norm_num)

/-- The fidelity deficit directly supplies a strict symbolic lower bound for the existing zeroth
Liouville--Gibbs moment. -/
theorem exp_orientation_lt_two_pi_mul_thetaCuspLiouvilleGibbsMoment_zero
    {n : ℕ} (hn : 0 < n) :
    Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) <
      2 * Real.pi * thetaCuspLiouvilleGibbsMoment 0 n := by
  have h := thetaCuspAtomRawEvenMoment_zero_lt_halfDensityBudget hn
  rw [thetaCuspAtomRawEvenMoment_zero_eq_liouvilleGibbs hn,
    thetaCuspLiouvilleGibbsAtom_zero] at h
  nlinarith

theorem exp_neg_pi_lt_two_pi_mul_firstLiouvilleGibbsMoment_zero :
    Real.exp (-Real.pi) <
      2 * Real.pi * thetaCuspLiouvilleGibbsMoment 0 1 := by
  simpa using
    exp_orientation_lt_two_pi_mul_thetaCuspLiouvilleGibbsMoment_zero
      (n := 1) (by norm_num)

theorem integrableOn_cosh_half_mul_thetaCuspSourceTerm
    {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ =>
      Real.cosh (x / 2) * thetaCuspSourceTerm x n) (Ioi 0) := by
  have hplus := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    hn (z := (1 / 2 : ℝ)) (by norm_num)
  have hminus := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    hn (z := (-1 / 2 : ℝ)) (by norm_num)
  have hsum := hplus.add hminus
  have hhalf := hsum.const_mul (1 / 2 : ℝ)
  apply hhalf.congr
  filter_upwards [] with x
  rw [Real.cosh_eq]
  have hpos : x / 2 = (1 / 2 : ℝ) * x := by ring
  have hneg : -(x / 2) = (-1 / 2 : ℝ) * x := by ring
  rw [hneg, hpos]
  simp only [Pi.add_apply]
  ring

theorem two_mul_integral_cosh_half_mul_thetaCuspSourceTerm_eq_budget
    {n : ℕ} (hn : 0 < n) :
    2 * (∫ x : ℝ in Ioi 0,
        Real.cosh (x / 2) * thetaCuspSourceTerm x n) =
      (4 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 1) *
        Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  have hplus := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    hn (z := (1 / 2 : ℝ)) (by norm_num)
  have hminus := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
    hn (z := (-1 / 2 : ℝ)) (by norm_num)
  calc
    2 * (∫ x : ℝ in Ioi 0,
        Real.cosh (x / 2) * thetaCuspSourceTerm x n) =
        ∫ x : ℝ in Ioi 0,
          2 * (Real.cosh (x / 2) * thetaCuspSourceTerm x n) := by
            rw [integral_const_mul]
    _ = ∫ x : ℝ in Ioi 0,
        (Real.exp ((1 / 2 : ℝ) * x) * thetaCuspSourceTerm x n +
          Real.exp ((-1 / 2 : ℝ) * x) * thetaCuspSourceTerm x n) := by
            apply integral_congr_ae
            filter_upwards [] with x
            rw [Real.cosh_eq]
            have hpos : x / 2 = (1 / 2 : ℝ) * x := by ring
            have hneg : -(x / 2) = (-1 / 2 : ℝ) * x := by ring
            rw [hneg, hpos]
            ring
    _ = thetaCuspSourceExponentialTilt (1 / 2) n +
        thetaCuspSourceExponentialTilt (-1 / 2) n := by
          rw [integral_add hplus hminus]
          rfl
    _ = (4 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 1) *
        Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) :=
      thetaCuspSourceExponentialTilt_half_budget hn

theorem thetaCuspAtomRawEvenMoment_zero_le_halfDensityBudget
    {n : ℕ} (hn : 0 < n) :
    thetaCuspAtomRawEvenMoment 0 n ≤
      (4 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 1) *
        Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  have hsource : IntegrableOn (fun x : ℝ => thetaCuspSourceTerm x n) (Ioi 0) := by
    simpa using integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
      hn (z := (0 : ℝ)) (by norm_num)
  have hcosh := integrableOn_cosh_half_mul_thetaCuspSourceTerm hn
  have hmono : (∫ x : ℝ in Ioi 0, thetaCuspSourceTerm x n) ≤
      ∫ x : ℝ in Ioi 0,
        Real.cosh (x / 2) * thetaCuspSourceTerm x n := by
    apply integral_mono_ae hsource hcosh
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hf : 0 ≤ thetaCuspSourceTerm x n :=
      thetaCuspSourceTerm_nonneg_of_pos hx n
    nlinarith [Real.one_le_cosh (x / 2)]
  rw [thetaCuspAtomRawEvenMoment]
  simp only [Nat.mul_zero, pow_zero, one_mul]
  rw [← two_mul_integral_cosh_half_mul_thetaCuspSourceTerm_eq_budget hn]
  linarith

theorem thetaCuspFirstAtomRawEvenMoment_zero_le_halfDensityBudget :
    thetaCuspAtomRawEvenMoment 0 1 ≤
      (4 * Real.pi - 1) * Real.exp (-Real.pi) := by
  simpa using thetaCuspAtomRawEvenMoment_zero_le_halfDensityBudget
    (n := 1) (by norm_num)

theorem one_add_sq_div_two_le_cosh (u : ℝ) :
    1 + u ^ (2 : ℕ) / 2 ≤ Real.cosh u := by
  rw [Real.cosh_eq_tsum]
  have hsum := (Real.hasSum_cosh u).summable.sum_le_tsum
    (Finset.range 2) (fun n _hn => by
      rw [pow_mul]
      positivity)
  norm_num [Finset.sum_range_succ] at hsum ⊢
  simpa [pow_two] using hsum

theorem one_add_sq_div_eight_le_cosh_half (x : ℝ) :
    1 + x ^ (2 : ℕ) / 8 ≤ Real.cosh (x / 2) := by
  have h := one_add_sq_div_two_le_cosh (x / 2)
  convert h using 1
  ring

theorem thetaCuspFirstAtomMomentPair_le_halfDensityBudget :
    thetaCuspAtomRawEvenMoment 0 1 +
        thetaCuspAtomRawEvenMoment 1 1 / 8 ≤
      (4 * Real.pi - 1) * Real.exp (-Real.pi) := by
  have h0 : IntegrableOn (fun x : ℝ => thetaCuspSourceTerm x 1) (Ioi 0) := by
    simpa using integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
      (n := 1) (by norm_num) (z := (0 : ℝ)) (by norm_num)
  have hcosh := integrableOn_cosh_half_mul_thetaCuspSourceTerm (n := 1) (by norm_num)
  have h1 : IntegrableOn (fun x : ℝ => x ^ (2 : ℕ) * thetaCuspSourceTerm x 1) (Ioi 0) := by
    have hmajor := hcosh.const_mul 8
    apply Integrable.mono hmajor
    · exact (continuous_id.pow 2).aestronglyMeasurable.mul h0.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hf : 0 ≤ thetaCuspSourceTerm x 1 :=
        thetaCuspSourceTerm_nonneg_of_pos hx 1
      have hcosh0 : 0 ≤ Real.cosh (x / 2) := (Real.cosh_pos _).le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg x), abs_of_nonneg hf,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) (mul_nonneg hcosh0 hf))]
      have hbound := one_add_sq_div_eight_le_cosh_half x
      nlinarith
  have hpair : IntegrableOn (fun x : ℝ =>
      (1 + x ^ (2 : ℕ) / 8) * thetaCuspSourceTerm x 1) (Ioi 0) := by
    have h := h0.add (h1.const_mul (1 / 8 : ℝ))
    apply h.congr
    filter_upwards [] with x
    simp only [Pi.add_apply]
    ring
  have hmono : (∫ x : ℝ in Ioi 0,
      (1 + x ^ (2 : ℕ) / 8) * thetaCuspSourceTerm x 1) ≤
      ∫ x : ℝ in Ioi 0,
        Real.cosh (x / 2) * thetaCuspSourceTerm x 1 := by
    apply integral_mono_ae hpair hcosh
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hf : 0 ≤ thetaCuspSourceTerm x 1 :=
      thetaCuspSourceTerm_nonneg_of_pos hx 1
    exact mul_le_mul_of_nonneg_right
      (one_add_sq_div_eight_le_cosh_half x) hf
  rw [thetaCuspAtomRawEvenMoment, thetaCuspAtomRawEvenMoment]
  simp only [Nat.mul_zero, pow_zero, one_mul, Nat.mul_one]
  have hbudget : 2 * (∫ x : ℝ in Ioi 0,
      Real.cosh (x / 2) * thetaCuspSourceTerm x 1) =
      (4 * Real.pi - 1) * Real.exp (-Real.pi) := by
    simpa using two_mul_integral_cosh_half_mul_thetaCuspSourceTerm_eq_budget
      (n := 1) (by norm_num)
  rw [← hbudget]
  have hpair' :
      (∫ x : ℝ in Ioi 0,
        (1 + x ^ (2 : ℕ) / 8) * thetaCuspSourceTerm x 1) =
      (∫ x : ℝ in Ioi 0, thetaCuspSourceTerm x 1) +
        (1 / 8 : ℝ) *
          (∫ x : ℝ in Ioi 0, x ^ (2 : ℕ) * thetaCuspSourceTerm x 1) := by
    calc
      _ = ∫ x : ℝ in Ioi 0,
          (thetaCuspSourceTerm x 1 +
            (1 / 8 : ℝ) * (x ^ (2 : ℕ) * thetaCuspSourceTerm x 1)) := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = _ := by rw [integral_add h0 (h1.const_mul (1 / 8 : ℝ)), integral_const_mul]
  rw [hpair'] at hmono
  linarith

/-! ### Completed-source and higher-tail half-density budgets -/

/-- Every real exponential tilt strictly inside the Fourier--Laplace strip is integrable. -/
theorem integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one
    {a : ℝ} (ha : |a| < 1) :
    Integrable (fun x : ℝ => Real.exp (a * x) * thetaCuspFullSource x) := by
  simpa only [thetaCuspTiltedSchwartzReal_apply, thetaCuspTiltedSource] using!
    (thetaCuspTiltedSchwartzReal a ha).integrable (μ := (volume : Measure ℝ))

/-- The positive half-density tilt of the completed source is the endpoint value `XiC (I/2)`. -/
theorem integral_exp_half_mul_thetaCuspFullSource_eq_half :
    (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x) = 1 / 2 := by
  have hw : (I / 2 : ℂ) ∈ thetaCuspFourierLaplaceStrip := by
    simp [thetaCuspFourierLaplaceStrip]
    norm_num
  have hXi := thetaCuspFourierLaplace_eq_XiC_on_strip hw
  rw [XiC_I_half_eq] at hXi
  rw [thetaCuspFourierLaplace] at hXi
  have hfun : thetaCuspFourierLaplaceIntegrand (I / 2) =
      fun x : ℝ => ((Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ) := by
    funext x
    rw [thetaCuspFourierLaplaceIntegrand]
    have harg : -I * (I / 2) * (x : ℂ) =
        (((1 / 2 : ℝ) * x : ℝ) : ℂ) := by
      push_cast
      field_simp
      rw [I_sq]
      ring
    rw [harg, ← Complex.ofReal_exp]
    norm_cast
  rw [hfun] at hXi
  change (∫ x : ℝ,
      ((Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ)) =
        (1 / 2 : ℂ) at hXi
  have hcoe := integral_ofReal (X := ℝ) (μ := (volume : Measure ℝ))
    (𝕜 := ℂ)
    (f := fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x)
  apply Complex.ofReal_injective
  calc
    ((∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ) =
        ∫ x : ℝ,
          ((Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ) := hcoe.symm
    _ = ((1 / 2 : ℝ) : ℂ) := by simpa using hXi

theorem integrableOn_cosh_half_mul_thetaCuspFullSource :
    IntegrableOn (fun x : ℝ =>
      Real.cosh (x / 2) * thetaCuspFullSource x) (Ioi 0) := by
  have hplus : IntegrableOn (fun x : ℝ =>
      Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x) (Ioi 0) :=
    (integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one
      (a := (1 / 2 : ℝ)) (by norm_num)).integrableOn
  have hminus : IntegrableOn (fun x : ℝ =>
      Real.exp ((-1 / 2 : ℝ) * x) * thetaCuspFullSource x) (Ioi 0) :=
    (integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one
      (a := (-1 / 2 : ℝ)) (by norm_num)).integrableOn
  have hsum := hplus.add hminus
  have hhalf := hsum.const_mul (1 / 2 : ℝ)
  apply hhalf.congr
  filter_upwards [] with x
  rw [Real.cosh_eq]
  have hpos : x / 2 = (1 / 2 : ℝ) * x := by ring
  have hneg : -(x / 2) = (-1 / 2 : ℝ) * x := by ring
  rw [hneg, hpos]
  simp only [Pi.add_apply]
  ring

/-- Reflection turns the full-line endpoint value into the positive-half-line cosh budget. -/
theorem two_mul_integral_cosh_half_mul_thetaCuspFullSource_eq_half :
    2 * (∫ x : ℝ in Ioi 0,
        Real.cosh (x / 2) * thetaCuspFullSource x) = 1 / 2 := by
  let p : ℝ → ℝ := fun x =>
    Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x
  let m : ℝ → ℝ := fun x =>
    Real.exp ((-1 / 2 : ℝ) * x) * thetaCuspFullSource x
  have hp : Integrable p := by
    simpa only [p] using integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one
      (a := (1 / 2 : ℝ)) (by norm_num)
  have hm : Integrable m := by
    simpa only [m] using integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one
      (a := (-1 / 2 : ℝ)) (by norm_num)
  have hm_eq_neg : m = fun x => p (-x) := by
    funext x
    simp only [m, p]
    rw [thetaCuspFullSource_neg]
    congr 2
    ring
  calc
    2 * (∫ x : ℝ in Ioi 0,
        Real.cosh (x / 2) * thetaCuspFullSource x) =
        ∫ x : ℝ in Ioi 0,
          2 * (Real.cosh (x / 2) * thetaCuspFullSource x) := by
      rw [integral_const_mul]
    _ = ∫ x : ℝ in Ioi 0, p x + m x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [p, m]
      rw [Real.cosh_eq]
      have hpos : x / 2 = (1 / 2 : ℝ) * x := by ring
      have hneg : -(x / 2) = (-1 / 2 : ℝ) * x := by ring
      rw [hneg, hpos]
      ring
    _ = (∫ x : ℝ in Ioi 0, p x) + (∫ x : ℝ in Ioi 0, m x) := by
      rw [integral_add hp.integrableOn hm.integrableOn]
    _ = (∫ x : ℝ in Ioi 0, p x) + (∫ x : ℝ in Iic 0, p x) := by
      rw [hm_eq_neg, integral_comp_neg_Ioi]
      norm_num
    _ = ∫ x : ℝ, p x := by
      rw [add_comm]
      exact intervalIntegral.integral_Iic_add_Ioi hp.integrableOn hp.integrableOn
    _ = 1 / 2 := by
      simpa only [p] using integral_exp_half_mul_thetaCuspFullSource_eq_half

/-- The exact half-density mass remaining after removing the first theta atom. -/
def thetaCuspHigherHalfDensityBudget : ℝ :=
  1 / 2 - (4 * Real.pi - 1) * Real.exp (-Real.pi)

theorem integrableOn_cosh_half_mul_thetaCuspHigherSource :
    IntegrableOn (fun x : ℝ => Real.cosh (x / 2) *
      (thetaCuspFullSource x - thetaCuspSourceTerm x 1)) (Ioi 0) := by
  have hfull := integrableOn_cosh_half_mul_thetaCuspFullSource
  have hfirst := integrableOn_cosh_half_mul_thetaCuspSourceTerm
    (n := 1) (by norm_num)
  have hsub := hfull.sub hfirst
  apply hsub.congr
  filter_upwards [] with x
  simp only [Pi.sub_apply]
  ring

/-- The higher theta atoms exhaust exactly the completed budget minus the first-atom budget. -/
theorem two_mul_integral_cosh_half_mul_thetaCuspHigherSource_eq_budget :
    2 * (∫ x : ℝ in Ioi 0, Real.cosh (x / 2) *
      (thetaCuspFullSource x - thetaCuspSourceTerm x 1)) =
        thetaCuspHigherHalfDensityBudget := by
  have hfull := integrableOn_cosh_half_mul_thetaCuspFullSource
  have hfirst := integrableOn_cosh_half_mul_thetaCuspSourceTerm
    (n := 1) (by norm_num)
  have hfullValue := two_mul_integral_cosh_half_mul_thetaCuspFullSource_eq_half
  have hfirstValue :=
    two_mul_integral_cosh_half_mul_thetaCuspSourceTerm_eq_budget
      (n := 1) (by norm_num)
  rw [show (fun x : ℝ => Real.cosh (x / 2) *
      (thetaCuspFullSource x - thetaCuspSourceTerm x 1)) =
      fun x : ℝ => Real.cosh (x / 2) * thetaCuspFullSource x -
        Real.cosh (x / 2) * thetaCuspSourceTerm x 1 by
    funext x
    ring,
    integral_sub hfull hfirst]
  rw [thetaCuspHigherHalfDensityBudget]
  norm_num at hfirstValue
  nlinarith

theorem thetaCuspHigherAtomRawEvenMoment_eq_integral_tail (j : ℕ) :
    thetaCuspHigherAtomRawEvenMoment j =
      2 * ∫ x : ℝ in Ioi 0, x ^ (2 * j) *
        (thetaCuspFullSource x - thetaCuspSourceTerm x 1) := by
  have hfull := integrableOn_thetaCuspRawMoment (2 * j)
  have hfirst := integrableOn_pow_mul_thetaCuspSourceTerm j 1
  rw [thetaCuspHigherAtomRawEvenMoment, thetaCuspRawEvenMoment,
    thetaCuspAtomRawEvenMoment, ← mul_sub, ← integral_sub hfull hfirst]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- The first two positive Taylor terms of the higher source fit inside its exact reflected
half-density budget. -/
theorem thetaCuspHigherAtomMomentPair_le_halfDensityBudget :
    thetaCuspHigherAtomRawEvenMoment 0 +
        thetaCuspHigherAtomRawEvenMoment 1 / 8 ≤
      thetaCuspHigherHalfDensityBudget := by
  let h : ℝ → ℝ := fun x =>
    thetaCuspFullSource x - thetaCuspSourceTerm x 1
  have h0 : IntegrableOn h (Ioi 0) := by
    have hfull := integrableOn_thetaCuspRawMoment 0
    have hfirst := integrableOn_pow_mul_thetaCuspSourceTerm 0 1
    have hsub := hfull.sub hfirst
    apply hsub.congr
    filter_upwards [] with x
    simp only [Pi.sub_apply, Nat.mul_zero, pow_zero, one_mul, h]
  have h1 : IntegrableOn (fun x : ℝ => x ^ (2 : ℕ) * h x) (Ioi 0) := by
    have hfull := integrableOn_thetaCuspRawMoment 2
    have hfirst := integrableOn_pow_mul_thetaCuspSourceTerm 1 1
    have hsub := hfull.sub hfirst
    apply hsub.congr
    filter_upwards [] with x
    simp only [Pi.sub_apply, Nat.mul_one, h]
    ring
  have hpair : IntegrableOn (fun x : ℝ => (1 + x ^ (2 : ℕ) / 8) * h x) (Ioi 0) := by
    have hi := h0.add (h1.const_mul (1 / 8 : ℝ))
    apply hi.congr
    filter_upwards [] with x
    simp only [Pi.add_apply]
    ring
  have hcosh : IntegrableOn (fun x : ℝ => Real.cosh (x / 2) * h x) (Ioi 0) := by
    simpa only [h] using integrableOn_cosh_half_mul_thetaCuspHigherSource
  have hmono : (∫ x : ℝ in Ioi 0, (1 + x ^ (2 : ℕ) / 8) * h x) ≤
      ∫ x : ℝ in Ioi 0, Real.cosh (x / 2) * h x := by
    apply integral_mono_ae hpair hcosh
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hterm : thetaCuspSourceTerm x 1 ≤ thetaCuspFullSource x := by
      rw [thetaCuspFullSource]
      exact (summable_thetaCuspSourceTerm x).le_tsum 1
        (fun n _ => thetaCuspSourceTerm_nonneg_of_pos hx n)
    exact mul_le_mul_of_nonneg_right
      (one_add_sq_div_eight_le_cosh_half x) (sub_nonneg.mpr hterm)
  have hpairEq : (∫ x : ℝ in Ioi 0, (1 + x ^ (2 : ℕ) / 8) * h x) =
      (∫ x : ℝ in Ioi 0, h x) +
        (1 / 8 : ℝ) * (∫ x : ℝ in Ioi 0, x ^ (2 : ℕ) * h x) := by
    calc
      _ = ∫ x : ℝ in Ioi 0,
          (h x + (1 / 8 : ℝ) * (x ^ (2 : ℕ) * h x)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := by rw [integral_add h0 (h1.const_mul (1 / 8 : ℝ)), integral_const_mul]
  have hbudget := two_mul_integral_cosh_half_mul_thetaCuspHigherSource_eq_budget
  rw [thetaCuspHigherAtomRawEvenMoment_eq_integral_tail,
    thetaCuspHigherAtomRawEvenMoment_eq_integral_tail]
  simp only [Nat.mul_zero, pow_zero, one_mul, Nat.mul_one]
  simp only [h] at hmono hpairEq hbudget ⊢
  rw [hpairEq] at hmono
  nlinarith

theorem thetaCuspHigherAtomRawEvenMoment_zero_le_halfDensityBudget :
    thetaCuspHigherAtomRawEvenMoment 0 ≤ thetaCuspHigherHalfDensityBudget := by
  have hpair := thetaCuspHigherAtomMomentPair_le_halfDensityBudget
  have hnonneg := thetaCuspHigherAtomRawEvenMoment_nonneg 1
  linarith

/-- The closed higher-tail constant is nonnegative without numerical evaluation. -/
theorem thetaCuspHigherHalfDensityBudget_nonneg :
    0 ≤ thetaCuspHigherHalfDensityBudget :=
  (thetaCuspHigherAtomRawEvenMoment_nonneg 0).trans
    thetaCuspHigherAtomRawEvenMoment_zero_le_halfDensityBudget

/-- Direct completed-source consumer: the zeroth and second raw moments occupy at most the full
half-density observation budget. -/
theorem thetaCuspRawEvenMomentPair_le_fullHalfDensityBudget :
    thetaCuspRawEvenMoment 0 + thetaCuspRawEvenMoment 1 / 8 ≤ 1 / 2 := by
  rw [thetaCuspRawEvenMoment_eq_one_add_higher,
    thetaCuspRawEvenMoment_eq_one_add_higher]
  have hfirst := thetaCuspFirstAtomMomentPair_le_halfDensityBudget
  have hhigher := thetaCuspHigherAtomMomentPair_le_halfDensityBudget
  rw [thetaCuspHigherHalfDensityBudget] at hhigher
  linarith

/-- The exact reflected tail budget replaces a free zeroth-moment remainder hypothesis. -/
theorem thetaCuspRawEvenMoment_zero_le_first_add_higherHalfDensityBudget :
    thetaCuspRawEvenMoment 0 ≤
      thetaCuspAtomRawEvenMoment 0 1 + thetaCuspHigherHalfDensityBudget := by
  rw [thetaCuspRawEvenMoment_eq_one_add_higher]
  simpa [add_comm] using
    add_le_add_left thetaCuspHigherAtomRawEvenMoment_zero_le_halfDensityBudget
      (thetaCuspAtomRawEvenMoment 0 1)

end

end RHTower
