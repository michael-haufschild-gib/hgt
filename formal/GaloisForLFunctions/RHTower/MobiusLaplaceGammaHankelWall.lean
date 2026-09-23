import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangle
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Gamma--Hankel localization of finite Möbius--Laplace energy

For a finite real coefficient vector `a`, its Laplace pencil

`F_N(x) = sum_{n<N} a_n exp(-(n+1)x)`

has exact weighted energy

`integral_0^infinity x^(r-1) F_N(x)^(2 : ℕ) dx
  = Gamma(r) sum_{m,n<N} a_m a_n / (m+n+2)^r`.

Thus archimedean Gamma localization does not diagonalize the source channels.  It turns them into
the positive Hankel kernel `(m+n+2)^(-r)`, retaining every additive cross correlation.  The final
specialization uses shifted Möbius coefficients and supplies the finite kernel identity behind the
Gamma-weighted height formulation of the Möbius--Laplace frontier.

No zero data, RH assumption, asymptotic estimate, or numerical computation enters this module.
-/

open Complex Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Finite Laplace pencil with frequencies `1,...,N`. -/
def finiteRealLaplacePencil (a : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, a n * Real.exp (-((n + 1 : ℕ) : ℝ) * x)

/-- Gamma--Hankel quadratic energy of a finite real coefficient vector. -/
def finiteGammaHankelEnergy (a : ℕ → ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  Real.Gamma r * ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
    a m * a n / (((m + n + 2 : ℕ) : ℝ) ^ r)

/-- One entry of the Gamma--Hankel matrix is the Mellin moment of one Laplace cross term. -/
private theorem integral_gamma_hankel_atom
    {r : ℝ} (hr : 0 < r) (m n : ℕ) :
    (∫ x : ℝ in Ioi 0,
      x ^ (r - 1) * Real.exp (-(((m + n + 2 : ℕ) : ℝ) * x))) =
      Real.Gamma r / (((m + n + 2 : ℕ) : ℝ) ^ r) := by
  have hb : 0 < (((m + n + 2 : ℕ) : ℝ)) := by positivity
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := r - 1) (b := ((m + n + 2 : ℕ) : ℝ))
    (by norm_num) (by linarith) hb
  calc
    (∫ x : ℝ in Ioi 0,
        x ^ (r - 1) * Real.exp (-(((m + n + 2 : ℕ) : ℝ) * x))) =
        ∫ x : ℝ in Ioi 0,
          x ^ (r - 1) * Real.exp
            (-((m + n + 2 : ℕ) : ℝ) * x ^ (1 : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      have hxpow : x ^ (1 : ℝ) = x := Real.rpow_one x
      rw [hxpow]
      congr 2
      ring
    _ = (((m + n + 2 : ℕ) : ℝ)) ^
          (-(r - 1 + 1) / (1 : ℝ)) * (1 / (1 : ℝ)) *
            Real.Gamma ((r - 1 + 1) / (1 : ℝ)) := h
    _ = Real.Gamma r / (((m + n + 2 : ℕ) : ℝ) ^ r) := by
      rw [show -(r - 1 + 1) / (1 : ℝ) = -r by ring,
        show (r - 1 + 1) / (1 : ℝ) = r by ring,
        Real.rpow_neg hb.le]
      ring

private theorem integrableOn_gamma_hankel_atom
    {r : ℝ} (hr : 0 < r) (m n : ℕ) :
    IntegrableOn
      (fun x : ℝ =>
        x ^ (r - 1) * Real.exp (-(((m + n + 2 : ℕ) : ℝ) * x)))
      (Ioi 0) := by
  have hb : 0 < (((m + n + 2 : ℕ) : ℝ)) := by positivity
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := r - 1) (b := ((m + n + 2 : ℕ) : ℝ))
      (by linarith) (by norm_num) hb)

/-- **Finite Gamma--Hankel localization law.**  The weighted Laplace square is exactly the
Gamma--Hankel quadratic form. -/
theorem integral_finiteRealLaplacePencil_sq
    (a : ℕ → ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0,
      x ^ (r - 1) * finiteRealLaplacePencil a N x ^ 2) =
      finiteGammaHankelEnergy a N r := by
  have hfun : (fun x : ℝ =>
      x ^ (r - 1) * finiteRealLaplacePencil a N x ^ 2) =
      fun x : ℝ => ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        (a m * a n) *
          (x ^ (r - 1) * Real.exp (-(((m + n + 2 : ℕ) : ℝ) * x))) := by
    funext x
    rw [finiteRealLaplacePencil, pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    have hcast : (((m + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ)) =
        ((m + n + 2 : ℕ) : ℝ) := by push_cast; ring
    calc
      x ^ (r - 1) *
          (a m * Real.exp (-((m + 1 : ℕ) : ℝ) * x) *
            (a n * Real.exp (-((n + 1 : ℕ) : ℝ) * x))) =
          a m * a n * (x ^ (r - 1) *
            (Real.exp (-((m + 1 : ℕ) : ℝ) * x) *
              Real.exp (-((n + 1 : ℕ) : ℝ) * x))) := by ring
      _ = a m * a n * (x ^ (r - 1) *
            Real.exp (-(((m + n + 2 : ℕ) : ℝ) * x))) := by
          rw [← Real.exp_add]
          congr 4
          rw [← hcast]
          ring
  rw [hfun]
  have hatom (m n : ℕ) : IntegrableOn
      (fun x : ℝ => (a m * a n) *
        (x ^ (r - 1) * Real.exp (-(((m + n + 2 : ℕ) : ℝ) * x))))
      (Ioi 0) :=
    (integrableOn_gamma_hankel_atom hr m n).const_mul (a m * a n)
  calc
    (∫ x : ℝ in Ioi 0, ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        (a m * a n) *
          (x ^ (r - 1) * Real.exp (-(((m + n + 2 : ℕ) : ℝ) * x)))) =
        ∑ m ∈ Finset.range N, ∫ x : ℝ in Ioi 0,
          ∑ n ∈ Finset.range N, (a m * a n) *
            (x ^ (r - 1) * Real.exp (-(((m + n + 2 : ℕ) : ℝ) * x))) := by
      rw [integral_finsetSum]
      intro m hm
      exact integrable_finsetSum _ fun n hn => hatom m n
    _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          ∫ x : ℝ in Ioi 0, (a m * a n) *
            (x ^ (r - 1) * Real.exp (-(((m + n + 2 : ℕ) : ℝ) * x))) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [integral_finsetSum]
      intro n hn
      exact hatom m n
    _ = finiteGammaHankelEnergy a N r := by
      rw [finiteGammaHankelEnergy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul, integral_gamma_hankel_atom hr]
      ring


/-- The finite Gamma--Hankel density is integrable, not merely assigned an integral value. -/
theorem integrableOn_finiteRealLaplacePencil_sq
    (a : ℕ → ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ =>
      x ^ (r - 1) * finiteRealLaplacePencil a N x ^ 2) (Ioi 0) := by
  have hfun : (fun x : ℝ =>
      x ^ (r - 1) * finiteRealLaplacePencil a N x ^ 2) =
      fun x : ℝ => ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        (a m * a n) *
          (x ^ (r - 1) * Real.exp (-(((m + n + 2 : ℕ) : ℝ) * x))) := by
    funext x
    rw [finiteRealLaplacePencil, pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    have hcast : (((m + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ)) =
        ((m + n + 2 : ℕ) : ℝ) := by push_cast; ring
    calc
      x ^ (r - 1) *
          (a m * Real.exp (-((m + 1 : ℕ) : ℝ) * x) *
            (a n * Real.exp (-((n + 1 : ℕ) : ℝ) * x))) =
          a m * a n * (x ^ (r - 1) *
            (Real.exp (-((m + 1 : ℕ) : ℝ) * x) *
              Real.exp (-((n + 1 : ℕ) : ℝ) * x))) := by ring
      _ = a m * a n * (x ^ (r - 1) *
            Real.exp (-(((m + n + 2 : ℕ) : ℝ) * x))) := by
          rw [← Real.exp_add]
          congr 4
          rw [← hcast]
          ring
  rw [hfun]
  apply integrable_finsetSum
  intro m hm
  apply integrable_finsetSum
  intro n hn
  exact (integrableOn_gamma_hankel_atom hr m n).const_mul (a m * a n)


/-- The finite Gamma--Hankel matrix is positive semidefinite, expressed as nonnegativity of every
real quadratic form. -/
theorem finiteGammaHankelEnergy_nonneg
    (a : ℕ → ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    0 ≤ finiteGammaHankelEnergy a N r := by
  rw [← integral_finiteRealLaplacePencil_sq a N hr]
  apply setIntegral_nonneg measurableSet_Ioi
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg hx.le _) (sq_nonneg _)

/-- Möbius coefficients shifted so index zero represents the first positive integer. -/
def shiftedMobiusRealCoefficient (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (n + 1) : ℤ)

/-- Finite positive-integer Möbius--Laplace pencil. -/
def finiteMobiusLaplacePencil (N : ℕ) (x : ℝ) : ℝ :=
  finiteRealLaplacePencil shiftedMobiusRealCoefficient N x

/-- Finite Möbius specialization of the Gamma--Hankel energy. -/
def finiteMobiusGammaHankelEnergy (N : ℕ) (r : ℝ) : ℝ :=
  finiteGammaHankelEnergy shiftedMobiusRealCoefficient N r

/-- Exact weighted-energy identity for the finite Möbius--Laplace source. -/
theorem integral_finiteMobiusLaplacePencil_sq
    (N : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0,
      x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2) =
      finiteMobiusGammaHankelEnergy N r := by
  exact integral_finiteRealLaplacePencil_sq shiftedMobiusRealCoefficient N hr

/-- Every finite Möbius Gamma--Hankel energy is nonnegative despite its signed off-diagonal
entries. -/
theorem finiteMobiusGammaHankelEnergy_nonneg
    (N : ℕ) {r : ℝ} (hr : 0 < r) :
    0 ≤ finiteMobiusGammaHankelEnergy N r :=
  finiteGammaHankelEnergy_nonneg shiftedMobiusRealCoefficient N hr

private theorem rexp_neg_deriv_gammaHankel :
    ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-u)) Set.univ u :=
  fun u _ => mul_neg_one (Real.exp (-u)) ▸
    ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt

private theorem rexp_neg_image_gammaHankel :
    (Real.exp ∘ Neg.neg) '' (Set.univ : Set ℝ) = Set.Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
    Set.image_univ, Real.range_exp]

private theorem rexp_neg_injOn_gammaHankel :
    (Set.univ : Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (Set.univ.mapsTo_univ _)

/-- Log-coordinate form of finite Gamma--Hankel localization. -/
theorem integral_log_finiteRealLaplacePencil_sq
    (a : ℕ → ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ u : ℝ,
      Real.exp (-r * u) *
        finiteRealLaplacePencil a N (Real.exp (-u)) ^ 2) =
      finiteGammaHankelEnergy a N r := by
  rw [← integral_finiteRealLaplacePencil_sq a N hr]
  rw [← rexp_neg_image_gammaHankel,
    integral_image_eq_integral_abs_deriv_smul
      MeasurableSet.univ rexp_neg_deriv_gammaHankel rexp_neg_injOn_gammaHankel]
  rw [Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [Function.comp_apply, smul_eq_mul, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Log-coordinate finite Gamma--Hankel density is integrable. -/
theorem integrable_log_finiteRealLaplacePencil_sq
    (a : ℕ → ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun u : ℝ =>
      Real.exp (-r * u) *
        finiteRealLaplacePencil a N (Real.exp (-u)) ^ 2) := by
  let g : ℝ → ℝ := fun x =>
    x ^ (r - 1) * finiteRealLaplacePencil a N x ^ 2
  have hg : IntegrableOn g (Ioi 0) :=
    integrableOn_finiteRealLaplacePencil_sq a N hr
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ rexp_neg_deriv_gammaHankel rexp_neg_injOn_gammaHankel g
  rw [rexp_neg_image_gammaHankel] at hiff
  have hlog := hiff.mp hg
  rw [integrableOn_univ] at hlog
  convert hlog using 1
  funext u
  simp only [g, Function.comp_apply, smul_eq_mul, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Exact log-coordinate energy of a finite Möbius--Laplace pencil. -/
theorem integral_log_finiteMobiusLaplacePencil_sq
    (N : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ u : ℝ,
      Real.exp (-r * u) *
        finiteMobiusLaplacePencil N (Real.exp (-u)) ^ 2) =
      finiteMobiusGammaHankelEnergy N r := by
  exact integral_log_finiteRealLaplacePencil_sq
    shiftedMobiusRealCoefficient N hr

/-- Log-coordinate finite Möbius--Laplace energy density is integrable. -/
theorem integrable_log_finiteMobiusLaplacePencil_sq
    (N : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun u : ℝ =>
      Real.exp (-r * u) *
        finiteMobiusLaplacePencil N (Real.exp (-u)) ^ 2) :=
  integrable_log_finiteRealLaplacePencil_sq
    shiftedMobiusRealCoefficient N hr

/-- Diagonal part of finite Möbius Gamma--Hankel energy.  Unlike the signed cross covariance,
this part is unconditionally summable throughout the critical range `r > 1`. -/
def finiteMobiusGammaHankelDiagonalEnergy (N : ℕ) (r : ℝ) : ℝ :=
  Real.Gamma r * ∑ n ∈ Finset.range N,
    shiftedMobiusRealCoefficient n ^ 2 /
      (((2 * (n + 1) : ℕ) : ℝ) ^ r)

/-- Signed off-diagonal covariance, isolated by subtracting the exact diagonal energy. -/
def finiteMobiusGammaHankelOffDiagonalCovariance (N : ℕ) (r : ℝ) : ℝ :=
  finiteMobiusGammaHankelEnergy N r -
    finiteMobiusGammaHankelDiagonalEnergy N r

/-- Exact diagonal/off-diagonal decomposition. -/
theorem finiteMobiusGammaHankelEnergy_eq_diagonal_add_offDiagonal
    (N : ℕ) (r : ℝ) :
    finiteMobiusGammaHankelEnergy N r =
      finiteMobiusGammaHankelDiagonalEnergy N r +
        finiteMobiusGammaHankelOffDiagonalCovariance N r := by
  rw [finiteMobiusGammaHankelOffDiagonalCovariance]
  ring

private theorem shiftedMobiusRealCoefficient_sq_le_one (n : ℕ) :
    shiftedMobiusRealCoefficient n ^ 2 ≤ 1 := by
  have hmu : |shiftedMobiusRealCoefficient n| ≤ 1 := by
    rw [shiftedMobiusRealCoefficient]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)
  rw [← sq_abs]
  nlinarith [abs_nonneg (shiftedMobiusRealCoefficient n)]

/-- Diagonal Möbius Gamma--Hankel energy is nonnegative. -/
theorem finiteMobiusGammaHankelDiagonalEnergy_nonneg
    (N : ℕ) {r : ℝ} (hr : 0 < r) :
    0 ≤ finiteMobiusGammaHankelDiagonalEnergy N r := by
  rw [finiteMobiusGammaHankelDiagonalEnergy]
  exact mul_nonneg (Real.Gamma_pos_of_pos hr).le
    (Finset.sum_nonneg fun _n _hn => by positivity)

/-- A summable p-series majorant for the diagonal energy. -/
def mobiusGammaHankelDiagonalMajorant (r : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma r * (1 / |(n : ℝ) + 1| ^ r)

theorem summable_mobiusGammaHankelDiagonalMajorant
    {r : ℝ} (hr : 1 < r) :
    Summable (mobiusGammaHankelDiagonalMajorant r) := by
  exact ((Real.summable_one_div_nat_add_rpow 1 r).mpr hr).mul_left
    (Real.Gamma r)

private theorem mobiusGammaHankelDiagonalTerm_le_majorant
    {r : ℝ} (hr : 1 < r) (n : ℕ) :
    Real.Gamma r *
        (shiftedMobiusRealCoefficient n ^ 2 /
          (((2 * (n + 1) : ℕ) : ℝ) ^ r)) ≤
      mobiusGammaHankelDiagonalMajorant r n := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hsmall : 0 < ((n : ℝ) + 1) ^ r := by positivity
  have hbase : (n : ℝ) + 1 ≤ ((2 * (n + 1) : ℕ) : ℝ) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    norm_num
    nlinarith
  have hpow : ((n : ℝ) + 1) ^ r ≤ (((2 * (n + 1) : ℕ) : ℝ) ^ r) :=
    Real.rpow_le_rpow (by positivity) hbase hr0.le
  have hinv :
      1 / (((2 * (n + 1) : ℕ) : ℝ) ^ r) ≤
        1 / ((n : ℝ) + 1) ^ r :=
    one_div_le_one_div_of_le hsmall hpow
  have hcoeff :
      shiftedMobiusRealCoefficient n ^ 2 /
          (((2 * (n + 1) : ℕ) : ℝ) ^ r) ≤
        1 / ((n : ℝ) + 1) ^ r := by
    calc
      shiftedMobiusRealCoefficient n ^ 2 /
          (((2 * (n + 1) : ℕ) : ℝ) ^ r) ≤
          1 / (((2 * (n + 1) : ℕ) : ℝ) ^ r) := by
            exact div_le_div_of_nonneg_right
              (shiftedMobiusRealCoefficient_sq_le_one n) (by positivity)
      _ ≤ 1 / ((n : ℝ) + 1) ^ r := hinv
  rw [mobiusGammaHankelDiagonalMajorant,
    abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
  exact mul_le_mul_of_nonneg_left hcoeff (Real.Gamma_pos_of_pos hr0).le

/-- The entire diagonal family has one aperture-independent finite ceiling when `r > 1`. -/
theorem finiteMobiusGammaHankelDiagonalEnergy_le_tsum
    (N : ℕ) {r : ℝ} (hr : 1 < r) :
    finiteMobiusGammaHankelDiagonalEnergy N r ≤
      ∑' n : ℕ, mobiusGammaHankelDiagonalMajorant r n := by
  rw [finiteMobiusGammaHankelDiagonalEnergy, Finset.mul_sum]
  calc
    ∑ n ∈ Finset.range N,
        Real.Gamma r *
          (shiftedMobiusRealCoefficient n ^ 2 /
            (((2 * (n + 1) : ℕ) : ℝ) ^ r)) ≤
        ∑ n ∈ Finset.range N, mobiusGammaHankelDiagonalMajorant r n := by
          exact Finset.sum_le_sum fun n _hn =>
            mobiusGammaHankelDiagonalTerm_le_majorant hr n
    _ ≤ ∑' n : ℕ, mobiusGammaHankelDiagonalMajorant r n := by
      exact Summable.sum_le_tsum (Finset.range N)
        (fun n _hn => by
          rw [mobiusGammaHankelDiagonalMajorant]
          positivity)
        (summable_mobiusGammaHankelDiagonalMajorant hr)

/-- Positivity of full Gamma--Hankel energy supplies an automatic lower floor for signed
off-diagonal covariance.  No lower source estimate remains to be proved. -/
theorem finiteMobiusGammaHankelOffDiagonalCovariance_lower_floor
    (N : ℕ) {r : ℝ} (hr : 0 < r) :
    -finiteMobiusGammaHankelDiagonalEnergy N r ≤
      finiteMobiusGammaHankelOffDiagonalCovariance N r := by
  rw [finiteMobiusGammaHankelOffDiagonalCovariance]
  linarith [finiteMobiusGammaHankelEnergy_nonneg N hr]

/-- Uniform finite-section Gamma--Hankel energy at one exponent. -/
def MobiusGammaHankelEnergyUniformlyBounded (r : ℝ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, finiteMobiusGammaHankelEnergy N r ≤ C

/-- One-sided uniform ceiling on signed off-diagonal Möbius covariance. -/
def MobiusGammaHankelOffDiagonalUpperBounded (r : ℝ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ,
    finiteMobiusGammaHankelOffDiagonalCovariance N r ≤ C

/-- **One-sided covariance compression.**  In the RH-critical range `r > 1`, uniform
Gamma--Hankel energy is equivalent to only an upper bound on signed off-diagonal covariance.
The diagonal is unconditionally summable and positivity supplies the missing lower bound. -/
theorem mobiusGammaHankelEnergyUniformlyBounded_iff_offDiagonalUpperBounded
    {r : ℝ} (hr : 1 < r) :
    MobiusGammaHankelEnergyUniformlyBounded r ↔
      MobiusGammaHankelOffDiagonalUpperBounded r := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun N => ?_⟩
    rw [finiteMobiusGammaHankelOffDiagonalCovariance]
    exact (sub_le_self _
      (finiteMobiusGammaHankelDiagonalEnergy_nonneg N (by linarith))).trans (hC N)
  · rintro ⟨C, hC⟩
    let D : ℝ := ∑' n : ℕ, mobiusGammaHankelDiagonalMajorant r n
    refine ⟨D + C, fun N => ?_⟩
    rw [finiteMobiusGammaHankelEnergy_eq_diagonal_add_offDiagonal]
    exact add_le_add (finiteMobiusGammaHankelDiagonalEnergy_le_tsum N hr) (hC N)


end

end RHTower
