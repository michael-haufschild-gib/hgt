import GaloisForLFunctions.HTGeometry.GammaInversePoleBranchCoefficientFreeness
import GaloisForLFunctions.HTGeometry.SimpleZeroBellHorizon

/-!
# The simple-zero Bell horizon for reciprocal Gamma at its zeros

The reciprocal Gamma function `1/Γ` has a simple zero at each `-n`. Zooming in with the factorial
scale, `G_n(x) = 1/Γ(-n + ε_n x)` with `ε_n = (-1)^(n+1) / n!`, this module shows that near
`x = 0` one has `G_n(x) = -x / U_n(x)`, where `U_n` is the analytic unit
`Γ(ε_n x + 1) / ∏_{j<n} (1 - ε_n x / (j + 1))`. Consequently the covariant residues
`G_n^(j+2)(0) / G_n'(0)` equal `(j + 2)!` times the Taylor coefficients of `1/U_n`. As germs of
sequences in `n → ∞` these residues are algebraically independent over `ℂ`, so the universal
simple-zero Bell-horizon classification applies to `1/Γ` with these actual residues: the pole
profile of a jet polynomial has `T`-degree equal to its total degree, and a raw jet polynomial
has at most a simple-pole profile exactly when it is the Bell substitution of an affine
polynomial.

## Main results

- `analyticJetPowerSeries_mul`: the Taylor series at `x` of a product of functions smooth at `x`
  is the product of their Taylor series.
- `analyticJetPowerSeries_inv_eq_unitInverse`: if `f(x) = 1`, the Taylor series of `1/f` at `x`
  is the formal inverse unit built from the positive Taylor coefficients of `f`.
- `gammaPoleSimpleZeroSection_eventuallyEq_reciprocalGammaFactorialZoom`: near `0`,
  `1/Γ(-n + ε_n x) = -x / U_n(x)`.
- `reciprocalGammaFactorialZoom_covariantResidue`: `G_n^(j+2)(0) / G_n'(0)` equals `(j + 2)!`
  times the `(j + 1)`-th Taylor coefficient of `1/U_n` at `0`.
- `AlgebraicIndependent.diagonalScale`: multiplying an algebraically independent family by
  nonzero constants keeps it algebraically independent.
- `algebraicIndependent_gammaSimpleZeroCovariantResidueGerm`: the sequence germs of the covariant
  residues of `1/Γ` at its zeros are algebraically independent over `ℂ`.
- `gammaSimpleZeroPrincipalProfile_natDegree_eq_totalDegree`: for nonzero `P`, the `T`-degree of
  its Gamma principal profile equals its total degree.
- `gammaSimpleZeroRawJetPrincipalProfile_natDegree_le_one_iff_exists_bellAffine`: a raw jet
  polynomial has profile degree at most one iff it is the Bell substitution of an affine
  polynomial.

## Hypotheses

Unconditional for the Gamma statements. The general Taylor-series lemmas assume smoothness of
all orders at the base point (`ContDiffAt ℂ n f x` for every `n`) and `f x ≠ 0` or `f x = 1`
where an inverse is taken; `AlgebraicIndependent.diagonalScale` assumes all scaling constants
are nonzero.
-/

open PowerSeries MvPolynomial Filter Topology

namespace GaloisForLFunctions

noncomputable section

local instance analyticJetNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

/-- The formal Taylor series `Σ_n f^(n)(x) / n! · X^n` of `f` at `x`. -/
def analyticJetPowerSeries (f : ℂ → ℂ) (x : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => ((n.factorial : ℂ)⁻¹) * iteratedDeriv n f x

/-- Leibniz rule for Taylor series: if `f` and `g` are `C^n` at `x` for every `n`, the Taylor
series of `f * g` at `x` is the product of the Taylor series of `f` and `g`. -/
theorem analyticJetPowerSeries_mul
    {f g : ℂ → ℂ} {x : ℂ}
    (hf : ∀ n : ℕ, ContDiffAt ℂ n f x)
    (hg : ∀ n : ℕ, ContDiffAt ℂ n g x) :
    analyticJetPowerSeries (f * g) x =
      analyticJetPowerSeries f x * analyticJetPowerSeries g x := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [analyticJetPowerSeries, PowerSeries.coeff_mk]
  rw [iteratedDeriv_mul (hf n) (hg n), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hfacNat := Nat.choose_mul_factorial_mul_factorial hin
  have hfac :
      (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) =
        (n.factorial : ℂ) := by
    exact_mod_cast hfacNat
  have hi0 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hni0 : ((n - i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - i)
  have hn0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hchoose0 : (n.choose i : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hin))
  have hscalar :
      ((n.factorial : ℂ)⁻¹) * (n.choose i : ℂ) =
        ((i.factorial : ℂ)⁻¹) * (((n - i).factorial : ℂ)⁻¹) := by
    rw [← hfac]
    field_simp [hchoose0, hi0, hni0]
  calc
    (n.factorial : ℂ)⁻¹ *
        ((n.choose i : ℂ) * iteratedDeriv i f x *
          iteratedDeriv (n - i) g x) =
        ((n.factorial : ℂ)⁻¹ * (n.choose i : ℂ)) *
          (iteratedDeriv i f x * iteratedDeriv (n - i) g x) := by ring
    _ = ((i.factorial : ℂ)⁻¹ * ((n - i).factorial : ℂ)⁻¹) *
          (iteratedDeriv i f x * iteratedDeriv (n - i) g x) := by rw [hscalar]
    _ = (i.factorial : ℂ)⁻¹ * iteratedDeriv i f x *
          (((n - i).factorial : ℂ)⁻¹ * iteratedDeriv (n - i) g x) := by ring

/-- The positive-degree Taylor coefficients `f^(j+1)(x) / (j + 1)!` of `f` at `x`. -/
def analyticPositiveJet (f : ℂ → ℂ) (x : ℂ) (j : ℕ) : ℂ :=
  (((j + 1).factorial : ℂ)⁻¹) * iteratedDeriv (j + 1) f x

theorem analyticJetPowerSeries_eq_unitPowerSeriesOfCoefficients
    {f : ℂ → ℂ} {x : ℂ} (hfx : f x = 1) :
    analyticJetPowerSeries f x = unitPowerSeriesOfCoefficients (analyticPositiveJet f x) := by
  apply PowerSeries.ext
  intro n
  obtain (_ | n) := n
  · simp [analyticJetPowerSeries, hfx]
  · simp [analyticJetPowerSeries, analyticPositiveJet]

/-- If `f` is smooth of all orders at `x` and `f x ≠ 0`, the Taylor series of `f` and of `1/f`
at `x` multiply to `1`. -/
theorem analyticJetPowerSeries_mul_inv
    {f : ℂ → ℂ} {x : ℂ}
    (hf : ∀ n : ℕ, ContDiffAt ℂ n f x) (hfx : f x ≠ 0) :
    analyticJetPowerSeries f x * analyticJetPowerSeries (fun z => (f z)⁻¹) x = 1 := by
  have hfinv : ∀ n : ℕ, ContDiffAt ℂ n (fun z => (f z)⁻¹) x := by
    intro n
    exact (hf n).inv hfx
  rw [← analyticJetPowerSeries_mul hf hfinv]
  have hne : ∀ᶠ z : ℂ in 𝓝 x, f z ≠ 0 :=
    (hf 0).continuousAt.eventually_ne hfx
  have hev : f * (fun z => (f z)⁻¹) =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [hne] with z hz
    exact mul_inv_cancel₀ hz
  apply PowerSeries.ext
  intro n
  obtain (_ | n) := n
  · simp [analyticJetPowerSeries, iteratedDeriv_zero, hfx]
  · simp only [analyticJetPowerSeries, PowerSeries.coeff_mk]
    rw [show iteratedDeriv (n + 1) (f * fun z => (f z)⁻¹) x =
        iteratedDeriv (n + 1) (fun _ : ℂ => 1) x from hev.iteratedDeriv_eq (n + 1)]
    rw [iteratedDeriv_const, if_neg (Nat.succ_ne_zero n)]
    simp

/-- If `f` is smooth of all orders at `x` and `f x = 1`, the Taylor series of `1/f` at `x` is the
formal inverse unit specialized at the positive Taylor coefficients of `f`. -/
theorem analyticJetPowerSeries_inv_eq_unitInverse
    {f : ℂ → ℂ} {x : ℂ}
    (hf : ∀ n : ℕ, ContDiffAt ℂ n f x) (hfx : f x = 1) :
    analyticJetPowerSeries (fun z => (f z)⁻¹) x =
      unitInversePowerSeriesOfCoefficients (analyticPositiveJet f x) := by
  let U := unitPowerSeriesOfCoefficients (analyticPositiveJet f x)
  let V := analyticJetPowerSeries (fun z => (f z)⁻¹) x
  let W := unitInversePowerSeriesOfCoefficients (analyticPositiveJet f x)
  have hUV : U * V = 1 := by
    rw [show U = analyticJetPowerSeries f x by
      exact (analyticJetPowerSeries_eq_unitPowerSeriesOfCoefficients hfx).symm]
    exact analyticJetPowerSeries_mul_inv hf (by rw [hfx]; exact one_ne_zero)
  have hWU : W * U = 1 := by
    exact unitInverse_mul_unitPowerSeries (analyticPositiveJet f x)
  calc
    V = 1 * V := by rw [one_mul]
    _ = (W * U) * V := by rw [hWU]
    _ = W * (U * V) := by rw [mul_assoc]
    _ = W := by rw [hUV, mul_one]

/-- The positive Taylor coefficients at `0` of `1/U_n` are the universal inverse-unit
coefficients evaluated at the positive Taylor coefficients of the Gamma pole unit `U_n`. -/
theorem analyticPositiveJet_inv_gammaPoleRegularUnit (j n : ℕ) :
    analyticPositiveJet (fun z => (gammaPoleRegularUnit n z)⁻¹) 0 j =
      unitInverseCoefficientOfCoefficients
        (analyticPositiveJet (gammaPoleRegularUnit n) 0) j := by
  have hf : ∀ k : ℕ, ContDiffAt ℂ k (gammaPoleRegularUnit n) 0 := by
    intro k
    exact (gammaPoleRegularUnit_analyticAt_zero n).contDiffAt
  have hseries := analyticJetPowerSeries_inv_eq_unitInverse hf
    (gammaPoleRegularUnit_zero n)
  have hcoeff := congrArg (PowerSeries.coeff (j + 1)) hseries
  simpa [analyticJetPowerSeries, analyticPositiveJet,
    unitInverseCoefficientOfCoefficients] using hcoeff

/-- The sequence germ `N ↦` (the `(j + 1)`-th Taylor coefficient at `0` of `1/U_(N-1)`), taken
from the actual analytic Gamma pole units. -/
def gammaPoleActualReciprocalUnitCoefficientGerm (j : ℕ) : NatGerm :=
  fun N : ℕ =>
    analyticPositiveJet
      (fun z => (gammaPoleRegularUnit (N - 1) z)⁻¹) 0 j

/-- The analytic reciprocal-unit coefficient germs agree with the formal reciprocal-unit
coefficient germs `gammaPoleReciprocalUnitCoefficientGerm`. -/
theorem gammaPoleActualReciprocalUnitCoefficientGerm_eq (j : ℕ) :
    gammaPoleActualReciprocalUnitCoefficientGerm j =
      gammaPoleReciprocalUnitCoefficientGerm j := by
  let aseq : ℕ → ℕ → ℂ := fun i N =>
    analyticPositiveJet (gammaPoleRegularUnit (N - 1)) 0 i
  have ha (i : ℕ) :
      gammaPoleUnitPositiveCoefficientGerm i = (aseq i : NatGerm) := by
    simpa [aseq, analyticPositiveJet] using
      gammaPoleUnitPositiveCoefficientGerm_eq_actualTaylorCoefficient i
  rw [gammaPoleReciprocalUnitCoefficientGerm,
    unitInverseCoefficientOfCoefficients_eq_aeval]
  have haseq : gammaPoleUnitPositiveCoefficientGerm =
      fun i => (aseq i : NatGerm) := funext ha
  rw [haseq]
  rw [aeval_sequenceGerm_eq]
  symm
  rw [gammaPoleActualReciprocalUnitCoefficientGerm, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun N => by
    rw [mvPolynomialSequenceEval_apply]
    have hp := analyticPositiveJet_inv_gammaPoleRegularUnit j (N - 1)
    rw [unitInverseCoefficientOfCoefficients_eq_aeval] at hp
    simpa [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq] using hp.symm

/-- The simple-zero section `z ↦ -z / U_n(z)` built from the Gamma pole unit `U_n`. -/
def gammaPoleSimpleZeroSection (n : ℕ) (z : ℂ) : ℂ :=
  -z * (gammaPoleRegularUnit n z)⁻¹

theorem analyticJetPowerSeries_neg_id_zero :
    analyticJetPowerSeries (fun z : ℂ => -z) 0 = -PowerSeries.X := by
  apply PowerSeries.ext
  intro k
  obtain (_ | _ | k) := k
  · simp [analyticJetPowerSeries, iteratedDeriv_zero]
  · simp [analyticJetPowerSeries, iteratedDeriv_one]
  · simp [analyticJetPowerSeries, iteratedDeriv_succ', PowerSeries.coeff_X]

theorem analyticJetPowerSeries_gammaPoleSimpleZeroSection (n : ℕ) :
    analyticJetPowerSeries (gammaPoleSimpleZeroSection n) 0 =
      -PowerSeries.X *
        analyticJetPowerSeries (fun z => (gammaPoleRegularUnit n z)⁻¹) 0 := by
  have hneg : ∀ k : ℕ, ContDiffAt ℂ k (fun z : ℂ => -z) 0 := by
    intro k
    fun_prop
  have hinv : ∀ k : ℕ,
      ContDiffAt ℂ k (fun z => (gammaPoleRegularUnit n z)⁻¹) 0 := by
    intro k
    exact (gammaPoleRegularUnit_analyticAt_zero n).contDiffAt.inv
      (by rw [gammaPoleRegularUnit_zero]; exact one_ne_zero)
  have hmul := analyticJetPowerSeries_mul hneg hinv
  change analyticJetPowerSeries (gammaPoleSimpleZeroSection n) 0 = _ at hmul
  rw [analyticJetPowerSeries_neg_id_zero] at hmul
  exact hmul

/-- The section `-z / U_n(z)` has derivative `-1` at its simple zero `0`. -/
theorem deriv_gammaPoleSimpleZeroSection_zero (n : ℕ) :
    deriv (gammaPoleSimpleZeroSection n) 0 = -1 := by
  have hcoeff := congrArg (PowerSeries.coeff 1)
    (analyticJetPowerSeries_gammaPoleSimpleZeroSection n)
  simpa [analyticJetPowerSeries, iteratedDeriv_one,
    gammaPoleRegularUnit_zero] using hcoeff

/-- Covariant residues of the section `G = -z / U_n(z)`: `G^(j+2)(0) / G'(0)` equals `(j + 2)!`
times the `(j + 1)`-th Taylor coefficient of `1/U_n` at `0`. -/
theorem gammaPoleSimpleZeroSection_covariantResidue (j n : ℕ) :
    iteratedDeriv (j + 2) (gammaPoleSimpleZeroSection n) 0 /
        deriv (gammaPoleSimpleZeroSection n) 0 =
      ((j + 2).factorial : ℂ) *
        analyticPositiveJet
          (fun z => (gammaPoleRegularUnit n z)⁻¹) 0 j := by
  have hcoeff := congrArg (PowerSeries.coeff (j + 2))
    (analyticJetPowerSeries_gammaPoleSimpleZeroSection n)
  have hcoeff' :
      (((j + 2).factorial : ℂ)⁻¹) *
          iteratedDeriv (j + 2) (gammaPoleSimpleZeroSection n) 0 =
        -((((j + 1).factorial : ℂ)⁻¹) *
          iteratedDeriv (j + 1) (fun z => (gammaPoleRegularUnit n z)⁻¹) 0) := by
    calc
      (((j + 2).factorial : ℂ)⁻¹) *
          iteratedDeriv (j + 2) (gammaPoleSimpleZeroSection n) 0 =
          (PowerSeries.coeff (j + 2))
            (-PowerSeries.X * analyticJetPowerSeries
              (fun z => (gammaPoleRegularUnit n z)⁻¹) 0) := by
        simpa [analyticJetPowerSeries] using hcoeff
      _ = -(PowerSeries.coeff (j + 2))
            (PowerSeries.X * analyticJetPowerSeries
              (fun z => (gammaPoleRegularUnit n z)⁻¹) 0) := by
        rw [show -PowerSeries.X * analyticJetPowerSeries
            (fun z => (gammaPoleRegularUnit n z)⁻¹) 0 =
          -(PowerSeries.X * analyticJetPowerSeries
            (fun z => (gammaPoleRegularUnit n z)⁻¹) 0) by ring, map_neg]
      _ = -((((j + 1).factorial : ℂ)⁻¹) *
          iteratedDeriv (j + 1) (fun z => (gammaPoleRegularUnit n z)⁻¹) 0) := by
        rw [show j + 2 = (j + 1) + 1 by omega,
          PowerSeries.coeff_succ_X_mul]
        simp [analyticJetPowerSeries]
  have hfac0 : ((j + 2).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (j + 2)
  have hcancel : ((j + 2).factorial : ℂ) * ((j + 2).factorial : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ hfac0
  rw [deriv_gammaPoleSimpleZeroSection_zero, analyticPositiveJet]
  calc
    iteratedDeriv (j + 2) (gammaPoleSimpleZeroSection n) 0 / -1 =
        -iteratedDeriv (j + 2) (gammaPoleSimpleZeroSection n) 0 := by ring
    _ = -(((j + 2).factorial : ℂ) *
        (((j + 2).factorial : ℂ)⁻¹ *
          iteratedDeriv (j + 2) (gammaPoleSimpleZeroSection n) 0)) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ = -(((j + 2).factorial : ℂ) *
        -((((j + 1).factorial : ℂ)⁻¹) *
          iteratedDeriv (j + 1) (fun z => (gammaPoleRegularUnit n z)⁻¹) 0)) := by
      rw [hcoeff']
    _ = ((j + 2).factorial : ℂ) *
        (((j + 1).factorial : ℂ)⁻¹ *
          iteratedDeriv (j + 1) (fun z => (gammaPoleRegularUnit n z)⁻¹) 0) := by ring

/-- Near `x = 0`, the factorial zoom of reciprocal Gamma at its zero `-n` equals the simple-zero
section: `1/Γ(-n + ε_n x) = -x / U_n(x)`. -/
theorem gammaPoleSimpleZeroSection_eventuallyEq_reciprocalGammaFactorialZoom (n : ℕ) :
    gammaPoleSimpleZeroSection n =ᶠ[𝓝 0] reciprocalGammaFactorialZoom n := by
  have haff : ContinuousAt
      (fun x : ℂ => reciprocalGammaFactorialScale n * x + 1) 0 := by fun_prop
  have hoff : ∀ m : ℕ,
      reciprocalGammaFactorialScale n * 0 + 1 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [mul_zero, zero_add, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hpole : ∀ᶠ x : ℂ in 𝓝 0,
      ∀ m : ℕ, reciprocalGammaFactorialScale n * x + 1 ≠ -(m : ℂ) :=
    haff (offPoles_isOpen.mem_nhds (by simpa using hoff))
  have hprodcont : ContinuousAt (reciprocalGammaNormalizedProduct n) 0 := by
    unfold reciprocalGammaNormalizedProduct
    fun_prop
  have hprod : ∀ᶠ x : ℂ in 𝓝 0,
      reciprocalGammaNormalizedProduct n x ≠ 0 :=
    hprodcont.eventually_ne (by
      rw [reciprocalGammaNormalizedProduct_zero]
      exact one_ne_zero)
  filter_upwards [hpole, hprod] with x hxpole hxprod
  by_cases hx : x = 0
  · subst x
    simp [gammaPoleSimpleZeroSection, gammaPoleRegularUnit_zero,
      reciprocalGammaFactorialZoom_zero]
  · have hnum :
        Complex.Gamma (reciprocalGammaFactorialScale n * x + 1) ≠ 0 :=
      Complex.Gamma_ne_zero hxpole
    have hU : gammaPoleRegularUnit n x ≠ 0 := by
      exact div_ne_zero hnum hxprod
    rw [gammaPoleSimpleZeroSection, reciprocalGammaFactorialZoom,
      factorialBlowUpZoom, reciprocalGammaEntire,
      gammaPoleRegularUnit_source_identity n hx hxpole hxprod]
    field_simp [hU, hx]

theorem gammaPoleSimpleZeroSection_iteratedDeriv_eq_zoom (k n : ℕ) :
    iteratedDeriv k (gammaPoleSimpleZeroSection n) 0 =
      iteratedDeriv k (reciprocalGammaFactorialZoom n) 0 :=
  (gammaPoleSimpleZeroSection_eventuallyEq_reciprocalGammaFactorialZoom n).iteratedDeriv_eq k

/-- For the zoom `G_n(x) = 1/Γ(-n + ε_n x)`, the covariant residue `G_n^(j+2)(0) / G_n'(0)` is
`(j + 2)!` times the `(j + 1)`-th Taylor coefficient of `1/U_n` at `0`. -/
theorem reciprocalGammaFactorialZoom_covariantResidue (j n : ℕ) :
    iteratedDeriv (j + 2) (reciprocalGammaFactorialZoom n) 0 /
        deriv (reciprocalGammaFactorialZoom n) 0 =
      ((j + 2).factorial : ℂ) *
        analyticPositiveJet
          (fun z => (gammaPoleRegularUnit n z)⁻¹) 0 j := by
  rw [← iteratedDeriv_one, ← gammaPoleSimpleZeroSection_iteratedDeriv_eq_zoom 1 n,
    ← gammaPoleSimpleZeroSection_iteratedDeriv_eq_zoom (j + 2) n]
  rw [iteratedDeriv_one]
  exact gammaPoleSimpleZeroSection_covariantResidue j n

/-- The diagonal linear substitution `X_i ↦ c_i X_i` on multivariate polynomials. -/
def diagonalCoordinateMap {ι : Type*} (c : ι → ℂ) :
    MvPolynomial ι ℂ →+* MvPolynomial ι ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => MvPolynomial.C (c i) * MvPolynomial.X i)

/-- Assuming every `c_i ≠ 0`, the diagonal substitution `X_i ↦ c_i X_i` is injective. -/
theorem diagonalCoordinateMap_injective {ι : Type*} {c : ι → ℂ}
    (hc : ∀ i, c i ≠ 0) : Function.Injective (diagonalCoordinateMap c) := by
  let invMap := diagonalCoordinateMap (fun i => (c i)⁻¹)
  apply Function.LeftInverse.injective (g := invMap)
  intro P
  have hcomp : invMap.comp (diagonalCoordinateMap c) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [invMap, diagonalCoordinateMap]
    · intro i
      simp [invMap, diagonalCoordinateMap]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc i), map_one, one_mul]
  exact RingHom.congr_fun hcomp P

/-- If `x` is algebraically independent over `ℂ` and every `c_i ≠ 0`, then the rescaled family
`c_i x_i` is algebraically independent over `ℂ`. -/
theorem AlgebraicIndependent.diagonalScale
    {ι A : Type*} [CommRing A] [Algebra ℂ A]
    {x : ι → A} (hx : AlgebraicIndependent ℂ x)
    {c : ι → ℂ} (hc : ∀ i, c i ≠ 0) :
    AlgebraicIndependent ℂ (fun i => algebraMap ℂ A (c i) * x i) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have hxinj := algebraicIndependent_iff_injective_aeval.mp hx
  have hhom :
      (MvPolynomial.aeval (fun i => algebraMap ℂ A (c i) * x i)).toRingHom =
        (MvPolynomial.aeval x).toRingHom.comp (diagonalCoordinateMap c) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [diagonalCoordinateMap]
    · intro i
      simp [diagonalCoordinateMap]
  change Function.Injective
    (MvPolynomial.aeval (fun i => algebraMap ℂ A (c i) * x i)).toRingHom
  rw [hhom]
  exact hxinj.comp (diagonalCoordinateMap_injective hc)

/-- The sequence germ `N ↦ G^(j+2)(0) / G'(0)` for `G` the factorial zoom of `1/Γ` at its zero
`-(N - 1)`: the `j`-th covariant residue along the zeros of reciprocal Gamma. -/
def gammaSimpleZeroCovariantResidueGerm (j : ℕ) : NatGerm :=
  fun N : ℕ =>
    iteratedDeriv (j + 2) (reciprocalGammaFactorialZoom (N - 1)) 0 /
      deriv (reciprocalGammaFactorialZoom (N - 1)) 0

/-- The `j`-th covariant residue germ is `(j + 2)!` times the `j`-th reciprocal-unit coefficient
germ of the Gamma pole family. -/
theorem gammaSimpleZeroCovariantResidueGerm_eq (j : ℕ) :
    gammaSimpleZeroCovariantResidueGerm j =
      algebraMap ℂ NatGerm ((j + 2).factorial : ℂ) *
        gammaPoleReciprocalUnitCoefficientGerm j := by
  rw [gammaSimpleZeroCovariantResidueGerm]
  rw [← gammaPoleActualReciprocalUnitCoefficientGerm_eq j]
  change (↑(fun N : ℕ =>
      iteratedDeriv (j + 2) (reciprocalGammaFactorialZoom (N - 1)) 0 /
        deriv (reciprocalGammaFactorialZoom (N - 1)) 0) : NatGerm) =
    complexNatGerm ((j + 2).factorial : ℂ) *
      gammaPoleActualReciprocalUnitCoefficientGerm j
  rw [gammaPoleActualReciprocalUnitCoefficientGerm,
    complexNatGerm_eq_constGerm, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun N =>
    reciprocalGammaFactorialZoom_covariantResidue j (N - 1)

/-- The covariant residue germs of reciprocal Gamma at its zeros are algebraically independent
over `ℂ` in the ring of sequence germs at infinity. -/
theorem algebraicIndependent_gammaSimpleZeroCovariantResidueGerm :
    AlgebraicIndependent ℂ gammaSimpleZeroCovariantResidueGerm := by
  have hscaled := AlgebraicIndependent.diagonalScale
    algebraicIndependent_gammaPoleReciprocalUnitCoefficientGerm
      (c := fun j => ((j + 2).factorial : ℂ)) (by
        intro j
        exact_mod_cast Nat.factorial_ne_zero (j + 2))
  have heq : gammaSimpleZeroCovariantResidueGerm =
      fun j => algebraMap ℂ NatGerm ((j + 2).factorial : ℂ) *
        gammaPoleReciprocalUnitCoefficientGerm j := by
    funext j
    exact gammaSimpleZeroCovariantResidueGerm_eq j
  rwa [heq]

/-- The simple-zero principal profile `Z₀ ↦ T`, `Z_(i+1) ↦ T · R_i`, with the boundary residues
`R_i` specialized to the actual Gamma covariant residue germs. -/
def gammaSimpleZeroPrincipalProfile (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* Polynomial NatGerm :=
  (Polynomial.mapRingHom
      (MvPolynomial.aeval
        (fun i : Fin n => gammaSimpleZeroCovariantResidueGerm i.val)).toRingHom).comp
    (HTGeometry.simpleZeroPrincipalProfile n)

/-- For nonzero `P`, the `T`-degree of its Gamma principal profile equals its total degree; no
cancellation occurs because the Gamma residues are algebraically independent. -/
theorem gammaSimpleZeroPrincipalProfile_natDegree_eq_totalDegree
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP0 : P ≠ 0) :
    (gammaSimpleZeroPrincipalProfile n P).natDegree = P.totalDegree := by
  have hAI : AlgebraicIndependent ℂ
      (fun i : Fin n => gammaSimpleZeroCovariantResidueGerm i.val) :=
    algebraicIndependent_gammaSimpleZeroCovariantResidueGerm.comp Fin.val Fin.val_injective
  have hinj : Function.Injective
      (MvPolynomial.aeval
        (fun i : Fin n => gammaSimpleZeroCovariantResidueGerm i.val)).toRingHom :=
    algebraicIndependent_iff_injective_aeval.mp hAI
  change ((HTGeometry.simpleZeroPrincipalProfile n P).map
      (MvPolynomial.aeval
        (fun i : Fin n => gammaSimpleZeroCovariantResidueGerm i.val)).toRingHom).natDegree = _
  rw [Polynomial.natDegree_map_eq_of_injective hinj]
  exact HTGeometry.simpleZeroPrincipalProfile_natDegree_eq_totalDegree hP0

/-- The Gamma principal profile of `P` has `T`-degree at most one iff `P` has total degree at most
one. -/
theorem gammaSimpleZeroPrincipalProfile_natDegree_le_one_iff
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (gammaSimpleZeroPrincipalProfile n P).natDegree ≤ 1 ↔ P.totalDegree ≤ 1 := by
  by_cases hP0 : P = 0
  · simp [hP0]
  · rw [gammaSimpleZeroPrincipalProfile_natDegree_eq_totalDegree hP0]

/-- The raw-jet principal profile (inverse Bell change of coordinates followed by the profile map),
with boundary residues specialized to the actual Gamma covariant residue germs. -/
def gammaSimpleZeroRawJetPrincipalProfile (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* Polynomial NatGerm :=
  (Polynomial.mapRingHom
      (MvPolynomial.aeval
        (fun i : Fin n => gammaSimpleZeroCovariantResidueGerm i.val)).toRingHom).comp
    (HTGeometry.simpleZeroRawJetPrincipalProfile n)

/-- Raw-jet horizon classification for reciprocal Gamma: the Gamma raw-jet profile of `P` has
`T`-degree at most one iff `P` is the Bell substitution of a polynomial of total degree at most
one. -/
theorem gammaSimpleZeroRawJetPrincipalProfile_natDegree_le_one_iff_exists_bellAffine
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (gammaSimpleZeroRawJetPrincipalProfile n P).natDegree ≤ 1 ↔
      ∃ Q : MvPolynomial (Fin (n + 1)) ℂ,
        Q.totalDegree ≤ 1 ∧ bellCoefficientMap n Q = P := by
  have hAI : AlgebraicIndependent ℂ
      (fun i : Fin n => gammaSimpleZeroCovariantResidueGerm i.val) :=
    algebraicIndependent_gammaSimpleZeroCovariantResidueGerm.comp Fin.val Fin.val_injective
  have hinj : Function.Injective
      (MvPolynomial.aeval
        (fun i : Fin n => gammaSimpleZeroCovariantResidueGerm i.val)).toRingHom :=
    algebraicIndependent_iff_injective_aeval.mp hAI
  change ((HTGeometry.simpleZeroRawJetPrincipalProfile n P).map
      (MvPolynomial.aeval
        (fun i : Fin n => gammaSimpleZeroCovariantResidueGerm i.val)).toRingHom).natDegree ≤ 1 ↔ _
  rw [Polynomial.natDegree_map_eq_of_injective hinj]
  exact HTGeometry.simpleZeroRawJetPrincipalProfile_natDegree_le_one_iff_exists_bellAffine P

end

end GaloisForLFunctions
