import GaloisForLFunctions.RHTower.LiEvenCrossCayleySquareDefectPrimeSignWall
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeMehlerHeine
import GaloisForLFunctions.RHTower.VanDerCorput

/-!
# Exact all-mode Laguerre clock for the LI critical cross density

Corpus search linked the all-mode Chebyshev square defect from
`LiEvenCrossCayleySquareDefectPrimeSignWall` to the exact Cayley cosine-square transform in
`CayleyLaguerreFourier`. Multiplication by the residual `1+x^2` is transferred through the
Fourier integral by two dominated frequency derivatives. The result is one explicit finite
polynomial clock for every LI mode:

`Fourier(density_n)(xi) = (pi/4) exp(-|xi|/2) Q_n(|xi|)`,

where `Q_n = P_(2n+2)'' - P_(2n+2)'` and `P_m` is the corpus associated-Laguerre polynomial.

This significantly reduces the surviving RH burden: the completed Abel prime--polar--Gamma
finite part no longer contains an unknown all-mode Fourier transform. Its remaining sign is a
finite Laguerre-clock problem. The fixed proof chain is completed-clock nonnegativity for every
mode, then LI common-reversal cross-capital nonnegativity, then positive even Li coefficients,
then RH. If completed coupling cannot carry these clocks, this exact formula is the route-killing
test for the LI producer.
-/

open Complex MeasureTheory Polynomial Real Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def liUnitEvenCrossCauchyDensity (n : ℕ) (x : ℝ) : ℝ :=
  liCriticalEvenCrossCauchyDensity n (x / 2)

theorem liUnitEvenCrossCauchyDensity_eq_cos (n : ℕ) (x : ℝ) :
    liUnitEvenCrossCauchyDensity n x =
      (1 - Real.cos (2 * ((n + 1 : ℕ) : ℝ) * Real.arctan x) ^ 2) / 2 := by
  rw [liUnitEvenCrossCauchyDensity,
    liCriticalEvenCrossCauchyDensity_eq_chebyshevSquareDefect]
  have hcoord : liCriticalCayleyCoordinate (x / 2) =
      (1 ^ 2 - x ^ 2) / (1 ^ 2 + x ^ 2) := by
    rw [liCriticalCayleyCoordinate]
    have h : (1 / 2 : ℝ) ^ 2 + (x / 2) ^ 2 ≠ 0 := by positivity
    field_simp [h]
  rw [hcoord]
  have hphase := chebyshevT_eval_xiHardEdgeCayleyCoordinate_real
    (a := 1) (by norm_num) x (n + 1)
  norm_num only [one_pow, div_one, Nat.cast_add, Nat.cast_one] at hphase ⊢
  rw [hphase]

theorem liUnitEvenCrossCauchyDensity_eq_kernelDefect (n : ℕ) (x : ℝ) :
    (liUnitEvenCrossCauchyDensity n x : ℂ) =
      ((1 + x ^ 2 : ℝ) : ℂ) / 2 *
        (routeUCauchyKernel x -
          routeUCayleyCosineSquareKernel (2 * (n + 1)) x) := by
  rw [liUnitEvenCrossCauchyDensity_eq_cos,
    routeUCauchyKernel, routeUCayleyCosineSquareKernel_eq]
  norm_cast
  have h : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  field_simp [h]

def polynomialCoefficientMass (P : Polynomial ℝ) : ℝ :=
  ∑ k ∈ P.support, |P.coeff k|

theorem abs_eval_le_polynomialCoefficientMass
    (P : Polynomial ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    |P.eval x| ≤ polynomialCoefficientMass P := by
  rw [Polynomial.eval_eq_sum]
  change |∑ k ∈ P.support, P.coeff k * x ^ k| ≤ _
  calc
    |∑ k ∈ P.support, P.coeff k * x ^ k| ≤
        ∑ k ∈ P.support, |P.coeff k * x ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ P.support, |P.coeff k| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg x) hx)
    _ = polynomialCoefficientMass P := rfl

theorem polynomialCoefficientMass_nonneg (P : Polynomial ℝ) :
    0 ≤ polynomialCoefficientMass P := by
  exact Finset.sum_nonneg fun k _ => abs_nonneg _

theorem liUnitEvenCrossCauchyDensity_le_cauchyMajorant (n : ℕ) (x : ℝ) :
    liUnitEvenCrossCauchyDensity n x ≤
      (2 * polynomialCoefficientMass (liEvenCrossLeftPolynomial n) ^ 2) *
        (1 + x ^ 2)⁻¹ := by
  let u := liCriticalCayleyCoordinate (x / 2)
  let C := polynomialCoefficientMass (liEvenCrossLeftPolynomial n)
  have huSq : u ^ 2 ≤ 1 := liCriticalCayleyCoordinate_square_le_one (x / 2)
  have huLower : -1 ≤ u := by nlinarith [sq_nonneg (u + 1)]
  have huUpper : u ≤ 1 := by nlinarith [sq_nonneg (u - 1)]
  have huAbs : |u| ≤ 1 := abs_le.mpr ⟨huLower, huUpper⟩
  have hEvalAbs : |(liEvenCrossLeftPolynomial n).eval u| ≤ C :=
    abs_eval_le_polynomialCoefficientMass _ huAbs
  have hC : 0 ≤ C := polynomialCoefficientMass_nonneg _
  have hEvalSq : ((liEvenCrossLeftPolynomial n).eval u) ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs]
    have hprod : 0 ≤
        (C - |(liEvenCrossLeftPolynomial n).eval u|) *
          (C + |(liEvenCrossLeftPolynomial n).eval u|) :=
      mul_nonneg (sub_nonneg.mpr hEvalAbs)
        (add_nonneg hC (abs_nonneg _))
    nlinarith
  have hfactor : (1 - u ^ 2) / 2 = 2 * x ^ 2 / (1 + x ^ 2) ^ 2 := by
    dsimp only [u]
    rw [liCriticalCayleyCoordinate]
    have h : (1 / 2 : ℝ) ^ 2 + (x / 2) ^ 2 ≠ 0 := by positivity
    have h' : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
    field_simp [h, h']
    ring
  have hbase : 0 ≤ 2 * x ^ 2 / (1 + x ^ 2) ^ 2 := by positivity
  rw [liUnitEvenCrossCauchyDensity,
    liCriticalEvenCrossCauchyDensity_eq_squareDefect]
  change (1 - u ^ 2) / 2 * ((liEvenCrossLeftPolynomial n).eval u) ^ 2 ≤ _
  rw [hfactor]
  calc
    2 * x ^ 2 / (1 + x ^ 2) ^ 2 *
        ((liEvenCrossLeftPolynomial n).eval u) ^ 2 ≤
        (2 * x ^ 2 / (1 + x ^ 2) ^ 2) * C ^ 2 :=
      mul_le_mul_of_nonneg_left hEvalSq hbase
    _ ≤ (2 * C ^ 2) * (1 + x ^ 2)⁻¹ := by
      have hden : 0 < 1 + x ^ 2 := by positivity
      have hxratio : x ^ 2 / (1 + x ^ 2) ≤ 1 :=
        (div_le_one hden).2 (by linarith)
      calc
        2 * x ^ 2 / (1 + x ^ 2) ^ 2 * C ^ 2 =
            ((2 * C ^ 2) * (1 + x ^ 2)⁻¹) *
              (x ^ 2 / (1 + x ^ 2)) := by
          rw [inv_eq_one_div]
          field_simp [hden.ne']
        _ ≤ ((2 * C ^ 2) * (1 + x ^ 2)⁻¹) * 1 :=
          mul_le_mul_of_nonneg_left hxratio (by positivity)
        _ = _ := by ring

theorem integrable_liUnitEvenCrossCauchyDensity (n : ℕ) :
    Integrable (liUnitEvenCrossCauchyDensity n) := by
  let C := 2 * polynomialCoefficientMass (liEvenCrossLeftPolynomial n) ^ 2
  have hmajor : Integrable (fun x : ℝ => C * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  refine Integrable.mono' hmajor ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hcont : Continuous (fun x : ℝ =>
        (1 - Real.cos (2 * ((n + 1 : ℕ) : ℝ) * Real.arctan x) ^ 2) / 2) := by
      fun_prop
    exact hcont.congr fun x => (liUnitEvenCrossCauchyDensity_eq_cos n x).symm
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact liUnitEvenCrossCauchyDensity_le_cauchyMajorant n x
  · exact liCriticalEvenCrossCauchyDensity_nonneg n (x / 2)

def liUnitEvenCrossKernelDefect (n : ℕ) (x : ℝ) : ℂ :=
  routeUCauchyKernel x - routeUCayleyCosineSquareKernel (2 * (n + 1)) x

theorem integrable_routeUCayleyCosineSquareKernel_all
    {m : ℕ} (hm : 0 < m) :
    Integrable (routeUCayleyCosineSquareKernel m) := by
  rw [show routeUCayleyCosineSquareKernel m = fun x : ℝ =>
      (1 / 4 : ℂ) * (((2 : ℂ) * routeUCauchyKernel x +
        routeUCayleyModeKernel m x) + routeUCayleyInverseModeKernel m x) by
    funext x
    rw [routeUCayleyCosineSquareKernel]
    ring]
  exact (((integrable_routeUCauchyKernel.const_mul (2 : ℂ)).add
    (integrable_routeUCayleyModeKernel hm)).add
      (integrable_routeUCayleyInverseModeKernel hm)).const_mul (1 / 4 : ℂ)

theorem integrable_liUnitEvenCrossKernelDefect (n : ℕ) :
    Integrable (liUnitEvenCrossKernelDefect n) := by
  exact integrable_routeUCauchyKernel.sub
    (integrable_routeUCayleyCosineSquareKernel_all (by omega))

theorem liUnitEvenCrossKernelDefect_weighted_eq (n : ℕ) (x : ℝ) :
    (x : ℂ) ^ 2 * liUnitEvenCrossKernelDefect n x =
      2 * (liUnitEvenCrossCauchyDensity n x : ℂ) -
        liUnitEvenCrossKernelDefect n x := by
  rw [liUnitEvenCrossCauchyDensity_eq_kernelDefect]
  simp only [liUnitEvenCrossKernelDefect]
  push_cast
  ring

theorem integrable_sq_mul_liUnitEvenCrossKernelDefect (n : ℕ) :
    Integrable (fun x : ℝ =>
      (x : ℂ) ^ 2 * liUnitEvenCrossKernelDefect n x) := by
  have hD : Integrable (fun x : ℝ =>
      (liUnitEvenCrossCauchyDensity n x : ℂ)) :=
    (integrable_liUnitEvenCrossCauchyDensity n).ofReal
  have hR : Integrable (fun x : ℝ =>
      2 * (liUnitEvenCrossCauchyDensity n x : ℂ) -
        liUnitEvenCrossKernelDefect n x) :=
    (hD.const_mul 2).sub (integrable_liUnitEvenCrossKernelDefect n)
  exact hR.congr (Filter.Eventually.of_forall fun x =>
    (liUnitEvenCrossKernelDefect_weighted_eq n x).symm)

theorem hasDerivAt_routeUFourierIntegral
    {f : ℝ → ℂ} (hf : Integrable f)
    (hxf : Integrable (fun x : ℝ => (x : ℂ) * f x)) (ξ : ℝ) :
    HasDerivAt (routeUFourierIntegral f)
      (∫ x : ℝ, f x * (-I * (x : ℂ)) *
        Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) ξ := by
  change HasDerivAt
    (fun η : ℝ => ∫ x : ℝ,
      f x * Complex.exp (-I * ((η * x : ℝ) : ℂ))) _ ξ
  let F : ℝ → ℝ → ℂ := fun η x =>
    f x * Complex.exp (-I * ((η * x : ℝ) : ℂ))
  let F' : ℝ → ℝ → ℂ := fun η x =>
    f x * (-I * (x : ℂ)) * Complex.exp (-I * ((η * x : ℝ) : ℂ))
  have hFi : ∀ η : ℝ, Integrable (F η) := by
    intro η
    apply hf.mul_bdd (by fun_prop)
    filter_upwards with x
    rw [show -I * ((η * x : ℝ) : ℂ) = (((-(η * x) : ℝ) : ℂ) * I) by
      push_cast
      ring]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  have hF'i : ∀ η : ℝ, Integrable (F' η) := by
    intro η
    have hbase : Integrable (fun x : ℝ => f x * (-I * (x : ℂ))) := by
      convert hxf.const_mul (-I) using 1
      funext x
      ring
    apply hbase.mul_bdd (by fun_prop)
    filter_upwards with x
    rw [show -I * ((η * x : ℝ) : ℂ) = (((-(η * x) : ℝ) : ℂ) * I) by
      push_cast
      ring]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := ξ) (s := Set.univ)
    (by exact univ_mem)
    (Filter.Eventually.of_forall fun η => (hFi η).aestronglyMeasurable)
    (hFi ξ)
    (hF'i ξ).aestronglyMeasurable
    (bound := fun x : ℝ => ‖(x : ℂ) * f x‖)
    (Filter.Eventually.of_forall fun x η hη => by
      dsimp only [F']
      have hexp : ‖Complex.exp (-I * ((η * x : ℝ) : ℂ))‖ = 1 := by
        rw [show -I * ((η * x : ℝ) : ℂ) = (((-(η * x) : ℝ) : ℂ) * I) by
          push_cast
          ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [norm_mul, hexp, mul_one]
      simp [mul_comm])
    hxf.norm
    (Filter.Eventually.of_forall fun x η hη => by
      change HasDerivAt
        (fun η : ℝ => f x * Complex.exp (-I * ((η * x : ℝ) : ℂ)))
        (f x * (-I * (x : ℂ)) *
          Complex.exp (-I * ((η * x : ℝ) : ℂ))) η
      have hreal0 : HasDerivAt (fun η : ℝ => -(η * x)) (-x) η := by
        have htmp := ((hasDerivAt_id η).mul_const x).neg
        change HasDerivAt (fun y : ℝ => -(y * x)) (-(1 * x)) η at htmp
        simpa only [one_mul] using htmp
      have hderiv : deriv (fun η : ℝ => -(η * x)) η = -x := hreal0.deriv
      have hreal : HasDerivAt (fun η : ℝ => -(η * x))
          (deriv (fun η : ℝ => -(η * x)) η) η := by
        rw [hderiv]
        exact hreal0
      have hp := hasDerivAt_phase η hreal
      have hmul := hp.const_mul (f x)
      rw [hderiv] at hmul
      have hexp_eq (y : ℝ) :
          Complex.exp (-I * ((y * x : ℝ) : ℂ)) =
            Complex.exp (I * ((-(y * x) : ℝ) : ℂ)) := by
        congr 1
        push_cast
        ring
      have hfun : (fun y : ℝ =>
          f x * Complex.exp (-I * ((y * x : ℝ) : ℂ))) =
          (fun y : ℝ => f x * Complex.exp (I * ((-(y * x) : ℝ) : ℂ))) := by
        funext y
        rw [hexp_eq]
      have hval :
          f x * (-I * (x : ℂ)) *
              Complex.exp (-I * ((η * x : ℝ) : ℂ)) =
            f x * (Complex.exp (I * ((-(η * x) : ℝ) : ℂ)) *
              (I * ((-x : ℝ) : ℂ))) := by
        rw [hexp_eq]
        push_cast
        ring
      rw [hfun, hval]
      exact hmul)
  simpa only [F, F'] using hmain.2

theorem hasDerivAt_routeUFourierIntegral_eq
    {f : ℝ → ℂ} (hf : Integrable f)
    (hxf : Integrable (fun x : ℝ => (x : ℂ) * f x)) (ξ : ℝ) :
    HasDerivAt (routeUFourierIntegral f)
      (routeUFourierIntegral (fun x : ℝ =>
        f x * (-I * (x : ℂ))) ξ) ξ := by
  simpa only [routeUFourierIntegral] using
    hasDerivAt_routeUFourierIntegral hf hxf ξ

theorem hasDerivAt_routeUFourierIntegral_firstWeighted
    {f : ℝ → ℂ} (hxf : Integrable (fun x : ℝ => (x : ℂ) * f x))
    (hx2f : Integrable (fun x : ℝ => (x : ℂ) ^ 2 * f x)) (ξ : ℝ) :
    HasDerivAt
      (fun η : ℝ => routeUFourierIntegral
        (fun x : ℝ => f x * (-I * (x : ℂ))) η)
      (-routeUFourierIntegral (fun x : ℝ => (x : ℂ) ^ 2 * f x) ξ) ξ := by
  have hg : Integrable (fun x : ℝ => f x * (-I * (x : ℂ))) := by
    have h := hxf.const_mul (-I)
    convert h using 1
    funext x
    ring
  have hxg : Integrable (fun x : ℝ =>
      (x : ℂ) * (f x * (-I * (x : ℂ)))) := by
    have h := hx2f.const_mul (-I)
    convert h using 1
    funext x
    ring
  have hder := hasDerivAt_routeUFourierIntegral_eq hg hxg ξ
  convert hder using 1
  rw [routeUFourierIntegral, routeUFourierIntegral, ← MeasureTheory.integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  have hi : (-I : ℂ) * (-I) = -1 := by
    rw [neg_mul_neg, ← pow_two, Complex.I_sq]
  calc
    -((x : ℂ) ^ 2 * f x * Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) =
        f x * (((-I) * (-I)) * (x : ℂ) ^ 2) *
          Complex.exp (-I * ((ξ * x : ℝ) : ℂ)) := by rw [hi]; ring
    _ = f x * (-I * (x : ℂ)) * (-I * (x : ℂ)) *
          Complex.exp (-I * ((ξ * x : ℝ) : ℂ)) := by ring

theorem integrable_mul_of_integrable_sq_mul
    {f : ℝ → ℂ} (hf : Integrable f)
    (hx2f : Integrable (fun x : ℝ => (x : ℂ) ^ 2 * f x)) :
    Integrable (fun x : ℝ => (x : ℂ) * f x) := by
  have hmajor : Integrable (fun x : ℝ => ‖f x‖ + ‖(x : ℂ) ^ 2 * f x‖) :=
    hf.norm.add hx2f.norm
  refine Integrable.mono' hmajor ?_ ?_
  · exact ((Complex.continuous_ofReal.comp continuous_id).aestronglyMeasurable.mul
      hf.aestronglyMeasurable)
  filter_upwards with x
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  have hx : |x| ≤ 1 + x ^ 2 := by
    nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x]
  calc
    |x| * ‖f x‖ ≤ (1 + x ^ 2) * ‖f x‖ :=
      mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = ‖f x‖ + ‖(x : ℂ) ^ 2 * f x‖ := by
      rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, sq_abs]
      ring

theorem integrable_mul_liUnitEvenCrossKernelDefect (n : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) * liUnitEvenCrossKernelDefect n x) :=
  integrable_mul_of_integrable_sq_mul
    (integrable_liUnitEvenCrossKernelDefect n)
    (integrable_sq_mul_liUnitEvenCrossKernelDefect n)

private theorem integrable_routeUFourierIntegrand_all
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x : ℝ =>
      f x * Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) := by
  apply hf.mul_bdd (by fun_prop)
  filter_upwards with x
  rw [show -I * ((ξ * x : ℝ) : ℂ) = (((-(ξ * x) : ℝ) : ℂ) * I) by
    push_cast
    ring]
  exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)

theorem routeUFourierIntegral_liUnitEvenCrossKernelDefect
    (n : ℕ) (ξ : ℝ) :
    routeUFourierIntegral (liUnitEvenCrossKernelDefect n) ξ =
      ((Real.pi / 4 * Real.exp (-|ξ|) *
        (2 - routeUAssociatedLaguerreMinusOne
          (2 * (n + 1)) (2 * |ξ|)) : ℝ) : ℂ) := by
  rw [routeUFourierIntegral]
  have hC := integrable_routeUFourierIntegrand_all
    integrable_routeUCauchyKernel ξ
  have hK := integrable_routeUFourierIntegrand_all
    (integrable_routeUCayleyCosineSquareKernel_all (by omega : 0 < 2 * (n + 1))) ξ
  simp only [liUnitEvenCrossKernelDefect]
  rw [show (∫ x : ℝ,
      (routeUCauchyKernel x -
          routeUCayleyCosineSquareKernel (2 * (n + 1)) x) *
        Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) =
      (∫ x : ℝ, routeUCauchyKernel x *
        Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) -
      (∫ x : ℝ, routeUCayleyCosineSquareKernel (2 * (n + 1)) x *
        Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) by
    rw [← integral_sub hC hK]
    apply integral_congr_ae
    filter_upwards with x
    ring]
  rw [← routeUFourierIntegral, ← routeUFourierIntegral,
    routeUFourierIntegral_cauchyKernel,
    routeUFourierIntegral_cayleyCosineSquareKernel (by omega)]
  have heven : (-1 : ℝ) ^ (2 * (n + 1)) = 1 := by
    rw [pow_mul]
    norm_num
  rw [heven, one_mul]
  push_cast
  ring

def routeUAssociatedLaguerreMinusOnePolynomial (m : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range m,
    Polynomial.C
      ((-1 : ℝ) ^ (k + 1) * (Nat.choose (m - 1) k : ℝ) /
        ((k + 1).factorial : ℝ)) * X ^ (k + 1)

theorem eval_routeUAssociatedLaguerreMinusOnePolynomial (m : ℕ) (x : ℝ) :
    (routeUAssociatedLaguerreMinusOnePolynomial m).eval x =
      routeUAssociatedLaguerreMinusOne m x := by
  rw [routeUAssociatedLaguerreMinusOnePolynomial,
    routeUAssociatedLaguerreMinusOne]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro k hk
  ring

def liCrossLaguerreClockPolynomial (n : ℕ) : Polynomial ℝ :=
  (routeUAssociatedLaguerreMinusOnePolynomial (2 * (n + 1))).derivative.derivative -
    (routeUAssociatedLaguerreMinusOnePolynomial (2 * (n + 1))).derivative

def liUnitEvenCrossKernelDefectFourierProfile (n : ℕ) (ξ : ℝ) : ℝ :=
  Real.pi / 4 * (Real.exp (-ξ) *
    (2 - (routeUAssociatedLaguerreMinusOnePolynomial
      (2 * (n + 1))).eval (2 * ξ)))

def liUnitEvenCrossKernelDefectFourierProfileDeriv (n : ℕ) (ξ : ℝ) : ℝ :=
  let P := routeUAssociatedLaguerreMinusOnePolynomial (2 * (n + 1))
  Real.pi / 4 * (Real.exp (-ξ) *
    (P.eval (2 * ξ) - 2 - 2 * P.derivative.eval (2 * ξ)))

def liUnitEvenCrossKernelDefectFourierProfileSecondDeriv (n : ℕ) (ξ : ℝ) : ℝ :=
  let P := routeUAssociatedLaguerreMinusOnePolynomial (2 * (n + 1))
  Real.pi / 4 * (Real.exp (-ξ) *
    (4 * P.derivative.eval (2 * ξ) -
      4 * P.derivative.derivative.eval (2 * ξ) - P.eval (2 * ξ) + 2))

theorem hasDerivAt_polynomial_eval_two_mul (P : Polynomial ℝ) (ξ : ℝ) :
    HasDerivAt (fun η : ℝ => P.eval (2 * η))
      (2 * P.derivative.eval (2 * ξ)) ξ := by
  have hlin : HasDerivAt (fun η : ℝ => 2 * η) 2 ξ := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id ξ).const_mul 2
  have h := (P.hasDerivAt (2 * ξ)).comp ξ hlin
  change HasDerivAt (fun η : ℝ => P.eval (2 * η))
    (P.derivative.eval (2 * ξ) * 2) ξ at h
  simpa only [mul_comm] using h

private theorem hasDerivAt_exp_neg (ξ : ℝ) :
    HasDerivAt (fun η : ℝ => Real.exp (-η)) (-Real.exp (-ξ)) ξ := by
  have h := (Real.hasDerivAt_exp (-ξ)).comp ξ (hasDerivAt_id ξ).neg
  change HasDerivAt (fun η : ℝ => Real.exp (-η))
    (Real.exp (-ξ) * (-1)) ξ at h
  simpa only [mul_neg, mul_one] using h

theorem hasDerivAt_liUnitEvenCrossKernelDefectFourierProfile
    (n : ℕ) (ξ : ℝ) :
    HasDerivAt (liUnitEvenCrossKernelDefectFourierProfile n)
      (liUnitEvenCrossKernelDefectFourierProfileDeriv n ξ) ξ := by
  let P := routeUAssociatedLaguerreMinusOnePolynomial (2 * (n + 1))
  have hP := hasDerivAt_polynomial_eval_two_mul P ξ
  have hB : HasDerivAt (fun η : ℝ => 2 - P.eval (2 * η))
      (-2 * P.derivative.eval (2 * ξ)) ξ := by
    have hraw := (hasDerivAt_const ξ 2).sub hP
    change HasDerivAt (fun η : ℝ => 2 - P.eval (2 * η))
      (0 - 2 * P.derivative.eval (2 * ξ)) ξ at hraw
    have hval : 0 - 2 * P.derivative.eval (2 * ξ) =
        -2 * P.derivative.eval (2 * ξ) := by ring
    rw [hval] at hraw
    exact hraw
  have hprod := (hasDerivAt_exp_neg ξ).mul hB
  have hscaled := hprod.const_mul (Real.pi / 4)
  change HasDerivAt
    (fun ξ : ℝ => Real.pi / 4 * (Real.exp (-ξ) * (2 - P.eval (2 * ξ))))
    (Real.pi / 4 * (Real.exp (-ξ) *
      (P.eval (2 * ξ) - 2 - 2 * P.derivative.eval (2 * ξ)))) ξ
  have hval :
      Real.pi / 4 *
          ((-Real.exp (-ξ)) * (2 - P.eval (2 * ξ)) +
            Real.exp (-ξ) * (-2 * P.derivative.eval (2 * ξ))) =
        Real.pi / 4 * (Real.exp (-ξ) *
          (P.eval (2 * ξ) - 2 - 2 * P.derivative.eval (2 * ξ))) := by ring
  rw [hval] at hscaled
  exact hscaled

theorem hasDerivAt_liUnitEvenCrossKernelDefectFourierProfileDeriv
    (n : ℕ) (ξ : ℝ) :
    HasDerivAt (liUnitEvenCrossKernelDefectFourierProfileDeriv n)
      (liUnitEvenCrossKernelDefectFourierProfileSecondDeriv n ξ) ξ := by
  let P := routeUAssociatedLaguerreMinusOnePolynomial (2 * (n + 1))
  have hP := hasDerivAt_polynomial_eval_two_mul P ξ
  have hP' := hasDerivAt_polynomial_eval_two_mul P.derivative ξ
  have hC : HasDerivAt (fun η : ℝ =>
      P.eval (2 * η) - 2 - 2 * P.derivative.eval (2 * η))
      (2 * P.derivative.eval (2 * ξ) -
        4 * P.derivative.derivative.eval (2 * ξ)) ξ := by
    have hraw := (hP.sub_const 2).sub (hP'.const_mul 2)
    change HasDerivAt (fun η : ℝ =>
        P.eval (2 * η) - 2 - 2 * P.derivative.eval (2 * η))
      (2 * P.derivative.eval (2 * ξ) -
        2 * (2 * P.derivative.derivative.eval (2 * ξ))) ξ at hraw
    have hval :
        2 * P.derivative.eval (2 * ξ) -
            2 * (2 * P.derivative.derivative.eval (2 * ξ)) =
          2 * P.derivative.eval (2 * ξ) -
            4 * P.derivative.derivative.eval (2 * ξ) := by ring
    rw [hval] at hraw
    exact hraw
  have hprod := (hasDerivAt_exp_neg ξ).mul hC
  have hscaled := hprod.const_mul (Real.pi / 4)
  change HasDerivAt
    (fun ξ : ℝ => Real.pi / 4 * (Real.exp (-ξ) *
      (P.eval (2 * ξ) - 2 - 2 * P.derivative.eval (2 * ξ))))
    (Real.pi / 4 * (Real.exp (-ξ) *
      (4 * P.derivative.eval (2 * ξ) -
        4 * P.derivative.derivative.eval (2 * ξ) - P.eval (2 * ξ) + 2))) ξ
  have hval :
      Real.pi / 4 *
          ((-Real.exp (-ξ)) *
              (P.eval (2 * ξ) - 2 - 2 * P.derivative.eval (2 * ξ)) +
            Real.exp (-ξ) *
              (2 * P.derivative.eval (2 * ξ) -
                4 * P.derivative.derivative.eval (2 * ξ))) =
        Real.pi / 4 * (Real.exp (-ξ) *
          (4 * P.derivative.eval (2 * ξ) -
            4 * P.derivative.derivative.eval (2 * ξ) - P.eval (2 * ξ) + 2)) := by
    ring
  rw [hval] at hscaled
  exact hscaled

theorem routeUFourierIntegral_liUnitEvenCrossKernelDefect_eq_profile_of_pos
    (n : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    routeUFourierIntegral (liUnitEvenCrossKernelDefect n) ξ =
      (liUnitEvenCrossKernelDefectFourierProfile n ξ : ℂ) := by
  rw [routeUFourierIntegral_liUnitEvenCrossKernelDefect, abs_of_pos hξ,
    liUnitEvenCrossKernelDefectFourierProfile,
    eval_routeUAssociatedLaguerreMinusOnePolynomial]
  push_cast
  ring

theorem routeUFourierIntegral_liUnitEvenCrossKernelDefect_firstWeighted_eq_profileDeriv_of_pos
    (n : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    routeUFourierIntegral (fun x : ℝ =>
      liUnitEvenCrossKernelDefect n x * (-I * (x : ℂ))) ξ =
      (liUnitEvenCrossKernelDefectFourierProfileDeriv n ξ : ℂ) := by
  have hFourier := hasDerivAt_routeUFourierIntegral_eq
    (integrable_liUnitEvenCrossKernelDefect n)
    (integrable_mul_liUnitEvenCrossKernelDefect n) ξ
  have hProfile :=
    (hasDerivAt_liUnitEvenCrossKernelDefectFourierProfile n ξ).ofReal_comp
  have hEq : (fun η : ℝ =>
      (liUnitEvenCrossKernelDefectFourierProfile n η : ℂ)) =ᶠ[𝓝 ξ]
      routeUFourierIntegral (liUnitEvenCrossKernelDefect n) := by
    filter_upwards [isOpen_Ioi.mem_nhds hξ] with η hη
    exact (routeUFourierIntegral_liUnitEvenCrossKernelDefect_eq_profile_of_pos
      n hη).symm
  have hProfileFromFourier := hFourier.congr_of_eventuallyEq hEq
  exact hProfileFromFourier.unique hProfile

theorem routeUFourierIntegral_sq_mul_liUnitEvenCrossKernelDefect_eq_profile_of_pos
    (n : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    routeUFourierIntegral (fun x : ℝ =>
      (x : ℂ) ^ 2 * liUnitEvenCrossKernelDefect n x) ξ =
      -(liUnitEvenCrossKernelDefectFourierProfileSecondDeriv n ξ : ℂ) := by
  have hWeighted := hasDerivAt_routeUFourierIntegral_firstWeighted
    (integrable_mul_liUnitEvenCrossKernelDefect n)
    (integrable_sq_mul_liUnitEvenCrossKernelDefect n) ξ
  have hProfile :=
    (hasDerivAt_liUnitEvenCrossKernelDefectFourierProfileDeriv n ξ).ofReal_comp
  have hEq : (fun η : ℝ =>
      (liUnitEvenCrossKernelDefectFourierProfileDeriv n η : ℂ)) =ᶠ[𝓝 ξ]
      (fun η : ℝ => routeUFourierIntegral
        (fun x : ℝ => liUnitEvenCrossKernelDefect n x * (-I * (x : ℂ))) η) := by
    filter_upwards [isOpen_Ioi.mem_nhds hξ] with η hη
    exact (routeUFourierIntegral_liUnitEvenCrossKernelDefect_firstWeighted_eq_profileDeriv_of_pos
      n hη).symm
  have hProfileFromWeighted := hWeighted.congr_of_eventuallyEq hEq
  have hunique := hProfileFromWeighted.unique hProfile
  have hneg := congrArg Neg.neg hunique
  simpa only [neg_neg] using hneg

theorem routeUFourierIntegral_liUnitEvenCrossCauchyDensity_eq_half_sum
    (n : ℕ) (ξ : ℝ) :
    routeUFourierIntegral (fun x : ℝ =>
      (liUnitEvenCrossCauchyDensity n x : ℂ)) ξ =
      (1 / 2 : ℂ) *
        (routeUFourierIntegral (liUnitEvenCrossKernelDefect n) ξ +
          routeUFourierIntegral (fun x : ℝ =>
            (x : ℂ) ^ 2 * liUnitEvenCrossKernelDefect n x) ξ) := by
  rw [routeUFourierIntegral, routeUFourierIntegral, routeUFourierIntegral]
  have hH := integrable_routeUFourierIntegrand_all
    (integrable_liUnitEvenCrossKernelDefect n) ξ
  have hX := integrable_routeUFourierIntegrand_all
    (integrable_sq_mul_liUnitEvenCrossKernelDefect n) ξ
  rw [← integral_add hH hX, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [liUnitEvenCrossKernelDefect_weighted_eq]
  ring

theorem profile_sub_second_eq_laguerreClock (n : ℕ) (ξ : ℝ) :
    (liUnitEvenCrossKernelDefectFourierProfile n ξ -
        liUnitEvenCrossKernelDefectFourierProfileSecondDeriv n ξ) / 2 =
      Real.pi / 2 * Real.exp (-ξ) *
        (liCrossLaguerreClockPolynomial n).eval (2 * ξ) := by
  rw [liUnitEvenCrossKernelDefectFourierProfile,
    liUnitEvenCrossKernelDefectFourierProfileSecondDeriv,
    liCrossLaguerreClockPolynomial, Polynomial.eval_sub]
  ring

theorem routeUFourierIntegral_liUnitEvenCrossCauchyDensity_pos
    (n : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    routeUFourierIntegral (fun x : ℝ =>
      (liUnitEvenCrossCauchyDensity n x : ℂ)) ξ =
      ((Real.pi / 2 * Real.exp (-ξ) *
        (liCrossLaguerreClockPolynomial n).eval (2 * ξ) : ℝ) : ℂ) := by
  rw [routeUFourierIntegral_liUnitEvenCrossCauchyDensity_eq_half_sum,
    routeUFourierIntegral_liUnitEvenCrossKernelDefect_eq_profile_of_pos n hξ,
    routeUFourierIntegral_sq_mul_liUnitEvenCrossKernelDefect_eq_profile_of_pos n hξ]
  have hprofile := profile_sub_second_eq_laguerreClock n ξ
  calc
    (1 / 2 : ℂ) *
        ((liUnitEvenCrossKernelDefectFourierProfile n ξ : ℂ) +
          -(liUnitEvenCrossKernelDefectFourierProfileSecondDeriv n ξ : ℂ)) =
        (((liUnitEvenCrossKernelDefectFourierProfile n ξ -
          liUnitEvenCrossKernelDefectFourierProfileSecondDeriv n ξ) / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    _ = _ := by rw [hprofile]

theorem liUnitEvenCrossCauchyDensity_neg (n : ℕ) (x : ℝ) :
    liUnitEvenCrossCauchyDensity n (-x) = liUnitEvenCrossCauchyDensity n x := by
  rw [liUnitEvenCrossCauchyDensity_eq_cos,
    liUnitEvenCrossCauchyDensity_eq_cos, Real.arctan_neg]
  rw [show 2 * ((n + 1 : ℕ) : ℝ) * -Real.arctan x =
      -(2 * ((n + 1 : ℕ) : ℝ) * Real.arctan x) by ring,
    Real.cos_neg]

theorem routeUFourierIntegral_liUnitEvenCrossCauchyDensity_neg_frequency
    (n : ℕ) (ξ : ℝ) :
    routeUFourierIntegral (fun x : ℝ =>
      (liUnitEvenCrossCauchyDensity n x : ℂ)) (-ξ) =
      routeUFourierIntegral (fun x : ℝ =>
        (liUnitEvenCrossCauchyDensity n x : ℂ)) ξ := by
  rw [← routeUFourierIntegral_reflect]
  congr 1
  funext x
  rw [liUnitEvenCrossCauchyDensity_neg]

theorem routeUFourierIntegral_liUnitEvenCrossCauchyDensity_neg
    (n : ℕ) {ξ : ℝ} (hξ : ξ < 0) :
    routeUFourierIntegral (fun x : ℝ =>
      (liUnitEvenCrossCauchyDensity n x : ℂ)) ξ =
      ((Real.pi / 2 * Real.exp (-|ξ|) *
        (liCrossLaguerreClockPolynomial n).eval (2 * |ξ|) : ℝ) : ℂ) := by
  rw [← routeUFourierIntegral_liUnitEvenCrossCauchyDensity_neg_frequency n ξ]
  have hpos : 0 < -ξ := neg_pos.mpr hξ
  rw [routeUFourierIntegral_liUnitEvenCrossCauchyDensity_pos n hpos,
    abs_of_neg hξ]

theorem continuousAt_routeUFourierIntegral
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    ContinuousAt (routeUFourierIntegral f) ξ := by
  rw [continuousAt_def]
  rw [routeUFourierIntegral]
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => ‖f x‖)
  · exact Filter.Eventually.of_forall fun η =>
      (integrable_routeUFourierIntegrand_all hf η).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun η =>
      Filter.Eventually.of_forall fun a => by
        rw [norm_mul]
        have hexp : ‖Complex.exp (-I * ((η * a : ℝ) : ℂ))‖ = 1 := by
          rw [show -I * ((η * a : ℝ) : ℂ) = (((-(η * a) : ℝ) : ℂ) * I) by
            push_cast
            ring]
          exact Complex.norm_exp_ofReal_mul_I _
        rw [hexp, mul_one]
  · exact hf.norm
  · filter_upwards with x
    have hphase : Tendsto
        (fun n : ℝ => Complex.exp (-I * ((n * x : ℝ) : ℂ)))
        (𝓝 ξ) (𝓝 (Complex.exp (-I * ((ξ * x : ℝ) : ℂ)))) := by
      exact (by fun_prop : ContinuousAt
        (fun n : ℝ => Complex.exp (-I * ((n * x : ℝ) : ℂ))) ξ)
    exact tendsto_const_nhds.mul hphase

def liUnitEvenCrossLaguerreFourierProfile (n : ℕ) (ξ : ℝ) : ℂ :=
  ((Real.pi / 2 * Real.exp (-|ξ|) *
    (liCrossLaguerreClockPolynomial n).eval (2 * |ξ|) : ℝ) : ℂ)

theorem continuous_liUnitEvenCrossLaguerreFourierProfile (n : ℕ) :
    Continuous (liUnitEvenCrossLaguerreFourierProfile n) := by
  unfold liUnitEvenCrossLaguerreFourierProfile
  fun_prop

theorem routeUFourierIntegral_liUnitEvenCrossCauchyDensity_zero (n : ℕ) :
    routeUFourierIntegral (fun x : ℝ =>
      (liUnitEvenCrossCauchyDensity n x : ℂ)) 0 =
      liUnitEvenCrossLaguerreFourierProfile n 0 := by
  let F : ℝ → ℂ := fun ξ => routeUFourierIntegral (fun x : ℝ =>
    (liUnitEvenCrossCauchyDensity n x : ℂ)) ξ
  let G : ℝ → ℂ := liUnitEvenCrossLaguerreFourierProfile n
  have hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) :=
    ((continuousAt_routeUFourierIntegral
      (integrable_liUnitEvenCrossCauchyDensity n).ofReal 0).tendsto).mono_left
        inf_le_left
  have hG : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (G 0)) :=
    ((continuous_liUnitEvenCrossLaguerreFourierProfile n).continuousAt.tendsto).mono_left
      inf_le_left
  have hEq : F =ᶠ[𝓝[>] (0 : ℝ)] G := by
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    dsimp only [F, G, liUnitEvenCrossLaguerreFourierProfile]
    rw [abs_of_pos hξ]
    exact routeUFourierIntegral_liUnitEvenCrossCauchyDensity_pos n hξ
  have hG' : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (G 0)) := hG.congr' hEq.symm
  exact tendsto_nhds_unique hF hG'

theorem routeUFourierIntegral_liUnitEvenCrossCauchyDensity (n : ℕ) (ξ : ℝ) :
    routeUFourierIntegral (fun x : ℝ =>
      (liUnitEvenCrossCauchyDensity n x : ℂ)) ξ =
      liUnitEvenCrossLaguerreFourierProfile n ξ := by
  rcases lt_trichotomy ξ 0 with hneg | rfl | hpos
  · unfold liUnitEvenCrossLaguerreFourierProfile
    exact routeUFourierIntegral_liUnitEvenCrossCauchyDensity_neg n hneg
  · exact routeUFourierIntegral_liUnitEvenCrossCauchyDensity_zero n
  · unfold liUnitEvenCrossLaguerreFourierProfile
    rw [abs_of_pos hpos]
    exact routeUFourierIntegral_liUnitEvenCrossCauchyDensity_pos n hpos

theorem liCriticalEvenCrossCauchyDensity_eq_unit_scaled (n : ℕ) (x : ℝ) :
    (liCriticalEvenCrossCauchyDensity n x : ℂ) =
      (liUnitEvenCrossCauchyDensity n (2 * x) : ℂ) := by
  rw [liUnitEvenCrossCauchyDensity]
  norm_num

def liCriticalEvenCrossLaguerreFourierProfile (n : ℕ) (ξ : ℝ) : ℂ :=
  ((Real.pi / 4 * Real.exp (-|ξ| / 2) *
    (liCrossLaguerreClockPolynomial n).eval |ξ| : ℝ) : ℂ)

theorem routeUFourierIntegral_liCriticalEvenCrossCauchyDensity
    (n : ℕ) (ξ : ℝ) :
    routeUFourierIntegral (fun x : ℝ =>
      (liCriticalEvenCrossCauchyDensity n x : ℂ)) ξ =
      liCriticalEvenCrossLaguerreFourierProfile n ξ := by
  let G : ℝ → ℂ := fun y =>
    (liUnitEvenCrossCauchyDensity n y : ℂ) *
      Complex.exp (-I * ((((ξ / 2) * y : ℝ) : ℂ)))
  have hscale := MeasureTheory.Measure.integral_comp_mul_left G 2
  norm_num at hscale
  rw [routeUFourierIntegral]
  rw [show (fun x : ℝ => (liCriticalEvenCrossCauchyDensity n x : ℂ) *
      Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) = fun x : ℝ => G (2 * x) by
    funext x
    rw [liCriticalEvenCrossCauchyDensity_eq_unit_scaled]
    dsimp only [G]
    congr 2
    push_cast
    ring]
  rw [hscale]
  dsimp only [G]
  change (1 / 2 : ℂ) * routeUFourierIntegral
    (fun x : ℝ => (liUnitEvenCrossCauchyDensity n x : ℂ)) (ξ / 2) = _
  rw [routeUFourierIntegral_liUnitEvenCrossCauchyDensity]
  unfold liUnitEvenCrossLaguerreFourierProfile
    liCriticalEvenCrossLaguerreFourierProfile
  have habs : |ξ / 2| = |ξ| / 2 := by rw [abs_div]; norm_num
  rw [habs]
  push_cast
  ring

end

end RHTower
