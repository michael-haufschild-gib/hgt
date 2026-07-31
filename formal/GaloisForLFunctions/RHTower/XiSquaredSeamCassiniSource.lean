import GaloisForLFunctions.HTGeometry.EvenEntireSquareFactor
import GaloisForLFunctions.RHTower.XiSquaredSeamPowerSixtyFourJensenKernel

/-!
# Entire Cassini source for the shift-one squared-Xi seam

The even entire function `XiC` descends through `z ↦ z²` to an entire quotient `Q`.  Translating
that quotient by `u ↦ u - 1` produces the Cassini source `Ψ`.  Its center is the Euler-safe value
`ξ(3/2)`, and every Xi spectral zero `α` maps to the zero `1 + α²`, exactly the inverse of the
shift-one squared-seam coordinate.  The analytic multiplicity is preserved because both the square
map at `α ≠ 0` and the translation have nonzero derivative.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Entire quotient `Q` characterized by `Q (z²) = XiC z`. -/
def xiSquaredSeamEntireQuotient : ℂ → ℂ :=
  GaloisForLFunctions.HTGeometry.evenEntireSquareFactor XiC

/-- Translated squared-coordinate source.  Its zero coordinate is the inverse shift-one seam
coordinate. -/
def xiSquaredSeamCassiniSource (u : ℂ) : ℂ :=
  xiSquaredSeamEntireQuotient (u - 1)

/-- Image of one multiplicity copy of an Xi zero in the translated squared coordinate. -/
def xiSquaredSeamCassiniZero (q : XiZeroCopy) : ℂ :=
  1 + xiSpectralPoint q ^ 2

/-- Cassini coordinate attached to one Xi divisor support point, before multiplicity copies. -/
def xiSquaredSeamCassiniZeroSupport (rho : XiDivisorSupport) : ℂ :=
  1 + xiSpectralPointSupport rho ^ 2

theorem differentiable_xiSquaredSeamEntireQuotient :
    Differentiable ℂ xiSquaredSeamEntireQuotient := by
  exact GaloisForLFunctions.HTGeometry.differentiable_evenEntireSquareFactor
    XiC_differentiable

/-- Exact square-factor identity for the centered Xi function. -/
theorem xiSquaredSeamEntireQuotient_sq (z : ℂ) :
    xiSquaredSeamEntireQuotient (z ^ 2) = XiC z := by
  exact GaloisForLFunctions.HTGeometry.evenEntireSquareFactor_sq
    XiC_differentiable (fun w => XiC_even w) z

theorem differentiable_xiSquaredSeamCassiniSource :
    Differentiable ℂ xiSquaredSeamCassiniSource := by
  exact differentiable_xiSquaredSeamEntireQuotient.comp (by fun_prop)

/-- The translated quotient is centered at the Euler-safe point `s = 3/2`. -/
theorem xiSquaredSeamCassiniSource_zero_eq_xi_threeHalves :
    xiSquaredSeamCassiniSource 0 = xi (3 / 2) := by
  calc
    xiSquaredSeamCassiniSource 0 = xiSquaredSeamEntireQuotient ((-I) ^ 2) := by
      rw [xiSquaredSeamCassiniSource]
      congr 1
      simp [pow_two, Complex.I_mul_I]
    _ = XiC (-I) := xiSquaredSeamEntireQuotient_sq (-I)
    _ = xi (3 / 2) := by
      rw [XiC]
      congr 1
      rw [neg_mul, Complex.I_mul_I]
      ring

theorem xiSquaredSeamCassiniSource_zero_ne :
    xiSquaredSeamCassiniSource 0 ≠ 0 := by
  rw [xiSquaredSeamCassiniSource_zero_eq_xi_threeHalves]
  apply xi_ne_zero_of_one_lt_re
  norm_num

/-- The Cassini source is not locally zero at any point. -/
theorem xiSquaredSeamCassiniSource_order_ne_top (u : ℂ) :
    analyticOrderAt xiSquaredSeamCassiniSource u ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ xiSquaredSeamCassiniSource Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr
      differentiable_xiSquaredSeamCassiniSource
  apply han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 0) (y := u) (Set.mem_univ _) (Set.mem_univ _)
  rw [analyticOrderAt_eq_zero.mpr (Or.inr xiSquaredSeamCassiniSource_zero_ne)]
  exact ENat.zero_ne_top

/-- Cassini zero coordinate is exactly the inverse shifted seam atom. -/
theorem xiSquaredSeamCassiniZero_eq_coordinate_inv (q : XiZeroCopy) :
    xiSquaredSeamCassiniZero q = (xiSquaredSeamOneCoordinate q)⁻¹ := by
  rw [xiSquaredSeamOneCoordinate, inv_inv]
  unfold xiSquaredSeamCassiniZero xiSpectralPoint
  unfold xiSquaredSeamOneRadialA xiSquaredSeamTransverseB
  apply Complex.ext <;>
    simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem norm_xiSquaredSeamCassiniZero (q : XiZeroCopy) :
    ‖xiSquaredSeamCassiniZero q‖ = xiSquaredSeamInverseRadius q := by
  rw [xiSquaredSeamCassiniZero_eq_coordinate_inv,
    xiSquaredSeamInverseRadius]

/-- Every multiplicity copy of an Xi zero maps to a zero of the Cassini source. -/
theorem xiSquaredSeamCassiniSource_zero (q : XiZeroCopy) :
    xiSquaredSeamCassiniSource (xiSquaredSeamCassiniZero q) = 0 := by
  calc
    xiSquaredSeamCassiniSource (xiSquaredSeamCassiniZero q) =
        xiSquaredSeamEntireQuotient (xiSpectralPoint q ^ 2) := by
      simp only [xiSquaredSeamCassiniSource, xiSquaredSeamCassiniZero]
      congr 1
      ring
    _ = XiC (xiSpectralPoint q) :=
      xiSquaredSeamEntireQuotient_sq (xiSpectralPoint q)
    _ = 0 := XiC_xiSpectralPoint_eq_zero q

theorem xiSquaredSeamCassiniZero_eq_support (q : XiZeroCopy) :
    xiSquaredSeamCassiniZero q = xiSquaredSeamCassiniZeroSupport q.1 := by
  rw [xiSquaredSeamCassiniZero, xiSquaredSeamCassiniZeroSupport,
    xiSpectralPoint_eq_support]

/-- Every Xi divisor support point maps to a Cassini source zero. -/
theorem xiSquaredSeamCassiniSource_zero_support (rho : XiDivisorSupport) :
    xiSquaredSeamCassiniSource (xiSquaredSeamCassiniZeroSupport rho) = 0 := by
  have hpos := xi_divisor_pos_on_support rho
  have hm : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨rho, ⟨0, hm⟩⟩
  simpa only [xiSquaredSeamCassiniZero_eq_support] using
    xiSquaredSeamCassiniSource_zero q

/-- The square and translation maps are unramified at every Xi zero, so the source zero keeps the
exact Xi analytic multiplicity. -/
theorem analyticOrderAt_xiSquaredSeamCassiniSource_cassiniZero
    (q : XiZeroCopy) :
    analyticOrderAt xiSquaredSeamCassiniSource (xiSquaredSeamCassiniZero q) =
      analyticOrderAt XiC (xiSpectralPoint q) := by
  let a := xiSpectralPoint q
  let u := xiSquaredSeamCassiniZero q
  let shift : ℂ → ℂ := fun w => w - 1
  have hshiftDeriv : HasDerivAt shift 1 u := by
    dsimp only [shift]
    simpa using (hasDerivAt_id u).sub_const 1
  have hshiftAnalytic : AnalyticAt ℂ shift u := by
    dsimp only [shift]
    fun_prop
  have hshift := analyticOrderAt_comp_of_deriv_ne_zero
    (f := xiSquaredSeamEntireQuotient) hshiftAnalytic
    (by rw [hshiftDeriv.deriv]; norm_num)
  have hsourceComp : xiSquaredSeamCassiniSource =
      xiSquaredSeamEntireQuotient ∘ shift := by
    rfl
  have hsourceOrder :
      analyticOrderAt xiSquaredSeamCassiniSource u =
        analyticOrderAt xiSquaredSeamEntireQuotient (a ^ 2) := by
    rw [hsourceComp, hshift]
    congr 1
    simp only [shift, u, a, xiSquaredSeamCassiniZero]
    ring
  let sq : ℂ → ℂ := fun w => w ^ 2
  have hsqDeriv : HasDerivAt sq (2 * a) a := by
    dsimp only [sq]
    convert hasDerivAt_pow 2 a using 1
    all_goals first | rfl | ring
  have hsqAnalytic : AnalyticAt ℂ sq a := by
    dsimp only [sq]
    fun_prop
  have haderiv : 2 * a ≠ 0 :=
    mul_ne_zero (by norm_num) (xiSpectralPoint_ne_zero q)
  have hsqOrder := analyticOrderAt_comp_of_deriv_ne_zero
    (f := xiSquaredSeamEntireQuotient) hsqAnalytic
    (by rw [hsqDeriv.deriv]; exact haderiv)
  have hfactor : xiSquaredSeamEntireQuotient ∘ sq = XiC := by
    funext z
    exact xiSquaredSeamEntireQuotient_sq z
  rw [hfactor] at hsqOrder
  exact hsourceOrder.trans hsqOrder.symm

theorem analyticOrderAt_xiSquaredSeamCassiniSource_cassiniZero_eq_multiplicity
    (q : XiZeroCopy) :
    analyticOrderAt xiSquaredSeamCassiniSource (xiSquaredSeamCassiniZero q) =
      Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q.1 : ℂ)) := by
  rw [analyticOrderAt_xiSquaredSeamCassiniSource_cassiniZero,
    xiSpectralPoint_eq_support, XiC_analyticOrderAt_support]

theorem analyticOrderAt_xiSquaredSeamCassiniSource_cassiniZeroSupport_eq_multiplicity
    (rho : XiDivisorSupport) :
    analyticOrderAt xiSquaredSeamCassiniSource
        (xiSquaredSeamCassiniZeroSupport rho) =
      Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
  have hpos := xi_divisor_pos_on_support rho
  have hm : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨rho, ⟨0, hm⟩⟩
  simpa only [xiSquaredSeamCassiniZero_eq_support] using
    analyticOrderAt_xiSquaredSeamCassiniSource_cassiniZero_eq_multiplicity q

/-- Divisor formulation of exact multiplicity preservation. -/
theorem xiSquaredSeamCassiniSource_divisor_cassiniZero_eq_multiplicity
    (q : XiZeroCopy) :
    (MeromorphicOn.divisor xiSquaredSeamCassiniSource Set.univ)
        (xiSquaredSeamCassiniZero q) =
      Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q.1 : ℂ)) := by
  have han : AnalyticOnNhd ℂ xiSquaredSeamCassiniSource Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr
      differentiable_xiSquaredSeamCassiniSource
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply han (Set.mem_univ _),
    analyticOrderAt_xiSquaredSeamCassiniSource_cassiniZero_eq_multiplicity]
  simp

/-- The Cassini source has no extra zeros: every source zero comes from an actual Xi divisor
copy under the translated square map. -/
theorem xiSquaredSeamCassiniSource_eq_zero_iff_exists_zeroCopy (u : ℂ) :
    xiSquaredSeamCassiniSource u = 0 ↔
      ∃ q : XiZeroCopy, xiSquaredSeamCassiniZero q = u := by
  constructor
  · intro hu
    let a := Complex.sqrt (u - 1)
    have ha : a ^ 2 = u - 1 := by
      exact GaloisForLFunctions.HTGeometry.complex_sqrt_sq (u - 1)
    have hXi : XiC a = 0 := by
      rw [← xiSquaredSeamEntireQuotient_sq a, ha]
      exact hu
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy a).mp hXi
    refine ⟨q, ?_⟩
    rw [xiSquaredSeamCassiniZero, hq, ha]
    ring
  · rintro ⟨q, rfl⟩
    exact xiSquaredSeamCassiniSource_zero q

/-- Two Xi copies have the same Cassini source coordinate exactly when their centered spectral
coordinates agree up to functional-equation reflection. -/
theorem xiSquaredSeamCassiniZero_eq_iff_spectral_eq_or_neg
    (p q : XiZeroCopy) :
    xiSquaredSeamCassiniZero p = xiSquaredSeamCassiniZero q ↔
      xiSpectralPoint p = xiSpectralPoint q ∨
        xiSpectralPoint p = -xiSpectralPoint q := by
  constructor
  · intro h
    have hsq : xiSpectralPoint p ^ 2 = xiSpectralPoint q ^ 2 := by
      simpa only [xiSquaredSeamCassiniZero] using add_left_cancel h
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  · intro h
    have hsq := sq_eq_sq_iff_eq_or_eq_neg.mpr h
    simp only [xiSquaredSeamCassiniZero, hsq]

end

end RHTower
