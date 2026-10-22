import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinCuspJointSmooth
import GaloisForLFunctions.HTGeometry.ScalarTwoJetCalculus

/-!
# Actual scalar equation of the complete literal cusp field

The actual coordinate second derivatives follow from the derivative-stable
infinite Fourier--Bessel family. Three corpus Schlaefli order recurrences give
the exact summand equation, which passes to the full absolutely convergent sum.
Both Weyl monomials obey the same equation. The result holds on the entire
positive-height chart, for arbitrary fixed complex spectral parameters.

This supplies the literal scalar harmonic equation in the physical source chain.
The coexact-vector geometry, reconstructed Einstein equation and causal extinction
remain separate obligations.
-/

open Complex Real Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMAngularSeries
noncomputable section

private theorem positive_nhds (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ∀ᶠ w in 𝓝 z, 0 < w 1 :=
  (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz

private theorem gradient_zero (X Y : ℂ) :
    gradient X Y (Pi.single 0 1) = X := by simp [gradient]

private theorem gradient_one (X Y : ℂ) :
    gradient X Y (Pi.single 1 1) = Y := by simp [gradient]

/-- Actual horizontal derivative of the complete infinite family. -/
theorem value_coordDeriv_zero (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 0 (value u nu a d negative) z =
      horizontalRate negative * value u nu a (d + 1) negative z := by
  rw [coordDeriv, (value_hasFDerivAt u nu a d negative z hz).fderiv]
  exact gradient_zero _ _

/-- Actual vertical derivative of the complete infinite family. -/
theorem value_coordDeriv_one (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 1 (value u nu a d negative) z =
      (a : ℂ) * value u nu (a - 1) d negative z - (Real.pi : ℂ) *
        (value u (nu + 1) a (d + 1) negative z + value u (nu - 1) a (d + 1) negative z) := by
  rw [coordDeriv, (value_hasFDerivAt u nu a d negative z hz).fderiv]
  exact gradient_one _ _

/-- Actual second horizontal derivative, still retaining every Fourier mode. -/
theorem value_coordDeriv_zero_zero (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 0 (coordDeriv 0 (value u nu a d negative)) z =
      horizontalRate negative ^ 2 * value u nu a (d + 2) negative z := by
  have he : coordDeriv 0 (value u nu a d negative) =ᶠ[𝓝 z]
      (fun w => horizontalRate negative * value u nu a (d + 1) negative w) := by
    filter_upwards [positive_nhds z hz] with w hw
    exact value_coordDeriv_zero u nu a d negative w hw
  have hd := ((value_hasFDerivAt u nu a (d + 1) negative z hz).const_mul
    (horizontalRate negative)).congr_of_eventuallyEq he
  rw [coordDeriv, hd.fderiv]
  simp only [smul_apply, smul_eq_mul, valueGradient, gradient_zero]
  ring

/-- The vertical derivative itself has the full joint derivative given by shifted families. -/
theorem value_coordDeriv_one_hasFDerivAt (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    HasFDerivAt (coordDeriv 1 (value u nu a d negative))
      ((a : ℂ) • valueGradient u nu (a - 1) d negative z - (Real.pi : ℂ) •
        (valueGradient u (nu + 1) a (d + 1) negative z +
          valueGradient u (nu - 1) a (d + 1) negative z)) z := by
  have he : coordDeriv 1 (value u nu a d negative) =ᶠ[𝓝 z]
      (fun w => (a : ℂ) * value u nu (a - 1) d negative w - (Real.pi : ℂ) *
        (value u (nu + 1) a (d + 1) negative w + value u (nu - 1) a (d + 1) negative w)) := by
    filter_upwards [positive_nhds z hz] with w hw
    exact value_coordDeriv_one u nu a d negative w hw
  exact (((value_hasFDerivAt u nu (a - 1) d negative z hz).const_mul (a : ℂ)).sub
    (((value_hasFDerivAt u (nu + 1) a (d + 1) negative z hz).add
      (value_hasFDerivAt u (nu - 1) a (d + 1) negative z hz)).const_mul (Real.pi : ℂ))).congr_of_eventuallyEq he

/-- The exact pure vertical second derivative of the full infinite family. -/
theorem value_coordDeriv_one_one (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 1 (coordDeriv 1 (value u nu a d negative)) z =
      (a : ℂ) * ((a : ℂ) - 1) * value u nu (a - 2) d negative z -
        (2 * (a : ℂ) * Real.pi) *
          (value u (nu + 1) (a - 1) (d + 1) negative z +
            value u (nu - 1) (a - 1) (d + 1) negative z) +
        (Real.pi : ℂ) ^ 2 *
          (value u (nu + 2) a (d + 2) negative z +
            2 * value u nu a (d + 2) negative z + value u (nu - 2) a (d + 2) negative z) := by
  rw [coordDeriv, (value_coordDeriv_one_hasFDerivAt u nu a d negative z hz).fderiv]
  simp only [sub_apply, smul_apply, add_apply, smul_eq_mul, valueGradient, gradient_one]
  rw [show a - 1 - 1 = a - 2 by ring,
    show nu + 1 + 1 = nu + 2 by ring, show nu - 1 - 1 = nu - 2 by ring,
    show nu + 1 - 1 = nu by ring, show nu - 1 + 1 = nu by ring,
    show d + 1 + 1 = d + 2 by omega]
  push_cast
  ring

/-- The centered second-order Bessel relation, derived from three exact order recurrences. -/
theorem bessel_second_order_relation {s : ℝ} (hs : 0 < s) (nu : ℂ) :
    (s : ℂ) ^ 2 / 4 * (modifiedBesselKOrder s (nu + 2) -
      2 * modifiedBesselKOrder s nu + modifiedBesselKOrder s (nu - 2)) -
      (s : ℂ) / 2 * (modifiedBesselKOrder s (nu + 1) + modifiedBesselKOrder s (nu - 1)) =
      nu ^ 2 * modifiedBesselKOrder s nu := by
  have h0 := modifiedBesselKOrder_add_one hs nu
  have hp := modifiedBesselKOrder_add_one hs (nu + 1)
  have hm := modifiedBesselKOrder_add_one hs (nu - 1)
  rw [show nu + 1 + 1 = nu + 2 by ring, show nu + 1 - 1 = nu by ring] at hp
  rw [show nu - 1 + 1 = nu by ring, show nu - 1 - 1 = nu - 2 by ring] at hm
  have hsne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  field_simp [hsne] at h0 hp hm
  linear_combination (s : ℂ) / 4 * hp - (s : ℂ) / 4 * hm + nu / 2 * h0

private theorem rpow_half_shift (Y : ℝ) (hY : 0 < Y) :
    Real.rpow Y (-1 / 2) = Y * Real.rpow Y (-3 / 2) ∧
      Real.rpow Y (1 / 2) = Y ^ 2 * Real.rpow Y (-3 / 2) := by
  constructor
  · change Y ^ (-1 / 2 : ℝ) = Y * Y ^ (-3 / 2 : ℝ)
    rw [show (-1 / 2 : ℝ) = -3 / 2 + 1 by ring, Real.rpow_add hY, Real.rpow_one]
    ring
  · change Y ^ (1 / 2 : ℝ) = Y ^ 2 * Y ^ (-3 / 2 : ℝ)
    rw [show (1 / 2 : ℝ) = -3 / 2 + (2 : ℕ) by norm_num, Real.rpow_add hY, Real.rpow_natCast]
    ring

/-- The exact hyperbolic equation for each weighted summand, at every positive height. -/
theorem term_hyperbolic_equation (u nu : ℂ) (d : ℕ) (negative : Bool)
    (N : ℕ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (z 1 : ℂ) ^ 2 * (
      -(1 / 4 : ℂ) * term u nu (-3 / 2) d negative N z - (Real.pi : ℂ) *
        (term u (nu + 1) (-1 / 2) (d + 1) negative N z +
          term u (nu - 1) (-1 / 2) (d + 1) negative N z) +
      (Real.pi : ℂ) ^ 2 * (term u (nu + 2) (1 / 2) (d + 2) negative N z -
        2 * term u nu (1 / 2) (d + 2) negative N z +
          term u (nu - 2) (1 / 2) (d + 2) negative N z)) =
      (nu ^ 2 - 1 / 4) * term u nu (1 / 2) d negative N z := by
  have hB := bessel_second_order_relation
    (by positivity : 0 < 2 * Real.pi * ((N : ℝ) + 1) * z 1) nu
  obtain ⟨h1, h2⟩ := rpow_half_shift (z 1) hz
  simp only [term, coefficient, h1, h2, pow_add, pow_one]
  push_cast at hB ⊢
  linear_combination
    (d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      ((N : ℂ) + 1) ^ d * d4BMCompletedEisensteinFourierPhase negative N (z 0) *
      (z 1 : ℂ) ^ 2 * (Real.rpow (z 1) (-3 / 2) : ℂ)) * hB

/-- Hyperbolic scalar Laplacian expressed through actual coordinate derivatives. -/
def hyperbolicLaplacian (f : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℝ) : ℂ :=
  (z 1 : ℂ) ^ 2 * (coordDeriv 0 (coordDeriv 0 f) z + coordDeriv 1 (coordDeriv 1 f) z)

/-- The full infinite half-power family satisfies the scalar equation on the entire chart. -/
theorem value_hyperbolicLaplacian (u nu : ℂ) (d : ℕ) (negative : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (value u nu (1 / 2) d negative) z =
      (nu ^ 2 - 1 / 4) * value u nu (1 / 2) d negative z := by
  have hs (v : ℂ) (a : ℝ) (j : ℕ) := (term_summable u v a j negative z hz).hasSum
  have hL := ((((hs nu (-3 / 2) d).mul_left (-(1 / 4 : ℂ))).sub
    (((hs (nu + 1) (-1 / 2) (d + 1)).add (hs (nu - 1) (-1 / 2) (d + 1))).mul_left (Real.pi : ℂ))).add
    ((((hs (nu + 2) (1 / 2) (d + 2)).sub ((hs nu (1 / 2) (d + 2)).mul_left 2)).add
      (hs (nu - 2) (1 / 2) (d + 2))).mul_left ((Real.pi : ℂ) ^ 2))).mul_left ((z 1 : ℂ) ^ 2)
  have hR := (hs nu (1 / 2) d).mul_left (nu ^ 2 - 1 / 4)
  have heq := hL.unique (hR.congr_fun (fun N => term_hyperbolic_equation u nu d negative N z hz))
  have hr : horizontalRate negative ^ 2 = -(4 * (Real.pi : ℂ) ^ 2) := by
    unfold horizontalRate
    rw [mul_pow, Complex.I_sq]
    cases negative <;> norm_num [d4BMFourierSign] <;> ring
  unfold hyperbolicLaplacian
  rw [value_coordDeriv_zero_zero u nu (1 / 2) d negative z hz,
    value_coordDeriv_one_one u nu (1 / 2) d negative z hz, hr]
  simp only [value] at heq ⊢
  norm_num at heq ⊢
  linear_combination heq

/-- The scalar operator depends only on the actual local field germ. -/
theorem hyperbolicLaplacian_congr {f g : (Fin 2 → ℝ) → ℂ} {z : Fin 2 → ℝ}
    (he : f =ᶠ[𝓝 z] g) : hyperbolicLaplacian f z = hyperbolicLaplacian g z := by
  have hd (i : Fin 2) : coordDeriv i f =ᶠ[𝓝 z] coordDeriv i g := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with w hw
    exact congrArg (fun L => L (Pi.single i 1)) hw
  unfold hyperbolicLaplacian coordDeriv
  rw [(hd 0).fderiv_eq, (hd 1).fderiv_eq]

/-- Linearity of the actual scalar operator under addition of smooth fields. -/
theorem hyperbolicLaplacian_add {f g : (Fin 2 → ℝ) → ℂ} {z : Fin 2 → ℝ}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    hyperbolicLaplacian (fun w => f w + g w) z =
      hyperbolicLaplacian f z + hyperbolicLaplacian g z := by
  change (z 1 : ℂ) ^ 2 * ((ofField (fun w => f w + g w) z).second 0 0 +
    (ofField (fun w => f w + g w) z).second 1 1) = _
  rw [ofField_add hf hg]
  simp only [ScalarTwoJet.add, ofField, hyperbolicLaplacian]
  ring

/-- Linearity of the actual scalar operator under a fixed complex amplitude. -/
theorem hyperbolicLaplacian_const_mul {f : (Fin 2 → ℝ) → ℂ} {z : Fin 2 → ℝ}
    (hf : ContDiffAt ℝ 2 f z) (c : ℂ) :
    hyperbolicLaplacian (fun w => c * f w) z = c * hyperbolicLaplacian f z := by
  change (z 1 : ℂ) ^ 2 * ((ofField (fun w => c * f w) z).second 0 0 +
    (ofField (fun w => c * f w) z).second 1 1) = _
  rw [ofField_mul contDiffAt_const hf, ofField_constant]
  simp only [ScalarTwoJet.mul, constant, ofField, hyperbolicLaplacian]
  ring

/-- The literal signed scalar tail obeys the actual equation at every positive height. -/
theorem signedTail_hyperbolicLaplacian (u nu : ℂ) (negative : Bool) (j : ℕ)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (fun w : Fin 2 → ℝ =>
      d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative (w 0) j 0 (w 1)) z =
      (nu ^ 2 - 1 / 4) * d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative (z 0) j 0 (z 1) := by
  have he : (fun w : Fin 2 → ℝ =>
      d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative (w 0) j 0 (w 1)) =ᶠ[𝓝 z]
      value u nu (1 / 2) j negative := by
    filter_upwards [positive_nhds z hz] with w hw
    simpa using signedTail_eq_value u nu negative j 0 w hw
  rw [hyperbolicLaplacian_congr he, he.eq_of_nhds]
  exact value_hyperbolicLaplacian u nu j negative z hz

/-- Actual joint derivative of a complex height monomial. -/
theorem height_cpow_hasFDerivAt (w : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    HasFDerivAt (fun q : Fin 2 → ℝ => (q 1 : ℂ) ^ w)
      (gradient 0 (w * (z 1 : ℂ) ^ (w - 1))) z := by
  have h := (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := w) hz).hasFDerivAt.comp z
    ((show (Fin 2 → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj 1).hasFDerivAt)
  convert! h using 1
  ext v
  simp [gradient, Complex.real_smul]

/-- Literal complex height powers satisfy their exact scalar eigen-equation. -/
theorem height_cpow_hyperbolicLaplacian (w : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (fun q : Fin 2 → ℝ => (q 1 : ℂ) ^ w) z =
      w * (w - 1) * (z 1 : ℂ) ^ w := by
  have hx : coordDeriv 0 (fun q : Fin 2 → ℝ => (q 1 : ℂ) ^ w) =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [positive_nhds z hz] with q hq
    rw [coordDeriv, (height_cpow_hasFDerivAt w q hq).fderiv]
    exact gradient_zero _ _
  have hy : coordDeriv 1 (fun q : Fin 2 → ℝ => (q 1 : ℂ) ^ w) =ᶠ[𝓝 z]
      (fun q => w * (q 1 : ℂ) ^ (w - 1)) := by
    filter_upwards [positive_nhds z hz] with q hq
    rw [coordDeriv, (height_cpow_hasFDerivAt w q hq).fderiv]
    exact gradient_one _ _
  have hd := ((height_cpow_hasFDerivAt (w - 1) z hz).const_mul w).congr_of_eventuallyEq hy
  unfold hyperbolicLaplacian coordDeriv
  rw [hx.fderiv_eq, hd.fderiv]
  simp only [fderiv_const_apply, zero_apply, smul_apply, smul_eq_mul, gradient_one, zero_add]
  have hpow : (z 1 : ℂ) ^ w = (z 1 : ℂ) ^ (w - 2) * (z 1 : ℂ) ^ 2 := by
    rw [← Complex.cpow_two, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hz.ne')]
    congr 1
    ring
  rw [show w - 1 - 1 = w - 2 by ring, hpow]
  ring

/-- Each literal scalar Weyl term obeys the same centered scalar eigen-equation. -/
theorem cuspConstantTerm_hyperbolicLaplacian (u : ℂ) (epsilon : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (fun q : Fin 2 → ℝ =>
      d4BMCompletedEisensteinCuspConstantTerm .scalar u epsilon (q 1)) z =
      (u ^ 2 - 1 / 4) * d4BMCompletedEisensteinCuspConstantTerm .scalar u epsilon (z 1) := by
  let w := d4BMCompletedEisensteinCuspWeylExponent u epsilon
  let c := d4BMCompletedEisensteinCuspConstantCoefficient u epsilon * 1
  have hw : w * (w - 1) = u ^ 2 - 1 / 4 := by
    dsimp [w, d4BMCompletedEisensteinCuspWeylExponent]
    cases epsilon <;> simp [d4BMCuspSign] <;> ring
  have hp := (height_cpow_contDiffOn w 2).contDiffAt (positive_nhds z hz)
  change hyperbolicLaplacian (fun q : Fin 2 → ℝ => c * (q 1 : ℂ) ^ w) z =
    (u ^ 2 - 1 / 4) * (c * (z 1 : ℂ) ^ w)
  rw [hyperbolicLaplacian_const_mul hp c, height_cpow_hyperbolicLaplacian w z hz, hw]
  ring

/-- The literal complete scalar cusp field satisfies its actual equation on all Y>0. -/
theorem scalarCusp_hyperbolicLaplacian (u : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (fun q : Fin 2 → ℝ =>
      d4BMCompletedEisensteinCuspLeg .scalar u (q 0) (q 1)) z =
      (u ^ 2 - 1 / 4) * d4BMCompletedEisensteinCuspLeg .scalar u (z 0) (z 1) := by
  let f0 : (Fin 2 → ℝ) → ℂ := fun q => d4BMCompletedEisensteinCuspConstantTerm .scalar u false (q 1)
  let f1 : (Fin 2 → ℝ) → ℂ := fun q => d4BMCompletedEisensteinCuspConstantTerm .scalar u true (q 1)
  let t0 : (Fin 2 → ℝ) → ℂ := fun q => d4BMCompletedEisensteinSignedSqrtWhittakerTail u u false (q 0) 0 0 (q 1)
  let t1 : (Fin 2 → ℝ) → ℂ := fun q => d4BMCompletedEisensteinSignedSqrtWhittakerTail u u true (q 0) 0 0 (q 1)
  have hf0 : ContDiffAt ℝ 2 f0 z :=
    ((contDiffOn_infty.mp (cuspConstantTerm_contDiffOn .scalar u false)) 2).contDiffAt (positive_nhds z hz)
  have hf1 : ContDiffAt ℝ 2 f1 z :=
    ((contDiffOn_infty.mp (cuspConstantTerm_contDiffOn .scalar u true)) 2).contDiffAt (positive_nhds z hz)
  have ht0 : ContDiffAt ℝ 2 t0 z :=
    ((contDiffOn_infty.mp (signedTail_contDiffOn u u false 0 0)) 2).contDiffAt (positive_nhds z hz)
  have ht1 : ContDiffAt ℝ 2 t1 z :=
    ((contDiffOn_infty.mp (signedTail_contDiffOn u u true 0 0)) 2).contDiffAt (positive_nhds z hz)
  change hyperbolicLaplacian (fun q => (f0 q + f1 q) + 2 * (t0 q + t1 q)) z =
    (u ^ 2 - 1 / 4) * ((f0 z + f1 z) + 2 * (t0 z + t1 z))
  rw [hyperbolicLaplacian_add (hf0.add hf1) (contDiffAt_const.mul (ht0.add ht1)),
    hyperbolicLaplacian_add hf0 hf1, hyperbolicLaplacian_const_mul (ht0.add ht1) 2,
    hyperbolicLaplacian_add ht0 ht1]
  dsimp only [f0, f1, t0, t1]
  rw [cuspConstantTerm_hyperbolicLaplacian u false z hz,
    cuspConstantTerm_hyperbolicLaplacian u true z hz,
    signedTail_hyperbolicLaplacian u u false 0 z hz,
    signedTail_hyperbolicLaplacian u u true 0 z hz]
  ring

end
end RHTower.D4BMAngularSeries
