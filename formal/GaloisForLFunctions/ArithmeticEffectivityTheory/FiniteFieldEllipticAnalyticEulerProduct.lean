import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticFormalEulerProduct
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticZetaBounds
import GaloisForLFunctions.BiarithmeticGeometry.GeometricPoleExtraction
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Analytic Euler product over the actual elliptic places

The inverse local factors have nonnegative real coefficients. Their finite
products increase coefficientwise and stabilize at the point-count zeta
coefficients. The rational zeta series supplies an absolutely summable
majorant throughout `|u| < 1/3`.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open IsDedekindDomain _root_.RHTower PowerSeries Filter Topology
open ArithmeticCastelnuovoSeveri
noncomputable section

private def NonnegativeRealCoefficients (f : PowerSeries ℂ) : Prop :=
  ∀ n, (PowerSeries.coeff n f).im = 0 ∧ 0 ≤ (PowerSeries.coeff n f).re

private theorem nonnegativeRealCoefficients_one :
    NonnegativeRealCoefficients (1 : PowerSeries ℂ) := by
  intro n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]

private theorem NonnegativeRealCoefficients.mul {f g : PowerSeries ℂ}
    (hf : NonnegativeRealCoefficients f) (hg : NonnegativeRealCoefficients g) :
    NonnegativeRealCoefficients (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  constructor
  · rw [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro p _
    rw [Complex.mul_im, (hf p.1).1, (hg p.2).1, mul_zero, zero_mul, add_zero]
  · rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro p _
    rw [Complex.mul_re, (hf p.1).1, (hg p.2).1, zero_mul, sub_zero]
    exact mul_nonneg (hf p.1).2 (hg p.2).2

private theorem NonnegativeRealCoefficients.prod {ι : Type*} (S : Finset ι)
    (f : ι → PowerSeries ℂ) (hf : ∀ i ∈ S, NonnegativeRealCoefficients (f i)) :
    NonnegativeRealCoefficients (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using nonnegativeRealCoefficients_one
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem NonnegativeRealCoefficients.coeff_le_mul {f g : PowerSeries ℂ}
    (hf : NonnegativeRealCoefficients f) (hg : NonnegativeRealCoefficients g)
    (hg0 : PowerSeries.constantCoeff g = 1) (n : ℕ) :
    (PowerSeries.coeff n f).re ≤ (PowerSeries.coeff n (f * g)).re := by
  rw [PowerSeries.coeff_mul, Complex.re_sum]
  have hterm : (PowerSeries.coeff n f * PowerSeries.coeff 0 g).re =
      (PowerSeries.coeff n f).re := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, hg0, mul_one]
  rw [← hterm]
  apply Finset.single_le_sum
    (f := fun p : ℕ × ℕ => (PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g).re)
    (a := (n, 0))
  · intro p _
    rw [Complex.mul_re, (hf p.1).1, (hg p.2).1, zero_mul, sub_zero]
    exact mul_nonneg (hf p.1).2 (hg p.2).2
  · simp

private theorem NonnegativeRealCoefficients.norm_coeff {f : PowerSeries ℂ}
    (hf : NonnegativeRealCoefficients f) (n : ℕ) :
    ‖PowerSeries.coeff n f‖ = (PowerSeries.coeff n f).re := by
  have he : PowerSeries.coeff n f = ((PowerSeries.coeff n f).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (hf n).1
  rw [he, Complex.norm_real, Real.norm_of_nonneg (hf n).2, Complex.ofReal_re]

private theorem nonnegativeRealCoefficients_geom (d : ℕ) :
    NonnegativeRealCoefficients (deningerBigWittGeom (1 : ℂ) d) := by
  intro n
  rw [deningerBigWittGeom_coeff]
  split_ifs <;> simp only [one_pow, Complex.one_im, Complex.one_re,
    Complex.zero_im, Complex.zero_re, le_refl, zero_le_one, and_self]

/-- Euler series of a finite set of actual affine places, together with infinity. -/
def ellipticZetaFinite (S : Finset (HeightOneSpectrum A)) : PowerSeries ℂ :=
  deningerBigWittGeom 1 1 *
    ∏ v ∈ S, deningerBigWittGeom 1 (affinePlaceDegree v)

/-- Finite Euler products at the actual residue-degree cutoff. -/
def ellipticZetaPartial (N : ℕ) : PowerSeries ℂ :=
  ellipticZetaFinite (affinePlacesDegreeLe N)

private theorem ellipticZetaFinite_nonnegative (S : Finset (HeightOneSpectrum A)) :
    NonnegativeRealCoefficients (ellipticZetaFinite S) :=
  (nonnegativeRealCoefficients_geom 1).mul
    (NonnegativeRealCoefficients.prod _ _ fun v _ => nonnegativeRealCoefficients_geom _)

private theorem ellipticZetaPartial_nonnegative (N : ℕ) :
    NonnegativeRealCoefficients (ellipticZetaPartial N) :=
  ellipticZetaFinite_nonnegative _

private theorem geom_constantCoeff (d : ℕ) :
    PowerSeries.constantCoeff (deningerBigWittGeom (1 : ℂ) d) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, deningerBigWittGeom_coeff]
  simp only [dvd_zero, if_true, one_pow]

private theorem ellipticZetaPartial_mul (N : ℕ) :
    ellipticZetaPartial N * ellipticEulerPartial N = 1 := by
  classical
  unfold ellipticZetaPartial ellipticZetaFinite ellipticEulerPartial
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
  simp only [affineEulerFactor, deningerBigWittGeom_mul_factor (1 : ℂ) (by omega : 0 < 1),
    deningerBigWittGeom_mul_factor (1 : ℂ) (affinePlaceDegree_pos _), Finset.prod_const_one,
    one_mul]

private theorem ellipticZetaPartial_eq_inverse (N : ℕ) :
    ellipticZetaPartial N = PowerSeries.invOfUnit (ellipticEulerPartial N) 1 := by
  have hunit : IsUnit (ellipticEulerPartial N) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [ellipticEulerPartial_constantCoeff]; exact isUnit_one)
  apply hunit.mul_right_cancel
  rw [ellipticZetaPartial_mul, PowerSeries.invOfUnit_mul _ _ (ellipticEulerPartial_constantCoeff N)]

/-- Each inverse Euler coefficient agrees with the zeta coefficient once the degree cutoff reaches it. -/
theorem ellipticZetaPartial_coeff_stable {n N : ℕ} (hnN : n ≤ N) :
    PowerSeries.coeff n (ellipticZetaPartial N) = PowerSeries.coeff n zeta := by
  rw [ellipticZetaPartial_eq_inverse, ← ellipticEulerProduct_inv_eq_zeta]
  apply deningerBigWittInvOfUnit_coeff_congr
  intro k hk
  rw [ellipticEulerProduct_coeff]
  exact ellipticEulerPartial_coeff_stable le_rfl (hk.trans hnN)

private theorem ellipticZetaFinite_coeff_mono {S T : Finset (HeightOneSpectrum A)}
    (hST : S ⊆ T) (n : ℕ) :
    (PowerSeries.coeff n (ellipticZetaFinite S)).re ≤
      (PowerSeries.coeff n (ellipticZetaFinite T)).re := by
  classical
  have hp :
      (∏ v ∈ S, deningerBigWittGeom (1 : ℂ) (affinePlaceDegree v)) *
      (∏ v ∈ T \ S,
        deningerBigWittGeom (1 : ℂ) (affinePlaceDegree v)) =
      ∏ v ∈ T, deningerBigWittGeom (1 : ℂ) (affinePlaceDegree v) :=
    (mul_comm _ _).trans (Finset.prod_sdiff hST)
  unfold ellipticZetaFinite
  rw [← hp, ← mul_assoc]
  apply NonnegativeRealCoefficients.coeff_le_mul
  · exact ellipticZetaFinite_nonnegative S
  · exact NonnegativeRealCoefficients.prod _ _ fun v _ => nonnegativeRealCoefficients_geom _
  · simp only [map_prod, geom_constantCoeff, Finset.prod_const_one]

private theorem zeta_nonnegative : NonnegativeRealCoefficients zeta := by
  intro n
  rw [← ellipticZetaPartial_coeff_stable (le_refl n)]
  exact ellipticZetaPartial_nonnegative n n

/-- One fixed zeta coefficient majorizes every finite-place Euler coefficient in norm. -/
theorem ellipticZetaFinite_coeff_norm_le (S : Finset (HeightOneSpectrum A)) (n : ℕ) :
    ‖PowerSeries.coeff n (ellipticZetaFinite S)‖ ≤ ‖PowerSeries.coeff n zeta‖ := by
  rw [(ellipticZetaFinite_nonnegative S).norm_coeff, zeta_nonnegative.norm_coeff]
  let M := max n (S.sup affinePlaceDegree)
  have hS : S ⊆ affinePlacesDegreeLe M := by
    intro v hv
    exact (mem_affinePlacesDegreeLe v M).mpr
      ((Finset.le_sup (f := affinePlaceDegree) hv).trans (le_max_right _ _))
  have h := ellipticZetaFinite_coeff_mono hS n
  change (PowerSeries.coeff n (ellipticZetaFinite S)).re ≤
    (PowerSeries.coeff n (ellipticZetaPartial M)).re at h
  rwa [ellipticZetaPartial_coeff_stable (le_max_left _ _)] at h

/-- Every finite-place product containing the degree cutoff has the exact coefficient. -/
theorem ellipticZetaFinite_coeff_stable {S : Finset (HeightOneSpectrum A)} {n : ℕ}
    (hS : affinePlacesDegreeLe n ⊆ S) :
    PowerSeries.coeff n (ellipticZetaFinite S) = PowerSeries.coeff n zeta := by
  have hupper := ellipticZetaFinite_coeff_norm_le S n
  rw [(ellipticZetaFinite_nonnegative S).norm_coeff, zeta_nonnegative.norm_coeff] at hupper
  have hlower := ellipticZetaFinite_coeff_mono hS n
  change (PowerSeries.coeff n (ellipticZetaPartial n)).re ≤
    (PowerSeries.coeff n (ellipticZetaFinite S)).re at hlower
  rw [ellipticZetaPartial_coeff_stable le_rfl] at hlower
  exact Complex.ext (le_antisymm hupper hlower)
    ((ellipticZetaFinite_nonnegative S n).1.trans (zeta_nonnegative n).1.symm)

private theorem zeta_absoluteSummableAt {u : ℂ} (hu : ‖u‖ < 1 / 3) :
    zeta.AbsoluteSummableAt u := by
  have hu1 : ‖(1 : ℂ) * u‖ < 1 := by simpa only [one_mul] using (by linarith : ‖u‖ < 1)
  have hu3 : ‖(3 : ℂ) * u‖ < 1 := by rw [norm_mul]; norm_num only [Complex.norm_ofNat]; linarith
  change (geom 1 * geom (datum.q : ℂ) * datum.hOnePoly).AbsoluteSummableAt u
  rw [datum_q, ← numeratorSeries_eq]
  norm_num only [Complex.ofReal_ofNat]
  exact ((BiarithmeticGeometry.geom_absoluteSummableAt hu1).mul
    (BiarithmeticGeometry.geom_absoluteSummableAt hu3)).mul (PowerSeries.coe_absoluteSummableAt _ _)

/-- The degree-cutoff inverse Euler series converge after evaluation throughout the true Euler disk. -/
theorem tendsto_ellipticZetaPartial_absoluteEval {u : ℂ} (hu : ‖u‖ < 1 / 3) :
    Tendsto (fun N => (ellipticZetaPartial N).absoluteEval u) atTop
      (𝓝 (zeta.absoluteEval u)) := by
  apply tendsto_tsum_of_dominated_convergence (zeta_absoluteSummableAt hu)
  · intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with N hN
    rw [ellipticZetaPartial_coeff_stable hN]
  · exact Eventually.of_forall fun N n => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (ellipticZetaFinite_coeff_norm_le _ n) (norm_nonneg _)

/-- Convergence holds along all finite place sets, independently of an enumeration. -/
theorem tendsto_ellipticZetaFinite_absoluteEval {u : ℂ} (hu : ‖u‖ < 1 / 3) :
    Tendsto (fun S => (ellipticZetaFinite S).absoluteEval u) atTop
      (𝓝 (zeta.absoluteEval u)) := by
  apply tendsto_tsum_of_dominated_convergence (zeta_absoluteSummableAt hu)
  · intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (affinePlacesDegreeLe n)] with S hS
    rw [ellipticZetaFinite_coeff_stable hS]
  · exact Eventually.of_forall fun S n => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (ellipticZetaFinite_coeff_norm_le S n) (norm_nonneg _)

private theorem localGeom_absoluteSummableAt (d : ℕ) {u : ℂ} (hu : ‖u‖ < 1) :
    (deningerBigWittGeom (1 : ℂ) d).AbsoluteSummableAt u := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
    (summable_geometric_of_lt_one (norm_nonneg u) hu)
  intro n
  rw [deningerBigWittGeom_coeff]
  split_ifs
  · simp only [one_pow, one_mul, norm_pow, le_refl]
  · simp only [zero_mul, norm_zero]
    exact pow_nonneg (norm_nonneg u) _

private theorem localFactor_eq_polynomial (d : ℕ) :
    deningerBigWittFactor (1 : ℂ) d =
      ((1 - Polynomial.X ^ d : Polynomial ℂ) : PowerSeries ℂ) := by
  simp only [deningerBigWittFactor, map_one, one_mul,
    Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X]

private theorem localGeom_absoluteEval {d : ℕ} (hd : 0 < d)
    {u : ℂ} (hu : ‖u‖ < 1) :
    (deningerBigWittGeom (1 : ℂ) d).absoluteEval u = (1 - u ^ d)⁻¹ := by
  have he := congrArg (fun f : PowerSeries ℂ => f.absoluteEval u)
    (deningerBigWittGeom_mul_factor (1 : ℂ) hd)
  rw [PowerSeries.absoluteEval_mul (localGeom_absoluteSummableAt d hu)
    (by rw [localFactor_eq_polynomial]; exact PowerSeries.coe_absoluteSummableAt _ _),
    localFactor_eq_polynomial, PowerSeries.coe_absoluteEval] at he
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X] at he
  change (deningerBigWittGeom (1 : ℂ) d).absoluteEval u * (1 - u ^ d) =
    (PowerSeries.C 1).absoluteEval u at he
  rw [PowerSeries.absoluteEval_C] at he
  have hne : 1 - u ^ d ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact zero_ne_one he
  simpa only [one_div] using (eq_div_iff hne).mpr he

private theorem finiteLocalGeoms_absoluteSummableAt
    (S : Finset (HeightOneSpectrum A)) {u : ℂ} (hu : ‖u‖ < 1) :
    (∏ v ∈ S, deningerBigWittGeom (1 : ℂ) (affinePlaceDegree v)).AbsoluteSummableAt u := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact PowerSeries.absoluteSummableAt_C 1 u
  | @insert v S hv ih =>
    rw [Finset.prod_insert hv]
    exact (localGeom_absoluteSummableAt _ hu).mul ih

private theorem finiteLocalGeoms_absoluteEval
    (S : Finset (HeightOneSpectrum A)) {u : ℂ} (hu : ‖u‖ < 1) :
    (∏ v ∈ S, deningerBigWittGeom (1 : ℂ) (affinePlaceDegree v)).absoluteEval u =
      ∏ v ∈ S, (1 - u ^ affinePlaceDegree v)⁻¹ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty]
    exact PowerSeries.absoluteEval_C 1 u
  | @insert v S hv ih =>
    rw [Finset.prod_insert hv, Finset.prod_insert hv,
      PowerSeries.absoluteEval_mul (localGeom_absoluteSummableAt _ hu)
        (finiteLocalGeoms_absoluteSummableAt S hu),
      localGeom_absoluteEval (affinePlaceDegree_pos v) hu, ih]

/-- Evaluation of a finite-place series is the literal local Euler product. -/
theorem ellipticZetaFinite_absoluteEval (S : Finset (HeightOneSpectrum A))
    {u : ℂ} (hu : ‖u‖ < 1) :
    (ellipticZetaFinite S).absoluteEval u =
      (1 - u)⁻¹ * ∏ v ∈ S, (1 - u ^ affinePlaceDegree v)⁻¹ := by
  rw [ellipticZetaFinite,
    PowerSeries.absoluteEval_mul (localGeom_absoluteSummableAt 1 hu)
      (finiteLocalGeoms_absoluteSummableAt _ hu),
    localGeom_absoluteEval (by omega : 0 < 1) hu, pow_one,
    finiteLocalGeoms_absoluteEval _ hu]

private theorem zeta_absoluteEval {u : ℂ} (hu : ‖u‖ < 1 / 3) :
    zeta.absoluteEval u = zetaFunction u := by
  let D : Polynomial ℂ := (1 - Polynomial.X) * (1 - Polynomial.C 3 * Polynomial.X)
  have hD : ((D : Polynomial ℂ) : PowerSeries ℂ) * zeta =
      (numerator : PowerSeries ℂ) := by
    simpa only [D, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_X, Polynomial.coe_C] using zeta_rational
  have he := congrArg (fun f : PowerSeries ℂ => f.absoluteEval u) hD
  rw [PowerSeries.absoluteEval_mul (PowerSeries.coe_absoluteSummableAt D u)
    (zeta_absoluteSummableAt hu), PowerSeries.coe_absoluteEval,
    PowerSeries.coe_absoluteEval] at he
  have hden : D.eval u ≠ 0 := by
    simp only [D, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X, Polynomial.eval_C]
    apply mul_ne_zero
    · intro hz
      have heq : u = 1 := (sub_eq_zero.mp hz).symm
      rw [heq, norm_one] at hu
      norm_num at hu
    · intro hz
      have heq : u = 1 / 3 := by linear_combination -(1 / 3 : ℂ) * hz
      rw [heq] at hu
      norm_num [norm_div] at hu
  have hval := (eq_div_iff hden).mpr (by simpa only [mul_comm] using he)
  simpa only [zetaFunction, D, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C] using hval

/-- The actual closed-place Euler products converge to the actual curve zeta function. -/
theorem tendsto_elliptic_euler_product {u : ℂ} (hu : ‖u‖ < 1 / 3) :
    Tendsto (fun N => (1 - u)⁻¹ *
      ∏ v ∈ affinePlacesDegreeLe N, (1 - u ^ affinePlaceDegree v)⁻¹)
      atTop (𝓝 (zetaFunction u)) := by
  have hu1 : ‖u‖ < 1 := by linarith only [hu]
  simpa only [ellipticZetaPartial, ellipticZetaFinite_absoluteEval _ hu1, zeta_absoluteEval hu] using
    tendsto_ellipticZetaPartial_absoluteEval hu

/-- The affine local factors have an unordered product with the actual zeta value. -/
theorem hasProd_elliptic_affine_euler_factors {u : ℂ} (hu : ‖u‖ < 1 / 3) :
    HasProd (fun v : HeightOneSpectrum A => (1 - u ^ affinePlaceDegree v)⁻¹)
      ((1 - u) * zetaFunction u) := by
  change Tendsto (fun S : Finset (HeightOneSpectrum A) =>
    ∏ v ∈ S, (1 - u ^ affinePlaceDegree v)⁻¹) atTop (𝓝 ((1 - u) * zetaFunction u))
  have hu1 : ‖u‖ < 1 := by linarith only [hu]
  have hne : 1 - u ≠ 0 := by
    intro h
    have he : u = 1 := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hu1
    exact lt_irrefl _ hu1
  have h := (tendsto_ellipticZetaFinite_absoluteEval hu).const_mul (1 - u)
  simpa only [ellipticZetaFinite_absoluteEval _ hu1, zeta_absoluteEval hu,
    ← mul_assoc, mul_inv_cancel₀ hne, one_mul] using h

/-- Euler's product includes the unique degree-one infinity place. -/
theorem elliptic_euler_product_eq_zeta {u : ℂ} (hu : ‖u‖ < 1 / 3) :
    (1 - u)⁻¹ * (∏' v : HeightOneSpectrum A, (1 - u ^ affinePlaceDegree v)⁻¹) =
      zetaFunction u := by
  rw [(hasProd_elliptic_affine_euler_factors hu).tprod_eq, ← mul_assoc,
    inv_mul_cancel₀, one_mul]
  intro h
  have he : u = 1 := (sub_eq_zero.mp h).symm
  rw [he, norm_one] at hu
  norm_num at hu

theorem elliptic_euler_product_limit_ne_zero {u : ℂ} (hu : ‖u‖ < 1 / 3) :
    zetaFunction u ≠ 0 := by
  unfold zetaFunction
  apply div_ne_zero (numerator_ne_zero_small_norm u hu.le)
  apply mul_ne_zero
  · intro hz
    have heq : u = 1 := (sub_eq_zero.mp hz).symm
    rw [heq, norm_one] at hu
    norm_num at hu
  · intro hz
    have heq : u = 1 / 3 := by linear_combination -(1 / 3 : ℂ) * hz
    rw [heq] at hu
    norm_num [norm_div] at hu

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.tendsto_elliptic_euler_product
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.elliptic_euler_product_limit_ne_zero
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.elliptic_euler_product_eq_zeta
