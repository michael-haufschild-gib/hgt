import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticAnalyticEulerProduct
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticPlaceNormalization
import GaloisForLFunctions.HTGeometry.LoopEisenstein.ValuationSpectralKernel

/-!
# Actual local spectral products and the elliptic zeta ratio

Residue cardinalities are powers of three with the closed-point degrees.
The quotient of two absolutely convergent Euler products gives the
unordered product of the actual local Haar factors, including infinity.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open Filter IsDedekindDomain
open HTGeometry.LoopEisenstein
open scoped NNReal Topology
noncomputable section

/-- Actual finite residue cardinalities are powers of three with their geometric degrees. -/
theorem finitePlace_residue_card_eq_pow_degree (v : FinitePlace) :
    Nat.card (RingOfIntegers ⧸ v.asIdeal) = 3 ^ affinePlaceDegree (finitePlaceAffineEquiv v) := by
  rw [← finitePlaceAffineEquiv_residue_card, affineIdealNorm_eq_pow_degree]

/-- The local intertwining ratio in the curve's common Euler variable. -/
def ellipticAffineIntertwiningFactor (u : ℂ) (v : HeightOneSpectrum A) : ℂ :=
  (1 - (u / 3) ^ affinePlaceDegree v) / (1 - u ^ affinePlaceDegree v)

private theorem div_three_small {u : ℂ} (hu : ‖u‖ < 1 / 3) : ‖u / 3‖ < 1 / 3 := by
  rw [norm_div]
  norm_num
  linarith only [hu]

private theorem one_sub_ne_zero_small {u : ℂ} (hu : ‖u‖ < 1 / 3) : 1 - u ≠ 0 := by
  intro h
  have he : u = 1 := (sub_eq_zero.mp h).symm
  rw [he, norm_one] at hu
  norm_num at hu

/-- The unordered product of local intertwining factors has its exact affine zeta ratio. -/
theorem hasProd_elliptic_affine_intertwining_factors {u : ℂ} (hu : ‖u‖ < 1 / 3) :
    HasProd (ellipticAffineIntertwiningFactor u)
      (((1 - u) * zetaFunction u) / ((1 - u / 3) * zetaFunction (u / 3))) := by
  have hv := div_three_small hu
  have hn : (1 - u / 3) * zetaFunction (u / 3) ≠ 0 :=
    mul_ne_zero (one_sub_ne_zero_small hv) (elliptic_euler_product_limit_ne_zero hv)
  have hA := hasProd_elliptic_affine_euler_factors hu
  have hB := hasProd_elliptic_affine_euler_factors hv
  change Tendsto (fun S : Finset (HeightOneSpectrum A) =>
    ∏ v ∈ S, (1 - u ^ affinePlaceDegree v)⁻¹) atTop
      (𝓝 ((1 - u) * zetaFunction u)) at hA
  change Tendsto (fun S : Finset (HeightOneSpectrum A) =>
    ∏ v ∈ S, (1 - (u / 3) ^ affinePlaceDegree v)⁻¹) atTop
      (𝓝 ((1 - u / 3) * zetaFunction (u / 3))) at hB
  have h := hA.div hB hn
  change Tendsto (fun S : Finset (HeightOneSpectrum A) =>
    ∏ v ∈ S, ellipticAffineIntertwiningFactor u v) atTop _
  convert h using 1
  funext S
  change (∏ v ∈ S, ellipticAffineIntertwiningFactor u v) =
    (∏ v ∈ S, (1 - u ^ affinePlaceDegree v)⁻¹) /
      ∏ v ∈ S, (1 - (u / 3) ^ affinePlaceDegree v)⁻¹
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro v _
  simp only [ellipticAffineIntertwiningFactor, div_inv_eq_mul, div_eq_mul_inv, mul_comm]

/-- Including the degree-one infinity factor gives the complete curve zeta ratio. -/
theorem elliptic_intertwining_product_eq_zeta_ratio {u : ℂ} (hu : ‖u‖ < 1 / 3) :
    ((1 - u / 3) / (1 - u)) * (∏' v, ellipticAffineIntertwiningFactor u v) =
      zetaFunction u / zetaFunction (u / 3) := by
  rw [(hasProd_elliptic_affine_intertwining_factors hu).tprod_eq]
  field_simp [one_sub_ne_zero_small hu, one_sub_ne_zero_small (div_three_small hu),
    elliptic_euler_product_limit_ne_zero (div_three_small hu)]
  <;> ring


/-- The finite-place factor in the actual normalized Haar integral. -/
def ellipticFiniteSpectralFactor (s : ℂ) (v : FinitePlace) : ℂ :=
  (1 - (Nat.card (RingOfIntegers ⧸ v.asIdeal) : ℂ)⁻¹ *
    localSpectralParameter (Nat.card (RingOfIntegers ⧸ v.asIdeal)) s) /
    (1 - localSpectralParameter (Nat.card (RingOfIntegers ⧸ v.asIdeal)) s)

/-- The infinity factor has residue cardinality three. -/
def ellipticInfinitySpectralFactor (s : ℂ) : ℂ :=
  (1 - (3 : ℂ)⁻¹ * localSpectralParameter 3 s) / (1 - localSpectralParameter 3 s)

/-- The predicted global spectral integral in the curve's Euler variable. -/
def ellipticSpectralZetaRatio (s : ℂ) : ℂ :=
  zetaFunction (localSpectralParameter 3 s) / zetaFunction (localSpectralParameter 3 s / 3)

private theorem parameter_three_pow (n : ℕ) (s : ℂ) :
    localSpectralParameter ((3 : ℝ≥0)^n) s = localSpectralParameter 3 s ^ n := by
  simp only [localSpectralParameter, NNReal.coe_pow]
  rw [Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.exp_nat_mul]
  congr 1
  ring

private theorem parameter_three_small (s : ℂ) (hs : 1 < s.re) :
    ‖localSpectralParameter 3 s‖ < 1 / 3 := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hthree : Real.exp (-Real.log 3) = (1 : ℝ) / 3 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    simp only [one_div]
  rw [localSpectralParameter, Complex.norm_exp, ← hthree]
  apply Real.exp_lt_exp.mpr
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, NNReal.coe_ofNat]
  nlinarith only [mul_pos (sub_pos.mpr hs) hlog]

/-- Actual local Haar factors agree with the geometric-degree Euler factors. -/
theorem ellipticFiniteSpectralFactor_eq_affine (s : ℂ) (v : FinitePlace) :
    ellipticFiniteSpectralFactor s v =
      ellipticAffineIntertwiningFactor (localSpectralParameter 3 s) (finitePlaceAffineEquiv v) := by
  unfold ellipticFiniteSpectralFactor ellipticAffineIntertwiningFactor
  rw [finitePlace_residue_card_eq_pow_degree]
  simp only [Nat.cast_pow, Nat.cast_ofNat, parameter_three_pow]
  simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_comm]

/-- The product is indexed by the actual finite adelic places. -/
theorem hasProd_ellipticFiniteSpectralFactor (s : ℂ) (hs : 1 < s.re) :
    HasProd (ellipticFiniteSpectralFactor s)
      (((1 - localSpectralParameter 3 s) * zetaFunction (localSpectralParameter 3 s)) /
        ((1 - localSpectralParameter 3 s / 3) * zetaFunction (localSpectralParameter 3 s / 3))) := by
  have h := (finitePlaceAffineEquiv.hasProd_iff).mpr
    (hasProd_elliptic_affine_intertwining_factors (parameter_three_small s hs))
  have he : ellipticFiniteSpectralFactor s =
      ellipticAffineIntertwiningFactor (localSpectralParameter 3 s) ∘ finitePlaceAffineEquiv := by
    funext v
    exact ellipticFiniteSpectralFactor_eq_affine s v
  rw [he]
  exact h

/-- Finite cylinder products converge to the complete zeta ratio on `Re(s)>1`. -/
theorem tendsto_ellipticSpectralCylinderProduct (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun S : Finset FinitePlace =>
      (∏ v ∈ S, ellipticFiniteSpectralFactor s v) * ellipticInfinitySpectralFactor s)
      atTop (𝓝 (ellipticSpectralZetaRatio s)) := by
  have hu := parameter_three_small s hs
  have hbase : Tendsto (fun S : Finset FinitePlace =>
      ∏ v ∈ S, ellipticFiniteSpectralFactor s v) atTop
      (𝓝 (((1 - localSpectralParameter 3 s) * zetaFunction (localSpectralParameter 3 s)) /
        ((1 - localSpectralParameter 3 s / 3) * zetaFunction (localSpectralParameter 3 s / 3)))) :=
    hasProd_ellipticFiniteSpectralFactor s hs
  have h := hbase.mul_const (ellipticInfinitySpectralFactor s)
  convert h using 1
  unfold ellipticSpectralZetaRatio ellipticInfinitySpectralFactor
  have hz := elliptic_euler_product_limit_ne_zero (div_three_small hu)
  have h₁ := one_sub_ne_zero_small hu
  have h₂ := one_sub_ne_zero_small (div_three_small hu)
  field_simp [h₁, h₂, hz]
  <;> ring

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.hasProd_elliptic_affine_intertwining_factors
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticFiniteSpectralFactor_eq_affine
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.tendsto_ellipticSpectralCylinderProduct
