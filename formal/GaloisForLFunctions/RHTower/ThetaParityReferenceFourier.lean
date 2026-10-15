import GaloisForLFunctions.RHTower.ThetaQuantileHalfPowerThreshold
import GaloisForLFunctions.RHTower.ThetaQuantileKronReduction
import GaloisForLFunctions.RHTower.ThetaParityReferenceCore
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# Fourier convergence of the theta parity reference readouts

The bounded quantile primitive `(pi/2) C (1-R)` has symmetric Fourier heads whose
paired sine/cosine expansion is exactly the finite reference operator from
`ThetaParityReferenceCore`, tested against `flatLp` source fields. Hilbert-basis
convergence therefore gives convergence of every such bilinear source readout.

Every bounded compactly supported source field has a `preFlat` representative
in the imported flat normal form. Thus the identity applies to the source packets
needed for the reference spectral lower bound. This module does not yet assert
that lower bound or residue alternation.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators InnerProductSpace
namespace RHTower
open HedenmalmThetaSource HedenmalmQuantile HedenmalmHilbertSchmidt
noncomputable section
local notation "H" => Lp ℂ 2 unitIntervalMeasure

/-- Unweighted primitive underlying the positive parity reference kernel. -/
def parityPrimitive : H →L[ℂ] H :=
  ((Real.pi / 2 : ℝ) : ℂ) • (pinnedVolterraCLM ∘L (1 - unitReflection))

def parityFourierTruncation (N : ℕ) : H →L[ℂ] H :=
  ContinuousLinearMap.hsTruncation unitFourierBasis parityPrimitive
    (Finset.Icc (-(N : ℤ)) (N : ℤ))

theorem tendsto_parityFourierTruncation (f : H) :
    Tendsto (fun N => parityFourierTruncation N f) atTop (𝓝 (parityPrimitive f)) := by
  have hmono : Monotone fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro a b hab
    refine Finset.Icc_subset_Icc ?_ ?_ <;> exact_mod_cast by omega
  have hex : ∀ x : ℤ, ∃ n : ℕ, x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    intro x
    refine ⟨x.natAbs, ?_⟩
    rw [Finset.mem_Icc]
    omega
  have h := (ContinuousLinearMap.hasSum_inner_smul unitFourierBasis parityPrimitive f).comp
    (tendsto_atTop_finset_of_monotone hmono hex)
  simpa only [parityFourierTruncation, ContinuousLinearMap.hsTruncation_apply, Function.comp_apply] using! h

theorem tendsto_inner_parityFourierTruncation (f g : H) :
    Tendsto (fun N => inner ℂ f (parityFourierTruncation N g)) atTop
      (𝓝 (inner ℂ f (parityPrimitive g))) :=
  ((innerSL ℂ f).continuous.tendsto _).comp (tendsto_parityFourierTruncation g)

theorem fourierMode_one_sub (n : ℤ) (t : ℝ) :
    fourierMode n (1 - t) = fourierMode (-n) t := by
  unfold fourierMode
  push_cast
  rw [show (2 * Real.pi * Complex.I * n * (1 - t) : ℂ) =
      (n : ℂ) * (2 * Real.pi * Complex.I) + 2 * Real.pi * Complex.I * (-n) * t by ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp

theorem unitReflection_unitFourierBasis (n : ℤ) :
    unitReflection (unitFourierBasis n) = unitFourierBasis (-n) := by
  apply Lp.ext
  filter_upwards [unitReflection_ae (unitFourierBasis n),
    ae_comp_unitReflection (coeFn_unitFourierBasis n), coeFn_unitFourierBasis (-n)]
    with t hr hn hm
  rw [hr, hn, hm, fourierMode_one_sub]

theorem parityPrimitive_unitFourierBasis_zero : parityPrimitive (unitFourierBasis 0) = 0 := by
  simp [parityPrimitive, unitReflection_unitFourierBasis]

theorem parityPrimitive_unitFourierBasis {n : ℤ} (hn : n ≠ 0) :
    parityPrimitive (unitFourierBasis n) =
      (4 * Complex.I * n : ℂ)⁻¹ •
        (unitFourierBasis n + unitFourierBasis (-n) - (2 : ℂ) • unitFourierBasis 0) := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [parityPrimitive, smul_apply, ContinuousLinearMap.comp_apply,
    sub_apply, one_apply_eq_self,
    unitReflection_unitFourierBasis, map_sub, pinnedVolterraCLM_unitFourierBasis hn,
    pinnedVolterraCLM_unitFourierBasis (neg_ne_zero.mpr hn), Int.cast_neg, mul_neg,
    inv_neg, neg_smul, sub_neg_eq_add]
  simp only [smul_add, smul_sub, smul_smul]
  have hs : ((Real.pi / 2 : ℝ) : ℂ) * (2 * Real.pi * Complex.I * n : ℂ)⁻¹ =
      (4 * Complex.I * n : ℂ)⁻¹ := by
    push_cast
    field_simp
    ring
  rw [hs]
  module

def paritySineMode (n : ℤ) : H :=
  (2 * Complex.I)⁻¹ • (unitFourierBasis n - unitFourierBasis (-n))

def parityCosineMode (n : ℤ) : H :=
  unitFourierBasis 0 - (2 : ℂ)⁻¹ • (unitFourierBasis n + unitFourierBasis (-n))

theorem paritySineMode_ae (n : ℤ) :
    (paritySineMode n : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => (Real.sin (2 * Real.pi * n * t) : ℂ) := by
  filter_upwards [Lp.coeFn_smul ((2 * Complex.I)⁻¹)
      (unitFourierBasis n - unitFourierBasis (-n)),
    Lp.coeFn_sub (unitFourierBasis n) (unitFourierBasis (-n)),
    coeFn_unitFourierBasis n, coeFn_unitFourierBasis (-n)] with t h1 h2 h3 h4
  change (((2 * Complex.I)⁻¹ • (unitFourierBasis n - unitFourierBasis (-n)) : H) t) = _
  rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, smul_eq_mul,
    fourierMode_eq_cos_add_sin, fourierMode_eq_cos_add_sin,
    show 2 * Real.pi * ((-n : ℤ) : ℝ) * t = -(2 * Real.pi * n * t) by push_cast; ring,
    Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  field_simp
  ring

theorem parityCosineMode_ae (n : ℤ) :
    (parityCosineMode n : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => ((1 - Real.cos (2 * Real.pi * n * t) : ℝ) : ℂ) := by
  filter_upwards [Lp.coeFn_sub (unitFourierBasis 0)
      ((2 : ℂ)⁻¹ • (unitFourierBasis n + unitFourierBasis (-n))),
    Lp.coeFn_smul ((2 : ℂ)⁻¹) (unitFourierBasis n + unitFourierBasis (-n)),
    Lp.coeFn_add (unitFourierBasis n) (unitFourierBasis (-n)),
    coeFn_unitFourierBasis 0, coeFn_unitFourierBasis n, coeFn_unitFourierBasis (-n)]
    with t h1 h2 h3 h4 h5 h6
  change ((unitFourierBasis 0 - (2 : ℂ)⁻¹ • (unitFourierBasis n + unitFourierBasis (-n)) : H) t) = _
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, Pi.add_apply, h4, h5, h6,
    fourierMode_zero, smul_eq_mul, fourierMode_eq_cos_add_sin, fourierMode_eq_cos_add_sin,
    show 2 * Real.pi * ((-n : ℤ) : ℝ) * t = -(2 * Real.pi * n * t) by push_cast; ring,
    Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem paritySineMode_zero : paritySineMode 0 = 0 := by simp [paritySineMode]

theorem parityCosineMode_neg (n : ℤ) : parityCosineMode (-n) = parityCosineMode n := by
  simp only [parityCosineMode, neg_neg, add_comm]

theorem parityPrimitive_unitFourierBasis_cosine {n : ℤ} (hn : n ≠ 0) :
    parityPrimitive (unitFourierBasis n) =
      (Complex.I / (2 * n : ℂ)) • parityCosineMode n := by
  rw [parityPrimitive_unitFourierBasis hn, parityCosineMode]
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hs : (4 * Complex.I * n : ℂ)⁻¹ = -(Complex.I / (2 * n : ℂ) * (2 : ℂ)⁻¹) := by
    field_simp
    norm_num [Complex.I_sq]
  rw [hs]
  module

theorem parityFourierPair (n : ℤ) (hn : n ≠ 0) (f : H) :
    inner ℂ (unitFourierBasis n) f • parityPrimitive (unitFourierBasis n) +
      inner ℂ (unitFourierBasis (-n)) f • parityPrimitive (unitFourierBasis (-n)) =
    ((n : ℂ)⁻¹ * inner ℂ (paritySineMode n) f) • parityCosineMode n := by
  rw [parityPrimitive_unitFourierBasis_cosine hn,
    parityPrimitive_unitFourierBasis_cosine (neg_ne_zero.mpr hn), parityCosineMode_neg,
    paritySineMode, inner_smul_left, inner_sub_left]
  simp only [smul_smul, ← add_smul, map_inv₀, map_mul, map_ofNat, Complex.conj_I, Int.cast_neg]
  congr 1
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp
  simp [Complex.I_sq]
  ring

theorem parityFourierTruncation_eq (N : ℕ) (f : H) :
    parityFourierTruncation N f =
      ∑ n ∈ Finset.range (N + 1),
        ((n : ℂ)⁻¹ * inner ℂ (paritySineMode n) f) • parityCosineMode n := by
  simp only [parityFourierTruncation, ContinuousLinearMap.hsTruncation_apply]
  induction N with
  | zero => simp [parityPrimitive_unitFourierBasis_zero]
  | succ N ih =>
    rw [show (↑(N + 1) : ℤ) = (N : ℤ) + 1 by omega,
      Finset.sum_Icc_succ_eq_add_endpoints, ih, Finset.sum_range_succ _ (N + 1),
      parityFourierPair ((N : ℤ) + 1) (by omega)]
    push_cast
    abel

private theorem inner_source_flatLp {v : ThetaParitySourceL2} {w : H} {p : ℝ → ℂ}
    (hv : (v : ℝ → ℂ) =ᵐ[volume] fun x => p (thetaSource.cdfFun x))
    (hw : (w : ℝ → ℂ) =ᵐ[unitIntervalMeasure] p)
    (hp : AEStronglyMeasurable p unitIntervalMeasure) (f : H) :
    inner ℂ v (flatLp f) = inner ℂ w f := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have he : (fun t => inner ℂ (w t) (f t)) =ᵐ[unitIntervalMeasure]
      fun t => (starRingEnd ℂ) (p t) * f t := by
    filter_upwards [hw] with t ht
    rw [ht, RCLike.inner_apply']
  have hm : AEStronglyMeasurable (fun t => (starRingEnd ℂ) (p t) * f t) unitIntervalMeasure :=
    (Complex.continuous_conj.comp_aestronglyMeasurable hp).mul (Lp.aestronglyMeasurable f)
  rw [integral_congr_ae he, integral_unitInterval_eq_cdf hm]
  apply integral_congr_ae
  filter_upwards [hv, flatLp_ae f] with x hx hf
  rw [hx, hf, RCLike.inner_apply', flatField, Complex.real_smul]
  ring

theorem inner_thetaParitySineVec_flatLp (n : ℤ) (f : H) :
    inner ℂ (thetaParitySineVec n) (flatLp f) = inner ℂ (paritySineMode n) f :=
  inner_source_flatLp (thetaParitySineVec_ae n) (paritySineMode_ae n)
    (Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable f

theorem inner_flatLp_thetaParityCosineVec (n : ℤ) (f : H) :
    inner ℂ (flatLp f) (thetaParityCosineVec n) = inner ℂ f (parityCosineMode n) := by
  have h := inner_source_flatLp (thetaParityCosineVec_ae n) (parityCosineMode_ae n)
    (Complex.continuous_ofReal.comp (continuous_const.sub
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)))).aestronglyMeasurable f
  simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) h

theorem inner_flatLp_thetaParityReferenceOperator (N : ℕ) (f g : H) :
    inner ℂ (flatLp g) (thetaParityReferenceOperator (N + 1) (flatLp f)) =
      inner ℂ g (parityFourierTruncation N f) := by
  rw [inner_thetaParityReferenceOperator, parityFourierTruncation_eq, inner_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [inner_smul_right, inner_thetaParitySineVec_flatLp, inner_flatLp_thetaParityCosineVec]

theorem tendsto_inner_flatLp_thetaParityReferenceOperator (f g : H) :
    Tendsto (fun N => inner ℂ (flatLp g) (thetaParityReferenceOperator (N + 1) (flatLp f))) atTop
      (𝓝 (inner ℂ g (parityPrimitive f))) := by
  simp_rw [inner_flatLp_thetaParityReferenceOperator]
  exact tendsto_inner_parityFourierTruncation g f

end
end RHTower
