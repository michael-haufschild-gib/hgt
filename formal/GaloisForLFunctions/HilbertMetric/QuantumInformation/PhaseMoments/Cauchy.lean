import GaloisForLFunctions.HilbertMetric.QuantumInformation.ToeplitzPartialTranspose
import GaloisForLFunctions.HTGeometry.FiniteAtomicCubature
import GaloisForLFunctions.RHTower.XiCosineShiftSechHandoff
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Integral

/-!
# Positive phase moments for the Cauchy charge state

The positive moment representation in Qian and Zhang (arXiv:2611.24473,
Theorem 4(b)) is explicit for the Cauchy kernel. A single random phase with
the hyperbolic secant law drives all sites. Its pushforward to the phase
torus represents every multidegree moment, and in particular the whole
qubit density matrix as an average of equatorial product states.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HilbertMetric.CauchyPhase

noncomputable section

private def density (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (RHTower.sechPort (1 / 2) t)

private def noise : Measure ℝ := volume.withDensity density

private theorem half_pos : 0 < (1 / 2 : ℝ) := by positivity

private instance : IsProbabilityMeasure noise := by
  rw [isProbabilityMeasure_iff, noise, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  unfold density
  rw [← ofReal_integral_eq_lintegral_ofReal (RHTower.integrable_sechPort half_pos)
    (Eventually.of_forall fun t => (RHTower.sechPort_pos half_pos t).le),
    RHTower.integral_sechPort half_pos, ENNReal.ofReal_one]

private theorem integral_noise_character (d : ℝ) :
    (∫ t : ℝ, Complex.exp (-(Complex.I * (t : ℂ) * (d : ℂ))) ∂noise) =
      ((Real.cosh (d / 2))⁻¹ : ℝ) := by
  have hm : Measurable density :=
    (ENNReal.continuous_ofReal.comp (RHTower.continuous_sechPort (1 / 2))).measurable
  rw [noise, integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [density, ENNReal.toReal_ofReal (RHTower.sechPort_pos half_pos _).le, Complex.real_smul]
  rw [RHTower.integral_sechPort_mul_cexp half_pos, show (1 / 2 : ℝ) * d = d / 2 by ring,
    one_div]

variable {σ : Type*} [Fintype σ]

/-- A common phase at all sites, with the indicated real charges. -/
def phaseCurve (w : σ → ℝ) (t : ℝ) : σ → Circle :=
  fun i => Circle.exp (-(t * w i))

private theorem continuous_phaseCurve (w : σ → ℝ) : Continuous (phaseCurve w) := by
  apply continuous_pi
  intro i
  exact Circle.exp.continuous.comp (by fun_prop : Continuous fun t : ℝ => -(t * w i))

/-- Positive representing measure on the entire site phase torus. -/
def phaseLaw (w : σ → ℝ) : ProbabilityMeasure (σ → Circle) :=
  (⟨noise, inferInstance⟩ : ProbabilityMeasure ℝ).map (continuous_phaseCurve w).aemeasurable

/-- The torus character at any integer multidegree. -/
def character (n : σ → ℤ) (z : σ → Circle) : ℂ := ∏ i, (z i : ℂ) ^ n i

private theorem continuous_character (n : σ → ℤ) : Continuous (character n) := by
  unfold character
  apply continuous_finsetProd
  intro i _
  have h : Continuous (fun z : σ → Circle => (z i) ^ n i) := (continuous_apply i).zpow _
  simpa only [Circle.coe_zpow] using continuous_subtype_val.comp h

private theorem character_phaseCurve (w : σ → ℝ) (n : σ → ℤ) (t : ℝ) :
    character n (phaseCurve w t) =
      Complex.exp (-(Complex.I * (t : ℂ) * ((∑ i, (n i : ℝ) * w i : ℝ) : ℂ))) := by
  simp only [character, phaseCurve, Circle.coe_exp, ← Complex.exp_int_mul, ← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- All integer moments are sech of half of the charge pairing. -/
theorem integral_character_phaseLaw (w : σ → ℝ) (n : σ → ℤ) :
    (∫ z, character n z ∂(phaseLaw w : Measure (σ → Circle))) =
      ((Real.cosh ((∑ i, (n i : ℝ) * w i) / 2))⁻¹ : ℝ) := by
  rw [phaseLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_phaseCurve w).aemeasurable (continuous_character n).aestronglyMeasurable]
  simp_rw [character_phaseCurve]
  exact integral_noise_character _

private def bitDifference (x y : σ → Bool) (i : σ) : ℤ :=
  (if x i then 1 else 0) - (if y i then 1 else 0)

private theorem charge_difference (w : σ → ℝ) (x y : σ → Bool) :
    ∑ i, (bitDifference x y i : ℝ) * w i = bitCharge w x - bitCharge w y := by
  rw [bitCharge, bitCharge, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases hx : x i <;> cases hy : y i <;> simp [bitDifference, hx, hy]

variable [DecidableEq σ]

/-- An equatorial product-state matrix, obtained by multiplying the local
one-qubit phase entries and dividing by the dimension. -/
def equatorialProduct (z : σ → Circle) (x y : σ → Bool) : ℂ :=
  (Fintype.card (σ → Bool) : ℂ)⁻¹ * character (bitDifference x y) z

/-- Normalized local vector with the specified equatorial phase. -/
def equatorialAmplitude (z : Circle) (b : Bool) : ℂ :=
  (if b then (z : ℂ) else 1) / (Real.sqrt 2 : ℂ)

/-- The mixture atoms are literal products of local pure-state entries. -/
theorem equatorialProduct_eq_local (z : σ → Circle) (x y : σ → Bool) :
    equatorialProduct z x y =
      ∏ i, equatorialAmplitude (z i) (x i) * star (equatorialAmplitude (z i) (y i)) := by
  have hcard : (Fintype.card (σ → Bool) : ℂ)⁻¹ = ∏ _ : σ, (1 / 2 : ℂ) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat,
      Finset.prod_const, Finset.card_univ, one_div, inv_pow]
  unfold equatorialProduct character
  rw [hcard, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity : 0 ≤ (2 : ℝ))]
    norm_cast
  have hi : (z i : ℂ)⁻¹ = (starRingEnd ℂ) (z i : ℂ) :=
    Complex.inv_eq_conj (Circle.norm_coe _)
  have hu : (z i : ℂ) * (starRingEnd ℂ) (z i : ℂ) = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, Circle.norm_coe]
    norm_num
  rw [equatorialAmplitude, equatorialAmplitude, Complex.star_def, map_div₀,
    Complex.conj_ofReal, div_mul_div_comm, hs]
  cases hx : x i <;> cases hy : y i <;>
    simp [bitDifference, hx, hy, hi, hu, div_eq_mul_inv, mul_comm]

/-- The Cauchy charge state is exactly the average of these product-state
entries. The representing measure is a probability for any real charges. -/
theorem cauchyChargeState_apply_integral (w : σ → ℝ) (x y : σ → Bool) :
    cauchyChargeState w x y =
      ∫ z, equatorialProduct z x y ∂(phaseLaw w : Measure (σ → Circle)) := by
  unfold equatorialProduct
  rw [integral_const_mul, integral_character_phaseLaw, charge_difference]
  simp only [cauchyChargeState, chargeDifferenceMatrix, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast]

/-- Real and imaginary coordinates for the kernel on the qubit basis. -/
private abbrev Entry (σ : Type*) := Bool × ((σ → Bool) × (σ → Bool))

private def coord (M : (σ → Bool) → (σ → Bool) → ℂ) (i : Entry σ) : ℝ :=
  if i.1 then (M i.2.1 i.2.2).im else (M i.2.1 i.2.2).re

private theorem continuous_equatorialProduct (x y : σ → Bool) :
    Continuous fun z : σ → Circle => equatorialProduct z x y :=
  continuous_const.mul (continuous_character (bitDifference x y))

/-- The Cauchy charge state has a finite positive equatorial decomposition.
The atom bound is the number of real matrix coordinates plus one. -/
theorem exists_finite_equatorial_decomposition (w : σ → ℝ) :
    ∃ (p : Fin (Fintype.card (Entry σ) + 1) → ℝ)
      (z : Fin (Fintype.card (Entry σ) + 1) → σ → Circle),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
      ∀ x y, (∑ i, (p i : ℂ) * equatorialProduct (z i) x y) = cauchyChargeState w x y := by
  classical
  let n := Fintype.card (Entry σ)
  let e : Fin n ≃ Entry σ := (Fintype.equivFin (Entry σ)).symm
  let f : (σ → Circle) → Fin n → ℝ := fun z j => coord (equatorialProduct z) (e j)
  let S : Set (Fin n → ℝ) := Set.range f
  let μ : Measure (σ → Circle) := phaseLaw w
  haveI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  have hf : Continuous f := by
    apply continuous_pi
    intro j
    change Continuous fun z : σ → Circle => coord (equatorialProduct z) (e j)
    unfold coord
    split
    · exact Complex.continuous_im.comp (continuous_equatorialProduct _ _)
    · exact Complex.continuous_re.comp (continuous_equatorialProduct _ _)
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm : (∫ z, f z ∂μ) = fun j => coord (cauchyChargeState w) (e j) := by
    funext j
    let L : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
    change L (∫ z, f z ∂μ) = _
    rw [← L.integral_comp_comm hfi]
    change (∫ z, coord (equatorialProduct z) (e j) ∂μ) =
      coord (cauchyChargeState w) (e j)
    let x := (e j).2.1
    let y := (e j).2.2
    have hint : Integrable (fun z => equatorialProduct z x y) μ :=
      (continuous_equatorialProduct x y).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hentry : (∫ z, equatorialProduct z x y ∂μ) = cauchyChargeState w x y :=
      (cauchyChargeState_apply_integral w x y).symm
    unfold coord
    by_cases h : (e j).1
    · simp only [h, if_true]
      exact (Complex.imCLM.integral_comp_comm hint).trans (congrArg Complex.im hentry)
    · simp only [h, if_false]
      exact (Complex.reCLM.integral_comp_comm hint).trans (congrArg Complex.re hentry)
  have hHull : (∫ z, f z ∂μ) ∈ closure (convexHull ℝ S) :=
    (convex_convexHull ℝ S).closure.integral_mem isClosed_closure
      (Eventually.of_forall fun z => subset_closure (subset_convexHull ℝ S ⟨z, rfl⟩)) hfi
  obtain ⟨p, atoms, hp, hsum, ha, heq⟩ :=
    HTGeometry.exists_atomic_of_mem_closure_convexHull (isCompact_range hf)
      ⟨f (fun _ => 1), ⟨_, rfl⟩⟩ hHull
  have ha' (i : Fin (n+1)) : ∃ z : σ → Circle, f z = atoms i := ha i
  choose z hz using ha'
  simp_rw [← hz, hm] at heq
  refine ⟨p, z, hp, hsum, fun x y => ?_⟩
  have hcoord (b : Bool) := congrFun heq (e.symm (b, x, y))
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f, Equiv.apply_symm_apply] at hcoord
  apply Complex.ext
  · have hr := hcoord false
    simp only [coord, Bool.false_eq_true, if_false] at hr
    simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hr
  · have hi := hcoord true
    simp only [coord, if_true] at hi
    simpa only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using hi

#print axioms integral_character_phaseLaw
#print axioms equatorialProduct_eq_local
#print axioms cauchyChargeState_apply_integral
#print axioms exists_finite_equatorial_decomposition

end

end GaloisForLFunctions.HilbertMetric.CauchyPhase
