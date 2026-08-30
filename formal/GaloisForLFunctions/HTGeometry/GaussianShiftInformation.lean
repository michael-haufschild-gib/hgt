import GaloisForLFunctions.HTGeometry.GaussianPacketTestingLaw
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Gaussian shift information

The reusable analytic layer behind the Gaussian formation cards.

* `lintegral_pi_prod`  Tonelli for a coordinatewise product on a finite product measure (mathlib
  has only the Bochner version, `integral_fintype_prod_eq_prod`);
* `pi_withDensity`  a coordinatewise density on a product measure is the product of the coordinate
  densities;
* `map_withDensity_measurableEquiv`  transport of a density along a measurable equivalence;
* `stdGaussian_shift_eq_withDensity`, `rnDeriv_stdGaussian_shift`  the **Cameron--Martin density**
  `exp(⟪m, x⟫ - ‖m‖²/2)` of a Gaussian shift, in coordinate-free form;
* `lintegral_exp_inner_stdGaussian`  the Gaussian moment generating function `exp(‖t‖²/2)`;
* `lintegral_cameronMartin_rpow`  the Rényi integral `exp(-α(1-α)‖m‖²/2)`, and its Hellinger
  specialization `lintegral_cameronMartin_sqrt` = `exp(-‖m‖²/8)`.

Everything is unconditional.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Tonelli for a product of coordinatewise functions on a finite product measure. -/
theorem lintegral_pi_prod {n : ℕ} {E : Fin n → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, f i y ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hmeas : Measurable fun x : ∀ i : Fin (n + 1), E i => ∏ i, f i (x i) :=
        Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
      have hsymm := (measurePreserving_piFinSuccAbove μ 0).symm
      rw [← hsymm.lintegral_comp hmeas]
      have hfun : ∀ z : E 0 × (∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j)),
          (∏ i, f i (((MeasurableEquiv.piFinSuccAbove E 0).symm z) i))
            = f 0 z.1 * ∏ j, f ((0 : Fin (n + 1)).succAbove j) (z.2 j) := by
        rintro ⟨a, y⟩
        rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.prod_univ_succ]
        congr 1
      simp_rw [hfun]
      have hprodmeas : Measurable fun (y : ∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j)) =>
          ∏ j, f ((0 : Fin (n + 1)).succAbove j) (y j) :=
        Finset.measurable_prod _ fun j _ => (hf _).comp (measurable_pi_apply j)
      rw [lintegral_prod _ (by
        exact (((hf 0).comp measurable_fst).mul (hprodmeas.comp measurable_snd)).aemeasurable)]
      have hstep : ∀ a : E 0,
          ∫⁻ y, f 0 a * ∏ j, f ((0 : Fin (n + 1)).succAbove j) (y j)
              ∂(Measure.pi fun j : Fin n => μ ((0 : Fin (n + 1)).succAbove j))
            = f 0 a * ∏ j : Fin n, ∫⁻ y, f ((0 : Fin (n + 1)).succAbove j) y
              ∂(μ ((0 : Fin (n + 1)).succAbove j)) := by
        intro a
        rw [lintegral_const_mul _ hprodmeas,
          ih (fun j : Fin n => μ ((0 : Fin (n + 1)).succAbove j))
            (f := fun j : Fin n => f ((0 : Fin (n + 1)).succAbove j)) (fun j => hf _)]
      simp_rw [hstep]
      rw [lintegral_mul_const _ (hf 0), Fin.prod_univ_succ]
      rfl

/-- A coordinatewise density on a finite product measure is the product of the coordinate
densities. -/
theorem pi_withDensity {n : ℕ} {E : Fin n → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
      = Measure.pi fun i => (μ i).withDensity (f i) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : ∀ i, E i, (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x
      = ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      rw [Set.indicator_of_notMem hi]
  simp_rw [hind]
  rw [lintegral_pi_prod μ (fun i => (hf i).indicator (hs i))]
  exact Finset.prod_congr rfl fun i _ => by
    rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]

/-- Transport of a density along a measurable equivalence. -/
theorem map_withDensity_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (e : α ≃ᵐ β) {g : α → ℝ≥0∞} (hg : Measurable g) :
    (ν.withDensity g).map e = (ν.map e).withDensity (fun y => g (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map e.measurable hs,
    lintegral_map (by exact hg.comp e.symm.measurable) e.measurable]
  refine setLIntegral_congr_fun (e.measurable hs) fun x _ => ?_
  rw [MeasurableEquiv.symm_apply_apply]

/-! ## The Cameron--Martin density -/

theorem pi_gaussianReal_shift {n : ℕ} (c : Fin n → ℝ) :
    (Measure.pi fun i => gaussianReal (c i) 1)
      = (Measure.pi fun _ : Fin n => gaussianReal 0 1).withDensity
        (fun x => ∏ i, ENNReal.ofReal (Real.exp (c i * x i - c i ^ 2 / 2))) := by
  have hf : ∀ i, Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (c i * x - c i ^ 2 / 2))) :=
    fun i => by fun_prop
  have hd : ∀ i, (gaussianReal 0 1).withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp (c i * x - c i ^ 2 / 2))) = gaussianReal (c i) 1 :=
    fun i => (gaussianReal_eq_withDensity_shift (c i)).symm
  haveI hsf : ∀ i, SigmaFinite ((gaussianReal 0 1).withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp (c i * x - c i ^ 2 / 2)))) := by
    intro i
    rw [hd i]
    infer_instance
  rw [pi_withDensity _ hf]
  congr 1
  funext i
  exact (hd i).symm

section CameronMartin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The coordinate isomorphism of an orthonormal basis as a measurable equivalence. -/
def onbMeasurableEquiv {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) : (Fin n → ℝ) ≃ᵐ E :=
  (onbEquiv b).toHomeomorph.toMeasurableEquiv

@[simp] theorem onbMeasurableEquiv_apply {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (x : Fin n → ℝ) : onbMeasurableEquiv b x = onbEquiv b x := rfl

theorem inner_onbEquiv {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (m : E) (x : Fin n → ℝ) :
    ⟪m, onbEquiv b x⟫ = ∑ i, x i * (b.repr m).ofLp i := by
  rw [onbEquiv_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, real_inner_comm]
  congr 1
  exact (b.repr_apply_apply m i).symm

/-- **The Cameron--Martin density.**  A Gaussian shift is an exponential tilt of the standard
Gaussian. -/
theorem stdGaussian_shift_eq_withDensity (m : E) :
    (stdGaussian E).map (fun x => x + m)
      = (stdGaussian E).withDensity
        (fun x => ENNReal.ofReal (Real.exp (⟪m, x⟫ - ‖m‖ ^ 2 / 2))) := by
  classical
  set n := Module.finrank ℝ E with hn
  set b := stdOrthonormalBasis ℝ E with hb
  set c : Fin n → ℝ := fun i => (b.repr m).ofLp i with hc
  have hnorm : ∑ i, c i ^ 2 = ‖m‖ ^ 2 := by
    have hiso : ‖b.repr m‖ = ‖m‖ := b.repr.norm_map m
    rw [← hiso, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]; exact (sq_abs _).symm
  have hmeasd : Measurable
      (fun x : Fin n → ℝ => ∏ i, ENNReal.ofReal (Real.exp (c i * x i - c i ^ 2 / 2))) := by
    fun_prop
  rw [stdGaussian_shift_eq_map_onb b m, pi_gaussianReal_shift c, stdGaussian_eq_map_onb b]
  rw [show ((onbEquiv b : (Fin n → ℝ) → E))
      = ((onbMeasurableEquiv b : (Fin n → ℝ) → E)) from rfl]
  rw [map_withDensity_measurableEquiv _ (onbMeasurableEquiv b) hmeasd]
  congr 1
  funext y
  have hy : onbEquiv b ((onbMeasurableEquiv b).symm y) = y :=
    MeasurableEquiv.apply_symm_apply (onbMeasurableEquiv b) y
  have hsum : ⟪m, y⟫ = ∑ i, ((onbMeasurableEquiv b).symm y) i * c i := by
    conv_lhs => rw [← hy]
    rw [inner_onbEquiv, hc]
  calc ∏ i, ENNReal.ofReal (Real.exp (c i * ((onbMeasurableEquiv b).symm y) i - c i ^ 2 / 2))
      = ENNReal.ofReal (∏ i, Real.exp (c i * ((onbMeasurableEquiv b).symm y) i - c i ^ 2 / 2)) := by
        rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_nonneg _))]
    _ = ENNReal.ofReal (Real.exp (∑ i, (c i * ((onbMeasurableEquiv b).symm y) i - c i ^ 2 / 2))) := by
        rw [Real.exp_sum]
    _ = ENNReal.ofReal (Real.exp (⟪m, y⟫ - ‖m‖ ^ 2 / 2)) := by
        congr 2
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, hnorm]
        congr 1
        rw [hsum]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end CameronMartin

/-! ## The Gaussian moment generating function and the Rényi integral -/

theorem lintegral_exp_mul_gaussianReal (d : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (y * d)) ∂(gaussianReal 0 1)
      = ENNReal.ofReal (Real.exp (d ^ 2 / 2)) := by
  have hint : Integrable (fun y : ℝ => Real.exp (y * d)) (gaussianReal 0 1) := by
    simpa [mul_comm] using integrable_exp_mul_gaussianReal (μ := 0) (v := 1) d
  have hmgf : ∫ y, Real.exp (y * d) ∂(gaussianReal 0 1) = Real.exp (d ^ 2 / 2) := by
    have h := mgf_gaussianReal (X := fun x : ℝ => x) (p := gaussianReal 0 1)
      (μ := 0) (v := 1) (by simp) d
    rw [mgf] at h
    simpa [mul_comm] using h
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun y => (Real.exp_nonneg _)), hmgf]

section MGF

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The Gaussian moment generating function.** -/
theorem lintegral_exp_inner_stdGaussian (t : E) :
    ∫⁻ x, ENNReal.ofReal (Real.exp ⟪t, x⟫) ∂(stdGaussian E)
      = ENNReal.ofReal (Real.exp (‖t‖ ^ 2 / 2)) := by
  classical
  set n := Module.finrank ℝ E with hn
  set b := stdOrthonormalBasis ℝ E with hb
  set d : Fin n → ℝ := fun i => (b.repr t).ofLp i with hd
  have hnorm : ∑ i, d i ^ 2 = ‖t‖ ^ 2 := by
    have hiso : ‖b.repr t‖ = ‖t‖ := b.repr.norm_map t
    rw [← hiso, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun i _ => by rw [hd]; exact (sq_abs _).symm
  rw [stdGaussian_eq_map_onb b, lintegral_map (by fun_prop) (by fun_prop)]
  have hterm : ∀ z : Fin n → ℝ,
      ENNReal.ofReal (Real.exp ⟪t, onbEquiv b z⟫)
        = ∏ i, ENNReal.ofReal (Real.exp (z i * d i)) := by
    intro z
    have hdi : ∀ i, (b.repr t).ofLp i = d i := fun i => rfl
    rw [inner_onbEquiv]
    simp only [hdi]
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.exp_nonneg _)]
  simp_rw [hterm]
  rw [lintegral_pi_prod (fun _ : Fin n => gaussianReal 0 1)
    (f := fun i => fun y : ℝ => ENNReal.ofReal (Real.exp (y * d i))) (fun i => by fun_prop)]
  simp_rw [lintegral_exp_mul_gaussianReal]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.exp_nonneg _), ← Real.exp_sum,
    ← Finset.sum_div, hnorm]

/-- **`(GQF.15)`.**  The Rényi integral of a Gaussian shift pair. -/
theorem lintegral_cameronMartin_rpow {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (m : E) :
    ∫⁻ x, (ENNReal.ofReal (Real.exp (⟪m, x⟫ - ‖m‖ ^ 2 / 2))) ^ (1 - α) ∂(stdGaussian E)
      = ENNReal.ofReal (Real.exp (-(α * (1 - α) * ‖m‖ ^ 2 / 2))) := by
  have hβ : (0:ℝ) ≤ 1 - α := by linarith
  have hpow : ∀ x : E, (ENNReal.ofReal (Real.exp (⟪m, x⟫ - ‖m‖ ^ 2 / 2))) ^ (1 - α)
      = ENNReal.ofReal (Real.exp (-((1 - α) * ‖m‖ ^ 2 / 2)))
        * ENNReal.ofReal (Real.exp ⟪(1 - α) • m, x⟫) := by
    intro x
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) hβ, ← Real.exp_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    rw [real_inner_smul_left]
    ring
  simp_rw [hpow]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_exp_inner_stdGaussian,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ, mul_pow]
  ring

/-- **`(GQF.13)`.**  The Hellinger/Bhattacharyya affinity of a Gaussian shift pair. -/
theorem lintegral_cameronMartin_sqrt (m : E) :
    ∫⁻ x, (ENNReal.ofReal (Real.exp (⟪m, x⟫ - ‖m‖ ^ 2 / 2))) ^ (1 / 2 : ℝ) ∂(stdGaussian E)
      = ENNReal.ofReal (Real.exp (-(‖m‖ ^ 2 / 8))) := by
  have h := lintegral_cameronMartin_rpow (α := (1/2 : ℝ)) (by norm_num) (by norm_num) m
  norm_num at h ⊢
  rw [h]
  congr 2
  ring

/-- The Radon--Nikodym derivative of the Gaussian shift. -/
theorem rnDeriv_stdGaussian_shift (m : E) :
    ((stdGaussian E).map (fun x => x + m)).rnDeriv (stdGaussian E)
      =ᵐ[stdGaussian E] fun x => ENNReal.ofReal (Real.exp (⟪m, x⟫ - ‖m‖ ^ 2 / 2)) := by
  rw [stdGaussian_shift_eq_withDensity]
  exact Measure.rnDeriv_withDensity _ (by fun_prop)

end MGF

/-! ## The binary orthogonal product -/

section ProdL2

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y]
  [BorelSpace Y]

/-- **The standard Gaussian on an `ℓ²` orthogonal product is the independent product.** -/
theorem stdGaussian_prodL2 :
    stdGaussian (WithLp 2 (X × Y))
      = ((stdGaussian X).prod (stdGaussian Y)).map (WithLp.toLp 2) := by
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_stdGaussian, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hinner : ∀ p : X × Y,
      (⟪(WithLp.toLp 2 p : WithLp 2 (X × Y)), t⟫ : ℝ) = ⟪p.1, t.fst⟫ + ⟪p.2, t.snd⟫ := by
    intro p
    rw [WithLp.prod_inner_apply]
    rfl
  simp_rw [hinner, Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [integral_prod_mul (f := fun x : X => Complex.exp ((⟪x, t.fst⟫ : ℝ) * Complex.I))
    (g := fun y : Y => Complex.exp ((⟪y, t.snd⟫ : ℝ) * Complex.I))]
  rw [← charFun_apply, ← charFun_apply, charFun_stdGaussian, charFun_stdGaussian,
    ← Complex.exp_add]
  congr 1
  have hn : (‖t‖ : ℝ) ^ 2 = ‖t.fst‖ ^ 2 + ‖t.snd‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 t
  have hnC : (‖t‖ : ℂ) ^ 2 = (‖t.fst‖ : ℂ) ^ 2 + (‖t.snd‖ : ℂ) ^ 2 := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hn
    push_cast at h
    exact h
  rw [hnC]
  ring

end ProdL2

end

end GaloisForLFunctions.HTGeometry
