import GaloisForLFunctions.HTGeometry.PoissonIntensityMarkingIsometry
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Gaussian formation rate region

Section 3 of the formation-resource card `ULF-FRM-4`, together with the Gaussian information layer
it needs.

* `klDiv_gaussianReal_shift`  the one-dimensional Cameron--Martin divergence `c²/2`;
* `klDiv_stdGaussian_shift`  its coordinate-free form `‖m‖²/2` on a finite-dimensional real inner
  product space, obtained by an orthonormal-basis reduction to a product of one-dimensional shifts;
* `klDiv_comp_le`  randomized data processing for `klDiv` (mathlib has only the deterministic form);
* `garblingOp`, `gaussianGarbling`  the explicit Gaussian garbling: rescale the source observation
  onto the signal direction and add shaped independent Gaussian noise;
* `nonempty_gaussianFormation_iff`  **`(CDS.15)`**: an exact Gaussian formation of signal `m` out of
  source capital `b > 0` exists **iff** `‖m‖² ≤ b`.

Everything is unconditional.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cameron--Martin density of a one-dimensional Gaussian shift. -/
theorem gaussianReal_eq_withDensity_shift (c : ℝ) :
    gaussianReal c 1 = (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (c * x - c ^ 2 / 2))) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianReal_of_var_ne_zero _ one_ne_zero,
    ← withDensity_mul _ (measurable_gaussianPDF 0 1) (by fun_prop)]
  congr 1
  funext x
  rw [Pi.mul_apply, gaussianPDF, gaussianPDF,
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  rw [gaussianPDFReal, gaussianPDFReal]
  have hexp : Real.exp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) * Real.exp (c * x - c ^ 2 / 2)
      = Real.exp (-(x - c) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [← hexp]
  ring

theorem klDiv_gaussianReal_shift (c : ℝ) :
    klDiv (gaussianReal c 1) (gaussianReal 0 1) = ENNReal.ofReal (c ^ 2 / 2) := by
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (c * x - c ^ 2 / 2))) := by
    fun_prop
  have hac : gaussianReal c 1 ≪ gaussianReal 0 1 := by
    rw [gaussianReal_eq_withDensity_shift c]
    exact withDensity_absolutelyContinuous _ _
  have hrn : (gaussianReal c 1).rnDeriv (gaussianReal 0 1)
      =ᵐ[gaussianReal 0 1] fun x => ENNReal.ofReal (Real.exp (c * x - c ^ 2 / 2)) := by
    rw [gaussianReal_eq_withDensity_shift c]
    exact Measure.rnDeriv_withDensity _ hmeas
  have hrn' : (gaussianReal c 1).rnDeriv (gaussianReal 0 1)
      =ᵐ[gaussianReal c 1] fun x => ENNReal.ofReal (Real.exp (c * x - c ^ 2 / 2)) := hac hrn
  have hllr : llr (gaussianReal c 1) (gaussianReal 0 1) =ᵐ[gaussianReal c 1]
      fun x => c * x - c ^ 2 / 2 := by
    filter_upwards [hrn'] with x hx
    rw [llr, hx, ENNReal.toReal_ofReal (Real.exp_nonneg _), Real.log_exp]
  have hidint : Integrable (fun x : ℝ => x) (gaussianReal c 1) :=
    IsGaussian.integrable_id (μ := gaussianReal c 1)
  have hint : Integrable (llr (gaussianReal c 1) (gaussianReal 0 1)) (gaussianReal c 1) :=
    Integrable.congr ((hidint.const_mul c).sub (integrable_const _)) hllr.symm
  have hval : ∫ a, (c * a - c ^ 2 / 2) ∂(gaussianReal c 1) = c ^ 2 / 2 := by
    rw [integral_sub (hidint.const_mul c) (integrable_const _), integral_const_mul,
      integral_id_gaussianReal]
    simp
    ring
  rw [klDiv_of_ac_of_integrable hac hint, integral_congr_ae hllr, hval]
  simp

/-! ## Multivariate Gaussian shift divergence -/

section Multivariate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Shifting the standard Gaussian by a vector costs exactly half its squared norm. -/
theorem klDiv_stdGaussian_shift (m : E) :
    klDiv ((stdGaussian E).map (fun x => x + m)) (stdGaussian E)
      = ENNReal.ofReal (‖m‖ ^ 2 / 2) := by
  classical
  set n := Module.finrank ℝ E with hn
  set b := stdOrthonormalBasis ℝ E with hb
  set c : Fin n → ℝ := fun i => (b.repr m).ofLp i with hc
  set P : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => gaussianReal 0 1 with hP
  set e : (Fin n → ℝ) ≃L[ℝ] E :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.trans
      b.repr.symm.toContinuousLinearEquiv with he
  have hcoe : ∀ x : Fin n → ℝ, e x = ∑ i, x i • b i := by
    intro x
    have h1 : e x = b.repr.symm (WithLp.toLp 2 x) := rfl
    rw [h1, ← b.sum_repr_symm]
  have hem : e c = m := by
    have h1 : e c = b.repr.symm (WithLp.toLp 2 c) := rfl
    rw [h1]
    have : (WithLp.toLp 2 c : EuclideanSpace ℝ (Fin n)) = b.repr m := rfl
    rw [this, LinearIsometryEquiv.symm_apply_apply]
  have hemb : MeasurableEmbedding (e : (Fin n → ℝ) → E) :=
    e.toHomeomorph.measurableEmbedding
  have hstd : stdGaussian E = P.map e := by
    rw [stdGaussian, hP]
    congr 1
    funext x
    exact (hcoe x).symm
  have hshift : (stdGaussian E).map (fun x => x + m)
      = (P.map (fun x => x + c)).map e := by
    rw [hstd, Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop)
      (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp_apply]
    rw [map_add, hem]
  have hpi : P.map (fun x => x + c) = Measure.pi fun i => gaussianReal (c i) 1 := by
    rw [hP]
    have hfun : (fun (x : Fin n → ℝ) => x + c) = fun (x : Fin n → ℝ) i => x i + c i := rfl
    rw [hfun, Measure.pi_map_pi (fun i => (measurable_add_const (c i)).aemeasurable)]
    congr 1
    funext i
    simpa using gaussianReal_map_add_const (μ := 0) (v := 1) (c i)
  rw [hshift, hstd, klDiv_map_measurableEmbedding hemb, hpi, klDiv_pi]
  have hterm : ∀ i : Fin n, klDiv (gaussianReal (c i) 1) (gaussianReal 0 1)
      = ENNReal.ofReal (c i ^ 2 / 2) := fun i => klDiv_gaussianReal_shift (c i)
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  congr 1
  have hnorm : ∑ i, c i ^ 2 = ‖m‖ ^ 2 := by
    have hiso : ‖b.repr m‖ = ‖m‖ := b.repr.norm_map m
    rw [← hiso, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]; exact (sq_abs _).symm
  rw [← hnorm, Finset.sum_div]

/-! ## Data processing for Markov kernels -/

/-- **Randomized data processing.**  A Markov kernel cannot increase relative entropy. -/
theorem klDiv_comp_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty α] [Nonempty β] [MeasurableEq β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ klDiv μ ν := by
  have h1 : κ ∘ₘ μ = (μ ⊗ₘ κ).map Prod.snd := by
    rw [← Measure.snd, Measure.snd_compProd]
  have h2 : κ ∘ₘ ν = (ν ⊗ₘ κ).map Prod.snd := by
    rw [← Measure.snd, Measure.snd_compProd]
  rw [h1, h2]
  calc klDiv ((μ ⊗ₘ κ).map Prod.snd) ((ν ⊗ₘ κ).map Prod.snd)
      ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) := klDiv_map_le _ _ measurable_snd
    _ = klDiv μ ν := klDiv_compProd_left μ ν κ

/-! ## The Gaussian shift experiment -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `(CDS.14)`  A Gaussian formation: a Markov kernel carrying the one-dimensional Gaussian shift
experiment of capital `b` onto the Gaussian genesis packet with signal `m`. -/
structure GaussianFormation (b : ℝ) (m : E) where
  kernel : Kernel ℝ E
  markov : IsMarkovKernel kernel
  forms_zero : kernel ∘ₘ gaussianReal 0 1 = stdGaussian E
  forms_one : kernel ∘ₘ gaussianReal (Real.sqrt b) 1
    = (stdGaussian E).map (fun x => x + m)

/-- **`(CDS.15)` necessity.**  A Gaussian formation forces the signal energy below the source
capital. -/
theorem GaussianFormation.norm_sq_le {b : ℝ} (hb : 0 ≤ b) {m : E} (F : GaussianFormation b m) :
    ‖m‖ ^ 2 ≤ b := by
  haveI := F.markov
  have hdp := klDiv_comp_le (gaussianReal (Real.sqrt b) 1) (gaussianReal 0 1) F.kernel
  rw [F.forms_one, F.forms_zero, klDiv_stdGaussian_shift,
    klDiv_gaussianReal_shift (Real.sqrt b), Real.sq_sqrt hb] at hdp
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hdp
  linarith

/-! ## Characteristic functions of formed laws -/

/-- The characteristic function of a formed law is the source average of the fibre characteristic
functions. -/
theorem charFun_comp {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α E) [IsMarkovKernel κ] (t : E) :
    charFun (κ ∘ₘ μ) t = ∫ x, charFun (κ x) t ∂μ := by
  have hsnd : κ ∘ₘ μ = (μ ⊗ₘ κ).map Prod.snd := by
    rw [← Measure.snd, Measure.snd_compProd]
  have hmeas : AEStronglyMeasurable (fun y : E => Complex.exp (⟪y, t⟫ * Complex.I))
      (κ ∘ₘ μ) := by
    fun_prop
  rw [charFun_apply, hsnd, integral_map measurable_snd.aemeasurable (by fun_prop)]
  rw [MeasureTheory.Measure.integral_compProd]
  · rfl
  · refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) ?_
    filter_upwards with p
    simp [Complex.norm_exp, mul_comm]

/-! ## The Gaussian garbling kernel -/

/-- Noise-shaping operator of the Gaussian garbling: the identity on the orthogonal complement of
the signal, contracted by `√(1 - ‖m‖²/b)` along the signal. -/
def garblingOp (b : ℝ) (m : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E -
    ((1 - Real.sqrt (1 - ‖m‖ ^ 2 / b)) / ‖m‖ ^ 2) • ((innerSL ℝ m).smulRight m)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem garblingOp_apply (b : ℝ) (m z : E) :
    garblingOp b m z
      = z - (((1 - Real.sqrt (1 - ‖m‖ ^ 2 / b)) / ‖m‖ ^ 2) * ⟪m, z⟫) • m := by
  simp [garblingOp, ContinuousLinearMap.smulRight_apply, smul_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inner_garblingOp (b : ℝ) (m z t : E) :
    ⟪garblingOp b m z, t⟫ = ⟪z, garblingOp b m t⟫ := by
  rw [garblingOp_apply, garblingOp_apply, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm z m]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_sq_garblingOp {b : ℝ} (hb : 0 < b) {m : E} (hm : ‖m‖ ^ 2 ≤ b) (t : E) :
    ‖garblingOp b m t‖ ^ 2 = ‖t‖ ^ 2 - ⟪m, t⟫ ^ 2 / b := by
  have hQ : (0:ℝ) ≤ ‖m‖ ^ 2 := sq_nonneg _
  set Q := ‖m‖ ^ 2 with hQdef
  set s := Real.sqrt (1 - Q / b) with hs
  set k := (1 - s) / Q with hk
  have hexp : ‖garblingOp b m t‖ ^ 2
      = ‖t‖ ^ 2 - 2 * ((k * ⟪m, t⟫) * ⟪m, t⟫) + (k * ⟪m, t⟫) ^ 2 * Q := by
    rw [garblingOp_apply, ← hk, @norm_sub_sq_real, real_inner_smul_right, norm_smul]
    rw [real_inner_comm t m]
    rw [mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hexp]
  rcases eq_or_lt_of_le hQ with hQ0 | hQ0
  · have hm0 : m = 0 := by
      refine norm_eq_zero.mp ?_
      nlinarith [norm_nonneg m, hQ0]
    subst hm0
    simp
  · have hsq : s ^ 2 = 1 - Q / b :=
      Real.sq_sqrt (by rw [sub_nonneg, div_le_one hb]; exact hm)
    have hkQ : k * Q = 1 - s := by rw [hk, div_mul_cancel₀ _ (ne_of_gt hQ0)]
    have hkey : 2 * k - k ^ 2 * Q = 1 / b := by
      have h1 : k ^ 2 * Q = k * (k * Q) := by ring
      rw [h1, hkQ]
      have h2 : k * (1 - s) = (1 - s) ^ 2 / Q := by rw [hk]; ring
      have h3 : 2 * k = 2 * (1 - s) / Q := by rw [hk]; ring
      rw [h2, h3, div_sub_div_same]
      have h4 : 2 * (1 - s) - (1 - s) ^ 2 = 1 - s ^ 2 := by ring
      rw [h4, hsq]
      field_simp
      ring
    have hfinal : ‖t‖ ^ 2 - 2 * ((k * ⟪m, t⟫) * ⟪m, t⟫) + (k * ⟪m, t⟫) ^ 2 * Q
        = ‖t‖ ^ 2 - (2 * k - k ^ 2 * Q) * ⟪m, t⟫ ^ 2 := by ring
    rw [hfinal, hkey]
    ring
/-- `(CDS.14)`  The Gaussian garbling kernel: scale the source observation onto the signal
direction and add the shaped independent Gaussian noise. -/
def gaussianGarbling (b : ℝ) (m : E) : Kernel ℝ E :=
  Kernel.map
    (Kernel.deterministic (fun x : ℝ => (x / Real.sqrt b) • m) (by fun_prop) ×ₖ
      Kernel.const ℝ ((stdGaussian E).map (garblingOp b m)))
    (fun p => p.1 + p.2)

instance isMarkovKernel_gaussianGarbling (b : ℝ) (m : E) :
    IsMarkovKernel (gaussianGarbling b m) := by
  unfold gaussianGarbling
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem gaussianGarbling_apply (b : ℝ) (m : E) (x : ℝ) :
    gaussianGarbling b m x
      = ((stdGaussian E).map (garblingOp b m)).map (fun z => (x / Real.sqrt b) • m + z) := by
  rw [gaussianGarbling, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem charFun_map_garblingOp (b : ℝ) (m t : E) :
    charFun ((stdGaussian E).map (garblingOp b m)) t
      = Complex.exp (-(‖garblingOp b m t‖ : ℂ) ^ 2 / 2) := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_garblingOp b m]
  rw [← charFun_apply, charFun_stdGaussian]

theorem charFun_map_add_right (μ : Measure E) (a t : E) :
    charFun (μ.map (fun z => z + a)) t
      = Complex.exp ((⟪a, t⟫ : ℝ) * Complex.I) * charFun μ t := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), charFun_apply]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show Complex.exp ((⟪z + a, t⟫ : ℝ) * Complex.I)
      = Complex.exp ((⟪a, t⟫ : ℝ) * Complex.I) * Complex.exp ((⟪z, t⟫ : ℝ) * Complex.I)
  rw [inner_add_left]
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

theorem charFun_gaussianGarbling (b : ℝ) (m : E) (x : ℝ) (t : E) :
    charFun (gaussianGarbling b m x) t
      = Complex.exp (((x / Real.sqrt b) * ⟪m, t⟫ : ℝ) * Complex.I)
        * Complex.exp (-(‖garblingOp b m t‖ : ℂ) ^ 2 / 2) := by
  have hcomm : (fun z : E => (x / Real.sqrt b) • m + z)
      = fun z : E => z + (x / Real.sqrt b) • m := by
    funext z; exact add_comm _ _
  rw [gaussianGarbling_apply, hcomm, charFun_map_add_right, charFun_map_garblingOp]
  congr 2
  rw [real_inner_smul_left]

/-- **`(CDS.15)` sufficiency.**  Below the capital wall the Gaussian garbling forms the whole
Gaussian shift family. -/
theorem gaussianGarbling_comp {b : ℝ} (hb : 0 < b) {m : E} (hm : ‖m‖ ^ 2 ≤ b) (c : ℝ) :
    gaussianGarbling b m ∘ₘ gaussianReal c 1
      = (stdGaussian E).map (fun y => y + (c / Real.sqrt b) • m) := by
  have hsb : (0:ℝ) < Real.sqrt b := Real.sqrt_pos.mpr hb
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_comp, charFun_map_add_right, charFun_stdGaussian]
  have hfib : ∀ x : ℝ, charFun (gaussianGarbling b m x) t
      = Complex.exp (((x / Real.sqrt b) * ⟪m, t⟫ : ℝ) * Complex.I)
        * Complex.exp (-(‖garblingOp b m t‖ : ℂ) ^ 2 / 2) :=
    fun x => charFun_gaussianGarbling b m x t
  simp_rw [hfib]
  rw [integral_mul_const]
  have hchar : ∫ x : ℝ, Complex.exp (((x / Real.sqrt b) * ⟪m, t⟫ : ℝ) * Complex.I)
      ∂(gaussianReal c 1)
      = charFun (gaussianReal c 1) (⟪m, t⟫ / Real.sqrt b) := by
    rw [charFun_apply_real]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    push_cast
    ring_nf
  rw [hchar, charFun_gaussianReal, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hA : (‖garblingOp b m t‖ : ℝ) ^ 2 = ‖t‖ ^ 2 - ⟪m, t⟫ ^ 2 / b :=
    norm_sq_garblingOp hb hm t
  have hA' : (‖garblingOp b m t‖ : ℂ) ^ 2
      = (‖t‖ : ℂ) ^ 2 - (⟪m, t⟫ : ℂ) ^ 2 / (b : ℂ) := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hA
    push_cast at h
    exact h
  have hbne : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hsbne : ((Real.sqrt b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsb.ne'
  have hsq : ((Real.sqrt b : ℝ) : ℂ) ^ 2 = (b : ℂ) := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) (Real.sq_sqrt hb.le)
    push_cast at h
    exact h
  rw [real_inner_smul_left, hA']
  push_cast
  field_simp
  rw [← hsq]
  ring

/-- **`(CDS.15)`.**  A Gaussian formation of signal `m` out of capital `b` exists exactly when the
signal energy is below the capital. -/
theorem nonempty_gaussianFormation_iff {b : ℝ} (hb : 0 < b) (m : E) :
    Nonempty (GaussianFormation b m) ↔ ‖m‖ ^ 2 ≤ b := by
  constructor
  · rintro ⟨F⟩
    exact F.norm_sq_le hb.le
  · intro hm
    have hsb : (0:ℝ) < Real.sqrt b := Real.sqrt_pos.mpr hb
    refine ⟨⟨gaussianGarbling b m, isMarkovKernel_gaussianGarbling b m, ?_, ?_⟩⟩
    · rw [gaussianGarbling_comp hb hm]
      simp
    · rw [gaussianGarbling_comp hb hm, div_self hsb.ne', one_smul]


end Multivariate



/-! ## Independent packet formation and the exact rate region -/

section ProductPacket

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Independent `d`-fold formation.**  The standard Gaussian on the `ℓ²` power is exactly the
`d`-fold independent product of the standard Gaussian. -/
theorem stdGaussian_piLp (d : ℕ) :
    stdGaussian (PiLp 2 fun _ : Fin d => F)
      = (Measure.pi fun _ : Fin d => stdGaussian F).map (WithLp.toLp 2) := by
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_stdGaussian, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hinner : ∀ x : Fin d → F,
      (⟪(WithLp.toLp 2 x : PiLp 2 fun _ : Fin d => F), t⟫ : ℝ) = ∑ i, ⟪x i, t i⟫ := by
    intro x
    rw [PiLp.inner_apply]
  simp_rw [hinner, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod
    (f := fun (i : Fin d) (y : F) => Complex.exp ((⟪y, t i⟫ : ℝ) * Complex.I))]
  have hfac : ∀ i : Fin d, ∫ y, Complex.exp ((⟪y, t i⟫ : ℝ) * Complex.I) ∂(stdGaussian F)
      = Complex.exp (-(‖t i‖ : ℂ) ^ 2 / 2) := by
    intro i
    rw [← charFun_apply, charFun_stdGaussian]
  simp_rw [hfac, ← Complex.exp_sum]
  congr 1
  have hn : (‖t‖ : ℝ) ^ 2 = ∑ i, ‖t.ofLp i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ t
  have hnC : (‖t‖ : ℂ) ^ 2 = ∑ i, ((‖t.ofLp i‖ : ℂ)) ^ 2 := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hn
    push_cast at h
    exact h
  rw [hnC, ← Finset.sum_neg_distrib, Finset.sum_div]

/-- **Independent `d`-fold formation of the shifted packet.** -/
theorem stdGaussian_piLp_shift (d : ℕ) (g : F) :
    (stdGaussian (PiLp 2 fun _ : Fin d => F)).map
        (fun y => y + (WithLp.toLp 2 fun _ : Fin d => g : PiLp 2 fun _ : Fin d => F))
      = (Measure.pi fun _ : Fin d => (stdGaussian F).map (fun y => y + g)).map (WithLp.toLp 2) := by
  rw [stdGaussian_piLp d, Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.pi_map_pi (fun _ : Fin d => (measurable_add_const g).aemeasurable),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- Total signal energy of the `d`-fold concatenated packet. -/
theorem norm_sq_packetPow (d : ℕ) (g : F) :
    ‖(WithLp.toLp 2 fun _ : Fin d => g : PiLp 2 fun _ : Fin d => F)‖ ^ 2 = d * ‖g‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Finset.sum_const]

/-- **Theorem 3.1, `(CDS.15)`.**  Exact rate classification: the source of capital `b` forms `d`
independent copies of the Gaussian genesis packet with signal `g` exactly when `d‖g‖² ≤ b`. -/
theorem nonempty_gaussianFormation_packetPow_iff {b : ℝ} (hb : 0 < b) (d : ℕ) (g : F) :
    Nonempty (GaussianFormation b
        (WithLp.toLp 2 fun _ : Fin d => g : PiLp 2 fun _ : Fin d => F))
      ↔ (d : ℝ) * ‖g‖ ^ 2 ≤ b := by
  rw [nonempty_gaussianFormation_iff hb, norm_sq_packetPow]

/-- `(CDS.15)` density form. -/
theorem nonempty_gaussianFormation_packetPow_iff_le_density {b : ℝ} (hb : 0 < b) {d : ℕ}
    (hd : 0 < d) (g : F) :
    Nonempty (GaussianFormation b
        (WithLp.toLp 2 fun _ : Fin d => g : PiLp 2 fun _ : Fin d => F))
      ↔ ‖g‖ ^ 2 ≤ b / d := by
  rw [nonempty_gaussianFormation_packetPow_iff hb, le_div_iff₀ (by exact_mod_cast hd), mul_comm]

end ProductPacket

/-! ## Vanishing density and the equalizer gap -/

/-- **`(CDS.17)`.**  Vanishing capital density forces vanishing formed signal energy. -/
theorem tendsto_signal_of_tendsto_density {Q ρ : ℕ → ℝ} (hQ : ∀ n, 0 ≤ Q n)
    (hle : ∀ n, Q n ≤ ρ n) (hρ : Filter.Tendsto ρ Filter.atTop (nhds 0)) :
    Filter.Tendsto Q Filter.atTop (nhds 0) :=
  squeeze_zero hQ hle hρ

/-- **`(CDS.19)`.**  A quantitative equalizer gap converts the rate region into a displacement
bound. -/
theorem displacement_le_of_gap {lam Q v b d : ℝ} (hlam : 0 < lam) (hd : 0 < d)
    (hv : 0 ≤ v) (hgap : lam * v ^ 2 ≤ Q) (hrate : d * Q ≤ b) :
    v ≤ Real.sqrt (b / (lam * d)) := by
  have hQ : lam * v ^ 2 ≤ b / d := by
    rw [le_div_iff₀ hd, mul_comm]
    exact le_trans (by nlinarith) hrate
  have hv2 : v ^ 2 ≤ b / (lam * d) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc v = Real.sqrt (v ^ 2) := (Real.sqrt_sq hv).symm
    _ ≤ Real.sqrt (b / (lam * d)) := Real.sqrt_le_sqrt hv2

end

end GaloisForLFunctions.HTGeometry
