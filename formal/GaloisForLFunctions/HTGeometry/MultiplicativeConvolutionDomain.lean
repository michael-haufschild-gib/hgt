import GaloisForLFunctions.HTGeometry.ComplexMeasurePairing
import GaloisForLFunctions.HTGeometry.CompactDeterminacy

/-!
# The multiplicative convolution algebra of finite complex measures on `(0, 1]`

On `[0, 1]` the multiplicative convolution `μ ⊠ ν` is the push-forward of `μ ⊗ ν` under
`(x, y) ↦ xy`; it extends bilinearly to finite complex measures through their Jordan parts.

* The moment map `c ↦ (∫ xⁿ dc)_{n ≥ 0}` is injective (Hausdorff determinacy) and multiplicative,
  so `(M([0,1]), +, ⊠)` is a commutative ring.
* **Lemma 5.1**: the finite complex measures carried by `(0, 1]` form a subring without zero
  divisors.  The Mellin transform `z ↦ ∫ x^z dc` is holomorphic on `Re z > 0` and multiplicative;
  holomorphic functions on the connected half-plane have no zero divisors; the transform at the
  integers `z = n ≥ 1` determines a measure carried by `(0, 1]`.
* **Lemma 5.2**: over an integral domain, `∏ (T + aᵢ) = ∏ (T + bᵢ)` forces `{aᵢ} = {bᵢ}`.

The point `0` is absorbing for `⊠`, so on all of `[0, 1]` the ring has zero divisors
(`δ₀ ⊠ (δ₁ - δ_{1/2}) = 0`); removing it is necessary.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal NNReal unitInterval

noncomputable section

namespace GaloisForLFunctions.HTGeometry.MeasureConvolution

/-! ### Multiplicative convolution of finite measures on `[0, 1]` -/

instance (μ ν : Measure I) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (μ ∗ₘ ν) := by
  unfold Measure.mconv; infer_instance

/-- A test function is multiplicative on `[0, 1]`. -/
def IsMultiplicative (g : I → ℂ) : Prop := ∀ x y, g (x * y) = g x * g y

theorem integral_mconv {g : I → ℂ} (hg : IsTest g) (hmul : IsMultiplicative g) (μ ν : Measure I)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, g x ∂(μ ∗ₘ ν) = (∫ x, g x ∂μ) * ∫ x, g x ∂ν := by
  rw [Measure.mconv, integral_map measurable_mul.aemeasurable hg.measurable.aestronglyMeasurable]
  calc ∫ p : I × I, g (p.1 * p.2) ∂(μ.prod ν) = ∫ p : I × I, g p.1 * g p.2 ∂(μ.prod ν) :=
        integral_congr_ae (ae_of_all _ fun p => hmul p.1 p.2)
    _ = _ := integral_prod_mul g g

/-- **Multiplicative convolution** of finite complex measures on `[0, 1]`, bilinear in the Jordan
parts. -/
def conv (c d : ComplexMeasure I) : ComplexMeasure I :=
  ∑ p : Fin 4 × Fin 4, (jordanWeight p.1 * jordanWeight p.2) •
    ofMeasure (jordanPart c p.1 ∗ₘ jordanPart d p.2)

theorem pair_conv (c d : ComplexMeasure I) {g : I → ℂ} (hg : IsTest g)
    (hmul : IsMultiplicative g) : pair (conv c d) g = pair c g * pair d g := by
  rw [conv, pair_sum_smul_ofMeasure _ _ _ hg, pair, pair, Finset.sum_mul_sum,
    ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [integral_mconv hg hmul]
  ring

/-! ### The moment map -/

/-- The moment test function `x ↦ xⁿ`. -/
def powTest (n : ℕ) (x : I) : ℂ := ((x : ℝ) : ℂ) ^ n

theorem isTest_powTest (n : ℕ) : IsTest (powTest n) := by
  refine ⟨(Complex.continuous_ofReal.comp continuous_subtype_val).pow n |>.measurable, 1,
    fun x => ?_⟩
  rw [powTest, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg x.2.1]
  exact pow_le_one₀ x.2.1 x.2.2

theorem isMultiplicative_powTest (n : ℕ) : IsMultiplicative (powTest n) := fun x y => by
  simp only [powTest, Set.Icc.coe_mul, Complex.ofReal_mul, mul_pow]

/-- The moment sequence `n ↦ ∫ xⁿ dc`. -/
def momentSeq (c : ComplexMeasure I) (n : ℕ) : ℂ := pair c (powTest n)

theorem integral_powTest (μ : Measure I) (n : ℕ) :
    ∫ x, powTest n x ∂μ = ((∫ x, (x : ℝ) ^ n ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  simp only [powTest, Complex.ofReal_pow]

/-- **Hausdorff determinacy on `[0, 1]`**: finite measures with the same moments are equal. -/
theorem measure_eq_of_moments_eq (μ ν : Measure I) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ℕ, ∫ x, (x : ℝ) ^ n ∂μ = ∫ x, (x : ℝ) ^ n ∂ν) : μ = ν := by
  have hemb : MeasurableEmbedding (Subtype.val : I → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hcarry : ∀ ρ : Measure I, (ρ.map Subtype.val) (Icc (0 : ℝ) 1)ᶜ = 0 := fun ρ => by
    rw [hemb.map_apply]
    have : (Subtype.val : I → ℝ) ⁻¹' (Icc (0 : ℝ) 1)ᶜ = ∅ := by
      ext x; simp
    rw [this, measure_empty]
  have hint : ∀ (ρ : Measure I) [IsFiniteMeasure ρ] (k : ℕ),
      Integrable (fun x : ℝ => x ^ k) (ρ.map Subtype.val) := fun ρ _ k => by
    rw [hemb.integrable_map_iff]
    refine (integrable_const (1 : ℝ)).mono' ((continuous_subtype_val.pow k).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    simp only [Function.comp_apply, norm_pow, Real.norm_eq_abs, abs_of_nonneg x.2.1]
    exact pow_le_one₀ x.2.1 x.2.2
  have hmap := HTGeometry.measure_eq_of_moments_eq_of_carried (s := fun k => ∫ x, (x : ℝ) ^ k ∂μ)
    (hcarry μ) (hcarry ν) (fun k => by rw [hemb.integral_map]) (hint μ)
    (fun k => by rw [hemb.integral_map, h]) (hint ν)
  rw [← hemb.comap_map μ, ← hemb.comap_map ν, hmap]

theorem ofReal_integral_jordan_eq (c : ComplexMeasure I) (n : ℕ) (h : momentSeq c n = 0) :
    ∫ x, (x : ℝ) ^ n ∂jordanPart c 0 = ∫ x, (x : ℝ) ^ n ∂jordanPart c 1 ∧
      ∫ x, (x : ℝ) ^ n ∂jordanPart c 2 = ∫ x, (x : ℝ) ^ n ∂jordanPart c 3 := by
  rw [momentSeq, pair_eq, integral_powTest, integral_powTest, integral_powTest,
    integral_powTest] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.ofReal_im, zero_mul, one_mul, Complex.zero_re,
    Complex.add_im, Complex.mul_im, Complex.zero_im, add_zero, zero_add, sub_self] at hre him
  constructor <;> linarith

/-- The moment map is injective. -/
theorem momentSeq_injective : Function.Injective (momentSeq : ComplexMeasure I → ℕ → ℂ) := by
  intro c d h
  have h0 : ∀ n, momentSeq (c - d) n = 0 := fun n => by
    rw [momentSeq, pair_sub _ _ (isTest_powTest n), ← momentSeq, ← momentSeq, h, sub_self]
  have hre : jordanPart (c - d) 0 = jordanPart (c - d) 1 :=
    measure_eq_of_moments_eq _ _ fun n => (ofReal_integral_jordan_eq _ n (h0 n)).1
  have him : jordanPart (c - d) 2 = jordanPart (c - d) 3 :=
    measure_eq_of_moments_eq _ _ fun n => (ofReal_integral_jordan_eq _ n (h0 n)).2
  have hzero : c - d = 0 := by
    apply ComplexMeasure.equivSignedMeasure.injective
    refine Prod.ext ?_ ?_
    · change ComplexMeasure.re (c - d) = ComplexMeasure.re 0
      simp only [re_eq_jordan, hre, sub_self, map_zero]
    · change ComplexMeasure.im (c - d) = ComplexMeasure.im 0
      simp only [im_eq_jordan, him, sub_self, map_zero]
  exact sub_eq_zero.1 hzero

/-! ### The convolution ring -/

/-- Finite complex measures on `[0, 1]` with multiplicative convolution. -/
def ConvMeasure : Type := ComplexMeasure I

instance : AddCommGroup ConvMeasure := inferInstanceAs (AddCommGroup (ComplexMeasure I))

instance : Mul ConvMeasure := ⟨conv⟩

instance : One ConvMeasure := ⟨ofMeasure (Measure.dirac 1)⟩

instance : Pow ConvMeasure ℕ := ⟨fun c n => npowRec n c⟩

instance : NatCast ConvMeasure := ⟨fun n => n • (1 : ConvMeasure)⟩

instance : IntCast ConvMeasure := ⟨fun n => n • (1 : ConvMeasure)⟩

/-- The underlying complex measure. -/
def ConvMeasure.toMeasure (c : ConvMeasure) : ComplexMeasure I := c

/-- A complex measure as an element of the convolution ring. -/
def ConvMeasure.ofComplexMeasure (c : ComplexMeasure I) : ConvMeasure := c

theorem momentSeq_one : momentSeq (1 : ConvMeasure) = 1 := by
  funext n
  change pair (ofMeasure (Measure.dirac (1 : I))) (powTest n) = 1
  rw [pair_ofMeasure _ (isTest_powTest n), integral_dirac]
  simp [powTest]

theorem momentSeq_mul (c d : ConvMeasure) :
    momentSeq (c * d) = momentSeq c * momentSeq d := by
  funext n
  exact pair_conv c d (isTest_powTest n) (isMultiplicative_powTest n)

theorem momentSeq_npow (c : ConvMeasure) (n : ℕ) : momentSeq (c ^ n) = momentSeq c ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact momentSeq_one
  | succ n ih =>
    change momentSeq (npowRec n c * c) = _
    rw [momentSeq_mul, pow_succ]
    change momentSeq (c ^ n) * _ = _
    rw [ih]

instance : CommRing ConvMeasure :=
  Function.Injective.commRing (momentSeq : ConvMeasure → ℕ → ℂ) momentSeq_injective
    (funext fun n => pair_zero (isTest_powTest n)) momentSeq_one
    (fun c d => funext fun n => pair_add c d (isTest_powTest n)) momentSeq_mul
    (fun c => funext fun n => pair_neg c (isTest_powTest n))
    (fun c d => funext fun n => pair_sub c d (isTest_powTest n))
    (fun k c => funext fun n => by
      rw [Pi.smul_apply]; exact pair_nsmul k c (isTest_powTest n))
    (fun k c => funext fun n => by
      rw [Pi.smul_apply]; exact pair_zsmul k c (isTest_powTest n))
    momentSeq_npow
    (fun k => funext fun n => by
      change pair (k • ofMeasure (Measure.dirac (1 : I))) (powTest n) = (k : ℕ → ℂ) n
      rw [pair_nsmul _ _ (isTest_powTest n), pair_ofMeasure _ (isTest_powTest n), integral_dirac]
      simp [powTest])
    (fun k => funext fun n => by
      change pair (k • ofMeasure (Measure.dirac (1 : I))) (powTest n) = (k : ℕ → ℂ) n
      rw [pair_zsmul _ _ (isTest_powTest n), pair_ofMeasure _ (isTest_powTest n), integral_dirac]
      simp [powTest])

end GaloisForLFunctions.HTGeometry.MeasureConvolution
