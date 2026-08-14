import GaloisForLFunctions.RHTower.FieldOneFiniteStageBruhatHalfDensityL2
import GaloisForLFunctions.RHTower.FieldOneFiniteStageMultiplicativeHaarFromAdditive
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Connes--Marcolli finite-stage correlation formula

This file formalizes the analytic content of Connes--Marcolli Lemma 2.32.
Bruhat--Schwartz tensors are realized on the literal additive adele carrier,
the scaling representation is the source action `f(a) ↦ f(γ⁻¹a)`, and all
integrability and interchange statements are proved from termwise-absolute
orbit estimates.
-/

open scoped NNReal ENNReal TensorProduct algebraMap ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

open Function IsDedekindDomain MeasureTheory MeasureTheory.Measure Set

/-- Realization of one finite-stage Bruhat pure tensor on the additive adeles. -/
def fieldOneFiniteStageBruhatEvalBilinear
    (S : Finset (HeightOneSpectrum ℤ)) :
    SchwartzMap ℝ ℂ →ₗ[ℂ]
      FieldOneFiniteStageFiniteBruhatSchwartz S →ₗ[ℂ]
        (FieldOneFiniteStageAdele S → ℂ) :=
  LinearMap.mk₂ ℂ (fun f phi a => f a.1 * phi.1 a.2)
    (fun f g phi => by funext a; simp [add_mul])
    (fun c f phi => by funext a; simp [mul_assoc])
    (fun f phi psi => by funext a; simp [mul_add])
    (fun c f phi => by
      funext a
      simp only [Pi.smul_apply, smul_eq_mul]
      change f a.1 * (c * phi.1 a.2) = c * (f a.1 * phi.1 a.2)
      ring)

/-- Literal realization of the algebraic finite-stage Bruhat--Schwartz core. -/
def fieldOneFiniteStageBruhatEval
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageBruhatSchwartz S →ₗ[ℂ]
      (FieldOneFiniteStageAdele S → ℂ) :=
  TensorProduct.lift (fieldOneFiniteStageBruhatEvalBilinear S)

@[simp]
theorem fieldOneFiniteStageBruhatEval_tmul
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (a : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageBruhatEval S (f ⊗ₜ[ℂ] phi) a =
      f a.1 * phi.1 a.2 :=
  rfl

theorem fieldOneFiniteStageBruhatEval_continuous
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    Continuous (fieldOneFiniteStageBruhatEval S x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      change Continuous (fun _ : FieldOneFiniteStageAdele S => (0 : ℂ))
      exact continuous_const
  | tmul f phi =>
      change Continuous (fun a : FieldOneFiniteStageAdele S =>
        f a.1 * phi.1 a.2)
      exact (f.continuous.comp continuous_fst).mul
        (phi.1.continuous.comp continuous_snd)
  | add x y hx hy =>
      convert hx.add hy using 1 <;>
        funext a <;> simp [fieldOneFiniteStageBruhatEval]

theorem fieldOneFiniteStageBruhatEval_val
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageBruhatEval S x (fieldOneFiniteStageIdeleVal S u) =
      fieldOneFiniteStageBruhatOrbit S x u 1 := by
  induction x using TensorProduct.induction_on with
  | zero => simp [fieldOneFiniteStageBruhatEval, fieldOneFiniteStageBruhatOrbit]
  | tmul f phi =>
      change f ((u.1 : ℝ)) * phi.1 (fun v =>
        (u.2 v : v.1.adicCompletion ℚ)) = _
      simp [fieldOneFiniteStageBruhatOrbit_tmul,
        fieldOneFiniteStageBruhatPureTensorOrbit]
  | add x y hx hy =>
      simpa [fieldOneFiniteStageBruhatEval, fieldOneFiniteStageBruhatOrbit] using
        congrArg₂ (· + ·) hx hy

/-- Exact identification of the abstract diagonal image with literal rational
`S`-units. -/
def fieldOneFiniteStageSUnitImageEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneSUnitSubgroup S ≃ fieldOneFiniteStageSUnitImage S :=
  Equiv.ofBijective
    (fun q => ⟨fieldOneFiniteStageDiagonalUnit S q.1,
      fieldOneFiniteStageDiagonalUnit_mem_sUnitImage S q⟩)
    ⟨fun q r h => by
        apply Subtype.ext
        exact fieldOneFiniteStageDiagonalUnit_injective S (Subtype.ext_iff.mp h),
      fun h => by
        have hh := h.2
        change h.1 ∈ Subgroup.map
          (fieldOneFiniteStageDiagonalUnit S) (fieldOneSUnitSubgroup S) at hh
        rw [Subgroup.mem_map] at hh
        obtain ⟨q, hq, hqh⟩ := hh
        exact ⟨⟨q, hq⟩, Subtype.ext hqh⟩⟩

@[simp]
theorem fieldOneFiniteStageSUnitImageEquiv_val
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S) :
    (fieldOneFiniteStageSUnitImageEquiv S q : FieldOneFiniteStageIdele S) =
      fieldOneFiniteStageDiagonalUnit S q.1 :=
  rfl

private theorem fieldOneFiniteStageFiniteBruhat_norm_sq_integrable
    (S : Finset (HeightOneSpectrum ℤ))
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    Integrable (fun y : FieldOneFiniteStageFinitePart S => ‖phi.1 y‖ ^ 2)
      (Measure.pi fun v : ↥S =>
        (addHaar : Measure (v.1.adicCompletion ℚ))) := by
  have hnorm : HasCompactSupport (fun y : FieldOneFiniteStageFinitePart S => ‖phi.1 y‖) := by
    change HasCompactSupport ((fun z : ℂ => ‖z‖) ∘ phi.1)
    exact phi.2.comp_left (g := fun z : ℂ => ‖z‖) norm_zero
  have hsupport : HasCompactSupport
      (fun y : FieldOneFiniteStageFinitePart S => ‖phi.1 y‖ ^ 2) := by
    have hm : HasCompactSupport
        ((fun y : FieldOneFiniteStageFinitePart S => ‖phi.1 y‖) *
          fun y => ‖phi.1 y‖) :=
      hnorm.mul_right
    rw [show (fun y : FieldOneFiniteStageFinitePart S => ‖phi.1 y‖ ^ 2) =
        ((fun y : FieldOneFiniteStageFinitePart S => ‖phi.1 y‖) *
          fun y => ‖phi.1 y‖) by
      funext y
      simp [pow_two]]
    exact hm
  exact (phi.1.continuous.norm.pow 2).integrable_of_hasCompactSupport hsupport

/-- Every literal finite-stage Bruhat--Schwartz function belongs to additive
`L²(A_S)`. -/
theorem fieldOneFiniteStageBruhatEval_memLp_two
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    MemLp (fieldOneFiniteStageBruhatEval S x) 2
      (fieldOneFiniteStageProductAddHaar S) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [fieldOneFiniteStageBruhatEval]
  | tmul f phi =>
      rw [memLp_two_iff_integrable_sq_norm
        (fieldOneFiniteStageBruhatEval_continuous S (f ⊗ₜ[ℂ] phi)).aestronglyMeasurable]
      have hf : Integrable (fun r : ℝ => ‖f r‖ ^ 2) (addHaar : Measure ℝ) :=
        (f.memLp 2 (addHaar : Measure ℝ)).integrable_norm_pow (by norm_num)
      have hphi := fieldOneFiniteStageFiniteBruhat_norm_sq_integrable S phi
      simpa [fieldOneFiniteStageProductAddHaar, norm_mul, mul_pow] using
        Integrable.mul_prod hf hphi
  | add x y hx hy =>
      have hxy := hx.add hy
      exact (memLp_congr_ae (Filter.Eventually.of_forall fun a => by
        simp [fieldOneFiniteStageBruhatEval])).2 hxy

/-- Source scaling action `(ϑ_a(γ)f)(a) = f(γ⁻¹a)`. -/
def fieldOneFiniteStageBruhatThetaEval
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (a : FieldOneFiniteStageAdele S) : ℂ :=
  fieldOneFiniteStageBruhatEval S x
    ((fieldOneFiniteStageDiagonalUnit S gamma.1)⁻¹ • a)

theorem fieldOneFiniteStageBruhatThetaEval_continuous
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    Continuous (fieldOneFiniteStageBruhatThetaEval S gamma x) := by
  exact (fieldOneFiniteStageBruhatEval_continuous S x).comp
    (continuous_const_smul _)

theorem fieldOneFiniteStageBruhatThetaEval_val
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageBruhatThetaEval S gamma x
        (fieldOneFiniteStageIdeleVal S u) =
      fieldOneFiniteStageBruhatOrbit S x u gamma⁻¹ := by
  rw [fieldOneFiniteStageBruhatThetaEval]
  have hval :
      (fieldOneFiniteStageDiagonalUnit S gamma.1)⁻¹ •
          fieldOneFiniteStageIdeleVal S u =
        fieldOneFiniteStageIdeleVal S
          ((fieldOneFiniteStageDiagonalUnit S gamma.1)⁻¹ * u) := by
    apply Prod.ext
    · rfl
    · funext v
      rfl
  rw [hval, fieldOneFiniteStageBruhatEval_val]
  simpa using fieldOneFiniteStageBruhatOrbit_diagonal_mul S x u gamma⁻¹ 1

private noncomputable instance fieldOneFiniteStageSUnitImage_smulInvariantProductAddHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    SMulInvariantMeasure (fieldOneFiniteStageSUnitImage S)
      (FieldOneFiniteStageAdele S) (fieldOneFiniteStageProductAddHaar S) where
  measure_preimage_smul h s hs := by
    rw [preimage_smul]
    exact fieldOneFiniteStageSUnitImage_measure_smul S h⁻¹
      (fieldOneFiniteStageProductAddHaar S) s

theorem fieldOneFiniteStageBruhatThetaEval_memLp_two
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    MemLp (fieldOneFiniteStageBruhatThetaEval S gamma x) 2
      (fieldOneFiniteStageProductAddHaar S) := by
  let h : fieldOneFiniteStageSUnitImage S :=
    ⟨fieldOneFiniteStageDiagonalUnit S gamma.1,
      fieldOneFiniteStageDiagonalUnit_mem_sUnitImage S gamma⟩
  have hx := (fieldOneFiniteStageBruhatEval_memLp_two S x).comp_measurePreserving
    (measurePreserving_smul h⁻¹ (fieldOneFiniteStageProductAddHaar S))
  change MemLp (fun a : FieldOneFiniteStageAdele S =>
    fieldOneFiniteStageBruhatEval S x
      ((fieldOneFiniteStageDiagonalUnit S gamma.1)⁻¹ • a)) 2
    (fieldOneFiniteStageProductAddHaar S) at hx
  exact hx

/-- Each source correlation integrand is genuinely Bochner integrable. -/
theorem fieldOneFiniteStageBruhatAdditiveCorrelation_integrable
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (gamma : fieldOneSUnitSubgroup S) :
    Integrable (fun a : FieldOneFiniteStageAdele S =>
      star (fieldOneFiniteStageBruhatEval S x a) *
        fieldOneFiniteStageBruhatThetaEval S gamma y a)
      (fieldOneFiniteStageProductAddHaar S) := by
  have hx : MemLp (fun a : FieldOneFiniteStageAdele S =>
      star (fieldOneFiniteStageBruhatEval S x a)) 2
      (fieldOneFiniteStageProductAddHaar S) := by
    change MemLp (star (fieldOneFiniteStageBruhatEval S x)) 2
      (fieldOneFiniteStageProductAddHaar S)
    exact (fieldOneFiniteStageBruhatEval_memLp_two S x).star
  exact hx.integrable_mul
    (fieldOneFiniteStageBruhatThetaEval_memLp_two S gamma y)

/-- Source half-density written directly on the canonical split idele
representative. -/
def fieldOneFiniteStageBruhatSplitHalfDensityDirect
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) : ℂ :=
  (Real.sqrt (fieldOneFiniteStageModule S
      (fieldOneFiniteStageIdeleFundamentalSection S z)) : ℂ) *
    fieldOneFiniteStageBruhatPeriodization S x
      (fieldOneFiniteStageIdeleFundamentalSection S z)

/-- Termwise-absolute half-density written directly on the canonical split
idele representative. -/
def fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) : ℝ :=
  Real.sqrt (fieldOneFiniteStageModule S
      (fieldOneFiniteStageIdeleFundamentalSection S z)) *
    ∑' q : fieldOneSUnitSubgroup S,
      ‖fieldOneFiniteStageBruhatOrbit S x
        (fieldOneFiniteStageIdeleFundamentalSection S z) q‖

private theorem fieldOnePositiveUnitsExpHomeomorph_symm_apply
    (r : ℝ≥0ˣ) :
    Real.exp (fieldOnePositiveUnitsExpHomeomorph.symm r) = r.1 := by
  have h := congrArg Units.val
    (fieldOnePositiveUnitsExpHomeomorph.apply_symm_apply r)
  exact congrArg Subtype.val h

theorem fieldOneFiniteStageBruhatSplitHalfDensityDirect_eq
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatSplitHalfDensityDirect S x =
      fieldOneFiniteStageBruhatSplitHalfDensity S x := by
  funext z
  let t := fieldOnePositiveUnitsExpHomeomorph.symm z.2
  let k := fieldOneFiniteStageAngularTorusRepresentative S z.1
  have hsection : fieldOneFiniteStageIdeleFundamentalSection S z =
      fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t := by
    rw [fieldOneFiniteStageIdeleFundamentalSection]
    apply Prod.ext
    · apply Units.ext
      change (1 : ℝ) * (z.2.1 : ℝ) = Real.exp t
      rw [one_mul]
      exact (fieldOnePositiveUnitsExpHomeomorph_symm_apply z.2).symm
    · funext v
      apply Units.ext
      change (k v).1.1 * 1 = (k v).1.1
      simp
  have hmodule : fieldOneFiniteStageModule S
      (fieldOneFiniteStageIdeleFundamentalSection S z) = z.2.1 := by
    rw [hsection]
    change ‖Real.exp t‖₊ * ∏ v : ↥S,
      ‖((k v).1 : v.1.adicCompletion ℚ)‖₊ = z.2.1
    have hlocal : ∏ v : ↥S,
        ‖((k v).1 : v.1.adicCompletion ℚ)‖₊ = 1 := by
      apply Finset.prod_eq_one
      intro v _
      apply NNReal.eq
      exact (k v).2
    rw [hlocal, mul_one]
    apply NNReal.eq
    change ‖Real.exp t‖ = (z.2.1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
    exact fieldOnePositiveUnitsExpHomeomorph_symm_apply z.2
  rw [fieldOneFiniteStageBruhatSplitHalfDensityDirect,
    fieldOneFiniteStageBruhatSplitHalfDensity,
    fieldOneFiniteStageBruhatLogHalfDensity,
    fieldOneFiniteStageBruhatLogPeriodization, hmodule, hsection]
  have hsqrt : Real.sqrt (z.2.1 : ℝ) = Real.exp (t / 2) := by
    rw [← fieldOnePositiveUnitsExpHomeomorph_symm_apply z.2,
      Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 2
    norm_num
  rw [hsqrt]

theorem fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect_eq
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect S x =
      fieldOneFiniteStageBruhatSplitAbsoluteHalfDensity S x := by
  funext z
  let t := fieldOnePositiveUnitsExpHomeomorph.symm z.2
  let k := fieldOneFiniteStageAngularTorusRepresentative S z.1
  have hsection : fieldOneFiniteStageIdeleFundamentalSection S z =
      fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t := by
    rw [fieldOneFiniteStageIdeleFundamentalSection]
    apply Prod.ext
    · apply Units.ext
      change (1 : ℝ) * (z.2.1 : ℝ) = Real.exp t
      rw [one_mul]
      exact (fieldOnePositiveUnitsExpHomeomorph_symm_apply z.2).symm
    · funext v
      apply Units.ext
      change (k v).1.1 * 1 = (k v).1.1
      simp
  have hmodule : fieldOneFiniteStageModule S
      (fieldOneFiniteStageIdeleFundamentalSection S z) = z.2.1 := by
    rw [hsection]
    change ‖Real.exp t‖₊ * ∏ v : ↥S,
      ‖((k v).1 : v.1.adicCompletion ℚ)‖₊ = z.2.1
    have hlocal : ∏ v : ↥S,
        ‖((k v).1 : v.1.adicCompletion ℚ)‖₊ = 1 := by
      apply Finset.prod_eq_one
      intro v _
      apply NNReal.eq
      exact (k v).2
    rw [hlocal, mul_one]
    apply NNReal.eq
    change ‖Real.exp t‖ = (z.2.1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
    exact fieldOnePositiveUnitsExpHomeomorph_symm_apply z.2
  rw [fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect,
    fieldOneFiniteStageBruhatSplitAbsoluteHalfDensity,
    fieldOneFiniteStageBruhatLogAbsoluteHalfDensity,
    fieldOneFiniteStageBruhatLogAbsolutePeriodization, hmodule, hsection]
  have hsqrt : Real.sqrt (z.2.1 : ℝ) = Real.exp (t / 2) := by
    rw [← fieldOnePositiveUnitsExpHomeomorph_symm_apply z.2,
      Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 2
    norm_num
  rw [hsqrt]

theorem fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect_memLp
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    MemLp (fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect S x) 2
      (fieldOneFiniteStageSplitProductHaarMeasure S) := by
  rw [fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect_eq]
  exact fieldOneFiniteStageBruhatSplitAbsoluteHalfDensity_memLp S x

/-- Exact pointwise collapse of the two lattice sums produced by quotient
unfolding.  The inner reindexing is `γ ↦ γ⁻¹r`; no conditional rearrangement
is used. -/
theorem fieldOneFiniteStageBruhatOrbit_norm_double_tsum
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) :
    (∑' h : fieldOneFiniteStageSUnitImage S,
      ∑' gamma : fieldOneSUnitSubgroup S,
        ‖fieldOneFiniteStageBruhatOrbit S x
          (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) 1‖ *
        ‖fieldOneFiniteStageBruhatOrbit S y
          (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) gamma⁻¹‖) =
      (∑' r : fieldOneSUnitSubgroup S,
        ‖fieldOneFiniteStageBruhatOrbit S x
          (fieldOneFiniteStageIdeleFundamentalSection S z) r‖) *
      ∑' s : fieldOneSUnitSubgroup S,
        ‖fieldOneFiniteStageBruhatOrbit S y
          (fieldOneFiniteStageIdeleFundamentalSection S z) s‖ := by
  let u := fieldOneFiniteStageIdeleFundamentalSection S z
  let A : fieldOneSUnitSubgroup S → ℝ := fun r =>
    ‖fieldOneFiniteStageBruhatOrbit S x u r‖
  let B : fieldOneSUnitSubgroup S → ℝ := fun s =>
    ‖fieldOneFiniteStageBruhatOrbit S y u s‖
  have hA : Summable A := fieldOneFiniteStageBruhatOrbit_summable S x u
  have hB : Summable B := fieldOneFiniteStageBruhatOrbit_summable S y u
  rw [← (fieldOneFiniteStageSUnitImageEquiv S).tsum_eq]
  change (∑' r : fieldOneSUnitSubgroup S,
    ∑' gamma : fieldOneSUnitSubgroup S,
      ‖fieldOneFiniteStageBruhatOrbit S x
        (fieldOneFiniteStageDiagonalUnit S r.1 * u) 1‖ *
      ‖fieldOneFiniteStageBruhatOrbit S y
        (fieldOneFiniteStageDiagonalUnit S r.1 * u) gamma⁻¹‖) = _
  simp_rw [fieldOneFiniteStageBruhatOrbit_diagonal_mul]
  simp only [one_mul]
  change (∑' r, ∑' gamma, A r * B (gamma⁻¹ * r)) =
    (∑' r, A r) * ∑' s, B s
  have hinner (r : fieldOneSUnitSubgroup S) :
      (∑' gamma, A r * B (gamma⁻¹ * r)) =
        A r * ∑' s, B s := by
    calc
      (∑' gamma, A r * B (gamma⁻¹ * r)) =
          A r * ∑' gamma, B (gamma⁻¹ * r) := tsum_mul_left
      _ = A r * ∑' s, B s := by
        congr 1
        simpa [div_eq_mul_inv, mul_comm] using
          (Equiv.divLeft r).tsum_eq B
  simp_rw [hinner]
  exact hA.tsum_mul_right (∑' s, B s)

/-- Phase-sensitive counterpart of the absolute double-sum collapse.  Every
reindexing is backed by the `ℓ1` orbit theorem, so this is not a conditional
rearrangement. -/
theorem fieldOneFiniteStageBruhatOrbit_complex_double_tsum
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) :
    (∑' h : fieldOneFiniteStageSUnitImage S,
      ∑' gamma : fieldOneSUnitSubgroup S,
        (fieldOneFiniteStageModule S
          (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) : ℂ) *
          (star (fieldOneFiniteStageBruhatOrbit S x
            (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) 1) *
          fieldOneFiniteStageBruhatOrbit S y
            (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) gamma⁻¹)) =
      star (fieldOneFiniteStageBruhatSplitHalfDensityDirect S x z) *
        fieldOneFiniteStageBruhatSplitHalfDensityDirect S y z := by
  let u := fieldOneFiniteStageIdeleFundamentalSection S z
  let A : fieldOneSUnitSubgroup S → ℂ := fun r =>
    fieldOneFiniteStageBruhatOrbit S x u r
  let B : fieldOneSUnitSubgroup S → ℂ := fun s =>
    fieldOneFiniteStageBruhatOrbit S y u s
  let m : ℝ≥0 := fieldOneFiniteStageModule S u
  have hA : Summable A := summable_norm_iff.mp
    (fieldOneFiniteStageBruhatOrbit_summable S x u)
  have hB : Summable B := summable_norm_iff.mp
    (fieldOneFiniteStageBruhatOrbit_summable S y u)
  have hmodule (r : fieldOneSUnitSubgroup S) :
      fieldOneFiniteStageModule S
          (fieldOneFiniteStageDiagonalUnit S r.1 * u) = m := by
    rw [map_mul]
    have hr := fieldOneSUnitSubgroup_le_moduleKernel S r.2
    change fieldOneFiniteStageModule S
      (fieldOneFiniteStageDiagonalUnit S r.1) = 1 at hr
    rw [hr, one_mul]
  have hinner (r : fieldOneSUnitSubgroup S) :
      (∑' gamma : fieldOneSUnitSubgroup S,
        (m : ℂ) * (star (A r) * B (gamma⁻¹ * r))) =
        (m : ℂ) * (star (A r) * ∑' s, B s) := by
    calc
      (∑' gamma : fieldOneSUnitSubgroup S,
          (m : ℂ) * (star (A r) * B (gamma⁻¹ * r))) =
          (m : ℂ) * ∑' gamma : fieldOneSUnitSubgroup S,
            star (A r) * B (gamma⁻¹ * r) := tsum_mul_left
      _ = (m : ℂ) * (star (A r) *
          ∑' gamma : fieldOneSUnitSubgroup S, B (gamma⁻¹ * r)) := by
        rw [tsum_mul_left]
      _ = (m : ℂ) * (star (A r) * ∑' s, B s) := by
        congr 2
        simpa [div_eq_mul_inv, mul_comm] using
          (Equiv.divLeft r).tsum_eq B
  rw [← (fieldOneFiniteStageSUnitImageEquiv S).tsum_eq]
  change (∑' r : fieldOneSUnitSubgroup S,
    ∑' gamma : fieldOneSUnitSubgroup S,
      (fieldOneFiniteStageModule S
        (fieldOneFiniteStageDiagonalUnit S r.1 * u) : ℂ) *
        (star (fieldOneFiniteStageBruhatOrbit S x
          (fieldOneFiniteStageDiagonalUnit S r.1 * u) 1) *
        fieldOneFiniteStageBruhatOrbit S y
          (fieldOneFiniteStageDiagonalUnit S r.1 * u) gamma⁻¹)) = _
  simp_rw [fieldOneFiniteStageBruhatOrbit_diagonal_mul, one_mul, hmodule]
  change (∑' r : fieldOneSUnitSubgroup S,
    ∑' gamma : fieldOneSUnitSubgroup S,
      (m : ℂ) * (star (A r) * B (gamma⁻¹ * r))) = _
  simp_rw [hinner]
  calc
    (∑' r : fieldOneSUnitSubgroup S,
        (m : ℂ) * (star (A r) * ∑' s, B s)) =
        (m : ℂ) * ∑' r : fieldOneSUnitSubgroup S,
          star (A r) * ∑' s, B s := tsum_mul_left
    _ = (m : ℂ) *
        ((∑' r : fieldOneSUnitSubgroup S, star (A r)) * ∑' s, B s) := by
      rw [tsum_mul_right]
    _ = (m : ℂ) * (star (∑' r, A r) * ∑' s, B s) := by
      rw [tsum_star]
    _ = star (fieldOneFiniteStageBruhatSplitHalfDensityDirect S x z) *
        fieldOneFiniteStageBruhatSplitHalfDensityDirect S y z := by
      rw [fieldOneFiniteStageBruhatSplitHalfDensityDirect,
        fieldOneFiniteStageBruhatSplitHalfDensityDirect]
      change (m : ℂ) * (star (∑' r, A r) * ∑' s, B s) =
        star ((Real.sqrt (m : ℝ) : ℂ) * ∑' r, A r) *
          ((Real.sqrt (m : ℝ) : ℂ) * ∑' s, B s)
      rw [star_mul]
      have hsqrtC :
          (Real.sqrt (m : ℝ) : ℂ) * (Real.sqrt (m : ℝ) : ℂ) =
            (m : ℂ) := by
        have hreal : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) =
            (m : ℝ) := by
          simpa [pow_two] using Real.sq_sqrt m.2
        calc
          (Real.sqrt (m : ℝ) : ℂ) * (Real.sqrt (m : ℝ) : ℂ) =
              ((Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) : ℝ) : ℂ) :=
            (Complex.ofReal_mul _ _).symm
          _ = ((m : ℝ) : ℂ) := congrArg (fun r : ℝ => (r : ℂ)) hreal
          _ = (m : ℂ) := rfl
      have hstarSqrt : star (Real.sqrt (m : ℝ) : ℂ) =
          (Real.sqrt (m : ℝ) : ℂ) := by
        exact Complex.conj_ofReal _
      rw [hstarSqrt]
      rw [← hsqrtC]
      ring

/-- Sum of termwise absolute additive correlation integrands. -/
def fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (a : FieldOneFiniteStageAdele S) : ℝ≥0∞ :=
  ∑' gamma : fieldOneSUnitSubgroup S,
    ENNReal.ofReal
      (‖fieldOneFiniteStageBruhatEval S x a‖ *
        ‖fieldOneFiniteStageBruhatThetaEval S gamma y a‖)

theorem fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand_measurable
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    Measurable (fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand S x y) := by
  letI : Countable ℚˣ := Units.val_injective.countable
  letI : Countable (fieldOneSUnitSubgroup S) := Subtype.countable
  apply Measurable.tsum
  intro gamma
  exact ENNReal.measurable_ofReal.comp
    ((fieldOneFiniteStageBruhatEval_continuous S x).norm.measurable.mul
      (fieldOneFiniteStageBruhatThetaEval_continuous S gamma y).norm.measurable)

/-- Total termwise-absolute correlation mass on additive adeles. -/
def fieldOneFiniteStageBruhatAbsoluteCorrelationMass
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) : ℝ≥0∞ :=
  ∫⁻ a, fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand S x y a
    ∂fieldOneFiniteStageProductAddHaar S

private theorem fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand_val
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand S x y
        (fieldOneFiniteStageIdeleVal S u) =
      ∑' gamma : fieldOneSUnitSubgroup S,
        ENNReal.ofReal ‖fieldOneFiniteStageBruhatOrbit S x u 1‖ *
          ENNReal.ofReal ‖fieldOneFiniteStageBruhatOrbit S y u gamma⁻¹‖ := by
  rw [fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand]
  apply tsum_congr
  intro gamma
  rw [fieldOneFiniteStageBruhatEval_val,
    fieldOneFiniteStageBruhatThetaEval_val,
    ENNReal.ofReal_mul (norm_nonneg _)]

private theorem fieldOneFiniteStageBruhatAbsolute_fundamental_sum
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) :
    (∑' h : fieldOneFiniteStageSUnitImage S,
      (fieldOneFiniteStageModule S
          (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) : ℝ≥0∞) *
        fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand S x y
          (fieldOneFiniteStageIdeleVal S
            (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z))) =
      ENNReal.ofReal
        (fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect S x z *
          fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect S y z) := by
  let u := fieldOneFiniteStageIdeleFundamentalSection S z
  let A : fieldOneSUnitSubgroup S → ℝ := fun r =>
    ‖fieldOneFiniteStageBruhatOrbit S x u r‖
  let B : fieldOneSUnitSubgroup S → ℝ := fun s =>
    ‖fieldOneFiniteStageBruhatOrbit S y u s‖
  let m : ℝ≥0 := fieldOneFiniteStageModule S u
  have hA : Summable A := fieldOneFiniteStageBruhatOrbit_summable S x u
  have hB : Summable B := fieldOneFiniteStageBruhatOrbit_summable S y u
  have hA0 : ∀ r, 0 ≤ A r := fun _ => norm_nonneg _
  have hB0 : ∀ s, 0 ≤ B s := fun _ => norm_nonneg _
  have hBsum0 : 0 ≤ ∑' s, B s := tsum_nonneg hB0
  have hmodule (r : fieldOneSUnitSubgroup S) :
      fieldOneFiniteStageModule S
          (fieldOneFiniteStageDiagonalUnit S r.1 * u) = m := by
    rw [map_mul]
    have hr := fieldOneSUnitSubgroup_le_moduleKernel S r.2
    change fieldOneFiniteStageModule S
      (fieldOneFiniteStageDiagonalUnit S r.1) = 1 at hr
    rw [hr, one_mul]
  have hinner (r : fieldOneSUnitSubgroup S) :
      (∑' gamma : fieldOneSUnitSubgroup S,
        ENNReal.ofReal (A r) * ENNReal.ofReal (B (gamma⁻¹ * r))) =
        ENNReal.ofReal (A r * ∑' s, B s) := by
    rw [ENNReal.tsum_mul_left]
    have hreindex := (Equiv.divLeft r).tsum_eq
      (fun s : fieldOneSUnitSubgroup S => ENNReal.ofReal (B s))
    have hreindex' :
        (∑' gamma : fieldOneSUnitSubgroup S,
          ENNReal.ofReal (B (gamma⁻¹ * r))) =
          ∑' s : fieldOneSUnitSubgroup S, ENNReal.ofReal (B s) := by
      simpa [div_eq_mul_inv, mul_comm] using hreindex
    rw [hreindex', ← ENNReal.ofReal_tsum_of_nonneg hB0 hB,
      ← ENNReal.ofReal_mul (hA0 r)]
  rw [← (fieldOneFiniteStageSUnitImageEquiv S).tsum_eq]
  change (∑' r : fieldOneSUnitSubgroup S,
      (fieldOneFiniteStageModule S
          (fieldOneFiniteStageDiagonalUnit S r.1 * u) : ℝ≥0∞) *
        fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand S x y
          (fieldOneFiniteStageIdeleVal S
            (fieldOneFiniteStageDiagonalUnit S r.1 * u))) = _
  simp_rw [fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand_val,
    fieldOneFiniteStageBruhatOrbit_diagonal_mul, one_mul]
  change (∑' r : fieldOneSUnitSubgroup S,
    (fieldOneFiniteStageModule S
      (fieldOneFiniteStageDiagonalUnit S r.1 * u) : ℝ≥0∞) *
      ∑' gamma : fieldOneSUnitSubgroup S,
        ENNReal.ofReal (A r) * ENNReal.ofReal (B (gamma⁻¹ * r))) = _
  simp_rw [hmodule, hinner]
  have houter : Summable
      (fun r : fieldOneSUnitSubgroup S => (m : ℝ) * (A r * ∑' s, B s)) :=
    (hA.mul_right (∑' s, B s)).mul_left (m : ℝ)
  have houter0 : ∀ r : fieldOneSUnitSubgroup S,
      0 ≤ (m : ℝ) * (A r * ∑' s, B s) := fun r =>
    mul_nonneg m.2 (mul_nonneg (hA0 r) hBsum0)
  calc
    (∑' r : fieldOneSUnitSubgroup S,
        (m : ℝ≥0∞) * ENNReal.ofReal (A r * ∑' s, B s)) =
        ∑' r : fieldOneSUnitSubgroup S,
          ENNReal.ofReal ((m : ℝ) * (A r * ∑' s, B s)) := by
      apply tsum_congr
      intro r
      symm
      calc
        ENNReal.ofReal ((m : ℝ) * (A r * ∑' s, B s)) =
            ENNReal.ofReal (m : ℝ) *
              ENNReal.ofReal (A r * ∑' s, B s) :=
          ENNReal.ofReal_mul m.2
        _ = (m : ℝ≥0∞) * ENNReal.ofReal (A r * ∑' s, B s) := by
          have hmcoe : ENNReal.ofReal (m : ℝ) = (m : ℝ≥0∞) :=
            (ENNReal.coe_nnreal_eq m).symm
          rw [hmcoe]
    _ = ENNReal.ofReal
        (∑' r : fieldOneSUnitSubgroup S,
          (m : ℝ) * (A r * ∑' s, B s)) :=
      (ENNReal.ofReal_tsum_of_nonneg houter0 houter).symm
    _ = ENNReal.ofReal ((m : ℝ) * ((∑' r, A r) * ∑' s, B s)) := by
      congr 1
      rw [tsum_mul_left, hA.tsum_mul_right]
    _ = ENNReal.ofReal
        (fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect S x z *
          fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect S y z) := by
      congr 1
      rw [fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect,
        fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect]
      change (m : ℝ) * ((∑' r, A r) * ∑' s, B s) =
        (Real.sqrt (m : ℝ) * ∑' r, A r) *
          (Real.sqrt (m : ℝ) * ∑' s, B s)
      calc
        (m : ℝ) * ((∑' r, A r) * ∑' s, B s) =
            Real.sqrt (m : ℝ) ^ 2 * ((∑' r, A r) * ∑' s, B s) := by
          exact congrArg
            (fun q : ℝ => q * ((∑' r, A r) * ∑' s, B s))
            (Real.sq_sqrt m.2).symm
        _ = (Real.sqrt (m : ℝ) * ∑' r, A r) *
            (Real.sqrt (m : ℝ) * ∑' s, B s) := by ring

/-- Exact Tonelli/unfolding identity for total absolute correlation mass.
The only scalar is the explicit Haar-normalization factor already present in
Connes--Marcolli's phrase “up to a fixed normalization constant”. -/
theorem fieldOneFiniteStageBruhatAbsoluteCorrelationMass_eq
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatAbsoluteCorrelationMass S x y =
      (haarScalarFactor
          (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S)
          (fieldOneFiniteStageIdeleFundamentalHaarMeasure S) : ℝ≥0∞) *
        ∫⁻ z,
          ENNReal.ofReal
            (fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect S x z *
              fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect S y z)
          ∂fieldOneFiniteStageSplitProductHaarMeasure S := by
  let H := fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand S x y
  have hH : Measurable H :=
    fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand_measurable S x y
  let G : FieldOneFiniteStageIdele S → ℝ≥0∞ := fun u =>
    H (fieldOneFiniteStageIdeleVal S u)
  have hG : Measurable G :=
    hH.comp (fieldOneFiniteStageIdeleVal_continuous S).measurable
  let F : FieldOneFiniteStageIdele S → ℝ≥0∞ := fun u =>
    (fieldOneFiniteStageModule S u : ℝ≥0∞) * G u
  have hF : Measurable F :=
    (fieldOneFiniteStageModule_continuous S).measurable.coe_nnreal_ennreal.mul hG
  calc
    fieldOneFiniteStageBruhatAbsoluteCorrelationMass S x y =
        ∫⁻ u, G u ∂fieldOneFiniteStageIdeleAdditivePullbackMeasure S := by
      rw [fieldOneFiniteStageBruhatAbsoluteCorrelationMass]
      exact (fieldOneFiniteStageIdeleAdditivePullback_lintegral_comp_val
        S H hH).symm
    _ = ∫⁻ u, F u
        ∂fieldOneFiniteStageIdeleMultiplicativeFromAdditive S := by
      exact (fieldOneFiniteStageIdeleMultiplicative_lintegral_module_mul
        S G hG).symm
    _ = (haarScalarFactor
          (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S)
          (fieldOneFiniteStageIdeleFundamentalHaarMeasure S) : ℝ≥0∞) *
        ∫⁻ z,
          ∑' h : fieldOneFiniteStageSUnitImage S,
            F (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z)
          ∂fieldOneFiniteStageSplitProductHaarMeasure S :=
      fieldOneFiniteStageIdeleMultiplicative_lintegral_fundamental S F hF
    _ = (haarScalarFactor
          (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S)
          (fieldOneFiniteStageIdeleFundamentalHaarMeasure S) : ℝ≥0∞) *
        ∫⁻ z,
          ENNReal.ofReal
            (fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect S x z *
              fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect S y z)
          ∂fieldOneFiniteStageSplitProductHaarMeasure S := by
      congr 1
      apply lintegral_congr
      intro z
      change (∑' h : fieldOneFiniteStageSUnitImage S,
        (fieldOneFiniteStageModule S
            (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) : ℝ≥0∞) *
          fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand S x y
            (fieldOneFiniteStageIdeleVal S
              (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z))) = _
      exact fieldOneFiniteStageBruhatAbsolute_fundamental_sum S x y z

/-- Lemma 2.32's absolute-convergence estimate, before discarding phases:
the total Tonelli mass of all additive correlations is finite. -/
theorem fieldOneFiniteStageBruhatAbsoluteCorrelationMass_lt_top
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatAbsoluteCorrelationMass S x y < ⊤ := by
  rw [fieldOneFiniteStageBruhatAbsoluteCorrelationMass_eq]
  apply ENNReal.mul_lt_top ENNReal.coe_lt_top
  have hx :=
    fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect_memLp S x
  have hy :=
    fieldOneFiniteStageBruhatSplitAbsoluteHalfDensityDirect_memLp S y
  exact (hx.integrable_mul hy).lintegral_lt_top

/-- Additive `L²` correlation from equation (2.246). -/
def fieldOneFiniteStageBruhatAdditiveCorrelation
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (gamma : fieldOneSUnitSubgroup S) : ℂ :=
  ∫ a, star (fieldOneFiniteStageBruhatEval S x a) *
      fieldOneFiniteStageBruhatThetaEval S gamma y a
    ∂fieldOneFiniteStageProductAddHaar S

/-- Pointwise phase-sensitive sum of all source correlations. -/
def fieldOneFiniteStageBruhatCorrelationSeries
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (a : FieldOneFiniteStageAdele S) : ℂ :=
  ∑' gamma : fieldOneSUnitSubgroup S,
    star (fieldOneFiniteStageBruhatEval S x a) *
      fieldOneFiniteStageBruhatThetaEval S gamma y a

theorem fieldOneFiniteStageBruhatCorrelationSeries_measurable
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    Measurable (fieldOneFiniteStageBruhatCorrelationSeries S x y) := by
  letI : Countable ℚˣ := Units.val_injective.countable
  letI : Countable (fieldOneSUnitSubgroup S) := Subtype.countable
  apply Measurable.tsum
  intro gamma
  exact (fieldOneFiniteStageBruhatEval_continuous S x).star.mul
    (fieldOneFiniteStageBruhatThetaEval_continuous S gamma y) |>.measurable

/-- The phase-sensitive integrand after replacing additive Haar by
`|u| d*u` on the idele locus. -/
def fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) : ℂ :=
  (fieldOneFiniteStageModule S u : ℂ) *
    fieldOneFiniteStageBruhatCorrelationSeries S x y
      (fieldOneFiniteStageIdeleVal S u)

theorem fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand_measurable
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    Measurable
      (fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand S x y) := by
  exact (Complex.measurable_ofReal.comp
      (NNReal.continuous_coe.comp
        (fieldOneFiniteStageModule_continuous S)).measurable).mul
    ((fieldOneFiniteStageBruhatCorrelationSeries_measurable S x y).comp
      (fieldOneFiniteStageIdeleVal_continuous S).measurable)

private theorem fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand_enorm_le
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    ‖fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand S x y u‖ₑ ≤
      (fieldOneFiniteStageModule S u : ℝ≥0∞) *
        fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand S x y
          (fieldOneFiniteStageIdeleVal S u) := by
  rw [fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand,
    enorm_mul]
  have hmoduleEnorm : ‖(fieldOneFiniteStageModule S u : ℂ)‖ₑ =
      (fieldOneFiniteStageModule S u : ℝ≥0∞) := by
    rw [enorm_eq_nnnorm]
    congr 1
    apply NNReal.eq
    simp
  rw [hmoduleEnorm]
  apply mul_le_mul_right
  rw [fieldOneFiniteStageBruhatCorrelationSeries,
    fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand]
  refine (enorm_tsum_le_tsum_enorm).trans_eq ?_
  apply tsum_congr
  intro gamma
  simp [norm_mul]

/-- The full multiplicative correlation integrand is integrable; all Fubini
steps below therefore follow from a proved `L¹` bound. -/
theorem fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand_integrable
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    Integrable (fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand S x y)
      (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S) := by
  refine ⟨
    (fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand_measurable S x y).aestronglyMeasurable,
    ?_⟩
  have hmass :
      (∫⁻ u,
        (fieldOneFiniteStageModule S u : ℝ≥0∞) *
          fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand S x y
            (fieldOneFiniteStageIdeleVal S u)
        ∂fieldOneFiniteStageIdeleMultiplicativeFromAdditive S) =
        fieldOneFiniteStageBruhatAbsoluteCorrelationMass S x y := by
    calc
      (∫⁻ u,
          (fieldOneFiniteStageModule S u : ℝ≥0∞) *
            fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand S x y
              (fieldOneFiniteStageIdeleVal S u)
          ∂fieldOneFiniteStageIdeleMultiplicativeFromAdditive S) =
          ∫⁻ u, fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand S x y
              (fieldOneFiniteStageIdeleVal S u)
            ∂fieldOneFiniteStageIdeleAdditivePullbackMeasure S := by
        exact fieldOneFiniteStageIdeleMultiplicative_lintegral_module_mul S _
          ((fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand_measurable S x y).comp
            (fieldOneFiniteStageIdeleVal_continuous S).measurable)
      _ = ∫⁻ a, fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand S x y a
          ∂fieldOneFiniteStageProductAddHaar S :=
        fieldOneFiniteStageIdeleAdditivePullback_lintegral_comp_val S _
          (fieldOneFiniteStageBruhatAbsoluteCorrelationIntegrand_measurable S x y)
      _ = fieldOneFiniteStageBruhatAbsoluteCorrelationMass S x y := rfl
  exact lt_of_le_of_lt
    (lintegral_mono
      (fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand_enorm_le S x y))
    (by
      rw [hmass]
      exact fieldOneFiniteStageBruhatAbsoluteCorrelationMass_lt_top S x y)

/-- The sum of the `L¹` norms of all correlation integrands is finite.  This
is the literal absolute-convergence assertion used in Lemma 2.32's Fubini
step. -/
theorem fieldOneFiniteStageBruhatCorrelationIntegralNorm_summable
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    Summable (fun gamma : fieldOneSUnitSubgroup S =>
      ∫ a, ‖star (fieldOneFiniteStageBruhatEval S x a) *
          fieldOneFiniteStageBruhatThetaEval S gamma y a‖
        ∂fieldOneFiniteStageProductAddHaar S) := by
  letI : Countable ℚˣ := Units.val_injective.countable
  letI : Countable (fieldOneSUnitSubgroup S) := Subtype.countable
  let F : fieldOneSUnitSubgroup S → FieldOneFiniteStageAdele S → ℂ :=
    fun gamma a => star (fieldOneFiniteStageBruhatEval S x a) *
      fieldOneFiniteStageBruhatThetaEval S gamma y a
  have hFint (gamma : fieldOneSUnitSubgroup S) :
      Integrable (F gamma) (fieldOneFiniteStageProductAddHaar S) := by
    simpa [F] using
      fieldOneFiniteStageBruhatAdditiveCorrelation_integrable S x y gamma
  have hmass :
      (∑' gamma : fieldOneSUnitSubgroup S,
        ENNReal.ofReal
          (∫ a, ‖F gamma a‖ ∂fieldOneFiniteStageProductAddHaar S)) =
        fieldOneFiniteStageBruhatAbsoluteCorrelationMass S x y := by
    calc
      (∑' gamma : fieldOneSUnitSubgroup S,
          ENNReal.ofReal
            (∫ a, ‖F gamma a‖ ∂fieldOneFiniteStageProductAddHaar S)) =
          ∑' gamma : fieldOneSUnitSubgroup S,
            ∫⁻ a, ENNReal.ofReal ‖F gamma a‖
              ∂fieldOneFiniteStageProductAddHaar S := by
        apply tsum_congr
        intro gamma
        exact ofReal_integral_eq_lintegral_ofReal (hFint gamma).norm
          (MeasureTheory.ae_of_all _ fun _ => norm_nonneg _)
      _ = fieldOneFiniteStageBruhatAbsoluteCorrelationMass S x y := by
        rw [fieldOneFiniteStageBruhatAbsoluteCorrelationMass]
        change (∑' gamma : fieldOneSUnitSubgroup S,
            ∫⁻ a, ENNReal.ofReal ‖F gamma a‖
              ∂fieldOneFiniteStageProductAddHaar S) =
          ∫⁻ a, ∑' gamma : fieldOneSUnitSubgroup S,
            ENNReal.ofReal
              (‖fieldOneFiniteStageBruhatEval S x a‖ *
                ‖fieldOneFiniteStageBruhatThetaEval S gamma y a‖)
            ∂fieldOneFiniteStageProductAddHaar S
        rw [lintegral_tsum]
        · apply tsum_congr
          intro gamma
          apply lintegral_congr
          intro a
          simp [F, norm_mul]
        · intro gamma
          exact (ENNReal.measurable_ofReal.comp
            ((fieldOneFiniteStageBruhatEval_continuous S x).norm.measurable.mul
              (fieldOneFiniteStageBruhatThetaEval_continuous S gamma y).norm.measurable)).aemeasurable
  let I : fieldOneSUnitSubgroup S → ℝ≥0 := fun gamma =>
    ⟨∫ a, ‖F gamma a‖ ∂fieldOneFiniteStageProductAddHaar S,
      integral_nonneg fun _ => norm_nonneg _⟩
  have hIne : (∑' gamma : fieldOneSUnitSubgroup S, (I gamma : ℝ≥0∞)) ≠ ⊤ := by
    have hIeq : (∑' gamma : fieldOneSUnitSubgroup S, (I gamma : ℝ≥0∞)) =
        fieldOneFiniteStageBruhatAbsoluteCorrelationMass S x y := by
      calc
        (∑' gamma : fieldOneSUnitSubgroup S, (I gamma : ℝ≥0∞)) =
            ∑' gamma : fieldOneSUnitSubgroup S,
              ENNReal.ofReal
                (∫ a, ‖F gamma a‖ ∂fieldOneFiniteStageProductAddHaar S) := by
          apply tsum_congr
          intro gamma
          change (I gamma : ℝ≥0∞) = ENNReal.ofReal (I gamma : ℝ)
          exact ENNReal.coe_nnreal_eq (I gamma)
        _ = fieldOneFiniteStageBruhatAbsoluteCorrelationMass S x y := hmass
    rw [hIeq]
    exact (fieldOneFiniteStageBruhatAbsoluteCorrelationMass_lt_top S x y).ne
  have hInn : Summable I :=
    ENNReal.tsum_coe_ne_top_iff_summable.1 hIne
  have hIr : Summable (fun gamma => (I gamma : ℝ)) :=
    NNReal.summable_coe.2 hInn
  change Summable (fun gamma =>
    ∫ a, ‖F gamma a‖ ∂fieldOneFiniteStageProductAddHaar S) at hIr
  exact hIr

/-- The scalar correlation series in Lemma 2.32 is absolutely summable. -/
theorem fieldOneFiniteStageBruhatAdditiveCorrelation_norm_summable
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    Summable (fun gamma : fieldOneSUnitSubgroup S =>
      ‖fieldOneFiniteStageBruhatAdditiveCorrelation S x y gamma‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun gamma => norm_integral_le_integral_norm _)
  exact fieldOneFiniteStageBruhatCorrelationIntegralNorm_summable S x y

/-- Absolute convergence, in the standard normed-space form. -/
theorem fieldOneFiniteStageBruhatAdditiveCorrelation_summable
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    Summable (fieldOneFiniteStageBruhatAdditiveCorrelation S x y) :=
  (fieldOneFiniteStageBruhatAdditiveCorrelation_norm_summable S x y).of_norm_bounded
    (fun _ => le_rfl)

/-- The sum of the additive correlations is the integral of their pointwise
series; this is Lemma 2.32's first Fubini interchange. -/
theorem fieldOneFiniteStageBruhatAdditiveCorrelation_tsum_eq_integral_series
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    (∑' gamma : fieldOneSUnitSubgroup S,
      fieldOneFiniteStageBruhatAdditiveCorrelation S x y gamma) =
      ∫ a, fieldOneFiniteStageBruhatCorrelationSeries S x y a
        ∂fieldOneFiniteStageProductAddHaar S := by
  letI : Countable ℚˣ := Units.val_injective.countable
  letI : Countable (fieldOneSUnitSubgroup S) := Subtype.countable
  apply integral_tsum_of_summable_integral_norm
  · intro gamma
    exact fieldOneFiniteStageBruhatAdditiveCorrelation_integrable S x y gamma
  · exact fieldOneFiniteStageBruhatCorrelationIntegralNorm_summable S x y

/-- Exact source inner product on the finite-stage idele-class quotient. -/
def fieldOneFiniteStageBruhatSourceInner
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) : ℂ :=
  ∫ z,
    star (fieldOneFiniteStageBruhatSplitHalfDensity S x z) *
      fieldOneFiniteStageBruhatSplitHalfDensity S y z
    ∂fieldOneFiniteStageSplitProductHaarMeasure S

/-- Source inner-product integrand is unconditionally integrable. -/
theorem fieldOneFiniteStageBruhatSourceInner_integrable
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    Integrable (fun z =>
      star (fieldOneFiniteStageBruhatSplitHalfDensity S x z) *
        fieldOneFiniteStageBruhatSplitHalfDensity S y z)
      (fieldOneFiniteStageSplitProductHaarMeasure S) :=
  (fieldOneFiniteStageBruhatSplitHalfDensity_memLp S x).star.integrable_mul
    (fieldOneFiniteStageBruhatSplitHalfDensity_memLp S y)

/-- Exact global change of variables `da = |u| d*u`, including the conull
idele-locus pullback. -/
theorem fieldOneFiniteStageBruhatCorrelation_integral_additive_eq_multiplicative
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    (∫ a, fieldOneFiniteStageBruhatCorrelationSeries S x y a
        ∂fieldOneFiniteStageProductAddHaar S) =
      ∫ u, fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand S x y u
        ∂fieldOneFiniteStageIdeleMultiplicativeFromAdditive S := by
  let H := fieldOneFiniteStageBruhatCorrelationSeries S x y
  have hmap := (fieldOneFiniteStageIdeleVal_isOpenEmbedding S).measurableEmbedding
    |>.integral_map
      (μ := fieldOneFiniteStageIdeleAdditivePullbackMeasure S) H
  rw [fieldOneFiniteStageIdeleAdditivePullbackMeasure,
    (fieldOneFiniteStageIdeleVal_isOpenEmbedding S).measurableEmbedding.map_comap,
    fieldOneFiniteStageIdeleVal_range,
    Measure.restrict_eq_self_of_ae_mem (fieldOneFiniteStageIdeleLocus_ae S)] at hmap
  have hcancel :
      (∫ u, fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand S x y u
          ∂fieldOneFiniteStageIdeleMultiplicativeFromAdditive S) =
        ∫ u, H (fieldOneFiniteStageIdeleVal S u)
          ∂fieldOneFiniteStageIdeleAdditivePullbackMeasure S := by
    rw [fieldOneFiniteStageIdeleMultiplicativeFromAdditive,
      integral_withDensity_eq_integral_toReal_smul
        (fieldOneFiniteStageIdeleModuleInvDensity_continuous S).measurable]
    · apply integral_congr_ae
      exact MeasureTheory.ae_of_all _ fun u => by
        let m : ℝ≥0 := fieldOneFiniteStageModule S u
        have hm : m ≠ 0 := fieldOneFiniteStageModule_ne_zero S u
        change (fieldOneFiniteStageIdeleModuleInvDensity S u).toReal •
          ((fieldOneFiniteStageModule S u : ℂ) *
            H (fieldOneFiniteStageIdeleVal S u)) =
          H (fieldOneFiniteStageIdeleVal S u)
        rw [fieldOneFiniteStageIdeleModuleInvDensity, ENNReal.coe_toReal]
        change ((m⁻¹ : ℝ≥0) : ℝ) •
            ((m : ℂ) * H (fieldOneFiniteStageIdeleVal S u)) =
          H (fieldOneFiniteStageIdeleVal S u)
        have hinner :
            (m : ℂ) *
                H (fieldOneFiniteStageIdeleVal S u) =
              (m : ℝ) •
                H (fieldOneFiniteStageIdeleVal S u) :=
          Complex.real_smul.symm
        rw [hinner, smul_smul]
        have hnn : m⁻¹ * m = 1 := inv_mul_cancel₀ hm
        have hcoef : ((m⁻¹ : ℝ≥0) : ℝ) * (m : ℝ) = 1 := by
          calc
            ((m⁻¹ : ℝ≥0) : ℝ) * (m : ℝ) =
                ((m⁻¹ * m : ℝ≥0) : ℝ) := (NNReal.coe_mul _ _).symm
            _ = ((1 : ℝ≥0) : ℝ) :=
              congrArg (fun r : ℝ≥0 => (r : ℝ)) hnn
            _ = 1 := rfl
        rw [hcoef, one_smul]
    · exact MeasureTheory.ae_of_all _ fun _ => ENNReal.coe_lt_top
  exact hmap.trans hcancel.symm

/-- Fundamental-domain unfolding of the phase-sensitive multiplicative
integral.  The result is exactly the source inner product, multiplied by the
positive Haar-normalization scalar. -/
theorem fieldOneFiniteStageBruhatCorrelation_integral_multiplicative_eq_sourceInner
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    (∫ u, fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand S x y u
        ∂fieldOneFiniteStageIdeleMultiplicativeFromAdditive S) =
      ((haarScalarFactor
        (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S)
        (fieldOneFiniteStageIdeleFundamentalHaarMeasure S) : ℝ) •
        fieldOneFiniteStageBruhatSourceInner S x y) := by
  let c : ℝ≥0 := haarScalarFactor
    (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S)
    (fieldOneFiniteStageIdeleFundamentalHaarMeasure S)
  let F := fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand S x y
  let e := (fieldOneFiniteStageIdeleImageFundamentalContinuousMulEquiv S).toHomeomorph.toMeasurableEquiv
  have hc : 0 < c := fieldOneFiniteStageIdeleMultiplicative_fundamentalScalar_pos S
  have hmeasure :
      fieldOneFiniteStageIdeleMultiplicativeFromAdditive S =
        (c : ℝ≥0∞) • fieldOneFiniteStageIdeleFundamentalHaarMeasure S := by
    simpa [c] using
      fieldOneFiniteStageIdeleMultiplicativeFromAdditive_eq_fundamentalHaar S
  have hFmul : Integrable F
      (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S) := by
    exact fieldOneFiniteStageBruhatMultiplicativeCorrelationIntegrand_integrable S x y
  have hFfund : Integrable F
      (fieldOneFiniteStageIdeleFundamentalHaarMeasure S) := by
    rw [hmeasure] at hFmul
    exact (integrable_smul_measure
      (ENNReal.coe_ne_zero.2 hc.ne') ENNReal.coe_ne_top).1 hFmul
  have hfundMap :
      fieldOneFiniteStageIdeleFundamentalHaarMeasure S =
        Measure.map e (fieldOneFiniteStageIdeleFundamentalProductMeasure S) := by
    rfl
  have hFprod : Integrable (F ∘ e)
      (fieldOneFiniteStageIdeleFundamentalProductMeasure S) := by
    rw [hfundMap] at hFfund
    exact (integrable_map_equiv e F).1 hFfund
  have hFprod' : Integrable (F ∘ e)
      ((count : Measure (fieldOneFiniteStageSUnitImage S)).prod
        (fieldOneFiniteStageSplitProductHaarMeasure S)) := by
    simpa [fieldOneFiniteStageIdeleFundamentalProductMeasure] using hFprod
  have hmapIntegral :
      (∫ u, F u ∂fieldOneFiniteStageIdeleFundamentalHaarMeasure S) =
        ∫ p, F (e p) ∂fieldOneFiniteStageIdeleFundamentalProductMeasure S := by
    rw [hfundMap]
    exact integral_map_equiv e F
  have hcountIntegral :
      (∫ p, F (e p) ∂fieldOneFiniteStageIdeleFundamentalProductMeasure S) =
        ∫ z,
          ∑' h : fieldOneFiniteStageSUnitImage S,
            F (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z)
          ∂fieldOneFiniteStageSplitProductHaarMeasure S := by
    rw [fieldOneFiniteStageIdeleFundamentalProductMeasure]
    calc
      (∫ p, F (e p)
          ∂(count : Measure (fieldOneFiniteStageSUnitImage S)).prod
            (fieldOneFiniteStageSplitProductHaarMeasure S)) =
          ∫ z, ∫ h, F (e (h, z)) ∂(count : Measure
              (fieldOneFiniteStageSUnitImage S))
            ∂fieldOneFiniteStageSplitProductHaarMeasure S :=
        integral_prod_symm _ hFprod'
      _ = ∫ z,
          ∑' h : fieldOneFiniteStageSUnitImage S,
            F (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z)
          ∂fieldOneFiniteStageSplitProductHaarMeasure S := by
        apply integral_congr_ae
        filter_upwards [hFprod'.prod_left_ae] with z hz
        have hz' : Integrable (fun h => F (e (h, z))) count := by
          simpa only [Function.comp_apply] using hz
        rw [MeasureTheory.integral_countable hz']
        apply tsum_congr
        intro h
        rw [MeasureTheory.count_real_singleton, one_smul]
        rfl
  have hpoint (z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) :
      (∑' h : fieldOneFiniteStageSUnitImage S,
        F (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z)) =
        star (fieldOneFiniteStageBruhatSplitHalfDensityDirect S x z) *
          fieldOneFiniteStageBruhatSplitHalfDensityDirect S y z := by
    change (∑' h : fieldOneFiniteStageSUnitImage S,
      (fieldOneFiniteStageModule S
        (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) : ℂ) *
        (∑' gamma : fieldOneSUnitSubgroup S,
          star (fieldOneFiniteStageBruhatEval S x
            (fieldOneFiniteStageIdeleVal S
              (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z))) *
          fieldOneFiniteStageBruhatThetaEval S gamma y
            (fieldOneFiniteStageIdeleVal S
              (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z)))) = _
    simp_rw [fieldOneFiniteStageBruhatEval_val,
      fieldOneFiniteStageBruhatThetaEval_val]
    calc
      (∑' h : fieldOneFiniteStageSUnitImage S,
          (fieldOneFiniteStageModule S
            (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) : ℂ) *
            ∑' gamma : fieldOneSUnitSubgroup S,
              star (fieldOneFiniteStageBruhatOrbit S x
                (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) 1) *
              fieldOneFiniteStageBruhatOrbit S y
                (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) gamma⁻¹) =
          ∑' h : fieldOneFiniteStageSUnitImage S,
            ∑' gamma : fieldOneSUnitSubgroup S,
              (fieldOneFiniteStageModule S
                (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) : ℂ) *
                (star (fieldOneFiniteStageBruhatOrbit S x
                  (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) 1) *
                fieldOneFiniteStageBruhatOrbit S y
                  (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z) gamma⁻¹) := by
        apply tsum_congr
        intro h
        exact tsum_mul_left.symm
      _ = _ := fieldOneFiniteStageBruhatOrbit_complex_double_tsum S x y z
  have hproductSource :
      (∫ p, F (e p) ∂fieldOneFiniteStageIdeleFundamentalProductMeasure S) =
        fieldOneFiniteStageBruhatSourceInner S x y := by
    rw [hcountIntegral, fieldOneFiniteStageBruhatSourceInner]
    apply integral_congr_ae
    exact MeasureTheory.ae_of_all _ fun z => by
      change (∑' h : fieldOneFiniteStageSUnitImage S,
          F (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z)) =
        star (fieldOneFiniteStageBruhatSplitHalfDensity S x z) *
          fieldOneFiniteStageBruhatSplitHalfDensity S y z
      rw [hpoint z, fieldOneFiniteStageBruhatSplitHalfDensityDirect_eq S x,
        fieldOneFiniteStageBruhatSplitHalfDensityDirect_eq S y]
  calc
    (∫ u, F u ∂fieldOneFiniteStageIdeleMultiplicativeFromAdditive S) =
        ∫ u, F u ∂((c : ℝ≥0∞) •
          fieldOneFiniteStageIdeleFundamentalHaarMeasure S) := by rw [hmeasure]
    _ = ((c : ℝ≥0∞).toReal) •
        ∫ u, F u ∂fieldOneFiniteStageIdeleFundamentalHaarMeasure S :=
      integral_smul_measure F (c : ℝ≥0∞)
    _ = (c : ℝ) • fieldOneFiniteStageBruhatSourceInner S x y := by
      rw [hmapIntegral, hproductSource]
      change (c : ℝ) • fieldOneFiniteStageBruhatSourceInner S x y =
        (c : ℝ) • fieldOneFiniteStageBruhatSourceInner S x y
      rfl
    _ = ((haarScalarFactor
        (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S)
        (fieldOneFiniteStageIdeleFundamentalHaarMeasure S) : ℝ) •
          fieldOneFiniteStageBruhatSourceInner S x y) := by
      rfl

/-- Connes--Marcolli Lemma 2.32, exact finite-stage form: the literal source
correlation series is absolutely convergent and equals the source inner
product with the unique positive Haar-normalization scalar. -/
theorem fieldOneFiniteStage_connesMarcolli_lemma_2_32
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    (∑' gamma : fieldOneSUnitSubgroup S,
      fieldOneFiniteStageBruhatAdditiveCorrelation S x y gamma) =
      ((haarScalarFactor
        (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S)
        (fieldOneFiniteStageIdeleFundamentalHaarMeasure S) : ℝ) •
        fieldOneFiniteStageBruhatSourceInner S x y) := by
  rw [fieldOneFiniteStageBruhatAdditiveCorrelation_tsum_eq_integral_series,
    fieldOneFiniteStageBruhatCorrelation_integral_additive_eq_multiplicative,
    fieldOneFiniteStageBruhatCorrelation_integral_multiplicative_eq_sourceInner]

end

end GaloisForLFunctions.RHTower
