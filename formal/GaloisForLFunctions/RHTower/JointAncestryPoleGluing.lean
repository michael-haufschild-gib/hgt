import GaloisForLFunctions.HTGeometry.TorusPoissonConvolutionSemigroup
import GaloisForLFunctions.HTGeometry.PrimePoissonSuperselectionScreen
import GaloisForLFunctions.RHTower.XiJointAncestrySuperselection
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion

/-!
# JAS pole gluing of reflected prime-Poisson sectors

The prime-Poisson law `μ_{σ+it}` is the product of circle Poisson laws with disk parameters
`p^{-σ+it}`.  The Poisson convolution semigroup gives `μ_s ∗ μ_{s'} = μ_{s+s'}` and
`(-)_* μ_{σ+it} = μ_{σ-it}`.  Three consequences for the joint-ancestry pair:

* **Pole gluing.**  For every `0 < σ < 1` the forward sector and the reflected sector are glued by
  the pole sector: `μ_{σ+it} ∗ (-)_* μ_{(1-σ)+it} = μ_1`.  Off the critical line the two sectors
  are mutually singular, yet the addition map is a measure-preserving correspondence from their
  product onto the pole sector, and composition with it is an `L²` isometry from the pole sector
  into the product which turns each character `χ` into `χ ⊗ χ`.
* **Grade covariance.**  One grade step is convolution with the pole sector,
  `μ_s ∗ μ_1 = μ_{s+1}`; every positive grade of every strip point is Haar absolutely continuous.
* **Critical square root.**  `μ_s ∗ (-)_* μ_s = μ_1` holds exactly on the critical line, so RH is
  equivalent to every Xi zero's sector being a convolution square root of the pole sector.

The square-root criterion reads only `Re ρ`; it never uses `ξ(ρ) = 0`.  The pole gluing holds at
every strip point, so it carries no RH content by itself: it identifies the pole sector as the
only coupling of reflected sectors that survives off the critical line.
-/

open MeasureTheory Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Prime-Poisson laws with equal parameters are equal, whatever the positivity proofs. -/
theorem primePoissonMeasure_congr {σ σ' t t' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ')
    (h1 : σ = σ') (h2 : t = t') :
    primePoissonMeasure σ t hσ = primePoissonMeasure σ' t' hσ' := by
  subst h1
  subst h2
  rfl

theorem primePoissonParameterValue_add (σ σ' t t' : ℝ) (p : Nat.Primes) :
    primePoissonParameterValue (σ + σ') (t + t') p =
      primePoissonParameterValue σ t p * primePoissonParameterValue σ' t' p := by
  rw [primePoissonParameterValue, primePoissonParameterValue, primePoissonParameterValue,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem primePoissonParameterValue_conj (σ t : ℝ) (p : Nat.Primes) :
    conj (primePoissonParameterValue σ t p) = primePoissonParameterValue σ (-t) p := by
  rw [primePoissonParameterValue, primePoissonParameterValue, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Prime-Poisson laws form a convolution semigroup in the strip point. -/
theorem primePoissonMeasure_conv {σ σ' : ℝ} (t t' : ℝ) (hσ : 0 < σ) (hσ' : 0 < σ') :
    primePoissonMeasure σ t hσ ∗ primePoissonMeasure σ' t' hσ' =
      primePoissonMeasure (σ + σ') (t + t') (add_pos hσ hσ') := by
  unfold primePoissonMeasure
  rw [torusPoissonMeasure_conv]
  congr 1
  funext p
  apply Subtype.ext
  simp [primePoissonParameterValue_add]

/-- Reflection of the prime torus reverses the height of a prime-Poisson law. -/
theorem map_neg_primePoissonMeasure (σ t : ℝ) (hσ : 0 < σ) :
    (primePoissonMeasure σ t hσ).map Neg.neg = primePoissonMeasure σ (-t) hσ := by
  unfold primePoissonMeasure
  rw [map_neg_torusPoissonMeasure]
  congr 1
  funext p
  apply Subtype.ext
  simp [primePoissonParameterValue_conj]

/-- **JAS pole gluing.**  The forward sector at `σ + it` and the reflected sector at
`(1 - σ) + it` convolve, after reflecting the second, to the pole sector `μ_1`. -/
theorem primePoissonMeasure_conv_reflected_eq_pole (σ t : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    primePoissonMeasure σ t hσ ∗
        (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)).map Neg.neg =
      primePoissonMeasure 1 0 one_pos := by
  rw [map_neg_primePoissonMeasure, primePoissonMeasure_conv]
  exact primePoissonMeasure_congr _ _ (by ring) (by ring)

/-- The addition map carries the product of the reflected pair onto the pole sector. -/
theorem measurePreserving_add_primePoissonPoleGluing (σ t : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    MeasurePreserving
      (fun x : (Nat.Primes → UnitAddCircle) × (Nat.Primes → UnitAddCircle) => x.1 + x.2)
      ((primePoissonMeasure σ t hσ).prod
        ((primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)).map Neg.neg))
      (primePoissonMeasure 1 0 one_pos) := by
  refine ⟨measurable_add, ?_⟩
  rw [← primePoissonMeasure_conv_reflected_eq_pole σ t hσ hσ1]
  rfl

/-- The pole-gluing isometry from the pole sector into the product of the reflected pair. -/
def jasPoleGluingIsometry (σ t : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    Lp ℂ 2 (primePoissonMeasure 1 0 one_pos) →ₗᵢ[ℂ]
      Lp ℂ 2 ((primePoissonMeasure σ t hσ).prod
        ((primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)).map Neg.neg)) :=
  Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_add_primePoissonPoleGluing σ t hσ hσ1)

/-- The pole-gluing isometry intertwines a character on the pole sector with the corresponding
tensor character on the reflected pair. -/
theorem jasPoleGluingIsometry_continuousL2Mul_infiniteTorusFourier
    (σ t : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) (n : Nat.Primes →₀ ℤ)
    (f : Lp ℂ 2 (primePoissonMeasure 1 0 one_pos)) :
    (jasPoleGluingIsometry σ t hσ hσ1
        (continuousL2Mul (primePoissonMeasure 1 0 one_pos) (infiniteTorusFourier n) f) :
          (Nat.Primes → UnitAddCircle) × (Nat.Primes → UnitAddCircle) → ℂ) =ᵐ[
        (primePoissonMeasure σ t hσ).prod
          ((primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)).map Neg.neg)]
      fun x => infiniteTorusFourier n x.1 * infiniteTorusFourier n x.2 *
        (jasPoleGluingIsometry σ t hσ hσ1 f :
          (Nat.Primes → UnitAddCircle) × (Nat.Primes → UnitAddCircle) → ℂ) x := by
  have hmp := measurePreserving_add_primePoissonPoleGluing σ t hσ hσ1
  have hmul := hmp.quasiMeasurePreserving.ae_eq_comp
    (continuousL2Mul_coeFn (primePoissonMeasure 1 0 one_pos) (infiniteTorusFourier n) f)
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (continuousL2Mul (primePoissonMeasure 1 0 one_pos) (infiniteTorusFourier n) f) hmp,
    Lp.coeFn_compMeasurePreserving f hmp, hmul] with x h1 h2 h3
  have happ : ∀ g : Lp ℂ 2 (primePoissonMeasure 1 0 one_pos),
      jasPoleGluingIsometry σ t hσ hσ1 g = Lp.compMeasurePreserving _ hmp g := fun _ => rfl
  rw [happ, happ, h1, h2, Function.comp_apply, Function.comp_apply]
  rw [Function.comp_apply] at h3
  rw [h3, Function.comp_apply, infiniteTorusFourier_add_point]

/-- **Grade covariance.**  Raising the grade by one is convolution with the pole sector. -/
theorem primePoissonMeasure_conv_pole (σ t : ℝ) (hσ : 0 < σ) :
    primePoissonMeasure σ t hσ ∗ primePoissonMeasure 1 0 one_pos =
      primePoissonMeasure (σ + 1) t (by linarith) := by
  rw [primePoissonMeasure_conv]
  exact primePoissonMeasure_congr _ _ rfl (by ring)

/-- Every positive grade of every strip point is Haar absolutely continuous. -/
theorem primePoissonMeasure_conv_pole_absolutelyContinuous_torusHaar
    (σ t : ℝ) (hσ : 0 < σ) :
    primePoissonMeasure σ t hσ ∗ primePoissonMeasure 1 0 one_pos ≪ torusHaar Nat.Primes := by
  rw [primePoissonMeasure_conv_pole]
  exact (primePoissonMeasure_absolutelyContinuous_torusHaar_iff _ _ _).2 (by linarith)

/-- Real-axis prime-Poisson laws determine their abscissa. -/
theorem primePoissonMeasure_real_injective {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ')
    (h : primePoissonMeasure σ 0 hσ = primePoissonMeasure σ' 0 hσ') : σ = σ' := by
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hint := congrArg
    (fun μ => ∫ x, infiniteTorusFourier (Finsupp.single p2 (1 : ℤ)) x ∂μ) h
  simp only [primePoissonMeasure, integral_infiniteTorusFourier_torusPoissonMeasure] at hint
  rw [Finsupp.prod_single_index (by simp [circlePoissonFourierMoment]),
    Finsupp.prod_single_index (by simp [circlePoissonFourierMoment])] at hint
  have hval : primePoissonParameterValue σ 0 p2 = primePoissonParameterValue σ' 0 p2 := by
    simpa [circlePoissonFourierMoment] using hint
  have hnorm := congrArg norm hval
  rw [norm_primePoissonParameterValue, norm_primePoissonParameterValue,
    Real.exp_eq_exp] at hnorm
  have hlog : 0 < Real.log ((p2 : ℕ) : ℝ) := by
    simp only [p2]
    exact Real.log_pos (by norm_num)
  nlinarith

/-- A sector convolved with its own reflection is the real-axis sector at twice the abscissa. -/
theorem primePoissonMeasure_conv_self_reflected (σ t : ℝ) (hσ : 0 < σ) :
    primePoissonMeasure σ t hσ ∗ (primePoissonMeasure σ t hσ).map Neg.neg =
      primePoissonMeasure (2 * σ) 0 (by positivity) := by
  rw [map_neg_primePoissonMeasure, primePoissonMeasure_conv]
  exact primePoissonMeasure_congr _ _ (by ring) (by ring)

/-- **Critical square-root law.**  A prime-Poisson sector is a convolution square root of the
pole sector exactly on the critical line. -/
theorem primePoissonMeasure_conv_self_reflected_eq_pole_iff (σ t : ℝ) (hσ : 0 < σ) :
    primePoissonMeasure σ t hσ ∗ (primePoissonMeasure σ t hσ).map Neg.neg =
        primePoissonMeasure 1 0 one_pos ↔ σ = 1 / 2 := by
  rw [primePoissonMeasure_conv_self_reflected]
  constructor
  · intro h
    have := primePoissonMeasure_real_injective _ _ h
    linarith
  · intro h
    exact primePoissonMeasure_congr _ _ (by rw [h]; norm_num) rfl

/-! ## Xi divisor specialization -/

/-- Every Xi divisor point has its forward and reflected prime-Poisson sectors glued by the pole
sector.  No property of the divisor beyond its strip location is used. -/
theorem xiPrimePoissonPoleGluing (rho : XiDivisorSupport) :
    primePoissonMeasure (rho : ℂ).re (rho : ℂ).im (xi_divisor_support_re_mem_open_unit rho).1 ∗
        (primePoissonMeasure (1 - (rho : ℂ).re) (rho : ℂ).im
          (sub_pos.mpr (xi_divisor_support_re_mem_open_unit rho).2)).map Neg.neg =
      primePoissonMeasure 1 0 one_pos :=
  primePoissonMeasure_conv_reflected_eq_pole _ _ (xi_divisor_support_re_mem_open_unit rho).1
    (xi_divisor_support_re_mem_open_unit rho).2

/-- Off the critical line, mutually singular reflected sectors are nonetheless glued by the pole
sector.  The pole gluing therefore never descends to a source-linear sewing off the line. -/
theorem xiPrimePoissonPoleGluing_of_offLine (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    (primePoissonMeasure (rho : ℂ).re (rho : ℂ).im
        (xi_divisor_support_re_mem_open_unit rho).1).MutuallySingular
      (primePoissonMeasure (1 - (rho : ℂ).re) (rho : ℂ).im
        (sub_pos.mpr (xi_divisor_support_re_mem_open_unit rho).2)) ∧
    primePoissonMeasure (rho : ℂ).re (rho : ℂ).im (xi_divisor_support_re_mem_open_unit rho).1 ∗
        (primePoissonMeasure (1 - (rho : ℂ).re) (rho : ℂ).im
          (sub_pos.mpr (xi_divisor_support_re_mem_open_unit rho).2)).map Neg.neg =
      primePoissonMeasure 1 0 one_pos ∧
    ¬ XiPrimePoissonReflectionSewing rho := by
  refine ⟨primePoissonMeasure_reflection_mutuallySingular_of_ne_half _ _
    (xi_divisor_support_re_mem_open_unit rho).1 (xi_divisor_support_re_mem_open_unit rho).2 hoff,
    xiPrimePoissonPoleGluing rho, ?_⟩
  rw [xiPrimePoissonReflectionSewing_iff_internalOnly,
    xiDivisorSyndromeIsInternalOnly_iff_re_eq_half]
  exact hoff

/-- The prime-Poisson sector of a Xi divisor point is a convolution square root of the pole
sector. -/
def XiPrimePoissonCriticalSquareRoot (rho : XiDivisorSupport) : Prop :=
  primePoissonMeasure (rho : ℂ).re (rho : ℂ).im (xi_divisor_support_re_mem_open_unit rho).1 ∗
      (primePoissonMeasure (rho : ℂ).re (rho : ℂ).im
        (xi_divisor_support_re_mem_open_unit rho).1).map Neg.neg =
    primePoissonMeasure 1 0 one_pos

theorem xiPrimePoissonCriticalSquareRoot_iff (rho : XiDivisorSupport) :
    XiPrimePoissonCriticalSquareRoot rho ↔ (rho : ℂ).re = 1 / 2 :=
  primePoissonMeasure_conv_self_reflected_eq_pole_iff _ _ _

/-- RH is equivalent to every Xi zero's prime-Poisson sector being a convolution square root of
the pole sector. -/
theorem forall_xiPrimePoissonCriticalSquareRoot_iff_riemannHypothesis :
    (∀ rho : XiDivisorSupport, XiPrimePoissonCriticalSquareRoot rho) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (xiPrimePoissonCriticalSquareRoot_iff rho).1 (h rho)
  · intro hRH rho
    exact (xiPrimePoissonCriticalSquareRoot_iff rho).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
