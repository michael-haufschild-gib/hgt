import GaloisForLFunctions.RHTower.FieldOneSemilocalL2WeylMultiplier
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Semilocal Bruhat tensors in product-Haar `L²`

A real Schwartz function and a compactly supported locally constant finite-
adele function have a square-integrable pointwise product on
`ℝ × 𝔸_f`.  The construction is bilinear, hence descends to the algebraic
Schwartz--Bruhat tensor.

The resulting map is exactly equivariant for the algebraic and product-Haar
`L²` Weyl actions.  This gives a canonical analytic realization of every
algebraic Bruhat tensor without assuming sigma-finiteness of finite-adele
Haar measure.  It does not yet assert injectivity, density, or identify a
completed Hilbert tensor product.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory
open scoped TensorProduct

/-- Pointwise product associated to a pure semilocal Bruhat tensor. -/
def fieldOneSemilocalPureTensorFun
    (f : FieldOneArchimedeanSchwartz)
    (g : FieldOneFiniteBruhatSchwartz) :
    ℝ × FieldOneFiniteAdele → ℂ :=
  fun x => f x.1 * g.1 x.2

theorem fieldOneSemilocalPureTensorFun_continuous
    (f : FieldOneArchimedeanSchwartz)
    (g : FieldOneFiniteBruhatSchwartz) :
    Continuous (fieldOneSemilocalPureTensorFun f g) := by
  exact
    (f.continuous.comp continuous_fst).mul
      (g.1.continuous.comp continuous_snd)

/-- A pure Schwartz--Bruhat tensor is square-integrable for product Haar
measure.  The proof uses only integrability of the two squared norms and the
product-integrability theorem, so no sigma-finiteness premise is needed. -/
theorem fieldOneSemilocalPureTensorFun_memLp
    (f : FieldOneArchimedeanSchwartz)
    (g : FieldOneFiniteBruhatSchwartz) :
    MemLp (fieldOneSemilocalPureTensorFun f g) 2
      fieldOneSemilocalAddHaar := by
  apply MeasurableEquiv.prodComm.memLp_map_measure_iff.2
  have hf :
      Integrable (fun x : ℝ => ‖f x‖ ^ (2 : ℕ)) volume :=
    (memLp_two_iff_integrable_sq_norm
      f.continuous.aestronglyMeasurable).1
      (f.memLp 2 volume)
  have hg :
      Integrable
        (fun x : FieldOneFiniteAdele => ‖g.1 x‖ ^ (2 : ℕ))
        fieldOneFiniteAdeleAddHaar :=
    (memLp_two_iff_integrable_sq_norm
      g.1.continuous.aestronglyMeasurable).1
      (g.1.continuous.memLp_of_hasCompactSupport g.2)
  apply
    (memLp_two_iff_integrable_sq_norm
      ((fieldOneSemilocalPureTensorFun_continuous f g).comp
        continuous_swap).aestronglyMeasurable).2
  simpa only [fieldOneSemilocalPureTensorFun, Function.comp_apply,
    Prod.swap_prod_mk, norm_mul, mul_pow, mul_comm] using!
    hg.mul_prod hf

/-- Product-Haar `L²` class of a pure semilocal Bruhat tensor. -/
def fieldOneSemilocalPureTensorToL2
    (f : FieldOneArchimedeanSchwartz)
    (g : FieldOneFiniteBruhatSchwartz) :
    Lp ℂ 2 fieldOneSemilocalAddHaar :=
  (fieldOneSemilocalPureTensorFun_memLp f g).toLp
    (fieldOneSemilocalPureTensorFun f g)

theorem fieldOneSemilocalPureTensorToL2_ae
    (f : FieldOneArchimedeanSchwartz)
    (g : FieldOneFiniteBruhatSchwartz) :
    fieldOneSemilocalPureTensorToL2 f g
      =ᵐ[fieldOneSemilocalAddHaar]
        fieldOneSemilocalPureTensorFun f g :=
  (fieldOneSemilocalPureTensorFun_memLp f g).coeFn_toLp

/-- Bilinear product-Haar realization of pure Schwartz--Bruhat tensors. -/
def fieldOneSemilocalBruhatToL2Bilinear :
    FieldOneArchimedeanSchwartz →ₗ[ℂ]
      FieldOneFiniteBruhatSchwartz →ₗ[ℂ]
        Lp ℂ 2 fieldOneSemilocalAddHaar :=
  LinearMap.mk₂ ℂ fieldOneSemilocalPureTensorToL2
    (fun f f' g => by
      apply Lp.ext
      filter_upwards [
        fieldOneSemilocalPureTensorToL2_ae (f + f') g,
        Lp.coeFn_add
          (fieldOneSemilocalPureTensorToL2 f g)
          (fieldOneSemilocalPureTensorToL2 f' g),
        fieldOneSemilocalPureTensorToL2_ae f g,
        fieldOneSemilocalPureTensorToL2_ae f' g]
        with x hsum hadd hf hf'
      rw [hsum, hadd]
      simp only [Pi.add_apply]
      rw [hf, hf']
      simp [fieldOneSemilocalPureTensorFun, add_mul])
    (fun c f g => by
      apply Lp.ext
      filter_upwards [
        fieldOneSemilocalPureTensorToL2_ae (c • f) g,
        Lp.coeFn_smul c (fieldOneSemilocalPureTensorToL2 f g),
        fieldOneSemilocalPureTensorToL2_ae f g]
        with x hleft hsmul hf
      rw [hleft, hsmul]
      simp only [Pi.smul_apply]
      rw [hf]
      simp [fieldOneSemilocalPureTensorFun]
      ring_nf)
    (fun f g g' => by
      apply Lp.ext
      filter_upwards [
        fieldOneSemilocalPureTensorToL2_ae f (g + g'),
        Lp.coeFn_add
          (fieldOneSemilocalPureTensorToL2 f g)
          (fieldOneSemilocalPureTensorToL2 f g'),
        fieldOneSemilocalPureTensorToL2_ae f g,
        fieldOneSemilocalPureTensorToL2_ae f g']
        with x hsum hadd hg hg'
      rw [hsum, hadd]
      simp only [Pi.add_apply]
      rw [hg, hg']
      simp [fieldOneSemilocalPureTensorFun, mul_add])
    (fun c f g => by
      apply Lp.ext
      filter_upwards [
        fieldOneSemilocalPureTensorToL2_ae f (c • g),
        Lp.coeFn_smul c (fieldOneSemilocalPureTensorToL2 f g),
        fieldOneSemilocalPureTensorToL2_ae f g]
        with x hleft hsmul hg
      rw [hleft, hsmul]
      simp only [Pi.smul_apply]
      rw [hg]
      simp [fieldOneSemilocalPureTensorFun]
      ring_nf)

/-- Canonical linear realization of the algebraic semilocal
Schwartz--Bruhat tensor in product-Haar `L²`. -/
def fieldOneSemilocalBruhatToL2 :
    FieldOneSemilocalBruhatSchwartz →ₗ[ℂ]
      Lp ℂ 2 fieldOneSemilocalAddHaar :=
  TensorProduct.lift fieldOneSemilocalBruhatToL2Bilinear

@[simp]
theorem fieldOneSemilocalBruhatToL2_tmul
    (f : FieldOneArchimedeanSchwartz)
    (g : FieldOneFiniteBruhatSchwartz) :
    fieldOneSemilocalBruhatToL2 (f ⊗ₜ[ℂ] g) =
      fieldOneSemilocalPureTensorToL2 f g :=
  rfl

/-- On a pure tensor, the algebraic Weyl action and product-Haar `L²`
unitary agree exactly. -/
theorem fieldOneSemilocalL2WeylUnitary_bruhat_tmul
    (a : ℝ × FieldOneFiniteAdele)
    (f : FieldOneArchimedeanSchwartz)
    (g : FieldOneFiniteBruhatSchwartz) :
    fieldOneSemilocalL2WeylUnitary a
        (fieldOneSemilocalBruhatToL2 (f ⊗ₜ[ℂ] g)) =
      fieldOneSemilocalBruhatToL2
        (fieldOneSemilocalBruhatWeylMultiplier a
          (f ⊗ₜ[ℂ] g)) := by
  simp only [fieldOneSemilocalBruhatToL2_tmul,
    fieldOneSemilocalBruhatWeylMultiplier_tmul]
  apply Lp.ext
  filter_upwards [
    fieldOneSemilocalL2WeylUnitary_ae a
      (fieldOneSemilocalPureTensorToL2 f g),
    fieldOneSemilocalPureTensorToL2_ae f g,
    fieldOneSemilocalPureTensorToL2_ae
      (fieldOneSemilocalArchimedeanWeylMultiplier a.1 f)
      (fieldOneFiniteAdeleStandardWeylMultiplier a.2 g)]
      with x hout hin htarget
  rw [hout, hin, htarget]
  change
    (HTGeometry.FieldOneCore.fieldOneArchimedeanPhase
        (2 * Real.pi * a.1) x.1 *
      fieldOneFiniteAdeleStandardAddChar (a.2 * x.2)) *
        (f x.1 * g.1 x.2) =
      (HTGeometry.FieldOneCore.fieldOneArchimedeanWeylMultiplier
          (2 * Real.pi * a.1) f x.1) *
        (fieldOneFiniteAdeleStandardAddChar (a.2 * x.2) * g.1 x.2)
  rw [HTGeometry.FieldOneCore.fieldOneArchimedeanWeylMultiplier_apply]
  ring

/-- The algebraic and analytic semilocal Weyl actions intertwine on every
algebraic Schwartz--Bruhat tensor. -/
theorem fieldOneSemilocalL2WeylUnitary_bruhat
    (a : ℝ × FieldOneFiniteAdele)
    (t : FieldOneSemilocalBruhatSchwartz) :
    fieldOneSemilocalL2WeylUnitary a
        (fieldOneSemilocalBruhatToL2 t) =
      fieldOneSemilocalBruhatToL2
        (fieldOneSemilocalBruhatWeylMultiplier a t) := by
  induction t using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul f g =>
      exact fieldOneSemilocalL2WeylUnitary_bruhat_tmul a f g
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Rational diagonal specialization of exact Bruhat-to-`L²`
equivariance. -/
theorem fieldOneRationalDiagonalL2WeylUnitary_bruhat
    (q : ℚ)
    (t : FieldOneSemilocalBruhatSchwartz) :
    fieldOneRationalDiagonalL2WeylUnitary q
        (fieldOneSemilocalBruhatToL2 t) =
      fieldOneSemilocalBruhatToL2
        (fieldOneRationalDiagonalBruhatWeylMultiplier q t) :=
  fieldOneSemilocalL2WeylUnitary_bruhat
    (fieldOneRationalDiagonalSemilocalParameter q) t

end

end GaloisForLFunctions.RHTower
