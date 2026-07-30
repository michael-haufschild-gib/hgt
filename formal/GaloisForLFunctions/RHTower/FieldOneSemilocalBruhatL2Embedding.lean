import GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatToL2
import GaloisForLFunctions.RHTower.FunctionTensorProduct

/-!
# Faithful semilocal Bruhat embedding in product-Haar `L²`

The algebraic Schwartz--Bruhat tensor first embeds in the full function space
on `ℝ × 𝔸_f`: uniqueness of finite separated sums is purely algebraic.
Every resulting function is continuous.  Since the semilocal measure was
formed with the sigma-finite real factor on the required side and transported
by coordinate swap, it is positive on nonempty open sets.  Continuous
functions equal almost everywhere are therefore equal everywhere.

Combining these facts proves that the canonical Bruhat-to-`L²` map is
injective.  No sigma-finiteness assertion for finite-adele Haar measure,
completed tensor product, density theorem, trace, positivity, or RH premise
is used.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory
open scoped TensorProduct

/-- Forgetful linear map from real Schwartz functions to full functions. -/
def fieldOneArchimedeanSchwartzToFunction :
    FieldOneArchimedeanSchwartz →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := f
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

theorem fieldOneArchimedeanSchwartzToFunction_injective :
    Function.Injective fieldOneArchimedeanSchwartzToFunction := by
  intro f g h
  ext x
  exact congrFun h x

/-- Forgetful linear map from finite Bruhat functions to full functions. -/
def fieldOneFiniteBruhatToFunction :
    FieldOneFiniteBruhatSchwartz →ₗ[ℂ]
      (FieldOneFiniteAdele → ℂ) where
  toFun g := g.1
  map_add' g h := by ext x; simp
  map_smul' c g := by ext x; simp

theorem fieldOneFiniteBruhatToFunction_injective :
    Function.Injective fieldOneFiniteBruhatToFunction := by
  intro f g h
  apply Subtype.ext
  ext x
  exact congrFun h x

/-- Pointwise-function realization of the algebraic semilocal
Schwartz--Bruhat tensor. -/
def fieldOneSemilocalBruhatToFunction :
    FieldOneSemilocalBruhatSchwartz →ₗ[ℂ]
      (ℝ × FieldOneFiniteAdele → ℂ) :=
  (functionTensorProductHom ℂ ℝ FieldOneFiniteAdele).comp
    (TensorProduct.map
      fieldOneArchimedeanSchwartzToFunction
      fieldOneFiniteBruhatToFunction)

@[simp]
theorem fieldOneSemilocalBruhatToFunction_tmul
    (f : FieldOneArchimedeanSchwartz)
    (g : FieldOneFiniteBruhatSchwartz)
    (x : ℝ × FieldOneFiniteAdele) :
    fieldOneSemilocalBruhatToFunction (f ⊗ₜ[ℂ] g) x =
      f x.1 * g.1 x.2 :=
  rfl

theorem fieldOneSemilocalBruhatToFunction_injective :
    Function.Injective fieldOneSemilocalBruhatToFunction := by
  exact
    (functionTensorProductHom_injective
      ℂ ℝ FieldOneFiniteAdele).comp
      (TensorProduct.map_injective_of_flat_flat
        fieldOneArchimedeanSchwartzToFunction
        fieldOneFiniteBruhatToFunction
        fieldOneArchimedeanSchwartzToFunction_injective
        fieldOneFiniteBruhatToFunction_injective)

/-- Every pointwise function represented by an algebraic semilocal Bruhat
tensor is continuous. -/
theorem fieldOneSemilocalBruhatToFunction_continuous
    (t : FieldOneSemilocalBruhatSchwartz) :
    Continuous (fieldOneSemilocalBruhatToFunction t) := by
  induction t using TensorProduct.induction_on with
  | zero =>
      simpa using! (continuous_const : Continuous
        (fun _ : ℝ × FieldOneFiniteAdele => (0 : ℂ)))
  | tmul f g =>
      simpa only [fieldOneSemilocalBruhatToFunction_tmul] using!
        fieldOneSemilocalPureTensorFun_continuous f g
  | add x y hx hy =>
      simpa only [map_add] using! hx.add hy

/-- The product-Haar `L²` realization has the pointwise tensor function as a
continuous representative. -/
theorem fieldOneSemilocalBruhatToL2_ae
    (t : FieldOneSemilocalBruhatSchwartz) :
    fieldOneSemilocalBruhatToL2 t
      =ᵐ[fieldOneSemilocalAddHaar]
        fieldOneSemilocalBruhatToFunction t := by
  induction t using TensorProduct.induction_on with
  | zero =>
      simpa using!
        (Lp.coeFn_zero ℂ 2 fieldOneSemilocalAddHaar)
  | tmul f g =>
      simpa only [fieldOneSemilocalBruhatToL2_tmul,
        fieldOneSemilocalBruhatToFunction_tmul] using!
        fieldOneSemilocalPureTensorToL2_ae f g
  | add x y hx hy =>
      filter_upwards [
        Lp.coeFn_add
          (fieldOneSemilocalBruhatToL2 x)
          (fieldOneSemilocalBruhatToL2 y),
        hx, hy] with z hadd hxz hyz
      rw [map_add, hadd, Pi.add_apply, hxz, hyz]
      simp

/-- Canonical algebraic Schwartz--Bruhat realization in semilocal
product-Haar `L²` is faithful. -/
theorem fieldOneSemilocalBruhatToL2_injective :
    Function.Injective fieldOneSemilocalBruhatToL2 := by
  intro t u htu
  have hcoe :
      (fieldOneSemilocalBruhatToL2 t :
          ℝ × FieldOneFiniteAdele → ℂ) =
        (fieldOneSemilocalBruhatToL2 u :
          ℝ × FieldOneFiniteAdele → ℂ) :=
    congrArg
      (fun v : Lp ℂ 2 fieldOneSemilocalAddHaar =>
        (v : ℝ × FieldOneFiniteAdele → ℂ)) htu
  have hcoe_ae :
      (fieldOneSemilocalBruhatToL2 t :
          ℝ × FieldOneFiniteAdele → ℂ)
        =ᵐ[fieldOneSemilocalAddHaar]
          (fieldOneSemilocalBruhatToL2 u :
            ℝ × FieldOneFiniteAdele → ℂ) :=
    Filter.Eventually.of_forall (fun z => congrFun hcoe z)
  have hae :
      fieldOneSemilocalBruhatToFunction t
        =ᵐ[fieldOneSemilocalAddHaar]
          fieldOneSemilocalBruhatToFunction u :=
    (fieldOneSemilocalBruhatToL2_ae t).symm.trans
      (hcoe_ae.trans (fieldOneSemilocalBruhatToL2_ae u))
  apply fieldOneSemilocalBruhatToFunction_injective
  exact
    (Continuous.ae_eq_iff_eq fieldOneSemilocalAddHaar
      (fieldOneSemilocalBruhatToFunction_continuous t)
      (fieldOneSemilocalBruhatToFunction_continuous u)).1 hae

end

end GaloisForLFunctions.RHTower
