import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Unit-modulus multipliers on complex `L²`

Any almost-everywhere strongly measurable complex phase of norm one acts by
an onto linear isometry on `L²`, with inverse given by its complex conjugate.
This is a measure-independent construction; no invariance or finiteness
hypothesis on the measure is required.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory

/-- Measurable unit-modulus phase relative to a specified measure. -/
structure UnitModulusL2Phase
    (α : Type*) [MeasurableSpace α] (μ : Measure α) where
  toFun : α → ℂ
  aestronglyMeasurable : AEStronglyMeasurable toFun μ
  norm_eq_one : ∀ᵐ x ∂μ, ‖toFun x‖ = 1

instance {α : Type*} [MeasurableSpace α] {μ : Measure α} :
    CoeFun (UnitModulusL2Phase α μ) (fun _ => α → ℂ) :=
  ⟨UnitModulusL2Phase.toFun⟩

namespace UnitModulusL2Phase

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Complex conjugate phase. -/
def conj (φ : UnitModulusL2Phase α μ) :
    UnitModulusL2Phase α μ where
  toFun x := star (φ x)
  aestronglyMeasurable :=
    Complex.continuous_conj.comp_aestronglyMeasurable
      φ.aestronglyMeasurable
  norm_eq_one := by
    filter_upwards [φ.norm_eq_one] with x hx
    simpa using hx

@[simp]
theorem conj_apply (φ : UnitModulusL2Phase α μ) (x : α) :
    φ.conj x = star (φ x) :=
  rfl

/-- Multiplication by a unit-modulus phase preserves `L²`. -/
theorem memLp_mul (φ : UnitModulusL2Phase α μ)
    (f : Lp ℂ 2 μ) :
    MemLp (fun x => φ x * f x) 2 μ := by
  apply (Lp.memLp f).congr_norm
  · exact φ.aestronglyMeasurable.mul (Lp.memLp f).1
  · filter_upwards [φ.norm_eq_one] with x hx
    simp [hx]

/-- Pointwise phase multiplication as an `L²` class. -/
def mulAux (φ : UnitModulusL2Phase α μ)
    (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (φ.memLp_mul f).toLp _

theorem mulAux_ae (φ : UnitModulusL2Phase α μ)
    (f : Lp ℂ 2 μ) :
    φ.mulAux f =ᵐ[μ] fun x => φ x * f x :=
  (φ.memLp_mul f).coeFn_toLp

/-- Linear phase multiplier on `L²`. -/
def mulLinear (φ : UnitModulusL2Phase α μ) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := φ.mulAux
  map_add' f g := by
    apply Lp.ext
    filter_upwards [φ.mulAux_ae (f + g),
      φ.mulAux_ae f, φ.mulAux_ae g,
      Lp.coeFn_add f g,
      Lp.coeFn_add (φ.mulAux f) (φ.mulAux g)]
      with x hfg hf hg hadd hout
    rw [hfg, hout]
    change φ x * (f + g : Lp ℂ 2 μ) x =
      φ.mulAux f x + φ.mulAux g x
    rw [hadd, hf, hg]
    change φ x * (f x + g x) =
      φ x * f x + φ x * g x
    ring
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [φ.mulAux_ae (c • f),
      φ.mulAux_ae f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (φ.mulAux f)]
      with x hcf hf hcin hcout
    rw [hcf, hcout]
    change φ x * (c • f : Lp ℂ 2 μ) x =
      c • φ.mulAux f x
    rw [hcin, hf]
    change φ x * (c * f x) = c * (φ x * f x)
    ring

theorem norm_mulAux (φ : UnitModulusL2Phase α μ)
    (f : Lp ℂ 2 μ) :
    ‖φ.mulAux f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (φ.mulAux_ae f)]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [φ.norm_eq_one] with x hx
  simp [hx]

/-- Isometric phase multiplier. -/
def mulIsometry (φ : UnitModulusL2Phase α μ) :
    Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ where
  __ := φ.mulLinear
  norm_map' := φ.norm_mulAux

/-- Unitary phase multiplier, with inverse given by the conjugate phase. -/
def mulUnitary (φ : UnitModulusL2Phase α μ) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  __ := φ.mulIsometry
  invFun := φ.conj.mulAux
  left_inv f := by
    change φ.conj.mulAux (φ.mulAux f) = f
    apply Lp.ext
    filter_upwards [φ.mulAux_ae f,
      φ.conj.mulAux_ae (φ.mulAux f),
      φ.norm_eq_one] with x hf hout hnorm
    rw [hout, hf, ← mul_assoc]
    have hphase : star (φ x) * φ x = 1 := by
      change (starRingEnd ℂ) (φ x) * φ x = 1
      rw [← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    change (star (φ x) * φ x) * f x = f x
    rw [hphase, one_mul]
  right_inv f := by
    change φ.mulAux (φ.conj.mulAux f) = f
    apply Lp.ext
    filter_upwards [φ.conj.mulAux_ae f,
      φ.mulAux_ae (φ.conj.mulAux f),
      φ.norm_eq_one] with x hf hout hnorm
    rw [hout, hf, ← mul_assoc]
    have hphase : φ x * star (φ x) = 1 := by
      change φ x * (starRingEnd ℂ) (φ x) = 1
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    change (φ x * star (φ x)) * f x = f x
    rw [hphase, one_mul]

theorem mulUnitary_ae (φ : UnitModulusL2Phase α μ)
    (f : Lp ℂ 2 μ) :
    φ.mulUnitary f =ᵐ[μ] fun x => φ x * f x :=
  φ.mulAux_ae f

end UnitModulusL2Phase

end

end GaloisForLFunctions.RHTower
