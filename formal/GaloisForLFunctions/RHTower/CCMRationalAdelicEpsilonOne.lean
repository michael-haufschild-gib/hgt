import GaloisForLFunctions.RHTower.CCMRationalFiniteAdeleHaarCharacter
import GaloisForLFunctions.RHTower.CCMRationalArchimedeanHaar
import GaloisForLFunctions.RHTower.CCMRationalAdelicCrossedProduct

/-!
# Haar endpoint trace on the rational CCM cyclic source

Archimedean Lebesgue integration and normalized finite-adele Haar integration are tensored on the
actual algebraic adelic Bruhat core. Exact finite-adelic Haar character cancels the archimedean
Jacobian, proving invariance under every rational inverse scaling.

The identity-coefficient functional on the actual nonunital twisted crossed product is therefore a
trace. Its minimal-unitization extension is normalized by `ε₁(1)=1`. No abstract invariant
functional, product-formula premise, completion surrogate, or quotient proxy occurs.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

private abbrev Arch := CCMRationalArchimedeanSchwartz
private abbrev FinBruhat := CCMRationalFiniteBruhatSchwartz
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra

local instance ccmRationalAdelicEpsilonOneScaleDecidableEq : DecidableEq Scale :=
  Classical.decEq _

def ccmRationalAdelicBruhatIntegralBilinear : Arch →ₗ[ℂ] FinBruhat →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := fun φ ↦ ccmRationalArchimedeanSchwartzIntegral f *
          ccmRationalFiniteBruhatIntegral φ
      map_add' := by
        intro φ ψ
        change ccmRationalArchimedeanSchwartzIntegral f *
            ccmRationalFiniteBruhatIntegral (φ + ψ) = _
        rw [map_add]
        ring
      map_smul' := by intro z φ; simp; ring }
  map_add' := by
    intro f g
    ext φ
    change ccmRationalArchimedeanSchwartzIntegral (f + g) *
        ccmRationalFiniteBruhatIntegral φ =
      ccmRationalArchimedeanSchwartzIntegral f *
          ccmRationalFiniteBruhatIntegral φ +
        ccmRationalArchimedeanSchwartzIntegral g *
          ccmRationalFiniteBruhatIntegral φ
    rw [map_add]
    ring
  map_smul' := by intro z f; ext φ; simp; ring

def ccmRationalAdelicBruhatIntegral : Core →ₗ[ℂ] ℂ :=
  TensorProduct.lift ccmRationalAdelicBruhatIntegralBilinear

@[simp] theorem ccmRationalAdelicBruhatIntegral_tmul (f : Arch) (φ : FinBruhat) :
    ccmRationalAdelicBruhatIntegral (f ⊗ₜ[ℂ] φ) =
      ccmRationalArchimedeanSchwartzIntegral f *
        ccmRationalFiniteBruhatIntegral φ := rfl

theorem ccmRationalAdelicBruhatIntegral_smul (k : Scale) (x : Core) :
    ccmRationalAdelicBruhatIntegral (k • x) = ccmRationalAdelicBruhatIntegral x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f φ =>
      simp only [ccmRationalAdelicScaling_smul_tmul, ccmRationalAdelicBruhatIntegral_tmul,
        ccmRationalArchimedeanSchwartzIntegral_scaling,
        ccmRationalFiniteBruhatIntegral_scaling]
      let a := |(((k.val : CCMRationalUnit) : ℚ) : ℝ)|
      have ha : a ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast k.val.ne_zero)
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      field_simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy]

theorem ccmRationalAdelicBruhatIntegral_twisted_swap
    (k l : Scale) (hkl : k * l = 1) (a b : Core) :
    ccmRationalAdelicBruhatIntegral (a * (k • b)) =
      ccmRationalAdelicBruhatIntegral (b * (l • a)) := by
  have hl : l = k⁻¹ := by
    calc
      l = 1 * l := by simp
      _ = (k⁻¹ * k) * l := by simp
      _ = k⁻¹ * (k * l) := by rw [mul_assoc]
      _ = k⁻¹ := by rw [hkl]; simp
  subst l
  calc
    ccmRationalAdelicBruhatIntegral (a * (k • b)) =
        ccmRationalAdelicBruhatIntegral ((k • b) * a) := by rw [mul_comm]
    _ = ccmRationalAdelicBruhatIntegral (k • (b * (k⁻¹ • a))) := by
      rw [ccmRationalAdelicBruhatScaling_map_mul, smul_smul]
      simp
    _ = ccmRationalAdelicBruhatIntegral (b * (k⁻¹ • a)) := ccmRationalAdelicBruhatIntegral_smul _ _

def ccmRationalAdelicEpsilonOneNonunital : Crossed →ₗ[ℂ] ℂ where
  toFun F := ccmRationalAdelicBruhatIntegral (F 1)
  map_add' F H := by simp
  map_smul' z F := by simp

@[simp]
theorem ccmRationalAdelicEpsilonOneNonunital_apply (F : Crossed) :
    ccmRationalAdelicEpsilonOneNonunital F =
      ccmRationalAdelicBruhatIntegral (F 1) :=
  rfl

@[simp] theorem ccmRationalAdelicEpsilonOneNonunital_single (k : Scale) (a : Core) :
    ccmRationalAdelicEpsilonOneNonunital (Finsupp.single k a) =
      if k = 1 then ccmRationalAdelicBruhatIntegral a else 0 := by
  by_cases hk : k = 1
  · subst k
    simp [ccmRationalAdelicEpsilonOneNonunital]
  · have hk' : (1 : Scale) ≠ k := fun h ↦ hk h.symm
    simp [ccmRationalAdelicEpsilonOneNonunital, hk, hk']

theorem ccmRationalAdelicEpsilonOneNonunital_isTrace (F H : Crossed) :
    ccmRationalAdelicEpsilonOneNonunital (F * H) =
      ccmRationalAdelicEpsilonOneNonunital (H * F) := by
  classical
  have hpure (k l : Scale) (a b : Core) :
      ccmRationalAdelicEpsilonOneNonunital
          (Finsupp.single k a * Finsupp.single l b) =
        ccmRationalAdelicEpsilonOneNonunital
          (Finsupp.single l b * Finsupp.single k a) := by
    by_cases hkl : k * l = 1
    · have hlk : l * k = 1 := by
        calc
          l * k = l * (k * l) * l⁻¹ := by simp [mul_assoc]
          _ = 1 := by rw [hkl]; simp
      simp only [ccmRationalAdelicCrossedProduct_single_mul_single,
        ccmRationalAdelicEpsilonOneNonunital_single, if_pos hkl, if_pos hlk]
      exact ccmRationalAdelicBruhatIntegral_twisted_swap k l hkl a b
    · have hlk : l * k ≠ 1 := by
        intro h
        apply hkl
        calc
          k * l = k * (l * k) * k⁻¹ := by simp [mul_assoc]
          _ = 1 := by rw [h]; simp
      simp [ccmRationalAdelicCrossedProduct_single_mul_single, hkl, hlk]
  have hpureLeft (k : Scale) (a : Core) (J : Crossed) :
      ccmRationalAdelicEpsilonOneNonunital (Finsupp.single k a * J) =
        ccmRationalAdelicEpsilonOneNonunital (J * Finsupp.single k a) := by
    induction J using Finsupp.induction with
    | zero => simp
    | @single_add l b J hl hb hJ =>
        rw [ccmRationalAdelicCrossedProduct_mul_add,
          ccmRationalAdelicCrossedProduct_add_mul, map_add, map_add,
          hpure, hJ]
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add k a F hk ha hF =>
      rw [ccmRationalAdelicCrossedProduct_add_mul,
        ccmRationalAdelicCrossedProduct_mul_add, map_add, map_add,
        hpureLeft, hF]

def ccmRationalAdelicEpsilonOne : Source →ₗ[ℂ] ℂ where
  toFun x := x.fst + ccmRationalAdelicEpsilonOneNonunital x.snd
  map_add' x y := by
    simp only [Unitization.fst_add, Unitization.snd_add, map_add]
    ring
  map_smul' z x := by
    simp only [Unitization.fst_smul, Unitization.snd_smul, map_smul,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem ccmRationalAdelicEpsilonOne_one :
    ccmRationalAdelicEpsilonOne (1 : Source) = 1 := by
  simp [ccmRationalAdelicEpsilonOne]

@[simp] theorem ccmRationalAdelicEpsilonOne_inr (F : Crossed) :
    ccmRationalAdelicEpsilonOne (F : Source) = ccmRationalAdelicEpsilonOneNonunital F := by
  simp [ccmRationalAdelicEpsilonOne]

theorem ccmRationalAdelicEpsilonOne_isTrace (x y : Source) :
    ccmRationalAdelicEpsilonOne (x * y) = ccmRationalAdelicEpsilonOne (y * x) := by
  change (x * y).fst + ccmRationalAdelicEpsilonOneNonunital (x * y).snd =
    (y * x).fst + ccmRationalAdelicEpsilonOneNonunital (y * x).snd
  rw [Unitization.fst_mul, Unitization.fst_mul,
    Unitization.snd_mul, Unitization.snd_mul]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [ccmRationalAdelicEpsilonOneNonunital_isTrace x.snd y.snd]
  ring

end GaloisForLFunctions.RHTower
