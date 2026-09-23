import GaloisForLFunctions.RHTower.RouteRSignedKummerCyclicCartierLanding

/-!
# Hochschild-cycle wall for the retained Route-R prime chain

The retained tensor `p tensor p^-1` has nonzero cyclic product trace and nonzero Kummer regulator,
but those facts do not make it a Hochschild one-cycle.  This module computes its degree-one
Hochschild boundary in the actual rational-adelic crossed product and proves that boundary is
nonzero.

The separating functional evaluates the real Schwartz factor at `1` and the finite Bruhat factor
at the zero finite adele.  Forward and backward products then contain respectively the Gaussian
values at `p^-1` and `p`; strict injectivity of the real exponential separates them for every
ordinary prime.

Consequently any genuine source homology producer must supply a singular relative correction or
replace the decorated prime tensor by a genuine multiplier/K1 dilation cycle.  Quotienting by
signed cyclic and degree-two boundaries alone is not a homology construction.
-/

open Complex
open GaloisForLFunctions.RHTower
open scoped TensorProduct

namespace RHTower

noncomputable section

private abbrev Arch := CCMRationalArchimedeanSchwartz
private abbrev FinBruhat := CCMRationalFiniteBruhatSchwartz
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor

/-- Evaluation at real coordinate `x` and the zero finite adele. -/
def ccmRationalAdelicBruhatRealZeroFiniteEvalBilinear (x : ℝ) :
    Arch →ₗ[ℂ] FinBruhat →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := fun phi => f x * phi.1 0
      map_add' := by
        intro phi psi
        simp [mul_add]
      map_smul' := by
        intro z phi
        simp
        ring }
  map_add' := by
    intro f g
    ext phi
    simp [add_mul]
  map_smul' := by
    intro z f
    ext phi
    simp
    ring

/-- Tensor-core form of real/zero-finite evaluation. -/
def ccmRationalAdelicBruhatRealZeroFiniteEval (x : ℝ) : Core →ₗ[ℂ] ℂ :=
  TensorProduct.lift (ccmRationalAdelicBruhatRealZeroFiniteEvalBilinear x)

@[simp]
theorem ccmRationalAdelicBruhatRealZeroFiniteEval_tmul
    (x : ℝ) (f : Arch) (phi : FinBruhat) :
    ccmRationalAdelicBruhatRealZeroFiniteEval x (f ⊗ₜ[ℂ] phi) =
      f x * phi.1 0 :=
  rfl

theorem ccmRationalAdelicPrimeCore_forwardProduct_eval_one
    (p : Nat.Primes) :
    ccmRationalAdelicBruhatRealZeroFiniteEval 1
      (ccmRationalAdelicPrimeCycleCore *
        ccmRationalAdelicPrimeScaling p • ccmRationalAdelicPrimeCycleCore) =
      ((GaloisForLFunctions.gaussReal 1 *
        GaloisForLFunctions.gaussReal ((p : ℝ)⁻¹) : ℝ) : ℂ) := by
  rw [ccmRationalAdelicPrimeCycleCore,
    ccmRationalAdelicScaling_smul_tmul,
    ccmRationalAdelicBruhat_tmul_mul_tmul,
    ccmRationalAdelicBruhatRealZeroFiniteEval_tmul]
  simp [ccmRationalArchimedeanScaling_apply,
    ccmRationalAdelicPrimeScaling]

theorem ccmRationalAdelicPrimeCore_backwardProduct_eval_one
    (p : Nat.Primes) :
    ccmRationalAdelicBruhatRealZeroFiniteEval 1
      (ccmRationalAdelicPrimeCycleCore *
        (ccmRationalAdelicPrimeScaling p)⁻¹ • ccmRationalAdelicPrimeCycleCore) =
      ((GaloisForLFunctions.gaussReal 1 *
        GaloisForLFunctions.gaussReal (p : ℝ) : ℝ) : ℂ) := by
  rw [ccmRationalAdelicPrimeCycleCore,
    ccmRationalAdelicScaling_smul_tmul,
    ccmRationalAdelicBruhat_tmul_mul_tmul,
    ccmRationalAdelicBruhatRealZeroFiniteEval_tmul]
  simp [ccmRationalArchimedeanScaling_apply,
    ccmRationalAdelicPrimeScaling]

/-- Prime and inverse-prime Gaussian scales differ. -/
theorem gaussReal_prime_inv_ne_prime (p : Nat.Primes) :
    GaloisForLFunctions.gaussReal ((p : ℝ)⁻¹) ≠
      GaloisForLFunctions.gaussReal (p : ℝ) := by
  rw [GaloisForLFunctions.gaussReal, GaloisForLFunctions.gaussReal,
    Real.exp_injective.ne_iff]
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hsquare : (p : ℝ)⁻¹ ^ (2 : ℕ) < (p : ℝ) ^ (2 : ℕ) := by
    nlinarith [inv_pos.mpr hp0, inv_lt_one_of_one_lt₀ hp]
  nlinarith [Real.pi_pos]

/-- Forward and backward coefficient products are genuinely different in the Bruhat core. -/
theorem ccmRationalAdelicPrimeCore_forwardProduct_ne_backwardProduct
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeCycleCore *
        ccmRationalAdelicPrimeScaling p • ccmRationalAdelicPrimeCycleCore ≠
      ccmRationalAdelicPrimeCycleCore *
        (ccmRationalAdelicPrimeScaling p)⁻¹ •
          ccmRationalAdelicPrimeCycleCore := by
  intro h
  have he := congrArg (ccmRationalAdelicBruhatRealZeroFiniteEval 1) h
  rw [ccmRationalAdelicPrimeCore_forwardProduct_eval_one,
    ccmRationalAdelicPrimeCore_backwardProduct_eval_one] at he
  norm_cast at he
  exact gaussReal_prime_inv_ne_prime p
    (mul_left_cancel₀ (GaloisForLFunctions.gaussReal_pos 1).ne' he)

/-- Degree-one Hochschild boundary `d0 - d1` on the actual cyclic bar source. -/
def ccmRationalAdelicHochschildBoundaryOne :
    CCMRationalAdelicDegreeOneCyclicSource →ₗ[ℂ]
      CCMRationalAdelicCyclicSourceAlgebra :=
  (cyclicBarDegreeZeroProduct (R := ℂ)).comp
    (cyclicBarFace (R := ℂ) (A := CCMRationalAdelicCyclicSourceAlgebra)
        (0 : Fin 2) -
      cyclicBarFace (R := ℂ) (A := CCMRationalAdelicCyclicSourceAlgebra)
        (1 : Fin 2))

theorem ccmRationalAdelicHochschildBoundaryOne_tprod
    (a b : CCMRationalAdelicCyclicSourceAlgebra) :
    ccmRationalAdelicHochschildBoundaryOne
        (PiTensorProduct.tprod ℂ (fun i : Fin 2 =>
          Fin.cases a (fun _ => b) i)) =
      a * b - b * a := by
  let x : Fin 2 → CCMRationalAdelicCyclicSourceAlgebra :=
    fun i => Fin.cases a (fun _ => b) i
  have hface0 : cyclicBarFaceTuple (0 : Fin 2) x 0 = a * b := by
    rw [show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) by rfl]
    rw [cyclicBarFaceTuple, Fin.lastCases_castSucc]
    simp [x, cyclicBarFaceNonwrapTuple]
    rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, Fin.cases_succ]
  have hface1 : cyclicBarFaceTuple (1 : Fin 2) x 0 = b * a := by
    rw [show (1 : Fin 2) = Fin.last 1 by rfl]
    rw [cyclicBarFaceTuple, Fin.lastCases_last]
    simp [x, cyclicBarFaceWrapTuple]
    rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, Fin.cases_succ]
  change ccmRationalAdelicHochschildBoundaryOne
    (PiTensorProduct.tprod ℂ x) = _
  simp only [ccmRationalAdelicHochschildBoundaryOne,
    LinearMap.comp_apply, LinearMap.sub_apply, cyclicBarFace_tprod,
    map_sub, cyclicBarDegreeZeroProduct_tprod]
  rw [hface0, hface1]

/-- **Cycle wall.** The existing retained ordinary-prime tensor is not a Hochschild one-cycle. -/
theorem ccmRationalAdelicOrdinaryPrimeCycleAtom_boundaryOne_ne_zero
    (p : Nat.Primes) :
    ccmRationalAdelicHochschildBoundaryOne
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p) ≠ 0 := by
  intro hzero
  rw [ccmRationalAdelicOrdinaryPrimeCycleAtom,
    ccmRationalAdelicHochschildBoundaryOne_tprod] at hzero
  have hsnd := congrArg
    (fun z : CCMRationalAdelicCyclicSourceAlgebra => z.snd) hzero
  simp only [Unitization.snd_zero] at hsnd
  change
    ((ccmRationalAdelicPrimeCycleForward p :
        CCMRationalAdelicCyclicSourceAlgebra) *
      (ccmRationalAdelicPrimeCycleBackward p :
        CCMRationalAdelicCyclicSourceAlgebra)).snd -
    ((ccmRationalAdelicPrimeCycleBackward p :
        CCMRationalAdelicCyclicSourceAlgebra) *
      (ccmRationalAdelicPrimeCycleForward p :
        CCMRationalAdelicCyclicSourceAlgebra)).snd = 0 at hsnd
  rw [Unitization.snd_mul, Unitization.snd_mul] at hsnd
  simp at hsnd
  rw [sub_eq_zero] at hsnd
  simp only [ccmRationalAdelicPrimeCycleForward,
    ccmRationalAdelicPrimeCycleBackward,
    ccmRationalAdelicCrossedProduct_single_mul_single] at hsnd
  simp only [mul_inv_cancel, inv_mul_cancel] at hsnd
  exact ccmRationalAdelicPrimeCore_forwardProduct_ne_backwardProduct p
    ((Finsupp.single_injective (1 : CCMRationalAdelicScaling)) hsnd)

end

end RHTower
