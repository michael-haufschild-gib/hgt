import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Derivation.Basic

/-!
# Extending a coefficient derivation to a polynomial ring

A map of the coefficient field into a polynomial ring over it that obeys the Leibniz rule extends
uniquely to a derivation of that polynomial ring killing the variables.

The construction is the dual-number graph: such a map is exactly a ring homomorphism
`K → (MvPolynomial σ K)[ε]`, `a ↦ C a + (δ a) ε`, and evaluating a polynomial through it with the
variables sent to `ε`-free values produces the pair `(p, extension applied to p)`.  The Leibniz rule
of the extension is the multiplicativity of that evaluation, read in the `ε` component.

Taking `δ a = C (a′)` recovers differentiation of coefficients; taking
`δ a = ∑ j, C (∂ⱼ a) · X (j, 0)` gives the chain rule of a reparametrisation with several
velocities.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {σ : Type*}

/-- The dual-number graph of a coefficient derivation. -/
noncomputable def generalGraphHom (δ : K →+ MvPolynomial σ K)
    (hδ : ∀ a b : K, δ (a * b) = MvPolynomial.C a * δ b + MvPolynomial.C b * δ a)
    (hδone : δ 1 = 0) :
    K →+* DualNumber (MvPolynomial σ K) where
  toFun a := (MvPolynomial.C a, δ a)
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simpa using hδone
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [TrivSqZeroExt.fst_mul]
    · rw [TrivSqZeroExt.snd_mul]
      simp only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.fst_mk, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      rw [hδ a b]
      ring
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp

/-- Evaluation of a polynomial through the dual-number graph of a coefficient derivation. -/
noncomputable def generalCoeffEval (δ : K →+ MvPolynomial σ K)
    (hδ : ∀ a b : K, δ (a * b) = MvPolynomial.C a * δ b + MvPolynomial.C b * δ a)
    (hδone : δ 1 = 0) :
    MvPolynomial σ K →+* DualNumber (MvPolynomial σ K) :=
  MvPolynomial.eval₂Hom (generalGraphHom δ hδ hδone)
    fun i => TrivSqZeroExt.inl (MvPolynomial.X i)

theorem generalCoeffEval_fst (δ : K →+ MvPolynomial σ K)
    (hδ : ∀ a b : K, δ (a * b) = MvPolynomial.C a * δ b + MvPolynomial.C b * δ a)
    (hδone : δ 1 = 0) (p : MvPolynomial σ K) :
    (generalCoeffEval δ hδ hδone p).fst = p := by
  have hcomp : ((TrivSqZeroExt.fstHom ℤ (MvPolynomial σ K) (MvPolynomial σ K)).toRingHom.comp
      (generalCoeffEval δ hδ hδone)) = RingHom.id (MvPolynomial σ K) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      simp [generalCoeffEval, generalGraphHom]
    · intro i
      simp [generalCoeffEval]
  exact RingHom.congr_fun hcomp p

/-- The extension of a coefficient derivation to the polynomial ring. -/
noncomputable def generalCoeffDerivFun (δ : K →+ MvPolynomial σ K)
    (hδ : ∀ a b : K, δ (a * b) = MvPolynomial.C a * δ b + MvPolynomial.C b * δ a)
    (hδone : δ 1 = 0) (p : MvPolynomial σ K) : MvPolynomial σ K :=
  (generalCoeffEval δ hδ hδone p).snd

variable {δ : K →+ MvPolynomial σ K}
  {hδ : ∀ a b : K, δ (a * b) = MvPolynomial.C a * δ b + MvPolynomial.C b * δ a}
  {hδone : δ 1 = 0}

@[simp] theorem generalCoeffDerivFun_C (a : K) :
    generalCoeffDerivFun δ hδ hδone (MvPolynomial.C a) = δ a := by
  simp [generalCoeffDerivFun, generalCoeffEval, generalGraphHom]

@[simp] theorem generalCoeffDerivFun_X (i : σ) :
    generalCoeffDerivFun δ hδ hδone (MvPolynomial.X i : MvPolynomial σ K) = 0 := by
  simp [generalCoeffDerivFun, generalCoeffEval]

theorem generalCoeffDerivFun_zero :
    generalCoeffDerivFun δ hδ hδone (0 : MvPolynomial σ K) = 0 := by
  simp [generalCoeffDerivFun]

theorem generalCoeffDerivFun_add (p q : MvPolynomial σ K) :
    generalCoeffDerivFun δ hδ hδone (p + q)
      = generalCoeffDerivFun δ hδ hδone p + generalCoeffDerivFun δ hδ hδone q := by
  simp [generalCoeffDerivFun]

theorem generalCoeffDerivFun_mul (p q : MvPolynomial σ K) :
    generalCoeffDerivFun δ hδ hδone (p * q)
      = p • generalCoeffDerivFun δ hδ hδone q + q • generalCoeffDerivFun δ hδ hδone p := by
  have hmul := map_mul (generalCoeffEval δ hδ hδone) p q
  have hsnd := congrArg TrivSqZeroExt.snd hmul
  rw [TrivSqZeroExt.snd_mul, generalCoeffEval_fst, generalCoeffEval_fst] at hsnd
  simpa [generalCoeffDerivFun, smul_eq_mul, mul_comm] using hsnd

/-- **A coefficient derivation extends to the polynomial ring.** -/
noncomputable def generalCoeffDerivation (δ : K →+ MvPolynomial σ K)
    (hδ : ∀ a b : K, δ (a * b) = MvPolynomial.C a * δ b + MvPolynomial.C b * δ a)
    (hδone : δ 1 = 0) :
    Derivation ℤ (MvPolynomial σ K) (MvPolynomial σ K) := by
  let D : MvPolynomial σ K →+ MvPolynomial σ K :=
    { toFun := generalCoeffDerivFun δ hδ hδone
      map_zero' := generalCoeffDerivFun_zero
      map_add' := generalCoeffDerivFun_add }
  exact Derivation.mk' D.toIntLinearMap generalCoeffDerivFun_mul

@[simp] theorem generalCoeffDerivation_apply (p : MvPolynomial σ K) :
    generalCoeffDerivation δ hδ hδone p = generalCoeffDerivFun δ hδ hδone p := rfl

end GaloisForLFunctions.HTGeometry
