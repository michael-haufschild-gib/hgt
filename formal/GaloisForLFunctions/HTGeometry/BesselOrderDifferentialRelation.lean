import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphicScalarExtension
import GaloisForLFunctions.HTGeometry.MobiusJetTransfer

/-!
# A differential-algebraic Bessel order function supplies a scalar PPV relation

A hypothetical algebraic differential equation for the entire order carrier is first moved to the
global meromorphic field, compiled from a finite jet polynomial to one differential indeterminate,
and then extended from `ℂ(z)` to `Constants(z)`.  Faithful tensor inclusion puts the resulting
nonzero relation at the actual Bessel point used by the relation-adapted PPV construction.
-/

open scoped Differential TensorProduct

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic besselScalarComplexDifferential
  besselScalarRatFuncComplexDifferential besselScalarRatFuncConstantsDifferential
  constantsDifferentialAlgebra besselScalarRatFuncAlgebra besselScalarMeroAlgebra
  ratFuncConstantsDifferentialAlgebra meromorphicDifferentialAlgebra
  besselScalarTensorDifferential besselScalarTensorDifferentialAlgebra

local instance besselOrderDifferentialRelationRatIntAlgebra :
    Algebra ℤ (RatFunc Constants) := Ring.toIntAlgebra _

/-- Embed a finite consecutive-jet polynomial into one differential indeterminate. -/
def finiteJetScalarDifferentialPolynomial {n : ℕ}
    (Q : MvPolynomial (Fin (n + 1)) (RatFunc ℂ)) :
    DifferentialPolynomial Unit (RatFunc ℂ) :=
  MvPolynomial.rename (fun j : Fin (n + 1) => ((), (j : ℕ))) Q

theorem finiteJetScalarDifferentialPolynomial_ne_zero {n : ℕ}
    {Q : MvPolynomial (Fin (n + 1)) (RatFunc ℂ)} (hQ : Q ≠ 0) :
    finiteJetScalarDifferentialPolynomial Q ≠ 0 := by
  intro hzero
  apply hQ
  exact MvPolynomial.rename_injective
    (fun j : Fin (n + 1) => ((), (j : ℕ)))
    (fun i j hij => Fin.ext (congrArg Prod.snd hij))
    (by
      simpa [finiteJetScalarDifferentialPolynomial] using hzero)

theorem finiteJetScalarDifferentialPolynomial_eval {n : ℕ}
    (Q : MvPolynomial (Fin (n + 1)) (RatFunc ℂ))
    (y : meroField Set.univ) :
    differentialPolynomialEvalOver (K := RatFunc ℂ) (fun _ : Unit => y)
        (finiteJetScalarDifferentialPolynomial Q) =
      MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) y) Q := by
  rw [finiteJetScalarDifferentialPolynomial, differentialPolynomialEvalOver,
    MvPolynomial.aeval_rename]
  rfl

theorem besselScalarIncludeRight_deriv (x : meroField Set.univ) :
    Algebra.TensorProduct.includeRight
        (R := RatFunc ℂ) (A := RatFunc Constants) (B := meroField Set.univ)
        (Differential.deriv x) =
      Differential.deriv
        (Algebra.TensorProduct.includeRight
          (R := RatFunc ℂ) (A := RatFunc Constants) (B := meroField Set.univ) x) := by
  change (1 : RatFunc Constants) ⊗ₜ[RatFunc ℂ] Differential.deriv x =
    tensorProductDerivation (K := RatFunc ℂ)
      ((1 : RatFunc Constants) ⊗ₜ[RatFunc ℂ] x)
  rw [tensorProductDerivation_tmul, Derivation.map_one_eq_zero,
    TensorProduct.zero_tmul, zero_add]

/-- Differential algebraicity of the Bessel order carrier produces a nonzero relation at the
actual scalar-extension point. -/
theorem exists_nonzero_besselScalarRelation_of_differentiallyAlgebraic
    (s : ℝ) (hs : 0 < s)
    (hDA : DifferentiallyAlgebraic (modifiedBesselKOrder s)) :
    ∃ P : DifferentialPolynomial Unit (RatFunc Constants), P ≠ 0 ∧
      differentialPolynomialEvalOver (K := RatFunc Constants)
        (fun _ : Unit => besselScalarY0 s hs) P = 0 := by
  have hyDA : DifferentialAlgebraicOver (RatFunc ℂ) (modifiedBesselKOrderMero s hs) := by
    simpa [modifiedBesselKOrderMero] using
      (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
        (analyticOnNhd_modifiedBesselKOrder hs) hDA)
  obtain ⟨n, Q, hQ, hQeval⟩ :=
    (differentialAlgebraicOver_iff_exists_finPoly
      (F := RatFunc ℂ) (modifiedBesselKOrderMero s hs)).mp hyDA
  let Qd : DifferentialPolynomial Unit (RatFunc ℂ) :=
    finiteJetScalarDifferentialPolynomial Q
  have hQd : Qd ≠ 0 := finiteJetScalarDifferentialPolynomial_ne_zero hQ
  have hQdEval : differentialPolynomialEvalOver (K := RatFunc ℂ)
      (fun _ : Unit => modifiedBesselKOrderMero s hs) Qd = 0 := by
    exact (finiteJetScalarDifferentialPolynomial_eval Q
      (modifiedBesselKOrderMero s hs)).trans hQeval
  let P : DifferentialPolynomial Unit (RatFunc Constants) :=
    differentialCoeffExtend (ι := Unit) (F := RatFunc ℂ) (L := RatFunc Constants) Qd
  have hP : P ≠ 0 := by
    intro hzero
    apply hQd
    apply MvPolynomial.map_injective (algebraMap (RatFunc ℂ) (RatFunc Constants))
      (ratFuncCoeffMap_injective (algebraMap ℂ Constants))
    simpa [P, differentialCoeffExtend] using hzero
  refine ⟨P, hP, ?_⟩
  rw [show differentialPolynomialEvalOver (K := RatFunc Constants)
      (fun _ : Unit => besselScalarY0 s hs) P =
      differentialPolynomialEvalOver (K := RatFunc ℂ)
        (fun _ : Unit => besselScalarY0 s hs) Qd by
    exact differentialPolynomialEvalOver_differentialCoeffExtend
      (F := RatFunc ℂ) (L := RatFunc Constants) (M := BesselScalarTensor)
      (fun _ : Unit => besselScalarY0 s hs) Qd]
  have hmap := evalOver_algHom (C := RatFunc ℂ)
    (Algebra.TensorProduct.includeRight :
      meroField Set.univ →ₐ[RatFunc ℂ] BesselScalarTensor)
    besselScalarIncludeRight_deriv
    (fun _ : Unit => modifiedBesselKOrderMero s hs) Qd
  rw [hQdEval, map_zero] at hmap
  simpa [besselScalarY0] using hmap.symm

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
