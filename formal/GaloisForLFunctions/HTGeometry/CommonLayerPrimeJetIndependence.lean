import GaloisForLFunctions.HTGeometry.PrimeValuationLeadingEchelon

/-!
# Algebraic independence from a common valuation layer

The leading-echelon law separates finitely many prime-power sources by giving each a private
valuation coordinate.  A family of translates and derivative jets of a *single* source has no
such privacy: every member lives on the same valuation layers.  What separates them there is the
feature vector

`p ↦ (source coefficient at p) · (rotated prime clock at p)^(jet order)`,

and tail independence of that feature family — no nonzero linear functional annihilating a
cofinite prime tail — is exactly the input the prime-ray Jacobian criterion needs when the layer
exponent is held constant.  Arbitrary higher valuation layers remain unrestricted.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Matrix
open scoped Differential

noncomputable section

set_option maxHeartbeats 800000

/-- **Common-layer jet rectangle law.**  A finite family of positive-prime-power sources, each
read at one logarithmic jet order, is algebraically independent as soon as its first valuation
layer carries a tail-independent feature family.  No source needs a private valuation coordinate,
and the higher valuation layers are unrestricted. -/
theorem commonLayerJetRectangle_algebraicIndependent
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (g : I → ArithmeticFunction ℂ) (k : I → ℕ)
    (hsupport : ∀ i, SupportedOnPositivePrimePowers (g i))
    (htail : TailCoefficientIndependent
      (fun i : I => fun p : Nat.Primes => g i ((p : ℕ)) * rotatedPrimeLogClock p ^ (k i))) :
    AlgebraicIndependent ℂ (fun i : I => rotatedLogArithmeticJet (k i) (g i)) := by
  classical
  let A : Fin 1 → Type := fun _ => I
  letI (r : Fin 1) : Fintype (A r) := inferInstance
  letI (r : Fin 1) : DecidableEq (A r) := inferInstance
  let a : ∀ r, A r → Nat.Primes → ℂ := fun _ i p =>
    g i ((p : ℕ)) * rotatedPrimeLogClock p ^ (k i)
  have htail' : ∀ r, TailCoefficientIndependent (a r) := fun _ => htail
  obtain ⟨q, hq, _havoid, hdet⟩ :=
    cofinitePrimePowerPacket_of_injective_layerExponents 1 A (fun _ => 0)
      (fun x y _ => Subsingleton.elim x y) a htail' ∅ Set.finite_empty
  let J := Σ r : Fin 1, A r
  let exponent : J → ℕ := fun i => (fun _ : Fin 1 => 0) i.1
  let sourceJet : J → ArithmeticFunction ℂ := fun x => rotatedLogArithmeticJet (k x.2) (g x.2)
  let M : Matrix J J (ArithmeticFunction ℂ) := fun i j => primeDeriv (q i).1 (sourceJet j)
  have hMsupport : ∀ i j, SupportedOnPrimeRay (q i) (M i j) := by
    intro i j
    exact primeDeriv_rotatedLogArithmeticJet_supportedOnPrimeRay
      (g j.2) (hsupport j.2) (q i) (k j.2)
  have hcoeff :
      (fun i j => M i j ((q i : ℕ) ^ exponent i)) =
        primePowerBlockMatrix exponent
          (primePowerPacketCoefficientMatrix exponent
            (primePowerSigmaCoefficient a) q) := by
    funext i j
    simp only [M, sourceJet, exponent]
    rw [primeDeriv_rotatedLogArithmeticJet_apply_primePow]
    rw [primePowerBlockMatrix, if_pos rfl]
    simp only [primePowerPacketCoefficientMatrix, primePowerSigmaCoefficient, a]
    norm_num
    ring
  have hMdet : M.det ≠ 0 := by
    apply primeRayMatrix_det_ne_zero q hq exponent M hMsupport
    rw [hcoeff]
    exact hdet
  have hAI : AlgebraicIndependent ℂ sourceJet := by
    refine algebraicIndependent_of_domain_jacobian
      (K := ℂ) (R := ArithmeticFunction ℂ)
      sourceJet (fun i => primeDeriv (q i).1)
      (fun i => primeDeriv_add (q i).1)
      (fun i => primeDeriv_mul (q i).1 (q i).2)
      (fun i => primeDeriv_algebraMap (q i).1 (q i).2)
      M hMdet ?_
    intro i j
    rfl
  let f : I → J := fun i => ⟨0, i⟩
  have hf : Function.Injective f := by
    intro i j h
    have := congrArg Sigma.snd h
    simpa using this
  have hsub := hAI.comp f hf
  simpa only [Function.comp_apply, f, sourceJet] using! hsub

end

end GaloisForLFunctions.HTGeometry
