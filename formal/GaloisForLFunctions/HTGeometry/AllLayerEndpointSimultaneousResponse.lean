import GaloisForLFunctions.HTGeometry.AllVertexEndpointSimultaneousResponse
import GaloisForLFunctions.HTGeometry.LocalExtensionMatrixChart

/-!
# Simultaneous endpoint response for every layer of a finite local alphabet

A single integer scale is used to place every new local layer on an
injectively coded affine shift line.  One nonzero polynomial then enforces
both simplicity of the complete product spectrum and nonvanishing of every
prescribed old-observer response, across all layers at once.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical injective natural-number code of a finite type. -/
def finiteLayerCode
    {ρ : Type*} [Fintype ρ] (r : ρ) : ℕ :=
  (Fintype.equivFin ρ r).val

theorem finiteLayerCode_injective
    {ρ : Type*} [Fintype ρ] :
    Function.Injective (finiteLayerCode : ρ → ℕ) := by
  intro r s hrs
  apply (Fintype.equivFin ρ).injective
  apply Fin.ext
  exact hrs

/-- Real layer shifts on one coded integer ray, normalized to vanish at the
chosen anchor layer. -/
def codedIntegerLayerShift
    {ρ : Type*} [Fintype ρ]
    (anchor : ρ) (n : ℕ) (r : ρ) : ℝ :=
  (n : ℝ) *
    ((finiteLayerCode r : ℝ) - finiteLayerCode anchor)

/-- Collision factor for one ordered pair of distinct product labels along
the coded shift ray. -/
def codedLayerCollisionPolynomial
    {I ρ : Type*} [Fintype ρ]
    (energy : I → ℝ)
    (p : {p : (I × ρ) × (I × ρ) // p.1 ≠ p.2}) :
    ℂ[X] :=
  Polynomial.C
      ((energy p.1.2.1 - energy p.1.1.1 : ℝ) : ℂ) -
    Polynomial.C
        (((finiteLayerCode p.1.1.2 : ℝ) -
          finiteLayerCode p.1.2.2 : ℝ) : ℂ) *
      Polynomial.X

theorem codedLayerCollisionPolynomial_ne_zero
    {I ρ : Type*} [Fintype ρ]
    (energy : I → ℝ) (hinj : Function.Injective energy)
    (p : {p : (I × ρ) × (I × ρ) // p.1 ≠ p.2}) :
    codedLayerCollisionPolynomial energy p ≠ 0 := by
  intro hzero
  by_cases hlayer : p.1.1.2 = p.1.2.2
  · have hold : p.1.1.1 ≠ p.1.2.1 := by
      intro h
      apply p.2
      exact Prod.ext h hlayer
    have hcoeff :=
      congrArg (fun P : ℂ[X] => P.coeff 0) hzero
    simp [codedLayerCollisionPolynomial, hlayer] at hcoeff
    have heq :
        energy p.1.2.1 = energy p.1.1.1 :=
      Complex.ofReal_injective (sub_eq_zero.mp hcoeff)
    exact hold (hinj heq).symm
  · have hcode :
        finiteLayerCode p.1.1.2 ≠
          finiteLayerCode p.1.2.2 :=
      fun h => hlayer (finiteLayerCode_injective h)
    have hcoeff :=
      congrArg (fun P : ℂ[X] => P.coeff 1) hzero
    simp [codedLayerCollisionPolynomial] at hcoeff
    exact hcode
      (Nat.cast_injective (sub_eq_zero.mp hcoeff).symm)

/-- Scaling a nonzero packet numerator by a nonzero layer-code difference
preserves nonzeroness. -/
theorem packetNumerator_comp_codedLayerScale_ne_zero
    {I ρ : Type*} [Fintype I] [DecidableEq I]
    [Fintype ρ]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (attachment observer : Matrix I I ℂ)
    {a g b : I} (hag : a ≠ g) (hgb : g ≠ b)
    (hattachment : attachment a g ≠ 0)
    (hobserver : observer g b ≠ 0)
    {anchor layer : ρ} (hlayer : layer ≠ anchor) :
    (distinctNodePacketNumerator
        (twoStepEndpointPacketPole energy a b)
        (twoStepEndpointPacketCoefficient
          attachment observer a b)).comp
      (Polynomial.C
          ((((finiteLayerCode layer : ℝ) -
            finiteLayerCode anchor : ℝ)) : ℂ) *
        Polynomial.X) ≠ 0 := by
  have hnum :=
    twoStepEndpointPacketNumerator_ne_zero
      energy hmax attachment observer hag hgb
      hattachment hobserver
  intro hzero
  rw [Polynomial.comp_eq_zero_iff] at hzero
  rcases hzero with hzero | ⟨_heval, hscale⟩
  · exact hnum hzero
  · have hcoeff :=
      congrArg (fun P : ℂ[X] => P.coeff 1) hscale
    simp at hcoeff
    exact hlayer
      (finiteLayerCode_injective
        (Nat.cast_injective (sub_eq_zero.mp hcoeff)))

/-- **All-layer simultaneous response law.** Fix an anchor layer in any
finite local alphabet.  Given finitely many nonzero two-step channels, each
assigned to an arbitrary nonanchor layer, one nonnegative integer scale
simultaneously:

* makes the entire product spectrum simple across every layer; and
* keeps every prescribed two-step response nonzero at its actual coded
  layer-shift difference.

This is one global shift vector, not pairwise retuning. -/
theorem exists_codedIntegerLayerShift_all_responses_ne_zero
    {I ρ J : Type*} [Fintype I] [DecidableEq I]
    [Fintype ρ] [DecidableEq ρ]
    [Fintype J]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (anchor : ρ) (layer : J → ρ)
    (hlayer : ∀ q, layer q ≠ anchor)
    (attachment : Matrix I I ℂ)
    (observer : J → Matrix I I ℂ)
    (a g b : J → I)
    (hag : ∀ q, a q ≠ g q)
    (hgb : ∀ q, g q ≠ b q)
    (hattachment : ∀ q, attachment (a q) (g q) ≠ 0)
    (hobserver : ∀ q, observer q (g q) (b q) ≠ 0) :
    ∃ n : ℕ,
      Function.Injective
        (layeredEnergy
          (fun i => (energy i : ℂ))
          (fun r => (codedIntegerLayerShift anchor n r : ℂ))) ∧
      ∀ q,
        twoStepEndpointPacketResponse energy
          attachment (observer q) (a q) (b q)
          ((codedIntegerLayerShift anchor n (layer q) : ℂ) -
            codedIntegerLayerShift anchor n anchor) ≠ 0 := by
  let collision : ℂ[X] :=
    ∏ p : {p : (I × ρ) × (I × ρ) // p.1 ≠ p.2},
      codedLayerCollisionPolynomial energy p
  let numerator : J → ℂ[X] := fun q =>
    distinctNodePacketNumerator
      (twoStepEndpointPacketPole energy (a q) (b q))
      (twoStepEndpointPacketCoefficient
        attachment (observer q) (a q) (b q))
  let scale : J → ℂ[X] := fun q =>
    Polynomial.C
        ((((finiteLayerCode (layer q) : ℝ) -
          finiteLayerCode anchor : ℝ)) : ℂ) *
      Polynomial.X
  let Q : ℂ[X] :=
    collision * ∏ q, (numerator q).comp (scale q)
  have hcollision : collision ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact codedLayerCollisionPolynomial_ne_zero
      energy (maximallyProjectiveEnergy_injective energy hmax) p
  have hscaled : ∀ q, (numerator q).comp (scale q) ≠ 0 := by
    intro q
    exact packetNumerator_comp_codedLayerScale_ne_zero
      energy hmax attachment (observer q)
      (hag q) (hgb q) (hattachment q) (hobserver q)
      (hlayer q)
  have hQ : Q ≠ 0 := by
    apply mul_ne_zero hcollision
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    exact hscaled q
  obtain ⟨n, _hnmem, hnQ⟩ :=
    GaloisForLFunctions.exists_mem_eval_ne_zero
      (b := fun n : ℕ => (n : ℂ))
      Nat.cast_injective hQ Set.infinite_univ
  have hcollisionEval : collision.eval (n : ℂ) ≠ 0 :=
    (mul_ne_zero_iff.mp (by
      simpa only [Q, eval_mul, eval_prod] using hnQ)).1
  have hscaledEval :
      ∀ q, ((numerator q).comp (scale q)).eval (n : ℂ) ≠ 0 := by
    have hprod :
        (∏ q, ((numerator q).comp (scale q)).eval (n : ℂ)) ≠ 0 :=
      (mul_ne_zero_iff.mp (by
        simpa only [Q, eval_mul, eval_prod] using hnQ)).2
    intro q
    exact Finset.prod_ne_zero_iff.mp hprod q (Finset.mem_univ q)
  have hinjective :
      Function.Injective
        (layeredEnergy
          (fun i => (energy i : ℂ))
          (fun r => (codedIntegerLayerShift anchor n r : ℂ))) := by
    intro x y hxy
    by_contra hne
    let p : {p : (I × ρ) × (I × ρ) // p.1 ≠ p.2} :=
      ⟨(x, y), hne⟩
    have hfactor :
        (codedLayerCollisionPolynomial energy p).eval (n : ℂ) ≠ 0 := by
      have hprod :
          (∏ p :
              {p : (I × ρ) × (I × ρ) // p.1 ≠ p.2},
            (codedLayerCollisionPolynomial energy p).eval
              (n : ℂ)) ≠ 0 := by
        simpa only [collision, eval_prod] using hcollisionEval
      exact Finset.prod_ne_zero_iff.mp hprod p (Finset.mem_univ p)
    apply hfactor
    simp only [codedLayerCollisionPolynomial, eval_sub, eval_C,
      eval_mul, eval_X]
    dsimp [p]
    change
      (energy x.1 : ℂ) +
          codedIntegerLayerShift anchor n x.2 =
        (energy y.1 : ℂ) +
          codedIntegerLayerShift anchor n y.2 at hxy
    simp only [codedIntegerLayerShift] at hxy
    push_cast at hxy ⊢
    linear_combination -hxy
  refine ⟨n, hinjective, ?_⟩
  intro q hresponse
  let z : ℂ :=
    (codedIntegerLayerShift anchor n (layer q) : ℂ) -
      codedIntegerLayerShift anchor n anchor
  have hz :
      z =
        (n : ℂ) *
          (((finiteLayerCode (layer q) : ℝ) -
            finiteLayerCode anchor : ℝ) : ℂ) := by
    simp [z, codedIntegerLayerShift]
  have hnumEval :
      (numerator q).eval z ≠ 0 := by
    have hs := hscaledEval q
    rw [eval_comp] at hs
    simpa only [scale, eval_mul, eval_C, eval_X, hz,
      mul_comm] using hs
  have havoid :
      ∀ j,
        z ≠ twoStepEndpointPacketPole
          energy (a q) (b q) j := by
    intro j hzpole
    cases j with
    | inl d =>
        have hcollision :
            layeredEnergy
                (fun i => (energy i : ℂ))
                (fun r =>
                  (codedIntegerLayerShift anchor n r : ℂ))
                (a q, layer q) =
              layeredEnergy
                (fun i => (energy i : ℂ))
                (fun r =>
                  (codedIntegerLayerShift anchor n r : ℂ))
                (d, anchor) := by
          simp only [layeredEnergy]
          simp only [z] at hzpole
          simp only [twoStepEndpointPacketPole] at hzpole
          push_cast at hzpole
          linear_combination hzpole
        have hpairs := hinjective hcollision
        exact (hlayer q) (congrArg Prod.snd hpairs)
    | inr d =>
        have hcollision :
            layeredEnergy
                (fun i => (energy i : ℂ))
                (fun r =>
                  (codedIntegerLayerShift anchor n r : ℂ))
                (d, layer q) =
              layeredEnergy
                (fun i => (energy i : ℂ))
                (fun r =>
                  (codedIntegerLayerShift anchor n r : ℂ))
                (b q, anchor) := by
          simp only [layeredEnergy]
          simp only [z] at hzpole
          simp only [twoStepEndpointPacketPole] at hzpole
          push_cast at hzpole
          linear_combination hzpole
        have hpairs := hinjective hcollision
        exact (hlayer q) (congrArg Prod.snd hpairs)
  apply hnumEval
  change
    (distinctNodePacketNumerator
      (twoStepEndpointPacketPole energy (a q) (b q))
      (twoStepEndpointPacketCoefficient
        attachment (observer q) (a q) (b q))).eval z = 0
  rw [distinctNodePacketNumerator_eval_eq_packet_mul_prod]
  · rw [show
      (∑ j,
        twoStepEndpointPacketCoefficient
            attachment (observer q) (a q) (b q) j /
          (twoStepEndpointPacketPole energy
              (a q) (b q) j - z)) =
        twoStepEndpointPacketResponse energy
          attachment (observer q) (a q) (b q) z by rfl,
      hresponse, zero_mul]
  · exact havoid

end

end GaloisForLFunctions.HTGeometry
