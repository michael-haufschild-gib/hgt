import GaloisForLFunctions.HTGeometry.FiniteBlaschkeNumberOperator

/-!
# Energy in the complete Blaschke product basis

The maximal-domain number operator has an absolutely summable quadratic
form in its spectral coordinates. This is the energy of the original
vector, without a finite-mode approximation or an additional domain premise.
-/

noncomputable section
open scoped Classical InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {I : Type} [Fintype I]

/-- Parseval identifies the original quadratic form with the full occupation-energy sum. -/
theorem finiteBlaschkeNumberOperator_hasSum_energy
    (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) (c : I → ℝ) (a : ℝ)
    (x : (finiteBlaschkeNumberOperator q hq c a).domain) :
    HasSum (fun e => finiteBlaschkeEnergy q c a e *
      ‖(finiteBlaschkeBasis q hq).repr (x : FiniteNumberSpace I) e‖ ^ 2)
      (inner ℂ (x : FiniteNumberSpace I) (finiteBlaschkeNumberOperator q hq c a x)).re := by
  let B := finiteBlaschkeBasis q hq
  let A := finiteBlaschkeNumberOperator q hq c a
  have hcoord (e : I → ℕ) : B.repr (A x) e =
      (finiteBlaschkeEnergy q c a e : ℂ) * B.repr (x : FiniteNumberSpace I) e :=
    eigenbasis_graph_coordinates _ _ _
      (finiteBlaschkeNumberOperator_formalSelfAdjoint q hq c a)
      (finiteBlaschkeBasis_mem_domain q hq c a)
      (finiteBlaschkeNumberOperator_basis q hq c a) x e
  have hs := (B.hasSum_inner_mul_inner (x : FiniteNumberSpace I) (A x)).mapL Complex.reCLM
  change HasSum (fun e =>
    (inner ℂ (x : FiniteNumberSpace I) (B e) * inner ℂ (B e) (A x)).re) _ at hs
  have hterm (e : I → ℕ) :
      (inner ℂ (x : FiniteNumberSpace I) (B e) * inner ℂ (B e) (A x)).re =
        finiteBlaschkeEnergy q c a e * ‖B.repr (x : FiniteNumberSpace I) e‖ ^ 2 := by
    rw [← B.repr_apply_apply, hcoord]
    have hc : inner ℂ (x : FiniteNumberSpace I) (B e) =
        starRingEnd ℂ (B.repr (x : FiniteNumberSpace I) e) := by
      rw [B.repr_apply_apply, ← inner_conj_symm]
    rw [hc, mul_left_comm, RCLike.conj_mul]
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  simpa only [hterm] using hs

theorem finiteBlaschkeNumberOperator_energy_eq
    (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) (c : I → ℝ) (a : ℝ)
    (x : (finiteBlaschkeNumberOperator q hq c a).domain) :
    (inner ℂ (x : FiniteNumberSpace I) (finiteBlaschkeNumberOperator q hq c a x)).re =
      ∑' e, finiteBlaschkeEnergy q c a e *
        ‖(finiteBlaschkeBasis q hq).repr (x : FiniteNumberSpace I) e‖ ^ 2 :=
  (finiteBlaschkeNumberOperator_hasSum_energy q hq c a x).tsum_eq.symm

end GaloisForLFunctions.HTGeometry
