import GaloisForLFunctions.HTGeometry.MeromorphicPlaneTranslation

/-!
# The constants and polynomial evaluation in the meromorphic plane field

The complex constants embed in the field of meromorphic functions on the plane, making it a
`ℂ`-algebra in which polynomial evaluation is pointwise evaluation.  The Weierstrass `℘` of a period
lattice is transcendental over the constants there, because it is unbounded near a lattice point
while a nonzero polynomial has finitely many roots.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The constants of the meromorphic plane field. -/
noncomputable def constPlane : ℂ →+* MeromorphicPlane where
  toFun c := ofMeromorphic (fun _ => c) (fun z => MeromorphicAt.const c z)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem constPlane_injective : Function.Injective constPlane := by
  intro c d h
  have hev := (ofMeromorphic_eq_iff (f := fun _ : ℂ => c) (g := fun _ : ℂ => d)
    (fun z => MeromorphicAt.const c z) (fun z => MeromorphicAt.const d z)).mp h 0
  obtain ⟨z, hz⟩ := hev.exists
  exact hz

noncomputable instance : Algebra ℂ MeromorphicPlane := constPlane.toAlgebra

theorem algebraMap_plane (c : ℂ) :
    algebraMap ℂ MeromorphicPlane c = ofMeromorphic (fun _ => c) (fun z => MeromorphicAt.const c z) :=
  rfl

/-- A polynomial in a meromorphic function is meromorphic. -/
theorem meromorphicAt_polyEval {f : ℂ → ℂ} (hf : ∀ z, MeromorphicAt f z) (P : Polynomial ℂ)
    (z : ℂ) : MeromorphicAt (fun w => P.eval (f w)) z := by
  classical
  induction P using Polynomial.induction_on with
  | C a =>
      simp only [Polynomial.eval_C]
      exact MeromorphicAt.const a z
  | add p q hp hq =>
      simpa [Polynomial.eval_add] using hp.fun_add hq
  | monomial n a _ =>
      have hpow : MeromorphicAt (fun w => f w ^ (n + 1)) z := (hf z).pow _
      have := (MeromorphicAt.const a z).fun_mul hpow
      simpa [Polynomial.eval_mul] using this

/-- Polynomial evaluation at a germ is pointwise polynomial evaluation. -/
theorem aeval_ofMeromorphic (P : Polynomial ℂ) {f : ℂ → ℂ} (hf : ∀ z, MeromorphicAt f z) :
    Polynomial.aeval (ofMeromorphic f hf) P
      = ofMeromorphic (fun z => P.eval (f z)) (meromorphicAt_polyEval hf P) := by
  classical
  induction P using Polynomial.induction_on with
  | C a =>
      simp only [Polynomial.aeval_C, Polynomial.eval_C]
      rfl
  | add p q hp hq =>
      simp only [map_add, hp, hq, Polynomial.eval_add]
      rw [ofMeromorphic_add]
      rfl
  | monomial n a _ =>
      simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
      rfl

end GaloisForLFunctions.HTGeometry
