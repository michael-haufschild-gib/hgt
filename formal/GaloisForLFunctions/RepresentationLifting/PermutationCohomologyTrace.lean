import GaloisForLFunctions.RepresentationLifting.CohomologicalTrace
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Modular trace for transitive permutation representations

Equivariance makes the diagonal of an endomorphism constant on each group orbit.
For a finite transitive action, every endomorphism is traceless exactly when the
coefficient characteristic divides the orbit size. This extends the regular-module
trace mechanism in Scavia's Lemma 6.3 to permutation and coset representations.

In particular every endomorphism of the natural `F_p[S_p]`-module `F_p^p` is
traceless. Its scalar-line map followed by trace vanishes in every cohomological
degree. The coset classification applies to the coefficient modules used in
permutation Shapiro isomorphisms.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RepresentationLifting

universe u

variable {k G X : Type u} [Field k] [Group G] [MulAction G X]

/-- Permuting a basis permutes the corresponding coefficients. -/
theorem permutationAction_coeff_smul (g : G) (v : MonoidAlgebra k X) (x : X) :
    (Representation.ofMulAction k G X g v).coeff (g • x) = v.coeff x := by
  change (Finsupp.mapDomain (g • ·) v.coeff) (g • x) = v.coeff x
  exact Finsupp.mapDomain_apply (MulAction.injective g) v.coeff x

/-- The diagonal coefficient of an equivariant endomorphism is constant on orbits. -/
theorem permutationEndomorphism_diagonal_smul
    (T : Rep.ofMulAction k G X ⟶ Rep.ofMulAction k G X) (g : G) (x : X) :
    (T.hom (MonoidAlgebra.single (g • x) 1) : MonoidAlgebra k X).coeff (g • x) =
      (T.hom (MonoidAlgebra.single x 1) : MonoidAlgebra k X).coeff x := by
  have h := Rep.hom_comm_apply T g (MonoidAlgebra.single x 1)
  change T.hom (Representation.ofMulAction k G X g (MonoidAlgebra.single x 1)) =
    Representation.ofMulAction k G X g (T.hom (MonoidAlgebra.single x 1)) at h
  rw [Representation.ofMulAction_single] at h
  exact (congrArg (fun v : MonoidAlgebra k X => v.coeff (g • x)) h).trans
    (permutationAction_coeff_smul g _ x)

variable [Fintype X]

/-- Trace in the permutation basis is the sum of diagonal coefficients. -/
theorem permutationEndomorphism_trace_sum
    (T : Rep.ofMulAction k G X ⟶ Rep.ofMulAction k G X) :
    LinearMap.trace k (Rep.ofMulAction k G X) T.hom.toLinearMap =
      ∑ x : X, (T.hom (MonoidAlgebra.single x 1) : MonoidAlgebra k X).coeff x := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis X k)]
  change (∑ x : X, (LinearMap.toMatrix (MonoidAlgebra.basis X k)
    (MonoidAlgebra.basis X k) T.hom.toLinearMap) x x) = _
  apply Finset.sum_congr rfl
  intro x _
  rw [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply]
  rfl

variable [MulAction.IsPretransitive G X]

/-- On a transitive permutation module, trace is orbit size times any diagonal coefficient. -/
theorem transitivePermutationEndomorphism_trace
    (T : Rep.ofMulAction k G X ⟶ Rep.ofMulAction k G X) (x : X) :
    LinearMap.trace k (Rep.ofMulAction k G X) T.hom.toLinearMap =
      (Fintype.card X : k) * (T.hom (MonoidAlgebra.single x 1) : MonoidAlgebra k X).coeff x := by
  classical
  rw [permutationEndomorphism_trace_sum]
  have hdiag (y : X) :
      (T.hom (MonoidAlgebra.single y 1) : MonoidAlgebra k X).coeff y =
      (T.hom (MonoidAlgebra.single x 1) : MonoidAlgebra k X).coeff x := by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
    exact permutationEndomorphism_diagonal_smul T g x
  simp only [hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- All equivariant traces vanish exactly when the characteristic divides the orbit size. -/
theorem transitivePermutationEndomorphism_traces_zero_iff (p : ℕ) [CharP k p] :
    (∀ T : Rep.ofMulAction k G X ⟶ Rep.ofMulAction k G X,
      LinearMap.trace k (Rep.ofMulAction k G X) T.hom.toLinearMap = 0) ↔
      p ∣ Fintype.card X := by
  constructor
  · intro h
    have hid := h (𝟙 (Rep.ofMulAction k G X))
    change LinearMap.trace k (MonoidAlgebra k X) LinearMap.id = 0 at hid
    rw [LinearMap.trace_id, Module.finrank_eq_card_basis (MonoidAlgebra.basis X k)] at hid
    exact (CharP.cast_eq_zero_iff k p (Fintype.card X)).mp hid
  · intro hp T
    have hcard : (Fintype.card X : k) = 0 := (CharP.cast_eq_zero_iff k p _).mpr hp
    cases isEmpty_or_nonempty X with
    | inl hempty =>
      letI := hempty
      rw [permutationEndomorphism_trace_sum]
      simp
    | inr hnonempty =>
      obtain ⟨x⟩ := hnonempty
      rw [transitivePermutationEndomorphism_trace T x, hcard, zero_mul]

end GaloisForLFunctions.RepresentationLifting

namespace GaloisForLFunctions.RepresentationLifting

/-- The exact trace-vanishing boundary for a finite coset permutation module. -/
theorem cosetEndomorphism_traces_zero_iff {k G : Type u} [Field k] [Group G]
    (S : Subgroup G) [Fintype (G ⧸ S)] (p : ℕ) [CharP k p] :
    (∀ T : Rep.ofMulAction k G (G ⧸ S) ⟶ Rep.ofMulAction k G (G ⧸ S),
      LinearMap.trace k (Rep.ofMulAction k G (G ⧸ S)) T.hom.toLinearMap = 0) ↔
      p ∣ Fintype.card (G ⧸ S) :=
  transitivePermutationEndomorphism_traces_zero_iff p

/-- The natural permutation module on `q` points with coefficients modulo `q`. -/
abbrev modularPermutationModule (q : ℕ) : Rep (ZMod q) (Equiv.Perm (Fin q)) :=
  Rep.ofMulAction (ZMod q) (Equiv.Perm (Fin q)) (Fin q)

/-- Every endomorphism of the natural `p`-point permutation module over `F_p` is traceless. -/
theorem primePermutationModule_endomorphism_trace (p : ℕ) [Fact p.Prime]
    (T : modularPermutationModule p ⟶ modularPermutationModule p) :
    LinearMap.trace (ZMod p) (modularPermutationModule p) T.hom.toLinearMap = 0 := by
  apply (transitivePermutationEndomorphism_traces_zero_iff
    (k := ZMod p) (G := Equiv.Perm (Fin p)) (X := Fin p) p).mpr
  simp only [Fintype.card_fin, dvd_refl]

/-- Every endomorphism scalar line of the prime permutation module has zero cohomological trace. -/
theorem primePermutationModule_cohomologyTrace_zero (p : ℕ) [Fact p.Prime]
    (T : modularPermutationModule p ⟶ modularPermutationModule p) (n : ℕ) :
    (groupCohomology.functor (ZMod p) (Equiv.Perm (Fin p)) n).map (scalarHom T) ≫
        (groupCohomology.functor (ZMod p) (Equiv.Perm (Fin p)) n).map
          (endomorphismTrace (modularPermutationModule p)) = 0 := by
  rw [scalarHom_trace_cohomology, primePermutationModule_endomorphism_trace, zero_smul]
  rfl

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.transitivePermutationEndomorphism_traces_zero_iff
#print axioms GaloisForLFunctions.RepresentationLifting.primePermutationModule_cohomologyTrace_zero
