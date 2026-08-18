import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Split finite algebras over a field and the nonvanishing of the discriminant

Let `K` be a field and `C` a commutative `K`-algebra with a basis indexed by `Fin n`.  This module
proves the two directions of

```text
C carries n jointly surjective K-algebra maps to K   ⟺   Algebra.discr K b ≠ 0
```

the backwards direction over an algebraically closed `K`.  Both directions pass through the
basis-free reformulation "the trace form is nondegenerate", so no change-of-basis computation is
needed.

* forward: the `n` maps assemble into an isomorphism `C ≃ₐ[K] (Fin n → K)`; the discriminant of the
  standard basis of a finite product of copies of `K` is `1`;
* backward: a nondegenerate trace form kills nilpotents, so `C` is reduced; a reduced Artinian ring
  is the product of its residue fields, and over an algebraically closed field each of those is `K`
  itself.

The point of the equivalence is that the left-hand side is what a covering-space argument consumes
while the right-hand side is a single ring element, hence transportable along any ring
homomorphism.
-/

namespace GaloisForLFunctions.HTGeometry

open Algebra

section PiTrace

variable {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]

/-- The algebra trace of a finite product of copies of a field is the sum of the coordinates. -/
theorem trace_pi_apply (x : ι → K) : Algebra.trace K (ι → K) x = ∑ i, x i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun K ι)]
  simp [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]

variable (K ι) in
/-- The discriminant of the standard basis of a finite product of copies of a field is `1`. -/
theorem discr_pi_basisFun : Algebra.discr K (Pi.basisFun K ι) = 1 := by
  rw [Algebra.discr_def]
  have h : Algebra.traceMatrix K (Pi.basisFun K ι) = 1 := by
    ext i j
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, trace_pi_apply]
    simp only [Pi.basisFun_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · simp [Pi.single_apply]
    · intro k _ hk
      simp [Pi.single_apply, hk]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [h, Matrix.det_one]

end PiTrace

section PiField

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- **Every `K`-algebra homomorphism out of a finite product of copies of `K` is a coordinate.** -/
theorem exists_eval_of_algHom_pi (g : (ι → K) →ₐ[K] K) : ∃ i, ∀ x : ι → K, g x = x i := by
  classical
  have hidem : ∀ i, g (Pi.single i 1) = 0 ∨ g (Pi.single i 1) = 1 := by
    intro i
    have hsq : g (Pi.single i 1) * g (Pi.single i 1) = g (Pi.single i 1) := by
      rw [← map_mul]
      congr 1
      ext j
      by_cases hj : j = i <;> simp [hj]
    have h2 : g (Pi.single i 1) * (g (Pi.single i 1) - 1) = 0 := by
      ring_nf; linear_combination hsq
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hsum : ∑ i, g (Pi.single i 1) = 1 := by
    rw [← map_sum, ← map_one g]
    congr 1
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hex : ∃ i, g (Pi.single i 1) = 1 := by
    by_contra hcon
    simp only [not_exists] at hcon
    have hall : ∀ i ∈ (Finset.univ : Finset ι), g (Pi.single i 1) = 0 := by
      intro i _
      rcases hidem i with h | h
      · exact h
      · exact absurd h (hcon i)
    rw [Finset.sum_congr rfl hall] at hsum
    simp at hsum
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, fun x => ?_⟩
  have hzero : ∀ j, j ≠ i → g (Pi.single j 1) = 0 := by
    intro j hj
    have h0 : (Pi.single i 1 : ι → K) * Pi.single j 1 = 0 := by
      ext k
      simp only [Pi.mul_apply, Pi.single_apply, Pi.zero_apply]
      by_cases hk : k = i
      · subst hk
        rw [if_pos rfl, if_neg (Ne.symm hj), mul_zero]
      · rw [if_neg hk, zero_mul]
    have hg := congrArg g h0
    rw [map_mul, map_zero, hi, one_mul] at hg
    exact hg
  have hx : x = ∑ j, x j • Pi.single j (1 : K) := by
    ext k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  conv_lhs => rw [hx]
  rw [map_sum, Finset.sum_eq_single i]
  · rw [map_smul, hi, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [map_smul, hzero j hj, smul_zero]
  · intro hi'
    exact absurd (Finset.mem_univ i) hi'

end PiField

section SplitAlgebra

variable {K C : Type*} [Field K] [CommRing C] [Algebra K C]

/-- Nonvanishing of the discriminant of a basis is the basis-free statement that the trace form is
nondegenerate. -/
theorem discr_ne_zero_iff_traceForm_nondegenerate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K C) :
    Algebra.discr K b ≠ 0 ↔ (Algebra.traceForm K C).Nondegenerate := by
  rw [Algebra.discr_def, Algebra.traceMatrix_of_basis b]
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).symm

/-- A nondegenerate trace form forces the algebra to be reduced: the trace of a nilpotent element
is nilpotent, hence zero in a field. -/
theorem isReduced_of_traceForm_nondegenerate
    (h : (Algebra.traceForm K C).Nondegenerate) : IsReduced C := by
  constructor
  intro x hx
  refine h.1 x ?_
  intro y
  rw [Algebra.traceForm_apply]
  have hxy : IsNilpotent (x * y) := (Commute.all x y).isNilpotent_mul_right hx
  have htr : IsNilpotent (Algebra.trace K C (x * y)) :=
    Algebra.isNilpotent_trace_of_isNilpotent hxy
  exact htr.eq_zero

/-- **A finite algebra with nondegenerate trace form over an algebraically closed field is the
product of copies of that field**, indexed by its maximal spectrum. -/
theorem nonempty_algEquiv_pi_of_traceForm_nondegenerate
    [IsAlgClosed K] [Module.Finite K C] (h : (Algebra.traceForm K C).Nondegenerate) :
    Nonempty (C ≃ₐ[K] (MaximalSpectrum C → K)) := by
  haveI : IsReduced C := isReduced_of_traceForm_nondegenerate h
  haveI : IsArtinianRing C := isArtinian_of_tower K inferInstance
  letI fld : ∀ I : MaximalSpectrum C, Field (C ⧸ I.asIdeal) :=
    fun I => Ideal.Quotient.field I.asIdeal
  have hfin : ∀ I : MaximalSpectrum C, Module.Finite K (C ⧸ I.asIdeal) := by
    intro I
    exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  have hbij : ∀ I : MaximalSpectrum C, Function.Bijective (algebraMap K (C ⧸ I.asIdeal)) := by
    intro I
    haveI := hfin I
    haveI : Algebra.IsIntegral K (C ⧸ I.asIdeal) := Algebra.IsIntegral.of_finite K _
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨((IsArtinianRing.equivPi C).restrictScalars K).trans
    (AlgEquiv.piCongrRight fun I =>
      (AlgEquiv.ofBijective (Algebra.ofId K (C ⧸ I.asIdeal)) (hbij I)).symm)⟩

/-- **Nonvanishing discriminant produces the split family.**  Over an algebraically closed field, a
finite algebra of rank `n` with nonzero discriminant carries exactly `n` algebra maps to the field,
they are jointly surjective, and there are no others. -/
theorem exists_algHom_family_of_discr_ne_zero
    [IsAlgClosed K] {n : ℕ} (b : Module.Basis (Fin n) K C) (h : Algebra.discr K b ≠ 0) :
    ∃ χ : Fin n → (C →ₐ[K] K),
      (Function.Surjective fun c : C => fun i => χ i c) ∧
      ∀ ψ : C →ₐ[K] K, ∃ i, ψ = χ i := by
  classical
  haveI : Module.Finite K C := Module.Finite.of_basis b
  have hnd : (Algebra.traceForm K C).Nondegenerate :=
    (discr_ne_zero_iff_traceForm_nondegenerate b).mp h
  haveI : IsReduced C := isReduced_of_traceForm_nondegenerate hnd
  haveI : IsArtinianRing C := isArtinian_of_tower K inferInstance
  obtain ⟨Φ⟩ := nonempty_algEquiv_pi_of_traceForm_nondegenerate hnd
  haveI : Fintype (MaximalSpectrum C) := Fintype.ofFinite _
  have hcard : Fintype.card (MaximalSpectrum C) = n := by
    have h1 : Module.finrank K C = n := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    have h2 : Module.finrank K (MaximalSpectrum C → K) = Fintype.card (MaximalSpectrum C) :=
      Module.finrank_fintype_fun_eq_card K
    rw [← h2, ← h1]
    exact (LinearEquiv.finrank_eq Φ.toLinearEquiv).symm
  set σ : Fin n ≃ MaximalSpectrum C := (Fintype.equivFinOfCardEq hcard).symm with hσ
  refine ⟨fun i => (Pi.evalAlgHom K (fun _ : MaximalSpectrum C => K) (σ i)).comp Φ.toAlgHom,
    ?_, ?_⟩
  · intro y
    refine ⟨Φ.symm (fun m => y (σ.symm m)), ?_⟩
    funext i
    simp
  · intro ψ
    obtain ⟨m, hm⟩ := exists_eval_of_algHom_pi (ψ.comp Φ.symm.toAlgHom)
    refine ⟨σ.symm m, ?_⟩
    ext c
    have hc : ψ c = Φ c m := by simpa using hm (Φ c)
    simp [hc]

/-- **The split family forces the discriminant to be nonzero.** -/
theorem discr_ne_zero_of_algHom_family
    {n : ℕ} (b : Module.Basis (Fin n) K C) (χ : Fin n → (C →ₐ[K] K))
    (hsurj : Function.Surjective fun c : C => fun i => χ i c) :
    Algebra.discr K b ≠ 0 := by
  classical
  haveI : Module.Finite K C := Module.Finite.of_basis b
  have hfr : Module.finrank K C = Module.finrank K (Fin n → K) := by
    rw [Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hinj : Function.Injective (AlgHom.pi χ) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
      (f := (AlgHom.pi χ).toLinearMap)).mpr hsurj
  let e : C ≃ₐ[K] (Fin n → K) := AlgEquiv.ofBijective (AlgHom.pi χ) ⟨hinj, hsurj⟩
  rw [discr_ne_zero_iff_traceForm_nondegenerate b,
    ← discr_ne_zero_iff_traceForm_nondegenerate
      ((Pi.basisFun K (Fin n)).map e.symm.toLinearEquiv)]
  have hcoe : ⇑((Pi.basisFun K (Fin n)).map e.symm.toLinearEquiv)
      = ⇑e.symm ∘ ⇑(Pi.basisFun K (Fin n)) := by
    funext i; rfl
  have h1 : Algebra.discr K (⇑((Pi.basisFun K (Fin n)).map e.symm.toLinearEquiv)) = 1 := by
    rw [hcoe, ← Algebra.discr_eq_discr_of_algEquiv _ e.symm]
    exact discr_pi_basisFun K (Fin n)
  rw [h1]
  exact one_ne_zero

end SplitAlgebra

end GaloisForLFunctions.HTGeometry
