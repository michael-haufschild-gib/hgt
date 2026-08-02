import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreDivision
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# Cyclic quotients of the operator ring

For a nonzero operator `d` the cyclic left module `K[∂;δ] / K[∂;δ] d` has dimension `deg d` over
the coefficient field: division with remainder identifies it with the operators of order `< deg d`,
and those are freely spanned by `∂⁰, …, ∂^{deg d - 1}`.

This is the bridge between orders of operators and `K`-dimensions of torsion modules, which is what
turns a bounded chain of lattices into a bounded chain of Cartan vectors.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

/-- The operator with prescribed coefficients below order `n`. -/
def truncLT {n : ℕ} (c : Fin n → K) : DiffOp K := ∑ i : Fin n, mono (i : ℕ) (c i)

theorem coeff_truncLT {n : ℕ} (c : Fin n → K) (i : Fin n) :
    coeff (truncLT c) (i : ℕ) = c i := by
  classical
  rw [truncLT, ← coeffAddHom_apply (i : ℕ), map_sum]
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hji
    rw [coeffAddHom_apply, coeff_mono_of_ne]
    intro hcon
    exact hji (Fin.ext hcon)
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon
  · rw [coeffAddHom_apply, coeff_mono_self]

theorem coeff_truncLT_of_le {n : ℕ} (c : Fin n → K) {m : ℕ} (h : n ≤ m) :
    coeff (truncLT c) m = 0 := by
  classical
  rw [truncLT, ← coeffAddHom_apply m, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coeffAddHom_apply, coeff_mono_of_ne]
  intro hcon
  omega

theorem degree_truncLT_lt {n : ℕ} (c : Fin n → K) (hn : 0 < n) : degree (truncLT c) < n := by
  have hle : degree (truncLT c) ≤ n - 1 := by
    refine degree_le_iff.mpr fun m hm => ?_
    exact coeff_truncLT_of_le c (by omega)
  omega

theorem truncLT_injective {n : ℕ} : Function.Injective (truncLT (K := K) (n := n)) := by
  intro c d hcd
  funext i
  rw [← coeff_truncLT c i, ← coeff_truncLT d i, hcd]

theorem truncLT_coeff {n : ℕ} (p : DiffOp K) (h : degree p < n) :
    truncLT (fun i : Fin n => coeff p (i : ℕ)) = p := by
  ext m
  by_cases hm : m < n
  · exact coeff_truncLT (fun i : Fin n => coeff p (i : ℕ)) ⟨m, hm⟩
  · rw [coeff_truncLT_of_le _ (by omega), coeff_eq_zero_of_degree_lt (by omega)]

/-- Truncated operators, as a linear map. -/
def truncLTLin (n : ℕ) : (Fin n → K) →ₗ[K] DiffOp K where
  toFun := truncLT
  map_add' c d := by
    rw [truncLT, truncLT, truncLT, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, mono_add]
  map_smul' a c := by
    rw [RingHom.id_apply, truncLT, truncLT, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, smul_mono]

@[simp] theorem truncLTLin_apply (n : ℕ) (c : Fin n → K) : truncLTLin n c = truncLT c := rfl

/-- The left ideal of multiples of `d`, as a `K`-subspace. -/
def leftMultiples (d : DiffOp K) : Submodule K (DiffOp K) where
  carrier := {p | ∃ q, p = q * d}
  add_mem' := by
    rintro _ _ ⟨q₁, rfl⟩ ⟨q₂, rfl⟩
    exact ⟨q₁ + q₂, (add_mul' q₁ q₂ d).symm⟩
  zero_mem' := ⟨0, (zero_mul' d).symm⟩
  smul_mem' := by
    rintro a _ ⟨q, rfl⟩
    exact ⟨a • q, (smul_mul' a q d).symm⟩

theorem mem_leftMultiples {d p : DiffOp K} : p ∈ leftMultiples d ↔ ∃ q, p = q * d := Iff.rfl

/-- The empty truncation is zero. -/
@[simp] theorem truncLT_zero {n : ℕ} : truncLT (0 : Fin n → K) = 0 := by
  rw [truncLT]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Pi.zero_apply, mono_zero]

/-- Division with remainder identifies the cyclic quotient with the coefficient space of the
remainders. -/
def quotientLeftMultiplesEquiv {d : DiffOp K} (hd : d ≠ 0) :
    (Fin (degree d) → K) ≃ₗ[K] (DiffOp K ⧸ leftMultiples d) := by
  classical
  set f : (Fin (degree d) → K) →ₗ[K] (DiffOp K ⧸ leftMultiples d) :=
    (leftMultiples d).mkQ.comp (truncLTLin (degree d)) with hf
  have hsurj : Function.Surjective f := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H p =>
      obtain ⟨q, r, hqr, hr⟩ := exists_right_div hd p
      have htrunc : truncLT (fun i : Fin (degree d) => coeff r (i : ℕ)) = r := by
        rcases hr with hzero | hlt
        · rw [hzero]
          have hfun : (fun i : Fin (degree d) => coeff (0 : DiffOp K) (i : ℕ))
              = (0 : Fin (degree d) → K) := by
            funext i
            rw [coeff_zero]
            rfl
          rw [hfun, truncLT_zero]
        · exact truncLT_coeff r hlt
      refine ⟨fun i : Fin (degree d) => coeff r (i : ℕ), ?_⟩
      show (leftMultiples d).mkQ (truncLT fun i : Fin (degree d) => coeff r (i : ℕ)) = _
      rw [htrunc]
      refine (Submodule.Quotient.eq _).mpr ⟨-q, ?_⟩
      rw [hqr, neg_mul]
      abel
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_cases hd0 : degree d = 0
    · funext i
      have := i.isLt
      omega
    · have hmem : truncLT c ∈ leftMultiples d := by
        have hz : (leftMultiples d).mkQ (truncLT c) = 0 := hc
        exact (Submodule.Quotient.mk_eq_zero (leftMultiples d)).mp hz
      obtain ⟨q, hq⟩ := hmem
      have hzero : truncLT c = 0 := by
        by_contra hne
        have hq0 : q ≠ 0 := fun hq0 => hne (by rw [hq, hq0, zero_mul'])
        have hdeg : degree (truncLT c) = degree q + degree d := by
          rw [hq, degree_mul hq0 hd]
        have hlt := degree_truncLT_lt c (Nat.pos_of_ne_zero hd0)
        omega
      exact truncLT_injective (by rw [hzero, truncLT_zero])
  exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩

/-- **Dimension of a cyclic quotient.**  The cyclic module `K[∂;δ] / K[∂;δ] d` has dimension
`deg d` over the coefficient field. -/
theorem finrank_quotient_leftMultiples {d : DiffOp K} (hd : d ≠ 0) :
    Module.finrank K (DiffOp K ⧸ leftMultiples d) = degree d := by
  rw [← (quotientLeftMultiplesEquiv hd).finrank_eq]
  simp

theorem finiteDimensional_quotient_leftMultiples {d : DiffOp K} (hd : d ≠ 0) :
    FiniteDimensional K (DiffOp K ⧸ leftMultiples d) :=
  (quotientLeftMultiplesEquiv hd).finiteDimensional


/-- **Diagonal lattice pairs.**  The quotient of the free module by a diagonal family of left
ideals has dimension the sum of the orders. -/
theorem finrank_quotient_pi_leftMultiples {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → DiffOp K) (hd : ∀ i, d i ≠ 0) :
    Module.finrank K ((ι → DiffOp K) ⧸ Submodule.pi Set.univ fun i => leftMultiples (d i))
      = ∑ i, degree (d i) := by
  haveI : ∀ i, FiniteDimensional K (DiffOp K ⧸ leftMultiples (d i)) := fun i =>
    finiteDimensional_quotient_leftMultiples (hd i)
  have he : Module.finrank K ((ι → DiffOp K) ⧸ Submodule.pi Set.univ fun i => leftMultiples (d i))
      = Module.finrank K (∀ i : ι, DiffOp K ⧸ leftMultiples (d i)) :=
    (Submodule.quotientPi (R := K) (Ms := fun _ : ι => DiffOp K)
      (fun i => leftMultiples (d i))).finrank_eq
  rw [he, Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun i _ => finrank_quotient_leftMultiples (hd i)

end

end DiffOp

end GaloisForLFunctions.HTGeometry
