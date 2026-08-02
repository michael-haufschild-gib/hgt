import GaloisForLFunctions.HTGeometry.CoprimeSplit
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The split is as small as the error

Solving the linearised fibre step cannot create anything: if every coefficient of the prescribed
error lies in an ideal `J`, then so does every coefficient of the displacement pair that realises it.

The proof does not inspect the construction of the split at all.  Reducing the equation modulo `J`
leaves a split of the zero error over the quotient ring, where the monic factor is still monic and
the pair is still coprime — and there the split is *unique*, so it is zero.

This is the contraction estimate of the Newton iteration: it is what makes the error after `k` steps
lie in the `k`-th power of the ideal carrying the deformation.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {S : Type*} [CommRing S]

/-- **The displacement realising an error lies in every ideal the error lies in.** -/
theorem coprimeSplit_coeff_mem {m n : ℕ} {A B : S[X]} (hA : A.Monic)
    (hAdeg : A.natDegree = m) (hBdeg : B.natDegree ≤ n) (hm : 0 < m) (hn : 0 < n)
    (hcop : IsCoprime A B) (J : Ideal S) {E dP dQ : S[X]}
    (hE : ∀ i, E.coeff i ∈ J)
    (hdP : dP.natDegree < m) (hdQ : dQ.natDegree < n)
    (hsplit : dP * B + A * dQ = E) :
    (∀ i, dP.coeff i ∈ J) ∧ (∀ i, dQ.coeff i ∈ J) := by
  classical
  by_cases hJ : J = ⊤
  · subst hJ
    exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩
  haveI : Nontrivial (S ⧸ J) :=
    ⟨⟨1, 0, fun h => hJ ((Ideal.eq_top_iff_one J).2 (Ideal.Quotient.eq_zero_iff_mem.1 h))⟩⟩
  set f : S →+* S ⧸ J := Ideal.Quotient.mk J with hf
  have hmapE : Polynomial.map f E = 0 := by
    refine Polynomial.ext (fun i => ?_)
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hE i)
  have hmapsplit : Polynomial.map f dP * Polynomial.map f B
      + Polynomial.map f A * Polynomial.map f dQ = 0 := by
    rw [← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, hsplit, hmapE]
  have hAmap : (Polynomial.map f A).Monic := hA.map f
  have hAmapdeg : (Polynomial.map f A).natDegree = m := by
    rw [hA.natDegree_map f, hAdeg]
  have hBmapdeg : (Polynomial.map f B).natDegree ≤ n :=
    le_trans Polynomial.natDegree_map_le hBdeg
  have hcopmap : IsCoprime (Polynomial.map f A) (Polynomial.map f B) :=
    hcop.map (Polynomial.mapRingHom f)
  obtain ⟨p, -, huniq⟩ :=
    existsUnique_coprimeSplit hAmap hAmapdeg hBmapdeg hm hn hcopmap
      (E := (0 : (S ⧸ J)[X])) (by rw [Polynomial.natDegree_zero]; omega)
  have hzero : ((0 : (S ⧸ J)[X]), (0 : (S ⧸ J)[X])) = p :=
    huniq _ ⟨by rw [Polynomial.natDegree_zero]; omega,
      by rw [Polynomial.natDegree_zero]; omega, by rw [zero_mul, mul_zero, add_zero]⟩
  have hmapped : (Polynomial.map f dP, Polynomial.map f dQ) = p :=
    huniq _ ⟨lt_of_le_of_lt Polynomial.natDegree_map_le hdP,
      lt_of_le_of_lt Polynomial.natDegree_map_le hdQ, hmapsplit⟩
  have hdPzero : Polynomial.map f dP = 0 := congrArg Prod.fst (hmapped.trans hzero.symm)
  have hdQzero : Polynomial.map f dQ = 0 := congrArg Prod.snd (hmapped.trans hzero.symm)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [← Polynomial.coeff_map, hdPzero, Polynomial.coeff_zero]
  · refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [← Polynomial.coeff_map, hdQzero, Polynomial.coeff_zero]

end GaloisForLFunctions.HTGeometry
