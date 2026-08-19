import GaloisForLFunctions.HTGeometry.JetIntegerShiftRational
import GaloisForLFunctions.HTGeometry.IntegerCongruentShiftClasses

/-!
# Merging congruent shifts in a linear combination of digamma jets

Congruent shifts are algebraically dependent, so a polynomial in jets at colliding shifts can vanish
without being the zero polynomial.  The merge therefore has to be performed **linearly**, before any
polynomial is formed: a linear combination of jets at arbitrary shifts is a rational function plus a
linear combination of jets at pairwise incongruent representatives, with the coefficients of each
class added.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **A finite sum of quotients of polynomials is a single quotient.** -/
theorem exists_poly_finsetSum_div {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p q : ι → Polynomial ℂ) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, (∀ i ∈ s, (q i).eval z ≠ 0) →
      ∑ i ∈ s, (p i).eval z / (q i).eval z = P.eval z / (∏ i ∈ s, q i).eval z := by
  classical
  refine Finset.induction_on s ⟨0, fun z _ => by simp⟩ ?_
  rintro a s ha ⟨P, hP⟩
  refine ⟨p a * ∏ i ∈ s, q i + P * q a, fun z hz => ?_⟩
  have hqa : (q a).eval z ≠ 0 := hz a (Finset.mem_insert_self a s)
  have hsub : ∀ i ∈ s, (q i).eval z ≠ 0 := fun i hi => hz i (Finset.mem_insert_of_mem hi)
  have hprod : (∏ i ∈ s, q i).eval z ≠ 0 := by
    rw [Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr hsub
  rw [Finset.sum_insert ha, hP z hsub, Finset.prod_insert ha]
  simp only [Polynomial.eval_add, Polynomial.eval_mul]
  field_simp

variable {r : ℕ}

/-- **Merging congruent shifts in a linear combination of digamma jets.** -/
theorem exists_poly_digammaJet_sum_merge (nu : Fin r → ℂ) (cc : Fin r → ℂ) (n : ℕ) :
    ∃ (P Q : Polynomial ℂ), Q ≠ 0 ∧ ∀ z : ℂ, (∀ i : Fin r, ∀ j : ℤ, z + nu i ≠ (j : ℂ)) →
      Q.eval z ≠ 0 ∧
      ∑ i, cc i * iteratedDeriv n Complex.digamma (z + nu i)
        = P.eval z / Q.eval z
          + ∑ a : CongReps nu,
              (∑ i ∈ Finset.univ.filter fun i => toCongRep nu i = a, cc i)
                * iteratedDeriv n Complex.digamma (z + nu (a : Fin r)) := by
  classical
  have hstep : ∀ i : Fin r, ∃ (p q : Polynomial ℂ), q ≠ 0 ∧
      ∀ z : ℂ, (∀ j : ℤ, z + nu (toCongRep nu i : Fin r) ≠ (j : ℂ)) →
        q.eval z ≠ 0 ∧
        iteratedDeriv n Complex.digamma (z + nu i)
          = iteratedDeriv n Complex.digamma (z + nu (toCongRep nu i : Fin r))
            + p.eval z / q.eval z := by
    intro i
    obtain ⟨m, hm⟩ := exists_int_eq_lam_toCongRep nu i
    obtain ⟨p, q, hq, hpq⟩ :=
      exists_ratEval_jet_int_shift (nu (toCongRep nu i : Fin r)) n m
    refine ⟨p, q, hq, fun z hz => ?_⟩
    have hqz := (hpq z hz).1
    have hval := (hpq z hz).2
    have harg : z + nu i = z + (nu (toCongRep nu i : Fin r) + (m : ℂ)) := by
      linear_combination hm
    exact ⟨hqz, (congrArg (iteratedDeriv n Complex.digamma) harg).trans hval⟩
  choose p q hq hpq using hstep
  obtain ⟨P, hP⟩ := exists_poly_finsetSum_div (Finset.univ : Finset (Fin r))
    (fun i => Polynomial.C (cc i) * p i) q
  refine ⟨P, ∏ i, q i, Finset.prod_ne_zero_iff.mpr fun i _ => hq i, fun z hz => ?_⟩
  have hpole : ∀ i : Fin r, ∀ j : ℤ, z + nu (toCongRep nu i : Fin r) ≠ (j : ℂ) :=
    fun i => hz (toCongRep nu i : Fin r)
  have hqz : ∀ i : Fin r, (q i).eval z ≠ 0 := fun i => (hpq i z (hpole i)).1
  have hprodz : (∏ i, q i).eval z ≠ 0 := by
    rw [Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hqz i
  refine ⟨hprodz, ?_⟩
  have hsplit : ∀ i : Fin r, cc i * iteratedDeriv n Complex.digamma (z + nu i)
      = cc i * iteratedDeriv n Complex.digamma (z + nu (toCongRep nu i : Fin r))
        + (Polynomial.C (cc i) * p i).eval z / (q i).eval z := by
    intro i
    rw [(hpq i z (hpole i)).2]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    field_simp
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
    hP z fun i _ => hqz i]
  have hfib : ∑ a : CongReps nu,
      (∑ i ∈ Finset.univ.filter fun i => toCongRep nu i = a, cc i)
        * iteratedDeriv n Complex.digamma (z + nu (a : Fin r))
      = ∑ i : Fin r, cc i * iteratedDeriv n Complex.digamma (z + nu (toCongRep nu i : Fin r)) := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin r)) (fun i => toCongRep nu i)
      (fun i => cc i * iteratedDeriv n Complex.digamma (z + nu (toCongRep nu i : Fin r)))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hia : toCongRep nu i = a := (Finset.mem_filter.mp hi).2
    rw [hia]
  rw [hfib]
  ring

end

end GaloisForLFunctions.HTGeometry
