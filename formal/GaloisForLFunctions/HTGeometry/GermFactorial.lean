import GaloisForLFunctions.HTGeometry.GermDivisionRemainder
import GaloisForLFunctions.HTGeometry.GermLinearEquiv

/-!
# The ring of analytic germs is a unique factorization domain

Induction on the dimension.  In dimension zero the ring is a field.  For the step, a distinguished
polynomial of positive degree either is irreducible in `ℂ{z'}[X]` — and then prime, so its germ is
prime — or splits into two monic factors of strictly smaller degree, which are again distinguished;
strong induction on the degree therefore factors its germ into primes.

An arbitrary nonzero germ is carried by a linear change of coordinates to a regular one, which is a
unit times the germ of a distinguished polynomial; pulling the factorization back along the induced
ring isomorphism finishes the argument, because a ring isomorphism preserves primality.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Filter Topology

variable {n : ℕ}

/-- **Prime factorization of the germ of a distinguished polynomial.** -/
theorem exists_prime_factors_of_distPoly
    [UniqueFactorizationMonoid (AnalyticGerm (0 : Fin n → ℂ))] :
    ∀ d : ℕ, ∀ α : ℕ → AnalyticGerm (0 : Fin n → ℂ),
      (∀ j, j < d → germValueMap n (α j) = 0) →
      ∃ f : Multiset (AnalyticGerm (0 : Fin (n + 1) → ℂ)),
        (∀ b ∈ f, Prime b) ∧ f.prod = germEval n (distPoly d α) := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro α hzero
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · refine ⟨0, by simp, ?_⟩
      rw [Multiset.prod_zero, distPoly, lowDegreePoly, Finset.range_zero, Finset.sum_empty,
        pow_zero, add_zero, map_one]
    by_cases hirr : Irreducible (distPoly d α)
    · refine ⟨{germEval n (distPoly d α)}, ?_, by simp⟩
      intro b hb
      rw [Multiset.mem_singleton] at hb
      subst hb
      exact prime_germEval_of_prime hd hzero
        (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
    have hnu : ¬ IsUnit (distPoly d α) := by
      intro hU
      have hdeg := natDegree_eq_zero_of_isUnit hU
      rw [natDegree_distPoly] at hdeg
      omega
    obtain ⟨P, Q, hPQ, hPu, hQu⟩ :
        ∃ P Q : Polynomial (AnalyticGerm (0 : Fin n → ℂ)),
          distPoly d α = P * Q ∧ ¬ IsUnit P ∧ ¬ IsUnit Q := by
      by_contra hc
      refine hirr ⟨hnu, ?_⟩
      intro a b hab
      by_contra hd2
      rw [not_or] at hd2
      exact hc ⟨a, b, hab, hd2.1, hd2.2⟩
    obtain ⟨P', Q', hP'm, hQ'm, hP'Q', hPP', hQQ'⟩ :=
      exists_monic_factorization_germ (distPoly_monic d α) hPQ.symm
    have hP'u : ¬ IsUnit P' := fun hU => hPu ((hPP'.isUnit_iff).mpr hU)
    have hQ'u : ¬ IsUnit Q' := fun hU => hQu ((hQQ'.isUnit_iff).mpr hU)
    have hP'deg : 1 ≤ P'.natDegree := by
      by_contra hc
      have h0 : P'.natDegree = 0 := by omega
      exact hP'u (by rw [hP'm.natDegree_eq_zero.mp h0]; exact isUnit_one)
    have hQ'deg : 1 ≤ Q'.natDegree := by
      by_contra hc
      have h0 : Q'.natDegree = 0 := by omega
      exact hQ'u (by rw [hQ'm.natDegree_eq_zero.mp h0]; exact isUnit_one)
    have hsum : P'.natDegree + Q'.natDegree = d := by
      have := congrArg Polynomial.natDegree hP'Q'
      rwa [hP'm.natDegree_mul hQ'm, natDegree_distPoly] at this
    -- both factors are distinguished
    have hPdist : ∀ j, j < P'.natDegree → germValueMap n (P'.coeff j) = 0 :=
      coeff_eq_zero_of_monic_mul_eq_distPoly hP'm hQ'm hzero hP'Q'
    have hQdist : ∀ j, j < Q'.natDegree → germValueMap n (Q'.coeff j) = 0 :=
      coeff_eq_zero_of_monic_mul_eq_distPoly hQ'm hP'm hzero (by rw [mul_comm]; exact hP'Q')
    obtain ⟨fP, hfPp, hfPprod⟩ := ih P'.natDegree (by omega) (fun j => P'.coeff j) hPdist
    obtain ⟨fQ, hfQp, hfQprod⟩ := ih Q'.natDegree (by omega) (fun j => Q'.coeff j) hQdist
    refine ⟨fP + fQ, ?_, ?_⟩
    · intro b hb
      rcases Multiset.mem_add.mp hb with h | h
      · exact hfPp b h
      · exact hfQp b h
    · rw [Multiset.prod_add, hfPprod, hfQprod, ← map_mul, ← monic_eq_distPoly hP'm,
        ← monic_eq_distPoly hQ'm, hP'Q']

/-- **Prime factorization of an arbitrary nonzero germ.** -/
theorem exists_prime_factors_germ [UniqueFactorizationMonoid (AnalyticGerm (0 : Fin n → ℂ))]
    (x : AnalyticGerm (0 : Fin (n + 1) → ℂ)) (hx : x ≠ 0) :
    ∃ f : Multiset (AnalyticGerm (0 : Fin (n + 1) → ℂ)),
      (∀ b ∈ f, Prime b) ∧ Associated f.prod x := by
  classical
  obtain ⟨X0, hXA, hXeq⟩ := x.2
  have hxeq : x = analyticGermOf hXA := Subtype.ext hXeq.symm
  have hXne : ¬ X0 =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)] 0 := by
    intro hc
    refine hx ?_
    rw [hxeq]
    refine Subtype.ext ?_
    rw [analyticGermOf_val, ZeroMemClass.coe_zero]
    exact Germ.coe_eq.mpr hc
  obtain ⟨L, Y, hYA, hLeq, hYreg⟩ := exists_germLinearEquiv_regular hXA hXne
  obtain ⟨d, α, u, hu, hzero, hprep⟩ := germ_preparation_algebraic hYA hYreg
  obtain ⟨f, hfp, hfprod⟩ := exists_prime_factors_of_distPoly d α hzero
  set e := (germLinearEquiv L).symm with he
  refine ⟨f.map e, ?_, ?_⟩
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hb
    exact (MulEquiv.prime_iff (e : AnalyticGerm (0 : Fin (n + 1) → ℂ)
      ≃* AnalyticGerm (0 : Fin (n + 1) → ℂ))).mpr (hfp c hc)
  · have hLx : germLinearEquiv L (analyticGermOf hXA) = germEval n (distPoly d α) * u := by
      rw [hLeq, hprep, germEval_distPoly]
    have hxval : x = e (germEval n (distPoly d α) * u) := by
      rw [he, ← hLx, ← hxeq, RingEquiv.symm_apply_apply]
    refine ⟨hu.unit.map (e : AnalyticGerm (0 : Fin (n + 1) → ℂ)
      →* AnalyticGerm (0 : Fin (n + 1) → ℂ)), ?_⟩
    rw [hxval, map_mul, ← hfprod, ← map_multiset_prod]
    rfl

/-- **The ring of analytic germs at the origin of `ℂ^n` is a unique factorization domain.** -/
instance instUniqueFactorizationMonoidAnalyticGerm :
    ∀ n : ℕ, UniqueFactorizationMonoid (AnalyticGerm (0 : Fin n → ℂ))
  | 0 => by
      refine UniqueFactorizationMonoid.of_exists_prime_factors ?_
      intro a ha
      refine ⟨0, by simp, ?_⟩
      have hunit : IsUnit a := by
        rw [isUnit_analyticGerm_iff]
        intro hval
        refine ha ?_
        obtain ⟨g, hgA, hgeq⟩ := a.2
        have haeq : a = analyticGermOf hgA := Subtype.ext hgeq.symm
        rw [haeq, analyticGermValue_of hgA] at hval
        refine Subtype.ext ?_
        rw [haeq, analyticGermOf_val, ZeroMemClass.coe_zero]
        refine Germ.coe_eq.mpr ?_
        filter_upwards with w
        have hw : w = (0 : Fin 0 → ℂ) := Subsingleton.elim _ _
        rw [hw]
        exact hval
      rw [Multiset.prod_zero]
      exact (associated_one_iff_isUnit.mpr hunit).symm
  | (n + 1) => by
      haveI := instUniqueFactorizationMonoidAnalyticGerm n
      exact UniqueFactorizationMonoid.of_exists_prime_factors
        (fun a ha => exists_prime_factors_germ a ha)

end GaloisForLFunctions.HTGeometry
