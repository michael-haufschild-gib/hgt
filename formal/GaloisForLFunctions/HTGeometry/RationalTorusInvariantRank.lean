import GaloisForLFunctions.HTGeometry.AlgebraicTorusFractionAction
import GaloisForLFunctions.HTGeometry.LaurentMonomialSpanAlgebraicity

/-!
# Transcendence-rank bound for rational torus invariants

A rational function fixed by coordinate scalings has a finite state field
generated algebraically by the exponent differences in its eigen-presentation.
Consequently its state transcendence degree is bounded by the rational rank of
the full scaling-annihilator lattice.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {r : ℕ}

/-- A scaling-invariant rational function lies in a finite algebraic state
field whose transcendence degree is bounded by any integer-character lattice
dominating the scaling-annihilator rank. -/
theorem exists_rationalInvariant_stateField_rank_le
    {S : Set (Fin r → ℂˣ)} {A : Set (Fin r → ℤ)}
    (hscaleRank : Module.rank ℚ
        (Submodule.span ℚ (intCharacterToRat '' scaleAnnihilator ℂ S)) ≤
      Module.rank ℤ (Submodule.span ℤ A))
    {z : FractionRing (MvPolynomial (Fin r) ℂ)}
    (hfix : ∀ u ∈ S, rationalTorusScaleEquiv u z = z) :
    ∃ K : IntermediateField ℂ (FractionRing (MvPolynomial (Fin r) ℂ)),
      Algebra.trdeg ℂ K ≤ Module.rank ℤ (Submodule.span ℤ A) ∧ z ∈ K := by
  classical
  let x := rationalTorusCoordinate (C := ℂ) (r := r)
  obtain ⟨d, P, Q, hd, hPQeq, hQchar, hPchar⟩ :=
    exists_rationalTorusScale_eigen_representation hfix
  let ι := ↥(P.support ∪ Q.support)
  let m : ι → (Fin r → ℤ) := fun e i => (e.1 i : ℤ) - (d i : ℤ)
  have hmAnn : Set.range m ⊆ scaleAnnihilator ℂ S := by
    rintro a ⟨e, rfl⟩ u hu
    have hchar : rationalScaleChar u e.1 = rationalScaleChar u d := by
      rcases Finset.mem_union.mp e.2 with heP | heQ
      · exact hPchar e.1 heP u hu
      · exact hQchar e.1 heQ u hu
    have hsplit : (∏ i, ((u i : ℂ)) ^ (m e i)) =
        rationalScaleChar u e.1 / rationalScaleChar u d := by
      rw [rationalScaleChar, rationalScaleChar, ← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun i _ => by
        rw [zpow_sub₀ (Units.ne_zero (u i)), zpow_natCast, zpow_natCast]
    have hne : rationalScaleChar u d ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact pow_ne_zero _ (Units.ne_zero (u i))
    rw [hsplit, hchar, div_self hne]
  obtain ⟨K, hKtr, hKmono⟩ :=
    exists_laurentMonomial_algebraicClosure_rank_le
      (F := ℂ) (E := FractionRing (MvPolynomial (Fin r) ℂ)) x
      (rationalTorusCoordinate_ne_zero (C := ℂ)) m
  have hrank : Module.rank ℚ
      (Submodule.span ℚ (intCharacterToRat '' Set.range m)) ≤
      Module.rank ℤ (Submodule.span ℤ A) := by
    exact (Submodule.rank_mono
      (Submodule.span_mono (Set.image_mono hmAnn))).trans hscaleRank
  have htr : Algebra.trdeg ℂ K ≤ Module.rank ℤ (Submodule.span ℤ A) :=
    hKtr.trans hrank
  have hmono : ∀ e ∈ P.support ∪ Q.support,
      laurentMonomial x (fun i => (e i : ℤ) - (d i : ℤ)) ∈ K := by
    intro e he
    exact hKmono ⟨e, he⟩
  have hx0 : ∀ i, x i ≠ 0 := rationalTorusCoordinate_ne_zero (C := ℂ)
  have key : ∀ W : MvPolynomial (Fin r) ℂ,
      W.support ⊆ P.support ∪ Q.support →
      ∃ w ∈ K, MvPolynomial.aeval x W =
        w * laurentMonomial x (fun i => (d i : ℤ)) := by
    intro W hW
    refine ⟨∑ e ∈ W.support,
        algebraMap ℂ (FractionRing (MvPolynomial (Fin r) ℂ))
            (MvPolynomial.coeff e W) *
          laurentMonomial x (fun i => (e i : ℤ) - (d i : ℤ)), ?_, ?_⟩
    · exact K.sum_mem fun e he => K.mul_mem
        (K.algebraMap_mem (MvPolynomial.coeff e W)) (hmono e (hW he))
    · rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun e _ => ?_
      have hsplit : laurentMonomial x (fun i => (e i : ℤ) - (d i : ℤ)) *
          laurentMonomial x (fun i => (d i : ℤ)) =
        laurentMonomial x (fun i => (e i : ℤ)) := by
        rw [← laurentMonomial_add hx0]
        congr 1
        funext i
        simp
      rw [mul_assoc, hsplit, laurentMonomial_natCast]
      congr 1
      exact (Finset.prod_subset (Finset.subset_univ e.support) fun i _ hi => by
        rw [Finsupp.notMem_support_iff.mp hi, pow_zero])
  obtain ⟨n, hnmem, hnP⟩ := key P (fun e he => Finset.mem_union_left _ he)
  obtain ⟨w, hwmem, hwQ⟩ := key Q (fun e he => Finset.mem_union_right _ he)
  have hmon0 : laurentMonomial x (fun i => (d i : ℤ)) ≠ 0 :=
    laurentMonomial_ne_zero hx0 _
  have hQ0 : MvPolynomial.aeval x Q ≠ 0 := by
    intro h
    have hQne : Q ≠ 0 := by
      intro hzero
      rw [hzero, MvPolynomial.support_zero] at hd
      exact Finset.notMem_empty d hd
    exact hQne ((algebraicIndependent_iff.mp
      (algebraicIndependent_rationalTorusCoordinate (C := ℂ) (r := r))) Q h)
  have hw0 : w ≠ 0 := by
    intro h
    apply hQ0
    rw [hwQ, h, zero_mul]
  have hcancel : z * w = n := by
    refine mul_right_cancel₀ hmon0 ?_
    rw [mul_assoc, ← hwQ, hPQeq, hnP]
  have hzeq : z = n / w := by
    rw [eq_div_iff hw0]
    exact hcancel
  refine ⟨K, htr, ?_⟩
  rw [hzeq]
  exact K.div_mem hnmem hwmem

end

end GaloisForLFunctions.HTGeometry
