import GaloisForLFunctions.HTGeometry.RationalTorusInvariantRank

/-!
# Common rank-bounded state field for rational torus invariants

A finite family of rational functions invariant under one scaling set admits
one common toric state field.  Combining all exponent differences before
taking algebraic closure preserves the rank bound, unlike taking a compositum
of independently constructed state fields.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {r : ℕ} {ι : Type} [Fintype ι]

/-- A finite family of scaling-invariant rational functions lies in one common
state field with transcendence degree bounded by the scaling-annihilator rank. -/
theorem exists_rationalInvariant_family_stateField_rank_le
    {S : Set (Fin r → ℂˣ)} {A : Set (Fin r → ℤ)}
    (hscaleRank : Module.rank ℚ
        (Submodule.span ℚ (intCharacterToRat '' scaleAnnihilator ℂ S)) ≤
      Module.rank ℤ (Submodule.span ℤ A))
    (z : ι → FractionRing (MvPolynomial (Fin r) ℂ))
    (hfix : ∀ i u, u ∈ S → rationalTorusScaleEquiv u (z i) = z i) :
    ∃ K : IntermediateField ℂ (FractionRing (MvPolynomial (Fin r) ℂ)),
      Algebra.trdeg ℂ K ≤ Module.rank ℤ (Submodule.span ℤ A) ∧
        ∀ i, z i ∈ K := by
  classical
  let x := rationalTorusCoordinate (C := ℂ) (r := r)
  have hex : ∀ i, ∃ (d : Fin r →₀ ℕ) (P Q : MvPolynomial (Fin r) ℂ),
      d ∈ Q.support ∧
      z i * MvPolynomial.aeval x Q = MvPolynomial.aeval x P ∧
      (∀ e ∈ Q.support, ∀ u ∈ S,
        rationalScaleChar u e = rationalScaleChar u d) ∧
      (∀ e ∈ P.support, ∀ u ∈ S,
        rationalScaleChar u e = rationalScaleChar u d) := by
    intro i
    exact exists_rationalTorusScale_eigen_representation (hfix i)
  choose d P Q hd hPQeq hQchar hPchar using hex
  let κ := Σ i : ι, ↥((P i).support ∪ (Q i).support)
  let m : κ → (Fin r → ℤ) := fun e j =>
    (e.2.1 j : ℤ) - (d e.1 j : ℤ)
  have hmAnn : Set.range m ⊆ scaleAnnihilator ℂ S := by
    rintro a ⟨e, rfl⟩ u hu
    have hchar : rationalScaleChar u e.2.1 = rationalScaleChar u (d e.1) := by
      rcases Finset.mem_union.mp e.2.2 with heP | heQ
      · exact hPchar e.1 e.2.1 heP u hu
      · exact hQchar e.1 e.2.1 heQ u hu
    have hsplit : (∏ j, ((u j : ℂ)) ^ (m e j)) =
        rationalScaleChar u e.2.1 / rationalScaleChar u (d e.1) := by
      rw [rationalScaleChar, rationalScaleChar, ← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun j _ => by
        rw [zpow_sub₀ (Units.ne_zero (u j)), zpow_natCast, zpow_natCast]
    have hne : rationalScaleChar u (d e.1) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact pow_ne_zero _ (Units.ne_zero (u j))
    rw [hsplit, hchar, div_self hne]
  obtain ⟨K, hKtr, hKmono⟩ :=
    exists_laurentMonomial_algebraicClosure_rank_le
      (F := ℂ) (E := FractionRing (MvPolynomial (Fin r) ℂ)) x
      (rationalTorusCoordinate_ne_zero (C := ℂ)) m
  have hrank : Module.rank ℚ
      (Submodule.span ℚ (intCharacterToRat '' Set.range m)) ≤
      Module.rank ℤ (Submodule.span ℤ A) :=
    (Submodule.rank_mono
      (Submodule.span_mono (Set.image_mono hmAnn))).trans hscaleRank
  refine ⟨K, hKtr.trans hrank, ?_⟩
  intro i
  have hmono : ∀ e ∈ (P i).support ∪ (Q i).support,
      laurentMonomial x (fun j => (e j : ℤ) - (d i j : ℤ)) ∈ K := by
    intro e he
    exact hKmono ⟨i, ⟨e, he⟩⟩
  have hx0 : ∀ j, x j ≠ 0 := rationalTorusCoordinate_ne_zero (C := ℂ)
  have key : ∀ W : MvPolynomial (Fin r) ℂ,
      W.support ⊆ (P i).support ∪ (Q i).support →
      ∃ w ∈ K, MvPolynomial.aeval x W =
        w * laurentMonomial x (fun j => (d i j : ℤ)) := by
    intro W hW
    refine ⟨∑ e ∈ W.support,
        algebraMap ℂ (FractionRing (MvPolynomial (Fin r) ℂ))
            (MvPolynomial.coeff e W) *
          laurentMonomial x (fun j => (e j : ℤ) - (d i j : ℤ)), ?_, ?_⟩
    · exact K.sum_mem fun e he => K.mul_mem
        (K.algebraMap_mem (MvPolynomial.coeff e W)) (hmono e (hW he))
    · rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun e _ => ?_
      have hsplit : laurentMonomial x (fun j => (e j : ℤ) - (d i j : ℤ)) *
          laurentMonomial x (fun j => (d i j : ℤ)) =
        laurentMonomial x (fun j => (e j : ℤ)) := by
        rw [← laurentMonomial_add hx0]
        congr 1
        funext j
        simp
      rw [mul_assoc, hsplit, laurentMonomial_natCast]
      congr 1
      exact (Finset.prod_subset (Finset.subset_univ e.support) fun j _ hj => by
        rw [Finsupp.notMem_support_iff.mp hj, pow_zero])
  obtain ⟨n, hnmem, hnP⟩ :=
    key (P i) (fun e he => Finset.mem_union_left _ he)
  obtain ⟨w, hwmem, hwQ⟩ :=
    key (Q i) (fun e he => Finset.mem_union_right _ he)
  have hmon0 : laurentMonomial x (fun j => (d i j : ℤ)) ≠ 0 :=
    laurentMonomial_ne_zero hx0 _
  have hQ0 : MvPolynomial.aeval x (Q i) ≠ 0 := by
    intro h
    have hQne : Q i ≠ 0 := by
      intro hzero
      have hdi := hd i
      rw [hzero, MvPolynomial.support_zero] at hdi
      exact Finset.notMem_empty (d i) hdi
    exact hQne ((algebraicIndependent_iff.mp
      (algebraicIndependent_rationalTorusCoordinate (C := ℂ) (r := r))) (Q i) h)
  have hw0 : w ≠ 0 := by
    intro h
    apply hQ0
    rw [hwQ, h, zero_mul]
  have hcancel : z i * w = n := by
    refine mul_right_cancel₀ hmon0 ?_
    rw [mul_assoc, ← hwQ, hPQeq i, hnP]
  have hzeq : z i = n / w := by
    rw [eq_div_iff hw0]
    exact hcancel
  rw [hzeq]
  exact K.div_mem hnmem hwmem

end

end GaloisForLFunctions.HTGeometry
