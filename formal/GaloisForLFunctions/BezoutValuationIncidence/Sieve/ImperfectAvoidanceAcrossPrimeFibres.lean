import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveWithTheMontgomeryVaughanConstant

/-!
# The quadratic cost of imperfect residue avoidance

Dahan's collision detector in Theorem 4.1 (arXiv:2611.08717) separates
forbidden and allowed residues. At degree one the full Fourier energy has
an exact decomposition: a signed discrepancy between the two groups and
their two internal variances. The sharp Farey large sieve then controls
heterogeneous collision rates without an upper bound on their count.
-/

noncomputable section
open Finset RHTower.Sieve
namespace GaloisForLFunctions.BezoutValuationIncidence.Imperfect

/-- Residue multiplicity as a real variable for the Fourier energy. -/
abbrev residueMass (q : ℕ) (A : Finset ℕ) (j : ℕ) : ℝ := residueCount q A j

/-- Number of members in the designated residue classes, counted with multiplicity. -/
def hits (q : ℕ) (A Ω : Finset ℕ) : ℝ := ∑ j ∈ Ω, residueMass q A j

/-- The nonconstant part of the Fourier energy modulo q. -/
def energy (q : ℕ+) (A : Finset ℕ) : ℝ :=
  ∑ j ∈ (univ : Finset (Fin (q : ℕ))).erase ⟨0,q.pos⟩,
    ‖∑ n ∈ A, circleFreq (((n*(j : ℕ) : ℕ) : ℝ)/(q : ℝ))‖^2

theorem energy_eq (q : ℕ+) (A : Finset ℕ) :
    energy q A = (q : ℝ)*(∑ j ∈ range (q : ℕ), (residueMass q A j)^2)-(A.card : ℝ)^2 := by
  have h := add_sum_erase (univ : Finset (Fin (q : ℕ)))
    (fun j => ‖∑ n ∈ A, circleFreq (((n*(j : ℕ) : ℕ) : ℝ)/(q : ℝ))‖^2)
    (mem_univ (⟨0,q.pos⟩ : Fin (q : ℕ)))
  rw [sum_full_expSum_sq q.pos A] at h
  change ‖∑ n ∈ A, circleFreq (((n*0 : ℕ) : ℝ)/(q : ℝ))‖^2 + energy q A = _ at h
  rw [expSum_zero] at h
  simpa using (eq_sub_of_add_eq' h)

/-- Unnormalized squared deviations from the average on a block. -/
def scatter (S : Finset ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ j ∈ S, (f j-(∑ i ∈ S, f i)/(S.card : ℝ))^2

private theorem scatter_identity (S : Finset ℕ) (f : ℕ → ℝ) (hS : S.Nonempty) :
    (∑ j ∈ S, (f j)^2) = scatter S f+(∑ j ∈ S, f j)^2/(S.card : ℝ) := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hS).ne'
  simp only [scatter,sub_sq,sum_add_distrib,sum_sub_distrib,← sum_mul,← mul_sum,
    sum_const,nsmul_eq_mul]
  field_simp
  ring

/-- The cost is determined by the total collision count and the size of the
designated set, independently of the distribution within either group. -/
def discrepancy (q : ℕ+) (A Ω : Finset ℕ) : ℝ :=
  ((q : ℝ)*hits q A Ω-(Ω.card : ℝ)*A.card)^2 / ((Ω.card : ℝ)*((q : ℝ)-Ω.card))

theorem energy_decomposition (q : ℕ+) (A Ω : Finset ℕ) (hΩ : Ω ⊆ range (q : ℕ))
    (hB : Ω.Nonempty) (hG : (range (q : ℕ) \ Ω).Nonempty) :
    energy q A = discrepancy q A Ω+(q : ℝ)*
      (scatter Ω (residueMass q A)+scatter (range (q : ℕ) \ Ω) (residueMass q A)) := by
  let G := range (q : ℕ) \ Ω
  let X : ℝ := Ω.card
  let Y : ℝ := G.card
  let b := hits q A Ω
  let g := hits q A G
  have hX : X ≠ 0 := by dsimp only [X]; exact_mod_cast (card_pos.mpr hB).ne'
  have hY : Y ≠ 0 := by dsimp only [Y,G]; exact_mod_cast (card_pos.mpr hG).ne'
  have hc : (q : ℝ)=X+Y := by
    have h := card_sdiff_add_card_eq_card hΩ
    rw [card_range] at h
    dsimp only [X,Y,G]
    exact_mod_cast (by omega : (q : ℕ)=Ω.card+(range (q : ℕ) \ Ω).card)
  have hm : (A.card : ℝ)=b+g := by
    calc
      (A.card : ℝ) = ∑ j ∈ range (q : ℕ), residueMass q A j := by
        simp only [residueMass,← Nat.cast_sum,sum_residueCount q.pos A]
      _ = g+b := (sum_sdiff hΩ (f := residueMass q A)).symm
      _ = b+g := add_comm _ _
  have hsq : (∑ j ∈ range (q : ℕ), (residueMass q A j)^2)=
      (scatter Ω (residueMass q A)+b^2/X)+(scatter G (residueMass q A)+g^2/Y) := by
    rw [← sum_sdiff hΩ (f := fun j => (residueMass q A j)^2),add_comm]
    rw [scatter_identity Ω _ hB,scatter_identity G _ hG]
    rfl
  rw [energy_eq,hsq]
  change (q : ℝ)*_-(A.card : ℝ)^2 =
    ((q : ℝ)*b-X*A.card)^2/(X*((q : ℝ)-X))+(q : ℝ)*_
  rw [hc,hm,add_sub_cancel_left]
  field_simp
  ring

/-- The discrepancy exhausts the Fourier energy exactly when both blocks
have constant residue multiplicities. -/
theorem sharp_iff (q : ℕ+) (A Ω : Finset ℕ) (hΩ : Ω ⊆ range (q : ℕ))
    (hB : Ω.Nonempty) (hG : (range (q : ℕ) \ Ω).Nonempty) :
    energy q A = discrepancy q A Ω ↔
      (∀ j ∈ Ω, residueMass q A j = hits q A Ω/(Ω.card : ℝ)) ∧
      (∀ j ∈ range (q : ℕ) \ Ω, residueMass q A j =
        hits q A (range (q : ℕ) \ Ω)/((range (q : ℕ) \ Ω).card : ℝ)) := by
  have hs (S : Finset ℕ) : 0 ≤ scatter S (residueMass q A) := sum_nonneg fun _ _ => sq_nonneg _
  have hz (S : Finset ℕ) : scatter S (residueMass q A)=0 ↔
      ∀ j ∈ S, residueMass q A j=hits q A S/(S.card : ℝ) := by
    simp only [scatter,sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _),sq_eq_zero_iff,sub_eq_zero,hits]
  rw [energy_decomposition q A Ω hΩ hB hG,add_eq_left,mul_eq_zero,or_iff_right (by positivity : (q : ℝ) ≠ 0),
    add_eq_zero_iff_of_nonneg (hs _) (hs _),hz,hz]

/-- The sharp large-sieve constant pays for all local collision discrepancies
simultaneously, even when the prescribed forbidden sets are frequently hit. -/
theorem large_sieve (N Q : ℕ) (hQ : 2≤Q) (A P : Finset ℕ) (hA : A ⊆ range N)
    (Ω : ℕ → Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p≤Q)
    (hΩ : ∀ p ∈ P, Ω p ⊆ range p ∧ (Ω p).Nonempty ∧ (range p \ Ω p).Nonempty) :
    (∑ p ∈ P.attach, discrepancy ⟨p.val,((hP p.val p.property).1.pos)⟩ A (Ω p.val)) ≤
      ((N : ℝ)+(Q : ℝ)^2-1)*A.card := by
  classical
  let F (p : ℕ) := (properFareySet Q).filter (fun x => x.2=p)
  let v (x : ℕ × ℕ) := ‖∑ n ∈ A, circleFreq ((n : ℝ)*((x.1 : ℝ)/x.2))‖^2
  have localBound (p : ↥P) :
      discrepancy ⟨p.val,(hP _ p.property).1.pos⟩ A (Ω p.val) ≤ ∑ x ∈ F p.val, v x := by
    let m : ℕ+ := ⟨p.val,(hP _ p.property).1.pos⟩
    have he := energy_decomposition m A (Ω p.val) (hΩ _ p.property).1
      (hΩ _ p.property).2.1 (hΩ _ p.property).2.2
    have hh : discrepancy m A (Ω p.val) ≤ energy m A := by
      rw [he]
      apply le_add_of_nonneg_right
      exact mul_nonneg (by positivity) (add_nonneg (sum_nonneg fun _ _ => sq_nonneg _)
        (sum_nonneg fun _ _ => sq_nonneg _))
    rw [show F p.val=(fareySet Q).filter (fun x => x.2=p.val) from properFareySet_fibre_prime (hP _ p.property).1]
    exact hh.trans_eq (sum_fareySet_fibre_eq (hP _ p.property).1 (hP _ p.property).2 A).symm
  have hd : (↑P : Set ℕ).PairwiseDisjoint F := by
    intro p _ r _ hpr
    apply disjoint_left.mpr
    intro x hp hr
    exact hpr ((mem_filter.mp hp).2.symm.trans (mem_filter.mp hr).2)
  have hsub : P.biUnion F ⊆ properFareySet Q := by
    intro x hx
    obtain ⟨p,_,hp⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp hp).1
  calc
    _ ≤ ∑ p ∈ P.attach, ∑ x ∈ F p.val, v x := sum_le_sum fun p _ => localBound p
    _ = ∑ x ∈ P.biUnion F, v x := by
      rw [sum_biUnion hd]
      exact sum_attach P (fun p => ∑ x ∈ F p, v x)
    _ ≤ ∑ x ∈ properFareySet Q, v x :=
      sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ ≤ _ := largeSieve_set_properFarey_sharp N hQ A hA

end GaloisForLFunctions.BezoutValuationIncidence.Imperfect

#print axioms GaloisForLFunctions.BezoutValuationIncidence.Imperfect.energy_eq
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Imperfect.energy_decomposition
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Imperfect.sharp_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Imperfect.large_sieve
