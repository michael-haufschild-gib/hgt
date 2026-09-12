import GaloisForLFunctions.RHTower.RouteEEntropyComplementPairStability

/-!
# Entropy-complement physical incidence and cutoff-fibre uniqueness

The entropy-complement low/rough decomposition has no latent multiplicity after projection to a
squarefree physical endpoint: separated support forces the unique intrinsic cutoff split.  The
two orientations of the pair-stable relation consequently collapse to one symmetric physical
endpoint relation.  Arbitrary symmetric weights on this relation give a symmetric raw incidence
whose nonzero edges reverse the Möbius sign, and its finite row mass is exactly a sum over physical
endpoints rather than over factorization histories.

This removes only cutoff-factorization collisions.  It assumes no local endpoint count, degree
regularity, column-load estimate, pair-switch dispersion, Möbius cancellation, or RH premise.
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset ArithmeticFunction

namespace RHTower

noncomputable section

/-! ## Exact cutoff-factor fibre -/

/-- A squarefree product with low support in the left factor and rough support in the right factor
has exactly the left factor as its intrinsic low prime support. -/
theorem routeE_lowPrimeFactors_mul_eq_left_of_cutoffSplit
    (P t m : ℕ) (htm : Squarefree (t * m))
    (htLow : ∀ p ∈ t.primeFactors, p ≤ P)
    (hmRough : ∀ p ∈ m.primeFactors, P < p) :
    routeELowPrimeFactors P (t * m) = t.primeFactors := by
  have ht0 : t ≠ 0 := left_ne_zero_of_mul htm.ne_zero
  have hm0 : m ≠ 0 := right_ne_zero_of_mul htm.ne_zero
  rw [routeELowPrimeFactors, Nat.primeFactors_mul ht0 hm0, Finset.filter_union]
  have htFilter : t.primeFactors.filter (fun p => p ≤ P) = t.primeFactors :=
    Finset.filter_eq_self.mpr htLow
  have hmFilter : m.primeFactors.filter (fun p => p ≤ P) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp
    exact Nat.not_le_of_lt (hmRough p hp)
  rw [htFilter, hmFilter, Finset.union_empty]

/-- The same separated squarefree product has exactly the right factor as its intrinsic rough
prime support. -/
theorem routeE_roughPrimeFactors_mul_eq_right_of_cutoffSplit
    (P t m : ℕ) (htm : Squarefree (t * m))
    (htLow : ∀ p ∈ t.primeFactors, p ≤ P)
    (hmRough : ∀ p ∈ m.primeFactors, P < p) :
    routeERoughPrimeFactors P (t * m) = m.primeFactors := by
  have ht0 : t ≠ 0 := left_ne_zero_of_mul htm.ne_zero
  have hm0 : m ≠ 0 := right_ne_zero_of_mul htm.ne_zero
  rw [routeERoughPrimeFactors, Nat.primeFactors_mul ht0 hm0, Finset.filter_union]
  have htFilter : t.primeFactors.filter (fun p => P < p) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp
    exact Nat.not_lt_of_ge (htLow p hp)
  have hmFilter : m.primeFactors.filter (fun p => P < p) = m.primeFactors :=
    Finset.filter_eq_self.mpr hmRough
  rw [htFilter, hmFilter, Finset.empty_union]

/-- Separated squarefree factors are recovered numerically by the intrinsic cutoff split. -/
theorem routeE_cutoffSplit_recovers_intrinsicParts
    (P t m : ℕ) (htm : Squarefree (t * m))
    (htLow : ∀ p ∈ t.primeFactors, p ≤ P)
    (hmRough : ∀ p ∈ m.primeFactors, P < p) :
    routeELowPart P (t * m) = t ∧ routeERoughPart P (t * m) = m := by
  have hsplit := Nat.squarefree_mul_iff.mp htm
  constructor
  · rw [routeELowPart,
      routeE_lowPrimeFactors_mul_eq_left_of_cutoffSplit P t m htm htLow hmRough,
      Nat.prod_primeFactors_of_squarefree hsplit.2.1]
  · rw [routeERoughPart,
      routeE_roughPrimeFactors_mul_eq_right_of_cutoffSplit P t m htm htLow hmRough,
      Nat.prod_primeFactors_of_squarefree hsplit.2.2]

/-- Prime support of the intrinsic low part is the cutoff-filtered endpoint support. -/
theorem routeE_primeFactors_lowPart_eq (P q : ℕ) :
    (routeELowPart P q).primeFactors = routeELowPrimeFactors P q := by
  unfold routeELowPart
  apply Nat.primeFactors_prod
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

/-- Prime support of the intrinsic rough part is the complementary endpoint support. -/
theorem routeE_primeFactors_roughPart_eq (P q : ℕ) :
    (routeERoughPart P q).primeFactors = routeERoughPrimeFactors P q := by
  unfold routeERoughPart
  apply Nat.primeFactors_prod
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

/-- A labelled low/rough factorization history over physical endpoint `q`. -/
def routeECutoffSeparatedSplit (P q t m : ℕ) : Prop :=
  Squarefree q ∧ t * m = q ∧
    (∀ p ∈ t.primeFactors, p ≤ P) ∧
    ∀ p ∈ m.primeFactors, P < p

/-- Every admissible labelled history is the intrinsic factor pair of its endpoint. -/
theorem routeE_cutoffSeparatedSplit_eq_intrinsic
    {P q t m : ℕ} (h : routeECutoffSeparatedSplit P q t m) :
    t = routeELowPart P q ∧ m = routeERoughPart P q := by
  rcases h with ⟨hq, hprod, htLow, hmRough⟩
  have htm : Squarefree (t * m) := by simpa [hprod] using hq
  have hrecover := routeE_cutoffSplit_recovers_intrinsicParts P t m htm htLow hmRough
  constructor
  · calc
      t = routeELowPart P (t * m) := hrecover.1.symm
      _ = routeELowPart P q := congrArg (routeELowPart P) hprod
  · calc
      m = routeERoughPart P (t * m) := hrecover.2.symm
      _ = routeERoughPart P q := congrArg (routeERoughPart P) hprod

/-- Every squarefree endpoint admits its intrinsic separated history. -/
theorem routeE_cutoffSeparatedSplit_intrinsic
    (P : ℕ) {q : ℕ} (hq : Squarefree q) :
    routeECutoffSeparatedSplit P q (routeELowPart P q) (routeERoughPart P q) := by
  refine ⟨hq, routeE_lowPart_mul_roughPart_eq_of_squarefree P hq, ?_, ?_⟩
  · intro p hp
    rw [routeE_primeFactors_lowPart_eq] at hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp
    rw [routeE_primeFactors_roughPart_eq] at hp
    exact (Finset.mem_filter.mp hp).2

/-- Sharp classification of the cutoff-factor fibre over `q`. -/
theorem routeE_cutoffSeparatedSplit_iff_intrinsic
    (P q t m : ℕ) :
    routeECutoffSeparatedSplit P q t m ↔
      Squarefree q ∧ t = routeELowPart P q ∧ m = routeERoughPart P q := by
  constructor
  · intro h
    exact ⟨h.1, (routeE_cutoffSeparatedSplit_eq_intrinsic h).1,
      (routeE_cutoffSeparatedSplit_eq_intrinsic h).2⟩
  · rintro ⟨hq, rfl, rfl⟩
    exact routeE_cutoffSeparatedSplit_intrinsic P hq

/-- Physical multiplication has at most one separated factorization history over each endpoint. -/
theorem routeE_cutoffSeparatedSplit_unique
    {P q t₁ m₁ t₂ m₂ : ℕ}
    (h₁ : routeECutoffSeparatedSplit P q t₁ m₁)
    (h₂ : routeECutoffSeparatedSplit P q t₂ m₂) :
    t₁ = t₂ ∧ m₁ = m₂ := by
  have hc₁ := routeE_cutoffSeparatedSplit_eq_intrinsic h₁
  have hc₂ := routeE_cutoffSeparatedSplit_eq_intrinsic h₂
  exact ⟨hc₁.1.trans hc₂.1.symm, hc₁.2.trans hc₂.2.symm⟩

/-! ## Physical endpoint relation -/

/-- Cutoff-free physical support left after the unique low/rough split is forgotten. -/
def routeEEntropyComplementPhysicalPairRelation
    (z : ℕ) (shell : ℕ → ℕ → Prop) (n q : ℕ) : Prop :=
  Squarefree n ∧ Squarefree q ∧
    routeEPrimeSupportFriable z n ∧ routeEPrimeSupportFriable z q ∧
    Nat.Coprime n q ∧ shell n q ∧
    (cardFactors q = cardFactors n + 1 ∨ cardFactors n = cardFactors q + 1)

/-- Symmetrization of the two oriented upward certificates. -/
def routeEEntropyComplementPairRelation
    (z : ℕ) (shell : ℕ → ℕ → Prop) (n q : ℕ) : Prop :=
  routeEEntropyComplementUpRelation z shell n q ∨
    routeEEntropyComplementUpRelation z shell q n

/-- With a symmetric shell, symmetrized certificates are exactly the physical endpoint relation.
The cutoff and labelled factor history disappear from support, though a chosen weight may still
depend on the intrinsic split. -/
theorem routeE_entropyComplement_pairRelation_iff_physical
    (z : ℕ) (shell : ℕ → ℕ → Prop)
    (hshell : ∀ a b, shell a b ↔ shell b a) (n q : ℕ) :
    routeEEntropyComplementPairRelation z shell n q ↔
      routeEEntropyComplementPhysicalPairRelation z shell n q := by
  constructor
  · rintro (h | h)
    · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.1, Or.inl h.2.2.2.2.2.2⟩
    · exact ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.1.symm,
        (hshell q n).mp h.2.2.2.2.2.1, Or.inr h.2.2.2.2.2.2⟩
  · rintro ⟨hn, hq, hfn, hfq, hcop, hs, hgrade | hgrade⟩
    · exact Or.inl ⟨hn, hq, hfn, hfq, hcop, hs, hgrade⟩
    · exact Or.inr ⟨hq, hn, hfq, hfn, hcop.symm, (hshell n q).mp hs, hgrade⟩

/-- Symmetrized certificate support is symmetric without further assumptions. -/
theorem routeE_entropyComplement_pairRelation_comm
    (z : ℕ) (shell : ℕ → ℕ → Prop) (n q : ℕ) :
    routeEEntropyComplementPairRelation z shell n q ↔
      routeEEntropyComplementPairRelation z shell q n := by
  exact or_comm

/-- Every physical pair edge reverses squarefree Möbius sign. -/
theorem routeE_entropyComplement_pairRelation_reverses_moebius
    (z : ℕ) (shell : ℕ → ℕ → Prop) {n q : ℕ}
    (h : routeEEntropyComplementPairRelation z shell n q) :
    (μ q : ℤ) = -(μ n : ℤ) := by
  rcases h with h | h
  · exact routeE_entropyComplement_up_reverses_moebius z shell h
  · have hrev := routeE_entropyComplement_up_reverses_moebius z shell h
    linarith

/-- No endpoint is paired with itself. -/
theorem routeE_entropyComplement_pairRelation_irrefl
    (z : ℕ) (shell : ℕ → ℕ → Prop) (n : ℕ) :
    ¬routeEEntropyComplementPairRelation z shell n n := by
  rintro (⟨_, _, _, _, _, _, hgrade⟩ | ⟨_, _, _, _, _, _, hgrade⟩) <;> omega

/-! ## Symmetric raw incidence and exact row mass -/

/-- Raw weighted physical incidence.  The weight is not required to ignore the intrinsic cutoff
split; symmetry is imposed separately when the incidence is used as an undirected base. -/
noncomputable def routeEEntropyComplementRawIncidence
    (z : ℕ) (shell : ℕ → ℕ → Prop) (W : ℕ → ℕ → ℝ) (n q : ℕ) : ℝ := by
  classical
  exact if routeEEntropyComplementPairRelation z shell n q then W n q else 0

theorem routeE_entropyComplementRawIncidence_nonneg
    (z : ℕ) (shell : ℕ → ℕ → Prop) (W : ℕ → ℕ → ℝ)
    (hW : ∀ a b, 0 ≤ W a b) (n q : ℕ) :
    0 ≤ routeEEntropyComplementRawIncidence z shell W n q := by
  classical
  simp only [routeEEntropyComplementRawIncidence]
  split_ifs
  · exact hW n q
  · exact le_rfl

theorem routeE_entropyComplementRawIncidence_comm
    (z : ℕ) (shell : ℕ → ℕ → Prop) (W : ℕ → ℕ → ℝ)
    (hW : ∀ a b, W a b = W b a) (n q : ℕ) :
    routeEEntropyComplementRawIncidence z shell W n q =
      routeEEntropyComplementRawIncidence z shell W q n := by
  classical
  by_cases hrel : routeEEntropyComplementPairRelation z shell n q
  · rw [routeEEntropyComplementRawIncidence, if_pos hrel,
      routeEEntropyComplementRawIncidence,
      if_pos ((routeE_entropyComplement_pairRelation_comm z shell n q).mp hrel), hW n q]
  · rw [routeEEntropyComplementRawIncidence, if_neg hrel,
      routeEEntropyComplementRawIncidence,
      if_neg (fun hrev =>
        hrel ((routeE_entropyComplement_pairRelation_comm z shell n q).mpr hrev))]

theorem routeE_entropyComplementRawIncidence_diag
    (z : ℕ) (shell : ℕ → ℕ → Prop) (W : ℕ → ℕ → ℝ) (n : ℕ) :
    routeEEntropyComplementRawIncidence z shell W n n = 0 := by
  classical
  simp [routeEEntropyComplementRawIncidence,
    routeE_entropyComplement_pairRelation_irrefl z shell n]

theorem routeE_entropyComplementRawIncidence_support_reverses_moebius
    (z : ℕ) (shell : ℕ → ℕ → Prop) (W : ℕ → ℕ → ℝ) {n q : ℕ}
    (h : routeEEntropyComplementRawIncidence z shell W n q ≠ 0) :
    (μ q : ℤ) = -(μ n : ℤ) := by
  classical
  by_cases hrel : routeEEntropyComplementPairRelation z shell n q
  · exact routeE_entropyComplement_pairRelation_reverses_moebius z shell hrel
  · exact (h (by simp [routeEEntropyComplementRawIncidence, hrel])).elim

/-- Finite raw row mass on a predeclared physical aperture. -/
def routeEEntropyComplementPhysicalRowMass
    (S : Finset ℕ) (z : ℕ) (shell : ℕ → ℕ → Prop)
    (W : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ S, routeEEntropyComplementRawIncidence z shell W n q

/-- Physical endpoints selected by the cutoff-free relation. -/
noncomputable def routeEEntropyComplementPhysicalTargets
    (S : Finset ℕ) (z : ℕ) (shell : ℕ → ℕ → Prop) (n : ℕ) : Finset ℕ := by
  classical
  exact S.filter fun q => routeEEntropyComplementPhysicalPairRelation z shell n q

/-- Exact row-mass identification after physical projection: one weighted sum over endpoints,
with no multiplicity from separated low/rough histories. -/
theorem routeE_entropyComplementPhysicalRowMass_eq_targetSum
    (S : Finset ℕ) (z : ℕ) (shell : ℕ → ℕ → Prop)
    (hshell : ∀ a b, shell a b ↔ shell b a)
    (W : ℕ → ℕ → ℝ) (n : ℕ) :
    routeEEntropyComplementPhysicalRowMass S z shell W n =
      ∑ q ∈ routeEEntropyComplementPhysicalTargets S z shell n, W n q := by
  classical
  rw [routeEEntropyComplementPhysicalRowMass, routeEEntropyComplementPhysicalTargets]
  calc
    (∑ q ∈ S, routeEEntropyComplementRawIncidence z shell W n q) =
        ∑ q ∈ S,
          if routeEEntropyComplementPhysicalPairRelation z shell n q then W n q else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [routeEEntropyComplementRawIncidence,
        routeE_entropyComplement_pairRelation_iff_physical z shell hshell]
    _ = ∑ q ∈ S.filter
          (fun q => routeEEntropyComplementPhysicalPairRelation z shell n q), W n q := by
      rw [Finset.sum_filter]

/-- With unit raw weights, row mass is exactly the number of physical adjacent-grade endpoints. -/
theorem routeE_entropyComplementPhysicalRowMass_one_eq_card
    (S : Finset ℕ) (z : ℕ) (shell : ℕ → ℕ → Prop)
    (hshell : ∀ a b, shell a b ↔ shell b a) (n : ℕ) :
    routeEEntropyComplementPhysicalRowMass S z shell (fun _ _ => 1) n =
      ((routeEEntropyComplementPhysicalTargets S z shell n).card : ℝ) := by
  rw [routeE_entropyComplementPhysicalRowMass_eq_targetSum S z shell hshell]
  simp

end

end RHTower
