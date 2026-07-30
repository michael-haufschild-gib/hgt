import GaloisForLFunctions.HTGeometry.LocalSiteMobiusPhaseCharacterLaw
import GaloisForLFunctions.HTGeometry.SpectralCharacterReplicaHeightLaw

/-!
# Exact replica height of nondegenerate local Möbius characters

A Boolean site contrast supported on `s` genuinely changed sites has `2^s`
distinct phase monomials, half with positive and half with negative sign.
Consequently its exact minimum fidelity-replica order is `2^(s-1)`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every replica realization can be padded by adding the same dummy labels
to its positive and negative multisets.  Hence every order above the exact
positive mass realizes a balanced character. -/
theorem spectralCharacterReplicaRealizes_of_balanced_of_positiveMass_le
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {k : I → ℤ} (hbalanced : SpectralCharacterBalanced k)
    {m : ℕ} (hmass : spectralCharacterPositiveMass k ≤ m) :
    SpectralCharacterReplicaRealizes m k := by
  obtain ⟨p, q, hp, hq, hk⟩ :=
    spectralCharacterReplicaRealizes_positiveMass_of_balanced
      hbalanced
  let i₀ : I := Classical.choice ‹Nonempty I›
  let extra : I → ℕ :=
    Pi.single i₀ (m - spectralCharacterPositiveMass k)
  refine ⟨p + extra, q + extra, ?_, ?_, ?_⟩
  · change Finset.univ.sum (fun i => p i + extra i) = m
    rw [Finset.sum_add_distrib, hp]
    have hextra :
        ∑ i, extra i =
          m - spectralCharacterPositiveMass k := by
      simp [extra]
    rw [hextra]
    omega
  · change Finset.univ.sum (fun i => q i + extra i) = m
    rw [Finset.sum_add_distrib, hq]
    have hextra :
        ∑ i, extra i =
          m - spectralCharacterPositiveMass k := by
      simp [extra]
    rw [hextra]
    omega
  · intro i
    rw [hk i]
    change
      (p i : ℤ) - (q i : ℤ) =
        ((p i + extra i : ℕ) : ℤ) -
          ((q i + extra i : ℕ) : ℤ)
    push_cast
    ring

/-- Distinct Boolean subsets give distinct updated configurations when every
selected site is genuinely changed. -/
theorem dependentUpdateOnFinset_diff_injective_on_powerset
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hdistinct : ∀ v ∈ sites, alternative v ≠ x v) :
    ∀ d ∈ sites.powerset, ∀ e ∈ sites.powerset,
      dependentUpdateOnFinset x alternative (sites \ d) =
        dependentUpdateOnFinset x alternative (sites \ e) →
      d = e := by
  intro d hd e he hde
  have hdsub : d ⊆ sites := Finset.mem_powerset.mp hd
  have hesub : e ⊆ sites := Finset.mem_powerset.mp he
  ext v
  by_cases hvsites : v ∈ sites
  · constructor
    · intro hvd
      by_contra hve
      have hv :=
        congrFun hde v
      have hxeq :
          x v = alternative v := by
        simpa [dependentUpdateOnFinset, hvsites, hvd, hve] using hv
      exact (hdistinct v hvsites) hxeq.symm
    · intro hve
      by_contra hvd
      have hv :=
        congrFun hde v
      have haeq :
          alternative v = x v := by
        simpa [dependentUpdateOnFinset, hvsites, hvd, hve] using hv
      exact (hdistinct v hvsites) haeq
  · constructor
    · intro hvd
      exact False.elim (hvsites (hdsub hvd))
    · intro hve
      exact False.elim (hvsites (hesub hve))

/-- At a configuration selected by one Boolean subset, the local Möbius
coefficient is exactly the sign of that subset. -/
theorem siteMobiusIntegerCoefficient_update_eq_sign
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) (sites d : Finset V)
    (hd : d ∈ sites.powerset)
    (hdistinct : ∀ v ∈ sites, alternative v ≠ x v) :
    siteMobiusIntegerCoefficient x alternative sites
        (dependentUpdateOnFinset x alternative (sites \ d)) =
      (-1 : ℤ) ^ d.card := by
  unfold siteMobiusIntegerCoefficient
  rw [Finset.sum_eq_single d]
  · simp
  · intro e he hne
    have hconfig :
        dependentUpdateOnFinset x alternative (sites \ e) ≠
          dependentUpdateOnFinset x alternative (sites \ d) := by
      intro hed
      exact hne
        (dependentUpdateOnFinset_diff_injective_on_powerset
          x alternative sites hdistinct e he d hd hed)
    simp [hconfig]
  · exact fun hnot => False.elim (hnot hd)

/-- Pointwise positive mass is the sum of the positive Boolean signs.
Injectivity is what prevents opposite subsets from cancelling at one
configuration. -/
theorem siteMobiusIntegerCoefficient_toNat_eq_subsetSum
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hdistinct : ∀ v ∈ sites, alternative v ≠ x v)
    (config : ∀ v, A v) :
    (siteMobiusIntegerCoefficient
        x alternative sites config).toNat =
      ∑ d ∈ sites.powerset,
        if dependentUpdateOnFinset x alternative (sites \ d) = config
        then ((-1 : ℤ) ^ d.card).toNat else 0 := by
  by_cases hexists :
      ∃ d ∈ sites.powerset,
        dependentUpdateOnFinset x alternative (sites \ d) = config
  · obtain ⟨d, hd, hconfig⟩ := hexists
    subst config
    rw [siteMobiusIntegerCoefficient_update_eq_sign
      x alternative sites d hd hdistinct]
    rw [Finset.sum_eq_single d]
    · simp
    · intro e he hne
      have hconfig :
          dependentUpdateOnFinset x alternative (sites \ e) ≠
            dependentUpdateOnFinset x alternative (sites \ d) := by
        intro hed
        exact hne
          (dependentUpdateOnFinset_diff_injective_on_powerset
            x alternative sites hdistinct e he d hd hed)
      simp [hconfig]
    · exact fun hnot => False.elim (hnot hd)
  · have hnone :
        ∀ d ∈ sites.powerset,
          dependentUpdateOnFinset x alternative (sites \ d) ≠ config := by
      intro d hd hdc
      exact hexists ⟨d, hd, hdc⟩
    unfold siteMobiusIntegerCoefficient
    have hleft :
        (∑ d ∈ sites.powerset,
          if dependentUpdateOnFinset x alternative (sites \ d) = config
          then (-1 : ℤ) ^ d.card else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      simp [hnone d hd]
    have hright :
        (∑ d ∈ sites.powerset,
          if dependentUpdateOnFinset x alternative (sites \ d) = config
          then ((-1 : ℤ) ^ d.card).toNat else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      simp [hnone d hd]
    rw [hleft, hright]
    rfl

/-- Half of the subsets of a nonempty finite set have positive alternating
sign. -/
theorem sum_powerset_sign_toNat
    {V : Type*} [Fintype V] [DecidableEq V]
    (sites : Finset V) (hsites : sites.Nonempty) :
    ∑ d ∈ sites.powerset, ((-1 : ℤ) ^ d.card).toNat =
      2 ^ (sites.card - 1) := by
  let D := {d : Finset V // d ∈ sites.powerset}
  let sign : D → ℤ := fun d => (-1 : ℤ) ^ d.1.card
  have hbalanced : SpectralCharacterBalanced sign := by
    unfold SpectralCharacterBalanced
    change ∑ d : D, (-1 : ℤ) ^ d.1.card = 0
    have hattach :
        (∑ d : D, (-1 : ℤ) ^ d.1.card) =
          ∑ d ∈ sites.powerset, (-1 : ℤ) ^ d.card := by
      change
        (∑ d ∈ sites.powerset.attach, (-1 : ℤ) ^ d.1.card) =
          ∑ d ∈ sites.powerset, (-1 : ℤ) ^ d.card
      exact
        Finset.sum_attach sites.powerset
          (fun d => (-1 : ℤ) ^ d.card)
    rw [hattach]
    calc
      (∑ d ∈ sites.powerset, (-1 : ℤ) ^ d.card) =
          ∏ _v ∈ sites, ((1 : ℤ) - 1) := by
        simpa using
          (Finset.prod_sub (fun _ : V => (1 : ℤ))
            (fun _ : V => (1 : ℤ)) sites).symm
      _ = 0 := by
        rcases hsites with ⟨v, hv⟩
        exact Finset.prod_eq_zero hv (by ring)
  have hequal :
      (∑ d : D, (sign d).toNat) =
        ∑ d : D, (-sign d).toNat :=
    sum_toNat_eq_sum_neg_toNat_of_spectralCharacterBalanced
      hbalanced
  have htotal :
      (∑ d : D, (sign d).toNat) +
          (∑ d : D, (-sign d).toNat) =
        2 ^ sites.card := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ d : D, ((sign d).toNat + (-sign d).toNat)) =
          ∑ _d : D, 1 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Int.toNat_add_toNat_neg_eq_natAbs]
        simp [sign]
      _ = Fintype.card D := by simp
      _ = sites.powerset.card := by
        exact Fintype.card_coe sites.powerset
      _ = 2 ^ sites.card := by
        exact Finset.card_powerset sites
  have hpow :
      2 ^ sites.card = 2 * 2 ^ (sites.card - 1) := by
    have hcard :
        sites.card - 1 + 1 = sites.card :=
      Nat.sub_add_cancel hsites.card_pos
    conv_lhs => rw [← hcard]
    rw [pow_succ]
    ring
  have hpositive :
      (∑ d : D, (sign d).toNat) =
        2 ^ (sites.card - 1) := by
    rw [hequal, hpow] at htotal
    omega
  have hattach :
      (∑ d : D, (sign d).toNat) =
        ∑ d ∈ sites.powerset, ((-1 : ℤ) ^ d.card).toNat := by
    change
      (∑ d ∈ sites.powerset.attach,
          ((-1 : ℤ) ^ d.1.card).toNat) =
        ∑ d ∈ sites.powerset, ((-1 : ℤ) ^ d.card).toNat
    exact
      Finset.sum_attach sites.powerset
        (fun d => ((-1 : ℤ) ^ d.card).toNat)
  rw [hattach] at hpositive
  exact hpositive

/-- **Exact local replica-height law.** A nonempty Boolean Möbius phase
character on `s` genuinely changed sites first occurs at fidelity-replica
order `2^(s-1)`, and at no lower order. -/
theorem siteMobiusProjectiveCharacter_minimumReplica
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hsites : sites.Nonempty)
    (hdistinct : ∀ v ∈ sites, alternative v ≠ x v) :
    SpectralCharacterReplicaRealizes
        (2 ^ (sites.card - 1))
        (fun config =>
          (siteMobiusProjectiveCharacter
            x alternative sites hsites).1 config) ∧
      ∀ n,
        SpectralCharacterReplicaRealizes n
            (fun config =>
              (siteMobiusProjectiveCharacter
                x alternative sites hsites).1 config) →
          2 ^ (sites.card - 1) ≤ n := by
  have hmass :
      spectralCharacterPositiveMass
          (fun config =>
            (siteMobiusProjectiveCharacter
              x alternative sites hsites).1 config) =
        2 ^ (sites.card - 1) := by
    unfold spectralCharacterPositiveMass
    change
      (∑ config,
        (siteMobiusIntegerCoefficient
          x alternative sites config).toNat) =
        2 ^ (sites.card - 1)
    simp_rw [
      siteMobiusIntegerCoefficient_toNat_eq_subsetSum
        x alternative sites hdistinct]
    rw [Finset.sum_comm]
    simpa using sum_powerset_sign_toNat sites hsites
  have hbalanced :
      SpectralCharacterBalanced
        (fun config =>
            (siteMobiusProjectiveCharacter
              x alternative sites hsites).1 config) := by
    unfold SpectralCharacterBalanced
    calc
      (∑ config,
          (siteMobiusProjectiveCharacter
            x alternative sites hsites).1 config) =
          (siteMobiusProjectiveCharacter
            x alternative sites hsites).1.sum
              (fun _ m => m) := by
        symm
        rw [Finsupp.sum_fintype]
        intro config
        rfl
      _ = 0 :=
        (siteMobiusProjectiveCharacter
          x alternative sites hsites).2
  have hminimum :=
    spectralCharacterPositiveMass_eq_minimumReplica
      hbalanced
  rw [hmass] at hminimum
  exact hminimum

end

end GaloisForLFunctions.HTGeometry
