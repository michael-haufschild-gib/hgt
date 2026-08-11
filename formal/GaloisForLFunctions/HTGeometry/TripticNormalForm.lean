import GaloisForLFunctions.HTGeometry.TripticGammaCorrection
import GaloisForLFunctions.HTGeometry.EllipticGammaSourceGermConstraint
import GaloisForLFunctions.HTGeometry.TripticKernelDifferentialAlgebraicity

/-!
# The triptic normal form, and the realization of every divisor datum

Subtracting the gamma correction from a mixed-constraint source cancels its orbital divisor at every
base point and every order: on a class represented in the finite set of boundary pole classes the
correction reproduces the divisor exactly, off such a class both divisors vanish, and above the
order bound of the boundary function both vanish again.  The difference is again a mixed-constraint
source, because every gamma jet is exactly `1`-periodic and has a constant mixed difference, so the
kernel theorem applies to it.

This is the normal form `F - R(F)Ψ ∈ Mer_DA`, together with the augmentation law: the mixed constant
of the source is exactly the constant carried by the zeroth-order slice of its own correction.  In
the opposite direction every prescribed divisor datum is realized inside the class by an explicit
jet combination, which is the surjectivity half of the completeness theorem.

* `mixedConstGerm_jetCombination`, `periodicOneGerm_jetCombination`;
* `exists_gammaCorrection_vanishing_divisor`;
* `exists_gammaCorrection_differentiallyAlgebraic`;
* `exists_mem_class_with_prescribed_divisor`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Germ constraints are linear -/

theorem mixedConstGerm_add {F G : ℂ → ℂ} {τ σ c d : ℂ} (hF : MixedConstGerm F τ σ c)
    (hG : MixedConstGerm G τ σ d) : MixedConstGerm (F + G) τ σ (c + d) := by
  intro z
  filter_upwards [hF z, hG z] with w h1 h2
  simp only [Pi.add_apply]
  linear_combination h1 + h2

theorem mixedConstGerm_sub {F G : ℂ → ℂ} {τ σ c d : ℂ} (hF : MixedConstGerm F τ σ c)
    (hG : MixedConstGerm G τ σ d) : MixedConstGerm (fun z ↦ F z - G z) τ σ (c - d) := by
  intro z
  filter_upwards [hF z, hG z] with w h1 h2
  linear_combination h1 - h2

theorem mixedConstGerm_const_mul {F : ℂ → ℂ} {τ σ c : ℂ} (hF : MixedConstGerm F τ σ c) (k : ℂ) :
    MixedConstGerm (fun z ↦ k * F z) τ σ (k * c) := by
  intro z
  filter_upwards [hF z] with w h
  linear_combination k * h

theorem mixedConstGerm_zero (τ σ : ℂ) : MixedConstGerm (0 : ℂ → ℂ) τ σ 0 := by
  intro z
  filter_upwards with w
  simp

theorem mixedConstGerm_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (c : ι → ℂ) {τ σ : ℂ}
    (h : ∀ i ∈ s, MixedConstGerm (f i) τ σ (c i)) :
    MixedConstGerm (∑ i ∈ s, f i) τ σ (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using mixedConstGerm_zero τ σ
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact mixedConstGerm_add (h i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

theorem periodicOneGerm_add {F G : ℂ → ℂ} (hF : PeriodicOneGerm F) (hG : PeriodicOneGerm G) :
    PeriodicOneGerm (F + G) := by
  intro z
  filter_upwards [hF z, hG z] with w h1 h2
  simp only [Pi.add_apply]
  rw [h1, h2]

theorem periodicOneGerm_sub {F G : ℂ → ℂ} (hF : PeriodicOneGerm F) (hG : PeriodicOneGerm G) :
    PeriodicOneGerm (fun z ↦ F z - G z) := by
  intro z
  filter_upwards [hF z, hG z] with w h1 h2
  rw [h1, h2]

theorem periodicOneGerm_const_mul {F : ℂ → ℂ} (hF : PeriodicOneGerm F) (k : ℂ) :
    PeriodicOneGerm (fun z ↦ k * F z) := by
  intro z
  filter_upwards [hF z] with w h
  rw [h]

theorem periodicOneGerm_zero : PeriodicOneGerm (0 : ℂ → ℂ) := by
  intro z
  filter_upwards with w
  simp

theorem periodicOneGerm_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, PeriodicOneGerm (f i)) : PeriodicOneGerm (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using periodicOneGerm_zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact periodicOneGerm_add (h i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-! ### The constraints of a jet combination -/

/-- The mixed constant of a gamma jet: only the zeroth jet carries one. -/
def gammaJetConst (j : ℕ) : ℂ := if j = 0 then -(2 * (Real.pi : ℂ) * Complex.I) else 0

theorem mixedConstGerm_gammaJetSource {τ σ : ℂ} (hτ : 0 < τ.im) (hσ : 0 < σ.im) (g : ℂ) (j : ℕ) :
    MixedConstGerm (gammaJetSource τ σ g j) τ σ (gammaJetConst j) := by
  cases j with
  | zero => simpa [gammaJetConst] using mixedConstGerm_gammaJetSource_zero hτ hσ g
  | succ n => simpa [gammaJetConst] using mixedConstGerm_gammaJetSource_succ hτ hσ g n

/-- The mixed constant of a jet combination. -/
def jetCombinationConst (c : ℂ → ℕ → ℂ) (P : Finset ℂ) (J : ℕ) : ℂ :=
  ∑ j ∈ Finset.range J, ∑ q ∈ P, c q j * gammaJetConst j

/-- The mixed constant of the correction of a source. -/
def gammaCorrectionConst (τ σ : ℂ) (F : ℂ → ℂ) (P : Finset ℂ) (J : ℕ) : ℂ :=
  jetCombinationConst (gammaCorrectionCoeff τ σ F P) P J

theorem periodicOneGerm_jetCombination (τ σ : ℂ) (c : ℂ → ℕ → ℂ) (P : Finset ℂ) (J : ℕ) :
    PeriodicOneGerm (jetCombination τ σ c P J) := by
  rw [jetCombination]
  exact periodicOneGerm_finsetSum _ _ fun j _ ↦ periodicOneGerm_finsetSum _ _ fun q _ ↦
    periodicOneGerm_const_mul (periodicOneGerm_gammaJetSource τ σ q j) _

theorem mixedConstGerm_jetCombination {τ σ : ℂ} (hτ : 0 < τ.im) (hσ : 0 < σ.im) (c : ℂ → ℕ → ℂ)
    (P : Finset ℂ) (J : ℕ) :
    MixedConstGerm (jetCombination τ σ c P J) τ σ (jetCombinationConst c P J) := by
  rw [jetCombination, jetCombinationConst]
  exact mixedConstGerm_finsetSum _ _ _ fun j _ ↦ mixedConstGerm_finsetSum _ _ _ fun q _ ↦
    mixedConstGerm_const_mul (mixedConstGerm_gammaJetSource hτ hσ q j) _

/-! ### Vanishing divisors -/

theorem additiveOrbitalDivisorAt_eq_zero_of_terms (F : ℂ → ℂ) (σ p : ℂ) (ℓ : ℤ)
    (h : ∀ m : ℤ, laurentCoeff (fun w ↦ F (w + σ) - F w) (p + (m : ℂ) * σ) ℓ = 0) :
    additiveOrbitalDivisorAt F σ p ℓ = 0 := by
  rw [additiveOrbitalDivisorAt, finsum_congr h, finsum_zero]

theorem indepTriple_of_indepPeriods {τ σ : ℂ} (h : IndepPeriods τ σ) :
    ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0 := by
  intro n m j hh
  obtain ⟨h1, h2, h3⟩ := h j n m (by linear_combination hh)
  exact ⟨h2, h3, h1⟩

theorem indepSwap_of_indepPeriods {τ σ : ℂ} (h : IndepPeriods τ σ) :
    ∀ m n j : ℤ, (m : ℂ) * σ + (n : ℂ) * τ + (j : ℂ) = 0 → m = 0 ∧ n = 0 ∧ j = 0 := by
  intro m n j hh
  obtain ⟨h1, h2, h3⟩ := h j n m (by linear_combination hh)
  exact ⟨h3, h2, h1⟩

/-! ### The normal form -/

section

variable {F : ℂ → ℂ} {τ σ : ℂ} (hF : MeromorphicOn F (Set.univ : Set ℂ))
  (hper : PeriodicOneGerm F) {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
  (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
  (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])

include hF hper hmixed hτ hσ hindep hindepτ in
/-- **Subtracting the correction cancels the orbital divisor everywhere.** -/
theorem exists_gammaCorrection_vanishing_divisor :
    ∃ (P : Finset ℂ) (J : ℕ), ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
      additiveOrbitalDivisorAt (fun z ↦ F z - gammaCorrection τ σ F P J z) σ p ℓ = 0 := by
  classical
  obtain ⟨P, hP⟩ := exists_finset_boundaryPoleClasses hF hper hmixed hindepτ
  obtain ⟨L, hL⟩ := exists_orderBound_boundary hF hper hmixed hindepτ
  refine ⟨P, (-L).toNat, fun p ℓ hℓ ↦ ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, ℓ = -((i : ℤ) + 1) := ⟨(-ℓ - 1).toNat, by omega⟩
  have hUmero : MeromorphicOn (fun w ↦ F (w + σ) - F w) (Set.univ : Set ℂ) := fun y _ ↦
    (meromorphicAt_comp_add.mpr (hF (y + σ) (Set.mem_univ _))).sub (hF y (Set.mem_univ y))
  simp only [gammaCorrection]
  rw [additiveOrbitalDivisorAt_sub hF
    (meromorphicOn_jetCombination hτ hσ (gammaCorrectionCoeff τ σ F P) P _)
    (finite_support_orbitalDivisorTerm hF hper hmixed hτ (indepSwap_of_indepPeriods hindep) p
      (by omega))
    (finiteOrbitSupport_jetCombination hτ hσ hindep (gammaCorrectionCoeff τ σ F P) P _ p i),
    sub_eq_zero]
  -- the source has no divisor off the represented classes
  have hFoff : ¬ (∃ q ∈ P, SameClass τ σ q p) →
      additiveOrbitalDivisorAt F σ p (-((i : ℤ) + 1)) = 0 := by
    intro hp
    refine additiveOrbitalDivisorAt_eq_zero_of_terms F σ p _ fun m ↦ ?_
    by_contra hne
    have hpole : meromorphicOrderAt (fun w ↦ F (w + σ) - F w) (p + (m : ℂ) * σ) < 0 :=
      meromorphicOrderAt_neg_of_laurentCoeff_ne_zero (hUmero _ (Set.mem_univ _)) (by omega) hne
    obtain ⟨u, v, hmem⟩ := hP _ hpole
    refine hp ⟨_, hmem, ?_⟩
    refine ⟨-u, -v, m, ?_⟩
    simp only [zsmul_eq_mul]
    push_cast
    ring
  by_cases hiJ : i < (-L).toNat
  · by_cases hcls : ∃ q ∈ P, SameClass τ σ q p
    · exact (additiveOrbitalDivisorAt_gammaCorrection hτ hσ hindep hF hper hmixed P hiJ hcls).symm
    · rw [hFoff hcls, additiveOrbitalDivisorAt_jetCombination_of_notMem hτ hσ hindep
        (gammaCorrectionCoeff τ σ F P) P _ hcls]
  · have hbound : additiveOrbitalDivisorAt F σ p (-((i : ℤ) + 1)) = 0 := by
      refine additiveOrbitalDivisorAt_eq_zero_of_terms F σ p _ fun m ↦ ?_
      refine hL _ _ ?_
      have hJ : (-L) ≤ (((-L).toNat : ℕ) : ℤ) := Int.self_le_toNat _
      omega
    rw [hbound, additiveOrbitalDivisorAt_jetCombination_of_le hτ hσ hindep
      (gammaCorrectionCoeff τ σ F P) P (by omega : (-L).toNat ≤ i) p]

include hF hper hmixed hτ hσ hindep hindepτ hindepσ in
/-- **The triptic normal form.**  A mixed-constraint source differs from an explicit finite
combination of elliptic gamma jets by a differentially algebraic function, and its mixed constant is
exactly the constant carried by that combination. -/
theorem exists_gammaCorrection_differentiallyAlgebraic :
    ∃ (P : Finset ℂ) (J : ℕ), Cst = gammaCorrectionConst τ σ F P J ∧
      DifferentiallyAlgebraic
        (toMeromorphicNFOn (fun z ↦ F z - gammaCorrection τ σ F P J z) (Set.univ : Set ℂ)) := by
  obtain ⟨P, J, hvanish⟩ :=
    exists_gammaCorrection_vanishing_divisor hF hper hmixed hτ hσ hindep hindepτ
  have hGmero : MeromorphicOn (fun z ↦ F z - gammaCorrection τ σ F P J z)
      (Set.univ : Set ℂ) := fun z _ ↦
    (hF z (Set.mem_univ z)).sub
      (meromorphicOn_jetCombination hτ hσ (gammaCorrectionCoeff τ σ F P) P J z (Set.mem_univ z))
  have hGper : PeriodicOneGerm (fun z ↦ F z - gammaCorrection τ σ F P J z) :=
    periodicOneGerm_sub hper (periodicOneGerm_jetCombination τ σ (gammaCorrectionCoeff τ σ F P) P J)
  have hGmixed : MixedConstGerm (fun z ↦ F z - gammaCorrection τ σ F P J z) τ σ
      (Cst - gammaCorrectionConst τ σ F P J) :=
    mixedConstGerm_sub hmixed
      (mixedConstGerm_jetCombination hτ hσ (gammaCorrectionCoeff τ σ F P) P J)
  obtain ⟨hzero, hDA⟩ := differentiallyAlgebraic_toMeromorphicNFOn_of_vanishing_orbital_divisor
    hGmero hGper hGmixed hτ hσ (indepTriple_of_indepPeriods hindep) hindepτ hindepσ
    (fun p ℓ hℓ ↦ hvanish p ℓ hℓ)
  exact ⟨P, J, by linear_combination hzero, hDA⟩

end

/-! ### Every divisor datum is realized -/

/-- **Surjectivity of the orbital divisor.**  For distinct class representatives `P`, an order bound
`J` and arbitrary weights `d`, the jet combination with weights `d q j / ((-1)ʲ j!)` is a member of
the triptic class whose orbital divisor is `d q i` on the class of each `q ∈ P` at each order
`i < J`, and vanishes on every other class and at every other order. -/
theorem exists_mem_class_with_prescribed_divisor {τ σ : ℂ} (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : IndepPeriods τ σ) (P : Finset ℂ) (J : ℕ) (d : ℂ → ℕ → ℂ) :
    ∃ (Y : ℂ → ℂ) (C : ℂ), MeromorphicOn Y (Set.univ : Set ℂ) ∧ PeriodicOneGerm Y ∧
      MixedConstGerm Y τ σ C ∧
      (∀ q ∈ P, ∀ i < J, ∀ p : ℂ, SameClass τ σ q p →
          (∀ q' ∈ P, SameClass τ σ q' p → q' = q) →
          additiveOrbitalDivisorAt Y σ p (-((i : ℤ) + 1)) = d q i) ∧
      (∀ (i : ℕ) (p : ℂ), ¬ (∃ q ∈ P, SameClass τ σ q p) →
          additiveOrbitalDivisorAt Y σ p (-((i : ℤ) + 1)) = 0) ∧
      (∀ i : ℕ, J ≤ i → ∀ p : ℂ, additiveOrbitalDivisorAt Y σ p (-((i : ℤ) + 1)) = 0) := by
  classical
  set c : ℂ → ℕ → ℂ := fun q j ↦ d q j / ((-1 : ℂ) ^ j * (j.factorial : ℂ)) with hc
  refine ⟨jetCombination τ σ c P J, jetCombinationConst c P J,
    meromorphicOn_jetCombination hτ hσ c P J, periodicOneGerm_jetCombination τ σ c P J,
    mixedConstGerm_jetCombination hτ hσ c P J, ?_, ?_, ?_⟩
  · intro q hq i hi p hqp huniq
    rw [additiveOrbitalDivisorAt_jetCombination_eq_single hτ hσ hindep c P hi p]
    have hsingle : ∑ q' ∈ P,
        c q' i * additiveOrbitalDivisorAt (gammaJetSource τ σ q' i) σ p (-((i : ℤ) + 1))
          = c q i * additiveOrbitalDivisorAt (gammaJetSource τ σ q i) σ p (-((i : ℤ) + 1)) := by
      refine Finset.sum_eq_single q (fun q' hq' hne ↦ ?_) (fun hcon ↦ absurd hq hcon)
      have hnc : ¬ SameClass τ σ q' p := fun h ↦ hne (huniq q' hq' h)
      rw [additiveOrbitalDivisorAt_gammaJetSource_of_not_sameClass hτ hσ hnc i, mul_zero]
    rw [hsingle, additiveOrbitalDivisorAt_gammaJetSource_sameClass hτ hσ hindep hqp i, hc]
    have hfacn : ((i.factorial : ℂ)) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    have hsign : ((-1 : ℂ) ^ i) ≠ 0 := pow_ne_zero i (by norm_num)
    field_simp
  · intro i p hp
    exact additiveOrbitalDivisorAt_jetCombination_of_notMem hτ hσ hindep c P J hp
  · intro i hi p
    exact additiveOrbitalDivisorAt_jetCombination_of_le hτ hσ hindep c P hi p

end

end GaloisForLFunctions.HTGeometry
