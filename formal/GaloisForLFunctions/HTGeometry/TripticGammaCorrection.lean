import GaloisForLFunctions.HTGeometry.TripticGammaCorrectionBasis
import GaloisForLFunctions.HTGeometry.TripticOrbitalDivisorClassFunction

/-!
# The correcting combination of gamma jets

Given a finite set of class representatives and an order bound, the combination

`A = Σ_{j<J} Σ_{q∈P} ( d(q, -(j+1)) / ((-1)ʲ j! · classCount P q) ) · gammaJetSource τ σ q j`

has exactly the orbital divisor of the source it is built from, on every class represented in `P`
and at every order below `J`, and no divisor anywhere else.  The multiplicity divisor is what makes
this work without deduplicating `P`: each representative of a class contributes its share, and
because the divisor is a class function the shares sum to the class value.

* `gammaCorrection`;
* `additiveOrbitalDivisorAt_gammaCorrection` — the value on a represented class;
* `additiveOrbitalDivisorAt_gammaCorrection_of_notMem`, `..._of_le` — zero elsewhere.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem meromorphicOn_const_mul {F : ℂ → ℂ} (hF : MeromorphicOn F (Set.univ : Set ℂ)) (c : ℂ) :
    MeromorphicOn (fun z ↦ c * F z) (Set.univ : Set ℂ) := fun z _ ↦
  (analyticAt_const (x := z)).meromorphicAt.mul (hF z (Set.mem_univ z))

theorem finiteOrbitSupport_const_mul {F : ℂ → ℂ} {σ p : ℂ} {ℓ : ℤ}
    (hF : MeromorphicOn F (Set.univ : Set ℂ)) (hs : FiniteOrbitSupport F σ p ℓ) (c : ℂ) :
    FiniteOrbitSupport (fun z ↦ c * F z) σ p ℓ := by
  refine hs.subset fun m hm ↦ ?_
  simp only [Set.mem_setOf_eq] at hm ⊢
  intro hzero
  apply hm
  have hFa : MeromorphicAt (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) :=
    (meromorphicAt_comp_add.mpr (hF _ (Set.mem_univ _))).sub (hF _ (Set.mem_univ _))
  have hcm : laurentCoeff (fun z ↦ c * F (z + σ) - c * F z) (p + (m : ℂ) * σ) ℓ
      = c * laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ := by
    rw [← laurentCoeff_const_mul hFa c ℓ]
    congr 1
    funext z
    ring
  rw [hcm, hzero, mul_zero]

variable {τ σ : ℂ}

/-- The correcting combination of gamma jets attached to a finite set of representatives. -/
def gammaCorrection (τ σ : ℂ) (F : ℂ → ℂ) (P : Finset ℂ) (J : ℕ) : ℂ → ℂ :=
  ∑ j ∈ Finset.range J, ∑ q ∈ P,
    (fun z ↦ (additiveOrbitalDivisorAt F σ q (-((j : ℤ) + 1)) /
      ((-1 : ℂ) ^ j * (j.factorial : ℂ) * (classCount P τ σ q : ℂ))) * gammaJetSource τ σ q j z)

section

variable (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)

include hτ hσ in
theorem meromorphicOn_gammaJetSource (g : ℂ) (j : ℕ) :
    MeromorphicOn (gammaJetSource τ σ g j) (Set.univ : Set ℂ) := fun z _ ↦
  meromorphicAt_iteratedDeriv
    (((meromorphicOn_ellipticGammaConeTranslate hτ hσ g z (Set.mem_univ z)).deriv).div
      (meromorphicOn_ellipticGammaConeTranslate hτ hσ g z (Set.mem_univ z))) j

include hτ hσ hindep in
/-- **The divisor of one order slice of the correction.** -/
theorem additiveOrbitalDivisorAt_gammaSlice (F : ℂ → ℂ) (P : Finset ℂ) (j : ℕ) (i : ℕ) (p : ℂ) :
    additiveOrbitalDivisorAt
        (∑ q ∈ P, (fun z ↦ (additiveOrbitalDivisorAt F σ q (-((j : ℤ) + 1)) /
          ((-1 : ℂ) ^ j * (j.factorial : ℂ) * (classCount P τ σ q : ℂ)))
            * gammaJetSource τ σ q j z)) σ p (-((i : ℤ) + 1))
      = ∑ q ∈ P, (additiveOrbitalDivisorAt F σ q (-((j : ℤ) + 1)) /
          ((-1 : ℂ) ^ j * (j.factorial : ℂ) * (classCount P τ σ q : ℂ)))
            * additiveOrbitalDivisorAt (gammaJetSource τ σ q j) σ p (-((i : ℤ) + 1)) := by
  rw [additiveOrbitalDivisorAt_finsetSum P _
    (fun q _ ↦ meromorphicOn_const_mul (meromorphicOn_gammaJetSource hτ hσ q j) _)
    (fun q _ ↦ finiteOrbitSupport_const_mul (meromorphicOn_gammaJetSource hτ hσ q j)
      (finiteOrbitSupport_gammaJetSource hτ hσ hindep q p j i) _)]
  exact Finset.sum_congr rfl fun q _ ↦
    additiveOrbitalDivisorAt_const_mul (meromorphicOn_gammaJetSource hτ hσ q j) _ σ p _

include hτ hσ hindep in
/-- The correction splits into its order slices. -/
theorem additiveOrbitalDivisorAt_gammaCorrection_eq_sum (F : ℂ → ℂ) (P : Finset ℂ) (J : ℕ)
    (i : ℕ) (p : ℂ) :
    additiveOrbitalDivisorAt (gammaCorrection τ σ F P J) σ p (-((i : ℤ) + 1))
      = ∑ j ∈ Finset.range J, ∑ q ∈ P,
          (additiveOrbitalDivisorAt F σ q (-((j : ℤ) + 1)) /
            ((-1 : ℂ) ^ j * (j.factorial : ℂ) * (classCount P τ σ q : ℂ)))
              * additiveOrbitalDivisorAt (gammaJetSource τ σ q j) σ p (-((i : ℤ) + 1)) := by
  rw [gammaCorrection, additiveOrbitalDivisorAt_finsetSum (Finset.range J) _
    (fun j _ ↦ meromorphicOn_finsetSum P _
      fun q _ ↦ meromorphicOn_const_mul (meromorphicOn_gammaJetSource hτ hσ q j) _)
    (fun j _ ↦ finiteOrbitSupport_finsetSum P _
      (fun q _ ↦ meromorphicOn_const_mul (meromorphicOn_gammaJetSource hτ hσ q j) _)
      (fun q _ ↦ finiteOrbitSupport_const_mul (meromorphicOn_gammaJetSource hτ hσ q j)
        (finiteOrbitSupport_gammaJetSource hτ hσ hindep q p j i) _))]
  exact Finset.sum_congr rfl fun j _ ↦ additiveOrbitalDivisorAt_gammaSlice hτ hσ hindep F P j i p

include hτ hσ hindep in
/-- Only the slice of the matching order contributes. -/
theorem additiveOrbitalDivisorAt_gammaCorrection_eq_single (F : ℂ → ℂ) (P : Finset ℂ) {J : ℕ}
    {i : ℕ} (hi : i < J) (p : ℂ) :
    additiveOrbitalDivisorAt (gammaCorrection τ σ F P J) σ p (-((i : ℤ) + 1))
      = ∑ q ∈ P, (additiveOrbitalDivisorAt F σ q (-((i : ℤ) + 1)) /
          ((-1 : ℂ) ^ i * (i.factorial : ℂ) * (classCount P τ σ q : ℂ)))
            * additiveOrbitalDivisorAt (gammaJetSource τ σ q i) σ p (-((i : ℤ) + 1)) := by
  rw [additiveOrbitalDivisorAt_gammaCorrection_eq_sum hτ hσ hindep F P J i p]
  refine Finset.sum_eq_single i (fun j _ hj ↦ ?_) (fun hcon ↦ absurd (Finset.mem_range.mpr hi) hcon)
  refine Finset.sum_eq_zero fun q _ ↦ ?_
  rw [additiveOrbitalDivisorAt_gammaJetSource_of_ne_order hτ hσ q p j (fun h ↦ hj h.symm),
    mul_zero]

include hτ hσ hindep in
/-- A gamma jet reproduces its full weight at every point of its own class. -/
theorem additiveOrbitalDivisorAt_gammaJetSource_sameClass {q p : ℂ} (h : SameClass τ σ q p)
    (j : ℕ) :
    additiveOrbitalDivisorAt (gammaJetSource τ σ q j) σ p (-((j : ℤ) + 1))
      = (-1) ^ j * (j.factorial : ℂ) := by
  obtain ⟨u, v, k, huvk⟩ := h
  have hpeq : p = q + ((((-u : ℤ)) : ℂ) + (((-v : ℤ)) : ℂ) * τ + (((-k : ℤ)) : ℂ) * σ) := by
    push_cast
    linear_combination -huvk
  rw [hpeq]
  exact additiveOrbitalDivisorAt_gammaJetSource_periodPoint hτ hσ hindep q j (-u) (-v) (-k)

include hτ hσ in
/-- A gamma jet has no weight off its own class. -/
theorem additiveOrbitalDivisorAt_gammaJetSource_of_not_sameClass {q p : ℂ}
    (h : ¬ SameClass τ σ q p) (j : ℕ) :
    additiveOrbitalDivisorAt (gammaJetSource τ σ q j) σ p (-((j : ℤ) + 1)) = 0 := by
  refine additiveOrbitalDivisorAt_gammaJetSource_of_notMem_translate hτ hσ ?_ j
  intro hmem
  have hneg := periodGroupMem_neg hmem
  rw [neg_sub] at hneg
  exact h ((sameClass_iff τ σ q p).mpr hneg)

end

/-- A class represented in a finite set has a positive representative count. -/
theorem classCount_ne_zero_of_exists {P : Finset ℂ} {τ σ p : ℂ}
    (h : ∃ q ∈ P, SameClass τ σ q p) : (classCount P τ σ p : ℂ) ≠ 0 := by
  classical
  obtain ⟨q, hqP, hq⟩ := h
  have hne : (P.filter (fun r ↦ SameClass τ σ r p)).Nonempty :=
    ⟨q, Finset.mem_filter.mpr ⟨hqP, hq⟩⟩
  have : classCount P τ σ p ≠ 0 := by
    simp only [classCount]
    exact (Finset.card_pos.mpr hne).ne'
  exact_mod_cast this

section

variable {F : ℂ → ℂ} (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
  (hF : MeromorphicOn F (Set.univ : Set ℂ)) (hper : PeriodicOneGerm F)

include hF hper in
/-- The orbital divisor of a mixed-constraint source agrees along a class. -/
theorem additiveOrbitalDivisorAt_congr_sameClass {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    {q p : ℂ}
    (h : SameClass τ σ q p) {ℓ : ℤ} (hℓ : ℓ < 0) :
    additiveOrbitalDivisorAt F σ q ℓ = additiveOrbitalDivisorAt F σ p ℓ := by
  obtain ⟨u, v, k, huvk⟩ := h
  have hqeq : q = p + (u : ℂ) * 1 + (v : ℂ) * τ + (k : ℂ) * σ := by
    rw [mul_one]
    exact huvk
  rw [hqeq]
  exact additiveOrbitalDivisorAt_classFunction hF hper hmixed p hℓ u v k

include hτ hσ hindep hF hper in
/-- **The correction carries exactly the divisor of its source on every represented class.** -/
theorem additiveOrbitalDivisorAt_gammaCorrection {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    (P : Finset ℂ) {J i : ℕ} (hi : i < J) {p : ℂ} (hp : ∃ q ∈ P, SameClass τ σ q p) :
    additiveOrbitalDivisorAt (gammaCorrection τ σ F P J) σ p (-((i : ℤ) + 1))
      = additiveOrbitalDivisorAt F σ p (-((i : ℤ) + 1)) := by
  classical
  have hneg : (-((i : ℤ) + 1)) < 0 := by omega
  have hfacn : ((i.factorial : ℂ)) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hfac : ((-1 : ℂ) ^ i * (i.factorial : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero i (by norm_num)) hfacn
  have hcnt : (classCount P τ σ p : ℂ) ≠ 0 := classCount_ne_zero_of_exists hp
  rw [additiveOrbitalDivisorAt_gammaCorrection_eq_single hτ hσ hindep F P hi p,
    ← Finset.sum_filter_add_sum_filter_not P (fun q ↦ SameClass τ σ q p)]
  have hoff : ∑ q ∈ P.filter (fun q ↦ ¬ SameClass τ σ q p),
      (additiveOrbitalDivisorAt F σ q (-((i : ℤ) + 1)) /
        ((-1 : ℂ) ^ i * (i.factorial : ℂ) * (classCount P τ σ q : ℂ)))
          * additiveOrbitalDivisorAt (gammaJetSource τ σ q i) σ p (-((i : ℤ) + 1)) = 0 := by
    refine Finset.sum_eq_zero fun q hq ↦ ?_
    rw [additiveOrbitalDivisorAt_gammaJetSource_of_not_sameClass hτ hσ
      (Finset.mem_filter.mp hq).2 i, mul_zero]
  have hon : ∀ q ∈ P.filter (fun q ↦ SameClass τ σ q p),
      (additiveOrbitalDivisorAt F σ q (-((i : ℤ) + 1)) /
        ((-1 : ℂ) ^ i * (i.factorial : ℂ) * (classCount P τ σ q : ℂ)))
          * additiveOrbitalDivisorAt (gammaJetSource τ σ q i) σ p (-((i : ℤ) + 1))
        = additiveOrbitalDivisorAt F σ p (-((i : ℤ) + 1)) / (classCount P τ σ p : ℂ) := by
    intro q hq
    have hqc := (Finset.mem_filter.mp hq).2
    rw [additiveOrbitalDivisorAt_gammaJetSource_sameClass hτ hσ hindep hqc i,
      additiveOrbitalDivisorAt_congr_sameClass hF hper hmixed hqc hneg, classCount_congr P hqc]
    field_simp
  rw [hoff, add_zero, Finset.sum_congr rfl hon, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((P.filter (fun q ↦ SameClass τ σ q p)).card : ℂ) = (classCount P τ σ p : ℂ) := by
    simp only [classCount]
  rw [hcard, mul_div_cancel₀ _ hcnt]

end

end

end GaloisForLFunctions.HTGeometry
