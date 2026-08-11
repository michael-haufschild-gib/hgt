import GaloisForLFunctions.HTGeometry.TripticOrbitalDivisorFinsetSum
import GaloisForLFunctions.HTGeometry.EllipticGammaJetSourceDivisor
import GaloisForLFunctions.HTGeometry.EllipticGammaConeOrder

/-!
# The class relation and the finite orbit support of a gamma jet

Two base points carry the same orbital divisor exactly when they differ by an element of the period
group, so the correcting combination is indexed by classes.  This file records that relation as an
equivalence, counts the representatives of a class inside a finite set, and proves that every gamma
jet has finite orbit support at every negative order — the side condition the finite-sum divisor law
consumes.

* `SameClass` and its equivalence lemmas;
* `classCount`, `classCount_congr`;
* `laurentCoeff_shiftDiff_gammaJetSource`, `finiteOrbitSupport_gammaJetSource`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two points lie in the same class of `ℂ / (ℤ + ℤτ + ℤσ)`. -/
def SameClass (τ σ q p : ℂ) : Prop := ∃ u v k : ℤ, q = p + (u : ℂ) + (v : ℂ) * τ + (k : ℂ) * σ

theorem sameClass_iff (τ σ q p : ℂ) : SameClass τ σ q p ↔ PeriodGroupMem τ σ (q - p) := by
  constructor
  · rintro ⟨u, v, k, h⟩
    exact ⟨u, v, k, by linear_combination h⟩
  · rintro ⟨c, d, e, h⟩
    exact ⟨c, d, e, by linear_combination h⟩

theorem sameClass_refl (τ σ p : ℂ) : SameClass τ σ p p := ⟨0, 0, 0, by push_cast; ring⟩

theorem sameClass_symm {τ σ q p : ℂ} (h : SameClass τ σ q p) : SameClass τ σ p q := by
  obtain ⟨u, v, k, huvk⟩ := h
  exact ⟨-u, -v, -k, by push_cast; linear_combination -huvk⟩

theorem sameClass_trans {τ σ q r p : ℂ} (h₁ : SameClass τ σ q r) (h₂ : SameClass τ σ r p) :
    SameClass τ σ q p := by
  obtain ⟨u₁, v₁, k₁, h1⟩ := h₁
  obtain ⟨u₂, v₂, k₂, h2⟩ := h₂
  exact ⟨u₁ + u₂, v₁ + v₂, k₁ + k₂, by push_cast; linear_combination h1 + h2⟩

theorem periodGroupMem_neg {τ σ w : ℂ} (h : PeriodGroupMem τ σ w) : PeriodGroupMem τ σ (-w) := by
  obtain ⟨c, d, e, hc⟩ := h
  exact ⟨-c, -d, -e, by push_cast; linear_combination -hc⟩

/-- The number of representatives of the class of `p` inside a finite set. -/
def classCount (P : Finset ℂ) (τ σ p : ℂ) : ℕ := by
  classical
  exact (P.filter (fun q ↦ SameClass τ σ q p)).card

/-- The representative count depends only on the class. -/
theorem classCount_congr (P : Finset ℂ) {τ σ q p : ℂ} (h : SameClass τ σ q p) :
    classCount P τ σ q = classCount P τ σ p := by
  classical
  have hset : P.filter (fun r ↦ SameClass τ σ r q) = P.filter (fun r ↦ SameClass τ σ r p) := by
    refine Finset.filter_congr fun r _ ↦ ?_
    constructor
    · intro hr
      exact sameClass_trans hr h
    · intro hr
      exact sameClass_trans hr (sameClass_symm h)
  simp only [classCount]
  rw [hset]

/-- The boundary coefficients of a gamma jet, in terms of the source they differentiate. -/
theorem laurentCoeff_shiftDiff_gammaJetSource {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (g : ℂ) (j : ℕ) (w : ℂ) (ℓ : ℤ) :
    laurentCoeff (fun z ↦ gammaJetSource a b g j (z + b) - gammaJetSource a b g j z) w ℓ
      = (∏ i ∈ Finset.range j, ((ℓ : ℂ) + (i : ℂ) + 1))
        * laurentCoeff (fun z ↦ logDeriv (ellipticGammaConeTranslate a b g) (z + b)
            - logDeriv (ellipticGammaConeTranslate a b g) z) w (ℓ + (j : ℤ)) := by
  have hmero : MeromorphicOn (logDeriv (ellipticGammaConeTranslate a b g)) (Set.univ : Set ℂ) :=
    fun z _ ↦ ((meromorphicOn_ellipticGammaConeTranslate ha hb g z (Set.mem_univ z)).deriv).div
      (meromorphicOn_ellipticGammaConeTranslate ha hb g z (Set.mem_univ z))
  have hjet : MeromorphicOn (gammaJetSource a b g j) (Set.univ : Set ℂ) := fun z _ ↦
    meromorphicAt_iteratedDeriv (hmero z (Set.mem_univ z)) j
  rw [gammaJetSource] at hjet ⊢
  rw [laurentCoeff_shiftDiff hjet b w ℓ, laurentCoeff_shiftDiff hmero b w (ℓ + (j : ℤ)),
    laurentCoeff_iteratedDeriv_eq (hmero _ (Set.mem_univ _)) j ℓ,
    laurentCoeff_iteratedDeriv_eq (hmero _ (Set.mem_univ _)) j ℓ]
  ring

/-- **Every gamma jet has finite orbit support at every negative order.**  Above its own order the
falling product vanishes, below it the underlying logarithmic derivative contributes nothing, and at
its own order the support is the shift-order support, which is a single index. -/
theorem finiteOrbitSupport_gammaJetSource {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) (g p : ℂ) (j : ℕ) (i : ℕ) :
    FiniteOrbitSupport (gammaJetSource a b g j) b p (-((i : ℤ) + 1)) := by
  classical
  rcases lt_trichotomy i j with hlt | heq | hgt
  · refine Set.Finite.subset Set.finite_empty fun m hm ↦ ?_
    exact absurd (by
      rw [laurentCoeff_shiftDiff_gammaJetSource ha hb g j _ (-((i : ℤ) + 1)),
        prod_range_eq_zero_of_mem (j := j) (ℓ := -((i : ℤ) + 1))
          (by exact_mod_cast (by omega : -(j : ℤ) ≤ -((i : ℤ) + 1))) (by omega), zero_mul]) hm
  · subst heq
    have hfin := finite_shiftOrder_support_ellipticGammaConeTranslate ha hb hindep g p
    refine hfin.subset fun m hm ↦ ?_
    simp only [Set.mem_setOf_eq] at hm ⊢
    intro hzero
    apply hm
    rw [laurentCoeff_shiftDiff_gammaJetSource ha hb g i _ (-((i : ℤ) + 1)),
      show -((i : ℤ) + 1) + (i : ℤ) = -1 by ring,
      laurentCoeff_shiftDiff_logDeriv (meromorphicOn_ellipticGammaConeTranslate ha hb g)
        (meromorphicOrderAt_ellipticGammaConeTranslate_ne_top ha hb g) b _, hzero]
    simp
  · refine Set.Finite.subset Set.finite_empty fun m hm ↦ ?_
    refine absurd ?_ hm
    rw [laurentCoeff_shiftDiff_gammaJetSource ha hb g j _ (-((i : ℤ) + 1))]
    have hbase : laurentCoeff (fun z ↦ logDeriv (ellipticGammaConeTranslate a b g) (z + b)
        - logDeriv (ellipticGammaConeTranslate a b g) z) (p + (m : ℂ) * b)
        (-((i : ℤ) + 1) + (j : ℤ)) = 0 := by
      have hmero : MeromorphicOn (logDeriv (ellipticGammaConeTranslate a b g))
          (Set.univ : Set ℂ) := fun z _ ↦
        ((meromorphicOn_ellipticGammaConeTranslate ha hb g z (Set.mem_univ z)).deriv).div
          (meromorphicOn_ellipticGammaConeTranslate ha hb g z (Set.mem_univ z))
      rw [laurentCoeff_shiftDiff hmero b _ _]
      obtain ⟨n₁, hn₁⟩ := WithTop.ne_top_iff_exists.mp
        (meromorphicOrderAt_ellipticGammaConeTranslate_ne_top ha hb g (p + (m : ℂ) * b + b))
      obtain ⟨n₂, hn₂⟩ := WithTop.ne_top_iff_exists.mp
        (meromorphicOrderAt_ellipticGammaConeTranslate_ne_top ha hb g (p + (m : ℂ) * b))
      rw [laurentCoeff_logDeriv_eq_zero_of_le
          (meromorphicOn_ellipticGammaConeTranslate ha hb g _ (Set.mem_univ _)) hn₁.symm
          (by omega),
        laurentCoeff_logDeriv_eq_zero_of_le
          (meromorphicOn_ellipticGammaConeTranslate ha hb g _ (Set.mem_univ _)) hn₂.symm
          (by omega), sub_zero]
    rw [hbase, mul_zero]

end

end GaloisForLFunctions.HTGeometry
