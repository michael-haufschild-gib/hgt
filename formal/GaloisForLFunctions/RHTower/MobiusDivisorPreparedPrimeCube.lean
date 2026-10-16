import GaloisForLFunctions.RHTower.MobiusDivisorPrimePhaseGate
import GaloisForLFunctions.RHTower.MobiusDivisorBooleanEnergySpectrum

/-!
# One preparation makes a prescribed prime cube completely monotone

One fresh helper core makes every nonempty alternating difference positive
at every intermediate target subset. All orders and all vertices share one
tail of the original integer-cutoff energies. Targets are prescribed before
preparation; the helper mass budget is fixed before its lower prime bound.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower
open PrimePreparation

private def cubeFaces (T : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (T.powerset ×ˢ T.powerset).filter (fun e => e.2.Nonempty ∧ Disjoint e.1 e.2)

private lemma mem_cubeFaces {T A D : Finset ℕ} :
    (A, D) ∈ cubeFaces T ↔ A ⊆ T ∧ D ⊆ T ∧ D.Nonempty ∧ Disjoint A D := by
  simp only [cubeFaces, mem_filter, mem_product, Finset.mem_powerset, and_assoc]

private lemma eventually_boolean_pos (P D : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hD : ∀ p ∈ D, p.Prime)
    (h : 0 < mobiusDivisorBooleanAlternating P D mobiusDivisorCoreEnergyCoefficient) :
    ∀ᶠ M : ℕ in atTop,
      0 < mobiusDivisorBooleanAlternating P D (mobiusDivisorSelectionEnergy M) := by
  have he := (tendsto_mobiusDivisorBooleanEnergy_div_sq P D hP hD).eventually
    (eventually_gt_nhds h)
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with M hM hM0
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  apply (div_lt_div_iff_of_pos_right (pow_pos hMr 2)).mp
  simpa only [zero_div] using hM

/-- One actual fresh prime core makes the complete prescribed Boolean jet
strictly positive. The same preparation works at every vertex and every
order, both for limiting coefficients and all sufficiently large original
integer cutoffs. No sign, cancellation, or growth premise is assumed. -/
theorem exists_mobiusDivisorPreparedPrimeCube
    (P T : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (hT : ∀ p ∈ T, p.Prime) (hPT : Disjoint P T) :
    ∃ W : ℝ, 0 < W ∧ ∀ B : ℕ, ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ B < p) ∧ Disjoint (P ∪ T) S ∧
      (∑ p ∈ S, (Real.sqrt p)⁻¹) ≤ W ∧
      (∀ A ⊆ T, ∀ D ⊆ T \ A, D.Nonempty →
        0 < mobiusDivisorBooleanAlternating (P ∪ S ∪ A) D
          mobiusDivisorCoreEnergyCoefficient) ∧
      ∀ᶠ M : ℕ in atTop, ∀ A ⊆ T, ∀ D ⊆ T \ A, D.Nonempty →
        0 < mobiusDivisorBooleanAlternating (P ∪ S ∪ A) D
          (mobiusDivisorSelectionEnergy M) := by
  classical
  let J := cubeFaces T
  let R := insert 1 T
  let f : (Finset ℕ × Finset ℕ) → ℝ → ℝ := fun e t =>
    clusterWeight (P ∪ e.1) t * ∏ p ∈ e.2, Real.cos (Real.log p * t)
  have hQ (A : Finset ℕ) (hA : A ⊆ T) :
      (P ∪ A).Nonempty ∧ ∀ p ∈ P ∪ A, p.Prime := by
    refine ⟨hP.mono subset_union_left, ?_⟩
    intro p hp
    exact (mem_union.mp hp).elim (hprime p) (fun hp => hT p (hA hp))
  have hj (e : Finset ℕ × Finset ℕ) (he : e ∈ J) :
      e.1 ⊆ T ∧ e.2 ⊆ T ∧ e.2.Nonempty ∧ Disjoint e.1 e.2 := mem_cubeFaces.mp he
  have hfc (e : Finset ℕ × Finset ℕ) (_he : e ∈ J) : Continuous (f e) :=
    (clusterWeight_continuous (P ∪ e.1)).mul (by fun_prop)
  have hfi (e : Finset ℕ × Finset ℕ) (he : e ∈ J) : Integrable (f e) :=
    cosineProduct_integrable _ _ (hQ e.1 (hj e he).1).1 (hQ e.1 (hj e he).1).2
  have hf0 (e : Finset ℕ × Finset ℕ) (he : e ∈ J) : 0 < f e 0 := by
    simpa only [f, mul_zero, Real.cos_zero, prod_const_one, mul_one] using
      clusterWeight_zero_pos _ (hQ e.1 (hj e he).1).2
  have hbad (e : Finset ℕ × Finset ℕ) (he : e ∈ J) (t : ℝ) (ht : f e t < 0) :
      ∃ q ∈ R, q ≠ 1 ∧ Real.cos (Real.log q * t) ≤ 0 := by
    by_contra hn
    push Not at hn
    have hc (p : ℕ) (hp : p ∈ e.2) : 0 ≤ Real.cos (Real.log p * t) :=
      (hn p (mem_insert_of_mem ((hj e he).2.1 hp))
        (hT p ((hj e he).2.1 hp)).ne_one).le
    have hw : 0 ≤ clusterWeight (P ∪ e.1) t := sq_nonneg _
    exact (not_lt_of_ge (mul_nonneg hw (prod_nonneg hc))) ht
  obtain ⟨W, hW, hselect⟩ := exists_primeCluster_positive_tests J R (mem_insert_self _ _)
    (by
      intro r hr
      rcases mem_insert.mp hr with rfl | hr
      · omega
      · exact (hT r hr).pos) f hfc hfi hf0 hbad
  refine ⟨W, hW, fun B => ?_⟩
  let L := B + (P ∪ T).sup id + 1
  obtain ⟨S, hS, hmass, htests⟩ := hselect (L : ℝ)
  have hfresh (p : ℕ) (hp : p ∈ S) : L < p := by exact_mod_cast (hS p hp).2
  have hfree : Disjoint (P ∪ T) S := by
    apply Finset.disjoint_left.mpr
    intro p hp hpS
    have hle : p ≤ (P ∪ T).sup id := Finset.le_sup (f := id) hp
    have hlt := hfresh p hpS
    dsimp [L] at hlt
    omega
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have hprimeQ (A : Finset ℕ) (hA : A ⊆ T) : ∀ p ∈ P ∪ S ∪ A, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact (mem_union.mp hp).elim (hprime p) (hSprime p)
    · exact hT p (hA hp)
  have hpositive (A D : Finset ℕ) (hA : A ⊆ T) (hD : D ⊆ T)
      (hne : D.Nonempty) (hAD : Disjoint A D) :
      0 < mobiusDivisorBooleanAlternating (P ∪ S ∪ A) D
        mobiusDivisorCoreEnergyCoefficient := by
    have hQD : Disjoint (P ∪ S ∪ A) D := by
      apply Finset.disjoint_left.mpr
      intro p hp hpD
      rcases mem_union.mp hp with hp | hp
      · rcases mem_union.mp hp with hp | hp
        · exact Finset.disjoint_left.mp hPT hp (hD hpD)
        · exact Finset.disjoint_left.mp hfree (mem_union_right _ (hD hpD)) hp
      · exact Finset.disjoint_left.mp hAD hp hpD
    have hQne : (P ∪ S ∪ A).Nonempty := hP.mono (subset_union_left.trans subset_union_left)
    rw [mobiusDivisorCoreEnergyCoefficient_boolean_spectrum _ D hQne
      (hprimeQ A hA) (fun p hp => hT p (hD hp)) hQD]
    apply mul_pos
    · exact mul_pos (div_pos (coreDensity_pos _ (hprimeQ A hA)) (by positivity))
        (prod_pos (fun p hp => primeCosineFactor_pos (hT p (hD hp))))
    · have hAS : Disjoint (P ∪ A) S := hfree.mono_left (union_subset_union_right hA)
      have heq : P ∪ S ∪ A = (P ∪ A) ∪ S := by
        ext q
        simp only [Finset.mem_union]
        tauto
      have htest := htests (A, D) (mem_cubeFaces.mpr ⟨hA, hD, hne, hAD⟩)
      have heint : (∫ t, clusterWeight (P ∪ S ∪ A) t *
          ∏ p ∈ D, Real.cos (Real.log p * t)) =
          ∫ t, f (A, D) t * ‖divisorCoreMellinEuler S (1 + (t : ℂ) * Complex.I)‖ ^ 2 := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro t
        dsimp only
        rw [heq, clusterWeight_union (P ∪ A) S (hQ A hA).2 hSprime hAS]
        dsimp [f]
        ring
      rw [heint]
      exact htest
  have hparams (A D : Finset ℕ) (hD : D ⊆ T \ A) : D ⊆ T ∧ Disjoint A D := by
    refine ⟨hD.trans sdiff_subset, Finset.disjoint_left.mpr ?_⟩
    intro p hpA hpD
    exact (mem_sdiff.mp (hD hpD)).2 hpA
  refine ⟨S, fun p hp => ⟨hSprime p hp, ?_⟩, hfree, hmass, ?_, ?_⟩
  · have hlt := hfresh p hp
    dsimp [L] at hlt
    omega
  · intro A hA D hD hne
    exact hpositive A D hA (hparams A D hD).1 hne (hparams A D hD).2
  · have hall : ∀ᶠ M : ℕ in atTop, ∀ e ∈ J,
        0 < mobiusDivisorBooleanAlternating (P ∪ S ∪ e.1) e.2
          (mobiusDivisorSelectionEnergy M) := by
      apply (Filter.eventually_all_finset J).mpr
      intro e he
      exact eventually_boolean_pos _ _ (hprimeQ e.1 (hj e he).1)
        (fun p hp => hT p ((hj e he).2.1 hp))
        (hpositive e.1 e.2 (hj e he).1 (hj e he).2.1 (hj e he).2.2.1 (hj e he).2.2.2)
    filter_upwards [hall] with M hM
    intro A hA D hD hne
    exact hM (A, D) (mem_cubeFaces.mpr
      ⟨hA, (hparams A D hD).1, hne, (hparams A D hD).2⟩)

/-- Closed, premise-free form. The anchor `2` makes the inherited source
nonempty; already inherited targets are removed. Every other prescribed
prime participates in the same strictly completely monotone cube. -/
theorem mobiusDivisorPreparedPrimeCube_unconditional :
    ∀ P T : Finset Nat.Primes,
      let Q : Finset ℕ := insert 2 (P.image (fun p : Nat.Primes => (p : ℕ)))
      let U : Finset ℕ := T.image (fun p : Nat.Primes => (p : ℕ)) \ Q
      ∃ W : ℝ, 0 < W ∧ ∀ B : ℕ, ∃ S : Finset ℕ,
        (∀ p ∈ S, p.Prime ∧ B < p) ∧ Disjoint (Q ∪ U) S ∧
        (∑ p ∈ S, (Real.sqrt p)⁻¹) ≤ W ∧
        (∀ A ⊆ U, ∀ D ⊆ U \ A, D.Nonempty →
          0 < mobiusDivisorBooleanAlternating (Q ∪ S ∪ A) D
            mobiusDivisorCoreEnergyCoefficient) ∧
        ∀ᶠ M : ℕ in atTop, ∀ A ⊆ U, ∀ D ⊆ U \ A, D.Nonempty →
          0 < mobiusDivisorBooleanAlternating (Q ∪ S ∪ A) D
            (mobiusDivisorSelectionEnergy M) := by
  classical
  intro P T
  dsimp only
  apply exists_mobiusDivisorPreparedPrimeCube
  · exact ⟨2, mem_insert_self _ _⟩
  · intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact Nat.prime_two
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
      exact q.property
  · intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hp).1
    exact q.property
  · apply Finset.disjoint_left.mpr
    intro p hp hpU
    exact (mem_sdiff.mp hpU).2 hp

end RHTower
