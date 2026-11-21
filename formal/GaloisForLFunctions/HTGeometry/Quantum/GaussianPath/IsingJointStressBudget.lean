import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsingJointStress
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Extreme

/-!
# Generators of the joint stress region under an energy budget

Pair a configuration strictly below the budget with one above it.
Subtract the largest nonnegative multiple of their budget-saturating
law. The residual stays feasible and loses a support point. Induction
then expresses every feasible readout using singles and crossing chords.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace FiniteStrain

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

/-- Weight on the above-budget configuration of a crossing chord. -/
def budgetChordWeight (a : ι → ℝ) (B : ℝ) (i j : ι) : ℝ :=
  (B - a i) / (a j - a i)

/-- Feasible basis readouts together with crossing chords evaluated at the budget. -/
def stressBudgetGenerators (a : ι → ℝ) (b : ι → V) (B : ℝ) : Set V :=
  b '' {i | a i ≤ B} ∪
    {v | ∃ i j, a i < B ∧ B < a j ∧
      (1 - budgetChordWeight a B i j) • b i + budgetChordWeight a B i j • b j = v}

theorem stressBudgetGenerators_finite (a : ι → ℝ) (b : ι → V) (B : ℝ) :
    (stressBudgetGenerators a b B).Finite := by
  let c (ij : ι × ι) :=
    (1 - budgetChordWeight a B ij.1 ij.2) • b ij.1 + budgetChordWeight a B ij.1 ij.2 • b ij.2
  refine ((Set.finite_range b).union (Set.finite_range c)).subset ?_
  rintro v (⟨i, _, rfl⟩ | ⟨i, j, _, _, rfl⟩)
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨(i, j), rfl⟩

private def positiveBasisSupport (p : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => 0 < p i)

private theorem mem_positiveBasisSupport {p : ι → ℝ} {i : ι} :
    i ∈ positiveBasisSupport p ↔ 0 < p i := by
  classical
  simp [positiveBasisSupport]

private theorem budgetChordLaw (a : ι → ℝ) {B : ℝ} {i j : ι} (hi : a i < B) (hj : B < a j) :
    let t := budgetChordWeight a B i j
    0 < t ∧ t < 1 ∧ IsBasisLaw (mixBasisLaw (pointBasisLaw i) (pointBasisLaw j) t) ∧
      diagonalMean (mixBasisLaw (pointBasisLaw i) (pointBasisLaw j) t) a = B := by
  let t := budgetChordWeight a B i j
  have hgap : 0 < a j - a i := sub_pos.mpr (hi.trans hj)
  have ht₀ : 0 < t := div_pos (sub_pos.mpr hi) hgap
  have ht₁ : t < 1 := (div_lt_iff₀ hgap).mpr (by
    rw [one_mul]
    exact sub_lt_sub_right hj _)
  have ht : t * (a j - a i) = B - a i := div_mul_cancel₀ _ hgap.ne'
  refine ⟨ht₀, ht₁, isBasisLaw_mix (isBasisLaw_point i) (isBasisLaw_point j) ht₀.le ht₁.le, ?_⟩
  rw [diagonalMean_mix, diagonalMean_point, diagonalMean_point]
  calc
    _ = a i + t * (a j - a i) := by ring
    _ = B := by rw [ht]; ring

private theorem exists_positive_belowBudget {a p : ι → ℝ} {B : ℝ}
    (hp : IsBasisLaw p) (hB : diagonalMean p a ≤ B) {j : ι}
    (hj : 0 < p j) (hja : B < a j) : ∃ i, 0 < p i ∧ a i < B := by
  classical
  by_contra h
  have hnonneg (i : ι) : 0 ≤ p i * (a i - B) := by
    by_cases hi : p i = 0
    · rw [hi, zero_mul]
    · have hp₀ : 0 < p i := lt_of_le_of_ne (hp.1 i) (Ne.symm hi)
      exact mul_nonneg hp₀.le (sub_nonneg.mpr (le_of_not_gt fun ha => h ⟨i, hp₀, ha⟩))
  have hj₀ := mul_pos hj (sub_pos.mpr hja)
  have hle := Finset.single_le_sum (f := fun i => p i * (a i - B))
    (fun i _ => hnonneg i) (Finset.mem_univ j)
  have he : 0 < diagonalMean p (fun i => a i - B) := hj₀.trans_le hle
  rw [diagonalMean_sub_const hp] at he
  exact (not_lt_of_ge hB) (sub_pos.mp he)

private theorem diagonalVectorMean_mem_hull_of_feasible_support
    (a : ι → ℝ) (b : ι → V) (B : ℝ) {p : ι → ℝ} (hp : IsBasisLaw p)
    (h : ∀ i, 0 < p i → a i ≤ B) :
    diagonalVectorMean p b ∈ convexHull ℝ (stressBudgetGenerators a b B) := by
  classical
  let S := positiveBasisSupport p
  have hz (i : ι) (hi : i ∉ S) : p i = 0 :=
    le_antisymm (le_of_not_gt fun hpi => hi (mem_positiveBasisSupport.mpr hpi)) (hp.1 i)
  have hsum : ∑ i ∈ S, p i = 1 :=
    (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hz i hi)).trans hp.2
  have hmean : (∑ i ∈ S, p i • b i) = diagonalVectorMean p b :=
    Finset.sum_subset (Finset.subset_univ S) fun i _ hi => by simp only [hz i hi, zero_smul]
  rw [← hmean]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => hp.1 i) hsum fun i hi => ?_
  exact subset_convexHull ℝ _ (Or.inl ⟨i, h i (mem_positiveBasisSupport.mp hi), rfl⟩)

private theorem diagonalMean_scaled_sub (p q a : ι → ℝ) (t : ℝ) :
    diagonalMean (fun i => p i - t * q i) a = diagonalMean p a - t * diagonalMean q a := by
  simp only [diagonalMean, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]

private theorem diagonalMean_div_weight (p a : ι → ℝ) (c : ℝ) :
    diagonalMean (fun i => p i / c) a = diagonalMean p a / c := by
  unfold diagonalMean
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by rw [div_mul_eq_mul_div]

private theorem exists_budgetLaw_remove_crossing {a p : ι → ℝ} {B : ℝ}
    (hp : IsBasisLaw p) (hB : diagonalMean p a ≤ B) {i j : ι}
    (hpi : 0 < p i) (hpj : 0 < p j) (hi : a i < B) (hj : B < a j) :
    let q := mixBasisLaw (pointBasisLaw i) (pointBasisLaw j) (budgetChordWeight a B i j)
    p = q ∨ ∃ r t, IsBasisLaw r ∧ diagonalMean r a ≤ B ∧
      (positiveBasisSupport r).card < (positiveBasisSupport p).card ∧
        t ∈ Icc 0 1 ∧ p = mixBasisLaw r q t := by
  classical
  let θ := budgetChordWeight a B i j
  let q := mixBasisLaw (pointBasisLaw i) (pointBasisLaw j) θ
  obtain ⟨hθ₀, hθ₁, hq, hqB⟩ := budgetChordLaw a hi hj
  have hθ₀ : 0 < θ := hθ₀
  have hθ₁ : θ < 1 := hθ₁
  have hq : IsBasisLaw q := hq
  have hqB : diagonalMean q a = B := hqB
  have hij : i ≠ j := fun h => (not_lt_of_ge hi.le) (h.symm ▸ hj)
  have hqi : q i = 1 - θ := by simp [q, mixBasisLaw, pointBasisLaw, hij]
  have hqj : q j = θ := by simp [q, mixBasisLaw, pointBasisLaw, Ne.symm hij]
  have hqother (k : ι) (hki : k ≠ i) (hkj : k ≠ j) : q k = 0 := by
    simp [q, mixBasisLaw, pointBasisLaw, hki, hkj]
  let t := min (p i / (1 - θ)) (p j / θ)
  have ht : 0 < t := lt_min (div_pos hpi (sub_pos.mpr hθ₁)) (div_pos hpj hθ₀)
  have hti : t * q i ≤ p i := by
    rw [hqi]
    exact (le_div_iff₀ (sub_pos.mpr hθ₁)).mp (min_le_left _ _)
  have htj : t * q j ≤ p j := by
    rw [hqj]
    exact (le_div_iff₀ hθ₀).mp (min_le_right _ _)
  let w (k : ι) := p k - t * q k
  have hw (k : ι) : 0 ≤ w k := by
    by_cases hki : k = i
    · subst k
      exact sub_nonneg.mpr hti
    · by_cases hkj : k = j
      · subst k
        exact sub_nonneg.mpr htj
      · simpa only [w, hqother k hki hkj, mul_zero, sub_zero] using hp.1 k
  have hmass : ∑ k, w k = 1 - t := by
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2, hq.2, mul_one]
  have htle : t ≤ 1 := by
    have hsum : 0 ≤ ∑ k, w k := Finset.sum_nonneg fun k _ => hw k
    rw [hmass] at hsum
    exact sub_nonneg.mp hsum
  have hzero : ∃ k, 0 < p k ∧ w k = 0 := by
    rcases le_total (p i / (1 - θ)) (p j / θ) with h | h
    · refine ⟨i, hpi, ?_⟩
      simp only [w, t, min_eq_left h, hqi, div_mul_cancel₀ _ (sub_pos.mpr hθ₁).ne', sub_self]
    · refine ⟨j, hpj, ?_⟩
      simp only [w, t, min_eq_right h, hqj, div_mul_cancel₀ _ hθ₀.ne', sub_self]
  change p = q ∨ _
  rcases eq_or_lt_of_le htle with he | hlt
  · left
    have hsum : ∑ k, w k = 0 := by rw [hmass, he, sub_self]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hw k)).mp hsum
    funext k
    have hk := hz k (Finset.mem_univ k)
    change p k - t * q k = 0 at hk
    simpa only [he, one_mul, sub_eq_zero] using hk
  · right
    let r (k : ι) := w k / (1 - t)
    have hden : 0 < 1 - t := sub_pos.mpr hlt
    have hr : IsBasisLaw r := by
      refine ⟨fun k => div_nonneg (hw k) hden.le, ?_⟩
      change (∑ k, w k / (1 - t)) = 1
      rw [← Finset.sum_div, hmass, div_self hden.ne']
    have hrB : diagonalMean r a ≤ B := by
      change diagonalMean (fun k => w k / (1 - t)) a ≤ B
      rw [diagonalMean_div_weight]
      apply (div_le_iff₀ hden).mpr
      have he' : diagonalMean w a = diagonalMean p a - t * B := by
        change diagonalMean (fun k => p k - t * q k) a = _
        rw [diagonalMean_scaled_sub, hqB]
      rw [he', mul_sub, mul_one, mul_comm B t]
      exact sub_le_sub_right hB _
    have hrSub : positiveBasisSupport r ⊆ positiveBasisSupport p := by
      intro k hk
      have hr₀ := mem_positiveBasisSupport.mp hk
      apply mem_positiveBasisSupport.mpr
      by_contra hn
      have hpk : p k = 0 := le_antisymm (le_of_not_gt hn) (hp.1 k)
      have hwl : w k ≤ 0 := by
        change p k - t * q k ≤ 0
        rw [hpk, zero_sub]
        exact neg_nonpos.mpr (mul_nonneg ht.le (hq.1 k))
      exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg hwl hden.le)) hr₀
    have hne : positiveBasisSupport r ≠ positiveBasisSupport p := by
      intro h
      obtain ⟨k, hk, hwk⟩ := hzero
      have hkr : k ∈ positiveBasisSupport r := h.symm ▸ mem_positiveBasisSupport.mpr hk
      have hz : r k = 0 := by change w k / (1 - t) = 0; rw [hwk, zero_div]
      exact ((mem_positiveBasisSupport.mp hkr).ne' hz)
    refine ⟨r, t, hr, hrB, Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hrSub, hne⟩),
      ⟨ht.le, hlt.le⟩, ?_⟩
    funext k
    change p k = (1 - t) * (w k / (1 - t)) + t * q k
    rw [mul_div_cancel₀ _ hden.ne']
    dsimp only [w]
    ring

/-- The full feasible vector region is the convex hull of the single
and crossing-chord readouts, for every budget. -/
theorem basisStressBudgetRange_eq_generatorHull (a : ι → ℝ) (b : ι → V) (B : ℝ) :
    {v | ∃ p, IsBasisLaw p ∧ diagonalMean p a ≤ B ∧ diagonalVectorMean p b = v} =
      convexHull ℝ (stressBudgetGenerators a b B) := by
  classical
  let S : Set V := {v | ∃ p, IsBasisLaw p ∧ diagonalMean p a ≤ B ∧ diagonalVectorMean p b = v}
  let G := stressBudgetGenerators a b B
  change S = convexHull ℝ G
  apply le_antisymm
  · have main (n : ℕ) : ∀ p, IsBasisLaw p → diagonalMean p a ≤ B →
        (positiveBasisSupport p).card = n → diagonalVectorMean p b ∈ convexHull ℝ G := by
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro p hp hB hn
        by_cases hhigh : ∃ j, 0 < p j ∧ B < a j
        · obtain ⟨j, hpj, hj⟩ := hhigh
          obtain ⟨i, hpi, hi⟩ := exists_positive_belowBudget hp hB hpj hj
          let θ := budgetChordWeight a B i j
          let q := mixBasisLaw (pointBasisLaw i) (pointBasisLaw j) θ
          have hq : diagonalVectorMean q b ∈ convexHull ℝ G := by
            apply subset_convexHull ℝ G
            right
            refine ⟨i, j, hi, hj, ?_⟩
            simp only [q, θ, diagonalVectorMean_mix, diagonalVectorMean_point]
          rcases exists_budgetLaw_remove_crossing hp hB hpi hpj hi hj with h | ⟨r, t, hr, hrB, hcard, ht, he⟩
          · change p = q at h
            rwa [h]
          · have hrmem := ih _ (hcard.trans_eq hn) r hr hrB rfl
            rw [he, diagonalVectorMean_mix]
            exact (convex_convexHull ℝ G) hrmem hq (sub_nonneg.mpr ht.2) ht.1 (by ring)
        · exact diagonalVectorMean_mem_hull_of_feasible_support a b B hp fun i hi =>
            le_of_not_gt fun h => hhigh ⟨i, hi, h⟩
    rintro _ ⟨p, hp, hB, rfl⟩
    exact main _ p hp hB rfl
  · apply convexHull_min
    · rintro v (⟨i, hi, rfl⟩ | ⟨i, j, hi, hj, rfl⟩)
      · change a i ≤ B at hi
        exact ⟨pointBasisLaw i, isBasisLaw_point i, by simpa only [diagonalMean_point] using hi,
          diagonalVectorMean_point b i⟩
      · obtain ⟨_, _, hq, hB⟩ := budgetChordLaw a hi hj
        refine ⟨_, hq, hB.le, ?_⟩
        simp only [diagonalVectorMean_mix, diagonalVectorMean_point]
    · intro x hx y hy s t hs ht hst
      obtain ⟨p, hp, hpB, rfl⟩ := hx
      obtain ⟨q, hq, hqB, rfl⟩ := hy
      have he : 1 - t = s := by linarith only [hst]
      have ht₁ : t ≤ 1 := by linarith only [hs, hst]
      refine ⟨mixBasisLaw p q t, isBasisLaw_mix hp hq ht ht₁, ?_, ?_⟩
      · rw [diagonalMean_mix, he]
        calc
          _ ≤ s * B + t * B := add_le_add (mul_le_mul_of_nonneg_left hpB hs) (mul_le_mul_of_nonneg_left hqB ht)
          _ = B := by rw [← add_mul, hst, one_mul]
      · rw [diagonalVectorMean_mix, he]

/-- Normalized pure states attain the same joint budget region. -/
theorem pureJointStressBudgetRange_eq_generatorHull (a : ι → ℝ) (b : ι → V) (B : ℝ) :
    {v | ∃ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 ∧ pureDiagonalMean ψ a ≤ B ∧
      pureDiagonalVectorMean ψ b = v} = convexHull ℝ (stressBudgetGenerators a b B) := by
  rw [← basisStressBudgetRange_eq_generatorHull]
  ext v
  constructor
  · rintro ⟨ψ, hψ, ha, hb⟩
    exact ⟨pureBasisLaw ψ, isBasisLaw_pure ψ hψ, ha, hb⟩
  · rintro ⟨p, hp, ha, hb⟩
    obtain ⟨ψ, hψ, hprob⟩ := exists_pureBasisLaw hp
    exact ⟨ψ, hψ, by rwa [pureDiagonalMean, hprob], by rwa [pureDiagonalVectorMean, hprob]⟩

/-- Cutting the energy–stress hull and projecting to the stress coordinates
gives exactly the finite crossing-chord hull. -/
theorem stressBudgetProjection_eq_generatorHull (a : ι → ℝ) (b : ι → V) (B : ℝ) :
    Prod.snd '' (convexHull ℝ (range (fun i => (a i, b i))) ∩ {z : ℝ × V | z.1 ≤ B}) =
      convexHull ℝ (stressBudgetGenerators a b B) := by
  rw [← pureStressBudgetRange_eq_projection, pureJointStressBudgetRange_eq_generatorHull]

/-- A half-space cut of any finitely generated convex hull is generated
by retained points and the pairwise segments meeting the cutting plane. -/
theorem convexHull_inter_linearSublevel_eq_generatorHull (b : ι → V) (L : V →ₗ[ℝ] ℝ) (B : ℝ) :
    convexHull ℝ (range b) ∩ {v | L v ≤ B} =
      convexHull ℝ (stressBudgetGenerators (fun i => L (b i)) b B) := by
  have hHull := diagonalVectorMeanRange_eq_convexHull (Finset.univ : Finset ι) b
  rw [Finset.coe_univ, image_univ] at hHull
  rw [← hHull, ← basisStressBudgetRange_eq_generatorHull]
  have hmean (p : ι → ℝ) :
      L (diagonalVectorMean p b) = diagonalMean p (fun i => L (b i)) :=
    (diagonalVectorMean_map L p b).trans (diagonalVectorMean_real _ _)
  ext v
  constructor
  · rintro ⟨⟨p, hp, _, rfl⟩, hB⟩
    change L (diagonalVectorMean p b) ≤ B at hB
    exact ⟨p, hp, by rwa [hmean] at hB, rfl⟩
  · rintro ⟨p, hp, hB, rfl⟩
    exact ⟨⟨p, hp, fun i _ => Finset.mem_univ i, rfl⟩, by
      change L (diagonalVectorMean p b) ≤ B
      rwa [hmean]⟩

/-- The energy cut in the full energy–stress diagram retains the energy
coordinate of each crossing chord at precisely the budget. -/
theorem energyStressHull_inter_budget_eq_generatorHull (a : ι → ℝ) (b : ι → V) (B : ℝ) :
    convexHull ℝ (range (fun i => (a i, b i))) ∩ {z : ℝ × V | z.1 ≤ B} =
      convexHull ℝ (stressBudgetGenerators a (fun i => (a i, b i)) B) :=
  convexHull_inter_linearSublevel_eq_generatorHull (fun i => (a i, b i)) (LinearMap.fst ℝ ℝ V) B

/-- At ground energy the retained generators are exactly the ground
stress vectors. There are no crossing chords from below. -/
theorem stressBudgetGenerators_groundEnergy_eq [Nonempty ι] (a : ι → ℝ) (b : ι → V) :
    stressBudgetGenerators a b (groundEnergy a) = b '' (groundConfigurations a : Set ι) := by
  apply le_antisymm
  · rintro _ (⟨i, hi, rfl⟩ | ⟨i, _, hi, _, _⟩)
    · change a i ≤ groundEnergy a at hi
      exact ⟨i, mem_groundConfigurations.mpr (le_antisymm hi (groundEnergy_le a i)), rfl⟩
    · exact ((not_lt_of_ge (groundEnergy_le a i)) hi).elim
  · rintro _ ⟨i, hi, rfl⟩
    exact Or.inl ⟨i, (mem_groundConfigurations.mp hi).le, rfl⟩

/-- Every extreme joint stress has a pure preparation using at most two
configurations. When two configurations are needed their energy is exactly the budget. -/
theorem exists_twoConfig_pureState_of_extreme_jointBudget (a : ι → ℝ) (b : ι → V) (B : ℝ) {v : V}
    (hv : v ∈ (convexHull ℝ (stressBudgetGenerators a b B)).extremePoints ℝ) :
    ∃ (ψ : EuclideanSpace ℂ ι) (i j : ι) (t : ℝ), ‖ψ‖ = 1 ∧ t ∈ Icc 0 1 ∧
      pureBasisLaw ψ = mixBasisLaw (pointBasisLaw i) (pointBasisLaw j) t ∧
      pureDiagonalMean ψ a ≤ B ∧ pureDiagonalVectorMean ψ b = v ∧
      (i = j ∨ (a i < B ∧ B < a j ∧ pureDiagonalMean ψ a = B)) := by
  have h := extremePoints_convexHull_subset hv
  rcases h with ⟨i, hi, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · change a i ≤ B at hi
    obtain ⟨ψ, hψ, hp⟩ := exists_pureBasisLaw (isBasisLaw_point i)
    refine ⟨ψ, i, i, 0, hψ, ⟨le_rfl, zero_le_one⟩, ?_, ?_, ?_, Or.inl rfl⟩
    · rw [hp]
      funext k
      simp only [mixBasisLaw, sub_zero, one_mul, zero_mul, add_zero]
    · simpa only [pureDiagonalMean, hp, diagonalMean_point] using hi
    · simp only [pureDiagonalVectorMean, hp, diagonalVectorMean_point]
  · let t := budgetChordWeight a B i j
    obtain ⟨ht, ht₁, hp, hE⟩ := budgetChordLaw a hi hj
    obtain ⟨ψ, hψ, hprob⟩ := exists_pureBasisLaw hp
    have hE' : pureDiagonalMean ψ a = B := by rwa [pureDiagonalMean, hprob]
    refine ⟨ψ, i, j, t, hψ, ⟨ht.le, ht₁.le⟩, hprob, hE'.le, ?_, Or.inr ⟨hi, hj, hE'⟩⟩
    simp only [pureDiagonalVectorMean, hprob, diagonalVectorMean_mix, diagonalVectorMean_point]

end FiniteStrain

/-- All simultaneous stresses of a prepared Ising state at a prescribed
energy budget are characterized by singles and feasible crossing chords. -/
theorem isingStrain_jointStressBudget_eq_convexHull {n : ℕ} {κ : Type*}
    (h : Fin (n + 2) → ℝ) (d : κ → Fin (n + 2) → ℝ) (J : Fin (n + 1) → ℝ) (B : ℝ) :
    let a := pathDiagEnergy (strainPath h (fun _ => 0) J 0)
    let b := fun x j => onsiteResponse (d j) x
    {v : κ → ℝ | ∃ ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))),
      ‖ψ‖ = 1 ∧ FiniteStrain.pureDiagonalMean ψ a ≤ B ∧ FiniteStrain.pureDiagonalVectorMean ψ b = v} =
      convexHull ℝ (FiniteStrain.stressBudgetGenerators a b B) :=
  FiniteStrain.pureJointStressBudgetRange_eq_generatorHull _ _ _

#print axioms FiniteStrain.basisStressBudgetRange_eq_generatorHull
#print axioms FiniteStrain.pureJointStressBudgetRange_eq_generatorHull
#print axioms FiniteStrain.stressBudgetProjection_eq_generatorHull
#print axioms FiniteStrain.convexHull_inter_linearSublevel_eq_generatorHull
#print axioms FiniteStrain.energyStressHull_inter_budget_eq_generatorHull
#print axioms FiniteStrain.stressBudgetGenerators_groundEnergy_eq
#print axioms FiniteStrain.exists_twoConfig_pureState_of_extreme_jointBudget
#print axioms isingStrain_jointStressBudget_eq_convexHull

end

end GaloisForLFunctions.HTGeometry
