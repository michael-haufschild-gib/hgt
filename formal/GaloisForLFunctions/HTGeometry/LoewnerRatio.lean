import GaloisForLFunctions.HTGeometry.OperatorNormLoewner
import Mathlib.Analysis.SpecificLimits.Basic
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinNormBounds

/-!
# The Loewner ratio

For strictly positive `a, b` in a C*-algebra the **Loewner ratio**

`M(a/b) := inf {s > 0 : a ≤ s b}`

is attained, is multiplicative along a chain (`M(a/c) ≤ M(a/b) M(b/c)`), and controls the norm
distance two-sidedly on a Loewner interval.  It is the multiplicative form of the Thompson
metric: `d_T(a,b) = log (max (M(a/b)) (M(b/a)))`.  Working with the ratio rather than its
logarithm keeps every estimate algebraic.
-/

open scoped Ring

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions.HTGeometry.BuresWasserstein

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A nonnegative multiple of the unit has a nonnegative coefficient. -/
lemma nonneg_of_smul_one_nonneg [Nontrivial A] {c : ℝ} (h : (0 : A) ≤ c • (1 : A)) : 0 ≤ c := by
  by_contra hc
  have hc' : c < 0 := not_le.mp hc
  have h2 : (0 : A) ≤ -(c • (1 : A)) := by
    rw [← neg_smul]
    exact smul_nonneg (by linarith [hc']) zero_le_one
  have h1 : c • (1 : A) ≤ 0 := neg_nonneg.mp h2
  have h3 : c • (1 : A) = 0 := le_antisymm h1 h
  rcases smul_eq_zero.mp h3 with hc0 | h1z
  · linarith [hc']
  · exact one_ne_zero h1z

/-- The Loewner order on multiples of the unit is the order on the coefficients. -/
lemma le_of_smul_one_le_smul_one [Nontrivial A] {c d : ℝ} (h : c • (1 : A) ≤ d • (1 : A)) :
    c ≤ d := by
  have hd : (0 : A) ≤ (d - c) • (1 : A) := by
    rw [sub_smul]
    exact sub_nonneg.mpr h
  linarith [nonneg_of_smul_one_nonneg hd]

/-- The **Loewner ratio** `M(a/b) = inf {s > 0 : a ≤ s b}`. -/
def loewnerRatio (a b : A) : ℝ := sInf {s : ℝ | 0 < s ∧ a ≤ s • b}

omit [StarOrderedRing A] in
lemma loewnerRatio_def (a b : A) : loewnerRatio a b = sInf {s : ℝ | 0 < s ∧ a ≤ s • b} := rfl

omit [StarOrderedRing A] in
lemma loewnerRatio_bddBelow (a b : A) : BddBelow {s : ℝ | 0 < s ∧ a ≤ s • b} :=
  ⟨0, fun _ hr => le_of_lt hr.1⟩

omit [StarOrderedRing A] in
lemma loewnerRatio_le {a b : A} {s : ℝ} (hs : 0 < s) (h : a ≤ s • b) :
    loewnerRatio a b ≤ s :=
  csInf_le (loewnerRatio_bddBelow a b) ⟨hs, h⟩

omit [StarOrderedRing A] in
lemma loewnerRatio_nonneg (a b : A) : 0 ≤ loewnerRatio a b := by
  rcases Set.eq_empty_or_nonempty {s : ℝ | 0 < s ∧ a ≤ s • b} with hem | hne
  · rw [loewnerRatio, hem, Real.sInf_empty]
  · exact le_csInf hne fun r hr => le_of_lt hr.1

/-- On a Loewner interval the defining set is nonempty. -/
lemma loewnerRatio_set_nonempty {a b : A} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (haβ : a ≤ β • (1 : A)) (hbα : α • (1 : A) ≤ b) :
    {s : ℝ | 0 < s ∧ a ≤ s • b}.Nonempty := by
  refine ⟨β / α, by positivity, ?_⟩
  refine haβ.trans ?_
  have h := smul_le_smul_of_nonneg_left hbα (by positivity : (0 : ℝ) ≤ β / α)
  rwa [smul_smul, div_mul_cancel₀ _ (ne_of_gt hα)] at h

/-- **The Loewner ratio is attained.** -/
theorem le_loewnerRatio_smul {a b : A} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hb : 0 ≤ b) (haβ : a ≤ β • (1 : A)) (hbα : α • (1 : A) ≤ b) :
    a ≤ loewnerRatio a b • b := by
  have hne := loewnerRatio_set_nonempty hα hβ haβ hbα
  have hclosed : IsClosed {s : ℝ | a ≤ s • b} := by
    have hset : {s : ℝ | a ≤ s • b} = (fun s : ℝ => s • b - a) ⁻¹' {x : A | 0 ≤ x} := by
      ext s
      simp [sub_nonneg]
    rw [hset]
    exact IsClosed.preimage (by fun_prop) CStarAlgebra.isClosed_nonneg
  have hmem : ∀ ε : ℝ, 0 < ε → loewnerRatio a b + ε ∈ {s : ℝ | a ≤ s • b} := by
    intro ε hε
    obtain ⟨s, hs, hslt⟩ := Real.lt_sInf_add_pos hne hε
    refine le_trans hs.2 ?_
    exact smul_le_smul_of_nonneg_right (le_of_lt hslt) hb
  have htend : Filter.Tendsto (fun n : ℕ => loewnerRatio a b + 1 / ((n : ℝ) + 1))
      Filter.atTop (nhds (loewnerRatio a b)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using Filter.Tendsto.const_add (loewnerRatio a b) h1
  exact hclosed.mem_of_tendsto htend
    (Filter.Eventually.of_forall fun n => hmem _ (by positivity))

/-- The Loewner ratio is bounded below on a Loewner interval. -/
theorem loewnerRatio_pos [Nontrivial A] {a b : A} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hb : 0 ≤ b) (haβ : a ≤ β • (1 : A)) (hbα : α • (1 : A) ≤ b)
    (haα : α • (1 : A) ≤ a) (hbβ : b ≤ β • (1 : A)) :
    0 < loewnerRatio a b := by
  have hM := le_loewnerRatio_smul hα hβ hb haβ hbα
  have hMnn := loewnerRatio_nonneg a b
  have h1 : loewnerRatio a b • b ≤ (loewnerRatio a b * β) • (1 : A) := by
    have := smul_le_smul_of_nonneg_left hbβ hMnn
    rwa [smul_smul] at this
  have h2 : α • (1 : A) ≤ (loewnerRatio a b * β) • (1 : A) := le_trans haα (le_trans hM h1)
  have h3 : α ≤ loewnerRatio a b * β := le_of_smul_one_le_smul_one h2
  nlinarith [h3, hMnn, hα, hβ]

/-- Chain multiplicativity of the Loewner ratio. -/
theorem loewnerRatio_mul_le {a b c : A} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hb : 0 ≤ b) (hc : 0 ≤ c)
    (haβ : a ≤ β • (1 : A)) (hbα : α • (1 : A) ≤ b)
    (hbβ : b ≤ β • (1 : A)) (hcα : α • (1 : A) ≤ c)
    (hMab : 0 < loewnerRatio a b) (hMbc : 0 < loewnerRatio b c) :
    loewnerRatio a c ≤ loewnerRatio a b * loewnerRatio b c := by
  have h1 := le_loewnerRatio_smul hα hβ hb haβ hbα
  have h2 := le_loewnerRatio_smul hα hβ hc hbβ hcα
  refine loewnerRatio_le (by positivity) ?_
  refine h1.trans ?_
  have h3 := smul_le_smul_of_nonneg_left h2 (le_of_lt hMab)
  rwa [smul_smul] at h3

/-- The Loewner ratio of a pair is at least one. -/
theorem one_le_loewnerRatio_mul [Nontrivial A] {a b : A} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haα : α • (1 : A) ≤ a) (haβ : a ≤ β • (1 : A))
    (hbα : α • (1 : A) ≤ b) (hbβ : b ≤ β • (1 : A)) :
    1 ≤ loewnerRatio a b * loewnerRatio b a := by
  have h1 := le_loewnerRatio_smul hα hβ hb haβ hbα
  have h2 := le_loewnerRatio_smul hα hβ ha hbβ haα
  have hM1 := loewnerRatio_nonneg a b
  have hchain : a ≤ (loewnerRatio a b * loewnerRatio b a) • a := by
    refine h1.trans ?_
    have h3 := smul_le_smul_of_nonneg_left h2 hM1
    rwa [smul_smul] at h3
  by_contra hlt'
  have hlt : loewnerRatio a b * loewnerRatio b a < 1 := not_le.mp hlt'
  have hk : (0 : A) ≤ (loewnerRatio a b * loewnerRatio b a - 1) • a := by
    rw [sub_smul, one_smul]
    exact sub_nonneg.mpr hchain
  have hbound : ((loewnerRatio a b * loewnerRatio b a - 1) : ℝ) • a
      ≤ ((loewnerRatio a b * loewnerRatio b a - 1) * α) • (1 : A) := by
    have hpos : (0 : ℝ) ≤ 1 - loewnerRatio a b * loewnerRatio b a := by linarith
    have hdiff : (0 : A) ≤ (1 - loewnerRatio a b * loewnerRatio b a) • (a - α • (1 : A)) :=
      smul_nonneg hpos (sub_nonneg.mpr haα)
    have hid : (1 - loewnerRatio a b * loewnerRatio b a) • (a - α • (1 : A))
        = ((loewnerRatio a b * loewnerRatio b a - 1) * α) • (1 : A)
          - (loewnerRatio a b * loewnerRatio b a - 1) • a := by
      rw [smul_sub, smul_smul]
      module
    rw [hid] at hdiff
    exact sub_nonneg.mp hdiff
  have hfin : (0 : A) ≤ ((loewnerRatio a b * loewnerRatio b a - 1) * α) • (1 : A) :=
    le_trans hk hbound
  have := nonneg_of_smul_one_nonneg hfin
  nlinarith [this, hα, hlt]

/-- The Loewner ratio is close to one for nearby elements. -/
theorem loewnerRatio_le_one_add {a b : A} {α : ℝ} (hα : 0 < α)
    (hasa : IsSelfAdjoint (a - b)) (hbα : α • (1 : A) ≤ b) :
    loewnerRatio a b ≤ 1 + ‖a - b‖ / α := by
  refine loewnerRatio_le (by positivity) ?_
  have h1 : a - b ≤ ‖a - b‖ • (1 : A) := by
    have h := hasa.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have h2 : ‖a - b‖ • (1 : A) ≤ (‖a - b‖ / α) • b := by
    have h := smul_le_smul_of_nonneg_left hbα (by positivity : (0 : ℝ) ≤ ‖a - b‖ / α)
    rwa [smul_smul, div_mul_cancel₀ _ (ne_of_gt hα)] at h
  have h3 : a ≤ b + (‖a - b‖ / α) • b := by
    have h4 := sub_le_iff_le_add.mp (le_trans h1 h2)
    rwa [add_comm] at h4
  rw [add_smul, one_smul]
  exact h3

/-- The Loewner ratio controls the norm distance from above. -/
theorem norm_sub_le_of_loewnerRatio {a b : A} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haβ : a ≤ β • (1 : A)) (hbα : α • (1 : A) ≤ b)
    (hbβ : b ≤ β • (1 : A)) (haα : α • (1 : A) ≤ a)
    {ρ : ℝ} (hρ1 : 1 ≤ ρ) (hab : loewnerRatio a b ≤ ρ) (hba : loewnerRatio b a ≤ ρ) :
    ‖a - b‖ ≤ 3 * β * (ρ - 1) := by
  have hone : ‖(1 : A)‖ ≤ 1 :=
    norm_le_of_le_smul_one zero_le_one zero_le_one (by rw [one_smul])
  have hMab := le_loewnerRatio_smul hα hβ hb haβ hbα
  have hMba := le_loewnerRatio_smul hα hβ ha hbβ haα
  have hupper : a - b ≤ ((ρ - 1) * β) • (1 : A) := by
    have h1 : a - b ≤ (loewnerRatio a b - 1) • b := by
      rw [sub_smul, one_smul]
      exact sub_le_sub_right hMab b
    refine h1.trans ?_
    have h2 : (loewnerRatio a b - 1) • b ≤ (ρ - 1) • b := by
      refine smul_le_smul_of_nonneg_right (by linarith) hb
    refine h2.trans ?_
    have h3 := smul_le_smul_of_nonneg_left hbβ (by linarith : (0 : ℝ) ≤ ρ - 1)
    rwa [smul_smul] at h3
  have hlower : b - a ≤ ((ρ - 1) * β) • (1 : A) := by
    have h1 : b - a ≤ (loewnerRatio b a - 1) • a := by
      rw [sub_smul, one_smul]
      exact sub_le_sub_right hMba a
    refine h1.trans ?_
    have h2 : (loewnerRatio b a - 1) • a ≤ (ρ - 1) • a := by
      refine smul_le_smul_of_nonneg_right (by linarith) ha
    refine h2.trans ?_
    have h3 := smul_le_smul_of_nonneg_left haβ (by linarith : (0 : ℝ) ≤ ρ - 1)
    rwa [smul_smul] at h3
  have hshift0 : (0 : A) ≤ (a - b) + ((ρ - 1) * β) • (1 : A) := by
    have hneg : -(a - b) ≤ ((ρ - 1) * β) • (1 : A) := by
      rw [neg_sub]
      exact hlower
    have h5 := neg_le_iff_add_nonneg.mp hneg
    rwa [add_comm] at h5
  have hshift1 : (a - b) + ((ρ - 1) * β) • (1 : A) ≤ (2 * ((ρ - 1) * β)) • (1 : A) := by
    have : (2 * ((ρ - 1) * β)) • (1 : A)
        = ((ρ - 1) * β) • (1 : A) + ((ρ - 1) * β) • (1 : A) := by
      rw [← add_smul]; congr 1; ring
    rw [this]
    exact add_le_add hupper (le_refl _)
  have hn : ‖(a - b) + ((ρ - 1) * β) • (1 : A)‖ ≤ 2 * ((ρ - 1) * β) :=
    norm_le_of_le_smul_one hshift0 (by nlinarith [hρ1, hβ]) hshift1
  have hsplit : ‖a - b‖ ≤ ‖(a - b) + ((ρ - 1) * β) • (1 : A)‖ + ‖((ρ - 1) * β) • (1 : A)‖ := by
    have h6 := norm_sub_le ((a - b) + ((ρ - 1) * β) • (1 : A)) (((ρ - 1) * β) • (1 : A))
    simpa using h6
  have hsm : ‖((ρ - 1) * β) • (1 : A)‖ ≤ (ρ - 1) * β := by
    have hnn : (0 : ℝ) ≤ (ρ - 1) * β := by nlinarith [hρ1, hβ]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn]
    nlinarith [hone, hnn, norm_nonneg (1 : A)]
  have hgoal : 2 * ((ρ - 1) * β) + (ρ - 1) * β = 3 * β * (ρ - 1) := by ring
  linarith [hsplit, hn, hsm, hgoal]

end

end GaloisForLFunctions.HTGeometry
