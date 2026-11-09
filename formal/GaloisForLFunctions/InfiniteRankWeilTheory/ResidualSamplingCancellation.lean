import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Instances.Real.Lemmas

/-!+# Residual sampling cancellation from unbounded zeros

Integer dilations of an unbounded positive zero set meet every positive interval. For an even
continuous function, reflection and Baire's theorem give a dense G-delta of sampling bases
satisfying any prescribed countable family of positive accuracy schedules infinitely often.
-/

open Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

private theorem exists_sampled_zero_between {f : ℝ → ℝ}
    (hz : ∀ T : ℝ, ∃ z : ℝ, T ≤ z ∧ f z = 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ x ∈ Ioo a b, f ((n : ℝ) * x) = 0 := by
  have hb : 0 < b := ha.trans_lt hab
  obtain ⟨z, hzlarge, hfz⟩ := hz (max (b * (N : ℝ)) (a * b / (b - a)) + 1)
  have hzN : b * (N : ℝ) < z := by
    have := le_max_left (b * (N : ℝ)) (a * b / (b - a))
    linarith only [hzlarge, this]
  have hzgap : a * b / (b - a) < z := by
    have := le_max_right (b * (N : ℝ)) (a * b / (b - a))
    linarith only [hzlarge, this]
  have hz0 : 0 < z := (mul_nonneg hb.le (Nat.cast_nonneg N)).trans_lt hzN
  let n : ℕ := ⌊z / b⌋₊ + 1
  have hn : 0 < (n : ℝ) := by dsimp [n]; positivity
  have hN : N ≤ n := by
    have hfloor : N ≤ ⌊z / b⌋₊ := Nat.le_floor ((le_div_iff₀ hb).mpr (by linarith only [hzN]))
    dsimp [n]
    omega
  have hnb : (n : ℝ) * b ≤ z + b := by
    have h := mul_le_mul_of_nonneg_right (Nat.floor_le (div_pos hz0 hb).le) hb.le
    rw [div_mul_cancel₀ _ hb.ne'] at h
    dsimp [n]
    push_cast
    linarith only [h]
  have hzn : z < (n : ℝ) * b := by
    have h := (div_lt_iff₀ hb).mp (Nat.lt_floor_add_one (z / b))
    simpa only [n, Nat.cast_add, Nat.cast_one] using h
  have han : a * (n : ℝ) < z := by
    have hgap := (div_lt_iff₀ (sub_pos.mpr hab)).mp hzgap
    have hmul := mul_le_mul_of_nonneg_left hnb ha
    have hstrict : (a * (n : ℝ)) * b < z * b := by nlinarith only [hgap, hmul]
    exact (mul_lt_mul_iff_left₀ hb).mp hstrict
  refine ⟨n, hN, z / (n : ℝ), ⟨(lt_div_iff₀ hn).mpr han,
    (div_lt_iff₀ hn).mpr (by linarith only [hzn])⟩, ?_⟩
  rw [show (n : ℝ) * (z / (n : ℝ)) = z by field_simp]
  exact hfz

private def samplingCancellationTail (f : ℝ → ℝ) (ε : ℕ → ℝ) (N : ℕ) : Set ℝ :=
  ⋃ n ≥ N, {ℓ | |f ((n : ℝ) * ℓ)| < ε n}

private theorem isOpen_samplingCancellationTail {f : ℝ → ℝ} (hf : Continuous f)
    (ε : ℕ → ℝ) (N : ℕ) : IsOpen (samplingCancellationTail f ε N) := by
  apply isOpen_iUnion
  intro n
  apply isOpen_iUnion
  intro _
  exact isOpen_lt (hf.comp (continuous_const.mul continuous_id)).abs continuous_const

private theorem dense_samplingCancellationTail {f : ℝ → ℝ}
    (heven : ∀ t, f (-t) = f t) (hz : ∀ T : ℝ, ∃ z : ℝ, T ≤ z ∧ f z = 0)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (N : ℕ) :
    Dense (samplingCancellationTail f ε N) := by
  apply dense_iff_exists_between.mpr
  intro a b hab
  by_cases hb : 0 < b
  · obtain ⟨n, hn, x, hx, hfx⟩ := exists_sampled_zero_between hz
      (le_max_right a 0) (max_lt hab hb) N
    refine ⟨x, mem_iUnion₂.mpr ⟨n, hn, ?_⟩, (le_max_left a 0).trans_lt hx.1, hx.2⟩
    change |f ((n : ℝ) * x)| < ε n
    rw [hfx, abs_zero]
    exact hε n
  · obtain ⟨n, hn, x, hx, hfx⟩ := exists_sampled_zero_between hz
      (neg_nonneg.mpr (le_of_not_gt hb)) (neg_lt_neg hab) N
    refine ⟨-x, mem_iUnion₂.mpr ⟨n, hn, ?_⟩, by linarith only [hx.2],
      by linarith only [hx.1]⟩
    change |f ((n : ℝ) * -x)| < ε n
    rw [mul_neg, heven, hfx, abs_zero]
    exact hε n

/-- Bases meeting every prescribed accuracy schedule infinitely often. -/
def samplingCancellationBases (f : ℝ → ℝ) (ε : ℕ → ℕ → ℝ) : Set ℝ :=
  ⋂ p : ℕ × ℕ, samplingCancellationTail f (ε p.1) p.2

theorem mem_samplingCancellationBases_iff {f : ℝ → ℝ} {ε : ℕ → ℕ → ℝ} {ℓ : ℝ} :
    ℓ ∈ samplingCancellationBases f ε ↔
      ∀ m : ℕ, ∃ᶠ n : ℕ in atTop, |f ((n : ℝ) * ℓ)| < ε m n := by
  constructor
  · intro h m
    apply frequently_atTop.mpr
    intro N
    obtain ⟨n, hn, hsmall⟩ := mem_iUnion₂.mp (mem_iInter.mp h (m, N))
    exact ⟨n, hn, hsmall⟩
  · intro h
    apply mem_iInter.mpr
    intro p
    obtain ⟨n, hn, hsmall⟩ := frequently_atTop.mp (h p.1) p.2
    exact mem_iUnion₂.mpr ⟨n, hn, hsmall⟩

theorem isGδ_samplingCancellationBases {f : ℝ → ℝ} (hf : Continuous f)
    (ε : ℕ → ℕ → ℝ) : IsGδ (samplingCancellationBases f ε) :=
  IsGδ.iInter_of_isOpen fun p => isOpen_samplingCancellationTail hf (ε p.1) p.2

/-- Unbounded zeros of an even continuous function force residual recurrent sampling at any
countable family of positive accuracies. No lower bound on the accuracy is required. -/
theorem dense_samplingCancellationBases {f : ℝ → ℝ} (hf : Continuous f)
    (heven : ∀ t, f (-t) = f t) (hz : ∀ T : ℝ, ∃ z : ℝ, T ≤ z ∧ f z = 0)
    {ε : ℕ → ℕ → ℝ} (hε : ∀ m n, 0 < ε m n) :
    Dense (samplingCancellationBases f ε) :=
  dense_iInter_of_isOpen (fun p => isOpen_samplingCancellationTail hf (ε p.1) p.2)
    (fun p => dense_samplingCancellationTail heven hz (hε p.1) p.2)

/-- A dense G-delta in the real line meets every nonempty open interval uncountably. -/
theorem not_countable_inter_Ioo_of_dense_isGδ {S : Set ℝ} (hS : IsGδ S) (hd : Dense S)
    {a b : ℝ} (hab : a < b) : ¬ (S ∩ Ioo a b).Countable := by
  intro hcount
  have hm (x : ℝ) : IsMeagre ({x} : Set ℝ) :=
    residual_of_dense_open isClosed_singleton.isOpen_compl (dense_compl_singleton x)
  have hsmall : IsMeagre (S ∩ Ioo a b) := by
    have heq : (⋃ x ∈ S ∩ Ioo a b, ({x} : Set ℝ)) = S ∩ Ioo a b := by ext x; simp
    rw [← heq]
    exact isMeagre_biUnion hcount (fun x _ => hm x)
  have hcompl : IsMeagre Sᶜ := by
    rw [IsMeagre, compl_compl]
    exact residual_of_dense_Gδ hS hd
  apply not_isMeagre_of_isOpen isOpen_Ioo (Set.nonempty_Ioo.mpr hab)
  apply (hsmall.union hcompl).mono
  intro x hx
  by_cases hxs : x ∈ S
  · exact Or.inl ⟨hxs, hx⟩
  · exact Or.inr hxs

#print axioms dense_samplingCancellationBases
#print axioms not_countable_inter_Ioo_of_dense_isGδ

end GaloisForLFunctions.InfiniteRankWeilTheory
