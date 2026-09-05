import GaloisForLFunctions.RHTower.EulerDeletionCoprimeWordPeriodicity
import GaloisForLFunctions.RHTower.EulerDeletionChronologicalScheduleBoundary

/-!
# Absolute boundary normal forms for mixed arithmetic chronological words

A finite ordered integration-by-parts identity retains the terminal source boundary and removes
one latest-in-time letter. Closed single-letter prefixes of order O(N^(-sigma)), with
sigma > 1/2, make the resulting carry absolutely summable whenever the shorter word prefixes
are bounded. Induction therefore admits every finite mixed word and gives its exact carry limit.

For literal Euler-deletion sources, all decay and closure inputs are proved at each hypothetical
right-half zeta zero. Prime/modulus labels and independently conjugated letters are retained.
There is no coprimality restriction, pointwise-square cancellation, uniform-in-length bound,
vanishing of higher words, or identification of different arithmetic factorization operations.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace RHTower.DeletionMixedWords
open DeletionCoprimeWords

variable {ι : Type*}

theorem word_cons_succ (x : ι → ℕ → ℂ) (i : ι) (w : List ι) (N : ℕ) :
    sourceWordPrefix x (i::w) (N+1) = sourceWordPrefix x (i::w) N + x i N * sourceWordPrefix x w N := by
  simp only [sourceWordPrefix, Finset.sum_range_succ]

def closedCarry (x : ι → ℕ → ℂ) (j i : ι) (w : List ι) (n : ℕ) : ℂ :=
  (∑ k ∈ Finset.range (n+1), x j k) * x i n * sourceWordPrefix x w n

/-- Finite ordered integration by parts, with the full terminal source boundary retained. -/
theorem word_boundary_identity (x : ι → ℕ → ℂ) (j i : ι) (w : List ι) (N : ℕ) :
    sourceWordPrefix x (j::i::w) N =
      (∑ n ∈ Finset.range N, x j n) * sourceWordPrefix x (i::w) N -
        ∑ n ∈ Finset.range N, closedCarry x j i w n := by
  induction N with
  | zero => simp [sourceWordPrefix]
  | succ N ih =>
    rw [word_cons_succ, ih, word_cons_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    simp only [closedCarry, Finset.sum_range_succ]
    ring

theorem summable_closedCarry {x : ι → ℕ → ℂ} {j i : ι} {w : List ι}
    {A B M σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hσ : 1/2 < σ)
    (hx : ∀ k, ‖∑ n ∈ Finset.range k, x j n‖ ≤ A*((k : ℝ)+1)^(-σ))
    (hy : ∀ n, ‖x i n‖ ≤ B*((n : ℝ)+1)^(-σ))
    (hw : ∀ n, ‖sourceWordPrefix x w n‖ ≤ M) :
    Summable (fun n => ‖closedCarry x j i w n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => ?_) (DeletionSchedule.summable_majorant hσ (A*B*M))
  have hr := DeletionSchedule.row_bound hA hB (by norm_num : (0 : ℝ) < 1)
    (by linarith : 0 ≤ σ) hx hy (k := n+1) (n := n) (by push_cast; linarith)
  simp only [Real.one_rpow, mul_one] at hr
  calc
    ‖closedCarry x j i w n‖ =
        ‖DeletionSchedule.row (x j) (x i) (n+1) n‖ * ‖sourceWordPrefix x w n‖ := by
      simp only [closedCarry, DeletionSchedule.row, norm_mul, norm_star]
    _ ≤ (A*B*((n : ℝ)+1)^(-2*σ))*M :=
      mul_le_mul hr (hw n) (norm_nonneg _) (by positivity)
    _ = (A*B*M)*((n : ℝ)+1)^(-2*σ) := by ring

/-- Closed last-letter endpoints convert each higher word into an absolutely summable carry
as soon as its two shorter chronological prefixes have limits. -/
theorem word_two_converges {x : ι → ℕ → ℂ} {j i : ι} {w : List ι}
    {A B σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hσ : 1/2 < σ)
    (hx : ∀ k, ‖∑ n ∈ Finset.range k, x j n‖ ≤ A*((k : ℝ)+1)^(-σ))
    (hy : ∀ n, ‖x i n‖ ≤ B*((n : ℝ)+1)^(-σ))
    (hz : Tendsto (fun N => ∑ n ∈ Finset.range N, x j n) atTop (nhds 0))
    {L K : ℂ} (hw : Tendsto (sourceWordPrefix x w) atTop (nhds L))
    (hiw : Tendsto (sourceWordPrefix x (i::w)) atTop (nhds K)) :
    Summable (fun n => ‖closedCarry x j i w n‖) ∧
    Tendsto (sourceWordPrefix x (j::i::w)) atTop (nhds (-∑' n, closedCarry x j i w n)) := by
  obtain ⟨M, hM⟩ := hw.norm.bddAbove_range
  have hb : ∀ n, ‖sourceWordPrefix x w n‖ ≤ M := fun n => hM (Set.mem_range_self n)
  have hs := summable_closedCarry hA hB hσ hx hy hb
  refine ⟨hs, ?_⟩
  have ht := (hz.mul hiw).sub hs.of_norm.hasSum.tendsto_sum_nat
  simpa only [zero_mul, zero_sub, ← word_boundary_identity] using ht

/-- Arbitrarily many mixed labels and every finite word are admitted by the same
closed-prefix decay hypotheses. This asserts no bound uniform in word length. -/
theorem every_word_converges (x : ι → ℕ → ℂ) (A B : ι → ℝ) {σ : ℝ}
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (hσ : 1/2 < σ)
    (hx : ∀ i k, ‖∑ n ∈ Finset.range k, x i n‖ ≤ A i*((k : ℝ)+1)^(-σ))
    (hy : ∀ i n, ‖x i n‖ ≤ B i*((n : ℝ)+1)^(-σ))
    (hz : ∀ i, Tendsto (fun N => ∑ n ∈ Finset.range N, x i n) atTop (nhds 0))
    (w : List ι) : ∃ L : ℂ, Tendsto (sourceWordPrefix x w) atTop (nhds L) := by
  have H : ∀ w : List ι,
      (∃ L : ℂ, Tendsto (sourceWordPrefix x w) atTop (nhds L)) ∧
      ∀ i, ∃ L : ℂ, Tendsto (sourceWordPrefix x (i::w)) atTop (nhds L) := by
    intro w
    induction w with
    | nil =>
      refine ⟨⟨1, tendsto_const_nhds⟩, fun i => ⟨0, ?_⟩⟩
      simpa [sourceWordPrefix] using hz i
    | cons i w ih =>
      refine ⟨ih.2 i, fun j => ?_⟩
      obtain ⟨L, hL⟩ := ih.1
      obtain ⟨K, hK⟩ := ih.2 i
      exact ⟨_, (word_two_converges (hA j) (hB i) hσ (hx j) (hy i) (hz j) hL hK).2⟩
  exact (H w).1

/-- Each prime-labelled letter independently retains its original or conjugated orientation. -/
def sourceJump (q : ι → ℕ) (orientation : ι → Bool) (s : ℂ) (i : ι) (n : ℕ) : ℂ :=
  if orientation i then star (eulerDeletionWeightedJump (q i) s n)
  else eulerDeletionWeightedJump (q i) s n

theorem sourceJump_prefix_bound (q : ι → ℕ) (orientation : ι → Bool)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) (i : ι) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, sourceJump q orientation ρ i n‖ ≤
      eulerDeletionAbelTailConstant (q i) ρ * ((N : ℝ)+1)^(-ρ.re) := by
  have h := norm_eulerDeletionWeightedJump_prefix_le_of_zeta_zero (q i) N hρ hρ1 hz
  cases he : orientation i
  · simpa [sourceJump, he] using h
  · have hsum : (∑ n ∈ Finset.range N, sourceJump q orientation ρ i n) =
        star (∑ n ∈ Finset.range N, eulerDeletionWeightedJump (q i) ρ n) := by
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro n _
      simp [sourceJump, he]
    rw [hsum, norm_star]
    exact h

theorem norm_sourceJump_le (q : ι → ℕ) (orientation : ι → Bool)
    (hq : ∀ i, 0 < q i) (s : ℂ) (i : ι) (n : ℕ) :
    ‖sourceJump q orientation s i n‖ ≤ (q i : ℝ)*((n : ℝ)+1)^(-s.re) := by
  have h := norm_eulerDeletionWeightedJump_le (hq i) s n
  cases he : orientation i <;> simpa [sourceJump, he] using h

theorem sourceJump_prefix_zero (q : ι → ℕ) (orientation : ι → Bool)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) (i : ι) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, sourceJump q orientation ρ i n)
      atTop (nhds 0) := by
  have h := tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero (q i) hρ hρ1 hz
  cases he : orientation i
  · simpa [sourceJump, he] using h
  · simpa [sourceJump, he, star_sum] using h.star

/-- At a hypothetical right-half zero every finite mixed-modulus, mixed-conjugation
chronological word converges. No coprimality, repetition-free, or uniform-length hypothesis. -/
theorem source_every_word_converges (q : ι → ℕ) (orientation : ι → Bool)
    (hq : ∀ i, 0 < q i) {ρ : ℂ} (hρ : 1/2 < ρ.re) (hρ1 : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) (w : List ι) :
    ∃ L : ℂ, Tendsto (sourceWordPrefix (sourceJump q orientation ρ) w) atTop (nhds L) := by
  have hρ0 : 0 < ρ.re := by linarith
  apply every_word_converges (sourceJump q orientation ρ)
    (fun i => eulerDeletionAbelTailConstant (q i) ρ) (fun i => (q i : ℝ))
    (fun i => ?_) (fun _ => by positivity) hρ
    (sourceJump_prefix_bound q orientation hρ0 hρ1 hz)
    (norm_sourceJump_le q orientation hq ρ)
    (sourceJump_prefix_zero q orientation hρ0 hρ1 hz) w
  unfold eulerDeletionAbelTailConstant
  positivity

/-- One exact, absolutely summable last-letter carry represents every finite mixed arithmetic
word of length at least two. A source boundary, not a rearrangement assumption, proves the limit. -/
theorem source_word_normal_form (q : ι → ℕ) (orientation : ι → Bool)
    (hq : ∀ i, 0 < q i) {ρ : ℂ} (hρ : 1/2 < ρ.re) (hρ1 : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) (j i : ι) (w : List ι) :
    Summable (fun n => ‖closedCarry (sourceJump q orientation ρ) j i w n‖) ∧
    Tendsto (sourceWordPrefix (sourceJump q orientation ρ) (j::i::w)) atTop
      (nhds (-∑' n, closedCarry (sourceJump q orientation ρ) j i w n)) := by
  have hρ0 : 0 < ρ.re := by linarith
  obtain ⟨L, hL⟩ := source_every_word_converges q orientation hq hρ hρ1 hz w
  obtain ⟨K, hK⟩ := source_every_word_converges q orientation hq hρ hρ1 hz (i::w)
  apply word_two_converges (A := eulerDeletionAbelTailConstant (q j) ρ)
    (B := (q i : ℝ)) (by unfold eulerDeletionAbelTailConstant; positivity)
    (by positivity) hρ
    (sourceJump_prefix_bound q orientation hρ0 hρ1 hz j)
    (norm_sourceJump_le q orientation hq ρ i)
    (sourceJump_prefix_zero q orientation hρ0 hρ1 hz j) hL hK

/-- The literal middle-index expression for a triple word. Both endpoint prefixes remain,
so this is not a vanishing or positivity assertion. -/
theorem source_triple_middle_form (q : ι → ℕ) (orientation : ι → Bool)
    (hq : ∀ i, 0 < q i) {ρ : ℂ} (hρ : 1/2 < ρ.re) (hρ1 : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) (j i k : ι) :
    Tendsto (sourceWordPrefix (sourceJump q orientation ρ) [j,i,k]) atTop
      (nhds (-∑' n, (∑ m ∈ Finset.range (n+1), sourceJump q orientation ρ j m) *
        sourceJump q orientation ρ i n *
        (∑ m ∈ Finset.range n, sourceJump q orientation ρ k m))) := by
  simpa only [closedCarry, sourceWordPrefix, mul_one] using
    (source_word_normal_form q orientation hq hρ hρ1 hz j i [k]).2

end RHTower.DeletionMixedWords

