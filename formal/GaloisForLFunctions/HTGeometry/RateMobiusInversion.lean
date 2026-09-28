import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Möbius inversion of rate measures under prime-scale transport

For a positive measure `ν` on the rate line put `A_n ν = n² (λ ↦ n²λ)_* ν`, so that `A_m A_n = A_{mn}`
and the finite deletion `∏_{p∈S}(I - A_p)ν` is the difference of the positive and negative parts
`Σ A_{∏T} ν` over sets `T ⊆ S` of even and odd cardinality. The Euler reconstruction of a seed `ξ`
is `Σ_{n≥1} A_n ξ`.

The basic identity: the deletion of an Euler sum is the Euler sum over integers coprime to the
deleted primes, `(positive part) = (negative part) + Σ_{(m,S)=1} A_m ξ` (every integer is counted
once more by the even than by the odd prime words dividing it exactly when it has no deleted prime).
More generally, deleting primes outside `Q` from the partial Euler sum over `Q`-free integers gives
the partial Euler sum over integers free of both.

Under the window condition `Σ_{m,n} A_{mn}ν(-∞, R] < ∞` for all `R`, every finite deletion is
positive iff `ν = Σ A_n ξ` for a unique positive seed `ξ`; the seed is the cofinal Möbius
inverse, positivity along one exhaustion suffices, and along every exhaustion the finite deletions
converge to `ξ` on sets of finite mass. The window condition holds for measures carried by
`[λ₀, ∞)`, `λ₀ > 0`, with finite Laplace transform (only finitely many dilations reach a bounded
window, and `D_S ν = ξ` there once `S` contains every `p` with `p²λ₀ ≤ R`), and for measures on
`(0, ∞)` with `M_q(ν) = ∫ λ^{-q} dν < ∞`, `q > 3/2`, through
`A_k ν(-∞, b] ≤ b^q M_q(ν) k^{2-2q}`. Also `M_q(Σ A_n ξ) = (Σ n^{2-2q}) M_q(ξ)`, and a finite
`M_q` bounds every Laplace transform.
-/
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Prime-scale transport of rate measures -/

/-- The dilation `λ ↦ n² λ` of the rate line. -/
def rateScale (n : ℕ) (l : ℝ) : ℝ := (n : ℝ) ^ 2 * l

theorem measurable_rateScale (n : ℕ) : Measurable (rateScale n) :=
  measurable_const.mul measurable_id

/-- Prime-scale transport of rate measures: `A_n ν = n² (λ ↦ n²λ)_* ν`. -/
def rateDilate (n : ℕ) (ν : Measure ℝ) : Measure ℝ :=
  ((n : ℝ≥0∞) ^ 2) • ν.map (rateScale n)

theorem rateDilate_apply (n : ℕ) (ν : Measure ℝ) {E : Set ℝ} (hE : MeasurableSet E) :
    rateDilate n ν E = (n : ℝ≥0∞) ^ 2 * ν (rateScale n ⁻¹' E) := by
  rw [rateDilate, Measure.smul_apply, Measure.map_apply (measurable_rateScale n) hE, smul_eq_mul]

theorem rateDilate_zero (ν : Measure ℝ) : rateDilate 0 ν = 0 := by
  simp [rateDilate]

theorem rateScale_one : rateScale 1 = id := by
  funext l; simp [rateScale]

theorem rateDilate_one (ν : Measure ℝ) : rateDilate 1 ν = ν := by
  simp [rateDilate, rateScale_one]

theorem rateScale_mul (m n : ℕ) : rateScale m ∘ rateScale n = rateScale (m * n) := by
  funext l; simp [rateScale]; ring

theorem rateDilate_rateDilate (m n : ℕ) (ν : Measure ℝ) :
    rateDilate m (rateDilate n ν) = rateDilate (m * n) ν := by
  ext E hE
  rw [rateDilate_apply _ _ hE, rateDilate_apply _ _ (measurable_rateScale m hE),
    rateDilate_apply _ _ hE, ← Set.preimage_comp, rateScale_mul, ← mul_assoc]
  congr 1
  push_cast
  ring

theorem rateDilate_add (n : ℕ) (μ ν : Measure ℝ) :
    rateDilate n (μ + ν) = rateDilate n μ + rateDilate n ν := by
  ext E hE
  simp only [Measure.add_apply, rateDilate_apply _ _ hE, mul_add]

theorem rateDilate_sum {ι : Type*} [Countable ι] (n : ℕ) (μ : ι → Measure ℝ) :
    rateDilate n (Measure.sum μ) = Measure.sum fun i => rateDilate n (μ i) := by
  ext E hE
  rw [rateDilate_apply _ _ hE, Measure.sum_apply _ (measurable_rateScale n hE),
    Measure.sum_apply _ hE, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun i => (rateDilate_apply _ _ hE).symm

theorem rateDilate_mono (n : ℕ) {μ ν : Measure ℝ} (h : μ ≤ ν) : rateDilate n μ ≤ rateDilate n ν :=
  Measure.le_iff.2 fun E hE => by
    rw [rateDilate_apply _ _ hE, rateDilate_apply _ _ hE]
    gcongr

/-! ## Prime words, deletion parts and Euler sums -/

/-- A prime word for the prime set `P`: a finite set of primes in `P` of the given parity. -/
def IsRateWord (P : ℕ → Prop) (e : Bool) (T : Finset ℕ) : Prop :=
  (∀ p ∈ T, p.Prime ∧ P p) ∧ (Even T.card ↔ e = true)

/-- The positive (`e = true`) and negative (`e = false`) parts of the deletion `∏_{p∈P}(I - A_p)`:
`Σ A_{∏T}` over prime words `T` of that parity. -/
def rateDeletionPart (P : ℕ → Prop) (e : Bool) (ν : Measure ℝ) : Measure ℝ :=
  Measure.sum fun T : Finset ℕ => by
    classical exact if IsRateWord P e T then rateDilate (∏ p ∈ T, p) ν else 0

/-- The Euler sum `Σ A_m ξ` over positive integers `m` with no prime factor in `P`. -/
def rateEulerPart (P : ℕ → Prop) (ξ : Measure ℝ) : Measure ℝ :=
  Measure.sum fun m : ℕ => by
    classical exact if ∀ p ∈ m.primeFactors, ¬ P p then rateDilate m ξ else 0

/-- The full Euler reconstruction `Σ_{n ≥ 1} A_n ξ`. -/
def rateEuler (ξ : Measure ℝ) : Measure ℝ := rateEulerPart (fun _ => False) ξ

theorem rateEuler_apply (ξ : Measure ℝ) {E : Set ℝ} (hE : MeasurableSet E) :
    rateEuler ξ E = ∑' m : ℕ, rateDilate m ξ E := by
  rw [rateEuler, rateEulerPart, Measure.sum_apply _ hE]
  exact tsum_congr fun m => by simp

theorem prod_pos_of_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : 0 < ∏ p ∈ T, p :=
  Finset.prod_pos fun p hp => (hT p hp).pos

/-- Reindexing along the multiples of `c ≥ 1`. -/
theorem tsum_mul_right_eq {c : ℕ} (hc : 0 < c) (F : ℕ → ℝ≥0∞) :
    ∑' n : ℕ, F (c * n) = ∑' m : ℕ, if c ∣ m then F m else 0 := by
  have hinj : Function.Injective fun n : ℕ => c * n := fun a b h => by
    simpa [hc.ne'] using h
  have h := hinj.tsum_eq (f := fun m => if c ∣ m then F m else 0) (by
    intro m hm
    by_contra hnot
    apply hm
    simp only
    rw [if_neg]
    rintro ⟨k, rfl⟩
    exact hnot ⟨k, rfl⟩)
  simpa using h

/-- The prime words dividing `m ≠ 0` are the subsets of its prime factors in `P`. -/
theorem isRateWord_dvd_iff (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hm : m ≠ 0) (T : Finset ℕ) :
    ((∀ p ∈ T, p.Prime ∧ P p) ∧ ∏ p ∈ T, p ∣ m) ↔ T ⊆ m.primeFactors.filter P := by
  constructor
  · rintro ⟨hT, hdvd⟩ p hp
    refine Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨(hT p hp).1, ?_, hm⟩, (hT p hp).2⟩
    exact (Finset.dvd_prod_of_mem _ hp).trans hdvd
  · intro hT
    refine ⟨fun p hp => ?_, ?_⟩
    · have := Finset.mem_filter.1 (hT hp)
      exact ⟨Nat.prime_of_mem_primeFactors this.1, this.2⟩
    · exact (Finset.prod_dvd_prod_of_subset _ _ _ (hT.trans (Finset.filter_subset _ _))).trans
        (Nat.prod_primeFactors_dvd m)

/-- Even words minus odd words dividing `m`: the count difference is `1` exactly when `m` has no
prime factor in `P`. -/
theorem card_even_words_eq (A : Finset ℕ) :
    (A.powerset.filter fun T => Even T.card).card =
      (A.powerset.filter fun T => ¬ Even T.card).card + if A = ∅ then 1 else 0 := by
  classical
  have h := Finset.sum_powerset_neg_one_pow_card (x := A)
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun T => Even T.card)] at h
  have he : ∑ T ∈ A.powerset.filter (fun T => Even T.card), ((-1 : ℤ) ^ T.card) =
      (A.powerset.filter fun T => Even T.card).card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_congr rfl fun T hT => by
      rw [(Finset.mem_filter.1 hT).2.neg_one_pow]; simp
  have ho : ∑ T ∈ A.powerset.filter (fun T => ¬ Even T.card), ((-1 : ℤ) ^ T.card) =
      -((A.powerset.filter fun T => ¬ Even T.card).card : ℤ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun T hT => by
      rw [(Nat.not_even_iff_odd.1 (Finset.mem_filter.1 hT).2).neg_one_pow]; simp
  rw [he, ho] at h
  split_ifs at h ⊢ <;> omega

theorem rateDilate_rateEuler_apply (c : ℕ) (ξ : Measure ℝ) {E : Set ℝ} (hE : MeasurableSet E) :
    rateDilate c (rateEuler ξ) E = ∑' m : ℕ, rateDilate (c * m) ξ E := by
  have h : rateEuler ξ = Measure.sum fun m : ℕ => rateDilate m ξ := by
    rw [rateEuler, rateEulerPart]
    congr 1
    funext m
    simp
  rw [h, rateDilate_sum, Measure.sum_apply _ hE]
  exact tsum_congr fun m => by rw [rateDilate_rateDilate]

theorem rateDilate_ite {p : Prop} {_ : Decidable p} (m : ℕ) (μ : Measure ℝ) :
    rateDilate m (if p then μ else 0) = if p then rateDilate m μ else 0 := by
  split_ifs
  · rfl
  · ext E hE; simp [rateDilate_apply _ _ hE]

theorem rateDilate_rateEulerPart_apply (Q : ℕ → Prop) [DecidablePred Q] (c : ℕ) (ξ : Measure ℝ)
    {E : Set ℝ} (hE : MeasurableSet E) :
    rateDilate c (rateEulerPart Q ξ) E =
      ∑' m : ℕ, if ∀ p ∈ m.primeFactors, ¬ Q p then rateDilate (c * m) ξ E else 0 := by
  rw [rateEulerPart, rateDilate_sum, Measure.sum_apply _ hE]
  refine tsum_congr fun m => ?_
  rw [rateDilate_ite]
  by_cases h : ∀ p ∈ m.primeFactors, ¬ Q p
  · rw [if_pos h, if_pos h, rateDilate_rateDilate]
  · rw [if_neg h, if_neg h]
    rfl

/-- Evaluation of a deletion part on a partial Euler sum `Σ_{m without prime factors in Q} A_m ξ`,
for deletions by primes outside `Q`: every such integer `m` is counted once for each prime word of
the given parity dividing it. -/
theorem rateDeletionPart_rateEulerPart_apply (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ p, p.Prime → P p → ¬ Q p) (e : Bool) (ξ : Measure ℝ) {E : Set ℝ}
    (hE : MeasurableSet E) :
    rateDeletionPart P e (rateEulerPart Q ξ) E = ∑' m : ℕ,
      (if ∀ p ∈ m.primeFactors, ¬ Q p then rateDilate m ξ E else 0) *
      (((m.primeFactors.filter P).powerset.filter fun T => (Even T.card ↔ e = true)).card :
        ℝ≥0∞) := by
  classical
  set G : ℕ → ℝ≥0∞ := fun m => if ∀ p ∈ m.primeFactors, ¬ Q p then rateDilate m ξ E else 0
  have hG0 : G 0 = 0 := by simp [G, rateDilate_zero]
  rw [rateDeletionPart, Measure.sum_apply _ hE]
  have hT : ∀ T : Finset ℕ,
      (if IsRateWord P e T then rateDilate (∏ p ∈ T, p) (rateEulerPart Q ξ) else 0) E =
        ∑' m : ℕ, if IsRateWord P e T ∧ ∏ p ∈ T, p ∣ m then G m else 0 := by
    intro T
    split_ifs with hw
    · have hc := prod_pos_of_primes fun p hp => (hw.1 p hp).1
      have hshift : ∀ n : ℕ, (if ∀ p ∈ n.primeFactors, ¬ Q p then
          rateDilate ((∏ p ∈ T, p) * n) ξ E else 0) = G ((∏ p ∈ T, p) * n) := by
        intro n
        rcases eq_or_ne n 0 with rfl | hn
        · simp [G, rateDilate_zero]
        · have hiff : (∀ p ∈ n.primeFactors, ¬ Q p) ↔
              ∀ p ∈ ((∏ p ∈ T, p) * n).primeFactors, ¬ Q p := by
            rw [Nat.primeFactors_mul hc.ne' hn,
              Nat.primeFactors_prod fun p hp => (hw.1 p hp).1]
            constructor
            · intro h p hp
              rcases Finset.mem_union.1 hp with hp | hp
              · exact hPQ p (hw.1 p hp).1 (hw.1 p hp).2
              · exact h p hp
            · exact fun h p hp => h p (Finset.mem_union_right _ hp)
          simp only [G]
          by_cases h : ∀ p ∈ n.primeFactors, ¬ Q p
          · rw [if_pos h, if_pos (hiff.1 h)]
          · rw [if_neg h, if_neg fun h' => h (hiff.2 h')]
      rw [rateDilate_rateEulerPart_apply _ _ _ hE]
      simp_rw [hshift]
      rw [tsum_mul_right_eq hc G]
      exact tsum_congr fun m => by simp [hw]
    · simp [hw]
  simp_rw [hT]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hG0, rateDilate_zero]
  have hsupp : ∀ T : Finset ℕ, T ∉ ((m.primeFactors.filter P).powerset.filter
      fun T => (Even T.card ↔ e = true)) →
      (if IsRateWord P e T ∧ ∏ p ∈ T, p ∣ m then G m else 0) = 0 := by
    intro T hT
    rw [if_neg]
    rintro ⟨⟨hTp, hpar⟩, hdvd⟩
    apply hT
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨(isRateWord_dvd_iff P hm T).1 ⟨hTp, hdvd⟩, hpar⟩
  rw [tsum_eq_sum hsupp, Finset.sum_congr rfl (fun T hT =>
    (show (if IsRateWord P e T ∧ ∏ p ∈ T, p ∣ m then G m else 0) = G m from if_pos (by
      rw [Finset.mem_filter, Finset.mem_powerset] at hT
      obtain ⟨h1, h2⟩ := (isRateWord_dvd_iff P hm T).2 hT.1
      exact ⟨⟨h1, hT.2⟩, h2⟩))), Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Evaluation of a deletion part on an Euler sum: every integer `m` is counted once for each prime
word of the given parity dividing it. -/
theorem rateDeletionPart_rateEuler_apply (P : ℕ → Prop) [DecidablePred P] (e : Bool)
    (ξ : Measure ℝ) {E : Set ℝ} (hE : MeasurableSet E) :
    rateDeletionPart P e (rateEuler ξ) E = ∑' m : ℕ, rateDilate m ξ E *
      (((m.primeFactors.filter P).powerset.filter fun T => (Even T.card ↔ e = true)).card :
        ℝ≥0∞) := by
  simpa [rateEuler] using
    rateDeletionPart_rateEulerPart_apply P (fun _ => False) (fun _ _ _ h => h) e ξ hE

/-- **Deletion of a partial Euler sum.**  For primes `P` disjoint from `Q`,
`D_P Σ_{m Q-free} A_m ξ = Σ_{m (Q ∪ P)-free} A_m ξ`, written as the identity
`(positive part) = (negative part) + Σ_{m (Q ∪ P)-free} A_m ξ` of positive measures. -/
theorem rateDeletionPart_rateEulerPart (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ p, p.Prime → P p → ¬ Q p) (ξ : Measure ℝ) :
    rateDeletionPart P true (rateEulerPart Q ξ) =
      rateDeletionPart P false (rateEulerPart Q ξ) + rateEulerPart (fun p => Q p ∨ P p) ξ := by
  classical
  ext E hE
  rw [Measure.add_apply, rateDeletionPart_rateEulerPart_apply P Q hPQ true ξ hE,
    rateDeletionPart_rateEulerPart_apply P Q hPQ false ξ hE, rateEulerPart, Measure.sum_apply _ hE,
    ← ENNReal.tsum_add]
  refine tsum_congr fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp [rateDilate_zero]
  have hc := card_even_words_eq (m.primeFactors.filter P)
  simp only [Bool.false_eq_true, iff_false, iff_true] at hc ⊢
  rw [hc]
  have hiff : (m.primeFactors.filter P = ∅) ↔ ∀ p ∈ m.primeFactors, ¬ P p :=
    Finset.filter_eq_empty_iff
  by_cases hQ : ∀ p ∈ m.primeFactors, ¬ Q p
  · rw [if_pos hQ]
    by_cases h : ∀ p ∈ m.primeFactors, ¬ P p
    · rw [if_pos (hiff.2 h), if_pos (show ∀ p ∈ m.primeFactors, ¬ (Q p ∨ P p) from
        fun p hp => not_or.2 ⟨hQ p hp, h p hp⟩)]
      push_cast
      ring
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg (show ¬ ∀ p ∈ m.primeFactors, ¬ (Q p ∨ P p) from
        fun h' => h fun p hp => (not_or.1 (h' p hp)).2)]
      simp
  · rw [if_neg hQ, if_neg (show ¬ ∀ p ∈ m.primeFactors, ¬ (Q p ∨ P p) from
      fun h' => hQ fun p hp => (not_or.1 (h' p hp)).1)]
    simp

/-- **Deletion of an Euler sum.** `D_P Σ_n A_n ξ = Σ_{m coprime to P} A_m ξ`, written as the identity
`(positive part) = (negative part) + Σ_{m coprime to P} A_m ξ` of positive measures. -/
theorem rateDeletionPart_rateEuler (P : ℕ → Prop) [DecidablePred P] (ξ : Measure ℝ) :
    rateDeletionPart P true (rateEuler ξ) =
      rateDeletionPart P false (rateEuler ξ) + rateEulerPart P ξ := by
  simpa [rateEuler] using rateDeletionPart_rateEulerPart P (fun _ => False) (fun _ _ _ h => h) ξ

theorem rateDeletionPart_false_le_rateEuler (P : ℕ → Prop) [DecidablePred P] (ξ : Measure ℝ) :
    rateDeletionPart P false (rateEuler ξ) ≤ rateDeletionPart P true (rateEuler ξ) := by
  rw [rateDeletionPart_rateEuler]
  exact Measure.le_add_right le_rfl

theorem rateEulerPart_le_rateEuler (Q : ℕ → Prop) (ξ : Measure ℝ) : rateEulerPart Q ξ ≤ rateEuler ξ := by
  classical
  refine Measure.le_iff.2 fun E hE => ?_
  rw [rateEulerPart, Measure.sum_apply _ hE, rateEuler_apply _ hE]
  refine ENNReal.tsum_le_tsum fun m => ?_
  split_ifs
  · exact le_rfl
  · simp

/-- Integers without prime factors are `0` and `1`, so the cofinal Euler part is the seed. -/
theorem rateEulerPart_prime (ξ : Measure ℝ) : rateEulerPart Nat.Prime ξ = ξ := by
  classical
  ext E hE
  rw [rateEulerPart, Measure.sum_apply _ hE, tsum_eq_single 1]
  · simp [rateDilate_one]
  · intro m hm
    rcases eq_or_ne m 0 with rfl | hm0
    · simp [rateDilate_zero]
    · have hm2 : 2 ≤ m := by omega
      have hp := Nat.minFac_prime (show m ≠ 1 from hm)
      rw [if_neg]
      · rfl
      · push Not
        exact ⟨m.minFac, Nat.mem_primeFactors.2 ⟨hp, Nat.minFac_dvd m, hm0⟩, hp⟩

/-- Dilations commute with deletion parts. -/
theorem rateEuler_rateDeletionPart (P : ℕ → Prop) (e : Bool) (ν : Measure ℝ) :
    rateEuler (rateDeletionPart P e ν) = rateDeletionPart P e (rateEuler ν) := by
  classical
  ext E hE
  rw [rateEuler_apply _ hE]
  simp only [rateDeletionPart]
  rw [Measure.sum_apply _ hE]
  simp_rw [rateDilate_sum, Measure.sum_apply _ hE, rateDilate_ite]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun T => ?_
  split_ifs with hw
  · rw [rateDilate_rateEuler_apply _ _ hE]
    exact tsum_congr fun m => by rw [rateDilate_rateDilate, mul_comm]
  · simp

/-! ## Window finiteness -/

/-- `Σ_{m,n} F(mn) = Σ_k τ(k) F(k)` for `F(0) = 0`. -/
theorem tsum_tsum_mul_eq {F : ℕ → ℝ≥0∞} (hF0 : F 0 = 0) :
    ∑' m : ℕ, ∑' n : ℕ, F (m * n) = ∑' k : ℕ, F k * (k.divisors.card : ℝ≥0∞) := by
  classical
  have hm : ∀ m : ℕ, ∑' n : ℕ, F (m * n) = ∑' k : ℕ, if 0 < m ∧ m ∣ k then F k else 0 := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF0]
    · rw [tsum_mul_right_eq hm]
      exact tsum_congr fun k => by simp [hm]
  simp_rw [hm]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp [hF0]
  rw [tsum_eq_sum (s := k.divisors) (fun m hm => by
    rw [if_neg]
    rintro ⟨hm0, hmk⟩
    exact hm (Nat.mem_divisors.2 ⟨hmk, hk⟩))]
  rw [Finset.sum_congr rfl (fun m hm => if_pos ⟨Nat.pos_of_mem_divisors hm,
    (Nat.mem_divisors.1 hm).1⟩), Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The prime words of either parity dividing `k ≠ 0` are at most its divisors. -/
theorem card_words_le_divisors (P : ℕ → Prop) [DecidablePred P] (e : Bool) {k : ℕ} (hk : k ≠ 0) :
    ((k.primeFactors.filter P).powerset.filter fun T => (Even T.card ↔ e = true)).card ≤
      k.divisors.card := by
  refine Finset.card_le_card_of_injOn (fun T => ∏ p ∈ T, p) (fun T hT => ?_) (fun T₁ hT₁ T₂ hT₂ h => ?_)
  · rw [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hT
    exact Nat.mem_divisors.2 ⟨((isRateWord_dvd_iff P hk T).2 hT.1).2, hk⟩
  · rw [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hT₁ hT₂
    have h₁ := Nat.primeFactors_prod (fun p hp => ((isRateWord_dvd_iff P hk T₁).2 hT₁.1).1 p hp |>.1)
    have h₂ := Nat.primeFactors_prod (fun p hp => ((isRateWord_dvd_iff P hk T₂).2 hT₂.1).1 p hp |>.1)
    simp only at h
    rw [← h₁, ← h₂, h]

/-- Window finiteness of all double dilations: `Σ_{m,n} A_{mn}ν(-∞, R] < ∞` for every `R`. -/
def RateWindowFinite (ν : Measure ℝ) : Prop :=
  ∀ R : ℝ, ∑' m : ℕ, ∑' n : ℕ, rateDilate (m * n) ν (Iic R) ≠ ∞

theorem rateEuler_rateDeletionPart_le (P : ℕ → Prop) (e : Bool) (ν : Measure ℝ) {E : Set ℝ}
    (hE : MeasurableSet E) :
    rateEuler (rateDeletionPart P e ν) E ≤ ∑' m : ℕ, ∑' n : ℕ, rateDilate (m * n) ν E := by
  classical
  rw [rateEuler_rateDeletionPart, rateDeletionPart_rateEuler_apply P e ν hE,
    tsum_tsum_mul_eq (F := fun k => rateDilate k ν E) (by simp [rateDilate_zero])]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp [rateDilate_zero]
  · gcongr
    exact_mod_cast card_words_le_divisors P e hk

theorem le_rateEuler (ξ : Measure ℝ) : ξ ≤ rateEuler ξ :=
  Measure.le_iff.2 fun E hE => by
    rw [rateEuler_apply _ hE]
    calc ξ E = rateDilate 1 ξ E := by rw [rateDilate_one]
      _ ≤ ∑' m : ℕ, rateDilate m ξ E := ENNReal.le_tsum 1

theorem RateWindowFinite.rateEuler_rateDeletionPart {ν : Measure ℝ} (hν : RateWindowFinite ν)
    (P : ℕ → Prop) (e : Bool) (R : ℝ) : rateEuler (rateDeletionPart P e ν) (Iic R) ≠ ∞ :=
  ne_top_of_le_ne_top (hν R) (rateEuler_rateDeletionPart_le P e ν measurableSet_Iic)

theorem RateWindowFinite.rateDeletionPart {ν : Measure ℝ} (hν : RateWindowFinite ν)
    (P : ℕ → Prop) (e : Bool) (R : ℝ) : rateDeletionPart P e ν (Iic R) ≠ ∞ :=
  ne_top_of_le_ne_top (hν.rateEuler_rateDeletionPart P e R) (le_rateEuler _ _)

theorem rateEuler_add (μ ν : Measure ℝ) : rateEuler (μ + ν) = rateEuler μ + rateEuler ν := by
  ext E hE
  rw [Measure.add_apply, rateEuler_apply _ hE, rateEuler_apply _ hE, rateEuler_apply _ hE,
    ← ENNReal.tsum_add]
  exact tsum_congr fun m => by rw [rateDilate_add, Measure.add_apply]

/-! ## Cancellation on windows -/

/-- The window partition `(-∞, 0], (0, 1], (1, 2], …`. -/
def rateWindow : ℕ → Set ℝ
  | 0 => Iic 0
  | j + 1 => Ioc (j : ℝ) (j + 1)

theorem measurableSet_rateWindow (j : ℕ) : MeasurableSet (rateWindow j) := by
  cases j <;> simp [rateWindow, measurableSet_Iic, measurableSet_Ioc]

theorem rateWindow_subset_Iic (j : ℕ) : rateWindow j ⊆ Iic (j : ℝ) := by
  cases j with
  | zero => simp [rateWindow]
  | succ j => intro x hx; simp only [rateWindow, mem_Ioc] at hx; simp only [mem_Iic]; push_cast; linarith [hx.2]

theorem pairwise_disjoint_rateWindow : Pairwise (Function.onFun Disjoint rateWindow) := by
  intro i j hij
  refine Set.disjoint_left.2 fun x hi hj => ?_
  rcases i with _ | i <;> rcases j with _ | j
  · exact hij rfl
  · simp only [rateWindow, mem_Iic, mem_Ioc] at hi hj
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith [hj.1]
  · simp only [rateWindow, mem_Iic, mem_Ioc] at hi hj
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith [hi.1]
  · simp only [rateWindow, mem_Ioc] at hi hj
    rcases lt_or_gt_of_ne (fun h : i = j => hij (by rw [h])) with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith [hi.2, hj.1]
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      linarith [hj.2, hi.1]

theorem iUnion_rateWindow : ⋃ j, rateWindow j = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
  rcases le_or_gt x 0 with hx | hx
  · exact ⟨0, hx⟩
  · refine ⟨⌈x⌉₊ - 1 + 1, ?_⟩
    have h1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hx).ne'
    simp only [rateWindow, mem_Ioc]
    have hc : ((⌈x⌉₊ - 1 : ℕ) : ℝ) = (⌈x⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub h1, Nat.cast_one]
    rw [hc]
    exact ⟨by linarith [Nat.ceil_lt_add_one hx.le], by linarith [Nat.le_ceil x]⟩

theorem restrict_sum_rateWindow (μ : Measure ℝ) :
    Measure.sum (fun j => μ.restrict (rateWindow j)) = μ := by
  rw [← Measure.restrict_iUnion pairwise_disjoint_rateWindow measurableSet_rateWindow,
    iUnion_rateWindow, Measure.restrict_univ]

/-- If `N ≤ M` and `N` is finite on every window `(-∞, R]`, then `M = ξ + N` for a positive
measure `ξ`. -/
theorem exists_add_eq_of_le {M N : Measure ℝ} (hNM : N ≤ M) (hN : ∀ R : ℝ, N (Iic R) ≠ ∞) :
    ∃ ξ : Measure ℝ, ξ + N = M := by
  have hfin : ∀ j, IsFiniteMeasure (N.restrict (rateWindow j)) := fun j =>
    isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top (hN j) (measure_mono (rateWindow_subset_Iic j)))
  refine ⟨Measure.sum fun j => M.restrict (rateWindow j) - N.restrict (rateWindow j), ?_⟩
  have hN' := restrict_sum_rateWindow N
  have hM' := restrict_sum_rateWindow M
  calc (Measure.sum fun j => M.restrict (rateWindow j) - N.restrict (rateWindow j)) + N
      = (Measure.sum fun j => M.restrict (rateWindow j) - N.restrict (rateWindow j)) +
          Measure.sum (fun j => N.restrict (rateWindow j)) := by rw [hN']
    _ = Measure.sum (fun j => (M.restrict (rateWindow j) - N.restrict (rateWindow j)) +
          N.restrict (rateWindow j)) := Measure.sum_add_sum _ _
    _ = Measure.sum (fun j => M.restrict (rateWindow j)) := by
        refine congrArg Measure.sum (funext fun j => ?_)
        haveI := hfin j
        exact Measure.sub_add_cancel_of_le (Measure.restrict_mono subset_rfl hNM)
    _ = M := hM'

/-- Cancellation of a measure that is finite on every window `(-∞, R]`. -/
theorem eq_of_add_eq_add {ξ ξ' N : Measure ℝ} (hN : ∀ R : ℝ, N (Iic R) ≠ ∞)
    (h : ξ + N = ξ' + N) : ξ = ξ' := by
  ext E hE
  have hwin : ∀ n : ℕ, ξ (E ∩ Iic (n : ℝ)) = ξ' (E ∩ Iic (n : ℝ)) := by
    intro n
    have h1 := congrArg (fun μ : Measure ℝ => μ (E ∩ Iic (n : ℝ))) h
    simp only [Measure.add_apply] at h1
    exact (ENNReal.add_left_inj (ne_top_of_le_ne_top (hN n) (measure_mono inter_subset_right))).1 h1
  have hU : E = ⋃ n : ℕ, E ∩ Iic (n : ℝ) := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_Iic]
    exact ⟨fun hx => ⟨⌈x⌉₊, hx, Nat.le_ceil x⟩, fun ⟨_, hx, _⟩ => hx⟩
  have hmono : Monotone fun n : ℕ => E ∩ Iic (n : ℝ) := fun a b hab =>
    inter_subset_inter_right _ (Iic_subset_Iic.2 (by exact_mod_cast hab))
  rw [hU, hmono.measure_iUnion, hmono.measure_iUnion]
  exact iSup_congr hwin

/-! ## The Möbius classification of the all-sieve rate cone -/

theorem rateDeletionPart_mono {P Q : ℕ → Prop} (hPQ : ∀ p, P p → Q p) (e : Bool)
    (ν : Measure ℝ) : rateDeletionPart P e ν ≤ rateDeletionPart Q e ν := by
  classical
  refine Measure.le_iff.2 fun E hE => ?_
  rw [rateDeletionPart, rateDeletionPart, Measure.sum_apply _ hE, Measure.sum_apply _ hE]
  refine ENNReal.tsum_le_tsum fun T => ?_
  by_cases hP : IsRateWord P e T
  · have hQ : IsRateWord Q e T := ⟨fun p hp => ⟨(hP.1 p hp).1, hPQ p (hP.1 p hp).2⟩, hP.2⟩
    simp [hP, hQ]
  · simp [hP]

/-- Cofinal positivity from a cofinal family of positive finite deletions: if every finite set of
primes lies in some prime set `S` with `D_S ν ≥ 0`, then the cofinal deletion is positive. -/
theorem rateDeletionPart_prime_le_of_cofinal {ν : Measure ℝ}
    (hcof : ∀ A : Finset ℕ, (∀ p ∈ A, p.Prime) → ∃ S : Finset ℕ, A ⊆ S ∧
      rateDeletionPart (· ∈ S) false ν ≤ rateDeletionPart (· ∈ S) true ν) :
    rateDeletionPart Nat.Prime false ν ≤ rateDeletionPart Nat.Prime true ν := by
  classical
  refine Measure.le_iff.2 fun E hE => ?_
  rw [show rateDeletionPart Nat.Prime false ν E = ∑' T : Finset ℕ,
      (if IsRateWord Nat.Prime false T then rateDilate (∏ p ∈ T, p) ν else 0) E by
    rw [rateDeletionPart, Measure.sum_apply _ hE], ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  obtain ⟨S, hAS, hS⟩ := hcof ((F.biUnion id).filter Nat.Prime) fun p hp => (Finset.mem_filter.1 hp).2
  calc ∑ T ∈ F, (if IsRateWord Nat.Prime false T then rateDilate (∏ p ∈ T, p) ν else 0) E
      ≤ ∑' T : Finset ℕ, (if IsRateWord (· ∈ S) false T then rateDilate (∏ p ∈ T, p) ν else 0) E := by
        refine le_trans (Finset.sum_le_sum fun T hT => ?_) (ENNReal.sum_le_tsum F)
        by_cases hw : IsRateWord Nat.Prime false T
        · have : IsRateWord (· ∈ S) false T := ⟨fun p hp => ⟨(hw.1 p hp).1,
            hAS (Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨T, hT, hp⟩, (hw.1 p hp).1⟩)⟩, hw.2⟩
          simp [hw, this]
        · simp [hw]
    _ = rateDeletionPart (· ∈ S) false ν E := by rw [rateDeletionPart, Measure.sum_apply _ hE]
    _ ≤ rateDeletionPart (· ∈ S) true ν E := hS E
    _ ≤ rateDeletionPart Nat.Prime true ν E := by
        refine le_trans ?_ (rateDeletionPart_mono (P := fun p => p ∈ S ∧ p.Prime)
          (fun p hp => hp.2) true ν E)
        refine le_of_eq ?_
        rw [rateDeletionPart, rateDeletionPart, Measure.sum_apply _ hE, Measure.sum_apply _ hE]
        refine tsum_congr fun T => ?_
        have : IsRateWord (· ∈ S) true T ↔ IsRateWord (fun p => p ∈ S ∧ p.Prime) true T :=
          ⟨fun h => ⟨fun p hp => ⟨(h.1 p hp).1, (h.1 p hp).2, (h.1 p hp).1⟩, h.2⟩,
            fun h => ⟨fun p hp => ⟨(h.1 p hp).1, (h.1 p hp).2.1⟩, h.2⟩⟩
        simp only [this]

/-- Positivity of every finite deletion forces positivity of the cofinal deletion. -/
theorem rateDeletionPart_prime_le_of_finite {ν : Measure ℝ}
    (hpos : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      rateDeletionPart (· ∈ S) false ν ≤ rateDeletionPart (· ∈ S) true ν) :
    rateDeletionPart Nat.Prime false ν ≤ rateDeletionPart Nat.Prime true ν :=
  rateDeletionPart_prime_le_of_cofinal fun A hA => ⟨A, subset_rfl, hpos A hA⟩

/-- Positivity along one increasing exhaustion of the primes already gives the cofinal positivity. -/
theorem rateDeletionPart_prime_le_of_exhaustion {ν : Measure ℝ} {S : ℕ → Finset ℕ}
    (hmono : Monotone S) (hex : ∀ p, p.Prime → ∃ j, p ∈ S j)
    (hpos : ∀ j, rateDeletionPart (· ∈ S j) false ν ≤ rateDeletionPart (· ∈ S j) true ν) :
    rateDeletionPart Nat.Prime false ν ≤ rateDeletionPart Nat.Prime true ν := by
  classical
  refine rateDeletionPart_prime_le_of_cofinal fun A hA => ?_
  have : ∃ j, A ⊆ S j := by
    induction A using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert a A ha ih =>
        obtain ⟨j₁, hj₁⟩ := ih (fun p hp => hA p (Finset.mem_insert_of_mem hp))
        obtain ⟨j₂, hj₂⟩ := hex a (hA a (Finset.mem_insert_self a A))
        refine ⟨max j₁ j₂, fun p hp => ?_⟩
        rcases Finset.mem_insert.1 hp with rfl | hp
        · exact hmono (le_max_right _ _) hj₂
        · exact hmono (le_max_left _ _) (hj₁ hp)
  obtain ⟨j, hj⟩ := this
  exact ⟨S j, hj, hpos j⟩

/-- **Seed formula.** An Euler reconstruction `ν = Σ A_n ξ` satisfies
`ξ + (odd cofinal part of ν) = (even cofinal part of ν)`: the seed is the local Möbius inverse. -/
theorem rateMobius_seed {ν ξ : Measure ℝ} (hξ : rateEuler ξ = ν) :
    ξ + rateDeletionPart Nat.Prime false ν = rateDeletionPart Nat.Prime true ν := by
  classical
  rw [← hξ, rateDeletionPart_rateEuler, rateEulerPart_prime, add_comm]

/-- **Uniqueness of the seed.** -/
theorem rateMobius_unique {ν ξ₁ ξ₂ : Measure ℝ} (hν : RateWindowFinite ν)
    (h₁ : rateEuler ξ₁ = ν) (h₂ : rateEuler ξ₂ = ν) : ξ₁ = ξ₂ :=
  eq_of_add_eq_add (hν.rateDeletionPart Nat.Prime false)
    ((rateMobius_seed h₁).trans (rateMobius_seed h₂).symm)

/-- **Existence of the seed** from positivity of the cofinal deletion. -/
theorem rateMobius_exists {ν : Measure ℝ} (hν : RateWindowFinite ν)
    (hpos : rateDeletionPart Nat.Prime false ν ≤ rateDeletionPart Nat.Prime true ν) :
    ∃ ξ : Measure ℝ, rateEuler ξ = ν := by
  classical
  obtain ⟨ξ, hξ⟩ := exists_add_eq_of_le hpos (hν.rateDeletionPart Nat.Prime false)
  refine ⟨ξ, ?_⟩
  have h1 := congrArg rateEuler hξ
  rw [rateEuler_add, rateEuler_rateDeletionPart, rateEuler_rateDeletionPart,
    rateDeletionPart_rateEuler Nat.Prime ν, rateEulerPart_prime,
    add_comm (rateDeletionPart Nat.Prime false (rateEuler ν)) ν] at h1
  refine eq_of_add_eq_add (fun R => ?_) h1
  rw [← rateEuler_rateDeletionPart]
  exact hν.rateEuler_rateDeletionPart _ _ R

/-- **Classification of the all-sieve rate cone.** For a rate measure with finite window masses of
all double dilations, every finite prime deletion `∏_{p∈S}(I - A_p)ν` is positive if and only if
`ν = Σ_{n ≥ 1} A_n ξ` for a unique positive seed `ξ`. -/
theorem rateMobius_classification {ν : Measure ℝ} (hν : RateWindowFinite ν) :
    (∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      rateDeletionPart (· ∈ S) false ν ≤ rateDeletionPart (· ∈ S) true ν) ↔
      ∃! ξ : Measure ℝ, rateEuler ξ = ν := by
  classical
  constructor
  · intro h
    obtain ⟨ξ, hξ⟩ := rateMobius_exists hν (rateDeletionPart_prime_le_of_finite h)
    exact ⟨ξ, hξ, fun ξ' hξ' => rateMobius_unique hν hξ' hξ⟩
  · rintro ⟨ξ, hξ, -⟩ S -
    rw [← hξ]
    exact rateDeletionPart_false_le_rateEuler _ ξ

/-! ## The rate-gap class -/

theorem measure_Iic_ne_top_of_laplace {ν : Measure ℝ}
    (hlap : ∫⁻ l, ENNReal.ofReal (Real.exp (-l)) ∂ν ≠ ∞) (R : ℝ) : ν (Iic R) ≠ ∞ := by
  have h : ENNReal.ofReal (Real.exp (-R)) * ν (Iic R) ≤ ∫⁻ l, ENNReal.ofReal (Real.exp (-l)) ∂ν := by
    rw [← lintegral_indicator_const measurableSet_Iic]
    refine lintegral_mono fun l => ?_
    by_cases hl : l ∈ Iic R
    · rw [indicator_of_mem hl]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by simp only [mem_Iic] at hl; linarith))
    · rw [indicator_of_notMem hl]; exact zero_le
  have hpos : ENNReal.ofReal (Real.exp (-R)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  intro htop
  rw [htop, ENNReal.mul_top hpos] at h
  exact hlap (top_le_iff.1 h)

theorem rateDilate_Iic (n : ℕ) (hn : 0 < n) (ν : Measure ℝ) (R : ℝ) :
    rateDilate n ν (Iic R) = (n : ℝ≥0∞) ^ 2 * ν (Iic (R / (n : ℝ) ^ 2)) := by
  rw [rateDilate_apply _ _ measurableSet_Iic]
  congr 2
  ext l
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  simp only [mem_preimage, rateScale, mem_Iic]
  rw [le_div_iff₀ hn2, mul_comm]

/-- **Rate gap ⇒ window finiteness.** If `ν` is carried by `[λ₀, ∞)`, `λ₀ > 0`, and has a finite
Laplace transform, then on `(-∞, R]` only the finitely many dilations with `k² λ₀ ≤ R` survive. -/
theorem rateWindowFinite_of_gap {ν : Measure ℝ} {l₀ : ℝ} (hl₀ : 0 < l₀) (hsupp : ν (Iio l₀) = 0)
    (hlap : ∫⁻ l, ENNReal.ofReal (Real.exp (-l)) ∂ν ≠ ∞) : RateWindowFinite ν := by
  intro R
  set K : ℕ := ⌈R / l₀⌉₊
  have hzero : ∀ k : ℕ, K < k → rateDilate k ν (Iic R) = 0 := by
    intro k hk
    have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hk
    rw [rateDilate_Iic k hk0]
    have hlt : R / (k : ℝ) ^ 2 < l₀ := by
      have hk1 : (K : ℝ) < k := by exact_mod_cast hk
      have hKR : R / l₀ ≤ K := Nat.le_ceil _
      have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
        nlinarith
      have hkpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
      rw [div_lt_iff₀ hkpos]
      rw [div_le_iff₀ hl₀] at hKR
      nlinarith
    rw [measure_mono_null (Iic_subset_Iio.2 hlt) hsupp, mul_zero]
  have hfin : ∀ k : ℕ, rateDilate k ν (Iic R) ≠ ∞ := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [rateDilate_zero]
    · rw [rateDilate_Iic k hk]
      exact ENNReal.mul_ne_top (by simp) (measure_Iic_ne_top_of_laplace hlap _)
  have hinner : ∀ m : ℕ, ∑' n : ℕ, rateDilate (m * n) ν (Iic R) =
      ∑ n ∈ Finset.range (K + 1), rateDilate (m * n) ν (Iic R) := by
    intro m
    refine tsum_eq_sum fun n hn => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [rateDilate_zero]
    · refine hzero _ ?_
      have : K < n := by simpa using hn
      nlinarith
  simp_rw [hinner]
  rw [tsum_eq_sum (s := Finset.range (K + 1)) fun m hm => ?_]
  · exact ENNReal.sum_ne_top.2 fun m _ => ENNReal.sum_ne_top.2 fun n _ => hfin _
  · refine Finset.sum_eq_zero fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [rateDilate_zero]
    · refine hzero _ ?_
      have : K < m := by simpa using hm
      nlinarith

/-- **Window stabilization (3).** In the rate-gap class, `D_S ν = ξ` on `(-∞, R]` as soon as `S`
contains every prime `p` with `p² λ₀ ≤ R`. -/
theorem rateDeletion_eq_seed_of_gap {ν ξ : Measure ℝ} {l₀ R : ℝ} (hl₀ : 0 < l₀)
    (hξ : rateEuler ξ = ν) (hsupp : ν (Iio l₀) = 0) (S : Finset ℕ)
    (hS : ∀ p : ℕ, p.Prime → (p : ℝ) ^ 2 * l₀ ≤ R → p ∈ S) :
    (rateDeletionPart (· ∈ S) true ν).restrict (Iic R) =
      (rateDeletionPart (· ∈ S) false ν + ξ).restrict (Iic R) := by
  classical
  have hξν : ξ ≤ ν := hξ ▸ le_rateEuler ξ
  have hξsupp : ξ (Iio l₀) = 0 := le_zero_iff.1 ((hξν _).trans hsupp.le)
  rw [← hξ, rateDeletionPart_rateEuler, Measure.restrict_add, Measure.restrict_add]
  congr 1
  rw [rateEulerPart, Measure.restrict_sum _ measurableSet_Iic]
  ext E hE
  rw [Measure.sum_apply _ hE, tsum_eq_single 1]
  · simp [rateDilate_one]
  · intro m hm1
    split_ifs with hcop
    · rcases eq_or_ne m 0 with rfl | hm0
      · simp [rateDilate_zero]
      · have hq := Nat.minFac_prime hm1
        have hqm : m.minFac ∈ m.primeFactors :=
          Nat.mem_primeFactors.2 ⟨hq, Nat.minFac_dvd m, hm0⟩
        have hqS : m.minFac ∉ S := hcop _ hqm
        have hbig : R < (m.minFac : ℝ) ^ 2 * l₀ := by
          by_contra h
          exact hqS (hS _ hq (not_lt.1 h))
        have hmq : (m.minFac : ℝ) ≤ m := by
          exact_mod_cast Nat.minFac_le (Nat.pos_of_ne_zero hm0)
        have hq0 : (0 : ℝ) ≤ m.minFac := Nat.cast_nonneg _
        have hmpos : (0 : ℝ) < (m : ℝ) ^ 2 := by
          have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
          positivity
        have hlt : R / (m : ℝ) ^ 2 < l₀ := by
          rw [div_lt_iff₀ hmpos]
          have : (m.minFac : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ hq0 hmq 2
          nlinarith
        rw [Measure.restrict_apply hE]
        refine le_zero_iff.1 ((measure_mono inter_subset_right).trans ?_)
        rw [rateDilate_Iic m (Nat.pos_of_ne_zero hm0),
          measure_mono_null (Iic_subset_Iio.2 hlt) hξsupp, mul_zero]
    · simp

/-! ## The negative-moment class `M_q(ν) < ∞`, `q > 3/2` -/

/-- The negative moment `M_q(ν) = ∫_{(0,∞)} λ^{-q} dν`. -/
def rateNegMoment (q : ℝ) (ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ l, (Ioi (0 : ℝ)).indicator (fun l => ENNReal.ofReal (l ^ (-q))) l ∂ν

theorem measure_Ioc_le_rateNegMoment {q : ℝ} (hq : 0 ≤ q) (ν : Measure ℝ) {x : ℝ} (hx : 0 < x) :
    ν (Ioc 0 x) ≤ ENNReal.ofReal (x ^ q) * rateNegMoment q ν := by
  rw [rateNegMoment, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator_one measurableSet_Ioc]
  refine lintegral_mono fun l => ?_
  by_cases hl : l ∈ Ioc 0 x
  · rw [indicator_of_mem hl, indicator_of_mem (show l ∈ Ioi (0 : ℝ) from hl.1),
      ← ENNReal.ofReal_mul (by positivity)]
    have hl0 : 0 < l := hl.1
    have hlq : 0 < l ^ q := Real.rpow_pos_of_pos hl0 q
    have hxl : l ^ q ≤ x ^ q := Real.rpow_le_rpow hl0.le hl.2 hq
    rw [Pi.one_apply, ENNReal.one_le_ofReal, Real.rpow_neg hl0.le, ← div_eq_mul_inv,
      one_le_div hlq]
    exact hxl
  · rw [indicator_of_notMem hl]; exact zero_le

/-- **(W2).** On `E ⊆ (-∞, b]`, `A_k ν(E) ≤ b^q M_q(ν) k^{2-2q}` for a rate measure carried by
`(0, ∞)`. -/
theorem rateDilate_le_negMoment {q : ℝ} (hq : 0 ≤ q) {ν : Measure ℝ} (hν0 : ν (Iic 0) = 0)
    {k : ℕ} (hk : 0 < k) {b : ℝ} (hb : 0 < b) {E : Set ℝ} (hEb : E ⊆ Iic b) :
    rateDilate k ν E ≤ ENNReal.ofReal (b ^ q * (k : ℝ) ^ (2 - 2 * q)) * rateNegMoment q ν := by
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by have : (0 : ℝ) < k := (by exact_mod_cast hk); positivity
  have hx : 0 < b / (k : ℝ) ^ 2 := div_pos hb hk2
  calc rateDilate k ν E ≤ rateDilate k ν (Iic b) := measure_mono hEb
    _ = (k : ℝ≥0∞) ^ 2 * ν (Iic (b / (k : ℝ) ^ 2)) := rateDilate_Iic k hk ν b
    _ ≤ (k : ℝ≥0∞) ^ 2 * ν (Ioc 0 (b / (k : ℝ) ^ 2)) := by
        refine mul_le_mul' le_rfl ?_
        calc ν (Iic (b / (k : ℝ) ^ 2)) ≤ ν (Iic 0 ∪ Ioc 0 (b / (k : ℝ) ^ 2)) := by
              refine measure_mono fun x hx' => ?_
              rcases le_or_gt x 0 with h | h
              · exact Or.inl h
              · exact Or.inr ⟨h, hx'⟩
          _ ≤ ν (Iic 0) + ν (Ioc 0 (b / (k : ℝ) ^ 2)) := measure_union_le _ _
          _ = ν (Ioc 0 (b / (k : ℝ) ^ 2)) := by rw [hν0, zero_add]
    _ ≤ (k : ℝ≥0∞) ^ 2 * (ENNReal.ofReal ((b / (k : ℝ) ^ 2) ^ q) * rateNegMoment q ν) :=
        mul_le_mul' le_rfl (measure_Ioc_le_rateNegMoment hq ν hx)
    _ = ENNReal.ofReal (b ^ q * (k : ℝ) ^ (2 - 2 * q)) * rateNegMoment q ν := by
        rw [← mul_assoc]
        congr 1
        have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
        rw [show ((k : ℝ≥0∞) ^ 2) = ENNReal.ofReal ((k : ℝ) ^ 2) by
          rw [ENNReal.ofReal_pow hk0.le, ENNReal.ofReal_natCast], ← ENNReal.ofReal_mul hk2.le]
        congr 1
        rw [Real.div_rpow hb.le hk2.le, show ((k : ℝ) ^ 2) ^ q = (k : ℝ) ^ (2 * q) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]; norm_num,
          Real.rpow_sub hk0, show ((k : ℝ) ^ (2 : ℝ)) = (k : ℝ) ^ 2 by norm_cast]
        field_simp

/-- **Negative moment `q > 3/2` ⇒ window finiteness**, through
`Σ_{m,n} A_{mn}ν(-∞, R] ≤ R^q M_q(ν) (Σ_m m^{2-2q})²`. -/
theorem rateWindowFinite_of_negMoment {q : ℝ} (hq : 3 / 2 < q) {ν : Measure ℝ}
    (hν0 : ν (Iic 0) = 0) (hM : rateNegMoment q ν ≠ ∞) : RateWindowFinite ν := by
  intro R
  have hq0 : 0 ≤ q := by linarith
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ (2 - 2 * q) :=
    Real.summable_nat_rpow.2 (by linarith)
  rcases le_or_gt R 0 with hR | hR
  · have hz : ∀ k : ℕ, rateDilate k ν (Iic R) = 0 := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [rateDilate_zero]
      · rw [rateDilate_Iic k hk]
        have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by have : (0 : ℝ) < k := (by exact_mod_cast hk); positivity
        rw [measure_mono_null (Iic_subset_Iic.2 (div_nonpos_of_nonpos_of_nonneg hR hk2.le)) hν0,
          mul_zero]
    simp [hz]
  · set g : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((n : ℝ) ^ (2 - 2 * q))
    have hg0 : g 0 = 0 := by
      simp only [g, Nat.cast_zero]
      rw [Real.zero_rpow (by linarith), ENNReal.ofReal_zero]
    have hbound : ∀ m n : ℕ, rateDilate (m * n) ν (Iic R) ≤
        ENNReal.ofReal (R ^ q) * rateNegMoment q ν * (g m * g n) := by
      intro m n
      rcases Nat.eq_zero_or_pos (m * n) with h0 | hmn
      · rw [h0, rateDilate_zero]; exact zero_le
      · have hm : 0 < m := Nat.pos_of_mul_pos_right hmn
        have hn : 0 < n := Nat.pos_of_mul_pos_left hmn
        refine (rateDilate_le_negMoment hq0 hν0 hmn hR subset_rfl).trans (le_of_eq ?_)
        simp only [g]
        rw [← ENNReal.ofReal_mul (by positivity), mul_right_comm,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        push_cast
        rw [Real.mul_rpow (by positivity) (by positivity)]
    have hG : ∑' n : ℕ, g n ≠ ∞ := by
      simp only [g]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
      exact ENNReal.ofReal_ne_top
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun m => ENNReal.tsum_le_tsum fun n =>
      hbound m n)
    simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM)
      (ENNReal.mul_ne_top hG hG)

theorem measurable_negMomentKernel (q : ℝ) :
    Measurable ((Ioi (0 : ℝ)).indicator fun l : ℝ => ENNReal.ofReal (l ^ (-q))) :=
  (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).indicator measurableSet_Ioi

theorem rateEuler_eq_sum (ξ : Measure ℝ) : rateEuler ξ = Measure.sum fun m : ℕ => rateDilate m ξ := by
  rw [rateEuler, rateEulerPart]
  congr 1
  funext m
  simp

/-- **(W3).** `M_q(Σ A_n ξ) = (Σ_n n^{2-2q}) M_q(ξ)` for `q > 1`. -/
theorem rateNegMoment_rateEuler {q : ℝ} (hq : 1 < q) (ξ : Measure ℝ) :
    rateNegMoment q (rateEuler ξ) =
      (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) ^ (2 - 2 * q))) * rateNegMoment q ξ := by
  rw [rateNegMoment, rateEuler_eq_sum, lintegral_sum_measure, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [rateDilate_zero, lintegral_zero_measure, Nat.cast_zero]
    rw [Real.zero_rpow (by linarith), ENNReal.ofReal_zero, zero_mul]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : Measurable fun a : ℝ =>
      (Ioi (0 : ℝ)).indicator (fun l => ENNReal.ofReal (l ^ (-q))) (rateScale n a) :=
    (measurable_negMomentKernel q).comp (measurable_rateScale n)
  rw [rateDilate, lintegral_smul_measure, lintegral_map (measurable_negMomentKernel q)
    (measurable_rateScale n), smul_eq_mul, rateNegMoment,
    ← lintegral_const_mul _ (measurable_negMomentKernel q), ← lintegral_const_mul _ hm]
  refine lintegral_congr fun l => ?_
  simp only [rateScale]
  by_cases hl : 0 < l
  · have hnl : 0 < (n : ℝ) ^ 2 * l := by positivity
    rw [indicator_of_mem (show (n : ℝ) ^ 2 * l ∈ Ioi 0 from hnl),
      indicator_of_mem (show l ∈ Ioi 0 from hl),
      show ((n : ℝ≥0∞) ^ 2) = ENNReal.ofReal ((n : ℝ) ^ 2) by
        rw [ENNReal.ofReal_pow hn0.le, ENNReal.ofReal_natCast],
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow (by positivity) hl.le, show ((n : ℝ) ^ 2) ^ (-q) = (n : ℝ) ^ (-2 * q) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num,
      show (2 - 2 * q) = (2 : ℝ) + (-2 * q) by ring, Real.rpow_add hn0,
      show ((n : ℝ) ^ (2 : ℝ)) = (n : ℝ) ^ 2 by norm_cast]
    ring
  · have hnl : ¬ (0 < (n : ℝ) ^ 2 * l) := by
      intro h
      exact hl (pos_of_mul_pos_right h (by positivity))
    rw [indicator_of_notMem (show (n : ℝ) ^ 2 * l ∉ Ioi 0 from hnl),
      indicator_of_notMem (show l ∉ Ioi 0 from hl), mul_zero, mul_zero]

/-- `λ^q e^{-tλ} ≤ (q/t)^q e^{-q}` for `λ, t, q > 0`. -/
theorem rpow_mul_exp_neg_le_sharp {q t l : ℝ} (hq : 0 < q) (ht : 0 < t) (hl : 0 < l) :
    l ^ q * Real.exp (-(t * l)) ≤ (q / t) ^ q * Real.exp (-q) := by
  set u := t * l / q
  have hu : 0 < u := by positivity
  have hlu : l = q / t * u := by simp only [u]; field_simp
  have hexp : u ≤ Real.exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
  have hpow : u ^ q ≤ Real.exp (q * (u - 1)) := by
    calc u ^ q ≤ Real.exp (u - 1) ^ q := Real.rpow_le_rpow hu.le hexp hq.le
      _ = Real.exp (q * (u - 1)) := by rw [← Real.exp_mul, mul_comm]
  rw [hlu, Real.mul_rpow (by positivity) hu.le]
  have htl : t * (q / t * u) = q * u := by field_simp
  rw [htl, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc u ^ q * Real.exp (-(q * u)) ≤ Real.exp (q * (u - 1)) * Real.exp (-(q * u)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.exp (-q) := by rw [← Real.exp_add]; congr 1; ring

/-- A finite negative moment makes every Laplace transform finite. -/
theorem lintegral_exp_le_rateNegMoment {q t : ℝ} (hq : 0 < q) (ht : 0 < t) {ν : Measure ℝ}
    (hν0 : ν (Iic 0) = 0) :
    ∫⁻ l, ENNReal.ofReal (Real.exp (-(t * l))) ∂ν ≤
      ENNReal.ofReal ((q / t) ^ q * Real.exp (-q)) * rateNegMoment q ν := by
  rw [rateNegMoment, ← lintegral_const_mul _ (measurable_negMomentKernel q)]
  have hae : ∀ᵐ l ∂ν, 0 < l := by
    rw [ae_iff]
    simp only [not_lt]
    exact hν0
  refine lintegral_mono_ae (hae.mono fun l hl => ?_)
  rw [indicator_of_mem (show l ∈ Ioi 0 from hl), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := rpow_mul_exp_neg_le_sharp hq ht hl
  have hlq : 0 < l ^ q := Real.rpow_pos_of_pos hl q
  rw [Real.rpow_neg hl.le, ← div_eq_mul_inv, le_div_iff₀ hlq]
  linarith [mul_comm (l ^ q) (Real.exp (-(t * l)))]

/-! ## Cofinal convergence of finite deletions -/

/-- A sequence dominated by `F`, vanishing at `0` and on `[2, N]`, sums to at most
`F 1 + Σ_{k > N} F k`. -/
theorem tsum_le_one_add_tail {g F : ℕ → ℝ≥0∞} {N : ℕ} (hgF : ∀ m, g m ≤ F m)
    (hmid : ∀ m, 2 ≤ m → m ≤ N → g m = 0) (h0 : g 0 = 0) :
    ∑' m, g m ≤ F 1 + ∑' k, F (k + (N + 1)) := by
  rw [← (ENNReal.summable (f := fun n => g (n + (N + 1)))).sum_add_tsum_nat_add']
  refine add_le_add ?_ (ENNReal.tsum_le_tsum fun k => hgF _)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [h0]
  rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_range.2 (by omega)) fun m hm hm1 => ?_]
  · exact hgF 1
  · rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · exact h0
      · exact absurd rfl hm1
    · exact hmid m h (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))

/-- Along an increasing exhaustion of the primes, the Euler defect `Σ_{m coprime to S_j} A_m ξ(E)`
tends to `ξ(E)` whenever `Σ_m A_m ξ(E) < ∞`: every `m ≥ 2` coprime to `S_j` exceeds any fixed
bound once `S_j` contains all primes up to it. -/
theorem tendsto_rateEulerPart_of_exhaustion {ξ : Measure ℝ} {E : Set ℝ} (hE : MeasurableSet E)
    (hfin : rateEuler ξ E ≠ ∞) {S : ℕ → Finset ℕ} (hmono : Monotone S)
    (hex : ∀ p, p.Prime → ∃ j, p ∈ S j) :
    Tendsto (fun j => rateEulerPart (· ∈ S j) ξ E) atTop (𝓝 (ξ E)) := by
  classical
  set F : ℕ → ℝ≥0∞ := fun m => rateDilate m ξ E
  have hF : ∑' m, F m ≠ ∞ := by rwa [← rateEuler_apply _ hE]
  have hξ1 : F 1 = ξ E := by simp [F, rateDilate_one]
  -- lower bound: the `m = 1` term
  have hlow : ∀ j, ξ E ≤ rateEulerPart (· ∈ S j) ξ E := by
    intro j
    rw [rateEulerPart, Measure.sum_apply _ hE, ← hξ1]
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum 1)
    simp [F]
  -- upper bound: `ξ E + Σ_{m > N} F m` once all primes `≤ N` are deleted
  have hup : ∀ N : ℕ, ∀ᶠ j in atTop, rateEulerPart (· ∈ S j) ξ E ≤
      ξ E + ∑' k, F (k + (N + 1)) := by
    intro N
    have : ∃ j₀, ∀ p ≤ N, p.Prime → p ∈ S j₀ := by
      induction N with
      | zero =>
          refine ⟨0, fun p hp hpr => absurd hpr ?_⟩
          rw [Nat.le_zero.1 hp]
          exact Nat.not_prime_zero
      | succ N ih =>
          obtain ⟨j₁, hj₁⟩ := ih
          by_cases hN : (N + 1).Prime
          · obtain ⟨j₂, hj₂⟩ := hex (N + 1) hN
            refine ⟨max j₁ j₂, fun p hp hpr => ?_⟩
            rcases Nat.lt_or_ge p (N + 1) with h | h
            · exact hmono (le_max_left _ _) (hj₁ p (by omega) hpr)
            · have : p = N + 1 := by omega
              subst this; exact hmono (le_max_right _ _) hj₂
          · refine ⟨j₁, fun p hp hpr => ?_⟩
            rcases Nat.lt_or_ge p (N + 1) with h | h
            · exact hj₁ p (by omega) hpr
            · have : p = N + 1 := by omega
              subst this; exact absurd hpr hN
    obtain ⟨j₀, hj₀⟩ := this
    filter_upwards [eventually_ge_atTop j₀] with j hj
    rw [rateEulerPart, Measure.sum_apply _ hE]
    rw [← hξ1]
    refine tsum_le_one_add_tail (F := F) (fun m => ?_) (fun m hm2 hmN => ?_) ?_
    · split_ifs <;> simp [F]
    · have hm0 : m ≠ 0 := by omega
      have hm1 : m ≠ 1 := by omega
      have hq := Nat.minFac_prime hm1
      have hqS : m.minFac ∈ S j :=
        hmono hj (hj₀ _ ((Nat.minFac_le (Nat.pos_of_ne_zero hm0)).trans hmN) hq)
      rw [if_neg]
      · rfl
      · push Not
        exact ⟨m.minFac, Nat.mem_primeFactors.2 ⟨hq, Nat.minFac_dvd m, hm0⟩, hqS⟩
    · simp [rateDilate_zero]
  -- squeeze
  have hξfin : ξ E ≠ ∞ := ne_top_of_le_ne_top hfin (le_rateEuler ξ E)
  have htail := ENNReal.tendsto_sum_nat_add F hF
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun j => lt_of_lt_of_le ha (hlow j),
    fun b hb => ?_⟩
  have hlim : Tendsto (fun N : ℕ => ξ E + ∑' k, F (k + (N + 1))) atTop (𝓝 (ξ E)) := by
    have := (htail.comp (tendsto_add_atTop_nat 1)).const_add (ξ E)
    simpa using this
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hb)).exists
  filter_upwards [hup N] with j hj
  exact lt_of_le_of_lt hj hN

/-- **Cofinal deletion converges to the seed.** If `ν = Σ A_n ξ` is finite on `E`, then along any
increasing exhaustion of the primes, `D_{S_j}ν(E)` — the positive part minus the negative part —
converges to `ξ(E)`: the positive part equals the negative part plus a defect tending to `ξ(E)`. -/
theorem rateDeletion_tendsto_seed {ν ξ : Measure ℝ} (hξ : rateEuler ξ = ν) {E : Set ℝ}
    (hE : MeasurableSet E) (hfin : ν E ≠ ∞) {S : ℕ → Finset ℕ} (hmono : Monotone S)
    (hex : ∀ p, p.Prime → ∃ j, p ∈ S j) :
    (∀ j, rateDeletionPart (· ∈ S j) true ν E =
      rateDeletionPart (· ∈ S j) false ν E + rateEulerPart (· ∈ S j) ξ E) ∧
    Tendsto (fun j => rateEulerPart (· ∈ S j) ξ E) atTop (𝓝 (ξ E)) := by
  classical
  refine ⟨fun j => ?_, tendsto_rateEulerPart_of_exhaustion hE (hξ ▸ hfin) hmono hex⟩
  rw [← hξ, rateDeletionPart_rateEuler, Measure.add_apply]

end

end GaloisForLFunctions.HTGeometry
